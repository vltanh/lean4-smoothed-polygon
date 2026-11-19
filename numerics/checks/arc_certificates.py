"""The exact identities of the Lean proof of N4 and (INV), read off the Lean source and checked
with sympy (exact rational arithmetic): part 3 of the ``unstable`` check. This duplicates what Lean
checks (``ring``, ``linear_combination``), as a reference a reader can run. The numbering is that
of ``docs/unstable-curve.pdf``.

Read from ``SmoothedPolygons/Ch14/*.lean`` (statements, hypotheses and the ``linear_combination``
cofactors are parsed from the source; the goals of the three flow lemmas after their
``rw``/``simp`` steps are rebuilt here, as documented at each check):

* **The cofactor identities** ``goal.lhs - goal.rhs - sum c_i (h_i.lhs - h_i.rhs) = 0`` as rational
  functions (``sqrt3`` a free symbol ``s3``, ``h3 : s3^2 = 3``): ``arcParams_rel_identity``
  (``ArcRelation.lean``), the two halves of ``arc_normalForm`` (``ArcNormalForm.lean``, with
  ``huv : u v = 1``, ``u = e^{-t/eps}``, ``v = e^{t/eps}``) and the three components of
  ``frame_reducedCostate``.
* **Identities of the proof of (INV)** (Section 6 of the note): ``rel_eq`` (``R = Y^2 eps^4 R~``);
  the rearrangement of ``R~ = 0`` in Lemma 6.1 and the identity for its quantity ``D``; the closed
  forms of Lemma 6.2 (``2Y'_new - 1``, ``Y'_new - 2``, the numerator of ``p_new``,
  ``Y_new - 2``); the identity of Lemma 6.3 (``psi``); and, for Lemma 6.4, the derivatives of
  ``beta_Y(y)`` and of ``G(Y) = beta_Y(Y)`` and the value ``G(16/5)``.
"""
import os
import re
import time

import sympy as sp

LEAN = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                    'SmoothedPolygons', 'Ch14')

_SUP = str.maketrans('⁰¹²³⁴⁵⁶⁷⁸⁹', '0123456789')


class LeanSource:
    """the text of the Ch14 Lean files, with a minimal reader of declarations"""

    def __init__(self, files):
        self.text = {f: open(os.path.join(LEAN, f), encoding='utf-8').read() for f in files}

    def decl(self, name):
        """``(file, docstring, signature-and-proof text)`` of the declaration ``name``"""
        for f, t in self.text.items():
            m = re.search(r'(?:/--((?:(?!-/).)*?)-/\s*)?(?:private\s+)?'
                          r'(?:theorem|lemma|noncomputable def|def)\s+'
                          + re.escape(name) + r'(?=[\s({\[:])', t, re.S)
            if m:
                end = t.find('\n/--', m.end())
                end2 = t.find('\n\n', m.end())
                ends = [e for e in (end, end2) if e > 0]
                return f, m.group(1) or '', t[m.end():min(ends) if ends else len(t)]
        raise KeyError(name)

    def parts(self, name):
        """the binders (``{name: text}``) and the conclusion text of a theorem"""
        _, _, body = self.decl(name)
        i, depth, binders = 0, 0, {}
        start = None
        while i < len(body):
            c = body[i]
            if c in '({[':
                if depth == 0:
                    start = i
                depth += 1
            elif c in ')}]':
                depth -= 1
                if depth == 0 and body[start] == '(':
                    inner = body[start + 1:i]
                    k = inner.find(':')
                    if k > 0:
                        for nm in inner[:k].split():
                            binders[nm] = inner[k + 1:].strip()
            elif c == ':' and depth == 0 and body[i:i + 2] != ':=':
                j = body.find(':= by', i)
                if j < 0:
                    j = body.find(':=', i)
                return binders, body[i + 1:j].strip(), body[j:]
            i += 1
        raise ValueError(name)

    def linear_combinations(self, name):
        """the expressions of the ``linear_combination`` calls in the proof of ``name``"""
        _, _, body = self.decl(name)
        out = []
        for m in re.finditer(r'linear_combination(?:\s*\(norm := skip\))?', body):
            j = m.end()
            # the expression runs until the next tactic line at the indentation of the call
            line_start = body.rfind('\n', 0, m.start()) + 1
            indent = m.start() - line_start
            k = j
            while True:
                nl = body.find('\n', k)
                if nl < 0:
                    k = len(body)
                    break
                nxt = body[nl + 1:]
                ind = len(nxt) - len(nxt.lstrip(' '))
                if ind <= indent:
                    k = nl
                    break
                k = nl + 1
            out.append(body[j:k].strip())
        return out


def to_sympy(text, syms):
    """a Lean real expression as a sympy expression (``√3`` is the symbol ``s3``)"""
    t = text.replace('√3', 's3').replace('^', '**').replace('·', '*')
    t = re.sub(r'\(([^():]*?) : ℝ\)', r'(\1)', t)
    t = re.sub(r"\b([A-Za-z_]\w*)'", r'\1p', t)
    t = t.replace('₀', '0').replace('₁', '1')
    names = set(re.findall(r'\b[A-Za-z_]\w*\b', t))
    loc = {n: syms.setdefault(n, sp.Symbol(n)) for n in names}
    return sp.sympify(t, locals=loc, rational=True)


def split_rel(text, ops=('≤', '=')):
    """``(lhs, rhs, op)`` at the top-level relation"""
    depth = 0
    for i, c in enumerate(text):
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif depth == 0 and c in ops and text[i - 1:i + 1] != ':=':
            return text[:i].strip(), text[i + 1:].strip(), c
    raise ValueError(text[:80])


def is_zero(expr):
    """``expr`` is ``0`` as a rational function"""
    n, _ = sp.fraction(sp.together(expr))
    return sp.expand(n) == 0


# ---- the cofactor identities ------------------------------------------------------------------------
def _lc(src, name, idx, S, hyps):
    """the ``idx``-th ``linear_combination`` of ``name``, with the hypotheses substituted by
    their ``lhs - rhs``"""
    txt = src.linear_combinations(name)[idx]
    expr = to_sympy(txt, S)
    return expr.subs({S[h]: v for h, v in hyps.items() if h in S}, simultaneous=True)


def check_cofactors(src):
    out = {}
    S = {}
    s3, e, Y, lh, le, lf = (S.setdefault(n, sp.Symbol(n)) for n in ('s3', 'e', 'Y', 'lh', 'le', 'lf'))
    hs = s3 ** 2 - 3

    def tfo(a, b, c, a2, b2, c2):
        return 2 * a * a2 + b * c2 + c * b2           # traceForm_ofFrame

    # the goal of arcParams_rel_identity and frame_reducedCostate after their rewrites:
    # X0 = ofFrame (-e) (-2eY) (eY'/2), V_e = ofFrame xe (-xe^2/e) e, V_f = ofFrame xf e (-xf^2/e),
    # Lhat = ofFrame lh le lf, then Y' = (1 + e^2)/(e^2 Y)
    Yp = (1 + e ** 2) / (e ** 2 * Y)
    xe, xf = -2 * e * Y, e * Yp / 2
    F0 = -(s3 / (3 * e ** 3 * Yp)) * tfo(lh, le, lf, -e, xe, xf)
    Q = -(s3 / (6 * e)) * tfo(lh, le, lf, xe, -xe ** 2 / e, e)
    Pp = 2 / (s3 * e) * tfo(lh, le, lf, xf, e, -xf ** 2 / e)
    k = 1 + e ** 2
    rel = (k ** 2 * Q ** 2 - 2 * Q * (k ** 2 * F0 - Y ** 2 * e ** 2 * (1 - e ** 2) * Pp
                                      + 2 * Y ** 2 * e ** 2 - k * Y)
           + Y ** 4 * e ** 4 * Pp ** 2 + 2 * Y ** 2 * e ** 2 * (Y - 2) * Pp
           - 2 * Y ** 2 * e ** 2 * k * F0 * Pp + 4 * Y ** 2 * e ** 2 * k * F0
           - 2 * (2 * e ** 2 + 1) * k * Y * F0 + k ** 2 * F0 ** 2 + 4 * k ** 2 * F0)
    det = -((lh - sp.Rational(3, 2) * (-(1 / s3))) ** 2
            + (le - sp.Rational(3, 2) * (-(4 / s3))) * (lf - sp.Rational(3, 2) * (1 / s3)))
    goal = rel - 4 * Y ** 2 / 3 * (sp.Rational(9, 4) - det)
    c = _lc(src, 'arcParams_rel_identity', 0, S, {'hs': hs})
    out['arcParams_rel_identity'] = is_zero(goal - c)
    ok = []
    goals = [lh - s3 * (Y ** 2 * e ** 2 * Pp - k * (2 * e ** 2 + 1) * F0 + k * Q) / (2 * Y),
             le - 2 * s3 * e ** 2 * (Q - k * F0),
             lf + s3 * (Y ** 2 * e ** 2 * Pp - k ** 2 * F0) / (2 * Y ** 2)]
    for i, g in enumerate(goals):
        ok.append(is_zero(g - _lc(src, 'frame_reducedCostate', i, S, {'hs': hs})))
    out['frame_reducedCostate (3 components)'] = all(ok)
    # arc_normalForm: after rw [hN, arcPhiE_eq], simp, generalize u = e^{-t/e}, v = e^{t/e};
    # P0 = arcPhiE q 0, L = <Lambda_1(0), V_e>; hN0: N21(q) = -(2e/3) P0
    t, u, v, P0, L, Ypp = (S.setdefault(n, sp.Symbol(n)) for n in ('t', 'u', 'v', 'P0', 'L', 'Yp'))
    huv = u * v - 1
    x = -2 * e * Y
    lhs = s3 / (8 * e ** 3) * (-(2 * e / 3) * u * (P0 - 2 * e * (1 - u) * L
                                                  + s3 * (2 * x * t + x ** 2 * (1 - u)
                                                          + 4 * e ** 2 * (v - 1))))
    f0 = s3 / (8 * e ** 3) * (-(2 * e / 3) * P0)
    tJ = 2 * -(1 / s3) * x + -(4 / s3) * e + 1 / s3 * (-x ** 2 / e)
    q_ = -(s3 / (6 * e)) * (L + sp.Rational(3, 2) * tJ)
    B = Y - 1 + q_
    A = 1 + f0 - B
    tau = t / e
    rhs = -1 + A * u + B * u ** 2 + Y * tau * u
    c = _lc(src, 'arc_normalForm', 0, S, {'hs': hs, 'huv': huv})
    out['arc_normalForm (N21)'] = is_zero(lhs - rhs - c)
    # N23: x_f = e Y'/2 (Y' = arcY' q, free), P0 = arcPhiF q 0, L = <Lambda_1(0), V_f>;
    # hN0: N23(q) = (8e/3) P0
    xf2 = e * Ypp / 2
    lhs = s3 / (8 * e ** 3) * (8 * e / 3 * v * (P0 + 2 * e * (v - 1) * L
                                                + s3 * (-2 * xf2 * t + e ** 2 * (1 - u)
                                                        + 4 * xf2 ** 2 * (v - 1))))
    g0 = s3 / (8 * e ** 3) * (8 * e / 3 * P0)
    tJ = 2 * -(1 / s3) * xf2 + -(4 / s3) * (-xf2 ** 2 / e) + 1 / s3 * e
    p_ = 2 / (s3 * e) * (L + sp.Rational(3, 2) * tJ)
    Bp = Ypp - 1 + p_
    Ap = 1 + g0 - Bp
    rhs = -1 + Ap * v + Bp * v ** 2 - Ypp * tau * v
    c = _lc(src, 'arc_normalForm', 1, S, {'hs': hs, 'huv': huv})
    out['arc_normalForm (N23)'] = is_zero(lhs - rhs - c)
    return out


# ---- identities of the (INV) proof ------------------------------------------------------------------
def _def_body(src, name, S):
    _, _, body = src.decl(name)
    txt = body.split(':=', 1)[1].strip()
    txt = re.sub(r"\ba\.(\w+)'", r'\1p', txt)
    txt = re.sub(r'\ba\.(\w+)', r'\1', txt)
    return to_sympy(txt, S)


def check_identities(src):
    out = {}
    S = {}
    eps, Y, Yp, f0, q, p = (S.setdefault(n, sp.Symbol(n)) for n in ('eps', 'Y', 'Yp', 'f0', 'q', 'p'))
    rel = _def_body(src, 'rel', S)
    relT = _def_body(src, 'relT', S)
    sub = {Yp: (1 + eps ** 2) / (eps ** 2 * Y)}
    out['rel_eq: R = Y^2 eps^4 R~'] = is_zero((rel - Y ** 2 * eps ** 4 * relT).subs(sub))
    a, b = Y - 2, Yp - 2
    # Lemma 6.1: R~ = 0 rearranged, and the quantity D of part (ii)
    out['Lemma 6.1: 2Y\'(ab-3)f0 = 2q[(YY\'-1)b-2p] + (Y\'(f0-q)-Yp)^2 + 2(YY\'-1)ap - R~'] = is_zero(
        2 * Yp * (a * b - 3) * f0 - (2 * q * ((Y * Yp - 1) * b - 2 * p)
                                     + (Yp * (f0 - q) - Y * p) ** 2 + 2 * (Y * Yp - 1) * a * p)
        + relT)
    out['Lemma 6.1: D = Y((2Y\'-1)b-2p) + abY\' + 3Y\'(Y-1)'] = is_zero(
        Y * ((Y * Yp - 1) * b - 2 * p) - Yp * (Y - 1) * (a * b - 3)
        - (Y * ((2 * Yp - 1) * b - 2 * p) + a * b * Yp + 3 * Yp * (Y - 1)))
    # Lemma 6.2 and the identity of Lemma 6.3, with the Lean definitions of the next point
    s = S.setdefault('s', sp.Symbol('s'))
    Yn = _def_body(src, 'YNew', S)
    Ypn = _def_body(src, 'YNew\'', S)
    pn = _def_body(src, 'pNew', S)
    psi = _def_body(src, 'psiE', S)
    B = Y - 1 + q
    pn = pn.subs(S.get('B', sp.Symbol('B')), B)
    out["Lemma 6.2: (2Y'_new - 1)(Y'_new - 2) = (Y + s)(2s - Y)/(Y - s)^2"] = is_zero(
        (2 * Ypn - 1) * (Ypn - 2) - (Y + s) * (2 * s - Y) / (Y - s) ** 2)
    out['Lemma 6.2: s^2 - Ys + B = q + (s - 1)(s - Y + 1), p_new = that/(Y - s)^2'] = is_zero(
        s ** 2 - Y * s + B - (q + (s - 1) * (s - Y + 1))) and is_zero(
        pn - (s ** 2 - Y * s + B) / (Y - s) ** 2)
    out["Lemma 6.2: Y_new - 2 = (Y's^2 - Y)/(Y - s)"] = is_zero(Yn - 2 - (Yp * s ** 2 - Y) / (Y - s))
    out["Lemma 6.3: (Y - s)^2 [(Y_new - 2) - (Y_new - 1)(Y'_new - 2)] = psi(s)"] = is_zero(
        (Y - s) ** 2 * ((Yn - 2) - (Yn - 1) * (Ypn - 2)) - psi)
    # Lemma 6.4: the derivatives and the value at 16/5
    yv, tv = sp.symbols('yv tv', positive=True)
    beta = Y * sp.log(yv) - yv + 2 - Y + (Y - 1) / yv
    out["Lemma 6.4: beta_Y'(y) = -(y - 1)(y - (Y - 1))/y^2"] = is_zero(
        sp.diff(beta, yv) + (yv - 1) * (yv - (Y - 1)) / yv ** 2)
    G = tv * sp.log(tv) - 2 * tv + 3 - 1 / tv
    out["Lemma 6.4: G(t) = beta_t(t), G'(t) = log t - 1 + 1/t^2"] = is_zero(
        G - beta.subs(Y, tv).subs(yv, tv)) and is_zero(sp.diff(G, tv) - (sp.log(tv) - 1 + 1 / tv ** 2))
    c = sp.Rational(16, 5)
    out['Lemma 6.4: G(16/5) = (16/5)(log(16/5) - 297/256)'] = is_zero(
        G.subs(tv, c) - c * (sp.log(c) - sp.Rational(297, 256)))
    out['Lemma 6.4: log(16/5) > 297/256 (4 terms of 2 artanh(11/21))'] = bool(
        2 * sum(sp.Rational(11, 21) ** (2 * k + 1) / (2 * k + 1) for k in range(4))
        > sp.Rational(297, 256))
    return out


def run(quick=False):
    t0 = time.time()
    src = LeanSource(['ArcParams.lean', 'ArcStepClosed.lean', 'ArcRelation.lean',
                      'ArcNormalForm.lean'])
    out = {}
    for label, fn in (('cofactor identities', check_cofactors),
                      ('identities of the (INV) proof', check_identities)):
        t1 = time.time()
        try:
            out[label] = fn(src)
        except (KeyError, ValueError, IndexError) as ex:
            out[label] = {'error': 'could not read the Lean source: %r' % (ex,)}
        out[label + ' time_s'] = round(time.time() - t1, 1)

    def flat(d):
        for k, v in d.items():
            if isinstance(v, dict):
                yield from flat(v)
            elif isinstance(v, bool):
                yield v
    out['ok'] = all(flat({k: v for k, v in out.items() if isinstance(v, dict)})) and not any(
        'error' in v for v in out.values() if isinstance(v, dict))
    out['time_s'] = round(time.time() - t0, 1)
    return out
