"""The exact certificates of the Lean proof of N4 and (INV), read off the Lean source and checked
with sympy (exact rational arithmetic): part 3 of the ``unstable`` check. This duplicates what Lean
checks (``positivity``, ``ring``, ``linear_combination``), as a reference a reader can run.

Read from ``SmoothedPolygons/Ch14/*.lean`` (statements, hypotheses, the ``linear_combination``
cofactors and the docstring lists are parsed from the source; the goals of the three flow lemmas
after their ``rw``/``simp`` steps are rebuilt here, as documented at each check):

* **The three Bernstein certificates** (``ArcStepRegion.lean``: ``K~ >= 0`` on the triangle
  ``T = {x >= 0, z >= 0, x + 3z <= 1}``, 26 nonzero coefficients; ``ArcStepExit.lean``: ``tau_q >= 0``
  and ``U >= 0`` for ``x, y >= 0``, ``z in [0, 1]``): the Lean Bernstein form expanded has only
  nonnegative coefficients (what ``positivity`` uses), it agrees with the coefficient lists of the
  docstrings, and it equals the polynomial it certifies after the substitution
  (``l0 = 1 - x - 3z``, ``w = 3z``; resp. ``Y = 2 + x``, ``Y' = 2 + y``, ``s = 1 + x + z``,
  ``w = 1 - z``).
* **The cofactor identities** ``goal.lhs - goal.rhs - sum c_i (h_i.lhs - h_i.rhs) = 0`` as rational
  functions (``sqrt3`` a free symbol ``s3``, ``h3 : s3^2 = 3``): ``arcParams_rel_identity``
  (``ArcRelation.lean``), the two halves of ``arc_normalForm`` (``ArcNormalForm.lean``, with
  ``huv : u v = 1``, ``u = e^{-t/eps}``, ``v = e^{t/eps}``), the three components of
  ``frame_reducedCostate``, and ``n4h_Phi_key`` (``ArcStepRegion.lean``, modulo ``R~ = 0``).
* **Identities of the (INV) proof**: ``rel_eq`` (``R = Y^2 eps^4 R~``), ``n4h_P1_eq``, the
  concavity identity of ``n4h_K_nonneg`` and ``K~ = (1 + x)^2 K(x/(1 + x))``, and (5.3) of
  ``n4h_Tb_core``: ``s(s + 1) T_b - (s - 1) U = tau_f (s(s + 1) f0 - (s - 1)^2 z)
  + s tau_q ((s + 1) q + (s - 1) z) + s(s + 1) tau_p p``.
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


# ---- the Bernstein certificates ---------------------------------------------------------------------
def _nonneg_poly(expr, gens):
    P = sp.Poly(sp.expand(expr), *gens)
    coeffs = P.coeffs()
    return P, all(c >= 0 for c in coeffs), len(coeffs)


def check_bernstein(src):
    out = {}
    S = {}
    # K~ on the triangle
    _, kt_txt, _ = src.parts('n4h_Kt_nonneg')
    _, bk_txt, _ = src.parts('n4h_bernK')
    l0, x, w, z, y = (S.setdefault(n, sp.Symbol(n)) for n in ('l0', 'x', 'w', 'z', 'y'))
    bern = to_sympy(split_rel(bk_txt)[1], S)
    Kt = to_sympy(split_rel(kt_txt)[1], S)
    P, nonneg, n = _nonneg_poly(bern, (l0, x, w))
    # the docstring list `ijk:c`
    _, doc, _ = src.decl('Phi_nonpos')
    lst = dict((k, sp.Rational(v)) for k, v in re.findall(r'(\d{3}):(\d+(?:/\d+)?)', doc))
    from_lean = {'%d%d%d' % m: c for m, c in zip(P.monoms(), P.coeffs())}
    out['K~ (triangle)'] = dict(
        coefficients=n, all_nonnegative=nonneg,
        matches_docstring_list=(from_lean == lst), docstring_list_length=len(lst),
        min_coefficient=str(min(P.coeffs())),
        expansion_identity=is_zero(bern.subs({l0: 1 - x - 3 * z, w: 3 * z}, simultaneous=True) - Kt))
    # tau_q and U: Bernstein in z, w = 1 - z, coefficients of x^i y^j
    for label, berns, target, docname, key in (
            ('tau_q', ['n4h_bern_tq'], 'n4h_tq_nonneg', 'qNew_le_f0New', 'τ_q'),
            ('U', ['n4h_bern_U₀', 'n4h_bern_U₁'], 'n4h_U_nonneg', 'qNew_le_f0New', 'U')):
        b = 0
        for nm in berns:
            b += to_sympy(split_rel(src.parts(nm)[1])[1], S)
        P, nonneg, n = _nonneg_poly(b, (x, y, z, w))
        _, tgt, _ = src.parts(target)
        Y, Yp, s = (S.setdefault(n_, sp.Symbol(n_)) for n_ in ('Y', 'Yp', 's'))
        T = to_sympy(split_rel(tgt)[1], S)
        ident = is_zero(b.subs(w, 1 - z) - T.subs({Y: 2 + x, Yp: 2 + y, s: 1 + x + z},
                                                    simultaneous=True))
        # the docstring lists `x^i y^j [b0, ..., bn]`
        _, doc, _ = src.decl(docname)
        seg = doc.split('`%s`:' % key, 1)[1] if '`%s`:' % key in doc else ''
        seg = seg.split('`U`:', 1)[0] if label == 'tau_q' else seg.split('\n6.', 1)[0]
        lists = re.findall(r'x([⁰¹²³⁴⁵⁶⁷⁸⁹])y([⁰¹²³⁴⁵⁶⁷⁸⁹]) \[([^\]]*)\]', seg)
        match = True
        for i_, j_, vals in lists:
            i_, j_ = int(i_.translate(_SUP)), int(j_.translate(_SUP))
            beta = [sp.Rational(v.strip()) for v in vals.split(',')]
            nn = len(beta) - 1
            poly = sum(sp.binomial(nn, k) * beta[k] * z ** k * w ** (nn - k) for k in range(nn + 1))
            coeff = sp.Poly(sp.expand(b), x, y).as_dict().get((i_, j_), 0)
            if sp.expand(coeff - poly) != 0:
                match = False
        n_terms = len(sp.Poly(sp.expand(b), x, y).as_dict())
        out[label] = dict(monomials=n, all_nonnegative=nonneg, docstring_lists=len(lists),
                          xy_terms=n_terms, matches_docstring_lists=match and len(lists) == n_terms,
                          expansion_identity=ident)
    return out


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
    # arc_normalForm: after rw [hN, n4d_arcPhiE_eq], simp, generalize u = e^{-t/e}, v = e^{t/e};
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
    # n4h_Phi_key, modulo R~ = 0
    binders, concl, _ = src.parts('n4h_Phi_key')
    hR = split_rel(binders['hR'], ('=',))
    hRe = to_sympy(hR[0], S) - to_sympy(hR[1], S)
    a_, b_, _ = split_rel(concl, ('=',))
    c = _lc(src, 'n4h_Phi_key', 0, S, {'hR': hRe})
    out['n4h_Phi_key (modulo R~ = 0)'] = is_zero(to_sympy(a_, S) - to_sympy(b_, S) - c)
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
    a_, b_, _ = split_rel(src.parts('n4h_P1_eq')[1], ('=',))
    out['n4h_P1_eq'] = is_zero(to_sympy(a_, S) - to_sympy(b_, S))
    # the concavity identity of n4h_K_nonneg and K~ = (1 + x)^2 K(x/(1 + x))
    x, y, z = (S.setdefault(n, sp.Symbol(n)) for n in ('x', 'y', 'z'))
    K = to_sympy(split_rel(src.parts('n4h_K_nonneg')[1])[1], S)
    Kt = to_sympy(split_rel(src.parts('n4h_Kt_nonneg')[1])[1], S)
    k0 = sp.Rational(3, 2) * (x + 2 * z) ** 2
    k2 = (1 + (x + z)) ** 2 * (x * (x + z - 1) - 2 * z)
    out['n4h_K_nonneg: x(1+x)K = (1+x)(x-(1+x)y)k0 + y K~ + x k2 y((1+x)y-x)'] = is_zero(
        x * (1 + x) * K - ((1 + x) * (x - (1 + x) * y) * k0 + y * Kt
                           + x * k2 * y * ((1 + x) * y - x)))
    out['K~ = (1 + x)^2 K(x/(1 + x))'] = is_zero((1 + x) ** 2 * K.subs(y, x / (1 + x)) - Kt)
    # (5.3) of n4h_Tb_core
    s = S.setdefault('s', sp.Symbol('s'))
    Tb = to_sympy(split_rel(src.parts('n4h_Tb_core')[1])[1], S)
    U = to_sympy(split_rel(src.parts('n4h_U_nonneg')[1])[1], S)
    tq = to_sympy(split_rel(src.parts('n4h_tq_nonneg')[1])[1], S)
    zz = s - Y + 1
    tf = Yp * s ** 2 * (Yp * s - 2) * (s - Y)
    tp = Y * s ** 2 * (Y - s) * ((1 + Yp) * s - 2)
    out['(5.3) of n4h_Tb_core'] = is_zero(
        s * (s + 1) * Tb - (s - 1) * U
        - (tf * (s * (s + 1) * f0 - (s - 1) ** 2 * zz) + s * tq * ((s + 1) * q + (s - 1) * zz)
           + s * (s + 1) * tp * p))
    return out


def run(quick=False):
    t0 = time.time()
    src = LeanSource(['ArcParams.lean', 'ArcStepClosed.lean', 'ArcStepRegion.lean',
                      'ArcStepExit.lean', 'ArcRelation.lean', 'ArcNormalForm.lean'])
    out = {}
    for label, fn in (('Bernstein certificates', check_bernstein),
                      ('cofactor identities', check_cofactors),
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
