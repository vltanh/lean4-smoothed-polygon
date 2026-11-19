"""Theorem 14.4.1's numerical fact N4, ``UnstableCurveLeavesStarDomain``
(``SmoothedPolygons/Ch14/UnstableCurve.lean``; proved in Lean without computer assistance as
``unstableCurveLeavesStarDomain``, ``Ch14/ArcRegionInvariant.lean``): the reference computation of
the book's Figure 14.2, the global unstable curve ``W^u(q_out)`` and the orbits on it.

The statement:

    ∃ e, IsReinhardtPoincareExtension e ∧ ∃ U ∈ 𝓝 chartPtOut,
      ∀ p ∈ Function.localUnstableSet e chartPtOut U, 0 < p.1 → ReachesStarBoundary (lieChart p)

``ReachesStarBoundary q``: for some ``K`` the iterates ``q_j = reinPoincare^[j] q`` satisfy
``SwitchEntersE2 q_j`` (``j <= K``), ``ArcSwitchesToE1 q_j`` (``j < K``) and
``ArcLeavesStarDomain q_K``.

This module (part 1 of the ``unstable`` check; parts 2 and 3 are ``arc_invariant.py`` and
``arc_certificates.py``):

1. **The local unstable curve** (mpmath, 110 digits, not rigorous): the graph ``x~ = c(r)`` of
   ``W^u`` by the graph transform (forward orbits of ``(r_a, x~_out)``, ``r_a ~ 1e-22``, contract
   onto ``W^u`` by ``~0.08`` per step while ``r`` grows by ``~r_scale``), and the Taylor data
   ``c(r) = x~_out + v r + w r^2 + c3 r^3 + ...`` by a least-squares fit at ``r in [1e-12, 1e-5]``.
2. **Seeds** on a fundamental domain: ``s in [s0, lam s0)``, ``s0 = 1e-7``, ``lam = r(F(seed s0))/s0``,
   ``seed(s) = lieChart (s, c(s))`` with the cubic Taylor polynomial (error ``O(s^4) ~ 1e-26``, then
   contracted). The seeds lie on ``W^u`` only up to that error (not rigorous).
3. **N4 along each orbit, in Arb balls (512 bits): rigorous for the seed phase point.** From the
   exact seed (the chart in balls) every arc is the closed-form ``e2``-arc (``reinhardt.Arc``), and
   every sign below is decided by ball arithmetic (an undecided sign is reported, never guessed):
   ``rho_0, rho_1, rho_2 > 0`` (a star state), P1 ``f0 > 0``, P4 ``p > 0``, ``r > 0`` at every
   point, and ``SwitchEntersE2`` directly (``H(e1) < H(e2)``, and the slope of ``H(e3) - H(e2)``
   along the ``e3``-flow, from the vector field, is ``< 0``; also Proposition 4.4 (1),
   ``switchEntersE2_of_arc``, from P1 and P4); on a switching arc P2 ``q <= 0`` and
   ``F(log Y) < 0`` (Proposition 4.4 (2), ``arcSwitchesToE1_of_arc``: ``ArcSwitchesToE1``), the
   switching root ``tau_sw`` isolated in a ball (``F`` is monotone between its explicit critical
   points), ``f'(tau_sw) < 0``, ``g > 0`` on ``(0, tau_sw]``; on the last arc ``f > 0`` on
   ``[0, log Y]`` and ``g > 0`` on ``(0, log Y]`` directly from the monotone pieces
   (``ArcLeavesStarDomain`` with ``T = eps log Y``, through the signs of Theorem 2.3), and which
   Lean lemma also covers it (Proposition 4.4 (3), Lemma 6.4). The next point
   is ``Ad_{R^-1}`` of the state at ``t_sw = eps tau_sw``, in balls. Per arc also: the switching and
   exit times, the residuals of the four-term normal form (Theorem 2.3: the computed exponential
   polynomials of ``N21``, ``N23`` against ``f``, ``g``), of the section conditions, of
   Theorem 5.1 + ``q_new = Phi(s)/(Y - s)^2`` (computed here) against the flow, and the ``e3``-slope against
   ``-2 sqrt3 p/(Y' - 1)`` (``hasDerivAt_e3_sub_e2``). Rigorous modulo the correctness of this code,
   python-flint, and the Lean theorems that turn these signs into the predicates (Theorem 2.3 and
   ``phaseHam_signs_along_arc``: the switching functions have the signs of ``f``, ``g`` on
   ``[0, T)``;
   ``reinSwitchTime_eq_tauSw``, ``rho_2_iso_vfX_one_arcExitTime``: ``t_sw = eps tau_sw``, the exit at
   ``T``); the seeds being on ``W^u`` is not rigorous.
4. **The threshold** (mpmath, 60 digits): the seed ``s*`` at which the switch of the last switching
   arc meets its exit (``F(log Y) = 0``), by bisection; ``r*`` (the book's "about 0.065"), the end
   point of the curve of switching points (the book's ``(0.21, -3.03)``, on the chart boundary
   ``x~21 = sqrt3 - 1/r``), the slope of ``F(log Y)`` in ``log s``, and the cusp arcs just below
   ``s*`` (``eps -> 0``, exit) and the direct exits just above.
"""
import time

import mpmath as mp
from flint import ctx

from .. import reinhardt as rh
from .. import arcmap as am
from ..fuller import Undecided

S0 = '1e-7'
R_D = 1e-3          # the fundamental domain [1e-3, F_1(1e-3)) of UnstableCurve.lean's docstring
DIV = 0.01          # "near the divisor": r < DIV, margins normalized by r^3, r^2


# ---- the map in the chart -----------------------------------------------------------------------
def chart_step(p, num, C):
    """one step of the Reinhardt-Poincare map in the chart: ``lieChartInv (reinPoincare
    (lieChart p))``, for a point whose arc switches before the exit"""
    r, x = p
    q = rh.lie_chart(r, x, num, C)
    d = rh.arc_params(q, C, num)
    a = am.AP.of(d, num)
    tau = a.first_zero_F(num.log(a.Y))
    if tau is None:
        return None
    qs = rh.ad_rinv(rh.Arc(q, 1, num, C).state(d['eps'] * tau), C)
    return rh.lie_chart_inv(qs, num)


def taylor_data(dps=110):
    """the graph ``c(r)`` of ``W^u`` near ``r = 0`` by the graph transform, and the least-squares
    coefficients ``v = c'(0)``, ``w = c''(0)/2``, ``c3`` (mpmath; not rigorous)"""
    num = rh.MP(dps)
    C = rh.consts(num)
    rS, xo = rh.fixed_point(num)
    pts = []
    for ra in ('1e-22', '2.3e-22', '4.1e-22', '0.7e-22'):
        p = (mp.mpf(ra), xo)
        for _ in range(30):
            p = chart_step(p, num, C)
            if p[0] > mp.mpf('1e-12'):
                pts.append(p)
            if p[0] > mp.mpf('1e-5'):
                break
    coef = []
    for i in range(3):
        A = mp.matrix([[1, p[0], p[0] ** 2, p[0] ** 3] for p in pts])
        b = mp.matrix([(p[1][i] - xo[i]) / p[0] for p in pts])
        sol = mp.lu_solve(A.T * A, A.T * b)
        coef.append([sol[j] for j in range(4)])
    v = [coef[i][0] for i in range(3)]
    w = [coef[i][1] for i in range(3)]
    c3 = [coef[i][2] for i in range(3)]
    return dict(rS=rS, xo=xo, v=v, w=w, c3=c3, n_points=len(pts))


def seed_chart(s, td):
    """the chart point ``(s, c(s))`` with the cubic Taylor polynomial of ``W^u``"""
    s = mp.mpf(s)
    return (s, tuple(td['xo'][i] + td['v'][i] * s + td['w'][i] * s ** 2 + td['c3'][i] * s ** 3
                     for i in range(3)))


# ---- one arc, all its signs -----------------------------------------------------------------------
def _f(num, x):
    return num.mid(x)


def arc_record(q, num, C):
    """everything about the ``e2``-arc from the section point ``q``; returns ``(record, next q)``
    (``next q`` is ``None`` for the exit arc). In Arb every sign is decided or ``Undecided`` is
    raised."""
    s3 = C['s3']
    d = rh.arc_params(q, C, num)
    a = am.AP.of(d, num)
    arc = rh.Arc(q, 1, num, C)
    eps = d['eps']
    sg = num.sign
    rec = dict(r=_f(num, d['r']))
    ch = rh.lie_chart_inv(q, num)
    rec['x'] = [_f(num, v) for v in ch[1]]
    rec.update({k: _f(num, d[k]) for k in ('eps', 'Y', 'Yp', 'f0', 'q', 'p')})
    # the signs at the point (Proposition 4.4 (1): SwitchEntersE2)
    rec['star'] = all(sg(v) > 0 for v in d['rho'])      # IsStarState (det X = 1 by the chart)
    rec['P1'] = sg(d['f0']) > 0
    rec['P4'] = sg(d['p']) > 0
    rec['r>0'] = sg(d['Yp'] - 2) > 0
    rec['P2'] = sg(-d['q']) >= 0
    rec['E'] = sg(a.region_margins()['E']) >= 0
    rec['in G*'] = rec['P1'] and rec['P4'] and rec['r>0'] and rec['P2'] and rec['E']
    # residuals: section conditions; Theorem 2.3 (the four-term normal form)
    res = rh.section_residuals(q, C, num)
    rec['res_section'] = max(abs(_f(num, v)) + num.rad(v) for v in res.values())
    nrm = 8 * eps ** 3 / s3
    exp_f = {(0, 0): -num.one, (0, -2): a.A, (0, -4): a.B, (1, -2): a.Y / eps}
    exp_g = {(0, 0): -num.one, (0, 2): a.Ap, (0, 4): a.Bp, (1, 2): -a.Yp / eps}
    worst = 0.0
    for N, ex in ((arc.numer(0), exp_f), (arc.numer(2), exp_g)):
        for key in set(N) | set(ex):
            dv = N.get(key, num.zero) / nrm - ex.get(key, num.zero)
            worst = max(worst, abs(_f(num, dv)) + num.rad(dv))
    rec['res_normal_form'] = worst
    sl = rh.e3_slope(q, C, num)
    rec['e3_slope'] = _f(num, sl)
    rec['res_e3_slope'] = abs(_f(num, sl + 2 * s3 * d['p'] / (d['Yp'] - 1)))
    # SwitchEntersE2 directly: H(e1) < H(e2) at q, and H(e3) - H(e2) (= 0 at q) has a negative
    # slope along the e3-flow
    h21 = rh.phase_ham(q, 1, C, num) - rh.phase_ham(q, 0, C, num)
    rec['SwitchEntersE2'] = sg(h21) > 0 and sg(sl) < 0
    L = num.log(a.Y)
    FL = a.F(L)
    rec['F(log Y)'] = _f(num, FL)
    rec['T'] = _f(num, eps * L)
    if sg(FL) < 0:
        rec['kind'] = 'switch'
        tau = a.first_zero_F(L)
        rec['tau_sw'] = _f(num, tau)
        rec['tau_sw_rad'] = num.rad(tau)
        rec['t_sw'] = _f(num, eps * tau)
        fs = a.fDeriv(tau)
        rec["f'(tau_sw)"] = _f(num, fs)
        rec['slope<0'] = sg(fs) < 0
        gp = a.pieces('G', tau)
        mG = a.min_on('G', gp[1], tau)
        rec['min G on (0, tau_sw]'] = _f(num, mG)
        rec['g>0'] = sg(1 + a.Bp - a.Yp) > 0 and sg(mG) > 0
        rec['ArcSwitchesToE1'] = (rec['r>0'] and rec['P1'] and rec['P2'] and rec['P4']
                                  and rec['slope<0'] and rec['g>0'])
        new, (tau2, s, k) = a.step()
        qn = rh.ad_rinv(arc.state(eps * tau), C)
        dn = rh.arc_params(qn, C, num)
        rec['res_map'] = max(abs(_f(num, getattr(new, key) - dn[key]))
                             / (1e-300 + abs(_f(num, dn[key]))) for key in ('eps', 'Y', 'f0', 'q', 'p'))
        rec['psi(s)'] = _f(num, a.psiE(s))
        rec['Y_new'] = _f(num, a.YNew(s))
        return rec, qn
    rec['kind'] = 'exit'
    em = a.exit_margins()
    rec['min F on [0, log Y]'] = _f(num, em['F'])
    rec['min G on [tau_1, log Y]'] = _f(num, em['G'])
    rec['ArcLeavesStarDomain'] = (rec['r>0'] and rec['P1'] and rec['P4'] and sg(em['F']) > 0
                                  and sg(em['G']) > 0 and sg(em['G0slope']) > 0)
    lem = []
    if rec['P1'] and rec['P2'] and rec['P4'] and rec['r>0']:
        lem.append('Prop 4.4 (3)')
    try:
        if (rec['P1'] and rec['P4'] and rec['r>0'] and sg(a.Y - num.mk(16) / 5) >= 0
                and sg(a.f0 - a.q * (1 - 1 / a.Y)) >= 0):
            lem.append('Lemma 6.4')
    except Undecided:
        lem.append('(undecided)')
    rec['Lean lemmas'] = lem
    return rec, None


def follow(p0, num, C, maxn=60):
    """the orbit of ``lieChart p0`` until the exit arc: the list of arc records"""
    q = rh.lie_chart(num.mk(p0[0]), tuple(num.mk(v) for v in p0[1]), num, C)
    out = []
    for n in range(maxn):
        try:
            rec, q = arc_record(q, num, C)
        except Undecided as e:
            out.append(dict(kind='undecided', why=str(e)))
            return out
        rec['n'] = n
        out.append(rec)
        if q is None:
            return out
    out.append(dict(kind='no exit after %d arcs' % maxn))
    return out


def n4_holds(orbit):
    """``ReachesStarBoundary`` decided along the orbit: ``SwitchEntersE2`` (P1, P4) at every point,
    ``ArcSwitchesToE1`` on the switching arcs, ``ArcLeavesStarDomain`` on the last"""
    if not orbit or orbit[-1].get('kind') != 'exit':
        return False
    ok = all(r['star'] and r['P1'] and r['P4'] and r['r>0'] and r['SwitchEntersE2'] for r in orbit)
    ok = ok and all(r['ArcSwitchesToE1'] for r in orbit[:-1])
    return ok and orbit[-1]['ArcLeavesStarDomain']


# ---- the threshold --------------------------------------------------------------------------------
def threshold(td, s_lo, s_hi, n, dps=60, iters=150):
    """bisection for the seed ``s*`` in ``[s_lo, s_hi]`` at which the arc ``n`` of the orbit has
    ``F(log Y) = 0`` (switch = exit); mpmath"""
    num = rh.MP(dps)
    C = rh.consts(num)

    def orbit_to(s, m):
        p = seed_chart(s, td)
        q = rh.lie_chart(p[0], p[1], num, C)
        qs = [q]
        for _ in range(m):
            d = rh.arc_params(q, C, num)
            a = am.AP.of(d, num)
            tau = a.first_zero_F(num.log(a.Y))
            q = rh.ad_rinv(rh.Arc(q, 1, num, C).state(d['eps'] * tau), C)
            qs.append(q)
        return qs

    def phi(s):
        q = orbit_to(s, n)[-1]
        a = am.AP.of(rh.arc_params(q, C, num), num)
        return a.F(num.log(a.Y))

    lo, hi = mp.mpf(s_lo), mp.mpf(s_hi)
    flo, fhi = phi(lo), phi(hi)
    assert flo < 0 < fhi, (flo, fhi)
    for _ in range(iters):
        m = (lo + hi) / 2
        if phi(m) < 0:
            lo = m
        else:
            hi = m
        if hi - lo < hi * mp.mpf(10) ** (-dps + 12):
            break
    ss = (lo + hi) / 2
    q = orbit_to(ss, n)[-1]
    d = rh.arc_params(q, C, num)
    a = am.AP.of(d, num)
    L = num.log(a.Y)
    qT = rh.ad_rinv(rh.Arc(q, 1, num, C).state(d['eps'] * L), C)
    rT, xT = rh.lie_chart_inv(qT, num)
    ch = rh.lie_chart_inv(q, num)
    h = ss * mp.mpf(10) ** (-dps // 3)
    slope = (phi(ss + h) - phi(ss - h)) / (2 * h) * ss
    out = dict(seed=mp.nstr(ss, 30), arc=n, r_star=float(d['r']), x_star=[float(v) for v in ch[1]],
               eps=float(d['eps']), Y=float(a.Y), Yp=float(a.Yp), T=float(d['eps'] * L),
               end_point=[float(rT), float(xT[0])], end_point_all=[float(v) for v in xT],
               sqrt3_minus_1_over_r_end=float(num.sqrt3 - 1 / rT),
               rho1_at_end=float(rh.rho(qT[0], num.sqrt3)[1]),
               dF_dlogs=float(slope))
    # the cusp arcs just below s*, the direct exits just above
    below, above = [], []
    for e in (3, 8, 16):
        dlt = mp.mpf(10) ** (-e)
        qs = orbit_to(ss * (1 - dlt), n + 1)
        rec, _ = arc_record(qs[-1], num, C)
        below.append(dict(delta=-float(dlt), r=rec['r'], x21=rec['x'][0], eps=rec['eps'],
                          kind=rec['kind'], exits=rec.get('ArcLeavesStarDomain'),
                          lemmas=rec.get('Lean lemmas')))
        rec, _ = arc_record(orbit_to(ss * (1 + dlt), n)[-1], num, C)
        above.append(dict(delta=float(dlt), r=rec['r'], kind=rec['kind'],
                          exits=rec.get('ArcLeavesStarDomain'),
                          **{'F(log Y)': rec['F(log Y)']}))
    out['below s*: the next arc (a cusp arc)'] = below
    out['above s*: the arc itself'] = above
    return out


# ---- the run --------------------------------------------------------------------------------------
def _minrec(store, key, val, tag):
    if val is None:
        return
    if key not in store or val < store[key][0]:
        store[key] = (val, tag)


def run_curve(quick=False, n_seeds=None, prec=512):
    """part 1: the unstable curve, the orbits on it (Arb), the threshold (mpmath)"""
    old_prec = ctx.prec
    try:
        return _run(quick, n_seeds, prec)
    finally:
        ctx.prec = old_prec


def run(quick=False):
    """the ``unstable`` check: part 1 (this module), part 2 (``arc_invariant``), part 3
    (``arc_certificates``)"""
    from . import arc_invariant, arc_certificates
    out = {'1. W^u and N4 along its orbits': run_curve(quick)}
    out['2. (INV) sampled (mpmath)'] = arc_invariant.run(quick)
    out['3. the identities, exactly (sympy)'] = arc_certificates.run(quick)
    o = out['1. W^u and N4 along its orbits']['orbits (Arb)']
    out['ok'] = (o['undecided_or_failed'] == 0 and out['2. (INV) sampled (mpmath)']['ok']
                 and out['3. the identities, exactly (sympy)']['ok'])
    return out


def _run(quick, n_seeds, prec):
    out = {}
    t0 = time.time()
    td = taylor_data()
    out['local unstable curve (mpmath, graph transform)'] = dict(
        x_out=[float(v) for v in td['xo']], r_scale=float(td['rS']),
        v=[mp.nstr(x, 12) for x in td['v']], w=[mp.nstr(x, 6) for x in td['w']],
        c3=[mp.nstr(x, 4) for x in td['c3']], fit_points=td['n_points'],
        time_s=round(time.time() - t0, 1))
    # the fundamental domain of seeds
    numm = rh.MP(60)
    Cm = rh.consts(numm)
    s0 = mp.mpf(S0)
    lam = chart_step(seed_chart(s0, td), numm, Cm)[0] / s0
    N = n_seeds or (24 if quick else 500)
    seeds = [s0 * lam ** (mp.mpf(i) / N) for i in range(N)]
    # the orbits, in balls
    t1 = time.time()
    num = rh.ARB(prec)
    C = rh.consts(num)
    orbits = [follow(seed_chart(s, td), num, C) for s in seeds]
    t_orbits = time.time() - t1
    ok = [n4_holds(o) for o in orbits]
    Ks, KDs = {}, {}
    mins = {}
    worst = dict(res_section=0.0, res_normal_form=0.0, res_e3_slope=0.0, res_map=0.0, tau_rad=0.0)
    lemmas = {}
    sw_r_max, ex_r_min = 0.0, float('inf')
    curve = []
    for i, o in enumerate(orbits):
        if o[-1].get('kind') != 'exit':
            continue
        K = len(o) - 1
        Ks[K] = Ks.get(K, 0) + 1
        nD = next(j for j, rr in enumerate(o) if rr['r'] >= R_D)
        KDs[K - nD] = KDs.get(K - nD, 0) + 1
        for rr in o:
            tag = 'seed %d arc %d of K=%d, r=%.4g' % (i, rr['n'], K, rr['r'])
            curve.append((rr['r'], rr['x'][0]))
            for k in worst:
                if k == 'tau_rad':
                    worst[k] = max(worst[k], rr.get('tau_sw_rad', 0.0))
                elif k in rr:
                    worst[k] = max(worst[k], rr[k])
            r = rr['r']
            near = r < DIV
            zone = 'r < 0.01' if near else 'r >= 0.01'

            def nm(label, k):
                return label + (' /r^%d' % k if near and k > 1 else ' /r' if near and k else '')

            def sc(v, k):
                return v / r ** k if near else v
            _minrec(mins, (zone, nm('f0', 3)), sc(rr['f0'], 3), tag)
            _minrec(mins, (zone, nm('p', 2)), sc(rr['p'], 2), tag)
            _minrec(mins, (zone, nm('-(e3 slope)', 2)), sc(-rr['e3_slope'], 2), tag)
            if rr['kind'] == 'switch':
                sw_r_max = max(sw_r_max, r)
                _minrec(mins, (zone, nm('switching arcs: -q', 2)), sc(-rr['q'], 2), tag)
                _minrec(mins, (zone, 'switching arcs: -F(log Y)'), -rr['F(log Y)'], tag)
                _minrec(mins, (zone, nm("switching arcs: -f'(tau_sw)", 2)),
                        sc(-rr["f'(tau_sw)"], 2), tag)
                _minrec(mins, (zone, nm('switching arcs: E margin', 1)),
                        sc((rr['Y'] - 2) - (rr['Y'] - 1) * (rr['Yp'] - 2), 1), tag)
            else:
                ex_r_min = min(ex_r_min, r)
                _minrec(mins, ('exit', 'min F on [0, log Y]'), rr['min F on [0, log Y]'], tag)
                _minrec(mins, ('exit', 'F(log Y)'), rr['F(log Y)'], tag)
                _minrec(mins, ('exit', 'r'), r, tag)
                key = ' + '.join(rr['Lean lemmas']) or 'direct only'
                lemmas[key] = lemmas.get(key, 0) + 1
    curve.sort()
    rmax = curve[-1][0]
    sample, nxt = [], 0.0
    for a_, b_ in curve:
        if a_ >= nxt:
            sample.append([float('%.6g' % a_), float('%.6g' % b_)])
            nxt = a_ + rmax / 30
    sample.append([float('%.6g' % curve[-1][0]), float('%.6g' % curve[-1][1])])
    out['seeds'] = dict(s0=S0, lam=float(lam), n=N,
                        note='seed(s) = lieChart (s, c(s)), c the cubic Taylor polynomial; '
                             'orbits followed in Arb balls at %d bits' % prec)
    out['orbits (Arb)'] = dict(
        n=len(orbits), N4_decided_true=sum(ok), undecided_or_failed=len(ok) - sum(ok),
        K_from_seed=dict(sorted(Ks.items())), K_from_D=dict(sorted(KDs.items())),
        D='first orbit point with r >= %g (a fundamental domain [1e-3, F_1(1e-3)))' % R_D,
        exit_arc_lemmas=lemmas,
        max_r_of_a_switching_point=sw_r_max, min_r_of_an_exit_point=ex_r_min,
        max_residuals=worst,
        minima={'%s: %s' % k: [v[0], v[1]] for k, v in sorted(mins.items())},
        curve_sample_r_x21=sample, curve_points=len(curve),
        time_s=round(t_orbits, 1))
    if not all(ok):
        out['orbits (Arb)']['failures'] = [o[-1] for o, g in zip(orbits, ok) if not g][:5]
    keys = ('n', 'kind', 'r', 'x', 't_sw', 'T', 'F(log Y)', 'SwitchEntersE2', 'ArcSwitchesToE1',
            'ArcLeavesStarDomain', 'in G*', 'psi(s)', 'Lean lemmas')
    out['orbits (Arb)']['example: the orbit of the first seed'] = [
        {k: (rr[k] if k != 'x' else rr[k][0]) for k in keys if k in rr} for rr in orbits[0]]
    # the threshold
    t2 = time.time()
    o0 = orbits[0]
    n = len(o0) - 2                      # the last switching arc of the first seed
    th = threshold(td, s0, s0 * lam, n, iters=60 if quick else 150)
    th['time_s'] = round(time.time() - t2, 1)
    out['threshold (mpmath)'] = th
    out['book'] = dict(end_point=[0.21, -3.03], threshold_r=0.065, x21_out=-2.39)
    out['time_s'] = round(time.time() - t0, 1)
    return out
