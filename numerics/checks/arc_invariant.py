"""(INV), ``ArcRegionInvariant`` (``SmoothedPolygons/Ch14/ArcRegionInvariant.lean``; proved in Lean as
``arcRegionInvariant``, from its sharp form ``arcRegionInvariant_sharp``), sampled on the arc
parameters: part 2 of the ``unstable`` check. mpmath at 60 digits, **not rigorous** (a sampled
reference; the Lean proof is by identities and inequalities).

    ArcRegionInvariant : ∀ q ∈ arcRegion, (arcParams q).F (log (arcY q)) < 0 →
      reinPoincare q ∈ arcRegion ∨ ArcLeavesStarDomain (reinPoincare q)

On the parameters (``ArcParams.lean``, ``ArcStepClosed.lean``): a point of ``G*`` (``arcRegion``) is
``(eps, Y, f0, g0 = 0, q, p)`` with ``Y' = (1 + eps^2)/(eps^2 Y)``, the relation ``rel = 0`` (2.1),
``r = eps (Y' - 2)/2 > 0``, P1 ``f0 > 0``, P2 ``q <= 0``, P4 ``p > 0``, E
``(Y - 1)(Y' - 2) <= Y - 2``. The image is ``step (qNew s)`` (Theorem 2.1 and
``arcQ_reinPoincare``: ``q_new = Phi(s)/(Y - s)^2``, ``s = e^{tauSw}``); it exits iff ``f > 0`` and
``g > 0`` on ``(0, log Y_new)`` (``n4g_signs``), decided here from the monotone pieces of
``F = e^tau f`` and ``G = e^{-tau} g``.

Sampling, in ``x = Y - 2``, ``y = Y' - 2`` (``eps^2 = 1/(Y Y' - 1)``), ``f0``, ``p`` and both roots
``q`` of ``rel = 0`` (every point of ``G*`` is one of them): ``y`` log-uniform in ``[1e-9, 0.45]``
(``r -> 0`` is ``y -> 0``), ``x = x_E (1 + 10^u)`` with ``x_E = y/(1 - y)`` the boundary of E
(``u`` down to ``-10``: near E), ``f0 = y^3 10^a``, ``p = y^2 10^b`` (the scales at the divisor;
``a, b`` down to ``-8``: near P1, P4), on a product grid and at random; how close the switching
samples come to each face of ``G*`` is reported (``sample: ...``).

Checked at each switching point (``F(log Y) < 0``): (INV); the sharp form (``psi(s) >= 0`` gives
``F q in G*``, ``psi(s) < 0`` gives ``Y_new >= 16/5`` and the exit); INV Proposition 5
(``f0_new >= q_new (1 - 1/Y_new)``); ``rel = 0`` at the image (``q_new`` is a root, and which); the
closed forms of ``step_closed`` against ``step``; and on a subset, the whole map against the
closed-form flow from the section point with these parameters (``reinhardt.section_from_params``,
``Arc``, ``Ad_{R^-1}``, ``arc_params``).

Margins (``> 0`` where the alternative holds): ``in`` = min of ``-q/y^2``, ``E/y``, ``f0/y^3``,
``p/y^2`` at the image (``y = Y'_new - 2``, ``E = (Y - 2) - (Y - 1)(Y' - 2)``); ``exit`` =
``min F_new on [0, log Y_new] / f0_new``. (INV) at the point is ``max(in, exit) > 0``.
"""
import math
import multiprocessing
import os
import random
import time

import mpmath as mp

from .. import reinhardt as rh
from .. import arcmap as am
from ..fuller import Undecided

DPS = 60


def point(x, y, f0, p, num):
    """the points of ``G*`` with these ``(x, y, f0, p)``: the roots ``q <= 0`` of ``rel = 0``"""
    Y, Yp = 2 + x, 2 + y
    eps = 1 / mp.sqrt(Y * Yp - 1)
    rr = am.AP(eps, Y, f0, num.zero, num.zero, p, num).rel_roots()
    if rr is None:
        return []
    out = []
    for i, q in enumerate(rr):
        a = am.AP(eps, Y, f0, num.zero, q, p, num)
        if a.in_region():
            out.append((a, 'smaller root' if i == 0 else 'larger root'))
    return out


def _margins(b, num):
    yb = b.Yp - 2
    m = b.region_margins()
    m_in = min(m['mq'] / yb ** 2, m['E'] / yb, m['f0'] / yb ** 3, m['p'] / yb ** 2)
    em = b.exit_margins()
    m_exit = em['F'] / b.f0 if em['G'] > 0 and em['G0slope'] > 0 else -mp.inf
    return m_in, m_exit, m


def check_point(a, num):
    """(INV) and the sharp form at one point of ``G*``; ``None`` if the arc exits (nothing to show)"""
    L = num.log(a.Y)
    if not a.F(L) < 0:
        return None
    b, (tau, s, k) = a.step()
    m_in, m_exit, mr = _margins(b, num)
    psi = a.psiE(s)
    res = dict(m_in=m_in, m_exit=m_exit, inv=max(m_in, m_exit), psi=psi, Ynew=b.Y,
               in_G=b.in_region(), exits=b.exits())
    res['prop5'] = (b.f0 - b.q * (1 - 1 / b.Y)) / b.f0
    # q_new is a root of rel at the image; which one
    rr = b.rel_roots()
    xb, yb = b.Y - 2, b.Yp - 2
    terms = ((b.Yp * (b.f0 - b.q) - b.Y * b.p) ** 2, -4 * b.p * b.q,
             2 * (b.Y * b.Yp - 1) * (yb * b.q + xb * b.p), 2 * b.Yp * (3 - xb * yb) * b.f0)
    res['rel_res'] = abs(b.rel()) / (b.Y ** 2 * b.eps ** 4 * max(abs(t) for t in terms))
    res['root'] = None if rr is None else (
        'larger' if abs(b.q - rr[1]) <= abs(b.q - rr[0]) else 'smaller')
    # step_closed: the closed forms against step
    res['closed_res'] = max(abs(b.Y - a.YNew(s)) / b.Y, abs(b.Yp - a.YNew_(s)) / b.Yp,
                            abs(b.f0 - a.f0New(s)) / b.f0, abs(b.p - a.pNew(s)) / b.p,
                            abs(b.eps - a.eps * (a.Y - s) / s) / b.eps)
    res['b'] = b
    res['s'] = s
    return res


def flow_check(a, num, C):
    """the image by the closed-form flow from the section point with the parameters of ``a``,
    against ``a.step()``: the largest relative difference of ``(eps, Y, f0, q, p)``, and the
    residuals of ``arcParams`` at the reconstructed point and of the section at the image"""
    q0 = rh.section_from_params(a.eps, a.Y, a.f0, a.q, a.p, C, num)
    d0 = rh.arc_params(q0, C, num)
    back = max(abs(d0[k] - getattr(a, k)) / (abs(getattr(a, k)) + 1e-300)
               for k in ('eps', 'Y', 'f0', 'q', 'p'))
    b, (tau, s, k) = a.step()
    qn = rh.ad_rinv(rh.Arc(q0, 1, num, C).state(a.eps * tau), C)
    dn = rh.arc_params(qn, C, num)
    diff = max(abs(dn[key] - getattr(b, key)) / abs(getattr(b, key))
               for key in ('eps', 'Y', 'f0', 'q', 'p'))
    sec = max(abs(v) for v in rh.section_residuals(qn, C, num).values())
    return float(back), float(diff), float(sec)


def samples(quick, seed=5):
    """the sample points ``(x, y, f0, p)``: a product grid and random points"""
    out = []
    ys = [10 ** e for e in (-9, -7, -5, -3, -2, -1.5, -1, -0.7, -0.5, -0.36)]
    us = [-10, -6, -3, -1.5, -0.5, 0, 0.5, 1, 2] if not quick else [-10, -3, 0, 1, 2]
    abx = [-8, -4, -2, -1, 0, 1, 2, 4] if not quick else [-8, -2, 0, 2]
    for y in (ys if not quick else ys[::2]):
        xE = y / (1 - y)
        for u in us:
            x = xE * (1 + 10 ** u)
            for a_ in abx:
                for b_ in abx:
                    out.append(('grid', x, y, y ** 3 * 10 ** a_, y ** 2 * 10 ** b_))
    rnd = random.Random(seed)
    n = 3000 if quick else 40000
    for _ in range(n):
        y = 10 ** rnd.uniform(-9, math.log10(0.45))
        xE = y / (1 - y)
        if rnd.random() < 0.8:
            x = xE * (1 + 10 ** rnd.uniform(-10, 2.5))
        else:
            x = xE + 10 ** rnd.uniform(-3, 1.5)
        out.append(('random', x, y, y ** 3 * 10 ** rnd.uniform(-8, 5),
                    y ** 2 * 10 ** rnd.uniform(-8, 4)))
    return out


def _w(a):
    """where: the coordinates of a sample point"""
    m = a.floats()
    return dict(x=m['Y'] - 2, y=m['Yp'] - 2, f0=m['f0'], q=m['q'], p=m['p'], r=m['r'])


def _work(chunk):
    """the checks on a chunk of samples (a worker process): counts, extremes, the switching points"""
    num = rh.MP(DPS)
    st = dict(samples=0, in_G=0, switching=0, image_in_G=0, image_exits=0, both=0, inv_fail=0,
              sharp_fail=0, psi_neg=0, prop5_fail=0, undecided=0)
    by_root, root_new, worst, sw = {}, {}, {}, []

    def upd(key, val, a):
        v = float(val)
        if key not in worst or v < worst[key][0]:
            worst[key] = (v, _w(a))

    def upd_max(key, val, a):
        v = float(val)
        if key not in worst or v > worst[key][0]:
            worst[key] = (v, _w(a))
    for kind, x, y, f0, p in chunk:
        st['samples'] += 1
        try:
            pts = point(mp.mpf(x), mp.mpf(y), mp.mpf(f0), mp.mpf(p), num)
        except (Undecided, ZeroDivisionError, ValueError):
            st['undecided'] += 1
            continue
        for a, root in pts:
            st['in_G'] += 1
            by_root[root] = by_root.get(root, 0) + 1
            try:
                res = check_point(a, num)
            except (Undecided, ZeroDivisionError, ValueError):
                st['undecided'] += 1
                continue
            if res is None:
                continue
            st['switching'] += 1
            mm = a.region_margins()
            ya = a.Yp - 2
            upd("sample: y = Y' - 2 (r -> 0)", ya, a)
            upd('sample: E/y', mm['E'] / ya, a)
            upd('sample: f0/y^3', mm['f0'] / ya ** 3, a)
            upd('sample: p/y^2', mm['p'] / ya ** 2, a)
            upd('sample: -q/y^2', mm['mq'] / ya ** 2, a)
            upd('sample: -q', mm['mq'], a)
            st['image_in_G'] += res['in_G']
            st['image_exits'] += res['exits']
            st['both'] += res['in_G'] and res['exits']
            if not (res['in_G'] or res['exits']):
                st['inv_fail'] += 1
            upd('(INV): max(in, exit)', res['inv'], a)
            if res['in_G']:
                upd('image in G*: in-margin', res['m_in'], a)
            if res['exits']:
                upd('image exits: exit-margin', res['m_exit'], a)
            if res['psi'] >= 0:
                if not res['in_G']:
                    st['sharp_fail'] += 1
                upd('psi(s) >= 0: in-margin', res['m_in'], a)
            else:
                st['psi_neg'] += 1
                if not (res['Ynew'] >= mp.mpf(16) / 5 and res['exits']):
                    st['sharp_fail'] += 1
                upd('psi(s) < 0: Y_new (>= 16/5)', res['Ynew'], a)
                upd('psi(s) < 0: exit-margin', res['m_exit'], a)
            if res['prop5'] < 0:
                st['prop5_fail'] += 1
            upd('INV Prop 5: (f0_new - q_new (1 - 1/Y_new))/f0_new', res['prop5'], a)
            upd_max('rel at the image (relative)', res['rel_res'], a)
            upd_max('step_closed against step (relative)', res['closed_res'], a)
            key = '%s -> %s' % (root, res['root'])
            root_new[key] = root_new.get(key, 0) + 1
            sw.append((a.eps, a.Y, a.f0, a.q, a.p))
    return st, by_root, root_new, worst, sw


_MAXIMA = ('rel at the image (relative)', 'step_closed against step (relative)')


def run(quick=False, n_flow=None, jobs=None):
    t0 = time.time()
    smp = samples(quick)
    jobs = jobs or int(os.environ.get('NUMERICS_JOBS', min(10, os.cpu_count() or 1)))
    chunks = [smp[i::jobs * 4] for i in range(jobs * 4)]
    if jobs > 1:
        with multiprocessing.Pool(jobs) as pool:
            parts = pool.map(_work, chunks)
    else:
        parts = [_work(c) for c in chunks]
    st, by_root, root_new, worst, sw = {}, {}, {}, {}, []
    for st_, br, rn, wo, sw_ in parts:
        for dst, src in ((st, st_), (by_root, br), (root_new, rn)):
            for k, v in src.items():
                dst[k] = dst.get(k, 0) + v
        for k, v in wo.items():
            if k not in worst or ((v[0] > worst[k][0]) if k in _MAXIMA else (v[0] < worst[k][0])):
                worst[k] = v
        sw += sw_
    t1 = time.time()
    num = rh.MP(DPS)
    C = rh.consts(num)
    nf = n_flow or (40 if quick else 400)
    fl = dict(n=0, max_back=0.0, max_diff=0.0, max_section=0.0)
    for prm in sw[::max(1, len(sw) // nf)][:nf]:
        a = am.AP(prm[0], prm[1], prm[2], num.zero, prm[3], prm[4], num)
        try:
            back, diff, sec = flow_check(a, num, C)
        except (Undecided, ZeroDivisionError, ValueError):
            continue
        fl['n'] += 1
        fl['max_back'] = max(fl['max_back'], back)
        fl['max_diff'] = max(fl['max_diff'], diff)
        fl['max_section'] = max(fl['max_section'], sec)
    fl['time_s'] = round(time.time() - t1, 1)
    out = dict(counts=st, points_by_root=by_root, root_of_q_new=root_new,
               extremes={k: dict(value=v[0], at=v[1]) for k, v in sorted(worst.items())},
               flow_check=fl, dps=DPS, jobs=jobs, time_s=round(time.time() - t0, 1))
    out['ok'] = st['inv_fail'] == 0 and st['sharp_fail'] == 0 and st['prop5_fail'] == 0
    return out
