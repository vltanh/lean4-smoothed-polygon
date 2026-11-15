"""The runners of the command line (``python3 -m numerics``): each returns a JSON-able record."""
import math
import random
import time

from .iv import I
from . import fuller as fu
from . import boxmap as bm
from . import regions as rg
from . import faces
from .checks import common as cm
from .checks import dout, subclaims as sc, cell_two as c2, remark, unstable_curve


def _st(st):
    s = st.summary()
    return {k: s[k] for k in ('proved', 'leaves', 'evals', 'depth', 'time', 'n_failures',
                              'failures')}


# ---- sampled margins ------------------------------------------------------------------------------
def _grid(box, n):
    return dout.grid_points(box, n)


def _local_min(f, pts, keep=6, iters=40):
    """the smallest value of f over the points, refined by a pattern search from the best ones
    (points as (r2, Angle, Angle); the search moves the offsets inside the anchors)"""
    vals = []
    for p in pts:
        try:
            vals.append((f(p), p))
        except (fu.Undecided, RuntimeError, ValueError, ZeroDivisionError, AssertionError):
            continue
    vals.sort(key=lambda x: x[0])
    best = vals[0] if vals else (float('inf'), None)
    for v0, p0 in vals[:keep]:
        x0 = [p0[0], p0[1].x, p0[2].x]
        k1, k2 = p0[1].k, p0[2].k

        def g(x):
            try:
                return f((x[0], fu.Angle(k1, x[1]), fu.Angle(k2, x[2])))
            except (fu.Undecided, RuntimeError, ValueError, ZeroDivisionError, AssertionError):
                return float('inf')
        lo = [0.0, -4.0, -4.0]
        hi = [1.0, 4.0, 4.0]
        fx, x = cm.minimize_margin(g, x0, [1e-2, 1e-2, 1e-2], lo, hi, iters=iters)
        if fx < best[0]:
            best = (fx, (x[0], fu.Angle(k1, x[1]), fu.Angle(k2, x[2])))
    return best


def _pt(p):
    if p is None:
        return None
    return [float(p[0]), float(fu.Angle(p[1].k, p[1].x).value().mid()),
            float(fu.Angle(p[2].k, p[2].x).value().mid())]


def _clamped(box):
    """a margin function's domain guard: the point must lie in the closed box"""
    r, ps, t = box.r, box.psi(), box.th2()

    def inside(p):
        a = float(p[1].value().mid())
        b = float(p[2].value().mid())
        return (r.lo - 1e-15 <= p[0] <= r.hi + 1e-15 and ps.lo - 1e-12 <= a <= ps.hi + 1e-12
                and t.lo - 1e-12 <= b <= t.hi + 1e-12)
    return inside


def sampled(box, mfun, n=9):
    inside = _clamped(box)

    def f(p):
        if not inside(p):
            return float('inf')
        return mfun(p)
    m, p = _local_min(f, _grid(box, n))
    return m, p


def _img(p):
    res = cm.point_image(p)
    if res is None:
        raise fu.Undecided('face class')
    return res


def m_target(tgt):
    def f(p):
        cell, q, _ = _img(p)
        return rg.margin_box(cell, I(q[0]), I(q[1]), I(q[2]), tgt)
    return f


def m_subclaim(i, j):
    def f(p):
        z = fu.cell_point(*p)
        if fu.first_control(z) != 1:
            raise fu.Undecided('not a first-cell point')
        cell, q, _ = _img(p)
        if cell == 2:
            return float('inf')
        return rg.subclaim_margin(i, j, I(q[0]), I(q[1]), I(q[2]))
    return f


def m_celltwo(p):
    """max over n <= 3 of the D00 margin of F^n(p) (the structural margin of the claim)"""
    best = -float('inf')
    q = p
    for n in range(3):
        cell, q, _ = _img(q)
        if cell == 1:
            best = max(best, min(rg.PI3.lo - q[1], q[2] - rg.PI_M11.hi))
    return best


# ---- runners --------------------------------------------------------------------------------------
def sampled_rowsum(B, n=5, h=1e-7):
    """the largest row sum of |Dg| over an n^3 grid of the Box B (finite differences of the point
    evaluator), with the point"""
    best = (0.0, None)
    for p in _grid(B, n):
        try:
            x0 = [p[0], float(p[1].value().mid()), float(p[2].value().mid())]
            f0 = list(_img(tuple(x0))[1])
            J = []
            for k in range(3):
                x = list(x0)
                x[k] += h if x[k] + h <= [B.r.hi, B.psi().hi, B.th2().hi][k] else -h
                sg = 1.0 if x[k] > x0[k] else -1.0
                f1 = _img(tuple(x))[1]
                J.append([(a - b) / (h * sg) for a, b in zip(f1, f0)])
        except (fu.Undecided, RuntimeError, ValueError, ZeroDivisionError):
            continue
        m = max(sum(abs(J[k][i]) for k in range(3)) for i in range(3))
        if m > best[0]:
            best = (m, x0)
    return best


def run_selftest(quick=False):
    rng = random.Random(7)
    out = {}
    # 1. the semantic first control (IsFirstControl) agrees with Lemma 13.2.6's lexicographic rule
    agree = tot = 0
    for _ in range(300 if quick else 2000):
        kind = rng.randrange(6)
        r2 = rng.random() if kind else rng.choice([0.0, 1.0])
        psi = fu.Angle(rng.choice([0, 2]), 0) if kind == 1 else rng.uniform(0, math.pi)
        th2 = fu.Angle(rng.choice([0, 2, -2]), 0) if kind == 2 else rng.uniform(-math.pi, math.pi)
        try:
            z = fu.cell_point(r2, psi, th2)
            a, b = fu.first_control(z), fu.lex_first_control(z)
        except fu.Undecided:
            continue
        tot += 1
        agree += (a == b)
    out['first control = lexicographic rule'] = '%d / %d' % (agree, tot)
    # 2. the canonical representatives of the wrong-control face points: same class (the honest
    #    images computed from the point and from its representative agree), first control zeta
    good2 = tot2 = 0
    for _ in range(100 if quick else 400):
        face = rng.randrange(4)
        r2 = [0.0, 1.0, rng.uniform(0.05, 0.95), rng.uniform(0.05, 0.95)][face]
        psi = [rng.uniform(0, math.pi), rng.uniform(0, math.pi), 0.0, math.pi][face]
        th2 = rng.uniform(0, math.pi)
        q = faces.canonical_point(r2, psi, th2)
        try:
            ap = fu.Angle(2, 0) if psi == math.pi else psi
            z = fu.cell_point(r2, ap, th2)
            if fu.first_control(z) == 1:
                continue
            zq = fu.cell_point(*q)
            s1, s2 = fu.Step(z), fu.Step(zq)
        except fu.Undecided:
            continue
        if s1.coords is None or s2.coords is None:
            continue
        tot2 += 1
        same = all(abs(float(a.mid()) - float(b.mid())) < 1e-9 for a, b in zip(s1.coords, s2.coords))
        good2 += (same and fu.first_control(zq) == 1 and s1.newcell == s2.newcell)
    out['canonical face representatives: first control zeta, same image class'] = '%d / %d' % (
        good2, tot2)
    # 3. the box enclosures contain the point evaluations
    boxes = []
    for _ in range(150 if quick else 600):
        cell = rng.choice([1, 2])
        kind = rng.randrange(3)
        if kind == 0:
            r = rng.random() * 0.98
            w = 10 ** rng.uniform(-4, -1.5)
            p0 = rng.uniform(0, math.pi - 0.05)
            t0 = rng.uniform(0, math.pi - 0.05) * (1 if cell == 1 else -1)
            tt = I(min(t0, t0 + w * (1 if cell == 1 else -1)), max(t0, t0 + w * (1 if cell == 1 else -1)))
            boxes.append(rg.coord_box(cell, I(r, r + w), I(p0, p0 + w), tt))
        elif kind == 1:
            e = 10 ** rng.uniform(-6, -2)
            k = rng.uniform(0, 0.9)
            x0 = rng.uniform(0, 1.4) * (1 if cell == 1 else -1)
            boxes.append(bm.EdgeBox(cell, rng.choice([0, 2]), rng.choice('ab'), I(0, e),
                                    I(k, k + 0.1), 0, I(min(x0, x0 * 1.01), max(x0, x0 * 1.01))))
        else:
            e = 10 ** rng.uniform(-6, -2)
            p0 = rng.uniform(0.05, 3.0)
            x0 = rng.uniform(0, 1.4) * (1 if cell == 1 else -1)
            boxes.append(bm.SqrtBox(cell, I(0, e), 0, I(p0, p0 + 0.01), 0,
                                    I(min(x0, x0 * 1.01), max(x0, x0 * 1.01))))
    boxes = [b for b in boxes if b is not None]
    n, bad = cm.validate(boxes, n_per_box=3)
    out['box enclosures contain the point images'] = '%d points, %d violations' % (n, len(bad))
    out['violations'] = [repr(x[:5]) for x in bad[:5]]
    out['ok'] = (agree == tot) and (good2 == tot2) and not bad
    return out


def run_remark(quick=False):
    return remark.run()


def run_unstable(quick=False):
    return unstable_curve.run()


def _stage(domain, tgt, faces_too, required=0.0, max_depth=40):
    t0 = time.time()
    st = dout.run_into(domain, tgt, required=required, faces_too=faces_too, max_depth=max_depth)
    r = _st(st)
    r['required_margin'] = required
    return r


def run_dout(quick=False):
    out = {}
    D00 = rg.cell_box(0, 0)
    # F(D00) in D00
    rec = _stage(D00, rg.T_D00, True)
    m, p = sampled(D00, m_target(rg.T_D00), n=7 if quick else 11)
    rec['sampled_min_margin'] = m
    rec['sampled_at'] = _pt(p)
    if not quick:
        req = math.floor(0.9 * m * 1000) / 1000.0
        rr = _stage(D00, rg.T_D00, True, required=req)
        rec['certified_margin'] = req if rr['proved'] else None
        rec['certified_run'] = {k: rr[k] for k in ('proved', 'leaves', 'time')}
    out['F(D00) in D00'] = rec
    # witness routes
    routes = [
        ('recommended (BasinHypotheses.lean): N = 2 through D2', dout.B_REC, [dout.D2_REC]),
        ('wider: N = 2 through [0,0.4]x[0,0.4]x[2.5,pi] into [0.15,0.38]x[0.08,0.28]x[2.7,3.1]',
         (('0.15', '0.08', '2.7'), ('0.38', '0.28', '3.1')),
         [(('0', '0', '2.5'), ('0.4', '0.4', 'pi'))]),
    ]
    out['routes'] = []
    for name, Bw, mids in routes:
        rr = {'name': name, 'B': Bw, 'intermediate': mids, 'N': len(mids) + 1}
        chain = [D00] + [dout.box_of(x) for x in mids]
        targets = [dout.target_of(x) for x in mids] + [dout.target_of(Bw)]
        stages = []
        for k, (dom, tgt) in enumerate(zip(chain, targets)):
            s = _stage(dom, tgt, faces_too=(k == 0))
            m, p = sampled(dom, m_target(tgt), n=7 if quick else 9)
            s['sampled_min_margin'] = m
            s['sampled_at'] = _pt(p)
            stages.append(s)
        rr['stages'] = stages
        B = dout.box_of(Bw)
        TB = dout.target_of(Bw)
        s = _stage(B, TB, faces_too=False)
        m, p = sampled(B, m_target(TB), n=7 if quick else 9)
        s['sampled_min_margin'] = m
        s['sampled_at'] = _pt(p)
        rr['F(B) in B'] = s
        lip = dout.lipschitz(B, 0.5)
        rr['lipschitz kappa = 1/2'] = _st(lip)
        smax, sat = sampled_rowsum(B)
        rr['sampled max row sum of Dg'] = smax
        rr['sampled max at'] = sat
        # one attempt at a certified bound near the sampled maximum (15% above it; the Jacobian
        # enclosures need fine boxes, so closer attempts cost much more)
        best = 0.5 if lip.ok() else None
        kap = math.ceil(smax * 1.15 * 100) / 100.0
        if not quick and kap < 0.45:
            lk = dout.lipschitz(B, kap, max_depth=14)
            rr['lipschitz kappa = %.2f' % kap] = _st(lk)
            if lk.ok():
                best = kap
        rr['certified kappa'] = best
        rr['proved'] = all(x['proved'] for x in stages) and s['proved'] and lip.ok()
        out['routes'].append(rr)
    # the N = 3 route of the Lean certificates (DOutStep1-3): X1, X2, X3 in tan-half coordinates
    X1 = dout.tan_half_box(('0', '0.4'), ('0', '0.2'), ('0', '0.3'))
    X2 = dout.tan_half_box(('0.22', '0.32'), ('0.05', '0.14'), ('0.05', '0.2'))
    X3 = dout.tan_half_box(('0.252', '0.288'), ('0.077', '0.094'), ('0.088', '0.142'))
    lean = []
    for k, (dom, tgt) in enumerate([(D00, X1[1]), (X1[0], X2[1]), (X2[0], X3[1])]):
        s = _stage(dom, tgt, faces_too=(k == 0))
        m, p = sampled(dom, m_target(tgt), n=7 if quick else 9)
        s['sampled_min_margin'] = m
        s['sampled_at'] = _pt(p)
        lean.append(s)
    out['Lean route N = 3 (X1, X2, X3 of Ch16/Certificates)'] = lean
    return out


def run_subclaims(quick=False):
    out = {}
    for (i, j) in sc.BOXES:
        st = sc.run_box(i, j)
        r = _st(st)
        r['kinds'] = st.kinds
        if st.failures:
            r['failed clusters'] = _cluster(st.failures)[:20]
        b = rg.cell_box(i, j)
        m, p = sampled(b, m_subclaim(i, j), n=7 if quick else 11)
        r['sampled_min_margin'] = m
        r['sampled_at'] = _pt(p)
        out['D%d%d' % (i, j)] = r
    out['proved'] = all(v['proved'] for k, v in out.items() if k.startswith('D'))
    return out


def _cluster(failures, digits=1):
    """the failed boxes grouped by the rounded corner of their regular enclosure: (count, total
    volume, hull) per group"""
    groups = {}
    for b, info in failures:
        rb = b.regular() if not isinstance(b, bm.Box) else b
        r, p, t = rb.r, rb.psi(), rb.th2()
        key = (b.cell, round(r.lo, digits), round(p.lo, digits), round(t.lo, digits))
        g = groups.setdefault(key, [0, 0.0, [r.lo, r.hi, p.lo, p.hi, t.lo, t.hi], set()])
        g[0] += 1
        g[1] += r.width() * p.width() * t.width()
        h = g[2]
        g[2] = [min(h[0], r.lo), max(h[1], r.hi), min(h[2], p.lo), max(h[3], p.hi),
                min(h[4], t.lo), max(h[5], t.hi)]
        g[3].add(info.get('why') if isinstance(info, dict) else str(info))
    out = []
    for key, (n, vol, h, whys) in sorted(groups.items(), key=lambda kv: -kv[1][0]):
        out.append({'cell': key[0], 'count': n, 'volume': vol,
                    'r2': h[0:2], 'psi': h[2:4], 'theta2': h[4:6], 'why': sorted(whys)})
    return out


def evidence_celltwo(failures, n=2000, seed=11):
    """random points of the failed boxes (in cellTwoDomain), iterated by the point evaluator:
    how many reach D00 within 3 steps, and the smallest structural margin"""
    rng = random.Random(seed)
    if not failures:
        return None
    ok = tot = 0
    worst = (float('inf'), None)
    for _ in range(n):
        b, _info = failures[rng.randrange(len(failures))]
        p, _e = cm.sample_box(b, rng)
        if not (0 < p[0] < 1):
            continue
        try:
            v = m_celltwo(p)
        except (fu.Undecided, RuntimeError, ValueError, ZeroDivisionError, AssertionError):
            continue
        tot += 1
        if v > 0:
            ok += 1
        if v < worst[0]:
            worst = (v, _pt(p))
    return {'points': tot, 'reach D00 within 3 steps': ok, 'min structural margin': worst[0],
            'at': worst[1]}


def run_celltwo(quick=False):
    st = c2.run()
    r = _st(st)
    r['failed volume'] = sum((lambda w: w[0] * w[1] * w[2])(
        (b.regular() if not isinstance(b, bm.Box) else b).widths()) for b, _ in st.failures)
    r['failed clusters'] = _cluster(st.failures)[:30]
    r['evidence in the failed boxes'] = evidence_celltwo(st.failures, n=500 if quick else 3000)
    r['kinds'] = dict(list(st.kinds.items())[:20])
    r['min_margin_leaf'] = st.min_margin
    pts = []
    for b in c2.roots():
        pts += _grid(b, 7 if quick else 11)
    best = (float('inf'), None)
    for p in pts:
        # cellTwoDomain = (0, 1) x (0, pi) x (-pi, 0]
        if p[0] in (0.0, 1.0) or p[1].x == 0.0 or (p[2].k == -2 and p[2].x == 0.0):
            continue
        try:
            v = m_celltwo(p)
        except (fu.Undecided, RuntimeError, ValueError, ZeroDivisionError, AssertionError):
            continue
        if v < best[0]:
            best = (v, p)
    r['sampled_min_structural_margin'] = best[0]
    r['sampled_at'] = _pt(best[1])
    return r


RUNNERS = {'selftest': run_selftest, 'remark': run_remark, 'dout': run_dout,
           'subclaims': run_subclaims, 'celltwo': run_celltwo, 'unstable': run_unstable}
