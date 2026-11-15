"""Shared pieces of the checks: one-step leaves, sampling of the true margins, and the empirical
validation of the box enclosures against the point evaluator."""
import random

from .. import boxmap as bm
from .. import fuller as fu


def refine_outcome(b, o, u):
    """intersect the coordinates of a single-branch outcome on a Box with its mean value form"""
    if o.tie or o.img is None or not isinstance(b, bm.Box):
        return o
    try:
        mv = bm.image_mv(b, o, u)
    except ZeroDivisionError:
        mv = None
    if mv:
        im = o.img
        im.r2 = (im.r2.intersect(mv[0]) or im.r2) if im.r2 is not None else mv[0]
        im.psi = (im.psi.intersect(mv[1]) or im.psi) if im.psi is not None else mv[1]
        im.th2 = (im.th2.intersect(mv[2]) or im.th2) if im.th2 is not None else mv[2]
        o.kind = o.kind + '+mv'
    return o


def leaf_into(margin_fn, required=0.0, mv=True, allow_dual=True):
    """leaf for 'F(box) lies in the target': every outcome of the step must have
    margin_fn(o) > required"""
    def leaf(b):
        try:
            outs = bm.step(b, allow_dual=allow_dual)
        except ZeroDivisionError:
            outs = None
        if outs is None:
            return False, None, {'why': 'no certificate'}
        worst = float('inf')
        kinds = []
        for o in outs:
            m = margin_fn(o)
            if m <= required and mv and len(outs) == 1:
                o = refine_outcome(b, o, b.cell)
                m = margin_fn(o)
            kinds.append(o.kind)
            worst = min(worst, m)
        if worst > required:
            return True, worst, {'kind': '/'.join(kinds) + ('(dual)' if len(outs) > 1 else '')}
        return False, None, {'why': 'margin', 'm': worst}
    return leaf


def point_image(p):
    """the honest image of cellClass p (p = (r2, psi, theta2), floats or fuller.Angle) by the point
    evaluator: (cell, (r2', psi', theta2') as floats, Step), or None for a face class"""
    s = fu.step_coords(p)
    if s.coords is None:
        return None
    return s.newcell, tuple(float(x.mid()) for x in s.coords), s


def sample_box(b, rng):
    """a random point of the Box or EdgeBox b, as cell coordinates (Angles with the anchors), and
    the scale eps of the box at that point"""
    if isinstance(b, bm.EdgeBox):
        e = rng.uniform(b.eps.lo, b.eps.hi)
        k = rng.uniform(b.kap.lo, b.kap.hi)
        r2, al = (e, e * k) if b.chart == 'a' else (e * k, e)
        x2 = rng.uniform(b.x2.lo, b.x2.hi)
        psi = fu.Angle(0, al) if b.edge == 0 else fu.Angle(2, -al)
        return (r2, psi, fu.Angle(b.k2, x2)), e
    if isinstance(b, bm.SqrtBox):
        e = rng.uniform(b.eps.lo, b.eps.hi)
        xp = rng.uniform(b.xp.lo, b.xp.hi)
        x2 = rng.uniform(b.x2.lo, b.x2.hi)
        return (e * e, fu.Angle(b.kp, xp), fu.Angle(b.k2, x2)), e
    r = rng.uniform(b.r.lo, b.r.hi)
    xp = rng.uniform(b.xp.lo, b.xp.hi)
    x2 = rng.uniform(b.x2.lo, b.x2.hi)
    return (r, fu.Angle(b.kp, xp), fu.Angle(b.k2, x2)), 1.0


def validate(boxes, n_per_box=2, seed=0):
    """empirical soundness test: random points of the given boxes (with the cell's first control)
    evaluated by the point evaluator must lie in the enclosures of the box step. Returns
    (number of points tested, list of violations)."""
    rng = random.Random(seed)
    bad = []
    n = 0
    for b in boxes:
        try:
            outs = bm.step(b)
        except ZeroDivisionError:
            outs = None
        if outs is None:
            continue
        for _ in range(n_per_box):
            p, eps = sample_box(b, rng)
            if eps == 0:
                continue
            try:
                z = fu.cell_point(*p)
                if fu.first_control(z) != b.cell:
                    continue
                s = fu.Step(z)
            except (fu.Undecided, RuntimeError, ValueError):
                continue
            if s.coords is None:
                continue
            q = [float(x.mid()) for x in s.coords]
            n += 1
            tau = float(s.t.mid()) / eps
            okb = False
            for o in outs:
                if o.w != s.j or o.cell != s.newcell:
                    continue
                if not (o.T.lo * (1 - 1e-9) - 1e-12 <= tau <= o.T.hi * (1 + 1e-9) + 1e-12):
                    continue
                good = True
                for x, X in zip(q, (o.r2, o.psi, o.th2)):
                    if X is not None and not (X.lo - 1e-12 <= x <= X.hi + 1e-12):
                        good = False
                if good:
                    okb = True
            if not okb:
                bad.append((b, p, s.j, float(s.t.mid()), q, outs))
    return n, bad


def minimize_margin(f, x0, steps, lo, hi, iters=60):
    """a crude local minimization (coordinate pattern search) of f on the box [lo, hi]"""
    x = list(x0)
    fx = f(x)
    st = list(steps)
    for _ in range(iters):
        improved = False
        for k in range(len(x)):
            for sg in (1, -1):
                y = list(x)
                y[k] = min(max(y[k] + sg * st[k], lo[k]), hi[k])
                fy = f(y)
                if fy < fx:
                    x, fx, improved = y, fy, True
        if not improved:
            st = [s * 0.5 for s in st]
            if max(st) < 1e-12:
                break
    return fx, x
