"""``CellTwoEntersDOut`` (``SmoothedPolygons/Ch16/BasinHypotheses.lean``):

    ∀ x ∈ cellTwoSet, ∃ n ≤ 3, poincareAngZero^[n] x ∈ boxSet 0 0

``cellTwoSet = cellClass '' cellTwoDomain``, ``cellTwoDomain = (0, 1) x (0, pi) x (-pi, 0]``: the open
second cell and its top face ``theta2 = 0``, where the first control is ``zeta^2``. The closed cell
``[0, 1] x [0, pi] x [-pi, 0]`` is covered by boxes; a box certificate covers its points with first
control ``zeta^2``, which include all of ``cellTwoDomain`` (``theta2 = -pi`` and the faces
``r2 in {0, 1}``, ``psi in {0, pi}`` are not in the domain and need no treatment).

The proof is a set-oriented iteration (``prove_box(X, k)``: every point of ``X`` with the cell's first
control reaches ``D00`` within ``3 - k`` more steps):

* if ``k > 0`` and the box ``X`` lies in ``D00`` (``psi <= pi/3``, ``theta2 >= pi - 1.1`` in the
  first cell), done;
* if ``k = 3``, fail;
* else one certified step (``boxmap.step``) gives the outcomes (the image cell and coordinate
  enclosures of each possible branch); each image enclosure becomes a box ``Y`` of the next step
  (a regular box, or blow-up charts near a wrong-control edge), and ``Y`` is proved at level
  ``k + 1`` by a bounded subdivision. If that fails, ``X`` is split.

The images of points of the open cell lie in the open part of their cell (``x3 < 0``), so at later
steps the first control of every relevant point is its cell's control and the box certificates
apply. A dual outcome (a possible tie ``z3(t_sw) = 0``, whose image is a face class) is recorded:
the iteration of such a face class from its representative in the enclosure is covered only if
that representative has the cell's first control (see the report of the run for the count).
"""
from ..iv import I, PI
from .. import boxmap as bm
from .. import regions as rg
from .. import driver
from ..edges import edge_cover, sector_status
from .common import refine_outcome

EPS0 = 1.0 / 64
MAX_SUB = 8         # subdivision depth of an image box at the next level
YMAX = 0.3          # the widest image box passed to the next level
BUDGET = 600        # steps per top-level box before it is split instead


def in_d00(b):
    """the box (regular enclosure) lies in D00"""
    if b.cell != 1:
        return False
    rb = b.regular() if isinstance(b, bm.EdgeBox) else b
    p, t = rb.psi(), rb.th2()
    return p.hi < rg.PI3.lo and t.lo > rg.PI_M11.hi


def margin_d00(b):
    rb = b.regular() if isinstance(b, bm.EdgeBox) else b
    if rb.cell != 1:
        return -1.0
    p, t = rb.psi(), rb.th2()
    return min(rg.PI3.lo - p.hi, t.lo - rg.PI_M11.hi)


def image_boxes(o):
    """the boxes of the next step covering the image enclosure of the outcome o"""
    im = o.img
    if im is None or im.psi is None or im.th2 is None or im.r2 is None:
        return None
    cell = o.cell
    boxes = []
    near = (im.side is not None and im.A is not None and im.R is not None and im.r2.hi <= EPS0
            and (im.eps * im.A).hi <= EPS0)
    if near:
        e = im.side
        th = im.th2.intersect(rg.I(0.0, PI.hi) if cell == 1 else rg.I(-PI.hi, 0.0))
        if th is None:
            return None
        tb = rg.coord_box(cell, I(0.0, 0.0), I(0.0, 0.0), th)
        # the edge segment theta1 at r2 = 0
        th1 = th if e == 0 else th - PI
        if sector_status(cell, th1) == 'wrong':
            R, A, eps = im.R, im.A, im.eps
            if A.lo <= R.hi and R.lo > 0:
                ka = (A / R).intersect(I(0.0, 1.0))
                if ka is not None:
                    boxes.append(bm.EdgeBox(cell, e, 'a', (eps * R).intersect(I(0.0, 1.0)) or
                                            eps * R, ka, tb.k2, tb.x2))
            if R.lo <= A.hi and A.lo > 0:
                kb = (R / A).intersect(I(0.0, 1.0))
                if kb is not None:
                    boxes.append(bm.EdgeBox(cell, e, 'b', eps * A, kb, tb.k2, tb.x2))
            if boxes:
                return boxes
    b = rg.coord_box(cell, im.r2, im.psi, im.th2)
    return [b] if b is not None else None


TWO_PI3 = PI * 2.0 / 3.0


def _canon_theta(Th):
    """the parts of {theta + 2 pi k/3 : theta in Th} in the canonical arc [pi/3, pi] (outer)"""
    out = []
    for k in range(-6, 7):
        sh = Th + TWO_PI3 * float(k) if k else Th
        c = sh.intersect(I(rg.PI3.lo, PI.hi))
        if c is not None:
            out.append(c)
    return out


def tie_boxes(o):
    """the canonical representatives (cell-one faces, first control zeta) of the face classes that
    are images at a tie (z3(t_sw) = 0): the image enclosure of the branch formula gives a
    representative with x3 = 0, so psi' = 0 or pi (mod 2 pi) or r2' in {0, 1}; its class is that
    of the face point rotated into theta in (pi/3, pi] (faces.py). None if not computable."""
    im = o.img
    if im is None or im.psi is None or im.th2 is None or im.r2 is None:
        return None
    R, Ps, Th = im.r2, im.psi, im.th2
    out = []
    for face_psi, kp in ((0.0, 0), (PI, 2)):
        for m in (-2.0, 0.0, 2.0):
            target = (PI * m + face_psi) if isinstance(face_psi, I) else (PI * m if m else I(0.0))
            if isinstance(target, float):
                target = I(target)
            if Ps.hi >= target.lo and Ps.lo <= target.hi:
                r = R.intersect(I(0.0, 1.0))
                if r is None:
                    continue
                for th in _canon_theta(Th):
                    b = rg.coord_box(1, r, I(0.0) if kp == 0 else PI, th)
                    if b is not None:
                        b = bm.Box(1, b.r, kp, I(0.0), b.k2, b.x2)
                        out.append(b)
    if R.lo <= 0.0:
        for th in _canon_theta(Th - Ps):
            b = rg.coord_box(1, I(0.0), I(0.0), th)
            if b is not None:
                out.append(bm.Box(1, I(0.0), 0, I(0.0), b.k2, b.x2))
    if R.hi >= 1.0:
        for th in _canon_theta(Th):
            b = rg.coord_box(1, I(1.0), I(0.0), th)
            if b is not None:
                out.append(bm.Box(1, I(1.0), 0, I(0.0), b.k2, b.x2))
    return out


class Ctx:
    def __init__(self):
        self.steps = 0
        self.duals = 0
        self.ties = 0
        self.budget = BUDGET
        self.min_margin = float('inf')
        self.min_box = None


def prove_box(X, k, ctx, depth=0):
    if k > 0 and in_d00(X):
        m = margin_d00(X)
        if m < ctx.min_margin:
            ctx.min_margin, ctx.min_box = m, X
        return True
    if k >= 3:
        return False
    ctx.budget -= 1
    if ctx.budget < 0:
        return False
    try:
        outs = bm.step(X)
    except ZeroDivisionError:
        outs = None
    ctx.steps += 1
    if outs is None:
        return False
    if len(outs) > 1:
        ctx.duals += 1
    for o in outs:
        if len(outs) == 1 and isinstance(X, bm.Box):
            refine_outcome(X, o, X.cell)
        Ys = image_boxes(o)
        if Ys is None:
            return False
        if o.tie:
            tb = tie_boxes(o)
            if tb is None:
                return False
            ctx.ties += len(tb)
            Ys = Ys + tb
        for Y in Ys:
            if in_d00(Y):
                m = margin_d00(Y)
                if m < ctx.min_margin:
                    ctx.min_margin, ctx.min_box = m, Y
                continue
            if k + 1 >= 3 or max(_reg_widths(Y)) > YMAX:
                return False        # not in D00 after the last step, or too wide: split X
            if not prove_set(Y, k + 1, ctx):
                return False
    return True


def _reg_widths(Y):
    rb = Y.regular() if isinstance(Y, bm.EdgeBox) else Y
    w = rb.widths()
    return (w[0] * 2.0, w[1], w[2])


import math as _math

_CACHE = {}       # dyadic box key -> the largest level k at which it is proved (per process)
_FAIL = {}        # dyadic box key -> the smallest level k at which it failed
FRAMES = {0: (0.0, 1.0), 1: (0.0, 4.0), 2: {1: (0.0, 4.0), 2: (-4.0, 0.0)}}


def _frame(axis, cell):
    f = FRAMES[axis]
    return f[cell] if axis == 2 else f


def _dyadic_cover(lo, hi, L, U):
    """at most two dyadic intervals of the frame [L, U], of length >= hi - lo, covering [lo, hi]"""
    w = max(hi - lo, (U - L) * 2.0 ** -40)
    n = max(0, int(_math.floor(_math.log2((U - L) / w))))
    sz = (U - L) / 2.0 ** n
    i0 = int(_math.floor((lo - L) / sz))
    i1 = int(_math.floor((hi - L) / sz))
    i0 = max(0, min(i0, 2 ** n - 1))
    i1 = max(0, min(i1, 2 ** n - 1))
    return [(n, i) for i in range(i0, i1 + 1)]


def _dyadic_iv(axis, cell, n, i):
    L, U = _frame(axis, cell)
    sz = (U - L) / 2.0 ** n
    return I(L + sz * i, L + sz * (i + 1))


def _dyadic_box(key):
    cell, (nr, ir), (np_, ip), (nt, it) = key
    return rg.coord_box(cell, _dyadic_iv(0, cell, nr, ir), _dyadic_iv(1, cell, np_, ip),
                        _dyadic_iv(2, cell, nt, it))


def prove_dyadic(key, k, ctx, depth=0):
    if _CACHE.get(key, -1) >= k:
        return True
    Y = _dyadic_box(key)
    ok = Y is not None and prove_box(Y, k, ctx)
    if not ok and Y is not None and depth < MAX_SUB:
        cov = edge_cover(Y, EPS0)
        if cov is not None:
            ok = all(prove_set(c, k, ctx, depth + 1) for c in cov)
        else:
            cell, kr, kp, kt = key
            w = Y.widths()
            ax = max(range(3), key=lambda a: (w[0] * 2.0, w[1], w[2])[a])
            n, i = (kr, kp, kt)[ax]
            kids = []
            for c in (2 * i, 2 * i + 1):
                kk = [kr, kp, kt]
                kk[ax] = (n + 1, c)
                kids.append((cell,) + tuple(kk))
            ok = all(prove_dyadic(kid, k, ctx, depth + 1) for kid in kids)
    if ok:
        _CACHE[key] = max(_CACHE.get(key, -1), k)
    return ok


def prove_set(Y, k, ctx, depth=0):
    """every point of Y (with the cell's first control) reaches D00 within 3 - k steps; regular
    boxes are covered by cached dyadic boxes"""
    if isinstance(Y, bm.Box):
        if k > 0 and in_d00(Y):
            return prove_box(Y, k, ctx)
        cell = Y.cell
        covs = []
        for ax, x in enumerate((Y.r, Y.psi(), Y.th2())):
            L, U = _frame(ax, cell)
            covs.append(_dyadic_cover(x.lo, x.hi, L, U))
        for kr in covs[0]:
            for kp in covs[1]:
                for kt in covs[2]:
                    if not prove_dyadic((cell, kr, kp, kt), k, ctx):
                        return False
        return True
    if prove_box(Y, k, ctx):
        return True
    if depth >= MAX_SUB:
        return False
    a, b = Y.split(driver.default_axis(Y))
    return prove_set(a, k, ctx, depth + 1) and prove_set(b, k, ctx, depth + 1)


def leaf(X):
    ctx = Ctx()
    ok = prove_box(X, 0, ctx)
    if ok:
        return True, ctx.min_margin, {'kind': ('with ties' if ctx.ties else ('two branches' if ctx.duals else 'single branches')),
                                      'steps': ctx.steps, 'min_box': repr(ctx.min_box)}
    cov = edge_cover(X, EPS0) if isinstance(X, bm.Box) else None
    if cov is not None:
        return False, cov, {'why': 'replaced by the edge charts'}
    return False, None, {'why': 'not proved', 'steps': ctx.steps}


def roots():
    """the closed second cell, in four boxes with anchors at the faces"""
    h = PI * 0.5
    out = []
    for kp, xp in ((0, I(0.0, h.hi)), (2, I(-h.hi, 0.0))):
        for k2, x2 in ((0, I(-h.hi, 0.0)), (-2, I(0.0, h.hi))):
            out.append(bm.Box(2, I(0.0, 1.0), kp, xp, k2, x2))
    return out


def run(jobs=None, presplit=6, max_depth=18, time_limit=120):
    return driver.run(roots(), leaf, max_depth=max_depth, jobs=jobs, presplit=presplit,
                      max_fail=10 ** 7, time_limit=time_limit)
