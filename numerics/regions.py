"""The regions of Chapters 15-16 as boxes of cell coordinates, and the targets of the checks.

Lean: ``basinA``, ``basinB``, ``cellBox``, ``boxSet``, ``BoxLexLt`` (``Ch16/BasinHypotheses.lean``),
``closedBoxOne``, ``openBoxOne``, ``cellTwoDomain`` (``Ch15/CellCoordinates.lean``).

* ``a = (0, pi/3, 2pi/3, pi)`` (the ``psi``-breakpoints), ``b = (pi, pi - 1.1, 1.1, 0)`` (the
  ``theta2``-breakpoints); ``cellBox i j = [0, 1] x [a_i, a_{i+1}] x [b_{j+1}, b_j]``;
* ``D00 = cellBox 0 0`` is ``D_out``; the second big cell is ``cellTwoDomain``
  ``= (0, 1) x (0, pi) x (-pi, 0]``.

Domain boxes are outer enclosures (every point of the true box lies in the interval box), with the
faces at ``0``, ``1``, ``0``, ``+-pi`` exact through the anchors of ``boxmap.Box``; target boxes are
inner enclosures (the comparison uses the side of each breakpoint's enclosure that makes the test
conservative).
"""
from .iv import I, PI, HALF_PI, const
from .boxmap import Box

PI3 = PI / 3.0
TWO_PI3 = PI * 2.0 / 3.0
C11 = const('1.1')
PI_M11 = PI - C11

# breakpoints as intervals
A = [I(0.0), PI3, TWO_PI3, PI]
B = [PI, PI_M11, C11, I(0.0)]


def psi_range(i):
    """(anchor, offset interval) covering [a_i, a_{i+1}]"""
    if i == 0:
        return 0, I(0.0, PI3.hi)
    if i == 1:
        return 0, I(PI3.lo, TWO_PI3.hi)
    return 2, I(-(PI3.hi), 0.0)          # psi = pi + x, x in [-pi/3, 0]


def th2_range(j):
    """(anchor, offset interval) covering [b_{j+1}, b_j]"""
    if j == 0:
        return 2, I(-(C11.hi), 0.0)      # theta2 = pi + x, x in [-1.1, 0]
    if j == 1:
        return 0, I(C11.lo, PI_M11.hi)
    return 0, I(0.0, C11.hi)


def cell_box(i, j):
    kp, xp = psi_range(i)
    k2, x2 = th2_range(j)
    return Box(1, I(0.0, 1.0), kp, xp, k2, x2)


def coord_box(cell, r2, psi, th2):
    """a Box from coordinate intervals (r2, psi, theta2) in the closed cell, with anchors chosen
    near the faces; the intervals are clipped to the closed cell (valid when the true points lie in
    it)"""
    r = r2.intersect(I(0.0, 1.0))
    p = psi.intersect(I(0.0, PI.hi))
    if cell == 1:
        t = th2.intersect(I(0.0, PI.hi))
    else:
        t = th2.intersect(I(-PI.hi, 0.0))
    if r is None or p is None or t is None:
        return None
    # psi anchor
    if p.lo > HALF_PI.hi:
        kp, xp = 2, (p - PI)
        xp = I(xp.lo, min(xp.hi, 0.0))
    else:
        kp, xp = 0, I(max(p.lo, 0.0), p.hi)
    if cell == 1:
        if t.lo > HALF_PI.hi:
            k2, x2 = 2, (t - PI)
            x2 = I(x2.lo, min(x2.hi, 0.0))
        else:
            k2, x2 = 0, I(max(t.lo, 0.0), t.hi)
    else:
        if t.hi < -HALF_PI.hi:
            k2, x2 = -2, (t + PI)
            x2 = I(max(x2.lo, 0.0), x2.hi)
        else:
            k2, x2 = 0, I(t.lo, min(t.hi, 0.0))
    return Box(cell, r, kp, xp, k2, x2)


# ---- targets ----------------------------------------------------------------------------------------
def margin_box(cell, r2, psi, th2, tgt):
    """the margin (a lower bound, over the enclosure) of the image (cell, r2, psi, th2) in the target
    box tgt = (cell, (r_lo, r_hi), (p_lo, p_hi), (t_lo, t_hi)) of intervals (None: no bound);
    positive iff the enclosure lies inside the target with that margin (sup-distance to the faces of
    the target that are bounds)."""
    tc, rr, pp, tt = tgt
    if cell != tc:
        return -1.0
    m = float('inf')
    for x, (lo, hi) in ((r2, rr), (psi, pp), (th2, tt)):
        if x is None:
            if lo is not None or hi is not None:
                return -float('inf')
            continue
        if lo is not None:
            m = min(m, x.lo - lo.hi)
        if hi is not None:
            m = min(m, hi.lo - x.hi)
    return m


# D_out = D00 as a target: psi <= pi/3, theta2 >= pi - 1.1 in the first cell
T_D00 = (1, (None, None), (None, PI3), (PI_M11, None))


def target_box(lo, hi):
    """the target Icc lo hi (decimal strings), in the first cell"""
    return (1, (const(lo[0]), const(hi[0])), (const(lo[1]), const(hi[1])),
            (const(lo[2]), const(hi[2])))


def domain_box(lo, hi):
    """the domain Icc lo hi (decimal strings) as a Box of the first cell (outer enclosure)"""
    l = [const(x) for x in lo]
    h = [const(x) for x in hi]
    return coord_box(1, I(l[0].lo, h[0].hi), I(l[1].lo, h[1].hi), I(l[2].lo, h[2].hi))


def box_lex_lt(k, l, i, j):
    return k < i or (k == i and l < j)


def subclaim_margin(i, j, r2, psi, th2):
    """BoxSubclaims, an image in the first cell: in some cellBox k l with (k, l) < (i, j)
    lexicographically, i.e. psi' <= a_i (k < i), or psi' <= a_{i+1} and theta2' >= b_j (k = i,
    l < j). Returns a lower bound of the margin (the better of the two alternatives)."""
    best = -float('inf')
    if psi is None:
        return best
    if i > 0:
        best = max(best, A[i].lo - psi.hi)
    if j > 0 and th2 is not None:
        best = max(best, min(A[i + 1].lo - psi.hi, th2.lo - B[j].hi))
    return best
