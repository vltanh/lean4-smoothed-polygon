"""Blow-up charts of the edges ``{r2 = 0, psi in {0, pi}}`` where the cell's control is not the first
control of the edge points.

On the face ``r2 = 0`` the cell point is ``(e^{i theta1}, 0, 0)``; its first control is the vertex of
``V_T`` nearest to ``e^{i theta1}`` (``faces.py``). Where that is not the cell's control, the
switching time tends to ``0`` at the face, and near the edges ``psi in {0, pi}`` (where also
``z3 = -2 r1 r2 sin psi`` vanishes, to second order) the regular box enclosures of ``boxmap``
degenerate: the root equation does not determine ``r2/t`` (its denominator ``r1 sin psi`` vanishes).
There the box is replaced by the two charts of ``boxmap.EdgeBox`` (``r2 = eps``, ``alpha = eps kap``
and ``alpha = eps``, ``r2 = eps kap``, with ``alpha = psi`` or ``pi - psi``), in which the scaled
cubic, the scaled flow and the image are uniform up to ``eps = 0``.

Near the face ``r2 = 0`` where it meets ``theta2 = 0`` (the switch to the eventual winner takes a time
of order ``sqrt(r2)``, the other one a time of order ``r2``), a thin box is replaced by the chart
``boxmap.SqrtBox`` (``r2 = eps^2``, time ``t/eps``).
"""
from .iv import I, PI
from .boxmap import Box, EdgeBox, SqrtBox
from .iv import sqrt_hi
from .regions import PI3

TWO_PI = PI * 2.0


def correct_sector(cell):
    """the arc of theta1 (mod 2pi) where the cell's control is the first control of
    (e^{i theta1}, 0, 0): (pi/3, pi] for zeta, (-pi, -pi/3] for zeta^2"""
    return (PI3, PI) if cell == 1 else (-PI, -PI3)


def edge_theta1(b, edge):
    """theta1 = theta2 - psi at the edge psi = 0 (edge 0) or psi = pi (edge 2), as an interval"""
    t = b.th2() if isinstance(b, Box) else b.th2()
    return t if edge == 0 else t - PI


def sector_status(cell, th1):
    """'wrong' if the cell's control is not the first control at every point of the arc th1 (an
    interval), 'right' if it is at every point, 'mixed' otherwise (enclosure-safe)"""
    lo, hi = correct_sector(cell)
    meets = False
    inside = False
    for k in (-2.0, -1.0, 0.0, 1.0, 2.0):
        a = lo + TWO_PI * k
        b = hi + TWO_PI * k
        # the correct arc (a, b]
        if th1.hi > a.lo and th1.lo <= b.hi:
            meets = True
        if th1.lo > a.hi and th1.hi <= b.lo:
            inside = True
    if inside:
        return 'right'
    if not meets:
        return 'wrong'
    return 'mixed'


def which_edge(b):
    """0 or 2 if the Box b touches the edge {r2 = 0, psi = 0} or {r2 = 0, psi = pi}, else None"""
    if not isinstance(b, Box) or b.r.lo != 0.0:
        return None
    if b.kp == 0 and b.xp.lo == 0.0:
        return 0
    if b.kp == 2 and b.xp.hi == 0.0:
        return 2
    return None


def edge_cover(b, eps0):
    """the two charts covering the Box b near its edge (a superset of b), when b is small
    (r2 <= eps0, alpha <= eps0) and the cell's control is wrong on the whole edge segment;
    else None"""
    e = which_edge(b)
    if e is None or b.r.hi > eps0:
        return None
    al_hi = b.xp.hi if e == 0 else -b.xp.lo
    if al_hi > eps0:
        return None
    if sector_status(b.cell, edge_theta1(b, e)) != 'wrong':
        return None
    return [EdgeBox(b.cell, e, 'a', I(0.0, b.r.hi), I(0.0, 1.0), b.k2, b.x2),
            EdgeBox(b.cell, e, 'b', I(0.0, al_hi), I(0.0, 1.0), b.k2, b.x2)]


def sqrt_cover(b, r0):
    """the chart r2 = eps^2 (boxmap.SqrtBox) covering the Box b when b touches the face r2 = 0, is
    thin there (r2 <= r0), and the cell's control is wrong on the face segment of b; else None"""
    if not isinstance(b, Box) or b.r.lo != 0.0 or b.r.hi > r0:
        return None
    if sector_status(b.cell, b.th2() - b.psi()) != 'wrong':
        return None
    return [SqrtBox(b.cell, I(0.0, sqrt_hi(b.r.hi)), b.kp, b.xp, b.k2, b.x2)]


def with_edges(leaf, eps0=1.0 / 64, r0=2.0 ** -8):
    """wrap a leaf: a failing small Box at a wrong-control edge is replaced by its two charts, and a
    failing thin Box at a wrong-control part of the face r2 = 0 by its sqrt chart"""
    def lf(b):
        ok, val, info = leaf(b)
        if ok:
            return ok, val, info
        if isinstance(b, Box):
            cov = edge_cover(b, eps0)
            if cov is not None:
                return False, cov, {'why': 'replaced by the edge charts'}
            cov = sqrt_cover(b, r0)
            if cov is not None:
                return False, cov, {'why': 'replaced by the sqrt chart'}
        return ok, val, info
    return lf
