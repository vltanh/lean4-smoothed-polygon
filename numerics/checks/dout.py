"""``DOutContracts`` (``SmoothedPolygons/Ch16/BasinHypotheses.lean``):

    MapsTo poincareAngZero (boxSet 0 0) (boxSet 0 0) ∧
      ∃ lo hi N κ, κ < 1 ∧ Icc lo hi ⊆ openBoxOne ∧
        (∀ x ∈ boxSet 0 0, poincareAngZero^[N] x ∈ cellClass '' Icc lo hi) ∧
        ∃ g, MapsTo g (Icc lo hi) (Icc lo hi) ∧ LipschitzOnWith κ g (Icc lo hi) ∧
          ∀ p ∈ Icc lo hi, poincareAngZero (cellClass p) = cellClass (g p)

The checks:

* ``maps_to``: ``F(D00) ⊆ D00``, by one-step certificates on a subdivision of ``D00`` (faces
  included: the wrong-control face piece ``r2 = 0, theta1 <= pi/3`` has canonical representatives in
  ``D00`` itself, ``faces.py``). The margin is the sup-distance of the image to the two inner faces
  ``psi = pi/3``, ``theta2 = pi - 1.1`` (the other faces of ``D00`` are walls of the cell, where the
  image cannot go: the image lies in the open first cell by the switch structure).
* ``into(X, Y)``: ``F(X) ⊆ Y`` for boxes ``X``, ``Y`` (the chain ``F^N(D00) ⊆ B`` through
  intermediate boxes, and ``F(B) ⊆ B``); the margin is the sup-distance to the six faces of ``Y``.
  Only the images of points of the open cell enter a later step (the image of every point has
  ``x3 < 0``), and on the open cell the first control is ``zeta``, so no face treatment is needed
  after the first step.
* ``lipschitz(B)``: on ``B`` the map is one branch (switch to ``1`` at the simple root of ``chi_A``),
  ``g`` = that branch in coordinates, with ``dD/dt > 0``; the Jacobian of ``g`` is enclosed through
  the implicit root (``boxmap.jacobian``), and the sup-norm Lipschitz constant on the convex box is
  bounded by the maximal row sum of ``|Dg|`` (mean value inequality).
"""
from ..iv import I, const
from .. import boxmap as bm
from .. import regions as rg
from .. import driver
from .. import faces
from ..edges import with_edges
from .. import fuller as fu
from .common import leaf_into, point_image

# the recommended witnesses (BasinHypotheses.lean)
B_REC = (('0.25', '0.15', '2.85'), ('0.29', '0.19', '2.98'))
# the intermediate box of the two-step route (notes/briefs/l5_numerics_report.md)
D2_REC = (('0', '0', '2.72'), ('0.28', '0.2', 'pi'))
# wider witnesses (notes/cv/py/stages.py, WIDE)
B_WIDE = (('0.2', '0.12', '2.8'), ('0.33', '0.22', '3.02'))
D2_WIDE = (('0', '0', '2.7'), ('0.3', '0.22', 'pi'))


def _c(s):
    from ..iv import PI
    return PI if s == 'pi' else const(s)


def box_of(lohi):
    lo, hi = lohi
    l = [_c(x) for x in lo]
    h = [_c(x) for x in hi]
    return rg.coord_box(1, I(l[0].lo, h[0].hi), I(l[1].lo, h[1].hi), I(l[2].lo, h[2].hi))


def target_of(lohi):
    """the target box of the first cell; the bounds that are walls of the cell (r2 in {0, 1},
    psi in {0, pi}, theta2 in {0, pi}) are dropped: the image of a point lies in the open cell, so
    they need no margin"""
    lo, hi = lohi
    walls_lo = ('0', '0', '0')
    walls_hi = ('1', 'pi', 'pi')
    return (1,) + tuple((None if lo[k] == walls_lo[k] else _c(lo[k]),
                         None if hi[k] == walls_hi[k] else _c(hi[k])) for k in range(3))


def tan_half_box(r, a, b):
    """the cell coordinates of r2 in r, tan(psi/2) in a, tan((pi - theta2)/2) in b (rational
    endpoints as strings), the coordinates of the Lean certificates (DOutImageBounds.lean)"""
    from ..iv import atan, PI
    A = [atan(const(x)) * 2.0 for x in a]
    Bq = [atan(const(x)) * 2.0 for x in b]
    R = [const(x) for x in r]
    # outer box: psi in [2 atan a0, 2 atan a1], theta2 in [pi - 2 atan b1, pi - 2 atan b0]
    box = rg.coord_box(1, I(R[0].lo, R[1].hi), I(A[0].lo, A[1].hi),
                       I((PI - Bq[1]).lo, (PI - Bq[0]).hi))
    # inner target; the bounds at the walls r2 = 0, psi = 0, theta2 = pi are dropped (no margin
    # is needed there: images lie in the open cell)
    tgt = (1, (None if r[0] == '0' else R[0], R[1]), (None if a[0] == '0' else A[0], A[1]),
           (PI - Bq[1], None if b[0] == '0' else PI - Bq[0]))
    return box, tgt


def tgt_margin(tgt):
    def f(o):
        return rg.margin_box(o.cell, o.r2, o.psi, o.th2, tgt)
    return f


def roots_with_faces(box):
    """the box and the canonical representatives of its wrong-control face points"""
    rs = [box]
    for desc, fb in faces.wrong_control_pieces(box):
        rs.append(fb)
    return rs


def run_into(domain, tgt, required=0.0, jobs=None, presplit=6, faces_too=True, max_depth=40):
    roots = roots_with_faces(domain) if faces_too else [domain]
    leaf = with_edges(leaf_into(tgt_margin(tgt), required))
    return driver.run(roots, leaf, max_depth=max_depth, jobs=jobs, presplit=presplit)


def maps_to(required=0.0, jobs=None):
    return run_into(rg.cell_box(0, 0), rg.T_D00, required, jobs)


# ---- the Lipschitz bound --------------------------------------------------------------------------
def lipschitz_leaf(kappa):
    def leaf(b):
        outs = bm.step(b)
        if outs is None or len(outs) != 1:
            return False, None, {'why': 'no single branch'}
        Jm = bm.jacobian(b, outs[0], 1)
        if Jm is None:
            return False, None, {'why': 'no jacobian'}
        rows = [sum(x.mag() for x in row) for row in Jm]
        m = max(rows)
        if m <= kappa:
            # report the margin kappa - (row sum bound), and the bound itself
            return True, kappa - m, {'kind': 'jac', 'rowsum': m}
        return False, None, {'why': 'rowsum', 'rowsum': m}
    return leaf


def lipschitz(B, kappa=0.5, jobs=None, presplit=6, max_depth=30):
    st = driver.run([B], lipschitz_leaf(kappa), max_depth=max_depth, jobs=jobs,
                    presplit=presplit, max_fail=1)
    return st


# ---- sampled margins (upper bounds of the true minimal margins, with the location) ------------
def sampled_margin_into(domain_pts, tgt, refine=True):
    """the smallest margin over the given points (cell coordinate triples) of their images in the
    target, with a local refinement; returns (margin, point, image)"""
    def mfun(p):
        try:
            res = point_image(p)
        except (fu.Undecided, RuntimeError):
            return float('inf')
        if res is None:
            return float('inf')
        cell, q, _ = res
        return rg.margin_box(cell, I(q[0]), I(q[1]), I(q[2]), tgt)
    best = (float('inf'), None)
    for p in domain_pts:
        m = mfun(p)
        if m < best[0]:
            best = (m, p)
    return best, mfun


def grid_points(box, n):
    """an n^3 grid of points of the closed box, as cell coordinates with the anchors of the box
    (faces included exactly)"""
    pts = []
    r, xp, x2 = box.r, box.xp, box.x2
    for i in range(n):
        for j in range(n):
            for k in range(n):
                pts.append((r.lo + (r.hi - r.lo) * i / (n - 1),
                            fu.Angle(box.kp, xp.lo + (xp.hi - xp.lo) * j / (n - 1)),
                            fu.Angle(box.k2, x2.lo + (x2.hi - x2.lo) * k / (n - 1))))
    return pts
