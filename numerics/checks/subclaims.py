"""``BoxSubclaims`` (``SmoothedPolygons/Ch16/BasinHypotheses.lean``):

    ∀ i j : Fin 3, (i, j) ≠ (0, 0) → (i, j) ≠ (2, 2) → ∀ x ∈ boxSet i j, x ∉ cellTwoSet →
      poincareAngZero x ∈ cellTwoSet ∨ ∃ k l, BoxLexLt k l i j ∧ poincareAngZero x ∈ boxSet k l

For each of the seven boxes ``D_ij``, on a subdivision of the closed box (and of the canonical
representatives of its wrong-control face points, ``faces.py``; the face ``theta2 = 0`` of the boxes
``D_i2`` lies in ``cellTwoSet`` and is excluded by the hypothesis), each leaf certifies one of:

* the switch to ``zeta^2`` (the first control is ``zeta`` on the box): the image is in the second
  cell, ``x3 < 0`` and first control ``zeta^2``, hence in ``cellTwoSet`` (no coordinates needed);
* the switch to ``1``: the image coordinates lie in ``{psi' <= a_i} ∪ {psi' <= a_{i+1}, theta2' >= b_j}``
  (the union of the boxes ``D_kl``, ``(k, l) < (i, j)``) with a positive margin;
* near the surface where the two switching times coincide (``∂_res``), both outcomes: a point
  switches to ``1`` (its image, a face class at a tie, has the coordinates of that branch formula,
  which must lie in the union of boxes) or to ``zeta^2`` strictly earlier, with the ``1``-cubic
  then ``<= 0``, and ``< 0`` unless it is a tie, so into ``cellTwoSet``.

The margin of a leaf is the sup-distance of the coordinate enclosure of the ``1``-branch image to the
complement of the union of the smaller boxes (``regions.subclaim_margin``); leaves whose image is in
``cellTwoSet`` have no metric margin (the cell is decided by the switch).
"""
from .. import boxmap as bm
from .. import regions as rg
from .. import driver
from .. import faces
from ..edges import with_edges
from .common import refine_outcome

BOXES = [(i, j) for i in range(3) for j in range(3) if (i, j) not in ((0, 0), (2, 2))]
INF = float('inf')


def margin_of(i, j, o):
    if o.cell == 2:
        return INF
    return rg.subclaim_margin(i, j, o.r2, o.psi, o.th2)


def leaf_for(i, j, required=0.0, mv=True):
    def leaf(b):
        r = _leaf(b, 1)
        if r[0] or r[2].get('why') != 'margin':
            return r
        # the image enclosure of a long time window: cut the window (union of enclosures)
        for ws in (8, 32):
            r2 = _leaf(b, ws)
            if r2[0]:
                return r2
        return r

    def _leaf(b, ws):
        try:
            outs = bm.step(b, wsplit=ws)
        except ZeroDivisionError:
            outs = None
        if outs is not None:
            worst = INF
            kinds = []
            for o in outs:
                m = margin_of(i, j, o)
                if m <= required and mv and len(outs) == 1:
                    o = refine_outcome(b, o, b.cell)
                    m = margin_of(i, j, o)
                worst = min(worst, m)
                kinds.append('%s->%d' % (o.kind, o.w))
            if worst > required:
                kd = sorted(set(kinds))
                return True, worst, {'kind': '/'.join(kd) + (' (%d windows)' % len(kinds)
                                                            if len(kinds) > len(kd) else '')}
            return False, None, {'why': 'margin', 'm': worst}
        return False, None, {'why': 'no certificate'}
    return leaf


def roots(i, j):
    b = rg.cell_box(i, j)
    rs = [b]
    for desc, fb in faces.wrong_control_pieces(b):
        if fb.cell == 2:
            continue           # theta2 = 0: in cellTwoSet, excluded by the hypothesis
        rs.append(fb)
    return rs


def run_box(i, j, required=0.0, jobs=None, presplit=6, max_depth=40, extra_roots=None):
    rs = extra_roots if extra_roots is not None else roots(i, j)
    return driver.run(rs, with_edges(leaf_for(i, j, required)), max_depth=max_depth, jobs=jobs,
                      presplit=presplit)
