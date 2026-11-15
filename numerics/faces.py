"""The face points of a closed box of the first big cell whose first control is not ``zeta``, and
their canonical representatives.

``cellClass p`` for ``p`` on a face of the closed cell (``x3 = 0``: ``r2 in {0, 1}`` or
``psi in {0, pi}``; or ``theta2 = 0``) may have a first control other than the cell's control
``zeta`` (the red regions of Figure 15.1, ``proposition15_2_2``). The box certificates of
``boxmap`` cover only the points with first control ``zeta``; for the others the class is the class
of a rotated representative (``classOf_smul_scale``: ``cellPoint p~ = zeta^k cellPoint p``) that
lies on a face of the closed first cell with first control ``zeta``, and the honest map at the
class is computed from that representative (``poincareAngZero_classOf``). The first control on the
faces is decided by Lemma 13.2.6 (checked by ``fuller.first_control`` and
``fuller.lex_first_control``):

* ``r2 = 0``: ``cellPoint = (e^{i theta1}, 0, 0)``, ``theta1 = theta2 - psi``; the first control is
  the vertex nearest to ``e^{i theta1}``, with the ties ``{zeta^i, zeta^(i+1)}`` broken towards
  ``zeta^i``: ``zeta`` for ``theta1 in (pi/3, pi]`` (mod ``2 pi``), ``1`` for ``(-pi/3, pi/3]``,
  ``zeta^2`` for ``(-pi, -pi/3]``. Canonical: ``(0, 0, theta1 + 2pi/3)`` or ``(0, 0, theta1 + 4pi/3)``
  (the class depends only on ``theta1``).
* ``r2 = 1``: ``(0, e^{i theta2}, 0)``: ``1`` for ``theta2 in [0, pi/3]``; canonical
  ``(1, 0, theta2 + 2pi/3)`` (the class does not depend on ``psi``).
* ``psi = 0`` and ``psi = pi`` (``0 < r2 < 1``): ``(+-r1 e^{i theta2}, r2 e^{i theta2}, 0)``: the vertex
  nearest to ``e^{i theta2}`` (the ``z1``-entry ties too): ``1`` for ``theta2 in [0, pi/3]``;
  canonical ``(r2, psi, theta2 + 2pi/3)``.
* ``theta2 = 0`` (``0 < r2 < 1``, ``0 < psi < pi``): ``y2 = 0``, ``y1 = -r1 sin psi < 0``: the first
  control is ``zeta^2``; these points form the top face of the second cell (``cellTwoDomain``),
  and are returned as a box of the second cell.
* ``theta2 = pi``: ``y2 = 0``, ``y1 = r1 sin psi > 0``: ``zeta``, nothing to do.
"""
from .iv import I, PI, HALF_PI
from .boxmap import Box
from .regions import PI3, TWO_PI3

FOUR_PI3 = PI * 4.0 / 3.0


def _theta_box(cell, r, kp, xp, th):
    """a Box with theta2 in the interval th (in [0, pi]) of the first cell"""
    th = th.intersect(I(0.0, PI.hi))
    if th is None:
        return None
    if th.lo > HALF_PI.hi:
        x2 = th - PI
        return Box(cell, r, kp, xp, 2, I(x2.lo, min(x2.hi, 0.0)))
    return Box(cell, r, kp, xp, 0, I(max(th.lo, 0.0), th.hi))


def _meet(x, lo, hi):
    a = max(x.lo, lo)
    b = min(x.hi, hi)
    return I(a, b) if a <= b else None


def wrong_control_pieces(b):
    """the canonical representatives of the face points of the cell-one Box b whose first control
    is not zeta: a list of (description, Box) (cell-one boxes with first control zeta at the
    representatives, and the theta2 = 0 face as a cell-two box)"""
    assert b.cell == 1
    out = []
    psi, th2 = b.psi(), b.th2()
    psi0 = (b.kp == 0 and b.xp.lo == 0.0)
    psipi = (b.kp == 2 and b.xp.hi == 0.0)
    th0 = (b.k2 == 0 and b.x2.lo == 0.0)
    if b.r.lo == 0.0:
        th1 = th2 - psi
        s1 = _meet(th1, -PI3.hi, PI3.hi)            # control 1
        if s1 is not None:
            bx = _theta_box(1, I(0.0), 0, I(0.0), s1 + TWO_PI3)
            if bx is not None:
                out.append(('r2 = 0, control 1', bx))
        s2 = _meet(th1, -PI.hi, -PI3.lo)            # control zeta^2
        if s2 is not None:
            bx = _theta_box(1, I(0.0), 0, I(0.0), s2 + FOUR_PI3)
            if bx is not None:
                out.append(('r2 = 0, control zeta^2', bx))
    s = _meet(th2, 0.0, PI3.hi)                     # control 1 on the other x3 = 0 faces
    if s is not None:
        sh = s + TWO_PI3
        if b.r.hi == 1.0:
            bx = _theta_box(1, I(1.0), 0, I(0.0), sh)
            if bx is not None:
                out.append(('r2 = 1, control 1', bx))
        if psi0:
            bx = _theta_box(1, b.r, 0, I(0.0), sh)
            if bx is not None:
                out.append(('psi = 0, control 1', bx))
        if psipi:
            bx = _theta_box(1, b.r, 2, I(0.0), sh)
            if bx is not None:
                out.append(('psi = pi, control 1', bx))
    if th0:
        out.append(('theta2 = 0, control zeta^2 (top face of the second cell)',
                    Box(2, b.r, b.kp, b.xp, 0, I(0.0))))
    return out


def canonical_point(r2, psi, th2):
    """the canonical representative (cell-one coordinates with first control zeta) of the class of
    the face point cellPoint(r2, psi, th2) of the closed first cell (floats; psi, th2 in radians),
    or None if the point is not on a face with x3 = 0. The rotation by zeta^k adds 2 pi k/3 to
    theta1 and theta2."""
    import math
    t1 = th2 - psi
    if r2 == 0.0:
        # the class depends only on theta1; rotate theta1 into (pi/3, pi]
        k = 0
        while not (math.pi / 3 < t1 <= math.pi + 1e-15):
            t1 += 2 * math.pi / 3
            k += 1
            if t1 > math.pi + 1e-15:
                t1 -= 2 * math.pi
        return (0.0, 0.0, t1)
    if r2 == 1.0 or psi == 0.0 or psi == math.pi:
        t = th2
        while not (math.pi / 3 < t <= math.pi + 1e-15):
            t += 2 * math.pi / 3
            if t > math.pi + 1e-15:
                t -= 2 * math.pi
        return (r2, psi, t)
    return None
