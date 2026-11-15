"""One step of the Fuller-Poincare map on a box of cell coordinates: a certified switching branch and
an enclosure of the image.

Boxes
-----
A ``Box`` is a closed box of cell coordinates ``(r2, psi, theta2)`` (Lean ``p 0, p 1, p 2``) in a
closed big cell, with that cell's control: ``cell = 1`` (``theta2 in [0, pi]``, control ``zeta``) or
``cell = 2`` (``theta2 in [-pi, 0]``, control ``zeta^2``). The angles carry exact anchors,
``psi = kp pi/2 + xp``, ``theta2 = k2 pi/2 + x2`` (intervals ``xp``, ``x2``), so that the faces
``psi in {0, pi}``, ``theta2 in {0, +-pi}`` are exact (``sin`` is exactly ``0`` there).

An ``EdgeBox`` is a box of a blow-up chart of a neighbourhood of an edge ``{r2 = 0, psi = 0}``
(``edge = 0``) or ``{r2 = 0, psi = pi}`` (``edge = 2``), where ``z2 -> 0`` and ``z3 -> 0`` at different
rates and the switching time tends to ``0``. With ``alpha = psi`` or ``pi - psi``: chart ``'a'``,
``r2 = eps``, ``alpha = eps kap``; chart ``'b'``, ``alpha = eps``, ``r2 = eps kap`` (``kap in [0, 1]``).
The two charts cover the square ``{r2 <= eps0, alpha <= eps0}``.

Scaled values
-------------
Both kinds of boxes give the *scaled* cell point (``SV``): a scale ``eps`` (``1`` for a ``Box``),
``z1``, ``Z2 = z2/eps``, ``Z3 = z3/eps^2``, and the time ``tau = t/eps``. Then
``D_{u,v}(eps tau)/eps^2 = Re(d) Z3 + RR(d, Z2) tau + RR(d, z1)/2 tau^2 + c3 eps tau^3`` (``d = v - u``)
has the sign of ``D_{u,v}`` for ``eps > 0``, and every quantity below is bounded uniformly up to
``eps = 0``; the image of the scaled flow is ``w1 = z1(t)``, ``W2 = z2(t)/eps``, ``W3 = z3(t)/eps^2``.

What a step proves (``step``)
----------------------------
Let ``u`` be the cell's control. For every point of the box **at which the first control of the cell
point is ``u``** (the open cell, and the faces where the cell's control is the first control; the
other face points are treated by ``faces.py``), with ``D_w(t) = D_{u,w}(t)`` (``w`` beats ``u`` at
``t`` iff ``D_w(t) > 0``):

* ``hi``: a time with ``D_w(hi) > 0`` on the whole box for some ``w``, so ``t_sw <= hi``;
* a control ``w`` is excluded if, for every ``tau`` in ``(0, hi]``, ``D_w(tau) < 0`` or
  ``D_w'(tau) > 0`` (``w'`` the third control): ``w`` never beats ``u`` before ``w'`` has, so ``w`` is
  not the switching control and ``D_w(t_sw) < 0``; or, near ``r2 = 0``, if in the time
  ``s = t/r2`` the control ``w'`` certainly beats ``u`` by ``s = K`` while ``D_w < 0`` on ``(0, K]``
  (``_face_exclusion``);
* for each remaining control ``w``, ``lo_w`` with ``D_w < 0`` on ``(0, lo_w]`` (``neg_on``, a
  monotone extension, or the structure ``D = zeta2 (a0 + a1 tau) + tau^2 (b0 + b1 tau)``,
  ``_neg_struct``), and the windows of ``[lo_w, hi]`` where the enclosure of ``D_w`` contains ``0``:
  if ``w`` switches, ``t_sw = inf {D_w > 0} > 0`` lies in a window and ``D_w(t_sw) = 0``;
* one remaining control: its outcomes are trusted (the image is in the open part of its cell:
  ``z3(t_sw)`` is on the wall ``W_m`` minus ``0``, ``m`` the third index, the rotated image
  ``w = zeta^(-m) F(z)`` has ``w3 in R_{<0}`` and first control ``zeta^(-m) v``,
  ``firstControl_poincare_ne``; its class has the cell coordinates ``cellCoords w``,
  ``cellClass_cellCoords``); two: each point follows one of them, and at a tie ``t_w = t_w'`` the
  image is a face class (``z3(t_sw) = 0``) represented by either branch formula (no range of a
  cell is assumed for its coordinates).

``image`` evaluates the branch formula at the times of a window; ``image_mv`` and ``jacobian`` use
the implicit root (``dD/dtau > 0`` on the window, so the root is a smooth function on the box).

The image coordinates
---------------------
From ``w1``, ``W2`` (``image``): ``r2' = 4 eps |W2| / (|w1| + sqrt(|w1|^2 + 4 eps |W2|))^2``
(Lemma 15.1.1), ``theta2' = arg W2``, and ``psi'`` by two formulas, intersected: ``arg (W2 conj w1)``,
and ``sin psi' = -eps X3 / (2 |w1| |W2|)`` (``X3 = Re W3``; the vanishing of the Hamiltonian,
(15.1.1)), with the side ``psi' < pi/2`` or ``> pi/2`` from the sign of ``Re (W2 conj w1)``; the
second one is exact in its smallness near ``psi' in {0, pi}``. When the time interval reaches
``tau = 0`` the "divided" forms are used (as in ``DOutMapsTo.lean``): ``W2/tau`` and ``X3/tau``, with
``(r2/eps)/tau`` eliminated through the root equation ``D = 0``, and, for a ``Box`` touching
``r2 = 1``, ``w1/tau`` with ``r1/tau``. ``image_mv`` gives the centred (mean value) form through the
implicit root, ``G(p) in G(m) + sum_j (d_j g + d_tau g (-d_j D / d_tau D))(X x T) (p_j - m_j)``,
for a ``Box``.
"""
from .iv import I, PI, SQRT3, HALF_PI, sin_cos, asin, sinc
from .cubic import (horner, deriv, neg_on, pos_on, neg_or_pos, float_first_upcrossing, _eval_on)
from .jet import J
from . import jet

# controls zeta^k as interval complex numbers (re, im)
_S3H = SQRT3 * 0.5
ZP = [(I(1.0), I(0.0)), (I(-0.5), _S3H), (I(-0.5), -_S3H)]


def cmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def rr(a, b):
    """RR(a, b) = Re a Re b + Im a Im b"""
    return a[0] * b[0] + a[1] * b[1]


def dvec(u, v):
    """d = v - u (Re d is exactly 0 for {u, v} = {zeta, zeta^2}, and 3/2 otherwise)"""
    if {u, v} == {1, 2}:
        return (I(0.0), ZP[v][1] - ZP[u][1])
    return (ZP[v][0] - ZP[u][0], ZP[v][1] - ZP[u][1])


def re_zero(d):
    return d[0].lo == 0.0 and d[0].hi == 0.0


def c3(u, v):
    """RR(v - u, -i u)/6 = +sqrt3/12 for v = u zeta^2, -sqrt3/12 for v = u zeta"""
    s = SQRT3 / 12.0
    return s if (v - u) % 3 == 2 else -s


def eventual(u, v):
    return (v - u) % 3 == 2


def anchored(k, s, c):
    """(sin, cos) of k pi/2 + x from (sin x, cos x)"""
    m = k % 4
    if m == 0:
        return s, c
    if m == 1:
        return c, -s
    if m == 2:
        return -s, -c
    return -c, s


def new_cell(u, w):
    m = 3 - u - w
    return 1 if (w - m) % 3 == 1 else 2


# ---- boxes ----------------------------------------------------------------------------------------
class Box:
    __slots__ = ('cell', 'r', 'kp', 'xp', 'k2', 'x2')

    def __init__(self, cell, r, kp, xp, k2, x2):
        self.cell = cell
        self.r = r
        self.kp = kp
        self.xp = xp
        self.k2 = k2
        self.x2 = x2

    def psi(self):
        return HALF_PI * float(self.kp) + self.xp if self.kp else self.xp

    def th2(self):
        return HALF_PI * float(self.k2) + self.x2 if self.k2 else self.x2

    def iv(self, axis):
        return (self.r, self.xp, self.x2)[axis]

    def with_iv(self, axis, x):
        b = Box(self.cell, self.r, self.kp, self.xp, self.k2, self.x2)
        if axis == 0:
            b.r = x
        elif axis == 1:
            b.xp = x
        else:
            b.x2 = x
        return b

    def split(self, axis):
        a, b = self.iv(axis).split()
        return self.with_iv(axis, a), self.with_iv(axis, b)

    def widths(self):
        return (self.r.width(), self.xp.width(), self.x2.width())

    def center(self):
        return Box(self.cell, I(self.r.mid()), self.kp, I(self.xp.mid()), self.k2,
                   I(self.x2.mid()))

    def __repr__(self):
        p, t = self.psi(), self.th2()
        return 'Box(cell %d, r2 [%.9g, %.9g], psi [%.9g, %.9g], th2 [%.9g, %.9g])' % (
            self.cell, self.r.lo, self.r.hi, p.lo, p.hi, t.lo, t.hi)

    def regular(self):
        return self


class EdgeBox:
    """a box (eps, kap, theta2) of the blow-up chart of the edge {r2 = 0, psi = 0} (edge 0) or
    {r2 = 0, psi = pi} (edge 2) of the closed cell ``cell``"""
    __slots__ = ('cell', 'edge', 'chart', 'eps', 'kap', 'k2', 'x2')

    def __init__(self, cell, edge, chart, eps, kap, k2, x2):
        self.cell = cell
        self.edge = edge
        self.chart = chart
        self.eps = eps
        self.kap = kap
        self.k2 = k2
        self.x2 = x2

    def iv(self, axis):
        return (self.eps, self.kap, self.x2)[axis]

    def with_iv(self, axis, x):
        b = EdgeBox(self.cell, self.edge, self.chart, self.eps, self.kap, self.k2, self.x2)
        if axis == 0:
            b.eps = x
        elif axis == 1:
            b.kap = x
        else:
            b.x2 = x
        return b

    def split(self, axis):
        a, b = self.iv(axis).split()
        return self.with_iv(axis, a), self.with_iv(axis, b)

    def widths(self):
        return (self.eps.width(), self.kap.width(), self.x2.width())

    def th2(self):
        return HALF_PI * float(self.k2) + self.x2 if self.k2 else self.x2

    def r2_alpha(self):
        if self.chart == 'a':
            return self.eps, self.eps * self.kap
        return self.eps * self.kap, self.eps

    def center(self):
        return EdgeBox(self.cell, self.edge, self.chart, I(self.eps.mid()), I(self.kap.mid()),
                       self.k2, I(self.x2.mid()))

    def regular(self):
        """the regular Box enclosing this one"""
        r2, al = self.r2_alpha()
        if self.edge == 0:
            return Box(self.cell, r2, 0, al, self.k2, self.x2)
        return Box(self.cell, r2, 2, -al, self.k2, self.x2)

    def __repr__(self):
        r2, al = self.r2_alpha()
        t = self.th2()
        return ('EdgeBox(cell %d, edge psi=%s, chart %s, eps [%.4g, %.4g], kap [%.6g, %.6g], '
                'th2 [%.9g, %.9g]; r2 [%.3g, %.3g], alpha [%.3g, %.3g])' % (
                    self.cell, '0' if self.edge == 0 else 'pi', self.chart, self.eps.lo,
                    self.eps.hi, self.kap.lo, self.kap.hi, t.lo, t.hi, r2.lo, r2.hi, al.lo, al.hi))


class SqrtBox:
    """a box (eps, psi, theta2) of the chart r2 = eps^2 of a neighbourhood of the face r2 = 0, with
    the time scale eps = sqrt(r2): there the switch to the eventual winner takes a time of order
    sqrt(r2) and the other one a time of order r2 (the corner of the faces r2 = 0 and theta2 = 0)"""
    __slots__ = ('cell', 'eps', 'kp', 'xp', 'k2', 'x2')

    def __init__(self, cell, eps, kp, xp, k2, x2):
        self.cell = cell
        self.eps = eps
        self.kp = kp
        self.xp = xp
        self.k2 = k2
        self.x2 = x2

    def iv(self, axis):
        return (self.eps, self.xp, self.x2)[axis]

    def with_iv(self, axis, x):
        b = SqrtBox(self.cell, self.eps, self.kp, self.xp, self.k2, self.x2)
        if axis == 0:
            b.eps = x
        elif axis == 1:
            b.xp = x
        else:
            b.x2 = x
        return b

    def split(self, axis):
        a, b = self.iv(axis).split()
        return self.with_iv(axis, a), self.with_iv(axis, b)

    def widths(self):
        return (self.eps.width(), self.xp.width(), self.x2.width())

    def psi(self):
        return HALF_PI * float(self.kp) + self.xp if self.kp else self.xp

    def th2(self):
        return HALF_PI * float(self.k2) + self.x2 if self.k2 else self.x2

    def center(self):
        return SqrtBox(self.cell, I(self.eps.mid()), self.kp, I(self.xp.mid()), self.k2,
                       I(self.x2.mid()))

    def regular(self):
        return Box(self.cell, self.eps.sqr(), self.kp, self.xp, self.k2, self.x2)

    def __repr__(self):
        return 'SqrtBox(cell %d, sqrt r2 [%.4g, %.4g]; %r)' % (self.cell, self.eps.lo, self.eps.hi,
                                                              self.regular())


# ---- scaled values ----------------------------------------------------------------------------------
class SV:
    """the scaled cell point: eps, r1, zeta2 = r2/eps, spe = sin(psi)/eps, e1 = e^{i theta1},
    e2 = e^{i theta2}, z1, Z2 = z2/eps, Z3 = z3/eps^2 (real); r2 (the true r2), regular flag"""
    __slots__ = ('eps', 'r1', 'r2', 'zeta2', 'spe', 'e1', 'e2', 'z1', 'Z2', 'Z3', 'regular',
                 'nodiv')


def box_vals(b):
    v = SV()
    v.nodiv = False
    if isinstance(b, SqrtBox):
        v.regular = False
        v.nodiv = True
        v.eps = b.eps
        v.r2 = b.eps.sqr()
        v.zeta2 = b.eps
        sp, cp = sin_cos(b.xp)
        sps = anchored(b.kp, sp, cp)[0]
        v.spe = None
        s2, c2 = sin_cos(b.x2)
        v.e2 = anchored(b.k2, s2, c2)[::-1]
        s1, c1 = sin_cos(b.x2 - b.xp)
        s1, c1 = anchored(b.k2 - b.kp, s1, c1)
        v.e1 = (c1, s1)
        v.r1 = 1.0 - v.r2
        v.z1 = (v.r1 * v.e1[0], v.r1 * v.e1[1])
        v.Z2 = (v.zeta2 * v.e2[0], v.zeta2 * v.e2[1])
        v.Z3 = (v.r1 * sps) * (-2.0)          # z3/eps^2 = -2 r1 sin psi
        return v
    if isinstance(b, Box):
        v.regular = True
        v.eps = I(1.0)
        v.r2 = b.r
        v.zeta2 = b.r
        sp, cp = sin_cos(b.xp)
        v.spe = anchored(b.kp, sp, cp)[0]
        s2, c2 = sin_cos(b.x2)
        v.e2 = anchored(b.k2, s2, c2)[::-1]
        x1 = b.x2 - b.xp
        if x1.width() < 1.5:
            s1, c1 = sin_cos(x1)
            s1, c1 = anchored(b.k2 - b.kp, s1, c1)
        else:
            sps, cps = anchored(b.kp, sp, cp)
            c1 = v.e2[0] * cps + v.e2[1] * sps
            s1 = v.e2[1] * cps - v.e2[0] * sps
        v.e1 = (c1, s1)
    else:
        v.regular = False
        v.eps = b.eps
        r2, al = b.r2_alpha()
        v.r2 = r2
        if b.chart == 'a':
            v.zeta2 = I(1.0)
            v.spe = b.kap * sinc(al)
        else:
            v.zeta2 = b.kap
            v.spe = sinc(al)
        s2, c2 = sin_cos(b.x2)
        v.e2 = anchored(b.k2, s2, c2)[::-1]
        if b.edge == 0:
            s1, c1 = sin_cos(b.x2 - al)
            s1, c1 = anchored(b.k2, s1, c1)
        else:
            s1, c1 = sin_cos(b.x2 + al)
            s1, c1 = anchored(b.k2 - 2, s1, c1)
        v.e1 = (c1, s1)
    v.r1 = 1.0 - v.r2
    v.z1 = (v.r1 * v.e1[0], v.r1 * v.e1[1])
    v.Z2 = (v.zeta2 * v.e2[0], v.zeta2 * v.e2[1])
    v.Z3 = ((v.r1 * v.zeta2) * v.spe) * (-2.0)
    return v


def coeffs(v, u, w):
    """[C0, C1, C2, C3]: D_{u,w}(eps tau)/eps^2 as a cubic in tau"""
    d = dvec(u, w)
    cz = I(0.0) if re_zero(d) else d[0] * v.Z3
    # factored: RR(d, Z2) = zeta2 RR(d, e2), RR(d, z1) = r1 RR(d, e1) (signs kept at the faces)
    return [cz, v.zeta2 * rr(d, v.e2), (v.r1 * rr(d, v.e1)) * 0.5, c3(u, w) * v.eps]


# ---- the root certificates ----------------------------------------------------------------------
def _tmax(v):
    return 12.0 / v.eps.lo if v.eps.lo > 0 else 1e6


def _bracket(c, g, ev, tmax):
    """from a guess g: tl < g < th with D(th) > 0 and D(tl) < 0 on the box (tl = 0 if none)"""
    if ev is None:
        ev = lambda t: horner(c, I(t))
    if g is None or not g > 0:
        g = 1e-3
    delta = max(g * 1e-6, 1e-14)
    th = None
    for _ in range(90):
        t = g + delta
        if t > tmax:
            break
        if ev(t).lo > 0:
            th = t
            break
        delta *= 2.0
    if th is None:
        return None
    lo, hi = g, th
    for _ in range(12):
        m = 0.5 * (lo + hi)
        if ev(m).lo > 0:
            hi = m
        else:
            lo = m
    th = hi
    tl = 0.0
    delta = max(g * 1e-6, 1e-14)
    for _ in range(90):
        t = g - delta
        if t <= 0:
            break
        if ev(t).hi < 0:
            tl = t
            break
        delta *= 2.0
    if tl > 0:
        lo, hi = tl, min(g, th)
        for _ in range(12):
            m = 0.5 * (lo + hi)
            if ev(m).hi < 0:
                lo = m
            else:
                hi = m
        tl = lo
    return tl, th


# ---- image coordinates ----------------------------------------------------------------------------
def _arg(x, y, k):
    """the angle of (x, y) (intervals or jets) by a formula valid on the whole enclosure, in the
    branch centred at k pi/2: k pi/2 + atan(y'/x'), k pi/2 +- pi/2 - atan(x'/y') for the point
    rotated by -k pi/2. None if no formula applies (the enclosure meets the origin or the cut)."""
    m = k % 4
    if m == 0:
        xr, yr = x, y
    elif m == 1:
        xr, yr = y, -x
    elif m == 2:
        xr, yr = -x, -y
    else:
        xr, yr = -y, x
    base = HALF_PI * float(k)
    xv, yv = jet.val(xr), jet.val(yr)
    try:
        if xv.lo > 0:
            return jet.atan(yr / xr) + base
        if yv.lo > 0:
            return (-jet.atan(xr / yr)) + (base + HALF_PI)
        if yv.hi < 0:
            return (-jet.atan(xr / yr)) + (base - HALF_PI)
    except ZeroDivisionError:
        pass
    return None


def _clip(a, rng):
    if a is None or rng is None:
        return a
    if isinstance(a, J):
        v = a.v.intersect(rng)
        return None if v is None else J(v, a.d)
    return a.intersect(rng)


def _meet(a, b):
    if a is None:
        return b
    if b is None:
        return a
    if isinstance(a, J) or isinstance(b, J):
        return a
    m = a.intersect(b)
    return m if m is not None else a


def cell_range(cell):
    return I(0.0, PI.hi) if cell == 1 else I(-PI.hi, 0.0)


PSI_RANGE = I(0.0, PI.hi)


class Img:
    """the image of a branch: its cell, r2' = eps R, psi', theta2', and the edge data
    (side: 0 if psi' < pi/2, 2 if psi' > pi/2, None if unknown; A with alpha' = min(psi', pi -
    psi') = eps A)"""
    __slots__ = ('cell', 'eps', 'R', 'r2', 'psi', 'th2', 'side', 'A')


def flow_scaled(v, u, T):
    """w1 = z1(t), W2 = z2(t)/eps, W3 = z3(t)/eps^2 along the control u, t = eps tau, tau in T"""
    ur, ui = ZP[u]
    x1, y1 = v.z1
    X2, Y2 = v.Z2
    e = v.eps
    eT = e * T
    T2 = T.sqr() if isinstance(T, I) else T * T
    eT2h = e * T2 * 0.5
    eT3s = e * (T2 * T) / 6.0
    z1t = (x1 + eT * ui, y1 - eT * ur)
    Z2t = (X2 + x1 * T + eT2h * ui, Y2 + y1 * T - eT2h * ur)
    Z3t = (v.Z3 + X2 * T + x1 * T2 * 0.5 + eT3s * ui, Y2 * T + y1 * T2 * 0.5 - eT3s * ur)
    return z1t, Z2t, Z3t


def rot(m, w):
    """multiply by zeta^(-m)"""
    return cmul(ZP[(-m) % 3], w)


def _sq(x):
    return x.sqr()


def _mod(vec):
    return (_sq(vec[0]) + _sq(vec[1])).sqrt()


def coords(v, newcell, trust, w1s, W2s, Sforms):
    """the image record from the forms of w1 and W2: w1s, W2s are lists of (vec, scale) with
    w1 = scale * vec (scale an interval >= 0, or None for 1); Sforms is a list of
    (X3form, w1vec, W2vec) with S = sin(psi')/eps = -X3form / (2 |w1vec| |W2vec|) (the scales
    cancel)"""
    im = Img()
    im.cell = newcell
    im.eps = v.eps
    e = v.eps

    def modulus(forms):
        m = None
        for vec, sc in forms:
            try:
                x = _mod(vec)
            except ValueError:
                continue
            if sc is not None:
                x = x * sc
            m = x if m is None else _meet(m, x)
        return m
    a = modulus(w1s)
    B = modulus(W2s)
    try:
        R = (B * 4.0) / (a + (a.sqr() + e * B * 4.0).sqrt()).sqr()
    except (ZeroDivisionError, ValueError, AttributeError):
        R = None
    im.R = R
    if R is not None:
        im.r2 = R * e
        im.r2 = im.r2.intersect(I(0.0, 1.0)) or im.r2
    else:
        im.r2 = I(0.0, 1.0)
    crng = cell_range(newcell) if trust else None
    cen = 1 if newcell == 1 else -1
    th2 = None
    for W, sc in W2s:
        th2 = _meet(th2, _clip(_arg(W[0], W[1], cen), crng))
    im.th2 = th2
    prng = PSI_RANGE if trust else None
    psi = None
    cos_sign = None
    for p1, _s1 in w1s:
        for p2, _s2 in W2s:
            qx = p2[0] * p1[0] + p2[1] * p1[1]
            qy = p2[1] * p1[0] - p2[0] * p1[1]
            if cos_sign is None:
                if qx.lo > 0:
                    cos_sign = 1
                elif qx.hi < 0:
                    cos_sign = -1
            psi = _meet(psi, _clip(_arg(qx, qy, 1), prng))
    im.side = None
    im.A = None
    if cos_sign is not None:
        S = None
        for X3f, p1, p2 in Sforms:
            try:
                Sx = -(X3f / ((_mod(p1) * _mod(p2)) * 2.0))
            except (ZeroDivisionError, ValueError):
                continue
            S = Sx if S is None else _meet(S, Sx)
        if S is not None and (trust or S.lo >= 0):
            S = I(max(S.lo, 0.0), max(S.hi, 0.0))
            sp = S * e
            if sp.hi < 1.0:
                al = asin(sp)        # alpha' = asin(eps S)
                im.side = 0 if cos_sign > 0 else 2
                # A = alpha'/eps in [S, S / sqrt(1 - (eps S)^2)]
                try:
                    im.A = I(S.lo, (S / (1.0 - sp.sqr()).sqrt()).hi)
                except (ZeroDivisionError, ValueError):
                    im.A = None
                psi = _meet(psi, al if cos_sign > 0 else (PI - al))
    im.psi = psi
    return im


def image(v, u, w, T, trust):
    """the image record of the branch u -> w at the scaled times T, with the divided forms"""
    m = 3 - u - w
    nc = new_cell(u, w)
    z1t, Z2t, Z3t = flow_scaled(v, u, T)
    w1 = rot(m, z1t)
    W2 = rot(m, Z2t)
    X3 = rot(m, Z3t)[0]
    W2t = X3t = w1t = None
    if T.hi > 0 and T.lo <= 0.5 * T.hi and not v.nodiv:
        d = dvec(u, w)
        cc = c3(u, w) * v.eps
        C2 = (v.r1 * rr(d, v.e1)) * 0.5
        C1 = v.zeta2 * rr(d, v.e2)
        ur, ui = ZP[u]
        e = v.eps
        # zeta2/tau from the root equation: zeta2 (-2 Re d r1 spe + delta2 tau) = -tau^2 (C2 + C3 tau)
        q = None
        if v.zeta2.lo == 0 and v.zeta2.hi == 0:
            q = I(0.0)
        else:
            delta2 = d[0] * v.e2[0] + d[1] * v.e2[1]
            try:
                if re_zero(d):
                    q = -((C2 + cc * T) / delta2)
                else:
                    den = d[0] * (v.r1 * v.spe) * (-2.0) + delta2 * T
                    q = -((T * (C2 + cc * T)) / den)
            except ZeroDivisionError:
                q = None
        if q is not None:
            eT = e * T
            pre = (q * v.e2[0] + v.z1[0] + eT * ui * 0.5, q * v.e2[1] + v.z1[1] - eT * ur * 0.5)
            W2t = rot(m, pre)
            # X3/tau = Re rot(Z3/tau + Z2 + z1 tau/2 - i u eps tau^2/6), Z3/tau = -2 r1 spe q
            Z3t_ = ((v.r1 * v.spe) * q) * (-2.0)
            eT2s = e * T.sqr() / 6.0
            pre3 = (Z3t_ + v.Z2[0] + v.z1[0] * T * 0.5 + eT2s * ui,
                    v.Z2[1] + v.z1[1] * T * 0.5 - eT2s * ur)
            X3t = rot(m, pre3)[0]
        if v.regular and v.r2.hi == 1:
            # r1/tau = -(C1 + C3 tau^2) / (-2 Re d r2 sin psi + delta1 tau^2/2)  (0 on r2 = 1)
            q1 = None
            if v.r2.lo == 1:
                q1 = I(0.0)
            else:
                delta1 = d[0] * v.e1[0] + d[1] * v.e1[1]
                den = d[0] * (v.r2 * v.spe) * (-2.0) + delta1 * T.sqr() * 0.5
                try:
                    q1 = -((C1 + cc * T.sqr()) / den)
                except ZeroDivisionError:
                    q1 = None
            if q1 is not None:
                w1t = rot(m, (q1 * v.e1[0] + ui, q1 * v.e1[1] - ur))
    w1s = [(w1, None)]
    W2s = [(W2, None)]
    Sf = [(X3, w1, W2)]
    if W2t is not None:
        W2s.append((W2t, T))
        if X3t is not None:
            Sf.append((X3t, w1, W2t))
    if w1t is not None:
        w1s.append((w1t, T))
    # the forms divided by r1 (r2 near 1): tau = -C0/(C1 + C2 tau + C3 tau^2) at the root, so
    # tau/r1 = 2 Re d zeta2 spe / (C1 + C2 tau + C3 tau^2); w1 = r1 (e1 - i u eps tau/r1)
    d = dvec(u, w)
    if v.regular and v.r1.hi < 0.25 and not re_zero(d) and v.spe is not None:
        cc = c3(u, w) * v.eps
        C2 = (v.r1 * rr(d, v.e1)) * 0.5
        C1 = v.zeta2 * rr(d, v.e2)
        den = C1 + C2 * T + cc * T.sqr()
        if den.lo > 0 or den.hi < 0:
            tr1 = (d[0] * (v.zeta2 * v.spe) * 2.0) / den
            ur, ui = ZP[u]
            e = v.eps
            W1r = rot(m, (v.e1[0] + e * tr1 * ui, v.e1[1] - e * tr1 * ur))
            w1s.append((W1r, v.r1))
            # X3/r1 = Re rot(-2 zeta2 spe + Z2 tau/r1 + e1 tau^2/2 - i u eps tau^2 (tau/r1)/6)
            T2 = T.sqr()
            pre = (v.zeta2 * v.spe * (-2.0) + v.Z2[0] * tr1 + v.e1[0] * T2 * 0.5
                   + e * T2 * tr1 * ui / 6.0,
                   v.Z2[1] * tr1 + v.e1[1] * T2 * 0.5 - e * T2 * tr1 * ur / 6.0)
            X3r = rot(m, pre)[0]
            Sf.append((X3r, W1r, W2))
    im = coords(v, nc, trust, w1s, W2s, Sf)
    _cones(v, u, w, T, m, nc, trust, im)
    return im


def _cone_arg(vecs, k):
    """the angles (branch centred at k pi/2) of a positive combination of vectors whose
    directions are enclosed by vecs: the hull of their angles, when it is shorter than pi"""
    lo = hi = None
    for vec in vecs:
        a = _arg(vec[0], vec[1], k)
        if a is None:
            return None
        lo = a.lo if lo is None else min(lo, a.lo)
        hi = a.hi if hi is None else max(hi, a.hi)
    if hi - lo >= PI.lo:
        return None
    return I(lo, hi)


def _cones(v, u, w, T, m, nc, trust, im):
    """the cone forms near r2 = 0 and r1 = 0, valid at every time (no root relation):
    W2 = zeta2 e2 + tau (z1 - i u eps tau/2), w1 = r1 e1 + eps tau (-i u), positive
    combinations, so their directions lie between those of the summands"""
    ur, ui = ZP[u]
    e = v.eps
    cen = 1 if nc == 1 else -1
    a2 = a1 = None
    if v.zeta2.lo == 0 and T.lo >= 0:
        B = rot(m, (v.z1[0] + e * T * ui * 0.5, v.z1[1] - e * T * ur * 0.5))
        a2 = _cone_arg([rot(m, v.e2), B], cen)
        if a2 is not None:
            rng = cell_range(nc) if trust else None
            a2c = _clip(a2, rng)
            im.th2 = _meet(im.th2, a2c) if a2c is not None else im.th2
    if v.r1.lo == 0 and T.lo >= 0 and isinstance(v.e1[0], I):
        a1 = _cone_arg([rot(m, v.e1), rot(m, (ui, -ur))], cen)
    if trust and (a2 is not None or a1 is not None):
        # psi' = arg W2 - arg w1 (mod 2 pi), with the plain argument of the other one
        if a2 is None:
            a2 = _arg(*rot(m, flow_scaled(v, u, T)[1]), cen)
        if a1 is None:
            a1 = _arg(*rot(m, flow_scaled(v, u, T)[0]), cen)
        if a1 is not None and a2 is not None:
            d = a2 - a1
            if d.width() < PI.lo:
                for sh in (0.0, 2.0, -2.0):
                    dd = d + PI * sh if sh else d
                    c = dd.intersect(PSI_RANGE)
                    if c is not None:
                        im.psi = _meet(im.psi, c) if im.psi is not None else c
                        break


# ---- one step on a box ------------------------------------------------------------------------------
class Outcome:
    """a branch of a step: the beating control w, the time interval T (of tau), the certificate kind,
    the image record (``img``); ``tie``: the image may be a face class at points where the two
    switching times coincide (dual certificates); ``trust``: the image is in the open part of its
    cell"""
    __slots__ = ('w', 'T', 'kind', 'cell', 'img', 'tie', 'trust')

    @property
    def r2(self):
        return self.img.r2 if self.img else None

    @property
    def psi(self):
        return self.img.psi if self.img else None

    @property
    def th2(self):
        return self.img.th2 if self.img else None

    def __repr__(self):
        im = self.img
        return ('Outcome(-> %d, tau [%.6g, %.6g] %s, cell %d, r2 %s, psi %s, th2 %s, side %s, A %s, '
                'tie %s)' % (self.w, self.T.lo, self.T.hi, self.kind, self.cell,
                             im.r2 if im else None, im.psi if im else None,
                             im.th2 if im else None, im.side if im else None,
                             im.A if im else None, self.tie))


class BoxEval:
    """the data of a box shared by its certificates, with (for a Box, lazily) the mean value
    enclosures of the cubics at fixed times"""

    def __init__(self, b):
        self.b = b
        self.u = b.cell
        self.vals = box_vals(b)
        self.others = [w for w in range(3) if w != self.u]
        self.cf = {w: coeffs(self.vals, self.u, w) for w in self.others}
        self._mv = None

    def _mvdata(self):
        if self._mv is None:
            b = self.b
            cv = box_vals(b.center())
            vj = vals_jet(b)
            rad = [b.r - b.r.mid(), b.xp - b.xp.mid(), b.x2 - b.x2.mid()]
            data = {}
            for w in self.others:
                cc = coeffs(cv, self.u, w)
                cj = coeffs_jet(vj, self.u, w)
                lin = [sum((cj[k].d[j] * rad[j] for j in range(3)), I(0.0)) for k in range(4)]
                data[w] = (cc, lin)
            self._mv = data
        return self._mv

    def ev(self, w):
        c = self.cf[w]
        if not isinstance(self.b, Box):
            return None

        def f(t):
            T = I(t)
            v = horner(c, T)
            cc, lin = self._mvdata()[w]
            v2 = horner(cc, T) + horner(lin, T)
            return v.intersect(v2) or v
        return f

    def guesses(self):
        cv = box_vals(self.b.center())
        return {w: float_first_upcrossing([x.mid() for x in coeffs(cv, self.u, w)])
                for w in self.others}


def _lower(c, tl, th, ev=None):
    """a certified lower bound lo <= tl of the first upcrossing of the cubic c on the box:
    D < 0 on (0, lo]; tl itself when D < 0 on (0, tc] and dD/dtau > 0 on [tc, tl] for some tc,
    since D(tl) < 0 (the bracket); 0 if nothing is certified"""
    if tl <= 0:
        return 0.0
    if neg_on(c, 0.0, tl):
        return tl
    dc = deriv(c)
    # the monotone extension needs D(tl) < 0 on the box
    end_neg = (ev(tl) if ev is not None else horner(c, I(tl))).hi < 0
    w = max(th - tl, 1e-12)
    for k in range(0, 10, 2):
        tc = tl - w * 2.0 ** k
        if tc <= 0:
            break
        if neg_on(c, 0.0, tc):
            if end_neg and pos_on(dc, tc, tl):
                return tl
            return tc
    if end_neg and c[0].hi <= 0 and pos_on(dc, 0.0, tl):
        return tl
    return 0.0


def step(b, want_coords=True, allow_dual=True, wsplit=1):
    """certified outcomes of one step on the box b, for its points with first control u = b.cell, or
    None. The list of Outcomes covers every such point:

    * ``hi``: a time at which some control certainly beats u on the whole box, so t_sw <= hi;
    * a control w is excluded if, for every tau in (0, hi], D_w(tau) < 0 or D_w'(tau) > 0 (w' the
      third control): then w never beats u before w' has, so w is not the switching control, and
      at the switch D_w < 0 strictly (z3 != 0);
    * for each remaining control w, lo_w with D_w < 0 on (0, lo_w], so t_w >= lo_w; the outcome
      of w has T = [lo_w, hi] and its image is the w-formula at the time t_sw in T, where
      D_w(t_sw) = 0 (t_sw = inf {D_w > 0} > 0);
    * one remaining control: the single branch (``trust``: the image is in the open part of its
      cell); two: both outcomes (``tie``: at a tie t_w = t_w' the image is a face class, with the
      coordinates of either branch formula)."""
    E = BoxEval(b)
    u, others, cf = E.u, E.others, E.cf
    guess = E.guesses()
    tmax = _tmax(E.vals)
    br = {}
    for w in others:
        if guess[w] is None:
            continue
        x = _bracket(cf[w], guess[w], E.ev(w), tmax)
        if x is not None:
            br[w] = x
    if not br:
        return None
    hi = min(th for (tl, th) in br.values())
    excl = set()
    if E.vals.regular and E.vals.zeta2.lo == 0 and E.vals.zeta2.hi > 0:
        for w in others:
            wo = [x for x in others if x != w][0]
            K = _face_exclusion(E.vals, u, w, wo)
            if K is not None:
                excl.add(w)
                hi = min(hi, (E.vals.zeta2 * K).hi)
    poss = []
    for w in others:
        wo = [x for x in others if x != w][0]
        if w in excl or neg_or_pos(cf[w], cf[wo], 0.0, hi):
            continue
        lo = 0.0
        if w in br:
            tl, th = br[w]
            lo = min(_lower(cf[w], min(tl, hi), th, E.ev(w)), hi)
        lo = max(lo, min(_neg_struct(E.vals, u, w), hi))
        if lo >= hi:
            continue
        if lo > 0 and pos_on(deriv(cf[w]), lo, hi):
            wins = [I(lo, hi)]          # D increasing on [lo, hi]: one window, no scan
        else:
            wins = _windows(cf[w], cf[wo], lo, hi, E.ev(w), E.ev(wo))
        if wsplit > 1:
            wins = _split_windows(cf[w], wins, wsplit)
        if wins:
            poss.append((w, wins))
    if not poss:
        return None
    single = len(poss) == 1 and len(poss[0][1]) == 1
    one_control = len(poss) == 1
    if not one_control and not allow_dual:
        return None
    outs = []
    for w, wins in poss:
        for T in wins:
            o = Outcome()
            o.w, o.T, o.kind = w, T, 'win'
            o.tie = not one_control
            o.trust = one_control
            o.cell = new_cell(u, w)
            o.img = image(E.vals, u, w, o.T, one_control) if want_coords else None
            outs.append(o)
    return outs


NWIN = 24


def _face_coeffs(v, u, w):
    """D_{u,w}(r2 s)/N as a cubic in s = t/r2 (a regular box), N = r2 (Re d != 0) or r2^2
    (Re d = 0): uniform up to r2 = 0, with the sign of D for r2 > 0"""
    d = dvec(u, w)
    r = v.zeta2
    a = rr(d, v.e2)
    b = (v.r1 * rr(d, v.e1)) * 0.5
    c = c3(u, w)
    if re_zero(d):
        return [I(0.0), a, b, c * r]
    return [d[0] * (v.r1 * v.spe) * (-2.0), r * a, r * b, r.sqr() * c]


def _face_exclusion(v, u, w, wo):
    """near the face r2 = 0: a K such that, at every point of the box with r2 > 0, the control wo
    beats u by the time K r2 while w does not before (D_w < 0 on (0, K r2]); None if not found.
    Then w is not the switching control, t_sw <= K r2, and D_w(t_sw) < 0."""
    co = _face_coeffs(v, u, wo)
    cw = _face_coeffs(v, u, w)
    g = float_first_upcrossing([x.mid() for x in co])
    if g is None or not g > 0:
        return None
    K = None
    for f in (1.001, 1.01, 1.1, 1.5, 2.0):
        if horner(co, I(g * f)).lo > 0:
            K = g * f
            break
    if K is None:
        return None
    return K if neg_on(cw, 0.0, K) else None


def _neg_struct(v, u, w):
    """a T1 >= 0 with D_{u,w} < 0 on (0, T1] at every point of the box, from the structure
    D = zeta2 (a0 + a1 tau) + tau^2 (b0 + b1 tau), zeta2 >= 0, with a0 = -2 Re d r1 spe,
    a1 = RR(d, e2), b0 = RR(d, z1)/2, b1 = C3: D < 0 where a0 + a1 tau <= 0 and
    b0 + b1 tau < 0 (both linear in tau, checked at the ends); 0 if nothing is certified"""
    if v.spe is None:
        return 0.0
    d = dvec(u, w)
    a0 = I(0.0) if re_zero(d) else d[0] * (v.r1 * v.spe) * (-2.0)
    a1 = rr(d, v.e2)
    b0 = (v.r1 * rr(d, v.e1)) * 0.5
    b1 = c3(u, w) * v.eps
    if not (a0.hi <= 0 and b0.hi <= 0):
        return 0.0
    # the largest T1 with a0 + a1 T1 <= 0 and b0 + b1 T1 < 0
    T1 = 1e6
    if a1.hi > 0:
        if a0.hi == 0:
            return 0.0
        T1 = min(T1, (-a0.hi) / a1.hi)
    if b1.hi >= 0:
        if b0.hi == 0:
            return 0.0
        if b1.hi > 0:
            T1 = min(T1, (-b0.hi) / b1.hi)
    T1 *= 0.999
    if T1 <= 0:
        return 0.0
    if (a0 + a1 * T1).hi <= 0 and (b0 + b1 * T1).hi < 0:
        return T1
    return 0.0




def _split_windows(c, wins, k):
    """each window cut into k pieces, keeping those where the enclosure of D contains 0"""
    out = []
    for T in wins:
        h = (T.hi - T.lo) / k
        for i in range(k):
            P = I(T.lo + h * i, T.hi if i == k - 1 else T.lo + h * (i + 1))
            v = _eval_on(c, P)
            if not (v.lo > 0 or v.hi < 0):
                out.append(P)
    return out




def _piece_enc(c, P, ev):
    """an enclosure of D over the box x P: Horner/centred in t, intersected (when that one contains
    0) with the mean value form in the parameters at the midpoint of P plus the t-derivative"""
    v = _eval_on(c, P)
    if ev is not None and P.hi > P.lo and v.lo <= 0 <= v.hi:
        m = P.mid()
        v2 = ev(m) + horner(deriv(c), P) * (P - m)
        w = v.intersect(v2)
        if w is not None:
            v = w
    return v


def _windows(c, co, lo, hi, ev=None, evo=None):
    """the windows of [lo, hi] where the switch to the control of the cubic c can happen: the pieces
    where the enclosure of D contains 0 (D(t_sw) = 0 at the switch), cut where the other cubic co
    is certainly positive (the other control has switched before); merged, as a list of intervals"""
    if hi <= lo:
        return []
    _eval_on = lambda cc, P: _piece_enc(cc, P, ev if cc is c else evo)
    out = []
    n = NWIN
    h = (hi - lo) / n
    cur = None
    for k in range(n):
        a = lo + h * k
        b = hi if k == n - 1 else lo + h * (k + 1)
        P = I(a, b)
        if _eval_on(co, P).lo > 0:
            break
        v = _eval_on(c, P)
        if v.lo > 0 or v.hi < 0:
            if cur is not None:
                out.append(cur)
                cur = None
            continue
        # refine the piece once
        sub = []
        m = 0.5 * (a + b)
        for Q in (I(a, m), I(m, b)):
            vq = _eval_on(c, Q)
            if not (vq.lo > 0 or vq.hi < 0):
                sub.append(Q)
        if not sub:
            if cur is not None:
                out.append(cur)
                cur = None
            continue
        Pn = I(sub[0].lo, sub[-1].hi)
        if cur is not None and cur.hi >= Pn.lo:
            cur = I(cur.lo, Pn.hi)
        else:
            if cur is not None:
                out.append(cur)
            cur = Pn
    if cur is not None:
        out.append(cur)
    return out


# ---- the mean value form through the implicit root (regular boxes) ---------------------------------
def _sin_cos_jet(x, dirs, n):
    s, c = sin_cos(x)
    ds = [I(0.0)] * n
    dc = [I(0.0)] * n
    for k, sg in dirs:
        ds[k] = c * float(sg)
        dc[k] = -s * float(sg)
    return J(s, ds), J(c, dc)


def vals_jet(b):
    """the cell point of the Box b as jets in the directions (r2, psi, theta2, t)"""
    n = 4
    v = SV()
    v.nodiv = False
    v.regular = True
    v.eps = I(1.0)
    v.r2 = J.var(b.r, 0, n)
    v.zeta2 = v.r2
    sp, cp = _sin_cos_jet(b.xp, [(1, 1)], n)
    v.spe = anchored(b.kp, sp, cp)[0]
    s2, c2 = _sin_cos_jet(b.x2, [(2, 1)], n)
    v.e2 = anchored(b.k2, s2, c2)[::-1]
    s1, c1 = _sin_cos_jet(b.x2 - b.xp, [(2, 1), (1, -1)], n)
    v.e1 = anchored(b.k2 - b.kp, s1, c1)[::-1]
    v.r1 = 1.0 - v.r2
    v.z1 = (v.r1 * v.e1[0], v.r1 * v.e1[1])
    v.Z2 = (v.zeta2 * v.e2[0], v.zeta2 * v.e2[1])
    v.Z3 = ((v.r1 * v.zeta2) * v.spe) * (-2.0)
    return v


def coeffs_jet(v, u, w):
    d = dvec(u, w)
    cz = J.const(0.0, 4) if re_zero(d) else v.Z3 * d[0]
    return [cz, v.Z2[0] * d[0] + v.Z2[1] * d[1], (v.z1[0] * d[0] + v.z1[1] * d[1]) * 0.5,
            J.const(c3(u, w), 4)]


def _tight_root(c, T):
    lo, hi = T.lo, T.hi
    for _ in range(60):
        if hi - lo <= 1e-15 * max(1.0, hi):
            break
        m = 0.5 * (lo + hi)
        v = horner(c, I(m))
        if v.lo > 0:
            hi = m
        elif v.hi < 0:
            lo = m
        else:
            break
    return I(lo, hi)


def _jet_image(b, u, w, T, trust):
    vj = vals_jet(b)
    Tj = J.var(T, 3, 4)
    Dj = horner(coeffs_jet(vj, u, w), Tj)
    dt = Dj.d[3]
    if not dt.lo > 0:
        return None
    tau = [-(Dj.d[k] / dt) for k in range(3)]
    m = 3 - u - w
    z1t, Z2t, _ = flow_scaled(vj, u, Tj)
    w1 = rot(m, z1t)
    W2 = rot(m, Z2t)
    a2 = w1[0].sqr() + w1[1].sqr()
    B2 = W2[0].sqr() + W2[1].sqr()
    try:
        a = a2.sqrt()
        B = B2.sqrt()
        jr2 = (B * 4.0) / (a + (a2 + B * 4.0).sqrt()).sqr()
    except ZeroDivisionError:
        return None
    cen = 1 if new_cell(u, w) == 1 else -1
    jth2 = _arg(W2[0], W2[1], cen)
    qx = W2[0] * w1[0] + W2[1] * w1[1]
    qy = W2[1] * w1[0] - W2[0] * w1[1]
    jpsi = _arg(qx, qy, 1)
    if jth2 is None or jpsi is None:
        return None
    return [[G.d[k] + G.d[3] * tau[k] for k in range(3)] for G in (jr2, jpsi, jth2)]


def jacobian(b, o, u):
    """an enclosure of the Jacobian of the coordinates (r2', psi', theta2') of the single-branch
    outcome o in (r2, psi, theta2) on the Box b, through the implicit root"""
    return _jet_image(b, u, o.w, o.T, o.trust)


def image_mv(b, o, u):
    """the centred form of the coordinates of the single-branch outcome o on the Box b (needs
    dD/dt > 0 on the box x T); None if it does not apply"""
    if not isinstance(b, Box) or o.tie:
        return None
    w, T = o.w, o.T
    E = BoxEval(b)
    if not pos_on(deriv(E.cf[w]), T.lo, T.hi):
        return None
    cb = b.center()
    cv = box_vals(cb)
    cDc = coeffs(cv, u, w)
    lo, hi = T.lo, T.hi
    if not horner(cDc, I(hi)).lo > 0:
        return None
    if lo == 0 or not horner(cDc, I(lo)).hi < 0:
        g = float_first_upcrossing([x.mid() for x in cDc])
        if g is None:
            return None
        l2 = max(g * (1 - 1e-9), lo)
        if not horner(cDc, I(l2)).hi < 0:
            return None
        lo = l2
    Tc = _tight_root(cDc, I(lo, hi))
    ci = image(cv, u, w, Tc, o.trust)
    if ci.psi is None or ci.th2 is None:
        return None
    Jm = _jet_image(b, u, w, T, o.trust)
    if Jm is None:
        return None
    rad = [b.r - b.r.mid(), b.xp - b.xp.mid(), b.x2 - b.x2.mid()]
    out = []
    for row, Gc in zip(Jm, (ci.r2, ci.psi, ci.th2)):
        acc = Gc
        for k in range(3):
            acc = acc + row[k] * rad[k]
        out.append(acc)
    return out
