"""The Fuller-Poincare map at a point, exactly as the Lean definitions say, in Arb ball arithmetic.

Lean sources: ``SmoothedPolygons/Ch13/Defs.lean`` (``flow``, ``ham``, ``IsFirstControl``,
``firstControl``, ``firstSwitchTime``, ``tau``), ``Ch13/FirstControl.lean`` (Lemma 13.2.6, the
lexicographic rule), ``Ch13/PoincareMap.lean`` (``poincare``, ``poincareAngZero``),
``Ch15/CellCoordinates.lean`` (``cellPoint``, ``cellCoords``, ``cellTau``, ``cellTwoDomain``).

Conventions (as in Lean): a point of C^3 is ``z = (z1, z2, z3)`` (Lean's ``z 0, z 1, z 2``); the
controls are ``V_T = {1, zeta, zeta^2}``, indexed ``0, 1, 2`` (``ZETA_POW[k] = zeta^k``).

* ``flow(t, z, u) = (z1 - i t u, z2 + z1 t - i t^2 u/2, z3 + z2 t + z1 t^2/2 - i t^3 u/6)``.
* ``ham(w, v) - ham(w, u) = RR(v - u, w3)``, so along the trajectory with the constant control ``u``
  the control ``v`` beats ``u`` at time ``t`` iff ``D_{u,v}(t) := RR(v - u, z3(t; z, u)) > 0``, a
  real cubic in ``t`` with coefficients ``RR(d, z3), RR(d, z2), RR(d, z1)/2, RR(d, -iu)/6``,
  ``d = v - u`` (``ham_flow_sub_ham_flow``); its ``t^3`` coefficient is ``+-sqrt3/12 != 0``.
* **First control** (``IsFirstControl z u``): ``u`` is optimal along its own trajectory on some
  ``[0, eps]``, i.e. for both ``v != u`` the cubic ``D_{u,v}`` is ``<= 0`` near ``0+``: its lowest
  nonzero coefficient is negative (``first_control``). Lemma 13.2.6 (the lexicographic order of the
  control vectors, ties ``{zeta^i, zeta^(i+1)}`` broken towards ``zeta^i``) gives the same control
  (``lex_first_control``, used as a cross-check).
* **First switching time** (``firstSwitchTime``): ``inf {t > 0 | some v beats u at t}`` =
  ``min_v inf {t > 0 | D_{u,v}(t) > 0}``: for each ``v`` the first positive root of odd
  multiplicity of ``D_{u,v}`` (a sign change; a tangency, a double root at which ``D <= 0`` on both
  sides, is not a switch), found by rigorous isolation of the real roots on the monotone pieces of
  the cubic (``first_upcrossing``).
* ``poincare z = flow(t_sw, z, u)``. Its third coordinate lies on the wall ``W_m = R_{<=0} zeta^m``
  between ``u`` and the beating control ``v`` (``m`` the third index); the class in
  ``Xi_{W,0}/V_T`` is that of the rotation ``w = zeta^(-m) F(z)`` (``classOf_smul_scale``), with
  ``w3 in R_{<0}`` when the third control is strictly beaten at ``t_sw`` (then the cell coordinates
  ``cellCoords w`` are the unique coordinates of the class, ``cellClass_cellCoords``). The first
  control of ``F(z)`` is ``v`` (``firstControl_poincare_ne``), so that of ``w`` is
  ``zeta^(-m) v``: ``zeta`` (the image is in the first big cell, ``theta2 in (0, pi]``) or
  ``zeta^2`` (the second, ``theta2 in (-pi, 0]``).

Undecidable sign tests (a ball containing 0 that is not exactly 0: a tie, a tangency, or too little
precision) raise ``Undecided``; nothing is ever guessed. Exact face points are given with exact
anchors (``Angle``): ``theta2 = pi`` is ``Angle(2, 0)`` (``2 * pi/2 + 0``), so that ``sin theta2 = 0``
exactly.
"""
from flint import arb, acb, ctx


class Undecided(Exception):
    """A sign that the ball arithmetic cannot decide."""


# ---- precision and constants --------------------------------------------------------------------
_PREC = [0]
_C = {}


def set_prec(bits):
    """Working precision (bits) of the point evaluator; recomputes the constants."""
    ctx.prec = bits
    _PREC[0] = bits
    s3 = arb(3).sqrt()
    z = acb(arb(-1) / 2, s3 / 2)
    _C.update(PI=arb.pi(), SQ3=s3, ZETA=z,
              ZP=[acb(1), z, acb(arb(-1) / 2, -s3 / 2)], I=acb(0, 1))


def prec():
    return _PREC[0]


set_prec(200)


def ZP(k):
    """zeta^k"""
    return _C['ZP'][k % 3]


# ---- angles with exact anchors ------------------------------------------------------------------
class Angle:
    """The angle k pi/2 + x (k an integer, x an arb or a number): exact at the faces."""
    __slots__ = ('k', 'x')

    def __init__(self, k, x=0):
        self.k = k
        self.x = x

    def value(self):
        return _C['PI'] * self.k / 2 + arb(self.x)

    def sin_cos(self):
        x = arb(self.x)
        s, c = x.sin(), x.cos()
        m = self.k % 4
        if m == 0:
            return s, c
        if m == 1:
            return c, -s
        if m == 2:
            return -s, -c
        return -c, s

    def __sub__(self, o):
        return Angle(self.k - o.k, arb(self.x) - arb(o.x))

    def __repr__(self):
        return 'Angle(%d, %s)' % (self.k, self.x)


def as_angle(a):
    return a if isinstance(a, Angle) else Angle(0, a)


# ---- basic operations ---------------------------------------------------------------------------
def RR(a, b):
    """RR(a, b) = Re(conj(a) b)"""
    return a.real * b.real + a.imag * b.imag


def flow(t, z, u):
    I = _C['I']
    t = arb(t)
    return (z[0] - I * t * u,
            z[1] + z[0] * t - I * t * t * u / 2,
            z[2] + z[1] * t + z[0] * t * t / 2 - I * t * t * t * u / 6)


def cubic(z, u, v):
    """coefficients [c0, c1, c2, c3] of D_{u,v}(t) = RR(v - u, z3(t; z, u))"""
    d = v - u
    return [RR(d, z[2]), RR(d, z[1]), RR(d, z[0]) / 2, RR(d, -_C['I'] * u) / 6]


def sign(x):
    """+1, -1, or 0 (exact zero); Undecided otherwise"""
    if x.is_zero():
        return 0
    if x > 0:
        return 1
    if x < 0:
        return -1
    raise Undecided(str(x))


def peval(c, t):
    r = c[-1]
    for a in reversed(c[:-1]):
        r = r * t + a
    return r


def pderiv(c):
    return [c[k] * k for k in range(1, len(c))]


# ---- cell coordinates ---------------------------------------------------------------------------
def cell_point(r2, psi, th2):
    """cellPoint (r2, psi, theta2) = ((1 - r2) e^{i(theta2 - psi)}, r2 e^{i theta2},
    -2 (1 - r2) r2 sin psi); psi, theta2 numbers or Angles."""
    r2 = arb(r2)
    psi, th2 = as_angle(psi), as_angle(th2)
    r1 = 1 - r2
    s2, c2 = th2.sin_cos()
    s1, c1 = (th2 - psi).sin_cos()
    sp, _ = psi.sin_cos()
    return (acb(r1 * c1, r1 * s1), acb(r2 * c2, r2 * s2), acb(-2 * r1 * r2 * sp, 0))


def tau(z):
    """time reversal (z1, z2, z3) -> (conj z1, -conj z2, conj z3)"""
    return (z[0].conjugate(), -z[1].conjugate(), z[2].conjugate())


def rotate(v, z):
    return (v * z[0], v * z[1], v * z[2])


def arg_in(x, y, center):
    """the angle of (x, y) in the branch (center - pi, center + pi] (arb), from the formula that is
    valid where the signs of the rotated point are certain."""
    PI = _C['PI']
    cs, sn = center.cos(), center.sin()
    xr = x * cs + y * sn
    yr = y * cs - x * sn
    if xr > 0:
        return center + (yr / xr).atan()
    if yr > 0:
        return center + PI / 2 - (xr / yr).atan()
    if yr < 0:
        return center - PI / 2 - (xr / yr).atan()
    raise Undecided('angle near the branch cut or near 0')


def cell_coords(w, cell):
    """cellCoords w = (r2, psi, theta2) for w with w3 in R_{<0}; cell = 1 (first control zeta,
    theta2 in (0, pi]) or 2 (first control zeta^2, theta2 in (-pi, 0]). psi in (0, pi)."""
    PI = _C['PI']
    a = abs(w[0])
    b = abs(w[1])
    s = 2 / (a + (a * a + 4 * b).sqrt())
    r2 = s * s * b
    th2 = arg_in(w[1].real, w[1].imag, PI / 2 if cell == 1 else -PI / 2)
    q = w[1] * w[0].conjugate()
    psi = arg_in(q.real, q.imag, PI / 2)
    return (r2, psi, th2)


# ---- first control ------------------------------------------------------------------------------
def first_control(z):
    """the index k of the first control zeta^k (semantic IsFirstControl)"""
    good = []
    for k in range(3):
        u = ZP(k)
        ok = True
        for j in range(3):
            if j == k:
                continue
            c = cubic(z, u, ZP(j))
            s = 0
            for a in c:
                s = sign(a)
                if s != 0:
                    break
            if s > 0:
                ok = False
                break
        if ok:
            good.append(k)
    if len(good) != 1:
        raise RuntimeError('no unique first control: %r' % good)
    return good[0]


def control_vector(z, u):
    return (RR(z[2], u), RR(z[1], u), RR(z[0], u))


def lex_first_control(z):
    """Lemma 13.2.6: the lexicographic maximizers V_{T,max}; a singleton {u} gives u, a pair
    {zeta^i, zeta^(i+1)} gives zeta^i."""
    def lexlt(k, j):  # v(z, zeta^k) < v(z, zeta^j): v(z, zeta^j) - v(z, zeta^k) = v(z, d)
        d = ZP(j) - ZP(k)
        for x in control_vector(z, d):
            s = sign(x)
            if s != 0:
                return s > 0
        return False
    vmax = [k for k in range(3) if not any(lexlt(k, j) for j in range(3) if j != k)]
    if len(vmax) == 1:
        return vmax[0]
    if len(vmax) == 2:
        a, b = vmax
        return a if (a + 1) % 3 == b else b
    raise RuntimeError('V_T,max = V_T (z = 0?)')


# ---- the first switching time -------------------------------------------------------------------
def _real_roots_pos(c):
    """certainly positive real roots (sorted) of a polynomial of degree <= 2 with ball coefficients,
    each root certainly simple; Undecided if a root is double or near 0."""
    c = list(c)
    while c and c[-1].is_zero():
        c.pop()
    if len(c) <= 1:
        return []
    if len(c) == 2:
        r = -c[0] / c[1]
        return _pos_only([r])
    a, b, cc = c[2], c[1], c[0]
    if sign(a) == 0:
        return _pos_only([-cc / b])
    disc = b * b - 4 * a * cc
    s = sign(disc)
    if s < 0:
        return []
    if s == 0:
        raise Undecided('double critical point')
    sq = disc.sqrt()
    r1 = (-b - sq) / (2 * a)
    r2 = (-b + sq) / (2 * a)
    rs = _pos_only([r1, r2])
    rs.sort(key=lambda x: x.mid())
    return rs


def _pos_only(rs):
    out = []
    for r in rs:
        if r > 0:
            out.append(r)
        elif r <= 0:
            continue
        else:
            raise Undecided('root near t = 0')
    return out


def _refine_increasing(c, a, b):
    """the unique root of the polynomial c on [a, b], where it is increasing with c(a) < 0 < c(b)"""
    dc = pderiv(c)
    for _ in range(4 * prec()):
        m = (a + b) / 2
        m = arb(m.mid())
        v = peval(c, m)
        if v > 0:
            b = m
        elif v < 0:
            a = m
        else:
            break
        if (b - a).mid() < arb(2) ** (-prec() + 8) * (1 + abs(a.mid())):
            break
    T = a.union(b)
    # interval Newton steps
    for _ in range(4):
        d = peval(dc, T)
        if not d > 0:
            break
        m = arb(T.mid())
        N = m - peval(c, m) / d
        T2 = N.intersection(T) if N.overlaps(T) else None
        if T2 is None:
            break
        T = T2
    return T


def first_upcrossing(c):
    """inf {t > 0 | P(t) > 0} for the cubic P = c (ball coefficients, c[3] != 0) that is <= 0 on
    some (0, eps]; None for +infinity. The low coefficients that are exactly 0 are factored out
    (t^k P1 with P1(0) != 0); the positive axis is cut at the critical points of P1, on whose
    monotone pieces the sign changes are decided by the values at the ends."""
    c = list(c)
    k = 0
    while k < 3 and c[k].is_zero():
        k += 1
    P = c[k:]
    s0 = sign(P[0])
    if s0 > 0:
        raise RuntimeError('the control is not optimal at t = 0+')
    if len(P) == 1:
        return None
    crit = _real_roots_pos(pderiv(P))
    pts = [arb(0)] + crit
    vals = [P[0]] + [peval(P, x) for x in crit]
    for i in range(1, len(pts)):
        s = sign(vals[i])
        if s > 0:
            return _refine_increasing(P, pts[i - 1], pts[i])
        if s == 0:
            raise Undecided('critical value 0 (tangency)')
    # last piece: monotone towards the sign of the leading coefficient
    if P[-1] < 0:
        return None
    a = pts[-1]
    b = a + 1
    while not peval(P, b) > 0:
        b = 2 * b
    return _refine_increasing(P, a, b)


class Step:
    """One step of the honest map from a Cartesian point: first control index k, switching time t
    (ball), beating control index j, wall index m, image F(z), rotated image w = zeta^(-m) F(z),
    the cell of w (1 or 2) and its coordinates (r2, psi, theta2), and the value of the third
    cubic at t_sw (< 0: the image is off the corner z3 = 0)."""

    def __init__(self, z):
        self.z = z
        k = first_control(z)
        self.k = k
        u = ZP(k)
        cands = {}
        self.cubics = {}
        for j in range(3):
            if j == k:
                continue
            c = cubic(z, u, ZP(j))
            self.cubics[j] = c
            cands[j] = first_upcrossing(c)
        fin = [(t, j) for j, t in cands.items() if t is not None]
        if not fin:
            raise RuntimeError('no switch')
        if len(fin) == 2:
            (t1, j1), (t2, j2) = fin
            if t1 < t2:
                fin = [(t1, j1)]
            elif t2 < t1:
                fin = [(t2, j2)]
            else:
                raise Undecided('tie of the two switching times (z3(t_sw) = 0?)')
        self.t, self.j = fin[0]
        self.m = 3 - k - self.j
        other = [j for j in range(3) if j not in (k, self.j)][0]
        self.other_val = peval(self.cubics[other], self.t)
        self.F = flow(self.t, z, u)
        self.w = rotate(ZP(-self.m), self.F)
        self.newcell = 1 if (self.j - self.m) % 3 == 1 else 2
        if not self.other_val < 0:
            self.coords = None   # the image has z3 = 0 (or undecided): a face class
        else:
            self.coords = cell_coords(self.w, self.newcell)


def step_coords(p):
    """one step of F on the class of cellPoint p (p = (r2, psi, theta2), numbers or Angles)"""
    return Step(cell_point(*p))


def iterate(p, n):
    """the cell coordinates of F^j (cellClass p), j = 1..n, with the cells"""
    out = []
    for _ in range(n):
        s = step_coords(p)
        if s.coords is None:
            raise Undecided('face class')
        out.append((s.newcell, s.coords, s))
        p = s.coords
    return out


def weighted_norm(z):
    return (abs(z[0]) ** 6 + abs(z[1]) ** 3 + abs(z[2]) ** 2).root(6)


def cell_tau(p):
    """cellTau (r2, psi, theta2) = (r2, pi - psi, (pi if theta2 >= 0 else -pi) - theta2)"""
    PI = _C['PI']
    r2, psi, th2 = p
    return (r2, PI - psi, (PI if th2 >= 0 else -PI) - th2)


def image_first_control(s):
    """the first control of F(z) for a Step s: the rotated image w = zeta^(-m) F(z) has w3 real (it
    lies on the wall W_m: z3(t_sw) in W_m, poincare_mem_walls), so w3 is replaced by its real part
    (exact tie of the controls at the wall); firstControl(F z) = zeta^m firstControl(w)
    (equivariance, poincare_smul)"""
    w = (s.w[0], s.w[1], acb(s.w[2].real, 0))
    return (s.m + first_control(w)) % 3
