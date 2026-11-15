"""The Reinhardt system of Chapters 7-12 along an ``e2``-arc, in closed form, and the Lie algebra chart
of Chapter 14: the dynamical system of N4 (Theorem 14.4.1). Generic in the number type: mpmath
(``MP``) or Arb balls (``ARB``, python-flint).

Lean sources: ``SmoothedPolygons/Defs.lean`` (``controlMatrix``, ``rho_i``, ``hamiltonian``, ``J``),
``Ch7/Isolated/Defs.lean`` (``iso_vertexFlow``: ``iso_vfP``, ``iso_vfX``, ``iso_vfG``,
``iso_vfLambda1``, ``iso_vfM``, ``iso_vfC``, ``iso_vfLambdaR``), ``Ch14/LieChart.lean`` (``lieX``,
``lieLambda1``, ``lieLambdaR``, ``lieChart``, ``lieChartInv``), ``Ch14/AnalyticExtension.lean``
(``phaseHam``, ``reinSwitchTime``, ``reinPoincare = Ad_{R^-1}`` of the state at the switch),
``Ch14/Asymptotics.lean`` (``xTildeOut = fullerChartInv qOutCart``), ``Ch14/ArcFrame.lean``
(``ofFrame``, ``frameE``, ``frameF``, ``switchingNum``, ``arcEps``, ``arcY``, ``arcY'``),
``Ch14/ArcCostate.lean`` (``arcVe``, ``arcVf``), ``Ch14/ArcNormalForm.lean`` (``arcF0``, ``arcG0``,
``arcQ``, ``arcP``).

**The closed form.** Along the arc with the constant control ``e_m`` from ``q = (X0, L1, LR)``,
``P = Z_m/<Z_m, X0>`` has ``P^2 = w^2 I`` and ``det(X0 + P) = det P`` (Lemma 7.1.3), so
``X(t) = Ad_{e^{tP}} X0``, ``Lambda_1(t) = Ad_{e^{tP}} Ad_{e^{-t(X0 + P)}} Lambda_1(0)`` and the
quadratures ``iso_vfC``, ``iso_vfLambdaR`` are finite sums ``sum C_{m,k} t^m e^{k w t}``
(exponential polynomials, ``EP``: a dict ``{(m, k): coefficient}``, ``k`` in units of ``w``).
For ``e_2`` (``m = 1``) ``w = 1/(2 eps)``, ``eps = rho_1(X0)``, and ``e^{-2wt} = e^{-tau}``,
``tau = t/eps``. The integrals are exact (``ep_int``); nothing is approximated but the arithmetic.
2x2 matrices are tuples ``(a, b, c, d) = [[a, b], [c, d]]`` (Lean's ``M 0 0, M 0 1, M 1 0, M 1 1``).
"""
import mpmath as mp
from flint import arb, ctx, fmpz_poly

from .fuller import Undecided


# ---- number back ends ---------------------------------------------------------------------------
class MP:
    """mpmath at ``dps`` digits (floating point; signs are taken as computed)"""
    name = 'mpmath'

    def __init__(self, dps=60):
        self.dps = dps
        self.bits = int(dps * 3.33)
        mp.mp.dps = dps
        self.zero, self.one = mp.mpf(0), mp.mpf(1)
        self.sqrt3 = mp.sqrt(3)

    def mk(self, x): return mp.mpf(x)
    def exact(self, x): return x
    def exp(self, x): return mp.exp(x)
    def log(self, x): return mp.log(x)
    def sqrt(self, x): return mp.sqrt(x)
    def mid(self, x): return float(x)
    def rad(self, x): return 0.0
    def sign(self, x): return (x > 0) - (x < 0)
    def ball(self, lo, hi): return (lo + hi) / 2
    def bisect_mid(self, a, b): return (a + b) / 2


class ARB:
    """Arb balls at ``prec`` bits: every ``sign`` is decided rigorously or raises ``Undecided``"""
    name = 'arb'

    def __init__(self, prec=320):
        self.prec = self.bits = prec
        ctx.prec = prec
        self.zero, self.one = arb(0), arb(1)
        self.sqrt3 = arb(3).sqrt()

    def mk(self, x):
        """an exact ball: ints, strings, and mpmath numbers (binary, converted exactly)"""
        if isinstance(x, arb):
            return x
        if isinstance(x, mp.mpf):
            sgn, man, e, _ = x._mpf_
            return arb((-1) ** sgn * int(man)) * arb(2) ** int(e) if man else arb(0)
        return arb(x)

    def exact(self, x): return x.mid()
    def exp(self, x): return x.exp()
    def log(self, x): return x.log()
    def sqrt(self, x): return x.sqrt()
    def mid(self, x): return float(x.mid())
    def rad(self, x): return float(x.rad())

    def sign(self, x):
        if x > 0:
            return 1
        if x < 0:
            return -1
        if x == 0:
            return 0
        raise Undecided('sign of %s' % x.str(5, radius=True))

    def ball(self, lo, hi):
        """the ball containing ``lo`` and ``hi``"""
        return lo.union(hi)

    def bisect_mid(self, a, b):
        return ((a + b) / 2).mid()


# ---- 2x2 matrices -------------------------------------------------------------------------------
def madd(A, B): return (A[0] + B[0], A[1] + B[1], A[2] + B[2], A[3] + B[3])
def msub(A, B): return (A[0] - B[0], A[1] - B[1], A[2] - B[2], A[3] - B[3])
def msc(s, A): return (s * A[0], s * A[1], s * A[2], s * A[3])


def mmul(A, B):
    return (A[0] * B[0] + A[1] * B[2], A[0] * B[1] + A[1] * B[3],
            A[2] * B[0] + A[3] * B[2], A[2] * B[1] + A[3] * B[3])


def comm(A, B): return msub(mmul(A, B), mmul(B, A))
def tf(A, B): return A[0] * B[0] + A[1] * B[2] + A[2] * B[1] + A[3] * B[3]   # traceForm
def mdet(A): return A[0] * A[3] - A[1] * A[2]
def mtr(A): return A[0] + A[3]


def consts(num):
    """``J``, ``R`` (rotation by pi/3), ``R^-1``, ``Z_{e_1}, Z_{e_2}, Z_{e_3}`` (``controlMatrix``)"""
    s3, one, zero = num.sqrt3, num.one, num.zero
    J = (zero, -one, one, zero)
    R = (one / 2, -s3 / 2, s3 / 2, one / 2)
    Ri = (one / 2, s3 / 2, -s3 / 2, one / 2)

    def Z(u):
        return ((u[1] - u[2]) / s3, (u[0] - 2 * u[1] - 2 * u[2]) / 3, u[0], (u[2] - u[1]) / s3)
    ZV = [Z((one, zero, zero)), Z((zero, one, zero)), Z((zero, zero, one))]
    return dict(J=J, R=R, Ri=Ri, ZV=ZV, s3=s3)


def rho(X, s3):
    """``(rho_0, rho_1, rho_2)`` of ``X`` (``Defs.lean``); ``X`` is a star state iff all are > 0
    (with ``det X = 1``, ``tr X = 0``)"""
    a, b, c, _ = X
    return ((c + s3 * a) / s3, (c - s3 * a) / s3, -(3 * b + c) / (2 * s3))


def of_frame(h, e, f, s3):
    """``ofFrame h e f`` (``ArcFrame.lean``)"""
    return (h + f, (e - 2 * h - f) / s3, s3 * f, -(h + f))


def frame_e(M, s3): return s3 * M[1] + 2 * M[0] - M[2] / s3
def frame_f(M, s3): return M[2] / s3


# ---- exponential polynomials --------------------------------------------------------------------
def _put(out, key, v):
    out[key] = out[key] + v if key in out else v


def ep_add(*Fs):
    out = {}
    for F in Fs:
        for key, c in F.items():
            _put(out, key, c)
    return out


def ep_scale(s, F): return {key: s * c for key, c in F.items()}


def ep_mul(F, G):
    out = {}
    for (m1, k1), c1 in F.items():
        for (m2, k2), c2 in G.items():
            _put(out, (m1 + m2, k1 + k2), c1 * c2)
    return out


def ep_int(F, w):
    """``t -> int_0^t F``, exactly: ``int_0^t s^m e^{a s} ds`` (``a = k w != 0``) is
    ``e^{a t} sum_j (-1)^j m!/(m-j)! t^(m-j)/a^(j+1) - (-1)^m m!/a^(m+1)``"""
    out = {}
    for (m, k), c in F.items():
        if k == 0:
            _put(out, (m + 1, 0), c / (m + 1))
            continue
        a = k * w
        fact = 1
        for j in range(m + 1):
            if j > 0:
                fact *= (m - j + 1)
            _put(out, (m - j, k), c * ((-1) ** j * fact) / a ** (j + 1))
        mf = 1
        for i in range(2, m + 1):
            mf *= i
        _put(out, (0, 0), -c * ((-1) ** m * mf) / a ** (m + 1))
    return out


def ep_eval(F, t, num, w):
    tot = num.zero
    cache = {}
    for (m, k), c in F.items():
        if k not in cache:
            cache[k] = num.exp(k * w * t)
        tot = tot + c * t ** m * cache[k]
    return tot


def mep_tf(F, Y): return {key: tf(C, Y) for key, C in F.items()}


def mep_add(*Fs):
    out = {}
    for F in Fs:
        for key, c in F.items():
            out[key] = madd(out[key], c) if key in out else c
    return out


def mep_scale(s, F): return {key: msc(s, c) for key, c in F.items()}


def mep_eval(F, t, num, w):
    tot = (num.zero,) * 4
    for (m, k), C in F.items():
        tot = madd(tot, msc(t ** m * num.exp(k * w * t), C))
    return tot


def ad_split(B, Y, w):
    """for traceless ``B`` with ``B^2 = w^2 I``: ``Ad_{e^{sB}} Y = Y0 + Yp e^{2ws} + Ym e^{-2ws}``"""
    aY = comm(B, Y)
    a2Y = comm(B, aY)
    Yp = msc(1 / (8 * w * w), madd(a2Y, msc(2 * w, aY)))
    Ym = msc(1 / (8 * w * w), msub(a2Y, msc(2 * w, aY)))
    return msub(msub(Y, Yp), Ym), Yp, Ym


def mep_ad(B, F, w, sign=1):
    """``t -> Ad_{e^{sign t B}} F(t)`` for a matrix EP ``F``"""
    out = {}

    def put(key, v):
        out[key] = madd(out[key], v) if key in out else v
    for (m, k), C in F.items():
        Y0, Yp, Ym = ad_split(B, C, w)
        put((m, k), Y0)
        put((m, k + 2 * sign), Yp)
        put((m, k - 2 * sign), Ym)
    return out


class Arc:
    """The arc with the constant control ``e_m`` (``m = 0, 1, 2``) from ``q = (X0, L1, LR)``
    (Lean: ``iso_vertexFlow m q t``), as exponential polynomials in ``t``."""

    def __init__(self, q, m, num, C=None):
        self.num = num
        C = C or consts(num)
        self.C = C
        X0, L10, LR0 = q
        self.q, self.m = q, m
        Zm = C['ZV'][m]
        P = msc(1 / tf(Zm, X0), Zm)                   # iso_vfP
        w = num.sqrt(-mdet(P))
        self.w, self.P = w, P
        A = madd(X0, P)
        J = C['J']
        self.X = mep_ad(P, {(0, 0): X0}, w, +1)       # Ad_{e^{tP}} X0
        Nt = mep_ad(A, {(0, 0): L10}, w, -1)          # Ad_{e^{-tA}} Lambda_1(0)
        self.L1 = mep_ad(P, Nt, w, +1)
        # iso_vfM: M(s) = Ad_{e^{-sA}} Lambda_1(0) + (3/2) Ad_{e^{-sP}} J
        Mt = mep_add(Nt, mep_ad(P, {(0, 0): msc(num.mk(3) / 2, J)}, w, -1))
        X0P, PX0 = comm(X0, P), comm(P, X0)
        self.c = ep_add({(0, 0): tf(LR0, P)}, ep_scale(-1, ep_int(mep_tf(Mt, X0P), w)))
        intc = ep_int(self.c, w)
        MX = {key: comm(Cm, X0) for key, Cm in Mt.items()}
        ent = [ep_int({key: Cm[i] for key, Cm in MX.items()}, w) for i in range(4)]
        intMX = {key: tuple(ent[i].get(key, num.zero) for i in range(4))
                 for key in set().union(*[e.keys() for e in ent])}
        Lt = mep_add({(0, 0): LR0}, {key: msc(-c, PX0) for key, c in intc.items()},
                     mep_scale(-1, intMX))
        self.LR = mep_ad(P, Lt, w, +1)

    def numer(self, j):
        """the cleared switching numerator ``N_{mj} = <LR, Z_j><X, Z_m> - <LR, Z_m><X, Z_j>``
        along the arc (``switchingNum m j``)"""
        ZV, m = self.C['ZV'], self.m
        a = ep_mul(mep_tf(self.LR, ZV[j]), mep_tf(self.X, ZV[m]))
        b = ep_mul(mep_tf(self.LR, ZV[m]), mep_tf(self.X, ZV[j]))
        return ep_add(a, ep_scale(-1, b))

    def state(self, t):
        n, w = self.num, self.w
        return (mep_eval(self.X, t, n, w), mep_eval(self.L1, t, n, w), mep_eval(self.LR, t, n, w))


# ---- the chart and the rotation -----------------------------------------------------------------
def sl2_dual(M1, M2, M3, c1, c2, c3):
    T = tf(M1, comm(M2, M3))
    return msc(1 / T, madd(madd(msc(c1, comm(M2, M3)), msc(c2, comm(M3, M1))),
                           msc(c3, comm(M1, M2))))


def reduced_ham(L1, X, C, num):
    """``reducedHam = <Lambda_1 + (3/2) J, X>``"""
    return tf(madd(L1, msc(num.mk(3) / 2, C['J'])), X)


def lie_chart(r, x, num, C=None):
    """``lieChart (r, x~)``, ``x~ = (x21, l11, l21)``: a section point (``chi23 = 0``,
    ``H(e3) = 0``, ``<X, LR> = 0``, ``det Lambda_1 = 9/4``)"""
    C = C or consts(num)
    x21, l11, l21 = x
    X = (r, -(1 + r * r) / (1 + r * x21), 1 + r * x21, -r)
    L1 = (r * r * l11, (num.mk(9) / 4 + r ** 4 * l11 ** 2) / (num.mk(3) / 2 - r * r * l21),
          -num.mk(3) / 2 + r * r * l21, -r * r * l11)
    h = reduced_ham(L1, X, C, num)
    Z = C['ZV']
    LR = sl2_dual(X, Z[1], Z[2], num.zero, tf(X, Z[1]) * h, tf(X, Z[2]) * h)
    return (X, L1, LR)


def lie_chart_inv(q, num):
    """``lieChartInv``: ``(r, (x21, l11, l21))``"""
    X, L1, _ = q
    r = X[0]
    return (r, ((X[2] - 1) / r, L1[0] / r ** 2, (L1[2] + num.mk(3) / 2) / r ** 2))


def ad_rinv(q, C):
    """``Ad_{R^-1}`` on a phase point (the rotation of ``reinPoincare``)"""
    R, Ri = C['R'], C['Ri']
    return tuple(mmul(mmul(Ri, A), R) for A in q)


def switching_num(q, i, j, C):
    X, _, LR = q
    Z = C['ZV']
    return tf(LR, Z[j]) * tf(X, Z[i]) - tf(LR, Z[i]) * tf(X, Z[j])


def phase_ham(q, j, C, num):
    """``phaseHam q (vertex j)`` (``lambda = -1``)"""
    X, L1, LR = q
    return reduced_ham(L1, X, C, num) - tf(LR, C['ZV'][j]) / tf(X, C['ZV'][j])


def section_residuals(q, C, num):
    """the defining conditions of the section ``N_{9/4}`` (``iso_sectionN``): all ``0`` there"""
    X, L1, LR = q
    Z = C['ZV']
    return dict(trX=mtr(X), trL1=mtr(L1), trLR=mtr(LR), detX=mdet(X) - 1, XLR=tf(X, LR),
                H3=phase_ham(q, 2, C, num), chi23=switching_num(q, 1, 2, C),
                detL1=mdet(L1) - num.mk(9) / 4)


def arc_params(q, C, num):
    """``arcParams q`` and ``arcY'`` (``ArcNormalForm.lean``, ``ArcFrame.lean``) by their
    definitions: ``eps = rho_1``, ``Y = 1 + rho_2/rho_1``, ``Y' = 1 + rho_0/rho_1``,
    ``f0 = (sqrt3/(8 eps^3)) N21(q)``, ``g0 = (sqrt3/(8 eps^3)) N23(q)``,
    ``q = -(sqrt3/(6 eps)) <Lhat, V_e>``, ``p = (2/(sqrt3 eps)) <Lhat, V_f>``,
    ``Lhat = Lambda_1 + (3/2) J``"""
    X, L1, _ = q
    s3 = C['s3']
    r0, r1, r2 = rho(X, s3)
    eps = r1
    xe, xf = frame_e(X, s3), frame_f(X, s3)
    Ve = of_frame(xe, -xe ** 2 / r1, r1, s3)
    Vf = of_frame(xf, r1, -xf ** 2 / r1, s3)
    Lh = madd(L1, msc(num.mk(3) / 2, C['J']))
    nrm = s3 / (8 * eps ** 3)
    return dict(eps=eps, Y=1 + r2 / r1, Yp=1 + r0 / r1, f0=nrm * switching_num(q, 1, 0, C),
                g0=nrm * switching_num(q, 1, 2, C), q=-(s3 / (6 * eps)) * tf(Lh, Ve),
                p=2 / (s3 * eps) * tf(Lh, Vf), r=X[0], rho=(r0, r1, r2))


def section_from_params(eps, Y, f0, q, p, C, num):
    """the section point with the given arc parameters (``arcParams_injOn``): ``X0`` by
    ``(eps, Y)`` (``state_eq_ofFrame``), ``Lhat`` by ``frame_reducedCostate``, ``LR`` by
    ``frame_section_costateR``"""
    s3 = C['s3']
    k = 1 + eps ** 2
    Yp = k / (eps ** 2 * Y)
    xe, xf = -2 * eps * Y, eps * Yp / 2
    X = of_frame(-eps, xe, xf, s3)
    lh = s3 * (Y ** 2 * eps ** 2 * p - k * (2 * eps ** 2 + 1) * f0 + k * q) / (2 * Y)
    le = 2 * s3 * eps ** 2 * (q - k * f0)
    lf = -s3 * (Y ** 2 * eps ** 2 * p - k ** 2 * f0) / (2 * Y ** 2)
    L1 = msub(of_frame(lh, le, lf, s3), msc(num.mk(3) / 2, C['J']))
    h0 = reduced_ham(L1, X, C, num)
    LR = of_frame(-eps * h0, (1 - eps ** 2) * h0 / xf, xf * h0, s3)
    return (X, L1, LR)


def e3_slope(q, C, num):
    """``d/dt (H(e3) - H(e2))`` at ``t = 0`` along the ``e3``-flow, from the vector field
    (``SwitchEntersE2`` needs ``< 0``; ``hasDerivAt_e3_sub_e2``: it is ``-2 sqrt3 p/(Y' - 1)``)"""
    X, L1, LR = q
    Z, J = C['ZV'], C['J']
    P3 = msc(1 / tf(Z[2], X), Z[2])
    dX = comm(P3, X)
    dL1 = comm(L1, X)
    Yh = madd(L1, msc(num.mk(3) / 2, J))
    dLR = msub(msub(comm(P3, LR), msc(tf(LR, P3), comm(P3, X))), comm(Yh, X))
    dh = tf(dL1, X) + tf(Yh, dX)

    def dH(j):
        a, b = tf(LR, Z[j]), tf(X, Z[j])
        return dh - (tf(dLR, Z[j]) * b - a * tf(dX, Z[j])) / b ** 2
    return dH(2) - dH(1)


# ---- the fixed point ----------------------------------------------------------------------------
def fixed_point(num):
    """``rScale`` (the root > 1 of ``1 - 5r - 7r^2 - 5r^3 - 7r^4 - 5r^5 + r^6``) and
    ``xTildeOut = fullerChartInv (equilExact rScale)``"""
    if num.name == 'arb':
        P = fmpz_poly([1, -5, -7, -5, -7, -5, 1])
        big = [z.real for z, _ in P.complex_roots() if z.imag.is_zero() and z.real > 1]
        assert len(big) == 1
        r = big[0]
    else:
        r = mp.findroot(lambda t: 1 - 5 * t - 7 * t ** 2 - 5 * t ** 3 - 7 * t ** 4 - 5 * t ** 5
                        + t ** 6, mp.mpf('6.27'))
    s3 = num.sqrt3
    z1re, z1im = -num.one, (r - 1) / (s3 * (1 + r))
    z2re = -((r ** 3 - 1) / (s3 * (1 + r ** 3)))
    z2im = (1 - 3 * r - 2 * r ** 2 - 3 * r ** 3 + r ** 4) / (3 * (1 + r + r ** 3 + r ** 4))
    xo = (z1re / z1im, 3 * z2re / (2 * z1im ** 2), -(3 * z2im) / (2 * z1im ** 2))
    return r, xo
