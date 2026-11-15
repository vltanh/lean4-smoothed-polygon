"""The arc parameters ``(eps, Y, f0, g0, q, p)`` of an ``e2``-arc and the one-step map on them, as
``SmoothedPolygons/Ch14/ArcParams.lean`` and ``ArcStepClosed.lean`` define them (``ArcParams``,
``ArcParams.step``, ``tauSw``, ``stepK``, ``rel``, ``relT``, ``Phi``, ``Psi``, ``psiE``, ``YNew``,
``YNew'``, ``f0New``, ``pNew``, ``qNew``), and the region ``arcRegion`` (``G*``,
``Ch14/ArcConditions.lean``). Generic in the number type (``reinhardt.MP`` or ``reinhardt.ARB``).

Along the arc, with ``tau = t/eps`` (Theorem 1.3, ``arc_normalForm``):
``f(tau) = -1 + A e^{-tau} + B e^{-2 tau} + Y tau e^{-tau}``, ``B = Y - 1 + q``, ``A = 1 + f0 - B``;
``g(tau) = -1 + A' e^{tau} + B' e^{2 tau} - Y' tau e^{tau}``, ``B' = Y' - 1 + p``,
``A' = 1 + g0 - B'``; ``Y' = (1 + eps^2)/(eps^2 Y)``. ``F = e^tau f`` has
``F' = -e^{-tau}(y^2 - Y y + B)`` and ``G = e^{-tau} g`` has ``G' = e^{-tau}(B' y^2 - Y' y + 1)``
(``y = e^tau``): both are monotone between the explicit critical points, so zeros and minima on an
interval are found exactly from the pieces (``pieces``); in Arb every sign is decided or
``Undecided`` is raised.
"""
from .fuller import Undecided


class AP:
    """``ArcParams`` (``g0 = 0`` on the section)"""

    def __init__(self, eps, Y, f0, g0, q, p, num):
        self.num = num
        self.eps, self.Y, self.f0, self.g0, self.q, self.p = eps, Y, f0, g0, q, p
        self.Yp = (1 + eps ** 2) / (eps ** 2 * Y)
        self.B = Y - 1 + q
        self.A = 1 + f0 - self.B
        self.Bp = self.Yp - 1 + p
        self.Ap = 1 + g0 - self.Bp

    @classmethod
    def of(cls, d, num):
        return cls(d['eps'], d['Y'], d['f0'], d['g0'], d['q'], d['p'], num)

    def floats(self):
        m = self.num.mid
        return dict(eps=m(self.eps), Y=m(self.Y), Yp=m(self.Yp), f0=m(self.f0), q=m(self.q),
                    p=m(self.p), r=m(self.radius()))

    # the functions of the arc
    def f(self, t):
        e = self.num.exp(-t)
        return -1 + self.A * e + self.B * e * e + self.Y * t * e

    def fDeriv(self, t):
        e = self.num.exp(-t)
        return -self.A * e - 2 * self.B * e * e + self.Y * (1 - t) * e

    def g(self, t):
        e = self.num.exp(t)
        return -1 + self.Ap * e + self.Bp * e * e - self.Yp * t * e

    def F(self, t):
        """``F(tau) = e^tau f(tau) = -e^tau + A + B e^{-tau} + Y tau``"""
        return -self.num.exp(t) + self.A + self.B * self.num.exp(-t) + self.Y * t

    def G(self, t):
        """``G(tau) = e^{-tau} g(tau) = -e^{-tau} + A' + B' e^tau - Y' tau``"""
        return -self.num.exp(-t) + self.Ap + self.Bp * self.num.exp(t) - self.Yp * t

    def radius(self):
        """``r = eps (Y' - 2)/2`` (the chart radius ``X00``)"""
        return self.eps * (self.Yp - 2) / 2

    def rel(self):
        """the quadric relation (2.1), ``ArcParams.rel``"""
        e, Y, f0, q, p = self.eps, self.Y, self.f0, self.q, self.p
        k = 1 + e ** 2
        return (k ** 2 * q ** 2 - 2 * q * (k ** 2 * f0 - Y ** 2 * e ** 2 * (1 - e ** 2) * p
                                           + 2 * Y ** 2 * e ** 2 - k * Y)
                + Y ** 4 * e ** 4 * p ** 2 + 2 * Y ** 2 * e ** 2 * (Y - 2) * p
                - 2 * Y ** 2 * e ** 2 * k * f0 * p + 4 * Y ** 2 * e ** 2 * k * f0
                - 2 * (2 * e ** 2 + 1) * k * Y * f0 + k ** 2 * f0 ** 2 + 4 * k ** 2 * f0)

    def rel_roots(self):
        """the two roots in ``q`` of ``rel = 0`` (a quadratic, leading coefficient ``(1 + eps^2)^2``),
        or ``None``"""
        e, Y, f0, p = self.eps, self.Y, self.f0, self.p
        k = 1 + e ** 2
        a = k ** 2
        b = -2 * (k ** 2 * f0 - Y ** 2 * e ** 2 * (1 - e ** 2) * p + 2 * Y ** 2 * e ** 2 - k * Y)
        c = (Y ** 4 * e ** 4 * p ** 2 + 2 * Y ** 2 * e ** 2 * (Y - 2) * p
             - 2 * Y ** 2 * e ** 2 * k * f0 * p + 4 * Y ** 2 * e ** 2 * k * f0
             - 2 * (2 * e ** 2 + 1) * k * Y * f0 + k ** 2 * f0 ** 2 + 4 * k ** 2 * f0)
        D = b * b - 4 * a * c
        if self.num.sign(D) < 0:
            return None
        sD = self.num.sqrt(D)
        return ((-b - sD) / (2 * a), (-b + sD) / (2 * a))

    def relT(self):
        """``R~`` (INV (2.2)); ``rel = Y^2 eps^4 R~`` (``rel_eq``)"""
        Y, Yp, f0, q, p = self.Y, self.Yp, self.f0, self.q, self.p
        x, y = Y - 2, Yp - 2
        return ((Yp * (f0 - q) - Y * p) ** 2 - 4 * p * q + 2 * (Y * Yp - 1) * (y * q + x * p)
                + 2 * Yp * (3 - x * y) * f0)

    # the closed forms of ArcStepClosed.lean (A' = 2 - Y' - p, g0 = 0)
    def Phi(self, s):
        Y, Yp, p = self.Y, self.Yp, self.p
        return (self.Bp * s ** 4 - 3 * Yp * s ** 3 + (Yp * self.A + Y * (2 - Yp - p) + 2 * Y * Yp + 2)
                * s ** 2 - 3 * Y * s + self.B)

    def Psi(self, s):
        Y, Yp, p = self.Y, self.Yp, self.p
        return ((Y * self.Bp - Yp) * s ** 2 + (Yp * self.A + Y * (2 - Yp - p)) * s
                + (Yp * self.B - Y))

    def psiE(self, s):
        return -3 * self.Yp * s ** 3 + (2 * self.Y * self.Yp + 2) * s ** 2 - self.Y ** 2

    def YNew(self, s): return (self.Yp * s ** 2 - 2 * s + self.Y) / (self.Y - s)
    def YNew_(self, s): return self.Y / (self.Y - s)
    def f0New(self, s): return s ** 2 * self.Psi(s) / (self.Y * (self.Y - s) ** 2)
    def pNew(self, s): return (s ** 2 - self.Y * s + self.B) / (self.Y - s) ** 2
    def qNew(self, s): return self.Phi(s) / (self.Y - s) ** 2

    # the monotone pieces of F and G
    def _crit(self, a2, a1, a0, L):
        """the ``tau in (0, L)`` with ``a2 y^2 + a1 y + a0 = 0``, ``y = e^tau`` (sorted)"""
        num = self.num
        out = []
        if num.sign(a2) == 0:
            if num.sign(a1) != 0:
                ys = [-a0 / a1]
            else:
                ys = []
        else:
            D = a1 * a1 - 4 * a2 * a0
            sD = num.sign(D)
            if sD < 0:
                ys = []
            else:
                r = num.sqrt(D) if sD > 0 else num.zero
                ys = [(-a1 - r) / (2 * a2), (-a1 + r) / (2 * a2)]
        for y in ys:
            if num.sign(y - 1) > 0:
                t = num.log(y)
                if num.sign(t - L) < 0:
                    out.append(t)
        out.sort(key=num.mid)
        return out

    def pieces(self, which, L):
        """the breakpoints ``0 = t_0 < ... < t_n = L`` of the monotone pieces of ``F`` or ``G`` on
        ``[0, L]``"""
        if which == 'F':
            c = self._crit(self.num.one, -self.Y, self.B, L)
        else:
            c = self._crit(self.Bp, -self.Yp, self.num.one, L)
        return [self.num.zero] + c + [L]

    def first_zero_F(self, L, iters=None):
        """the least zero of ``F`` (equivalently of ``f``) in ``(0, L]`` at which ``F`` changes sign,
        as a ball (Arb) or a number (mpmath), or ``None`` if ``F > 0`` on ``(0, L]``.
        ``tauSw = sInf {tau > 0 | f tau = 0}`` when ``F(0) = f0 > 0`` (``tauSw_spec``)."""
        num = self.num
        pts = self.pieces('F', L)
        s0 = num.sign(self.F(pts[0]))
        if s0 <= 0:
            raise Undecided('F(0) = f0 <= 0')
        for a, b in zip(pts[:-1], pts[1:]):
            sb = num.sign(self.F(b))
            if sb > 0:
                continue
            if sb == 0 and b is L:
                return L
            lo, hi = num.exact(a), num.exact(b)
            if num.sign(self.F(lo)) <= 0 or num.sign(self.F(hi)) >= 0:
                raise Undecided('the zero of F at a piece end')
            if num.name == 'mpmath':
                return self._newton_bracket(lo, hi)
            n = iters or num.bits + 10
            for _ in range(n):
                m = num.bisect_mid(lo, hi)
                try:
                    sm = num.sign(self.F(m))
                except Undecided:
                    break
                if sm > 0:
                    lo = m
                elif sm < 0:
                    hi = m
                else:
                    return m
            return num.ball(lo, hi)
        return None

    def _newton_bracket(self, lo, hi):
        """the zero of ``F`` in ``[lo, hi]`` (``F(lo) > 0 > F(hi)``, ``F`` monotone there) by
        Newton's method safeguarded by bisection (mpmath)"""
        num = self.num
        tol = (abs(lo) + abs(hi)) * num.mk(2) ** (-num.bits)
        t = (lo + hi) / 2
        for _ in range(4 * num.bits):
            Ft = self.F(t)
            if Ft == 0:
                return t
            if Ft > 0:
                lo = t
            else:
                hi = t
            if hi - lo <= tol:
                break
            dF = -num.exp(t) - self.B * num.exp(-t) + self.Y
            tn = t - Ft / dF if dF != 0 else lo - 1
            if not lo < tn < hi:
                tn = (lo + hi) / 2
            if abs(tn - t) <= tol:
                t = tn
                break
            t = tn
        return t

    def min_on(self, which, a, b):
        """the minimum of ``F`` or ``G`` on ``[a, b]`` (a ball enclosing it in Arb): the smallest
        value at the ends and at the critical points inside"""
        num = self.num
        fn = self.F if which == 'F' else self.G
        pts = [t for t in self.pieces(which, b) if num.mid(t) > num.mid(a)]
        vals = [fn(a)] + [fn(t) for t in pts]
        return min(vals, key=num.mid)

    # the map
    def step(self):
        """``ArcParams.step (qNew s)`` (Theorem 2.1, with ``q_new = Phi(s)/(Y - s)^2``,
        ``arcQ_reinPoincare``), ``s = e^{tauSw}``; requires a switch inside the star domain. Returns
        the image and ``(tauSw, s, k)``."""
        num = self.num
        L = num.log(self.Y)
        tau = self.first_zero_F(L)
        if tau is None:
            raise ValueError('no switch before the exit')
        s = num.exp(tau)
        k = self.Y * num.exp(-tau) - 1
        new = AP(k * self.eps, 1 + (self.Yp * s - 1) / k, self.g(tau) / k ** 2, num.zero,
                 self.qNew(s), -self.fDeriv(tau) / k ** 2, num)
        return new, (tau, s, k)

    def region_margins(self):
        """the margins of ``arcRegion`` (``G*``): ``r``, ``f0``, ``-q``, ``p`` and
        ``E = (Y - 2) - (Y - 1)(Y' - 2)``, each ``> 0`` (``>= 0`` for ``-q`` and ``E``) in ``G*``"""
        return dict(r=self.radius(), f0=self.f0, mq=-self.q, p=self.p,
                    E=(self.Y - 2) - (self.Y - 1) * (self.Yp - 2))

    def in_region(self):
        m = self.region_margins()
        s = self.num.sign
        return s(m['r']) > 0 and s(m['f0']) > 0 and s(m['mq']) >= 0 and s(m['p']) > 0 \
            and s(m['E']) >= 0

    def exit_margins(self):
        """``ArcLeavesStarDomain`` on the parameters: the arc leaves the star domain at
        ``tau = log Y`` before it switches iff ``f > 0`` and ``g > 0`` on ``(0, log Y)``; returns the
        minima of ``F`` on ``[0, log Y]`` and of ``G`` on ``[tau_1, log Y]`` (``tau_1`` the first
        breakpoint of ``G``; ``G(0) = g0 = 0`` with slope ``G'(0) = 1 + B' - Y'`` (``= p`` on the
        section))"""
        num = self.num
        L = num.log(self.Y)
        mF = self.min_on('F', num.zero, L)
        gp = self.pieces('G', L)
        mG = self.min_on('G', gp[1], L)
        return dict(F=mF, G=mG, G0slope=1 + self.Bp - self.Yp, L=L)

    def exits(self):
        m = self.exit_margins()
        s = self.num.sign
        return s(m['F']) > 0 and s(m['G']) > 0 and s(m['G0slope']) > 0
