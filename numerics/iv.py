"""Rigorous interval arithmetic on Python floats, with directed rounding.

An interval ``I(lo, hi)`` is the closed set ``[lo, hi]`` of reals (``lo``, ``hi`` floats). Every
operation returns an interval that contains every value of the exact real operation on points of
the operands (outward rounding), and is exact when the float result is exact. The rounding is
emulated without changing the FPU mode:

* ``+``, ``-``: TwoSum (the exact error of a float sum) decides whether the rounded sum is below or
  above the true one, and ``nextafter`` moves it outward only when needed;
* ``*``: ``math.fma(a, b, -p)`` is the exact error of the product ``p = a * b``;
* ``/``, ``sqrt``: the residuals ``a - q b`` and ``x - s^2`` (exact by ``fma``) give the direction;
* the transcendental functions (``sin``, ``cos``, ``atan``) are evaluated at the endpoints by
  python-flint's ball arithmetic (Arb, rigorous error bounds), on pieces where they are monotone,
  and converted to floats with directed rounding.

Exactness matters at the faces of the cells: ``0 * x = 0`` and ``sin(0) = 0`` are exact, so a box
with ``r2 in [0, h]`` gives ``z2``, ``x3`` with an exact endpoint ``0`` and the sign facts used by the
checks (``x3 <= 0``, ``r1 r2 sin psi >= 0``) come out of the arithmetic, not from extra hypotheses.

Underflow (results below ``1e-290`` in magnitude) is rounded outward unconditionally; overflow does
not occur in the ranges used here (all quantities are bounded by about ``1e6``).
"""
import math
from math import fma, nextafter, inf, isfinite

from flint import arb, ctx

ctx.prec = 53

_TINY = 1e-290


def add_lo(a, b):
    s = a + b
    bp = s - a
    e = (a - (s - bp)) + (b - bp)
    return nextafter(s, -inf) if e < 0 or (abs(s) < _TINY and s != 0) else s


def add_hi(a, b):
    s = a + b
    bp = s - a
    e = (a - (s - bp)) + (b - bp)
    return nextafter(s, inf) if e > 0 or (abs(s) < _TINY and s != 0) else s


def mul_lo(a, b):
    p = a * b
    if p == 0:
        if a == 0 or b == 0:
            return 0.0
        return -_TINY
    if abs(p) < _TINY:
        return nextafter(p, -inf)
    return nextafter(p, -inf) if fma(a, b, -p) < 0 else p


def mul_hi(a, b):
    p = a * b
    if p == 0:
        if a == 0 or b == 0:
            return 0.0
        return _TINY
    if abs(p) < _TINY:
        return nextafter(p, inf)
    return nextafter(p, inf) if fma(a, b, -p) > 0 else p


def div_lo(a, b):
    """lower bound of a / b (b != 0)"""
    q = a / b
    if a == 0:
        return 0.0
    if abs(q) < _TINY:
        return nextafter(q, -inf)
    r = fma(-q, b, a)  # a - q b, exact
    # true quotient = q + r / b
    if (r > 0 and b < 0) or (r < 0 and b > 0):
        return nextafter(q, -inf)
    return q


def div_hi(a, b):
    q = a / b
    if a == 0:
        return 0.0
    if abs(q) < _TINY:
        return nextafter(q, inf)
    r = fma(-q, b, a)
    if (r > 0 and b > 0) or (r < 0 and b < 0):
        return nextafter(q, inf)
    return q


def sqrt_lo(x):
    if x <= 0:
        return 0.0
    s = math.sqrt(x)
    return nextafter(s, -inf) if fma(-s, s, x) < 0 else s


def sqrt_hi(x):
    if x <= 0:
        return 0.0
    s = math.sqrt(x)
    return nextafter(s, inf) if fma(-s, s, x) > 0 else s


def arb_lo(b):
    """a float <= every point of the arb ball b"""
    l = b.lower()
    f = float(l)
    if arb(f) > l:
        f = nextafter(f, -inf)
    return f


def arb_hi(b):
    u = b.upper()
    f = float(u)
    if arb(f) < u:
        f = nextafter(f, inf)
    return f


class I:
    """The closed interval [lo, hi] (floats, lo <= hi)."""
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        self.lo = float(lo)
        self.hi = float(hi)

    # ---- construction -------------------------------------------------------------------------
    @staticmethod
    def of_arb(b):
        return I(arb_lo(b), arb_hi(b))

    @staticmethod
    def hull(*xs):
        return I(min(x.lo for x in xs), max(x.hi for x in xs))

    def __repr__(self):
        return 'I(%r, %r)' % (self.lo, self.hi)

    # ---- queries ------------------------------------------------------------------------------
    def width(self):
        return self.hi - self.lo

    def mid(self):
        m = 0.5 * (self.lo + self.hi)
        if not (self.lo <= m <= self.hi):
            m = self.lo
        return m

    def contains0(self):
        return self.lo <= 0.0 <= self.hi

    def pos(self):
        return self.lo > 0.0

    def neg_(self):
        return self.hi < 0.0

    def nonneg(self):
        return self.lo >= 0.0

    def nonpos(self):
        return self.hi <= 0.0

    def subset(self, other):
        return other.lo <= self.lo and self.hi <= other.hi

    def mag(self):
        return max(abs(self.lo), abs(self.hi))

    def mig(self):
        if self.lo > 0:
            return self.lo
        if self.hi < 0:
            return -self.hi
        return 0.0

    def isfinite(self):
        return isfinite(self.lo) and isfinite(self.hi)

    def intersect(self, other):
        lo = max(self.lo, other.lo)
        hi = min(self.hi, other.hi)
        if lo > hi:
            return None
        return I(lo, hi)

    def split(self):
        m = self.mid()
        return I(self.lo, m), I(m, self.hi)

    # ---- arithmetic ---------------------------------------------------------------------------
    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __add__(self, o):
        if not isinstance(o, I):
            if not isinstance(o, (int, float)):
                return NotImplemented
            o = float(o)
            return I(add_lo(self.lo, o), add_hi(self.hi, o))
        return I(add_lo(self.lo, o.lo), add_hi(self.hi, o.hi))

    __radd__ = __add__

    def __sub__(self, o):
        if not isinstance(o, I):
            if not isinstance(o, (int, float)):
                return NotImplemented
            o = float(o)
            return I(add_lo(self.lo, -o), add_hi(self.hi, -o))
        return I(add_lo(self.lo, -o.hi), add_hi(self.hi, -o.lo))

    def __rsub__(self, o):
        o = float(o)
        return I(add_lo(o, -self.hi), add_hi(o, -self.lo))

    def __mul__(self, o):
        a, b = self.lo, self.hi
        if not isinstance(o, I):
            if not isinstance(o, (int, float)):
                return NotImplemented
            c = float(o)
            if c >= 0:
                return I(mul_lo(a, c), mul_hi(b, c))
            return I(mul_lo(b, c), mul_hi(a, c))
        c, d = o.lo, o.hi
        if a >= 0:
            if c >= 0:
                return I(mul_lo(a, c), mul_hi(b, d))
            if d <= 0:
                return I(mul_lo(b, c), mul_hi(a, d))
            return I(mul_lo(b, c), mul_hi(b, d))
        if b <= 0:
            if c >= 0:
                return I(mul_lo(a, d), mul_hi(b, c))
            if d <= 0:
                return I(mul_lo(b, d), mul_hi(a, c))
            return I(mul_lo(a, d), mul_hi(a, c))
        if c >= 0:
            return I(mul_lo(a, d), mul_hi(b, d))
        if d <= 0:
            return I(mul_lo(b, c), mul_hi(a, c))
        return I(min(mul_lo(a, d), mul_lo(b, c)), max(mul_hi(a, c), mul_hi(b, d)))

    __rmul__ = __mul__

    def sqr(self):
        a, b = self.lo, self.hi
        if a >= 0:
            return I(mul_lo(a, a), mul_hi(b, b))
        if b <= 0:
            return I(mul_lo(b, b), mul_hi(a, a))
        return I(0.0, max(mul_hi(a, a), mul_hi(b, b)))

    def recip(self):
        a, b = self.lo, self.hi
        if a > 0 or b < 0:
            return I(div_lo(1.0, b), div_hi(1.0, a))
        raise ZeroDivisionError('interval contains 0: %r' % (self,))

    def __truediv__(self, o):
        if not isinstance(o, I):
            if not isinstance(o, (int, float)):
                return NotImplemented
            c = float(o)
            if c > 0:
                return I(div_lo(self.lo, c), div_hi(self.hi, c))
            if c < 0:
                return I(div_lo(self.hi, c), div_hi(self.lo, c))
            raise ZeroDivisionError
        c, d = o.lo, o.hi
        if not (c > 0 or d < 0):
            raise ZeroDivisionError('interval contains 0: %r' % (o,))
        a, b = self.lo, self.hi
        # endpoints of a/c, a/d, b/c, b/d
        if c > 0:
            lo = div_lo(a, d) if a >= 0 else div_lo(a, c)
            hi = div_hi(b, c) if b >= 0 else div_hi(b, d)
        else:
            lo = div_lo(b, d) if b >= 0 else div_lo(b, c)
            hi = div_hi(a, c) if a >= 0 else div_hi(a, d)
        return I(lo, hi)

    def __rtruediv__(self, o):
        return I(o) / self

    def sqrt(self):
        if self.lo < 0:
            if self.hi < 0:
                raise ValueError('sqrt of a negative interval')
            return I(0.0, sqrt_hi(self.hi))
        return I(sqrt_lo(self.lo), sqrt_hi(self.hi))

    def __pow__(self, n):
        if n == 2:
            return self.sqr()
        if n == 3:
            return self.sqr() * self
        if n == 1:
            return self
        if n == 0:
            return I(1.0)
        raise NotImplementedError

    # ---- order (certain comparisons) ----------------------------------------------------------
    def lt(self, o):
        """certainly self < o"""
        return self.hi < (o.lo if isinstance(o, I) else o)

    def gt(self, o):
        return self.lo > (o.hi if isinstance(o, I) else o)

    def le(self, o):
        return self.hi <= (o.lo if isinstance(o, I) else o)

    def ge(self, o):
        return self.lo >= (o.hi if isinstance(o, I) else o)


def point(x):
    return I(x, x)


# ---- constants ----------------------------------------------------------------------------------
ctx.prec = 128
PI = I.of_arb(arb.pi())
SQRT3 = I.of_arb(arb(3).sqrt())
ctx.prec = 53
HALF_PI = PI * 0.5
TWO_PI = PI * 2.0


def const(s):
    """the interval enclosing the decimal (or rational) constant s, e.g. const('1.1')"""
    ctx.prec = 128
    b = arb(s)
    ctx.prec = 53
    return I.of_arb(b)


# ---- transcendental functions on intervals ------------------------------------------------------
def _arb_sin(x):
    return arb(x).sin()


def _arb_cos(x):
    return arb(x).cos()


def sin_cos(x):
    """(sin x, cos x) for an interval x of width < 1 (the boxes of the checks), by monotone pieces.

    The interval x is split at the multiples of pi/2 it contains (enclosed rigorously); on each
    piece sin and cos are monotone and are bounded by their values at the endpoints (Arb balls),
    and at a multiple of pi/2 inside x the extreme value +-1 or 0 is attained."""
    lo, hi = x.lo, x.hi
    if hi - lo > 1.5:
        return I(-1.0, 1.0), I(-1.0, 1.0)
    ctx.prec = 64
    sl, cl = arb(lo).sin_cos()
    sh, ch = arb(hi).sin_cos()
    ctx.prec = 53
    s_lo = min(arb_lo(sl), arb_lo(sh))
    s_hi = max(arb_hi(sl), arb_hi(sh))
    c_lo = min(arb_lo(cl), arb_lo(ch))
    c_hi = max(arb_hi(cl), arb_hi(ch))
    # Between consecutive critical points k pi/2 both functions are monotone, so the endpoint
    # values bound them; at a critical point that may lie in [lo, hi] (its enclosure meets it)
    # the function that is extremal there reaches +-1.
    k0 = math.floor(lo / HALF_PI.hi) - 1
    k1 = math.ceil(hi / HALF_PI.lo) + 1
    for k in range(k0, k1 + 1):
        if k == 0:
            cp_lo = cp_hi = 0.0
        else:
            c = HALF_PI * float(k)
            cp_lo, cp_hi = c.lo, c.hi
        if cp_hi < lo or cp_lo > hi:
            continue
        m = k % 4
        # at k pi/2: (sin, cos) = (0, 1), (1, 0), (0, -1), (-1, 0) for m = 0, 1, 2, 3
        if m == 0:
            c_hi = 1.0
        elif m == 1:
            s_hi = 1.0
        elif m == 2:
            c_lo = -1.0
        else:
            s_lo = -1.0
    return I(max(s_lo, -1.0), min(s_hi, 1.0)), I(max(c_lo, -1.0), min(c_hi, 1.0))


def atan(x):
    """arctan, monotone"""
    ctx.prec = 64
    a = arb(x.lo).atan()
    b = a if x.hi == x.lo else arb(x.hi).atan()
    ctx.prec = 53
    return I(arb_lo(a), arb_hi(b))


def asin(x):
    """arcsin on [-1, 1], monotone"""
    lo, hi = max(x.lo, -1.0), min(x.hi, 1.0)
    ctx.prec = 64
    a = arb(lo).asin()
    b = a if hi == lo else arb(hi).asin()
    ctx.prec = 53
    return I(arb_lo(a), arb_hi(b))


def sinc(x):
    """sin(x)/x for an interval x inside [0, 1] (1 at 0): between 1 - x^2/6 and 1 - x^2/6 + x^4/120
    (alternating series with decreasing terms)"""
    assert x.lo >= 0 and x.hi <= 1.0
    lo = (1.0 - I(x.hi).sqr() / 6.0).lo
    up = (1.0 - I(x.lo).sqr() / 6.0 + I(x.lo).sqr().sqr() / 120.0).hi
    return I(lo, min(up, 1.0))
