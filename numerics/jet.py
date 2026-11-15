"""First-order jets over intervals: forward-mode automatic differentiation with rigorous enclosures.

A jet ``J(v, d)`` is an interval value ``v`` (``iv.I``) with the intervals ``d[k]`` of its partial
derivatives in ``n`` directions, all evaluated over a box: if the inputs range over a box, every
value and every partial derivative of the computed function on the box lies in the corresponding
interval (the chain rule applied in interval arithmetic). The checks use four directions,
``(r2, psi, theta2, t)``; the partial derivatives give the mean value forms of the image of a box
and the Jacobian bounds of the contraction (``DOutContracts``).
"""
from .iv import I, atan as iatan


class J:
    __slots__ = ('v', 'd')

    def __init__(self, v, d):
        self.v = v
        self.d = d

    @staticmethod
    def var(v, k, n):
        return J(v, [I(1.0) if i == k else I(0.0) for i in range(n)])

    @staticmethod
    def const(v, n):
        if not isinstance(v, I):
            v = I(v)
        return J(v, [I(0.0)] * n)

    def __repr__(self):
        return 'J(%r, %r)' % (self.v, self.d)

    def _lift(self, o):
        if isinstance(o, J):
            return o
        if not isinstance(o, I):
            o = I(o)
        return J(o, [I(0.0)] * len(self.d))

    def __add__(self, o):
        if isinstance(o, J):
            return J(self.v + o.v, [a + b for a, b in zip(self.d, o.d)])
        return J(self.v + o, self.d)

    __radd__ = __add__

    def __neg__(self):
        return J(-self.v, [-a for a in self.d])

    def __sub__(self, o):
        if isinstance(o, J):
            return J(self.v - o.v, [a - b for a, b in zip(self.d, o.d)])
        return J(self.v - o, self.d)

    def __rsub__(self, o):
        return J(o - self.v, [-a for a in self.d])

    def __mul__(self, o):
        if isinstance(o, J):
            return J(self.v * o.v, [a * o.v + self.v * b for a, b in zip(self.d, o.d)])
        return J(self.v * o, [a * o for a in self.d])

    __rmul__ = __mul__

    def sqr(self):
        tv = self.v * 2.0
        return J(self.v.sqr(), [a * tv for a in self.d])

    def recip(self):
        r = self.v.recip()
        r2 = -(r.sqr())
        return J(r, [a * r2 for a in self.d])

    def __truediv__(self, o):
        if isinstance(o, J):
            q = self.v / o.v
            ri = o.v.recip()
            return J(q, [(a - q * b) * ri for a, b in zip(self.d, o.d)])
        return J(self.v / o, [a / o for a in self.d])

    def __rtruediv__(self, o):
        return self._lift(o) / self

    def sqrt(self):
        s = self.v.sqrt()
        if not s.lo > 0:
            raise ZeroDivisionError('sqrt jet at 0')
        h = (s * 2.0).recip()
        return J(s, [a * h for a in self.d])

    def __pow__(self, n):
        if n == 2:
            return self.sqr()
        if n == 3:
            return self.sqr() * self
        raise NotImplementedError


def atan(x):
    if isinstance(x, J):
        v = iatan(x.v)
        h = (x.v.sqr() + 1.0).recip()
        return J(v, [a * h for a in x.d])
    return iatan(x)


def sqrt(x):
    return x.sqrt()


def val(x):
    return x.v if isinstance(x, J) else x
