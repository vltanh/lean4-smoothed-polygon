"""Sign certificates for real cubics with interval coefficients, on intervals of time.

A cubic is a list ``c = [c0, c1, c2, c3]`` of intervals (``iv.I``): the coefficients over a box
of the parameters. ``neg_on(c, lo, hi)`` certifies ``P(t) < 0`` for every ``t`` in ``[lo, hi]``
(``lo > 0``) or in ``(0, hi]`` (``lo = 0``) and every choice of the coefficients in their intervals.
Near ``t = 0`` it uses the factorization ``P = c0 + t Q``: if ``c0 <= 0`` and ``Q < 0`` on
``(0, hi]`` then ``P < 0`` there (the coefficients that vanish at a face of the cell are handled
exactly, with no metric margin). Away from ``0`` it evaluates the centred form
``P(m) + P'([lo, hi]) ([lo, hi] - m)`` and bisects the time interval.
"""
from .iv import I

MAXD = 10


def horner(c, t):
    r = c[-1]
    for a in reversed(c[:-1]):
        r = r * t + a
    return r


def deriv(c):
    return [c[k] * float(k) for k in range(1, len(c))]


def neg(c):
    return [-a for a in c]


def _eval_on(c, T):
    """an enclosure of P on the interval T: the intersection of Horner's form and the centred
    form"""
    v = horner(c, T)
    if len(c) >= 2 and T.hi > T.lo:
        m = T.mid()
        cm = horner(c, I(m))
        d = horner(deriv(c), T)
        v2 = cm + d * (T - m)
        w = v.intersect(v2)
        if w is not None:
            v = w
    return v


def neg_on(c, lo, hi, depth=0):
    """P < 0 on [lo, hi] (lo > 0) or on (0, hi] (lo == 0), for all coefficients."""
    if hi < lo:
        return True
    if lo > 0:
        v = _eval_on(c, I(lo, hi))
        if v.hi < 0:
            return True
        if depth >= MAXD:
            return False
        m = 0.5 * (lo + hi)
        return neg_on(c, lo, m, depth + 1) and neg_on(c, m, hi, depth + 1)
    c0 = c[0]
    if c0.hi <= 0 and len(c) > 1:
        # P = c0 + t Q with c0 <= 0: P < 0 on (0, hi] if Q < 0 there
        if neg_on(c[1:], 0.0, hi, depth):
            return True
    if c0.hi < 0:
        v = _eval_on(c, I(0.0, hi))
        if v.hi < 0:
            return True
        if depth >= MAXD:
            return False
        m = 0.5 * hi
        return neg_on(c, 0.0, m, depth + 1) and neg_on(c, m, hi, depth + 1)
    return False


def pos_on(c, lo, hi):
    return neg_on(neg(c), lo, hi)


def neg_or_pos(c, d, lo, hi, depth=0):
    """for every t in (0, hi] (lo = 0) or [lo, hi]: c(t) < 0 or d(t) > 0, for all coefficients;
    used as: 'the third control is strictly beaten wherever the switch has not happened yet'."""
    if hi < lo:
        return True
    if lo > 0:
        T = I(lo, hi)
        if _eval_on(c, T).hi < 0 or _eval_on(d, T).lo > 0:
            return True
        if depth >= MAXD:
            return False
        m = 0.5 * (lo + hi)
        return neg_or_pos(c, d, lo, m, depth + 1) and neg_or_pos(c, d, m, hi, depth + 1)
    if neg_on(c, 0.0, hi):
        return True
    if depth >= MAXD:
        return False
    m = 0.5 * hi
    return neg_or_pos(c, d, 0.0, m, depth + 1) and neg_or_pos(c, d, m, hi, depth + 1)


# ---- non-rigorous float root of the first upcrossing (a guess for the brackets) ----------------
def float_first_upcrossing(c):
    """the least t > 0 at which the float cubic c changes sign from <= 0 to > 0 (None if none);
    used only to guess the time brackets, never as a certificate."""
    import numpy as np
    c = [float(x) for x in c]
    k = 0
    while k < 3 and c[k] == 0.0:
        k += 1
    p = c[k:]
    if len(p) <= 1:
        return None
    rts = np.roots(p[::-1])
    cand = sorted(r.real for r in rts if abs(r.imag) <= 1e-9 * (1 + abs(r)) and r.real > 0)
    dp = [p[i] * i for i in range(1, len(p))]
    for r in cand:
        d = sum(a * r ** i for i, a in enumerate(dp))
        if d > 0:
            return r
        if d == 0:
            continue
    return None
