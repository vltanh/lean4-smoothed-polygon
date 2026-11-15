"""Generate the Lean interval chains for the Lipschitz bound on B (mirrors hand2.py).

No longer used by the Lean proof (see `dout_contraction_bounds.py`); kept as a reference.
Every endpoint is a rational with denominator 10^6, outward rounded; every step is one interval
lemma whose numeric side conditions are closed by `norm_num`."""
from fractions import Fraction as Fr
import math
D = 10**6
def rd(x): return Fr(math.floor(x*D), D)
def ru(x): return Fr(math.ceil(x*D), D)
def lf(x):
    x = Fr(x)
    if x.denominator == 1:
        return f"({x.numerator} : ℝ)" if x.numerator >= 0 else f"(-{-x.numerator} : ℝ)"
    if x.numerator < 0: return f"(-{-x.numerator} / {x.denominator} : ℝ)"
    return f"({x.numerator} / {x.denominator} : ℝ)"
class E:
    """term: Lean term (fully parenthesized when compound); lo, hi; h: hypothesis name."""
    def __init__(s, term, lo, hi, h, atom=False):
        s.term = term; s.lo = Fr(lo); s.hi = Fr(hi); s.h = h; s.atom = atom
    def p(s): return s.term if s.atom else f"({s.term})"
class Gen:
    def __init__(s): s.lines = []; s.n = 0
    def fresh(s): s.n += 1; return f"h{s.n}"
    def have(s, term, lo, hi, proof):
        h = s.fresh()
        parts = proof.split(" (by norm_num)")
        head = parts[0]; nn = len(parts) - 1
        lname, rest = head.split(" ", 1)
        line = f"  have {h} := {lname} (lo := {numeral_l(lo)}) (hi := {numeral_l(hi)}) {rest}"
        s.lines.append(line)
        for i in range(0, nn, 4):
            k = min(4, nn - i)
            s.lines.append("    " + " ".join(["(by norm_num)"]*k))
        return E(term, lo, hi, h)
    def var(s, name, lo, hi, h): return E(name, lo, hi, h, atom=True)
    def const(s, k):
        k = Fr(k); h = s.fresh()
        t = lf(k)[1:-6] if True else None
        # numerals as Lean writes them
        t = numeral(k)
        s.lines.append(f"  have {h} := iconst ({t} : ℝ)")
        return E(t, k, k, h, atom=(Fr(k).denominator == 1 and k >= 0))
    def add(s, a, b):
        lo = rd(a.lo + b.lo); hi = ru(a.hi + b.hi)
        return s.have(f"{a.p() if not a.term.startswith('-') else a.p()} + {b.p()}", lo, hi,
            f"iadd {a.h} {b.h} (by norm_num) (by norm_num)")
    def sub(s, a, b):
        lo = rd(a.lo - b.hi); hi = ru(a.hi - b.lo)
        return s.have(f"{a.p()} - {b.p()}", lo, hi, f"isub {a.h} {b.h} (by norm_num) (by norm_num)")
    def mul(s, a, b):
        ps = [a.lo*b.lo, a.lo*b.hi, a.hi*b.lo, a.hi*b.hi]; lo = rd(min(ps)); hi = ru(max(ps))
        return s.have(f"{a.p()} * {b.p()}", lo, hi,
            f"imul {a.h} {b.h} " + " ".join(["(by norm_num)"]*8))
    def div(s, a, b):
        assert b.lo > 0
        ps = [a.lo/b.lo, a.lo/b.hi, a.hi/b.lo, a.hi/b.hi]; lo = rd(min(ps)); hi = ru(max(ps))
        return s.have(f"{a.p()} / {b.p()}", lo, hi,
            f"idiv {a.h} {b.h} (by norm_num) " + " ".join(["(by norm_num)"]*8))
    def neg(s, a):
        return s.have(f"-{a.p()}", rd(-a.hi), ru(-a.lo), f"ineg {a.h} (by norm_num) (by norm_num)")
    def pw(s, a, n):
        assert a.lo >= 0
        return s.have(f"{a.p()} ^ {n}", rd(a.lo**n), ru(a.hi**n),
            f"ipow (n := {n}) {a.h} (by norm_num) (by norm_num) (by norm_num)")
def numeral_l(k):
    k = Fr(k)
    if k.denominator == 1: return f"{k.numerator}" if k >= 0 else f"-{-k.numerator}"
    if k < 0: return f"-{-k.numerator} / {k.denominator}"
    return f"{k.numerator} / {k.denominator}"
def numeral(k):
    k = Fr(k)
    if k.denominator == 1: return f"{k.numerator}" if k >= 0 else f"-{-k.numerator}"
    return f"{k.numerator} / {k.denominator}"

SQ3 = (Fr(1732, 1000), Fr(17321, 10000))
def lemma_header(name, vars_, hyps, concl_doc):
    return name, vars_, hyps
def run():
    out = []
    # ---------- base intervals on B (as proved by hand in Lean) ----------
    # r in [11/50, 3/10]; psi: sin in [25/313, 20/101], cos in [99/101, 312/313]
    # cos phi2 in [(80-39q)/178, (112-15q)/226], sin phi2 in [-(80q+39)/178, -(112q+15)/226]
    # cos phi1 in [(7140-5461q)/17978, (34569-7480q)/70738], sin phi1 in [-1, -(34569q+7480)/70738]
    qlo, qhi = SQ3
    base = dict(
        r=(Fr(11,50), Fr(3,10)),
        sps=(Fr(25,313), Fr(20,101)), cps=(Fr(99,101), Fr(312,313)),
        cph2=(rd((80-39*qhi)/178), ru((112-15*qlo)/226)),
        sph2=(rd(-(80*qhi+39)/178), ru(-(112*qlo+15)/226)),
        cph1=(rd((7140-5461*qhi)/17978), ru((34569-7480*qlo)/70738)),
        sph1=(Fr(-1), ru(-(34569*qlo+7480)/70738)))
    return base
if __name__ == '__main__':
    b = run()
    for k, v in b.items(): print(k, float(v[0]), float(v[1]))
