"""Remark 15.3.1 (``SmoothedPolygons/Ch15/FixedPointCells.lean``): the fixed points in cell coordinates
(``remark15_3_1``) and the segment through ``q_in`` (``remark15_3_1_segment``), by the point evaluator
(Arb balls, 200 bits): every sign and every inequality below is decided rigorously.

Lean definitions used:
* ``rScale = sSup {r > 1 | P(r) = 0}``, ``P(r) = 1 - 5r - 7r^2 - 5r^3 - 7r^4 - 5r^5 + r^6``
  (``Ch13/RScale.lean``); the roots of ``P`` are isolated by FLINT (``fmpz_poly.complex_roots``);
* ``qOutCart = equilExact rScale`` (13.5.1, ``Ch13/FixedPoints.lean``), ``pOut = cellCoords qOutCart``,
  ``pIn = cellTau pOut`` (``Ch15/CellCoordinates.lean``);
* ``discrA ζ z``, ``discrB ζ z``: the discriminants of ``chi_A/t^{m_A}``, ``chi_B/t^{m_B}``
  (``Ch15/SmallerCells.lean``); on the open first cell ``m_A = 0``, ``m_B = 1``, with
  ``chi_A = -t^3/12 + (y1 - sqrt3 x1) t^2/4 + (y2 - sqrt3 x2) t/2 + (y3 - sqrt3 x3)/2`` (a cubic,
  ``Cubic.discr = b^2c^2 - 4ac^3 - 4b^3d - 27a^2d^2 + 18abcd``) and
  ``chi_B/t = t^2/12 + y1 t/2 + y2`` (a quadratic, ``discr = b^2 - 4ac``) (``chiA_chiB_eq``).
"""
from flint import arb, acb, fmpz_poly

from .. import fuller as fu


def r_scale():
    """rScale: the largest real root > 1 of P (FLINT's rigorous root isolation)"""
    P = fmpz_poly([1, -5, -7, -5, -7, -5, 1])
    real = [r for r, m in P.complex_roots() if r.imag.is_zero()]
    big = [r.real for r in real if r.real > 1]
    assert len(big) == 1, big
    return big[0]


def equil_exact(r):
    """equilExact r (13.5.1)"""
    s3 = arb(3).sqrt()
    I = acb(0, 1)
    z1 = -1 + I * ((-1 + r) / (s3 * (1 + r)))
    z2 = -((-1 + r ** 3) / (s3 * (1 + r ** 3))) + I * (
        (1 - 3 * r - 2 * r ** 2 - 3 * r ** 3 + r ** 4) / (3 * (1 + r + r ** 3 + r ** 4)))
    z3 = acb((-2 * (1 + r - 4 * r ** 3 - 7 * r ** 4 - 9 * r ** 5 - 7 * r ** 6 - 4 * r ** 7 + r ** 9
                    + r ** 10)) / (9 * (1 + r) ** 2 * (1 - r + r ** 2) * (1 + r ** 3 + r ** 6)), 0)
    return (z1, z2, z3)


def cell_coords_lean(z):
    """cellCoords z exactly as in Lean: a = |z1|, b = |z2|, s = (-a + sqrt(a^2 + 4b))/(2b),
    (s^2 b, toIcoMod 2pi 0 (arg z2 - arg z1), arg z2), with arg in (-pi, pi]"""
    PI = arb.pi()
    a, b = abs(z[0]), abs(z[1])
    s = (-a + (a * a + 4 * b).sqrt()) / (2 * b)
    d = z[1].arg() - z[0].arg()
    # toIcoMod 2pi 0 d: the representative in [0, 2pi)
    if d < 0:
        d = d + 2 * PI
    assert d >= 0 and d < 2 * PI
    return (s * s * b, d, z[1].arg())


def discr_A(z):
    x1, y1, x2, y2, x3, y3 = z[0].real, z[0].imag, z[1].real, z[1].imag, z[2].real, z[2].imag
    s3 = arb(3).sqrt()
    a = arb(-1) / 12
    b = (y1 - s3 * x1) / 4
    c = (y2 - s3 * x2) / 2
    d = (y3 - s3 * x3) / 2
    return b * b * c * c - 4 * a * c ** 3 - 4 * b ** 3 * d - 27 * a * a * d * d + 18 * a * b * c * d


def discr_B(z):
    """the quadratic chi_B/t (needs y3 = 0, y2 != 0: m_B = 1)"""
    y1, y2 = z[0].imag, z[1].imag
    return (y1 / 2) ** 2 - 4 * (arb(1) / 12) * y2


def run():
    fu.set_prec(200)
    PI = arb.pi()
    out = {}
    r = r_scale()
    q = equil_exact(r)
    p = cell_coords_lean(q)
    out['rScale'] = str(r)
    out['pOut'] = [str(x) for x in p]
    s3 = arb(3).sqrt()
    checks = {}
    checks['pOut in openBoxOne'] = bool(p[0] > 0 and p[0] < 1 and p[1] > 0 and p[1] < PI
                                        and p[2] > 0 and p[2] < PI)
    checks['|pOut0 - (2 - sqrt3)| < 1e-50 (Lean: equality)'] = bool(abs(p[0] - (2 - s3)) < arb(10) ** -50)
    checks['|pOut1 - 0.1705935| < 1e-7'] = bool(abs(p[1] - arb('0.1705935')) < arb('1e-7'))
    checks['|pOut2 - 2.91574| < 1e-7'] = bool(abs(p[2] - arb('2.91574')) < arb('1e-7'))
    pin = (p[0], PI - p[1], PI - p[2])
    out['pIn'] = [str(x) for x in pin]
    checks['pIn in openBoxOne'] = bool(pin[1] > 0 and pin[1] < PI and pin[2] > 0 and pin[2] < PI)
    # the fixed points (cellClass pOut = q_out; F(q_out) = q_out, Lemma 13.5.2)
    st = fu.step_coords(p)
    out['t_sw(q_out)'] = str(st.t)
    out['F(pOut) - pOut'] = [str(a - b) for a, b in zip(st.coords, p)]
    checks['F(pOut) contains pOut (fixed point, to the ball radius)'] = all(
        (a - b).contains(0) for a, b in zip(st.coords, p))
    st2 = fu.step_coords(pin)
    out['t_sw(q_in)'] = str(st2.t)
    checks['F(pIn) contains pIn'] = all((a - b).contains(0) for a, b in zip(st2.coords, pin))
    # the segment through q_in
    seg = lambda x: fu.cell_point(arb(x), pin[1], pin[2])
    zA, zB = seg('0.26775'), seg('0.26777')
    checks['0 < discrB(seg 0.26775)'] = bool(discr_B(zA) > 0)
    checks['discrB(seg 0.26777) < 0'] = bool(discr_B(zB) < 0)
    out['discrB(seg 0.26775), discrB(seg 0.26777)'] = [str(discr_B(zA)), str(discr_B(zB))]
    FA, FB = fu.Step(zA), fu.Step(zB)
    checks['firstControl(poincare(seg 0.26775)) = zeta^2'] = fu.image_first_control(FA) == 2
    checks['firstControl(poincare(seg 0.26777)) = 1'] = fu.image_first_control(FB) == 0
    z1, z2 = seg('0.26790'), seg('0.26791')
    checks['discrA(seg 0.26790) < 0'] = bool(discr_A(z1) < 0)
    checks['0 < discrA(seg 0.26791)'] = bool(discr_A(z2) > 0)
    out['discrA(seg 0.26790), discrA(seg 0.26791)'] = [str(discr_A(z1)), str(discr_A(z2))]
    S1, S2 = fu.Step(z1), fu.Step(z2)
    out['t_sw(seg 0.26790), t_sw(seg 0.26791)'] = [str(S1.t), str(S2.t)]
    checks['0.95 < firstSwitchTime(seg 0.26790)'] = bool(S1.t > arb('0.95'))
    checks['firstSwitchTime(seg 0.26791) < 0.86'] = bool(S2.t < arb('0.86'))
    checks['0.26791 < 2 - sqrt3'] = bool(arb('0.26791') < 2 - s3)
    # first controls along the segment cross-checked by the lexicographic rule
    def lexw(F):
        w = (F.w[0], F.w[1], acb(F.w[2].real, 0))
        return (F.m + fu.lex_first_control(w)) % 3
    checks['lex rule agrees'] = all(lexw(F) == fu.image_first_control(F) for F in (FA, FB))
    # the segment through the printed point (the book's "q_in", REPORT.md E75): no crossing
    segp = lambda x: fu.cell_point(arb(x), p[1], p[2])
    out['along the pOut segment, discrA, discrB at 0.2677..0.2681'] = [
        (x, str(discr_A(segp(x)).mid()), str(discr_B(segp(x)).mid()))
        for x in ('0.2677', '0.2679', '0.2681')]
    # the Jacobian of F at q_out in cell coordinates (Lemma 13.5.5): an interval enclosure on a box
    # of radius 1e-9 around pOut (through the implicit root), and its eigenvalues (Arb)
    from flint import acb_mat
    from ..iv import I
    from .. import boxmap as bm, regions as rg
    pf = [float(x.mid()) for x in p]
    h = 1e-9
    X = rg.coord_box(1, I(pf[0] - h, pf[0] + h), I(pf[1] - h, pf[1] + h), I(pf[2] - h, pf[2] + h))
    o = bm.step(X)[0]
    Jm = bm.jacobian(X, o, 1)
    M = acb_mat([[arb(0.5 * (x.lo + x.hi), 0.5 * (x.hi - x.lo)) for x in row] for row in Jm])
    out['DF(q_out) in cell coordinates'] = [[(x.lo, x.hi) for x in row] for row in Jm]
    out['eigenvalues of DF(q_out)'] = [str(e) for e in M.eig()]
    out['checks'] = checks
    out['all'] = all(checks.values())
    return out
