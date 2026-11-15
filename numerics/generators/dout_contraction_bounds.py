"""Generate the interval chains `lip_*` of `SmoothedPolygons/Ch16/DOutContractionBounds.lean`.

The Lipschitz bound of `DOutContracts` (`lipschitzOnWith_gmap`, `DOutContraction.lean`) rests on
bounds of the partial derivatives of the map on the single box `B x [371/2000, 441/2000]`. This
script writes them out step by step: every step is one elementary interval lemma (`iadd`,
`isub`, `imul`, `idiv`, ...) with rational endpoints of denominator 10^6, rounded outward, whose
numeric side conditions Lean closes by `norm_num`. Lean trusts nothing here: it checks every step.

    cd numerics/generators && python3 dout_contraction_bounds.py

writes `gen_out.lean` (the lemmas `lip_coef` ... `lip_combor2`, pasted into
`DOutContractionBounds.lean` after its interval lemmas) and the endpoints in `gen_R.json`,
`gen_L.json`; it prints the row sums of the Lipschitz matrix.
"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from contraction_intervals import *
qlo, qhi = SQ3
SLO, SHI = Fr(1855, 10000), Fr(2205, 10000)
def icc(lo, hi): return f"Icc {lf(lo)} {lf(hi)}"
def hyp(h, name, lo, hi): return f"({h} : {name} ∈ {icc(lo, hi)})"
lean = []
def lemma(name, binders, hyps, concls, body_lines, doc):
    s = f"/-- {doc} -/\ntheorem {name} {{{' '.join(binders)} : ℝ}}\n"
    for hp in hyps: s += f"    {hp}\n"
    def wrap(line, ind="    ", cont="      "):
        words = line.replace(" := by", "\u00a0:=\u00a0by").split(" "); out = []; cur = ind
        for w in words:
            if len(cur) + len(w) + 1 > 99 and cur.strip():
                out.append(cur.rstrip()); cur = cont
            cur += w + " "
        out.append(cur.rstrip())
        return "\n".join(out).replace("\u00a0", " ")
    cs = list(concls); cs[-1] = cs[-1] + " := by"
    s += "    :\n" + " ∧\n".join(wrap(c) for c in cs) + "\n"
    s += "\n".join(body_lines) + "\n"
    return s
def finish(g, results):
    """results: list of (concl_term_for_statement, E)."""
    concls = [f"{ct} ∈ {icc(e.lo, e.hi)}" for ct, e in results]
    g.lines.append("  exact ⟨" + ", ".join(e.h for _, e in results) + "⟩")
    return concls
R = {}  # name -> (lo, hi) of results, for later lemmas
def lemA():
    g = Gen()
    b = run()
    r = g.var("r", *b['r'], "hr"); c1 = g.var("cφ1", *b['cph1'], "hc1"); s1 = g.var("sφ1", *b['sph1'], "hs1")
    c2 = g.var("cφ2", *b['cph2'], "hc2"); s2 = g.var("sφ2", *b['sph2'], "hs2")
    sp = g.var("sψ", *b['sps'], "hsψ"); cp = g.var("cψ", *b['cps'], "hcψ")
    one = g.const(1); two = g.const(2)
    r1 = g.sub(one, r)
    x1 = g.mul(r1, c1); y1 = g.mul(r1, s1); x2 = g.mul(r, c2); y2 = g.mul(r, s2)
    rr = g.mul(r1, r); k = g.mul(rr, sp)
    dk0 = g.mul(g.sub(one, g.mul(two, r)), sp); dk1 = g.mul(rr, cp)
    res = [("(1 - r) * cφ1", x1), ("(1 - r) * sφ1", y1), ("r * cφ2", x2), ("r * sφ2", y2),
           ("(1 - r) * r * sψ", k), ("(1 - 2 * r) * sψ", dk0), ("(1 - r) * r * cψ", dk1)]
    for nm, e in zip(['x1', 'y1', 'x2', 'y2', 'k', 'dk0', 'dk1'], [x1, y1, x2, y2, k, dk0, dk1]):
        R[nm] = (e.lo, e.hi)
    for nm in ['cph1', 'sph1', 'cph2', 'sph2', 'sps', 'cps']: R[nm] = b[nm]
    concls = finish(g, res)
    hyps = [hyp("hr", "r", *b['r']), hyp("hc1", "cφ1", *b['cph1']), hyp("hs1", "sφ1", *b['sph1']),
            hyp("hc2", "cφ2", *b['cph2']), hyp("hs2", "sφ2", *b['sph2']), hyp("hsψ", "sψ", *b['sps']),
            hyp("hcψ", "cψ", *b['cps'])]
    return lemma("lip_coef", ["r", "cφ1", "sφ1", "cφ2", "sφ2", "sψ", "cψ"], hyps, concls, g.lines,
                 "The coefficients on `B` (generated interval chain).")
def uv(g, x1, x2, y2, k, t, q):
    one3 = g.const(Fr(1, 3)); one12 = g.const(Fr(1, 12)); two = g.const(2)
    t2 = g.pw(t, 2); t3 = g.pw(t, 3)
    u0 = g.sub(g.mul(x1, t), g.div(q, g.const(2)))
    v0 = g.add(g.sub(one3, g.mul(g.mul(two, y2), t2)), g.mul(g.mul(g.mul(two, q), k), t3))
    u1 = g.sub(g.add(g.mul(x1, t), g.mul(x2, t2)), g.div(q, g.const(4)))
    v1 = g.add(g.sub(one12, g.mul(y2, t2)), g.mul(g.mul(g.mul(two, q), k), t3))
    return u0, v0, u1, v1
def lemB():
    g = Gen()
    x1 = g.var("x1", *R['x1'], "hx1"); x2 = g.var("x2", *R['x2'], "hx2"); y2 = g.var("y2", *R['y2'], "hy2")
    k = g.var("k", *R['k'], "hk"); t = g.var("t", SLO, SHI, "ht"); q = g.var("√3", qlo, qhi, "hq")
    u0, v0, u1, v1 = uv(g, x1, x2, y2, k, t, q)
    for nm, e in zip(['u0', 'v0', 'u1', 'v1'], [u0, v0, u1, v1]): R[nm] = (e.lo, e.hi)
    concls = finish(g, [("nu0 x1 t", u0), ("nv0 y2 k t", v0), ("nu1 x1 x2 t", u1), ("nv1 y2 k t", v1)])
    hyps = [hyp("hx1", "x1", *R['x1']), hyp("hx2", "x2", *R['x2']), hyp("hy2", "y2", *R['y2']),
            hyp("hk", "k", *R['k']), hyp("ht", "t", SLO, SHI), hyp("hq", "√3", qlo, qhi)]
    return lemma("lip_uv", ["x1", "x2", "y2", "k", "t"], hyps, concls, g.lines,
                 "The normalized image on `B × [σlo, σhi]` (generated interval chain).")
def derivs(g, u0, v0, u1, v1, du0, dv0, du1, dv1):
    two = g.const(2)
    n1 = g.add(g.pw2(u0), g.pw2(v0)) if False else None
    u0s = sqs(g, u0); v0s = sqs(g, v0); u1s = sqs(g, u1); v1s = sqs(g, v1)
    n1 = g.add(u0s, v0s); n2 = g.add(u1s, v1s)
    a2 = g.div(g.sub(g.mul(u1, dv1), g.mul(v1, du1)), n2)
    a1 = g.div(g.sub(g.mul(u0, dv0), g.mul(v0, du0)), n1)
    dn2 = g.mul(two, g.add(g.mul(u1, du1), g.mul(v1, dv1)))
    dn1 = g.mul(two, g.add(g.mul(u0, du0), g.mul(v0, dv0)))
    gm = g.div(g.sub(g.mul(dn2, n1), g.mul(g.mul(two, n2), dn1)), g.pw(n1, 3))
    return a2, a1, gm
def sqs(g, a):
    if a.lo >= 0:
        return g.have(f"{a.p()} ^ 2", rd(a.lo**2), ru(a.hi**2), f"ipow (n := 2) {a.h} (by norm_num) (by norm_num) (by norm_num)")
    assert a.hi <= 0
    return g.have(f"{a.p()} ^ 2", rd(a.hi**2), ru(a.lo**2), f"isq_nonpos {a.h} (by norm_num) (by norm_num) (by norm_num)")
def lemC(j):
    g = Gen()
    u0 = g.var("u0", *R['u0'], "hu0"); v0 = g.var("v0", *R['v0'], "hv0")
    u1 = g.var("u1", *R['u1'], "hu1"); v1 = g.var("v1", *R['v1'], "hv1")
    t = g.var("t", SLO, SHI, "ht"); q = g.var("√3", qlo, qhi, "hq")
    neg = lambda nm: (rd(-R[nm][1]), ru(-R[nm][0]))
    zero = (Fr(0), Fr(0))
    din = {0: dict(dx1=neg('cph1'), dy1=neg('sph1'), dx2=R['cph2'], dy2=R['sph2'], dk=R['dk0']),
           1: dict(dx1=R['y1'], dy1=neg('x1'), dx2=zero, dy2=zero, dk=R['dk1']),
           2: dict(dx1=neg('y1'), dy1=R['x1'], dx2=neg('y2'), dy2=R['x2'], dk=zero)}[j]
    dx1 = g.var("dx1", *din['dx1'], "hdx1"); dy1 = g.var("dy1", *din['dy1'], "hdy1")
    dx2 = g.var("dx2", *din['dx2'], "hdx2"); dy2 = g.var("dy2", *din['dy2'], "hdy2")
    dk = g.var("dk", *din['dk'], "hdk")
    two = g.const(2)
    t2 = g.pw(t, 2); t3 = g.pw(t, 3)
    du0 = g.mul(dx1, t)
    tqdk = g.mul(g.mul(g.mul(two, q), dk), t3)
    dv0 = g.sub(tqdk, g.mul(g.mul(two, dy2), t2))
    du1 = g.add(g.mul(dx1, t), g.mul(dx2, t2))
    dv1 = g.sub(tqdk, g.mul(dy2, t2))
    dF = g.sub(g.sub(g.mul(g.mul(q, dk), t3), g.div(g.mul(dy1, t), two)), g.mul(dy2, t2))
    a2, a1, gm = derivs(g, u0, v0, u1, v1, du0, dv0, du1, dv1)
    R[f'a2_{j}'] = (a2.lo, a2.hi); R[f'a1_{j}'] = (a1.lo, a1.hi); R[f'gm_{j}'] = (gm.lo, gm.hi)
    R[f'F_{j}'] = (dF.lo, dF.hi)
    du0t, dv0t, du1t, dv1t = (f"dx1 * t", f"2 * √3 * dk * t ^ 3 - 2 * dy2 * t ^ 2",
                              f"dx1 * t + dx2 * t ^ 2", f"2 * √3 * dk * t ^ 3 - dy2 * t ^ 2")
    concls = finish(g, [(f"angD u1 v1 ({du1t}) ({dv1t})", a2), (f"angD u0 v0 ({du0t}) ({dv0t})", a1),
        (f"radD u0 v0 u1 v1 ({du0t}) ({dv0t}) ({du1t}) ({dv1t})", gm),
        ("√3 * dk * t ^ 3 - dy1 * t / 2 - dy2 * t ^ 2", dF)])
    hyps = [hyp("hu0", "u0", *R['u0']), hyp("hv0", "v0", *R['v0']), hyp("hu1", "u1", *R['u1']),
            hyp("hv1", "v1", *R['v1']), hyp("ht", "t", SLO, SHI), hyp("hq", "√3", qlo, qhi),
            hyp("hdx1", "dx1", *din['dx1']), hyp("hdy1", "dy1", *din['dy1']),
            hyp("hdx2", "dx2", *din['dx2']), hyp("hdy2", "dy2", *din['dy2']), hyp("hdk", "dk", *din['dk'])]
    body = ["  unfold angD radD"] + g.lines
    return lemma(f"lip_dir{j}", ["u0", "v0", "u1", "v1", "t", "dx1", "dy1", "dx2", "dy2", "dk"], hyps,
                 concls, body, f"The derivatives in the direction `{j}` (generated interval chain).")
def lemCs():
    g = Gen()
    u0 = g.var("u0", *R['u0'], "hu0"); v0 = g.var("v0", *R['v0'], "hv0")
    u1 = g.var("u1", *R['u1'], "hu1"); v1 = g.var("v1", *R['v1'], "hv1")
    t = g.var("t", SLO, SHI, "ht"); q = g.var("√3", qlo, qhi, "hq")
    x1 = g.var("x1", *R['x1'], "hx1"); y1 = g.var("y1", *R['y1'], "hy1")
    x2 = g.var("x2", *R['x2'], "hx2"); y2 = g.var("y2", *R['y2'], "hy2"); k = g.var("k", *R['k'], "hk")
    two = g.const(2); t2 = g.pw(t, 2)
    sqk = g.mul(g.mul(g.mul(g.const(6), q), k), t2)
    du0 = x1
    dv0 = g.sub(sqk, g.mul(g.mul(g.const(4), y2), t))
    du1 = g.add(x1, g.mul(g.mul(two, x2), t))
    dv1 = g.sub(sqk, g.mul(g.mul(two, y2), t))
    dF = g.sub(g.sub(g.mul(g.mul(g.mul(g.const(3), q), k), t2), g.div(y1, two)), g.mul(g.mul(two, y2), t))
    a2, a1, gm = derivs(g, u0, v0, u1, v1, du0, dv0, du1, dv1)
    R['a2_s'] = (a2.lo, a2.hi); R['a1_s'] = (a1.lo, a1.hi); R['gm_s'] = (gm.lo, gm.hi); R['F_s'] = (dF.lo, dF.hi)
    du0t, dv0t, du1t, dv1t = ("x1", "6 * √3 * k * t ^ 2 - 4 * y2 * t", "x1 + 2 * x2 * t",
                              "6 * √3 * k * t ^ 2 - 2 * y2 * t")
    concls = finish(g, [(f"angD u1 v1 ({du1t}) ({dv1t})", a2), (f"angD u0 v0 {du0t} ({dv0t})", a1),
        (f"radD u0 v0 u1 v1 {du0t} ({dv0t}) ({du1t}) ({dv1t})", gm),
        ("3 * √3 * k * t ^ 2 - y1 / 2 - 2 * y2 * t", dF)])
    hyps = [hyp("hu0", "u0", *R['u0']), hyp("hv0", "v0", *R['v0']), hyp("hu1", "u1", *R['u1']),
            hyp("hv1", "v1", *R['v1']), hyp("ht", "t", SLO, SHI), hyp("hq", "√3", qlo, qhi),
            hyp("hx1", "x1", *R['x1']), hyp("hy1", "y1", *R['y1']), hyp("hx2", "x2", *R['x2']),
            hyp("hy2", "y2", *R['y2']), hyp("hk", "k", *R['k'])]
    body = ["  unfold angD radD"] + g.lines
    return lemma("lip_dirσ", ["u0", "v0", "u1", "v1", "t", "x1", "y1", "x2", "y2", "k"], hyps, concls, body,
                 "The derivatives in the time variable `σ` (generated interval chain).")
def combo(Q, Et, P, Pt):
    ps = [Q[0], Q[1]]
    e = Et; a = P; b = Pt
    ea = [x*y for x in e for y in a]; ea = (min(ea), max(ea))
    eab = [x/y for x in ea for y in b]; eab = (min(eab), max(eab))
    lo = Q[0] - eab[1]; hi = Q[1] - eab[0]
    return max(abs(lo), abs(hi))
if __name__ == '__main__':
    A = lemA(); B = lemB(); Cs = [lemC(j) for j in range(3)]; Csig = lemCs()
    print('F_s', [float(x) for x in R['F_s']], 'u0', [float(x) for x in R['u0']])
    rows = {}
    for nm in ['a2', 'a1', 'gm']:
        Ls = []
        for j in range(3):
            if nm == 'a1':  # G1 = a2 - a1
                Q = (R[f'a2_{j}'][0] - R[f'a1_{j}'][1], R[f'a2_{j}'][1] - R[f'a1_{j}'][0])
                Qt = (R['a2_s'][0] - R['a1_s'][1], R['a2_s'][1] - R['a1_s'][0])
            else:
                Q = R[f'{nm}_{j}']; Qt = R[f'{nm}_s']
            Ls.append(combo(Q, Qt, R[f'F_{j}'], R['F_s']))
        rows[nm] = Ls
        print(nm, [round(float(x), 4) for x in Ls], round(float(sum(Ls)), 4))
    print('r-row', round(float(sum(rows['gm']))/1.7779, 4))
    open('gen_out.lean', 'w').write("\n".join([A, B] + Cs + [Csig]))

def lemBracket():
    g = Gen()
    y1 = g.var("y1", *R['y1'], "hy1"); y2 = g.var("y2", *R['y2'], "hy2"); k = g.var("k", *R['k'], "hk")
    q = g.var("√3", qlo, qhi, "hq")
    outs = []
    for tv in (SLO, SHI):
        t = g.const(tv); two = g.const(2)
        F = g.sub(g.sub(g.sub(g.mul(g.mul(q, k), g.pw(t, 3)), g.div(g.mul(y1, t), two)),
                        g.mul(y2, g.pw(t, 2))), g.const(Fr(1, 12)))
        outs.append(F)
    assert outs[0].hi < 0 and outs[1].lo > 0, (float(outs[0].hi), float(outs[1].lo))
    g.lines.append(f"  exact ⟨{outs[0].h}.2.trans_lt (by norm_num), lt_of_lt_of_le (by norm_num) {outs[1].h}.1⟩")
    concls = [f"nF y1 y2 k ({numeral_l(SLO)}) < 0", f"0 < nF y1 y2 k ({numeral_l(SHI)})"]
    hyps = [hyp("hy1", "y1", *R['y1']), hyp("hy2", "y2", *R['y2']), hyp("hk", "k", *R['k']),
            hyp("hq", "√3", qlo, qhi)]
    body = ["  unfold nF"] + g.lines
    return lemma("lip_bracket", ["y1", "y2", "k"], hyps, concls, body,
                 "The bracket `[σlo, σhi]` of the root `σ = 1/τ` (generated interval chain).")
LS = {}
def lemCombo(name, Q, Qt, P, Pt):
    g = Gen()
    qv = g.var("q", *Q, "hq"); e = g.var("e", *Qt, "he"); a = g.var("α", *P, "hα"); b = g.var("β", *Pt, "hβ")
    ea = g.mul(e, a); eab = g.div(ea, b); dd = g.sub(qv, eab)
    L = ru(max(abs(dd.lo), abs(dd.hi)))
    LS[name] = L
    g.lines.append(f"  exact iabs {dd.h} (by norm_num) (by norm_num)")
    concl = [f"|q - e * α / β| ≤ {numeral_l(L)}"]
    hyps = [hyp("hq", "q", *Q), hyp("he", "e", *Qt), hyp("hα", "α", *P), hyp("hβ", "β", *Pt)]
    return lemma(name, ["q", "e", "α", "β"], hyps, concl, g.lines, "A combination `|q - e α/β|`.")
def lemSub(name, A_, B_):
    g = Gen()
    a = g.var("a", *A_, "ha"); b = g.var("b", *B_, "hb"); d = g.sub(a, b)
    g.lines.append(f"  exact {d.h}")
    return lemma(name, ["a", "b"], [hyp("ha", "a", *A_), hyp("hb", "b", *B_)],
                 [f"a - b ∈ {icc(d.lo, d.hi)}"], g.lines, "A difference of intervals."), (d.lo, d.hi)
if __name__ == '__main__':
    out = []
    out += [lemA(), lemB()] + [lemC(j) for j in range(3)] + [lemCs(), lemBracket()]
    Qpsi = {}
    for j in ['0', '1', '2', 's']:
        txt, iv = lemSub(f"lip_sub{j}", R[f'a2_{j}'], R[f'a1_{j}']); out.append(txt); Qpsi[j] = iv
    for j in range(3):
        out.append(lemCombo(f"lip_comboθ{j}", R[f'a2_{j}'], R['a2_s'], R[f'F_{j}'], R['F_s']))
        out.append(lemCombo(f"lip_comboψ{j}", Qpsi[str(j)], Qpsi['s'], R[f'F_{j}'], R['F_s']))
        out.append(lemCombo(f"lip_combor{j}", R[f'gm_{j}'], R['gm_s'], R[f'F_{j}'], R['F_s']))
    for row in 'θψr':
        tot = sum(LS[f"lip_combo{row}{j}"] for j in range(3))
        print(row, [float(LS[f"lip_combo{row}{j}"]) for j in range(3)], float(tot))
    open('gen_out.lean', 'w').write("\n".join(out))
    import json
    json.dump({k: [str(v[0]), str(v[1])] for k, v in R.items()}, open('gen_R.json', 'w'), indent=1)
    json.dump({k: str(v) for k, v in LS.items()}, open('gen_L.json', 'w'), indent=1)
    print({k: str(v) for k, v in LS.items()})
