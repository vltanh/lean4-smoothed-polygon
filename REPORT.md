# Audit of the paper and the formalization

Paper: Thomas Hales and Koundinya Vajjha, *Packings of Smoothed Polygons*,
[arXiv:2405.04331v1](https://arxiv.org/abs/2405.04331) (7 May 2024, a 283-page book), audited
against the arXiv LaTeX source of that version, the only one. Chapter, section, result and
equation numbers are the book's; TeX line numbers refer to its source file `chapter2.tex`.

## Status

- **Proved:** Mahler's First conjecture (Theorem 16.3.1) with no hypothesis; the Challenge's three
  statements, Theorems 16.3.1 and 7.5.6 and the octagon's density `(8 - √32 - ln 2)/(√8 - 1)`.
- **Formalized:** every numbered result of Chapters 2–8, 13–16, Lemma 10.1.1, Corollary A.1.3 and
  A.3, A.6, A.11, except a few remarks and Proposition 15.3.2, proved in part (Section 9).
- **Not formalized,** by the user's scope decision: Chapter 1, Chapters 9–12 apart from Lemma
  10.1.1, the other appendices, and the remarks that no main result uses (Section 9).
- **Nothing assumed:** every cited result is proved (Section 2), and the four facts that the book
  reads off computations are proved without computer assistance (Section 7).
- **Build:** `lake build` succeeds; the only `sorry`s are the three statements of [`Challenge.lean`](Challenge.lean);
  no `axiom`, `admit`, `native_decide` or `decide +kernel`.
- **Axioms:** [`scripts/Audit.lean`](scripts/Audit.lean), with `import all`, finds only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and
  [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound) in all 10,734 declarations of the library and in the three Challenge theorems.
- **Routes:** the route check compares 140 results with the book's proofs: 185 differences, all
  recorded with reasons (Section 8). Comparator accepts the Solution under Lean's kernel and NanoDa.
- **Review:** independent agents reviewed the statements and the proofs; no person has reviewed the
  proofs. [CREDITS.md](CREDITS.md) says how this was made.

## 1. Summary

| Finding | E |
| --- | --- |
| Lemma 2.2.1 is false as printed (refuted in Lean); its classical form, all the book needs, holds. | [E1](docs/report/errors.md#e1) |
| The converse of Problem 3.6.2 that §6.1 uses is false; it holds for winding number one, so below cost `7π/2`. | [E15](docs/report/errors.md#e15) |
| Nontriviality on the full costate makes every admissible trajectory an extremal; it belongs on the reduced costate. | [E21](docs/report/errors.md#e21) |
| Theorem 7.7.1 is false read literally and Theorem 8.3.1 false as printed; corrected forms are proved. | [E32](docs/report/errors.md#e32), [E56](docs/report/errors.md#e56) |
| Theorem 3.1.4(3), Lemma 3.1.8 and the existence claim of Filippov's theorem each lack a hypothesis. | [E13](docs/report/errors.md#e13), [E34](docs/report/errors.md#e34), [E35](docs/report/errors.md#e35) |
| §6.1's existence argument fails as written, and minimizers are identified with `K_min` without proof; both are proved. | [E46](docs/report/errors.md#e46), [E47](docs/report/errors.md#e47) |
| The proof of Theorem 8.2.7 covers part of its statement; proved in the authors' reading, open for abnormal lifts. | [E55](docs/report/errors.md#e55) |
| Lemma 13.5.5, Lemmas 14.2.3–14.2.4, Table 16.1 and Figure 14.2 rest on uncertified Mathematica computations; each is replaced by a proof. | [E68](docs/report/errors.md#e68), [E84](docs/report/errors.md#e84), [E77](docs/report/errors.md#e77), [E88](docs/report/errors.md#e88) |
| §15.3 uses `F⁻¹ = τFτ` where it fails, and Remark 15.3.1 swaps `q_in` and `q_out`. | [E73](docs/report/errors.md#e73), [E75](docs/report/errors.md#e75) |
| Theorem 16.1.1 has gaps in its convergence step and its last row; the proof of Theorem 16.4.1 asserts the cells of §16.4.2 and turns a cluster point into a limit without proof. All are repaired. | [E78](docs/report/errors.md#e78), [E79](docs/report/errors.md#e79), [E90](docs/report/errors.md#e90), [E91](docs/report/errors.md#e91) |

## 2. Results from prior work and how the paper uses them

| Cited result (where the book uses it) | Proved in |
| --- | --- |
| Fejes Tóth's theorem `δ = δ_L` (Theorem 2.1.3) | [`External.fejes_toth`](External/FejesToth.lean#L882) |
| Gruber's lattice density formula (Definition 2.1.2) | [`External.gruber_corollary_30_1`](External/Gruber.lean#L320) |
| Minkowski and Mahler on critical lattices (Theorem 2.3.6) | [`External.minkowski_mahler`](External/MinkowskiMahler.lean#L964) |
| Mahler 1947, Theorems 1 and 2, the circumscribed hexagon (Theorem 2.3.7) | [`External.mahler_1947`](External/Mahler1947.lean#L1700) |
| Mahler 1947, Lemma 3, stated there without proof (the remark after Definition 2.3.5) | [`External.mahler_irreducible_iff`](External/MahlerIrreducible/Lemma3.lean#L367), along Mahler's paper A and Mahler 1946 |
| The Euler–Arnold equation (Proposition 6.5.1) | [`External.euler_arnold`](External/EulerArnold.lean#L72) |
| Filippov's theorem (Theorem 6.1.1; §6.1 needs a form with a state constraint) | [`External.filippov`](External/Filippov.lean#L153); the OptimalControl package |
| The Pontryagin maximum principle (§6.2, Proposition 8.1.3) | [`External.pontryagin_maximum_principle`](External/Pontryagin.lean#L80), from the OptimalControl package |
| Brouwer's fixed-point theorem (in the proof of the maximum principle) | the FixedPoint package |
| Gronwall's inequality (§6.1, Corollary A.1.3), the case of constant coefficients | the OptimalControl package |
| Irwin's stable manifold theorem (Theorem A.3.1; §14.3) | [`theoremA_3_1`](SmoothedPolygons/AppA/StableManifold.lean#L186), from the StableManifold package |
| Shifrin's Proposition 3.8 (Lemma 2.4.6) | not used: the book applies it outside its hypotheses ([E11](docs/report/errors.md#e11)) |

- The cited results are proved by their sources' arguments, with the departures of Section 7,
  except Filippov's theorem and the stable manifold theorem, which are proved by standard arguments.
- The book applies Filippov's theorem to a problem that it does not cover ([E46](docs/report/errors.md#e46)), and the maximum
  principle with a nontriviality condition that every trajectory meets ([E21](docs/report/errors.md#e21)).
- The standard facts that the book uses without citation are proved, in Mathlib, or not needed.
- Details: [docs/report/cited-results.md](docs/report/cited-results.md). The general mathematics
  that the formalization built ([`Basic/`](Basic), the three packages, what Mathlib lacks) is in
  [docs/report/libraries.md](docs/report/libraries.md).

## 3. Errors and gaps in the paper

94 findings, indexed here by chapter; each number links to its entry in
[docs/report/errors.md](docs/report/errors.md), which says how the formalization repairs it.

### Chapters 2–4

| E | Where (book §, TeX lines) | Finding, one line |
| --- | --- | --- |
| [E1](docs/report/errors.md#e1) | Lemma 2.2.1, §2.2 (1317–1351) | False: a lattice packing need not come from a tiling hexagon containing the disk; refuted in Lean. |
| [E2](docs/report/errors.md#e2) | Theorem 2.2.2, §2.2 (1382–1392) | Takes a lattice attaining `δ_L(K)` without showing that one exists. |
| [E3](docs/report/errors.md#e3) | Remark 2.2.4, §2.2 (~1435) | The hyperbolic arc near each edge midpoint is observed, not proved. |
| [E4](docs/report/errors.md#e4) | Lemma 2.2.5, §2.2 (1507–1543) | Existence needs more than Blaschke selection; the shaving argument cannot close one case. |
| [E5](docs/report/errors.md#e5) | Lemmas 2.2.6–2.2.7, §2.2 (1545–1720) | A midpoint case untreated; the closedness of the set of critical hexagons asserted. |
| [E6](docs/report/errors.md#e6) | Definition 2.3.4, §2.3 (1766–1770) | A critical lattice must be admissible; without it Theorem 2.3.6 is false. |
| [E7](docs/report/errors.md#e7) | Theorem 2.3.9, §2.3 (1888–1916) | The existence of a critical lattice is tacit; an equation is written before it is known. |
| [E8](docs/report/errors.md#e8) | Lemma 2.4.2, §2.4 (2034–2085) | A sign slip; the integral curve is not shown to stay on the boundary. |
| [E9](docs/report/errors.md#e9) | Lemma 2.4.3, §2.4 (2093–2148) | A proof sketch whose details are in handwritten notes. |
| [E10](docs/report/errors.md#e10) | Lemma 2.4.5, §2.4 (2165–2202) | Index slip: `j+2` for `j+1`. |
| [E11](docs/report/errors.md#e11) | Lemma 2.4.6, §2.4 (2214–2235) | Shifrin's proposition applied to curves that are only `C¹` with Lipschitz derivative. |
| [E12](docs/report/errors.md#e12) | Problem 2.4.8 (2289–2292, 6348) | That a balanced disk has least circumscribed hexagon of area `√12` is used, never proved. |
| [E13](docs/report/errors.md#e13) | Theorem 3.1.4(3), §3.1 (2414–2442) | False for a general convex disk; holds with Lipschitz tangents, as the book uses it. |
| [E14](docs/report/errors.md#e14) | Proof of Theorem 3.4.2, §3.4 (3055) | Index slip: `κ₀ + κ₁ + κ₂`. |
| [E15](docs/report/errors.md#e15) | Problem 3.6.2, §3.6 (~3205); §6.1 (4579) | The converse that §6.1 uses is false (the unit circle run seven times); true for winding number one. |
| [E16](docs/report/errors.md#e16) | Problem 3.6.2, §3.6 (3235) | Misprinted terminal condition: `X(t_f) = R⁻¹X₀R`. |
| [E34](docs/report/errors.md#e34) | Lemma 3.1.8, §3.1 (2554–2579) | False unless the curves are regular; two gaps. |
| [E39](docs/report/errors.md#e39) | §3.5 (3140–3156) | A reparameterization taken for granted. |
| [E17](docs/report/errors.md#e17) | Lemma 4.2.3, §4.2 (3382) | Needs `X ≠ 0`. |
| [E18](docs/report/errors.md#e18) | Lemma 4.2.3, §4.2 (3394–3420) | That every tangent vector of the orbit is a `[Y, X]` is used without proof. |
| [E19](docs/report/errors.md#e19) | Lemma 4.3.1, §4.3 (3514–3530) | "Area less than `π`" is not justified: the unit disk is admissible. |
| [E20](docs/report/errors.md#e20) | Problem 4.5.1, §4.5 (3631) | Sign misprint in `a(u)`; with it Lemma 4.5.2 fails. |
| [E40](docs/report/errors.md#e40) | §4.6 (3797–3808) | The printed fundamental domain is two sectors; two circle centres misprinted. |

### Chapters 5 and 6

| E | Where (book §, TeX lines) | Finding, one line |
| --- | --- | --- |
| [E41](docs/report/errors.md#e41) | Definition 5.0.1 (3900–3978) | The compactness and dihedral invariance of `𝔥**` and the image of a horoball are asserted. |
| [E42](docs/report/errors.md#e42) | Lemma 5.0.3 (4000–4015) | The hexagon is not shown to be the critical hexagon. |
| [E43](docs/report/errors.md#e43) | Theorem 5.0.6 (4203–4317) | The claim of Case 1 is not argued; Case 2 is only sketched. |
| [E44](docs/report/errors.md#e44) | Lemma 5.0.7 (4432–4465) | Gaps in (3) and (4), and a misprinted region. |
| [E45](docs/report/errors.md#e45) | Proof of Theorem 5.0.2 (4469–4513) | A curve printed as the domain, a false remark, a tacit re-centering, a bound read off a graph. |
| [E21](docs/report/errors.md#e21) | §6.2, Problem 6.7.1 (4764–4766, 4818–4820, 5248–5250) | Nontriviality on the full costate makes every admissible trajectory an extremal. |
| [E22](docs/report/errors.md#e22) | Proof of Proposition 6.5.1, §6.5 (5030–5040) | The sign convention for `ad*` contradicts the book's definition; the equation used is right. |
| [E23](docs/report/errors.md#e23) | Theorem 6.8.3, §6.8 (5385–5402) | Proof omitted ("the long direct calculation"). |
| [E35](docs/report/errors.md#e35) | Theorem 6.1.1, §6.1 (4538–4546) | Filippov's existence claim fails for costs that depend on the control; no source given. |
| [E38](docs/report/errors.md#e38) | Remark 6.6.1, §6.6 (5216–5242) | The periodic extension of extremals is stated without proof. |
| [E46](docs/report/errors.md#e46) | §6.1 (4520–4602) | The existence of a minimizer: four steps fail as written. |
| [E47](docs/report/errors.md#e47) | §6.1 (4571–4572), Proposition 8.1.3 (6786), Theorem 16.3.1 (12789–12795) | The minimizers of the control problem are identified with `K_min` without proof. |

### Chapters 7 and 8

| E | Where (book §, TeX lines) | Finding, one line |
| --- | --- | --- |
| [E24](docs/report/errors.md#e24) | Before Lemma 7.2.1, §7.1 (5550–5563) | "Eigenvectors" for eigenvalues; one eigenvector needs a negative rescaling. |
| [E25](docs/report/errors.md#e25) | Lemma 7.2.1, §7.2 (5747–5756) | The proof is the preceding discussion. |
| [E26](docs/report/errors.md#e26) | Lemma 7.3.1, §7.3 (5771–5792) | Needs `⟨X, Z_u⟩ ≠ 0` on `U`. |
| [E27](docs/report/errors.md#e27) | Theorem 7.5.1, Lemma 7.5.3, §7.5 (6099, 6206–6214) | Notation: `χ₂₃(0) = 0` and `χ₃₂(0) = 0`, which are equivalent. |
| [E28](docs/report/errors.md#e28) | Lemma 7.5.3, §7.5 (6230–6275) | The discarded "obviously positive" factor depends on `t`. |
| [E29](docs/report/errors.md#e29) | Lemma 7.5.3, §7.5 (6265–6273) | `∂²f/∂y² ≥ 0` is left as an exercise; it is true and tight at a corner. |
| [E30](docs/report/errors.md#e30) | Lemma 7.5.5, §7.5 (6287–6334) | The proof argues the other direction, and a uniqueness step is tacit. |
| [E31](docs/report/errors.md#e31) | Theorem 7.5.6, §7.5 (6359–6372) | Only the transversality conditions are checked. |
| [E32](docs/report/errors.md#e32) | Theorem 7.7.1, §7.7 (6543–6623) | False read literally (time translation, several laps); the proof is a sketch. |
| [E36](docs/report/errors.md#e36) | Remark 7.5.2, §7.5 (6185–6203) | Stated without proof. |
| [E37](docs/report/errors.md#e37) | Remarks 7.6.2 and 7.6.4, §7.6 (6402–6438) | A closing condition not stated; a limit read off a figure. |
| [E48](docs/report/errors.md#e48) | Proposition 8.1.3, §8.1 (6785–6798) | The principle of optimality is invoked without a construction. |
| [E49](docs/report/errors.md#e49) | Theorem 8.1.4, §8.1 (6807–6894) | "Optimal" in the statement; three steps of the proof. |
| [E50](docs/report/errors.md#e50) | Lemma 8.1.5, §8.1 (6908–7015) | A wrong constant: `C = -2x₀/y₀`. |
| [E51](docs/report/errors.md#e51) | Remark 8.1.6, §8.1 (7035–7070) | Wrong signs: as printed, the edge minimizes the Hamiltonian. |
| [E52](docs/report/errors.md#e52) | Lemma 8.2.1, §8.2 (7095–7126) | A quantifier too broad (`⟨X, Z_u⟩ ≠ 0` is needed), and a step left implicit. |
| [E53](docs/report/errors.md#e53) | Lemma 8.2.2, Theorem 8.2.3, §8.2 (7128–7216) | `H = 0` used at one time, though given almost everywhere; a closed interval for an open one. |
| [E54](docs/report/errors.md#e54) | Theorem 8.2.6, §8.2 (7259–7298) | A converse argued by necessary conditions; two typos. |
| [E55](docs/report/errors.md#e55) | Theorem 8.2.7, §8.2 (7300–7391) | The proof covers one kind of singular subarc; slips in the second variation. |
| [E56](docs/report/errors.md#e56) | Theorem 8.3.1, §8.3 (7448–7586) | False as printed; one claim sketched. |
| [E57](docs/report/errors.md#e57) | Theorem 8.3.2, §8.3 (7590–7605); Chapter 1 (851–856) | No interval in the statement; Chapter 1's restatement drops edge extremality and is false. |
| [E58](docs/report/errors.md#e58) | Remark 8.3.3, §8.3 (7610–7616) | The balanced disk need not exist; no proof. |
| [E59](docs/report/errors.md#e59) | Lemma 8.3.4, §8.3 (7619–7670) | A sign and a garbled display; the conclusion stands. |

### Chapters 13 and 14

| E | Where (book §, TeX lines) | Finding, one line |
| --- | --- | --- |
| [E62](docs/report/errors.md#e62) | §13.2, Lemma 13.2.6 (10740–10753, 10972–11009) | The first control is argued only as a necessary condition; the constancy of the Hamiltonian is asserted. |
| [E63](docs/report/errors.md#e63) | Lemmas 13.2.1–13.2.3, 13.2.5; §13.5 (10794–10906, 11246–11260) | Symmetries applied outside their hypothesis `H_F = 0`. |
| [E64](docs/report/errors.md#e64) | Corollary 13.2.7, Lemma 13.2.8, §13.2 (11011–11067) | A strict inequality that can be an equality; hypotheses not needed. |
| [E65](docs/report/errors.md#e65) | Lemma 13.3.2, §13.3 (11108–11156) | The proof assumes the maximizing face constant in time; two typos. |
| [E66](docs/report/errors.md#e66) | §13.4 (11161–11177) | The "diffeomorphism" of the blow-up is only `C²` along `z₂ = 0`. |
| [E67](docs/report/errors.md#e67) | §13.5, Lemma 13.5.2 (11236–11251, 11298–11387) | Silent steps, a garbled display, and fixed points not verified. |
| [E68](docs/report/errors.md#e68) | Lemma 13.5.5, §13.5 (11433–11453) | Proved by a Mathematica computation; two steps not argued. |
| [E69](docs/report/errors.md#e69) | Remark 13.5.4, §13.5 (11402–11428) | An interpretation stated without proof. |
| [E81](docs/report/errors.md#e81) | §14.1 (11561–11602) | `X̃` printed for `X`; the full rank of (14.1.3) and the orders of `Λ_R` asserted. |
| [E82](docs/report/errors.md#e82) | §14.2 (11612–11701) | `ξ(x̃) ∈ Ξ_{𝒲,0}` holds on one side of a hyperplane only; a commented-out citation. |
| [E83](docs/report/errors.md#e83) | §14.2, Lemma 14.3.1 (11706–11718, 11835–11836) | The first control near the singular locus is stated without proof. |
| [E84](docs/report/errors.md#e84) | Lemmas 14.2.3–14.2.4 (11720–11758) | Mathematica series sketches, without the uniformity that Lemma 14.3.1 needs. |
| [E85](docs/report/errors.md#e85) | Lemma 14.3.1 (11784–11872) | `χ₂₃` not examined, a divisibility asserted, the last step sketched. |
| [E86](docs/report/errors.md#e86) | Theorem 14.3.3 (11891–11919) | The block form of the derivative and the local stable manifold are not argued. |
| [E87](docs/report/errors.md#e87) | Remark 14.3.4 (11898–11902), Theorem 14.4.1 (11999–12001) | `q_in` is placed at a point outside the chart. |
| [E88](docs/report/errors.md#e88) | Theorem 14.4.1, §14.4 (11951–12013) | Rests on an uncertified computation of the unstable curve, and on steps it does not cite. |
| [E93](docs/report/errors.md#e93) | §14.4 (11924–11932, 11966–11977) | A global unstable curve is attributed to Theorem 14.3.3, which gives a local one. |
| [E94](docs/report/errors.md#e94) | §14.4 (11951–11955, 11987–11993) | At the threshold `r* ≈ 0.0649` switch and exit coincide: interval arithmetic has no margin. |

### Chapters 15 and 16

| E | Where (book §, TeX lines) | Finding, one line |
| --- | --- | --- |
| [E70](docs/report/errors.md#e70) | §15.1–15.3 (12139–12143, 12233–12276, 12419–12422) | The continuity of the switching time and of the cell maps is asserted, and fails on part of a 2-cell. |
| [E71](docs/report/errors.md#e71) | §15.1–15.3 (12038–12442) | Ranges, a region, a reversed substitution and typos. |
| [E72](docs/report/errors.md#e72) | Propositions 15.2.2 and 15.3.2 (12300–12314, 12467–12491) | Proved "by the discussion" and by figures. |
| [E73](docs/report/errors.md#e73) | §15.3 (12324–12328, 12333–12344) | `F⁻¹ = τFτ` holds only at switching points, not on the closed cells. |
| [E74](docs/report/errors.md#e74) | §15.3 (12411–12422) | On `𝒞₂^A` a double root is a tangency, not a switch; `F_A` is the continuous extension of `F`. |
| [E75](docs/report/errors.md#e75) | Remark 15.3.1, §15.3 (12445–12461) | `q_in` and `q_out` swapped. |
| [E60](docs/report/errors.md#e60) | Theorem 16.3.1, §16.3 (12789–12833) | The set of times at which the lift meets the singular locus is not handled. |
| [E76](docs/report/errors.md#e76) | Theorem 16.1.1, §16.1 (12526–12537, 12680) | An index slip in the boxes `𝒟_ij`. |
| [E77](docs/report/errors.md#e77) | Theorem 16.1.1, §16.1 (12541–12726) | Table 16.1 rests on Mathematica containments, by a method whose hypotheses are not stated. |
| [E78](docs/report/errors.md#e78) | Theorem 16.1.1, §16.1 (12592–12607, 12728–12743) | The convergence in `𝒟_out` does not follow from containment and local stability. |
| [E79](docs/report/errors.md#e79) | Theorem 16.1.1, §16.1 (12668–12676, 12733–12737) | The last row of Table 16.1 fails as written. |
| [E80](docs/report/errors.md#e80) | Theorem 16.2.1, §16.2 (12763–12778) | Details left implicit. |
| [E89](docs/report/errors.md#e89) | Theorem 16.3.1, the last step (12820–12833) | "The trajectory is not periodic": the contradiction is compressed. |
| [E90](docs/report/errors.md#e90) | §16.4, Theorem 16.4.1 (d)–(f) (12862–12987, 13028–13055) | The Reinhardt cells, parts and branch maps are asserted; the descent ignores the diagonal rows. |
| [E91](docs/report/errors.md#e91) | Theorem 16.4.1 (b)–(c) (13001–13026) | A cluster point at a hyperbolic fixed point is not shown to be a limit. |

### Appendix A and the bibliography

| E | Where (book §, TeX lines) | Finding, one line |
| --- | --- | --- |
| [E61](docs/report/errors.md#e61) | Corollary A.1.3, Appendix A.1 (13134–13142) | Stated for `t ≥ 0`, applied on both sides of `0`; no proof. |
| [E92](docs/report/errors.md#e92) | Appendix A.3 (13183–13210) | The local stable set omits that the orbit stays in `U`. |
| [E33](docs/report/errors.md#e33) | Bibliography | A wrong year, two later editions, Zelikin named as first author of Agrachev and Sachkov's book, a Mahler paper that states part of Theorem 2.3.6. |

## 4. Missing hypotheses

| Result | Missing hypothesis | E |
| --- | --- | --- |
| Theorem 3.1.4(3) | the tangents `σ_j'` are Lipschitz | [E13](docs/report/errors.md#e13) |
| Lemma 3.1.8 | the curves `σ_j` are regular | [E34](docs/report/errors.md#e34) |
| The converse of Problem 3.6.2 (§6.1) | the trajectory winds once around the origin | [E15](docs/report/errors.md#e15) |
| Lemma 4.2.3 | `X ≠ 0` | [E17](docs/report/errors.md#e17) |
| Theorem 6.1.1 (Filippov), the existence claim | the velocity sets extended by the cost are convex | [E35](docs/report/errors.md#e35) |
| Lemma 7.3.1 | `⟨X, Z_u⟩ ≠ 0` on `U` | [E26](docs/report/errors.md#e26) |
| Lemma 8.2.1 | `⟨X, Z_u⟩ ≠ 0` on `U_T` | [E52](docs/report/errors.md#e52) |
| Theorem 8.3.2 as restated in Chapter 1 | edge extremality | [E57](docs/report/errors.md#e57) |

Each statement fails without its hypothesis; the user approved the hypotheses of E13, E34 and E35.
Details and counterexamples: [docs/report/errors.md](docs/report/errors.md#missing-hypotheses).

## 5. Redundant hypotheses

- Ten statements hold without some of their hypotheses, and the Lean statements omit them:
  Theorem 3.1.4 (1)–(2), Proposition 3.1.9, Corollary 3.1.10, Lemma 3.3.1, Theorem 5.0.2,
  Corollary 6.5.4, Theorem 6.8.2, Lemmas 7.1.2 and 7.3.1, and Gruber's Corollary 30.1.
- Eleven Lean statements keep, as printed, a hypothesis that their proofs do not use: Lemma 3.1.8,
  Proposition 6.4.1, Lemma 8.1.5, Theorem 8.3.1, Lemmas 13.2.8, 13.3.1 and 13.3.2, the continuity
  claim of §15.1, the case `(m_A, m_B) = (0, 3)` of §15.2, Corollary A.1.3 and Filippov's theorem.
- The Challenge keeps the book's hypotheses. Details:
  [docs/report/errors.md](docs/report/errors.md#redundant-hypotheses).

## 6. How the formalization reads the paper

- Disks `B_r` are Euclidean; densities lie in `[0, ∞]`; a lattice is a discrete `ℤ`-submodule of
  `ℝ²` spanning it, with Mathlib's covolume as its determinant.
- Matrix-valued curves are differentiated entry by entry; differential equations with measurable
  controls are solved in Carathéodory's sense.
- A Pontryagin extremal satisfies the conditions of the maximum principle in the reduced variables
  `(Λ₁, Λ_R)`, with nontriviality of `(λ_cost, Λ₁, Λ_R)` and `H = 0` almost everywhere ([E21](docs/report/errors.md#e21)).
- The maximum principle is applied on the open set `GL₂⁺(ℝ) × C` of `Mat₂(ℝ) × 𝔰𝔩₂(ℝ)`, since
  `SL₂(ℝ)` is not open, with the transversality condition in mixed form.
- "The global minimizer" and "the minimizer `K_min`" are read as every global minimizer and every
  `K_min`; one of each exists ([E47](docs/report/errors.md#e47)).
- Theorem 7.7.1 is read up to time translation, in a conic neighbourhood and for terminal times
  near `t_f` ([E32](docs/report/errors.md#e32)); Theorems 8.2.7 and 8.3.1 as [E55](docs/report/errors.md#e55) and [E56](docs/report/errors.md#e56) say.
- The first control of the Fuller system is the vertex control that is optimal on some `[0, ε]`,
  so a tangency is not a switch ([E62](docs/report/errors.md#e62)).
- Theorem 14.4.1 is stated for extremals that are finitely bang-bang on compact subintervals, which
  is no restriction; N4 is stated orbit-wise, as the proof uses it ([E88](docs/report/errors.md#e88)).
- The boxes of Theorem 16.1.1 have the corrected index, and the box `𝒟₂₂` replaces `𝒟_in` ([E76](docs/report/errors.md#e76));
  Theorem A.3.1 is stated in its local part ([E92](docs/report/errors.md#e92)).
- Apart from the corrections of Section 3, the Lean statements differ from the book's only by the
  omitted hypotheses of Section 5 and the readings in [docs/report/readings.md](docs/report/readings.md).

## 7. Departures from the paper's proofs

Every proof follows the book's argument except the departures below. "Forced" means forced by an
error or gap of the book or by mathematics that Mathlib lacks.

| Result | The formalization's argument | Why |
| --- | --- | --- |
| Lemma 2.2.1 | a maximal half-lattice-free body, cut out by three strips | forced: the printed statement is false ([E1](docs/report/errors.md#e1)); approved by the user |
| Lemma 2.2.5 | Mahler's lattice route, through his Lemma 3 | forced ([E4](docs/report/errors.md#e4)); the route chosen by the user |
| Lemmas 2.4.2 (one step) and 2.4.6 | the differentiability of `σ₂` from its chords; a second-derivative test, not Shifrin | forced ([E8](docs/report/errors.md#e8), [E11](docs/report/errors.md#e11)) |
| The area formula of §3.2 | Green's formula for star-shaped regions | forced: Mathlib has no Green's theorem |
| Lemma 3.1.12 (Jacobi's formula) | the Leibniz expansion and Cramer's rule | forced: Mathlib lacks the book's tools; approved by the user |
| Lemma 4.3.1 | comparison with the smoothed octagon | forced ([E19](docs/report/errors.md#e19)) |
| Theorem 5.0.6 | the cut at a support line, corner by corner | forced ([E43](docs/report/errors.md#e43)) |
| Lemma 5.0.7 (3) | an inclusion in `h₀` and a maximum of two increasing functions | forced ([E44](docs/report/errors.md#e44)) |
| §6.1, the existence of a minimizer | Filippov's theorem under a closed state constraint | forced ([E46](docs/report/errors.md#e46)) |
| §6.2, minimizers are extremals | an open set of matrices; boundary conditions without two redundant equations | forced: `SL₂(ℝ)` is not open ([E21](docs/report/errors.md#e21)) |
| Theorem 7.7.1, step 6 | the inverse function theorem once, at the octagon's fixed point | forced ([E32](docs/report/errors.md#e32)) |
| Proposition 8.1.3 | only competitors close to the edge arc are spliced in | forced ([E48](docs/report/errors.md#e48)) |
| Theorem 8.1.4, two steps | the derivative of `λ₂` at its zeros only; a continuation past an end | forced ([E49](docs/report/errors.md#e49)) |
| Theorem 8.2.7 | the authors' reading, through the edge problem | forced; the reading is the user's decision ([E55](docs/report/errors.md#e55)) |
| Theorem 8.3.1 | a one-sided form, with the form about the control as a corollary | forced; the form is the user's decision ([E56](docs/report/errors.md#e56)) |
| Lemma 13.2.5; the descent of `F` | the substitutions redone for constant controls | forced ([E63](docs/report/errors.md#e63)) |
| Lemma 13.2.6 | the sufficient direction, by the same expansion | forced ([E62](docs/report/errors.md#e62)) |
| Lemma 13.3.2 | a maximizing face that may vary, reduced to the book's cases | forced ([E65](docs/report/errors.md#e65)) |
| Lemma 13.5.2, steps 3 and 5 | exact identities in `ℤ[r, ζ]` and `ℚ(√3)(r)` | forced ([E67](docs/report/errors.md#e67)) |
| Lemma 13.5.5 | an exact Jacobian and a certified eigenvalue bound | forced ([E68](docs/report/errors.md#e68)) |
| The first control near the singular locus | proved from the two signs that the book names | forced ([E83](docs/report/errors.md#e83)) |
| Lemmas 14.2.3–14.2.4 | a comparison of differential equations, with Grönwall bounds | forced ([E84](docs/report/errors.md#e84)) |
| Lemma 14.3.1, Step 2 | a linear equation in a rotating frame | forced: Mathlib has no analytic integrals with parameters |
| Theorem 14.3.3, the local stable manifold | proved directly, without the stable manifold theorem | forced ([E86](docs/report/errors.md#e86)) |
| N4, the fact of Figure 14.2 | the flow along an arc in closed form, and an invariant region | the user's decision ([E88](docs/report/errors.md#e88)) |
| §15.3, `𝔦 = τF` and `F_A` | the involution at switching points; `F_A` as a root-based map | forced ([E73](docs/report/errors.md#e73), [E74](docs/report/errors.md#e74)) |
| Remark 15.3.1 | the labels swapped back; the crossings certified exactly | forced ([E75](docs/report/errors.md#e75)) |
| Proposition 15.3.2, second clause | an exact deformation | the user's decision ([E72](docs/report/errors.md#e72)) |
| Theorem 16.1.1, Table 16.1 | three named facts about whole boxes, proved by identities at the switching root and signs, with one interval chain | forced ([E77](docs/report/errors.md#e77)); the proofs of the facts, the user's decision ([E78](docs/report/errors.md#e78)) |
| Theorem 16.1.1, steps (a), (d) and the last row | a contraction and Banach's theorem; a descent with no re-entry | forced ([E78](docs/report/errors.md#e78), [E79](docs/report/errors.md#e79)) |
| Theorem 16.2.1 | the radial factor in the chart of Lemma 13.5.5 | forced ([E80](docs/report/errors.md#e80)) |
| Theorem 16.3.1, the last step | the meeting set handled; the contradiction made precise | forced ([E60](docs/report/errors.md#e60), [E89](docs/report/errors.md#e89)) |
| Theorem 16.4.1 | the forward invariance of the cluster set; a hyperbolic box | forced ([E90](docs/report/errors.md#e90), [E91](docs/report/errors.md#e91)) |
| Theorem A.3.1 | the map cut off outside its source | forced by the form of the package's theorem ([E92](docs/report/errors.md#e92)) |
| Mahler 1947, Theorem 2 | an exact area formula, not the uniqueness of lattice tilings | forced: Lean lacks that theory |
| Mahler 1947, Lemma 3 | `Δ` of a parallelogram by Mahler's own example; two results of Mahler's Part I proved in the plane | the sources quote them from other works |
| Fejes Tóth's theorem | Dowker's theorem by a merge of normal angles; side counts by angle sums | forced: Mathlib lacks Euler's formula and the Jordan curve theorem |
| The maximum principle | Agrachev and Sachkov's argument in coordinates (D1–D11) | forced: Mathlib lacks the chronological calculus and Carathéodory theory |

The errors and gaps of Mahler's papers and of Agrachev and Sachkov's proof, all repaired, and the
details of the four computed facts are in [docs/report/departures.md](docs/report/departures.md).

## 8. What each result depends on

- Mahler's First conjecture uses, from prior work, the Euler–Arnold equation, Fejes Tóth's theorem,
  Gruber's formula, Mahler 1947, Mahler's Lemma 3, the maximum principle and Theorem A.3.1, all
  proved; it has no hypothesis and uses only the three standard axioms.
- The stable manifold theorem enters through Theorem 14.4.1. Chapters 13 and 15 and the four
  computed facts use no result from prior work.
- The route check finds 140 results of the book in the Lean code and 185 differences from the
  book's citations, each recorded with its reason in [`docs/route_differences.tsv`](docs/route_differences.tsv).
- Details: [docs/report/dependencies.md](docs/report/dependencies.md).

## 9. Not formalized

- By the user's decision (15 November 2026: formalize what the main results need): Chapter 1,
  Chapters 9–12 apart from Lemma 10.1.1, Appendix A apart from A.1.3, A.3, A.6 and A.11, Appendix B,
  and the remarks and claims of the running text that no main result uses.
- Open: the printed Theorem 8.2.7 for abnormal lifts, neither proved nor refuted ([E55](docs/report/errors.md#e55)).
- Within the formalized chapters: the conjectural Remarks 7.6.1 and 7.6.3; the interpretation in
  Remark 13.5.4 ([E69](docs/report/errors.md#e69)); the rest of Proposition 15.3.2, which no proof uses ([E72](docs/report/errors.md#e72)).
- Also: claims of Chapters 15–16 read off figures that no proof uses; Remarks 14.2.2 and 14.3.2;
  the numbers of Figure 14.2 and the global curve ([E93](docs/report/errors.md#e93)); the cells of §16.4.2 ([E90](docs/report/errors.md#e90)); the global
  part of Theorem A.3.1.
- Details: [docs/report/not-formalized.md](docs/report/not-formalized.md).

## 10. The paper in the literature

- The book is an unrefereed preprint: only version 1 exists, with no journal reference or erratum.
- Hales's 2017 preprint announced Theorem 7.5.6 and sketched another proof of Theorem 7.7.1.
- To our knowledge this is the first formalization of Theorems 7.5.6 and 7.7.1, of Chapters 6–8
  and of Mahler's First conjecture, and the packages give the first complete formal proofs of the
  maximum principle and of the stable manifold theorem for maps.
- M. Ho's independent Lean repository formalizes parts of Chapters 2, 3 and 5; this work did not use it.
- Details, with the search of 5 November 2026: [docs/report/literature.md](docs/report/literature.md).

## 11. Simpler arguments

Shorter routes that the formalization records. At the user's request the proofs keep the book's
route; they use only the three marked "taken".

| Result | Shorter argument |
| --- | --- |
| Lemma 7.2.1 | a constant of motion gives the circle at once (about 45 Lean lines against 300) |
| Lemma 7.5.5 | Cayley–Hamilton, without eigenvalues |
| Lemma 7.5.3, the case `y ∈ [2, 3]` | two brackets, each nonnegative by `ln u ≥ 1 - 1/u` |
| Proposition 3.1.9 | `X` is Lipschitz on `ℝ` directly, with no periodic extension |
| Lemma 3.1.8 | one determinant identity in place of the area argument |
| Theorem 7.7.1, step 6 | the linear independence of the section basis is not needed |
| Theorem 7.5.1 | only `h ≠ ±I` is used, not ellipticity |
| The reflection invariance of `𝔥*` | read off the inequalities of the star domain |
| Theorem 5.0.6 | the step `h₀ ∩ h₁ ∩ h₂ = ∅` can be dropped |
| Lemma 5.0.7 (2) | no derivatives, and valid for `y² ≥ 2/3` |
| Lemma 6.1.2 in §6.1 | a linear-fractional image of a convex set is convex |
| Lemma 8.2.1 | the matrices `Z_{e_i}` span `𝔰𝔩₂(ℝ)` |
| Theorem 8.1.4 | finiteness from the isolation of the zeros, with no count |
| Theorem 8.3.1, claim (a) | Lemma 8.2.2 gives the derivative of `Λ_R`, without the Gronwall step |
| Straight edges in Remark 8.3.3 | a proof without angle functions (taken) |
| The first control of `q_out` | Lemma 13.2.6 at once |
| Convergence in `𝒟_out` | the contraction alone, without the existence part of Banach's theorem |
| The `∂`-loci of §15.3 | a double root of `χ_B` at `0`; along `∂_res`, time reversal alone (taken) |
| The continuity of `F_A` | Mathlib's one-sided continuity of roots |
| (14.1.3) | a closed form for `Λ_R` (taken) |
| Lemma 14.3.1, Step 10 | the inverse function theorem, with a certified determinant |
| Theorem 14.4.1 | N4's region without the unstable curve, which frees Mahler's First from the stable manifold theorem |
| `q_out` is not a cluster point | the same region, in place of the hyperbolic box |
| The two large cofactors of N4 | a cofactor-free device used elsewhere in the proof |
| Lemma 3.1 of the proof of N4 | a lower bound without derivatives |
| `F(R₀) ⊆ 𝒟₀₀` | contains half of `DOutContracts` |
| The reading of Theorem 14.4.1 | the second part of the hypothesis is not used |
| Theorem A.3.1 | the package's form for small neighbourhoods, without the cut-off |

Details: [docs/report/simpler-arguments.md](docs/report/simpler-arguments.md).
