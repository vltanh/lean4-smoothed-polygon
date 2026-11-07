# Smoothed polygons in the Reinhardt control problem, in Lean

[![Lean Action CI](https://github.com/vltanh/lean4-smoothed-polygon/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-smoothed-polygon/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of the smoothed-polygon core of Thomas Hales and Koundinya Vajjha,
*Packings of Smoothed Polygons* ([arXiv:2405.04331v1](https://arxiv.org/abs/2405.04331), 2024),
with its geometric foundations. The book reformulates the Reinhardt problem, which asks for the
centrally symmetric convex disk whose densest packing is least dense, as an optimal control problem
on `SL₂(ℝ)`, and studies its Pontryagin extremals. This project formalizes the historical results
on packings, critical lattices and the boundary of the minimizer (Chapter 2), the reformulation
(Chapters 3, 4, 6 and 7, with Appendix A.6 and A.11), and its main construction: **every smoothed
`(6k+2)`-gon, in particular Reinhardt's smoothed octagon, is a Pontryagin extremal of the
Reinhardt control problem with bang-bang control** (Theorem 7.5.6), **the smoothed octagon is a
centrally symmetric convex disk whose greatest packing density is
`(8 - √32 - ln 2)/(√8 - 1) ≈ 0.902414`**, and **the smoothed octagon is an isolated extremal**
(Theorem 7.7.1). The book's main theorem, Mahler's First conjecture (Theorem 16.3.1), is not
formalized.

## What is proved

- Every numbered result of the formalized chapters, by the book's own arguments where they hold:
  among them Filippov's theorem (Theorem 6.1.1, cited), Proposition 6.4.1 on left-invariant
  systems, and Theorem 7.7.1, whose proof the book only sketches; and Remarks 2.2.4, 7.5.2 and
  7.6.4, which the book states without proof. What is left in these chapters (two conjectural
  remarks, and the application of Filippov's theorem, which needs Chapter 5) is listed in
  [REPORT.md, Section 9](REPORT.md#9-not-formalized).
- Lemma 2.2.1 is false as printed; it is refuted in Lean and proved in corrected form (E1).
  Theorem 7.7.1 is false read literally and holds up to time translation, for terminal times near
  `t_f` (E32); Lemma 3.1.8 and the existence of optimal controls in Filippov's theorem each lack
  a hypothesis (E34, E35). The user approved the four corrected statements.
- The formalization is unconditional: no cited theorem is assumed. The cited results that the
  proofs use are proved in [`External/`](External): Fejes Tóth's theorem that lattice packings are densest for
  centrally symmetric disks, Gruber's lattice density formula, the theorems of Minkowski and Mahler
  on critical lattices and circumscribed hexagons, and the Euler–Arnold equation; Filippov's
  theorem is proved there too ([External/README.md](External/README.md)). A *Pontryagin extremal* is defined by the conditions
  of the maximum principle ([`IsPontryaginExtremal`](Challenge.lean#L171)), so the maximum principle itself is not needed.
- `lake build` succeeds; the only `sorry`s are the statements of [`Challenge.lean`](Challenge.lean). There is no
  `axiom`. `lake env lean scripts/Audit.lean` checks that every declaration of the library and the
  Challenge theorems depend only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).

## Main results

- [`SmoothedPolygonsChallenge.smoothed_polygon_extremal`](Challenge.lean#L335) (Theorem 7.5.6): for every `k ≥ 1`, the
  state trajectory with the control `e₃, e₁, e₂, e₃, …` on `3k+1` switching intervals of length
  `t_sw`, starting from `g(0) = I₂` and `X(0) = Φ(i y₀)` with `4/(3y₀² + 1) = 2 cos(πk/(3k+1))`,
  exists, is unique on `[0, t_f]`, has bang-bang control, and lifts to a Pontryagin extremal, with
  the nontriviality condition of the maximum principle imposed on the reduced costate
  `(λ_cost, Λ₁, Λ_R)` (on the book's full costate it would hold for every trajectory, E21).
- [`SmoothedPolygonsChallenge.smoothed_octagon_density`](Challenge.lean#L351) (the example before Theorem 7.5.6): for
  `k = 1`, `y₀ = √((√8 - 1)/3)` and `t_sw = ln 2/(2√(√8 - 1))`; the cost of the smoothed octagon's
  trajectory is `√12 (8 - √32 - ln 2)/(√8 - 1) ≈ 3.126 < π`; the trajectory bounds a balanced disk
  `K` in circle representation whose area is that cost; and the greatest packing density of `K`
  (Definition 2.1.1: the supremum of the densities of packings of congruent copies, measured in
  Euclidean disks) is `(8 - √32 - ln 2)/(√8 - 1)`. The book takes this density from a normalization
  it never checks for the octagon (E12); the formalization proves it for every balanced disk.

The library also proves Theorem 7.7.1 ([`theorem7_7_1`](SmoothedPolygons/Ch7/Isolated.lean#L508)), which is not part of the Challenge: there
are a neighbourhood `U` of the octagon's initial condition `(X(0), Λ₁(0), Λ_R(0), λ_cost = -1)`
and `ε > 0` such that every Pontryagin extremal with terminal time `|T - t_f| < ε` whose initial
condition lies in `U` after rescaling its costate by a positive factor is the octagon's lifted
trajectory started at some time `s`, with a proportional costate; in particular `T = t_f`.
Without the time shift and the bound on `T` the statement is false (E32); the octagon's own lift
meets the hypotheses ([`theorem7_7_1_octagon`](SmoothedPolygons/Ch7/Isolated.lean#L633)).

The Reinhardt conjecture itself (that the smoothed octagon is the least dense) remains open, and
is not claimed here.

## Palomar

[`Challenge.lean`](Challenge.lean) states the two results of the list above with `sorry`; [`Solution.lean`](Solution.lean) restates them word for
word and proves them from the library. [`comparator.json`](comparator.json) configures Palomar's Comparator:

```sh
lake env lake comparator --config=comparator.json   # needs bubblewrap; expect "Your solution is okay!"
```

The definitions that the Challenge uses are kept in [`SmoothedPolygons/Defs.lean`](SmoothedPolygons/Defs.lean) between two
markers and copied into the Challenge by `python3 scripts/sync_challenge_defs.py` (CI checks the
copy with `--check`). [`formalization.yaml`](formalization.yaml) holds Palomar's metadata, and the workflow
[`palomar_preflight.yml`](.github/workflows/palomar_preflight.yml) runs Palomar's mechanical verification on demand.

## Audit summary

From [REPORT.md](REPORT.md), whose E-numbers are used here.

- **Errors:** Lemma 2.2.1 (Reinhardt's tiling lemma) is false as printed: a lattice packing need
  not be a tiling by a hexagon containing the disk (E1; counterexample `L = ℤ²`,
  `K = {|2y₀ + y₁| ≤ 1, |2y₁ - y₀| ≤ 1}`, refuted in Lean). The book only needs its classical
  packing form, which is proved, so nothing after it breaks. The terminal condition
  `X(t_f) = R X₀ R⁻¹` of the control problem should be `R⁻¹ X₀ R` (E16); the coefficient `a(u)` of
  the half-plane control problem has the wrong sign (E20). The nontriviality condition of a
  Pontryagin extremal, imposed on the full costate `(Λ₁, Λ₂)`, lets every admissible trajectory lift
  to an extremal; it must be imposed on the reduced costate `(Λ₁, Λ_R)` (E21). Theorem 7.7.1 (the
  smoothed octagon is an isolated extremal) is false read literally: the octagon's lift started at
  another time, or run for several laps, is another such extremal (E32). Slips that do not affect
  any result: E6 (the definition of a critical lattice omits admissibility), E7, E8, E10, E14, E22,
  E24.
- **Gaps:** the proof that the minimizer has no corners (Lemma 2.2.5) has a gap its argument cannot
  close; it is closed here by Mahler's lattice route (E4). The octagon's density value rests on a
  fact the book never proves, that balanced disks have least circumscribed hexagon of area `√12`;
  it is true and proved here (E12). The inequality behind the maximum principle for the smoothed
  polygons is left "as a tedious but elementary exercise"; it is true, tight at one corner, and
  proved here (E29). Lemma 2.4.6 applies a theorem about smooth curves to curves that are only
  `C¹,¹` (E11). Lemma 4.3.1 does not justify that the minimizer has area `< π` (E19). The proof of
  Theorem 7.7.1 is a sketch: the switching structure of nearby extremals is not argued, the "direct
  calculation" of hyperbolicity is not given, and the uniformity in the parameter `d` that its
  conclusion needs is missing; all are supplied here (E32). Remarks 7.5.2 and 7.6.4 are stated
  without proof, the second read off a figure; both are proved (E36, E37). Further gaps, all
  filled: E2, E3, E5, E8, E9, E15, E18, E23, E30, E31, E34.
- **Missing hypotheses:** Theorem 3.1.4(3) is false for a general convex disk and holds under the
  standing assumptions of §2.4 (E13, formalized with the hypothesis `σ_j'` Lipschitz, approved by
  the user); Lemma 3.1.8 (hyperbolic arcs) is false unless the curves are regular, as §2.4 assumes
  (E34, approved by the user); Filippov's theorem (Theorem 6.1.1, cited without a source) asserts
  that an optimal control exists when the velocity sets are convex, which fails for costs that
  depend on the control and holds when the velocity sets extended by the cost are convex (E35,
  approved by the user); Lemma 4.2.3 needs `X ≠ 0` (E17); Lemma 7.3.1 needs `⟨X, Z_u⟩ ≠ 0` on the
  control set (E26).
- **Redundant hypotheses:** eight results of the book and one cited result hold without some of
  their hypotheses, which the Lean statements omit
  ([Section 5](REPORT.md#5-redundant-hypotheses)); for instance Lemma 7.3.1 holds for every compact
  convex control set on which `⟨X, Z_u⟩ ≠ 0`. The Challenge keeps the book's hypotheses.
- **Use of cited results:** all correct, except Shifrin's characterization of convex curves, which
  Lemma 2.4.6 applies outside its hypotheses (E11); Filippov's theorem is stated without a source
  and with an existence claim that is false in general, though not for the Reinhardt problem,
  whose cost depends only on the state (E35)
  ([Section 2](REPORT.md#2-results-from-prior-work-and-how-the-paper-uses-them)).
- **Proofs:** every proof follows the book's argument, except the departures of
  [Section 7](REPORT.md#7-departures-from-the-papers-proofs), each forced by an error or gap of the
  book or by mathematics Mathlib lacks: Lemma 2.2.1 (its printed form is false), Lemma 2.2.5 (by
  Mahler's lattice route, chosen by the user), one step each of Lemmas 2.4.2 and 2.4.6, the area
  formula of §3.2 (polar coordinates for Green's theorem), Jacobi's formula (approved by the
  user), Lemma 4.3.1, and one step of Theorem 7.7.1 (the inverse function theorem applied once at
  the octagon's fixed point, which gives the uniformity the book's per-`d` argument lacks). The
  cited results are proved by their sources' arguments, with the exceptions listed there (notably
  Fejes Tóth's theorem, through Böröczky's cell lemma, with angle sums in place of Euler's
  formula); Filippov's theorem is proved by the standard argument, without comparison with its
  source, which was not available to us.

## Credits

- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code, with parallel sub-agents,
  at the request of The-Anh Vu-Le, who chose the scope and approved the corrections, following the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill.
- The statements and the proofs were checked against the book's TeX source by independent agents;
  no person has reviewed the proofs.
- Made on 5–7 November 2026 in three rounds (the control-theoretic chapters; then Chapter 2, its
  cited theorems and the octagon's packing density; then the rest of these chapters: Lemma 3.1.8,
  Filippov's theorem, Proposition 6.4.1, Theorem 7.7.1 and the remarks). [CREDITS.md](CREDITS.md)
  has the procedure and the figures.

## Related work

- The reformulation as a control problem, the claim that the smoothed `(6k+2)`-gons are
  Pontryagin extremals, and a sketched proof that the smoothed octagon is an isolated extremal go
  back to Hales's 2017 preprint ([arXiv:1703.01352](https://arxiv.org/abs/1703.01352)); the book is
  still an unrefereed preprint, with one version and no erratum.
- An independent, unreviewed Lean development by M. Ho
  ([sunfishho/reinhardt-density-bound](https://github.com/sunfishho/reinhardt-density-bound),
  2 November 2026) claims the lower bound `0.8950112` for the least packing density, above
  Tammela's `0.892656`, and formalizes parts of the book's Chapters 2, 3 and 5, among them the
  state dynamics and the area–cost identity of §3.2; it has no Hamiltonian or costate and does not
  formalize Theorem 7.5.6. This work did not use it.
- We found no earlier formal proof of Fejes Tóth's packing theorem, Dowker's theorem, or Mahler's
  theorems on critical lattices and circumscribed hexagons, which this project proves on the way.
- More in [REPORT.md, Section 10](REPORT.md#10-the-paper-in-the-literature).

## What's next

The main theorem, Mahler's First conjecture, needs Chapters 5 and 8–16: the Pontryagin maximum
principle (or the existence of an extremal lift of a minimizer), the compactification of Chapter 5
to which Filippov's theorem (proved here on `ℝⁿ`) is applied, and the analysis of chattering.
Beyond Theorem 7.7.1, Hales's 2017 preprint claims that the smoothed octagon is a strict local
minimum in a micro-local sense, by an interval-arithmetic computation not published in checkable
form; the smoothed `(6k−2)`-gons, claimed to be extremals of the maximization problem in 2023–24
posters, need a new sign inequality. See [REPORT.md, Section 11](REPORT.md#11-whats-next).

## Building

```sh
lake exe cache get     # Mathlib's compiled files
lake build             # the library, the Challenge and the Solution
lake env lean scripts/Audit.lean                                            # axioms and routes
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
python3 scripts/sync_challenge_defs.py --check                              # the Challenge's definitions
python3 scripts/linkify_docs.py                                             # links from the documents to the code
```

Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`.

## Layout

| Path | Content |
| --- | --- |
| [`Basic/`](Basic) | general mathematics, for Mathlib: matrix calculus and ODEs, generalized circles under `SL₂(ℝ)`, areas and convexity of star-shaped regions, Dowker's theorem, hexagon lattice tilings, polygon angles, Fejes Tóth's cell lemma, the Tietze–Nakajima theorem, critical lattices, lattice-packed bodies, control systems and Filippov's compactness theorem, measurable selection ([Basic/README.md](Basic/README.md)) |
| [`External/`](External) | cited results, proved: Fejes Tóth, Gruber, Minkowski–Mahler, Mahler 1947 (Theorem 2, half of Lemma 3), Euler–Arnold, Filippov ([External/README.md](External/README.md)) |
| [`SmoothedPolygons/Defs.lean`](SmoothedPolygons/Defs.lean) | the definitions that the Challenge uses |
| [`SmoothedPolygons/Ch2/`](SmoothedPolygons/Ch2) | Chapter 2: packing densities and Fejes Tóth's theorem (§2.1), Reinhardt's lemmas and the minimizer (§2.2), critical lattices and hexagons (§2.3), the boundary of the minimizer and balanced disks (§2.4), the density of balanced disks, the refutation of the printed Lemma 2.2.1 |
| [`SmoothedPolygons/Ch3/`](SmoothedPolygons/Ch3) | the control problem: state dynamics, hyperbolic arcs (Lemma 3.1.8), Jacobi's formula, cost and the area formula of §3.2, controls, Lie algebra dynamics, Proposition 3.6.1, Problem 3.6.2 |
| [`SmoothedPolygons/Ch4/`](SmoothedPolygons/Ch4) | the adjoint orbit and the upper half-plane, the star domain, the half-plane control problem, Lemma 4.3.1, the dihedral group on the ideal vertices (§4.6) |
| [`SmoothedPolygons/Ch6/`](SmoothedPolygons/Ch6) | left-invariant control systems on Lie groups (Definition 6.3.1, Proposition 6.4.1), the Hamiltonian, the costate equations, the half-plane Hamiltonian |
| [`SmoothedPolygons/Ch7/`](SmoothedPolygons/Ch7) | constant control, faces, the spline, Theorem 7.5.1, Lemma 7.5.3 and its inequality, Lemma 7.5.5, Theorem 7.5.6, the smoothed polygons as balanced disks, Remarks 7.5.2 and 7.6.4, Theorem 7.7.1 (`Isolated.lean` and `Isolated/`) |
| [`SmoothedPolygons/AppA/`](SmoothedPolygons/AppA) | the functional derivative, matrix identities, the Riemannian metric |
| [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean), [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml) | Palomar |
| [`scripts/`](scripts) | the audit, the route check, the Challenge sync, the documentation checks |
| [`docs/`](docs) | the routes of the book's proofs and the recorded differences |
| `.github/workflows/` | CI and Palomar's preflight |

## GitHub configuration

- [`lean_action_ci.yml`](.github/workflows/lean_action_ci.yml) runs on every push: it builds the project, checks that the audit imports
  every module, runs the audit and the route check, and checks the Challenge's copy of the shared
  definitions, the documents' links to the code and their tables.
- [`palomar_preflight.yml`](.github/workflows/palomar_preflight.yml) runs only on demand (`gh workflow run palomar_preflight.yml`); it needs
  the repository to be public, and declares the authorization relationship for Palomar.

## License

Apache-2.0; see [LICENSE](LICENSE).
