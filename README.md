# Smoothed polygons in the Reinhardt control problem, in Lean

[![Lean Action CI](https://github.com/vltanh/lean4-smoothed-polygon/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-smoothed-polygon/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of the control-theoretic core of Thomas Hales and Koundinya Vajjha,
*Packings of Smoothed Polygons* ([arXiv:2405.04331v1](https://arxiv.org/abs/2405.04331), 2024).
The book reformulates the Reinhardt problem, which asks for the centrally symmetric convex disk
whose densest packing is least dense, as an optimal control problem on `SL₂(ℝ)`, and studies its
Pontryagin extremals. This project formalizes that reformulation (Chapters 3, 4, 6 and 7, with
Appendix A.6 and A.11) and its main construction: **every smoothed `(6k+2)`-gon, in particular
Reinhardt's smoothed octagon, is a Pontryagin extremal of the Reinhardt control problem with
bang-bang control** (Theorem 7.5.6), and the smoothed octagon's density is
`(8 - √32 - ln 2)/(√8 - 1) ≈ 0.902414`. The book's main theorem, Mahler's First conjecture
(Theorem 16.3.1), is not formalized.

## What is proved

- Every numbered result of the formalized chapters, by the book's own arguments, with four
  exceptions that are listed, with their reasons, in [REPORT.md, Section 9](REPORT.md#9-not-formalized).
- The formalization is unconditional: no cited theorem is assumed. The one cited result that a
  proof uses, the Euler–Arnold equation (Cushman–Bates), is proved in [`External/`](External)
  ([External/README.md](External/README.md)). A *Pontryagin extremal* is defined by the conditions
  of the maximum principle ([`IsPontryaginExtremal`](Challenge.lean#L162)), so the maximum principle itself is not needed.
- `lake build` succeeds; the only `sorry`s are the statements of [`Challenge.lean`](Challenge.lean). There is no
  `axiom`. `lake env lean scripts/Audit.lean` checks that every declaration of the library and the
  Challenge theorems depend only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).

## Main results

- [`SmoothedPolygonsChallenge.smoothed_polygon_extremal`](Challenge.lean#L220) (Theorem 7.5.6): for every `k ≥ 1`, the
  state trajectory with the control `e₃, e₁, e₂, e₃, …` on `3k+1` switching intervals of length
  `t_sw`, starting from `g(0) = I₂` and `X(0) = Φ(i y₀)` with `4/(3y₀² + 1) = 2 cos(πk/(3k+1))`,
  exists, is unique on `[0, t_f]`, has bang-bang control, and lifts to a Pontryagin extremal, with
  the nontriviality condition of the maximum principle imposed on the reduced costate
  `(λ_cost, Λ₁, Λ_R)` (on the book's full costate it would hold for every trajectory, E8).
- [`SmoothedPolygonsChallenge.smoothed_octagon_density`](Challenge.lean#L234) (the example before Theorem 7.5.6): for
  `k = 1`, `y₀ = √((√8 - 1)/3)`, `t_sw = ln 2/(2√(√8 - 1))`, and the cost of the smoothed octagon's
  trajectory is `√12 (8 - √32 - ln 2)/(√8 - 1) ≈ 3.126 < π`, so its density, the cost divided by
  `√12`, is Reinhardt's value. In the book the cost is the area of the disk by Green's theorem and
  the density is the area divided by `√12` by a theorem of Reinhardt and Fejes Tóth; those two
  identifications are not formalized ([REPORT.md, Section 6](REPORT.md#6-how-the-formalization-reads-the-paper)).

The Reinhardt conjecture itself (that the smoothed octagon is the least dense) remains open, and
is not claimed here.

## Palomar

[`Challenge.lean`](Challenge.lean) states the two results above with `sorry`; [`Solution.lean`](Solution.lean) restates them word for
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

- **Errors:** the terminal condition `X(t_f) = R X₀ R⁻¹` of the control problem should be
  `R⁻¹ X₀ R` (E3); the coefficient `a(u)` of the half-plane control problem has the wrong sign (E7).
  The nontriviality condition of a Pontryagin extremal, imposed on the full costate `(Λ₁, Λ₂)`,
  lets every admissible trajectory lift to an extremal (`λ_cost = 0`, `Λ₁ = 0`, `Λ₂ = X`); it must
  be imposed on the reduced costate `(Λ₁, Λ_R)`, as the formalization does (E8). Slips that do not
  affect any result: E2, E9 (a sign convention for `ad*`), E11.
- **Gaps:** the inequality behind the maximum principle for the smoothed polygons is left "as a
  tedious but elementary exercise"; it is true and tight at one corner, and is proved here (E16).
  Lemma 4.3.1 does not justify that the minimizer has area `< π` (E6). The proof of Theorem 6.8.3
  is omitted (E10), the proof of Lemma 7.5.5 argues the converse of the statement (E17), and the
  proof of Theorem 7.5.6 checks only transversality (E18). Theorem 7.7.1 has only a proof sketch
  (E19).
- **Missing hypotheses:** Theorem 3.1.4(3) is false for a general convex disk and holds under the
  standing assumptions of §2.4 (E1, formalized with the hypothesis `σ_j'` Lipschitz, approved by
  the user); Lemma 4.2.3 needs `X ≠ 0` (E4); Lemma 7.3.1 needs `⟨X, Z_u⟩ ≠ 0` on the control set
  (E13).
- **Redundant hypotheses:** eight results hold without some of their hypotheses, which the Lean
  statements omit ([Section 5](REPORT.md#5-redundant-hypotheses)); for instance Lemma 7.3.1 holds
  for every compact convex control set on which `⟨X, Z_u⟩ ≠ 0`, and parts (1) and (2) of
  Theorem 3.1.4 for every `C¹` multi-curve induced by a curve in `SL₂(ℝ)`. The Challenge keeps the
  book's hypotheses.
- **Use of cited results:** the Euler–Arnold equations (Cushman–Bates), the Iwasawa decomposition,
  Rademacher's theorem and `det exp(X) = exp(tr X)` are used correctly
  ([Section 2](REPORT.md#2-results-from-prior-work-and-how-the-paper-uses-them)).
- **Proofs:** every proof follows the book's argument, except two departures
  ([Section 7](REPORT.md#7-departures-from-the-papers-proofs)): Jacobi's formula (Lemma 3.1.12) by
  the Leibniz expansion, since Mathlib has no differentiable eigen-decomposition (approved by the
  user); and Lemma 4.3.1, whose gap cannot be closed by the book's comparison with the unit disk
  and is repaired by comparison with the smoothed octagon. The gaps of Lemma 7.5.5 and
  Theorem 7.5.6 are filled along the book's lines.

## Credits

- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code, with parallel sub-agents,
  at the request of The-Anh Vu-Le, who chose the scope and approved the corrections, following the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill.
- The statements and the proofs were checked against the book's TeX source by independent agents;
  no person has reviewed the proofs.
- Made on 5 November 2026. [CREDITS.md](CREDITS.md) has the procedure and the figures.

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
- More in [REPORT.md, Section 10](REPORT.md#10-the-paper-in-the-literature).

## What's next

The area–cost identity for convex disks (already proved, by a radial-sector formula, in Ho's
repository) and the theorem of Reinhardt and Fejes Tóth would turn the octagon value into a
packing density. Theorem 7.7.1 (the smoothed octagon is an isolated extremal) needs the Jacobian of
a Poincaré map, whose fixed point the explicit costate lift gives; the smoothed `(6k−2)`-gons,
claimed to be extremals of the maximization problem in 2023–24 posters, need a new sign
inequality. See [REPORT.md, Section 11](REPORT.md#11-whats-next).

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
| [`Basic/`](Basic) | general mathematics, for Mathlib: entrywise calculus of matrix curves, the matrix exponential, FTC and Grönwall for matrix ODEs, generalized circles under `SL₂(ℝ)` ([Basic/README.md](Basic/README.md)) |
| [`External/`](External) | cited results, proved: the Euler–Arnold equation ([External/README.md](External/README.md)) |
| [`SmoothedPolygons/Defs.lean`](SmoothedPolygons/Defs.lean) | the definitions that the Challenge uses |
| [`SmoothedPolygons/Ch2/`](SmoothedPolygons/Ch2) | multi-points, multi-curves, balanced disks (Definitions 2.4.1, 2.4.7); the unit disk is a balanced pair |
| [`SmoothedPolygons/Ch3/`](SmoothedPolygons/Ch3) | the control problem: state dynamics, Jacobi's formula, cost, controls, Lie algebra dynamics, Proposition 3.6.1, Problem 3.6.2 |
| [`SmoothedPolygons/Ch4/`](SmoothedPolygons/Ch4) | the adjoint orbit and the upper half-plane, the star domain, the half-plane control problem, Lemma 4.3.1 |
| [`SmoothedPolygons/Ch6/`](SmoothedPolygons/Ch6) | the Hamiltonian, the costate equations, the half-plane Hamiltonian |
| [`SmoothedPolygons/Ch7/`](SmoothedPolygons/Ch7) | constant control, faces, the spline, Theorem 7.5.1, Lemma 7.5.3 and its inequality, Lemma 7.5.5, Theorem 7.5.6 |
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
