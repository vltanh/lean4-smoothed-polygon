# Smoothed polygons in the Reinhardt control problem, in Lean

[![Lean Action CI](https://github.com/vltanh/lean4-smoothed-polygon/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-smoothed-polygon/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of Thomas Hales and Koundinya Vajjha, *Packings of Smoothed Polygons*
([arXiv:2405.04331v1](https://arxiv.org/abs/2405.04331), 2024). The book recasts the Reinhardt
problem (which centrally symmetric convex disk packs least densely?) as an optimal control problem
on `SL₂(ℝ)` and studies its Pontryagin extremals.

- **Mahler's First conjecture** (Theorem 16.3.1, the book's main theorem) is proved with no
  hypothesis: every global minimizer is bang-bang with finitely many switches, and every worst
  disk `K_min` is a smoothed polygon.
- Chapters 2–8, §9.0–9.1, Chapters 13–16 and Appendices A.3, A.6 and A.11 are formalized: every
  numbered result is proved, some in corrected form (see below), except two conjectural remarks, the
  Mathematica-based part of Remark 13.5.4 and Proposition 15.3.2 (read off figures, used by no proof,
  proved in part).
- The four facts that the book reads off Mathematica computations are proved without computer
  assistance, a departure from the book by the user's decision (below).
- Not formalized, by the user's decision: Chapter 1, the rest of Chapters 9–12 (apart from Lemma
  10.1.1), the other appendices, Appendix B, and the remarks that no main result uses.
- The Reinhardt conjecture itself (that the smoothed octagon is the worst disk) is open and not
  claimed.

## Status

| Part of the book | Status |
| --- | --- |
| Ch. 2, historical results (packings, critical lattices, the minimizer's boundary) | proved |
| Ch. 3–4, the control problem and the upper half-plane | proved |
| Ch. 5, compactification of the star domain | proved |
| Ch. 6, Hamiltonians; existence of a minimizer (§6.1); every minimizer is an extremal (§6.2) | proved |
| Ch. 7, the smoothed `(6k+2)`-gons are extremals; the octagon is an isolated extremal | proved |
| Ch. 8, edge problems, singular locus, finite bang-bang | proved (two theorems restated, see below) |
| Ch. 9, §9.0–9.1, circular control: rotation invariance (Theorem 9.0.3), conservation of angular momentum (Theorem 9.1.6) | proved (the Noether–Sussmann theorem in Sussmann's form; as printed it is false, E95) |
| Ch. 13, the triangular Fuller system: blow-up, Poincaré map, fixed points `q_out`, `q_in` and their stability | proved |
| Ch. 14, the analytic extension of the Reinhardt–Poincaré map across the singular locus, its stable and unstable manifolds, Theorem 14.4.1 (no return) | proved (the unstable curve of Figure 14.2 without computer assistance) |
| Ch. 15, the geometry of the Fuller–Poincaré map: cell coordinates, smaller cells, the involution `τF` | proved (Proposition 15.3.2 in part) |
| Ch. 16, Theorems 16.1.1 (global basin), 16.2.1, 16.4.1 (cluster point theorem) and 16.3.1 (Mahler's First conjecture) | proved (Table 16.1 without computer assistance) |
| Appendix A.1 (Corollary A.1.3), A.3 (Theorem A.3.1, local part), A.6, A.11 | proved |
| Ch. 9 from §9.2, Ch. 10–12 apart from Lemma 10.1.1; the other appendices; Appendix B | not formalized (the user's scope decision) |

## Main results

| Result | Lean name | Statement |
| --- | --- | --- |
| Theorem 16.3.1 | [`SmoothedPolygonsChallenge.mahler_first_conjecture`](Challenge.lean#L468) | Mahler's First conjecture: every global minimizer is bang-bang with finitely many switches, and every `K_min` is a smoothed polygon |
| Theorem 7.5.6 | [`SmoothedPolygonsChallenge.smoothed_polygon_extremal`](Challenge.lean#L476) | every smoothed `(6k+2)`-gon is a Pontryagin extremal with bang-bang control |
| Example before 7.5.6 | [`SmoothedPolygonsChallenge.smoothed_octagon_density`](Challenge.lean#L492) | the smoothed octagon's greatest packing density is `(8 - √32 - ln 2)/(√8 - 1) ≈ 0.902414` |
| Theorem 7.7.1 | [`theorem7_7_1`](SmoothedPolygons/Ch7/Isolated.lean#L508) | the octagon is an isolated extremal, up to time translation (E32) |
| §6.1, §6.2 and `K_min` | [`exists_isReinhardtMinimizer_isPontryaginExtremal_isWorstDisk`](SmoothedPolygons/Ch6/WorstDisk.lean#L250) | a global minimizer exists, is an extremal, and bounds a worst disk `K_min` |
| Theorem 9.1.6 | [`theorem9_1_6`](SmoothedPolygons/Ch9/AngularMomentum.lean#L1689) | the angular momentum `⟨J, Λ₁ + Λ_R⟩` is conserved along every Pontryagin extremal of the circular control problem (E97) |
| Lemma 13.5.5 | [`lemma13_5_5`](SmoothedPolygons/Ch13/Stability.lean#L281) | the fixed point `q_out` of the Fuller–Poincaré map (Lemma 13.5.2) is asymptotically stable, and `q_in = τ(q_out)` is unstable |
| Theorem 14.4.1 | [`theorem14_4_1_unconditional`](SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L51) | a trajectory that emanates from the fixed point over `q_out` on the exceptional divisor does not return to it |
| Theorem 16.1.1 | [`theorem16_1_1_unconditional`](SmoothedPolygons/Ch16/BasinFacts.lean#L53) | every orbit of the Fuller–Poincaré map on `Ξ_{𝒲,0}/V_T` other than `q_in` tends to `q_out` |
| Theorem 16.4.1 | [`theorem16_4_1_unconditional`](SmoothedPolygons/Ch16/BasinFacts.lean#L71) | switching points that accumulate on the singular locus converge to `q_in`, along its stable curve |

The first three are the Palomar Challenge ([`Challenge.lean`](Challenge.lean));
[`theorem16_3_1_unconditional`](SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L94) proves the first.

### The computed facts

The book reads four facts off Mathematica computations that it did not certify. By the user's
decision they are proved without computer assistance, by exact structure and a few explicit
inequalities, with no enumeration of boxes; the few certificates found by computer (Bernstein
coefficients, polynomial cofactors) are checked by Lean.

| Fact | What it says | How it is proved |
| --- | --- | --- |
| [`UnstableCurveLeavesStarDomain`](SmoothedPolygons/Ch14/UnstableCurve.lean#L174) (N4, Figure 14.2) | the orbit of every point of the unstable curve over `q_out` switches cyclically, then leaves the star domain (E88) | the Reinhardt flow along an arc in closed form, and a region that one step keeps until an arc leaves |
| [`TriFuller.DOutContracts`](SmoothedPolygons/Ch16/BasinHypotheses.lean#L236) (Table 16.1) | the map sends the box `𝒟_out` into itself, and its square into a box where it is a `3/4`-contraction (the contraction is missing from the book, E78) | identities at the switching root; derivative bounds by hand on one box |
| [`TriFuller.CellTwoEntersDOut`](SmoothedPolygons/Ch16/BasinHypotheses.lean#L260) | every point of the second big cell reaches `𝒟_out` within three steps | identities and signs of switching functions |
| [`TriFuller.BoxSubclaims`](SmoothedPolygons/Ch16/BasinHypotheses.lean#L278) | every other box except `𝒟₂₂` goes to the second cell or to a smaller box | the same |

[`numerics/`](numerics) is a Python reference in rigorous ball arithmetic that checks these facts
numerically and guided the proofs; the Lean proofs do not depend on it
([numerics/README.md](numerics/README.md)).

## What the audit found

[REPORT.md](REPORT.md) checks the book against the formalization; 97 findings (E1–E97). The main
ones:

| | Finding |
| --- | --- |
| E1 | Lemma 2.2.1 is false as printed (refuted in Lean); its classical form, all the book needs, is proved. |
| E15 | The converse of the control problem used in §6.1 is false (the unit circle run seven times is admissible); it holds for winding number one, which every trajectory cheaper than `7π/2` has. |
| E21 | Nontriviality must be imposed on the reduced costate, or every trajectory is an extremal. |
| E32 | Theorem 7.7.1 is false read literally; it holds up to time translation. |
| E13, E34, E35 | Theorem 3.1.4(3), Lemma 3.1.8 and Filippov's theorem each lack a hypothesis (added with the user's approval). |
| E47 | The book identifies the control minimizers with Reinhardt's `K_min` without proof; proved here. |
| E55 | Theorem 8.2.7's proof covers only part of its statement. By the user's decision it is proved in the authors' reading; the printed form is proved for normal lifts and open for abnormal ones. |
| E56 | Theorem 8.3.1 is false as printed; by the user's decision it is proved in a one-sided form, which suffices for Theorem 8.3.2. |
| E95 | The Noether–Sussmann theorem as the book quotes it drops the invariance of the cost and is false (refuted in Lean); Theorem 9.1.6 needs only Sussmann's form, which is proved. |
| E65 | The proof of Lemma 13.3.2 assumes the maximizing face constant in time; repaired along its lines. |
| E68 | Lemma 13.5.5 (stability of `q_out`) rests on a Mathematica computation; proved here with an exact Jacobian and certified eigenvalue bounds. |
| E73, E75 | §15.3 uses `F⁻¹ = τFτ` where it fails (on the top faces of the cells), and Remark 15.3.1 swaps `q_in` and `q_out`. |
| E77–E79 | Theorem 16.1.1 rests on Mathematica containments, and two of its steps have gaps (convergence near `q_out`, the last row of its table); repaired, with the containments as three named facts, proved without computer assistance. |
| E85, E89–E91 | Lemma 14.3.1 skips a switching function and sketches its last step; §16.4.2's Reinhardt cells are asserted, and the proof of Theorem 16.4.1 turns a cluster point into a limit without justification; repaired (the forward invariance of the cluster set, a hyperbolic box). |
| E88, E93, E94 | Theorem 14.4.1 rests on an uncertified computation of a global unstable curve that Theorem 14.3.3 does not give, at a threshold where interval arithmetic has no margin, and on steps it does not cite; the computed fact and the uncited steps are proved. |

Every proof follows the book's argument; the departures, each forced, made where the book only
sketches, or, for the computed facts, by the user's decision, are listed in
[REPORT.md, Section 7](REPORT.md#7-departures-from-the-papers-proofs).

## Trust

- No `sorry` outside the statements of [`Challenge.lean`](Challenge.lean); no `axiom`, `native_decide` or `decide +kernel`.
- `lake env lean scripts/Audit.lean` checks, with `import all`, that every declaration (10,888) depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- A route check compares each proof with the results the book's proof cites; every difference is
  recorded in [`docs/route_differences.tsv`](docs/route_differences.tsv).
- Independent agents reviewed the statements against the TeX source and compared the proofs with
  the book's. No person has reviewed the proofs.

## Dependencies

- [OptimalControl](https://github.com/vltanh/lean4-optimal-control): Filippov's theorem (also under
  a state constraint), the Pontryagin maximum principle, by Agrachev and Sachkov's proof, and
  Sussmann's Noether theorem for optimal control.
- [FixedPoint](https://github.com/vltanh/lean4-fixed-point): Brouwer's fixed-point theorem, which
  the maximum principle needs.
- [StableManifold](https://github.com/vltanh/lean4-stable-manifold): the stable manifold theorem
  for maps (Lyapunov–Perron method, `Cⁿ` graphs, `n ≤ ∞`), which Appendix A.3 recalls from Irwin;
  Mahler's First uses it through Theorem 14.4.1. A shorter route that the proofs record but do not
  take would avoid it ([REPORT.md, Section 11](REPORT.md#11-simpler-arguments)).

OptimalControl (which requires FixedPoint) and StableManifold are required at pinned commits in
[`lakefile.toml`](lakefile.toml).

## Building

```sh
lake exe cache get                     # Mathlib's compiled files
lake build                             # the library, the Challenge and the Solution
lake env lean scripts/Audit.lean       # axioms
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
lake env lake comparator --config=comparator.json   # Palomar's Comparator (needs bubblewrap)
```

Lean and Mathlib `v4.36.0-rc2`.

## Layout

| Path | Content |
| --- | --- |
| [`SmoothedPolygons/`](SmoothedPolygons) | the book, one directory per chapter (`Ch2`–`Ch9`, `Ch13`–`Ch16`, `AppA`); the proof of N4 is `Ch14/Arc*` |
| [`External/`](External) | cited results, all proved ([External/README.md](External/README.md)) |
| [`Basic/`](Basic) | general mathematics written for this project ([Basic/README.md](Basic/README.md)) |
| [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean) | Palomar's statement of record and its proof |
| [`scripts/`](scripts), [`docs/`](docs) | the audit, the route check and its data; the details of REPORT.md in [`docs/report/`](docs/report) |
| [`numerics/`](numerics) | a Python reference for the computed facts (not used by the proofs) |
| [REPORT.md](REPORT.md), [CREDITS.md](CREDITS.md) | the audit of the book; how this was made |

## Related work

- Hales's 2017 preprint ([arXiv:1703.01352](https://arxiv.org/abs/1703.01352)) introduced the
  control formulation and sketched the octagon's isolation.
- M. Ho's independent Lean development
  ([sunfishho/reinhardt-density-bound](https://github.com/sunfishho/reinhardt-density-bound))
  formalizes parts of Chapters 2, 3 and 5; this work did not use it.
- More in [REPORT.md, Section 10](REPORT.md#10-the-paper-in-the-literature).

## Credits

- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code, with parallel sub-agents,
  at the request of The-Anh Vu-Le, who chose the scope and made the decisions recorded in REPORT.md,
  following the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill.
- Made on 5–15 November 2026; [CREDITS.md](CREDITS.md) has the procedure and figures.

## License

Apache-2.0; see [LICENSE](LICENSE).
