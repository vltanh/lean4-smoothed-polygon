# Smoothed polygons in the Reinhardt control problem, in Lean

[![Lean Action CI](https://github.com/vltanh/lean4-smoothed-polygon/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-smoothed-polygon/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of Thomas Hales and Koundinya Vajjha, *Packings of Smoothed Polygons*
([arXiv:2405.04331v1](https://arxiv.org/abs/2405.04331), 2024). The book recasts the Reinhardt
problem (which centrally symmetric convex disk packs least densely?) as an optimal control problem
on `SL₂(ℝ)` and studies its Pontryagin extremals.

Chapters 2–8, 13 and 15 are formalized: every numbered result is proved, some in corrected form
(see below), except two conjectural remarks, the Mathematica-based part of Remark 13.5.4 and
Proposition 15.3.2 (read off figures). The global basin theorem of the Fuller system (Theorem
16.1.1) and Theorem 16.2.1 are proved **conditionally**, on three named numerical facts that the
book reads off Mathematica plots. The book's main theorem, Mahler's First conjecture (Theorem
16.3.1), is proved **conditionally**, on one named hypothesis that stands for Theorems 16.4.1 and
14.4.1, not yet formalized. The Reinhardt conjecture itself (that the smoothed octagon is the
worst disk) is open and not claimed.

## Status

| Part of the book | Status |
| --- | --- |
| Ch. 2, historical results (packings, critical lattices, the minimizer's boundary) | proved |
| Ch. 3–4, the control problem and the upper half-plane | proved |
| Ch. 5, compactification of the star domain | proved |
| Ch. 6, Hamiltonians; existence of a minimizer (§6.1); every minimizer is an extremal (§6.2) | proved |
| Ch. 7, the smoothed `(6k+2)`-gons are extremals; the octagon is an isolated extremal | proved |
| Ch. 8, edge problems, singular locus, finite bang-bang | proved (two theorems restated, see below) |
| Ch. 13, the triangular Fuller system: blow-up, Poincaré map, fixed points `q_out`, `q_in` and their stability | proved |
| Ch. 15, the geometry of the Fuller–Poincaré map: cell coordinates, smaller cells, the involution `τF` | proved (Proposition 15.3.2 stated only) |
| §16.1–16.2, Theorems 16.1.1 (global basin) and 16.2.1 (outward Fuller trajectories) | **conditional** on three numerical facts (`DOutContracts`, `CellTwoEntersDOut`, `BoxSubclaims`) |
| Appendix A.1 (Corollary A.1.3), A.6, A.11 | proved |
| Theorem 16.3.1, Mahler's First conjecture | **conditional** on [`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107) |
| Ch. 9–12 (circular control, off the main path), Ch. 14, §16.4 | not yet formalized |

## Main results

| Result | Lean name | Statement |
| --- | --- | --- |
| Theorem 7.5.6 | [`SmoothedPolygonsChallenge.smoothed_polygon_extremal`](Challenge.lean#L335) | every smoothed `(6k+2)`-gon is a Pontryagin extremal with bang-bang control |
| Example before 7.5.6 | [`SmoothedPolygonsChallenge.smoothed_octagon_density`](Challenge.lean#L351) | the smoothed octagon's greatest packing density is `(8 - √32 - ln 2)/(√8 - 1) ≈ 0.902414` |
| Theorem 7.7.1 | [`theorem7_7_1`](SmoothedPolygons/Ch7/Isolated.lean#L508) | the octagon is an isolated extremal, up to time translation (E32) |
| §6.2, §6.6 | [`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L564) | every global minimizer lifts to a Pontryagin extremal |
| §6.1 and `K_min` | [`exists_isReinhardtMinimizer_isPontryaginExtremal_isWorstDisk`](SmoothedPolygons/Ch6/WorstDisk.lean#L250) | a global minimizer exists, is an extremal, and bounds a worst disk `K_min` |
| Theorem 8.3.2 with 8.1.3 | [`isFiniteBangBang_of_isReinhardtMinimizer_of_not_mem_singularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L165) | the minimizer is bang-bang with finitely many switches away from the singular locus |
| Lemma 13.5.5 | [`lemma13_5_5`](SmoothedPolygons/Ch13/Stability.lean#L281) | the fixed point `q_out` of the Fuller–Poincaré map (Lemma 13.5.2) is asymptotically stable, and `q_in = τ(q_out)` is unstable |
| Theorem 16.1.1 | [`theorem16_1_1`](SmoothedPolygons/Ch16/GlobalBasin.lean#L599) | **under three numerical facts**: every orbit of the Fuller–Poincaré map on `Ξ_{𝒲,0}/V_T` other than `q_in` tends to `q_out` |
| Theorem 16.3.1 | [`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343) | **under the hypothesis**: the minimizer is bang-bang with finitely many switches, and every `K_min` is a smoothed polygon |

The first two are the Palomar Challenge ([`Challenge.lean`](Challenge.lean)).

### The conditional results

Each hypothesis is part of a theorem's statement, not an axiom; nothing else assumes it, and the
audit lists it among the results that the theorem uses.

- [`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343) assumes [`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107): the switching times of an
  edge-extremal Pontryagin extremal do not accumulate where its lift meets the singular locus.
  Theorems 16.4.1 and 14.4.1 give this in the book's last step; Layers 6–7 are to prove it (E60).
- [`theorem16_1_1`](SmoothedPolygons/Ch16/GlobalBasin.lean#L599) and [`theorem16_2_1`](SmoothedPolygons/Ch16/OutwardFuller.lean#L567) assume three numerical facts
  ([`BasinHypotheses.lean`](SmoothedPolygons/Ch16/BasinHypotheses.lean)): the book's Table 16.1,
  read off Mathematica plots, restated on boxes. An independent check (about 1.1 million
  evaluations) found them true, with margins of at least 0.015; Layer 5b is to certify them.

| Fact | What it says |
| --- | --- |
| `DOutContracts` | the map sends the box `𝒟_out` into itself, and an iterate into a box where it contracts (the contraction is missing from the book, E78) |
| `CellTwoEntersDOut` | every point of the second big cell reaches `𝒟_out` within three steps |
| `BoxSubclaims` | every other box except `𝒟₂₂` goes to the second cell or to a smaller box |

Layers 6–7 will use Theorem 16.1.1, so Theorem 16.3.1 will rest on these facts until 5b is done.

## What the audit found

[REPORT.md](REPORT.md) checks the book against the formalization; 80 findings (E1–E80). The main
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
| E65 | The proof of Lemma 13.3.2 assumes the maximizing face constant in time; repaired along its lines. |
| E68 | Lemma 13.5.5 (stability of `q_out`) rests on a Mathematica computation; proved here with an exact Jacobian and certified eigenvalue bounds. |
| E73, E75 | §15.3 uses `F⁻¹ = τFτ` where it fails (on the top faces of the cells), and Remark 15.3.1 swaps `q_in` and `q_out`. |
| E77–E79 | Theorem 16.1.1 rests on Mathematica containments, and two of its steps have gaps (convergence near `q_out`, the last row of its table); repaired, with the containments as three named facts. |

Every proof follows the book's argument; the departures, each forced, are listed in
[REPORT.md, Section 7](REPORT.md#7-departures-from-the-papers-proofs).

## Trust

- No `sorry` outside the statements of [`Challenge.lean`](Challenge.lean); no `axiom`.
- `lake env lean scripts/Audit.lean` checks that every declaration depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- A route check compares each proof with the results the book's proof cites; every difference is
  recorded in [`docs/route_differences.tsv`](docs/route_differences.tsv).
- Independent agents reviewed the statements against the TeX source and compared the proofs with
  the book's. No person has reviewed the proofs.

## Dependencies

- [OptimalControl](https://github.com/vltanh/lean4-optimal-control): Filippov's theorem (also under
  a state constraint) and the Pontryagin maximum principle, by Agrachev and Sachkov's proof.
- [FixedPoint](https://github.com/vltanh/lean4-fixed-point): Brouwer's fixed-point theorem, which
  the maximum principle needs.

Both are required at pinned commits in [`lakefile.toml`](lakefile.toml).

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
| [`SmoothedPolygons/`](SmoothedPolygons) | the book, one directory per chapter (`Ch2`–`Ch8`, `Ch13`, `Ch15`, `Ch16`, `AppA`) |
| [`External/`](External) | cited results, all proved ([External/README.md](External/README.md)) |
| [`Basic/`](Basic) | general mathematics written for this project ([Basic/README.md](Basic/README.md)) |
| [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean) | Palomar's statement of record and its proof |
| [`scripts/`](scripts), [`docs/`](docs) | the audit, the route check and its data |
| [REPORT.md](REPORT.md), [CREDITS.md](CREDITS.md) | the audit of the book; how this was made |

## What's next

The plan's remaining layers are to certify the three numerical facts and to prove
[`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107) (details in [REPORT.md, Section 11](REPORT.md#11-whats-next)):

| Layer | Content | Status |
| --- | --- | --- |
| 5 | Ch. 15 and Theorems 16.1.1, 16.2.1, the global basin of the Fuller system, with its numerical facts as named hypotheses | done (conditional) |
| 5b | certify the three numerical facts and Proposition 15.3.2 by interval enclosures of the Fuller–Poincaré map | planned |
| 6 | Ch. 14 and Theorem 16.4.1, the cluster point theorem (stable manifolds, Weierstrass preparation) | planned |
| 7 | Theorem 14.4.1 (no return, an unstable curve to certify) and the final assembly | planned |

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
- Made on 5–14 November 2026 in eight rounds; [CREDITS.md](CREDITS.md) has the procedure and figures.

## License

Apache-2.0; see [LICENSE](LICENSE).
