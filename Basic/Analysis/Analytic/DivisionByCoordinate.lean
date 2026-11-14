module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Dividing an analytic function by a power of a coordinate

If `f : ℝ × E → F` is analytic at `(0, y₀)` and, for every `y` near `y₀`, `r ↦ f (r, y)` is
`O(r^k)` at `0`, then `f (r, y) = r^k g(r, y)` near `(0, y₀)` with `g` analytic at `(0, y₀)`
(the "division of power series" of Hales–Vajjha, *Packings of Smoothed Polygons*, proof of
Lemma 14.3.1, TeX 11800–11806: "By Lemma 14.2.4, by division of power series, the function
`χ₂₁(…)/r₀³` extends to an analytic function"; and TeX 11846–11848 for `X_sw - J` and
`Λ₁sw + (3/2) J`).

Mathlib has the identity theorem in several variables
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) and the analytic implicit function
theorem (`ContDiffAt.implicitFunction` with `n = ω`), but no division by a coordinate.
Weierstrass preparation exists in Mathlib only for formal power series over a complete local
ring (`Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean`), not for convergent ones;
this lemma is the only division the Chapter 14 proofs need.

## Proof (plan)

Expand `f` at `(0, y₀)` (`HasFPowerSeriesAt`); grouping the terms by their degree in `r` writes
`f (r, y) = Σ_j a_j(y) r^j` on a polydisc, with `a_j` analytic at `y₀` (the partial sums of a
convergent multilinear series; equivalently `a_j(y) = (1/j!) ∂_r^j f(0, y)`, and the iterated
derivatives of an analytic function are analytic, `AnalyticAt.iteratedFDeriv`). For each `y`
near `y₀` the one-variable function `r ↦ f (r, y)` is analytic at `0` and `O(r^k)`, so its
coefficients `a_j(y)`, `j < k`, vanish (`HasFPowerSeriesAt.eq_zero_of_isBigO`-type uniqueness, as
in `Mathlib/Analysis/Analytic/Uniqueness.lean`). Then `g (r, y) = Σ_{j ≥ k} a_j(y) r^{j-k}`
converges on the same polydisc (in the complete space `F`) and is analytic. Size: 400–800 lines.

Used by: the proof of `analyticAt_rescaledChi` (Step 3 of Lemma 14.3.1, `k = 3`, for `χ₂₁`) and
Step 7 of Lemma 14.3.1 (`k = 1, 2` for `X_sw - J`, `Λ₁sw + (3/2) J`), in
`SmoothedPolygons/Ch14/AnalyticExtension.lean`, which imports this file.
-/

@[expose] public section

open Filter Topology Asymptotics

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

/-- **Division by a power of a coordinate.** If `f : ℝ × E → F` (`F` complete) is analytic at
`(0, y₀)` and, for all `y` near `y₀`, `f (r, y) = O(r^k)` as `r → 0`, then
`f (r, y) = r^k • g (r, y)` near `(0, y₀)` for some `g` analytic at `(0, y₀)`. Completeness of
`F` is needed: the coefficient series `Σ_{j ≥ k} a_j(y) r^{j-k}` must converge in `F` (without
it the statement fails: `f(r, y) = Σ_{j≥1} r^j γ_j(y)`, `γ_j(y) = Σ_m y^m e_{jm}/m!`, with values
in the span `F ⊆ ℓ²(ℕ × ℕ)` of the `e_{jm}` and the values of `f`, is analytic and `O(r)`, but
`g(0, y) = γ₁(y) ∉ F` for `y ≠ 0`). All the uses are `ℝ`- or `ℂ³`-valued. -/
theorem AnalyticAt.exists_eq_pow_smul_of_isBigO {f : ℝ × E → F} {y₀ : E}
    (hf : AnalyticAt ℝ f ((0 : ℝ), y₀)) {k : ℕ}
    (hk : ∀ᶠ y in 𝓝 y₀, (fun r : ℝ ↦ f (r, y)) =O[𝓝 0] (fun r ↦ r ^ k)) :
    ∃ g : ℝ × E → F, AnalyticAt ℝ g ((0 : ℝ), y₀) ∧
      ∀ᶠ p in 𝓝 ((0 : ℝ), y₀), f p = p.1 ^ k • g p := by
  sorry
