module

public import SmoothedPolygons.Ch16.Certificates.ContractionBoxCheck
public import SmoothedPolygons.Ch15.CellCoordinates
public import Basic.Interval.ProgramEval
public import Basic.Interval.Lipschitz

/-!
# The contraction on `B`: a kernel-checked interval certificate

The contraction part of `DOutContracts` (`SmoothedPolygons/Ch16/BasinHypotheses.lean`) with the
recommended witnesses `B = [0.25, 0.29] × [0.15, 0.19] × [2.85, 2.98]` (cell coordinates
`(r₂, ψ, θ₂)`) and `κ = 1/2` (`contraction_on_B`, `contraction_part`): `B` lies in the open first
big cell, and on `B` the Fuller–Poincaré map `poincareAngZero` is, in coordinates, a map `g` of `B`
into itself that is `1/2`-Lipschitz in the sup metric.

## The map in coordinates

For `p ∈ B` the first control is `ζ` (`definition15_1_2`); along it, `ζ z(t) = (U_k + i V_k)_k`
with `U_k, V_k` polynomial in `t` and in `x₁ + i y₁ = (1 - r₂) e^{iφ₁}`, `x₂ + i y₂ = r₂ e^{iφ₂}`,
`κ = r₁ r₂ sin ψ` (`φ₁ = θ₂ - ψ + 2π/3`, `φ₂ = θ₂ + 2π/3`; `zeta_flow`). The control `1` beats `ζ`
exactly when `D = V₂ > 0` (`ham_one_sub_ham_ζ`, `D = -χ_A/√3`), and `ζ²` never does on `B`
(`Y₂ = Im z₃(t) > 0`, `ham_ζ_sq_sub_ham_ζ`). The first switch is the root `τ` of `D` in an
enclosure `[tl, th]` (`BoxFacts.firstSwitchTime_eq`); `ζ z(τ)` has `z₃` on the wall `𝒲₀`, and its
cell coordinates are `g p = (G₀, G₁, G₂)(p, τ)` with `G₀ = 4b/(a + √(a² + 4b))²` (the quadratic of
Lemma 15.1.1, rationalised), `G₁ = arctan (V₁/U₁) - arctan (V₀/U₀)`, `G₂ = arctan (V₁/U₁) + π`
(`BoxFacts.g_spec`; `g = cellCoords (ζ • F(cellPoint p))`).

## The certificate

The straight-line programs `progA`, `progB`, `progD` and the Bool-valued checks are in
`ContractionBoxData.lean`; the kernel evaluates them in `ContractionBoxCheck.lean`. Here:

* closed forms of the programs (`progA_steps`, `resA_vals`, `resB_vals`, `resD_eq`), by the
  one-step equations `getR_evalR_eq` (`Basic/Interval/ProgramEval.lean`);
* soundness of the box check (`boxFacts`): on each of the `3 × 3 × 6` boxes `B_k`, `D < 0` on
  `B_k × [0, tl]`, `D > 0` on `B_k × {th}`, the signs of `U₀, V₀, U₁, V₁, U₂, G₁` on
  `B_k × [tl, th]`, and enclosures of all the partial derivatives of `D, G₀, G₁, G₂` there, with
  `∂_t D > 0` and `|∂_j G_i - ∂_t G_i ∂_j D / ∂_t D| ≤ L_{ij}` for every choice of the four points
  (interval vector-mode differentiation along the curves `curveB`, `evalV_sound`,
  `passA_sound`, `passB_sound`);
* the entries of the Jacobian of `g`, without differentiating the root `τ`: the mean value theorem
  along `(p, τ p) → (q, τ p) → (q, τ q)` (`abs_sub_le_of_implicit`), glued along the grid in each
  coordinate (`abs_sub_le_of_grid`, `coord_lip`) and summed over the coordinates
  (`g_entry_bound`): `|g_i(q) - g_i(p)| ≤ Σ_j L_{ij} |q_j - p_j|` on `B`;
* `Σ_j L_{ij} ≤ 1/2` gives the Lipschitz bound (`lipschitzOnWith_g`), and an enclosure of `g(c)` at
  the center `c` with `g(c) ± Σ_j L_{ij} r_j ⊆ B` gives `g(B) ⊆ B` (`center_facts`, `mapsTo_g`).

`#print axioms contraction_on_B`: `propext`, `Classical.choice`, `Quot.sound`.
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.ContractionBox

open DyadicInterval Set
open Complex (I)

/-! ### The programs in closed form -/

theorem progA_wf : wf progA = true := by decide +kernel

theorem progB_wf : wf progB = true := by decide +kernel

theorem progD_wf : wf progD = true := by decide +kernel

/-- The one-step equations of `progA`. -/
theorem progA_steps (x : ℕ → ℝ) :
    getR (evalR x progA) 0 = x 0 ∧
    getR (evalR x progA) 1 = x 1 ∧
    getR (evalR x progA) 2 = x 2 ∧
    getR (evalR x progA) 3 = Real.pi ∧
    getR (evalR x progA) 4 = (((2 / 3) : ℚ) : ℝ) ∧
    getR (evalR x progA) 5 = getR (evalR x progA) 4 * getR (evalR x progA) 3 ∧
    getR (evalR x progA) 6 = getR (evalR x progA) 2 - getR (evalR x progA) 1 ∧
    getR (evalR x progA) 7 = getR (evalR x progA) 6 + getR (evalR x progA) 5 ∧
    getR (evalR x progA) 8 = getR (evalR x progA) 2 + getR (evalR x progA) 5 ∧
    getR (evalR x progA) 9 = Real.cos (getR (evalR x progA) 7) ∧
    getR (evalR x progA) 10 = Real.sin (getR (evalR x progA) 7) ∧
    getR (evalR x progA) 11 = Real.cos (getR (evalR x progA) 8) ∧
    getR (evalR x progA) 12 = Real.sin (getR (evalR x progA) 8) ∧
    getR (evalR x progA) 13 = Real.sin (getR (evalR x progA) 1) ∧
    getR (evalR x progA) 14 = ((1 : ℚ) : ℝ) ∧
    getR (evalR x progA) 15 = getR (evalR x progA) 14 - getR (evalR x progA) 0 ∧
    getR (evalR x progA) 16 = getR (evalR x progA) 15 * getR (evalR x progA) 9 ∧
    getR (evalR x progA) 17 = getR (evalR x progA) 15 * getR (evalR x progA) 10 ∧
    getR (evalR x progA) 18 = getR (evalR x progA) 0 * getR (evalR x progA) 11 ∧
    getR (evalR x progA) 19 = getR (evalR x progA) 0 * getR (evalR x progA) 12 ∧
    getR (evalR x progA) 20 = getR (evalR x progA) 15 * getR (evalR x progA) 0 ∧
    getR (evalR x progA) 21 = getR (evalR x progA) 20 * getR (evalR x progA) 13 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (getR_evalR_eq x progA_wf (i := 0) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 1) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 2) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 3) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 4) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 5) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 6) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 7) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 8) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 9) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 10) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 11) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 12) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 13) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 14) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 15) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 16) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 17) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 18) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 19) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 20) rfl).trans rfl
  · exact (getR_evalR_eq x progA_wf (i := 21) rfl).trans rfl

/-- The one-step equations of `progB`. -/
theorem progB_steps (x : ℕ → ℝ) :
    getR (evalR x progB) 0 = x 0 ∧
    getR (evalR x progB) 1 = x 1 ∧
    getR (evalR x progB) 2 = x 2 ∧
    getR (evalR x progB) 3 = x 3 ∧
    getR (evalR x progB) 4 = x 4 ∧
    getR (evalR x progB) 5 = x 5 ∧
    getR (evalR x progB) 6 = ((3 : ℚ) : ℝ) ∧
    getR (evalR x progB) 7 = Real.sqrt (getR (evalR x progB) 6) ∧
    getR (evalR x progB) 8 = getR (evalR x progB) 5 ^ 2 ∧
    getR (evalR x progB) 9 = getR (evalR x progB) 8 * getR (evalR x progB) 5 ∧
    getR (evalR x progB) 10 = getR (evalR x progB) 7 * getR (evalR x progB) 5 ∧
    getR (evalR x progB) 11 = (((1 / 2) : ℚ) : ℝ) ∧
    getR (evalR x progB) 12 = getR (evalR x progB) 11 * getR (evalR x progB) 10 ∧
    getR (evalR x progB) 13 = getR (evalR x progB) 0 - getR (evalR x progB) 12 ∧
    getR (evalR x progB) 14 = getR (evalR x progB) 11 * getR (evalR x progB) 5 ∧
    getR (evalR x progB) 15 = getR (evalR x progB) 1 + getR (evalR x progB) 14 ∧
    getR (evalR x progB) 16 = getR (evalR x progB) 0 * getR (evalR x progB) 5 ∧
    getR (evalR x progB) 17 = getR (evalR x progB) 1 * getR (evalR x progB) 5 ∧
    getR (evalR x progB) 18 = getR (evalR x progB) 7 * getR (evalR x progB) 8 ∧
    getR (evalR x progB) 19 = (((1 / 4) : ℚ) : ℝ) ∧
    getR (evalR x progB) 20 = getR (evalR x progB) 19 * getR (evalR x progB) 18 ∧
    getR (evalR x progB) 21 = getR (evalR x progB) 2 + getR (evalR x progB) 16 ∧
    getR (evalR x progB) 22 = getR (evalR x progB) 21 - getR (evalR x progB) 20 ∧
    getR (evalR x progB) 23 = getR (evalR x progB) 19 * getR (evalR x progB) 8 ∧
    getR (evalR x progB) 24 = getR (evalR x progB) 3 + getR (evalR x progB) 17 ∧
    getR (evalR x progB) 25 = getR (evalR x progB) 24 + getR (evalR x progB) 23 ∧
    getR (evalR x progB) 26 = getR (evalR x progB) 2 * getR (evalR x progB) 5 ∧
    getR (evalR x progB) 27 = getR (evalR x progB) 3 * getR (evalR x progB) 5 ∧
    getR (evalR x progB) 28 = getR (evalR x progB) 11 * getR (evalR x progB) 8 ∧
    getR (evalR x progB) 29 = getR (evalR x progB) 0 * getR (evalR x progB) 28 ∧
    getR (evalR x progB) 30 = getR (evalR x progB) 1 * getR (evalR x progB) 28 ∧
    getR (evalR x progB) 31 = getR (evalR x progB) 7 * getR (evalR x progB) 9 ∧
    getR (evalR x progB) 32 = (((1 / 12) : ℚ) : ℝ) ∧
    getR (evalR x progB) 33 = getR (evalR x progB) 32 * getR (evalR x progB) 31 ∧
    getR (evalR x progB) 34 = getR (evalR x progB) 32 * getR (evalR x progB) 9 ∧
    getR (evalR x progB) 35 = getR (evalR x progB) 4 + getR (evalR x progB) 26 ∧
    getR (evalR x progB) 36 = getR (evalR x progB) 35 + getR (evalR x progB) 29 ∧
    getR (evalR x progB) 37 = getR (evalR x progB) 36 - getR (evalR x progB) 33 ∧
    getR (evalR x progB) 38 = getR (evalR x progB) 7 * getR (evalR x progB) 4 ∧
    getR (evalR x progB) 39 = getR (evalR x progB) 27 - getR (evalR x progB) 38 ∧
    getR (evalR x progB) 40 = getR (evalR x progB) 39 + getR (evalR x progB) 30 ∧
    getR (evalR x progB) 41 = getR (evalR x progB) 40 + getR (evalR x progB) 34 ∧
    getR (evalR x progB) 42 = getR (evalR x progB) 13 ^ 2 ∧
    getR (evalR x progB) 43 = getR (evalR x progB) 15 ^ 2 ∧
    getR (evalR x progB) 44 = getR (evalR x progB) 42 + getR (evalR x progB) 43 ∧
    getR (evalR x progB) 45 = Real.sqrt (getR (evalR x progB) 44) ∧
    getR (evalR x progB) 46 = getR (evalR x progB) 22 ^ 2 ∧
    getR (evalR x progB) 47 = getR (evalR x progB) 25 ^ 2 ∧
    getR (evalR x progB) 48 = getR (evalR x progB) 46 + getR (evalR x progB) 47 ∧
    getR (evalR x progB) 49 = Real.sqrt (getR (evalR x progB) 48) ∧
    getR (evalR x progB) 50 = ((4 : ℚ) : ℝ) ∧
    getR (evalR x progB) 51 = getR (evalR x progB) 50 * getR (evalR x progB) 49 ∧
    getR (evalR x progB) 52 = getR (evalR x progB) 44 + getR (evalR x progB) 51 ∧
    getR (evalR x progB) 53 = Real.sqrt (getR (evalR x progB) 52) ∧
    getR (evalR x progB) 54 = getR (evalR x progB) 45 + getR (evalR x progB) 53 ∧
    getR (evalR x progB) 55 = getR (evalR x progB) 54 ^ 2 ∧
    getR (evalR x progB) 56 = getR (evalR x progB) 51 / getR (evalR x progB) 55 ∧
    getR (evalR x progB) 57 = getR (evalR x progB) 25 / getR (evalR x progB) 22 ∧
    getR (evalR x progB) 58 = Real.arctan (getR (evalR x progB) 57) ∧
    getR (evalR x progB) 59 = getR (evalR x progB) 15 / getR (evalR x progB) 13 ∧
    getR (evalR x progB) 60 = Real.arctan (getR (evalR x progB) 59) ∧
    getR (evalR x progB) 61 = getR (evalR x progB) 58 - getR (evalR x progB) 60 ∧
    getR (evalR x progB) 62 = Real.pi ∧
    getR (evalR x progB) 63 = getR (evalR x progB) 58 + getR (evalR x progB) 62 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (getR_evalR_eq x progB_wf (i := 0) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 1) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 2) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 3) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 4) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 5) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 6) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 7) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 8) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 9) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 10) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 11) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 12) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 13) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 14) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 15) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 16) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 17) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 18) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 19) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 20) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 21) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 22) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 23) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 24) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 25) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 26) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 27) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 28) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 29) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 30) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 31) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 32) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 33) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 34) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 35) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 36) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 37) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 38) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 39) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 40) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 41) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 42) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 43) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 44) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 45) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 46) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 47) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 48) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 49) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 50) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 51) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 52) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 53) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 54) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 55) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 56) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 57) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 58) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 59) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 60) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 61) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 62) rfl).trans rfl
  · exact (getR_evalR_eq x progB_wf (i := 63) rfl).trans rfl

/-- The one-step equations of `progD`. -/
theorem progD_steps (x : ℕ → ℝ) :
    getR (evalR x progD) 0 = x 0 ∧
    getR (evalR x progD) 1 = x 1 ∧
    getR (evalR x progD) 2 = x 2 ∧
    getR (evalR x progD) 3 = x 3 ∧
    getR (evalR x progD) 4 = x 4 ∧
    getR (evalR x progD) 5 = x 5 ∧
    getR (evalR x progD) 6 = ((3 : ℚ) : ℝ) ∧
    getR (evalR x progD) 7 = Real.sqrt (getR (evalR x progD) 6) ∧
    getR (evalR x progD) 8 = getR (evalR x progD) 7 * getR (evalR x progD) 4 ∧
    getR (evalR x progD) 9 = (((1 / 12) : ℚ) : ℝ) ∧
    getR (evalR x progD) 10 = getR (evalR x progD) 9 * getR (evalR x progD) 5 ∧
    getR (evalR x progD) 11 = (((1 / 2) : ℚ) : ℝ) ∧
    getR (evalR x progD) 12 = getR (evalR x progD) 11 * getR (evalR x progD) 1 ∧
    getR (evalR x progD) 13 = getR (evalR x progD) 12 + getR (evalR x progD) 10 ∧
    getR (evalR x progD) 14 = getR (evalR x progD) 13 * getR (evalR x progD) 5 ∧
    getR (evalR x progD) 15 = getR (evalR x progD) 3 + getR (evalR x progD) 14 ∧
    getR (evalR x progD) 16 = getR (evalR x progD) 15 * getR (evalR x progD) 5 ∧
    getR (evalR x progD) 17 = getR (evalR x progD) 16 - getR (evalR x progD) 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (getR_evalR_eq x progD_wf (i := 0) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 1) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 2) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 3) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 4) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 5) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 6) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 7) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 8) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 9) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 10) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 11) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 12) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 13) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 14) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 15) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 16) rfl).trans rfl
  · exact (getR_evalR_eq x progD_wf (i := 17) rfl).trans rfl

/-- The inputs of `progA`: the cell coordinates `(r₂, ψ, θ₂)`. -/
noncomputable def inA (p : Fin 3 → ℝ) : ℕ → ℝ := fun k ↦ if h : k < 3 then p ⟨k, h⟩ else 0

/-- The results of `progA`. -/
noncomputable def resA (p : Fin 3 → ℝ) : List ℝ := evalR (inA p) progA

/-- `x₁ = r₁ cos φ₁`, with `r₁ = 1 - r₂` and `φ₁ = θ₂ - ψ + 2π/3`. -/
noncomputable def cx₁ (p : Fin 3 → ℝ) : ℝ := (1 - p 0) * Real.cos (p 2 - p 1 + 2 / 3 * Real.pi)

/-- `y₁ = r₁ sin φ₁`. -/
noncomputable def cy₁ (p : Fin 3 → ℝ) : ℝ := (1 - p 0) * Real.sin (p 2 - p 1 + 2 / 3 * Real.pi)

/-- `x₂ = r₂ cos φ₂`, `φ₂ = θ₂ + 2π/3`. -/
noncomputable def cx₂ (p : Fin 3 → ℝ) : ℝ := p 0 * Real.cos (p 2 + 2 / 3 * Real.pi)

/-- `y₂ = r₂ sin φ₂`. -/
noncomputable def cy₂ (p : Fin 3 → ℝ) : ℝ := p 0 * Real.sin (p 2 + 2 / 3 * Real.pi)

/-- `κ = r₁ r₂ sin ψ`. -/
noncomputable def cκ (p : Fin 3 → ℝ) : ℝ := (1 - p 0) * p 0 * Real.sin (p 1)

theorem resA_vals (p : Fin 3 → ℝ) :
    getR (resA p) 16 = cx₁ p ∧ getR (resA p) 17 = cy₁ p ∧ getR (resA p) 18 = cx₂ p ∧
      getR (resA p) 19 = cy₂ p ∧ getR (resA p) 21 = cκ p := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := progA_steps (inA p)
  have h0 : inA p 0 = p 0 := rfl
  have h1 : inA p 1 = p 1 := rfl
  have h2 : inA p 2 = p 2 := rfl
  simp only [resA]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [a16, a15, a14, a9, a7, a6, a5, a4, a3, a2, a1, a0, h0, h1, h2, cx₁]; push_cast; ring_nf
  · rw [a17, a15, a14, a10, a7, a6, a5, a4, a3, a2, a1, a0, h0, h1, h2, cy₁]; push_cast; ring_nf
  · rw [a18, a11, a8, a5, a4, a3, a2, a0, h0, h2, cx₂]; push_cast; ring_nf
  · rw [a19, a12, a8, a5, a4, a3, a2, a0, h0, h2, cy₂]; push_cast; ring_nf
  · rw [a21, a20, a15, a14, a13, a1, a0, h0, h1, cκ]; push_cast; ring_nf

/-- The inputs of `progB`: `(x₁, y₁, x₂, y₂, κ)` from `progA`, and the time `t`. -/
noncomputable def inB (p : Fin 3 → ℝ) (t : ℝ) : ℕ → ℝ := fun k ↦
  if k < 5 then getR (resA p) (aOut.getD k 0) else if k = 5 then t else 0

theorem inB_vals (p : Fin 3 → ℝ) (t : ℝ) :
    inB p t 0 = cx₁ p ∧ inB p t 1 = cy₁ p ∧ inB p t 2 = cx₂ p ∧ inB p t 3 = cy₂ p ∧
      inB p t 4 = cκ p ∧ inB p t 5 = t := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := resA_vals p
  exact ⟨e1, e2, e3, e4, e5, rfl⟩

/-- The results of `progB`. -/
noncomputable def resB (p : Fin 3 → ℝ) (t : ℝ) : List ℝ := evalR (inB p t) progB

/-- `U₀ = x₁ - √3 t/2` (`Re (ζ z₁(t))`). -/
noncomputable def U₀ (p : Fin 3 → ℝ) (t : ℝ) : ℝ := cx₁ p - √3 / 2 * t

/-- `V₀ = y₁ + t/2`. -/
noncomputable def V₀ (p : Fin 3 → ℝ) (t : ℝ) : ℝ := cy₁ p + t / 2

/-- `U₁ = x₂ + x₁ t - √3 t²/4`. -/
noncomputable def U₁ (p : Fin 3 → ℝ) (t : ℝ) : ℝ := cx₂ p + cx₁ p * t - √3 / 4 * t ^ 2

/-- `V₁ = y₂ + y₁ t + t²/4`. -/
noncomputable def V₁ (p : Fin 3 → ℝ) (t : ℝ) : ℝ := cy₂ p + cy₁ p * t + t ^ 2 / 4

/-- `U₂ = κ + x₂ t + x₁ t²/2 - √3 t³/12`. -/
noncomputable def U₂ (p : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  cκ p + cx₂ p * t + cx₁ p * t ^ 2 / 2 - √3 / 12 * t ^ 3

/-- `V₂ = -√3 κ + y₂ t + y₁ t²/2 + t³/12`: the switching function `D`. -/
noncomputable def V₂ (p : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  -(√3 * cκ p) + cy₂ p * t + cy₁ p * t ^ 2 / 2 + t ^ 3 / 12

theorem resB_vals (p : Fin 3 → ℝ) (t : ℝ) :
    getR (resB p t) 13 = U₀ p t ∧ getR (resB p t) 15 = V₀ p t ∧
      getR (resB p t) 22 = U₁ p t ∧ getR (resB p t) 25 = V₁ p t ∧
      getR (resB p t) 37 = U₂ p t ∧ getR (resB p t) 41 = V₂ p t ∧
      getR (resB p t) 44 = U₀ p t ^ 2 + V₀ p t ^ 2 ∧
      getR (resB p t) 45 = √(U₀ p t ^ 2 + V₀ p t ^ 2) ∧
      getR (resB p t) 49 = √(U₁ p t ^ 2 + V₁ p t ^ 2) ∧
      getR (resB p t) 56 = 4 * √(U₁ p t ^ 2 + V₁ p t ^ 2) /
        (√(U₀ p t ^ 2 + V₀ p t ^ 2) +
          √(U₀ p t ^ 2 + V₀ p t ^ 2 + 4 * √(U₁ p t ^ 2 + V₁ p t ^ 2))) ^ 2 ∧
      getR (resB p t) 58 = Real.arctan (V₁ p t / U₁ p t) ∧
      getR (resB p t) 61 = Real.arctan (V₁ p t / U₁ p t) - Real.arctan (V₀ p t / U₀ p t) ∧
      getR (resB p t) 63 = Real.arctan (V₁ p t / U₁ p t) + Real.pi := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18,
    b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36,
    b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54,
    b55, b56, b57, b58, b59, b60, b61, b62, b63⟩ := progB_steps (inB p t)
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := inB_vals p t
  simp only [resB]
  have hU₀ : getR (evalR (inB p t) progB) 13 = U₀ p t := by
    rw [b13, b12, b11, b10, b7, b6, b5, b0, i0, i5, U₀]; push_cast; ring
  have hV₀ : getR (evalR (inB p t) progB) 15 = V₀ p t := by
    rw [b15, b14, b11, b5, b1, i1, i5, V₀]; push_cast; ring
  have hU₁ : getR (evalR (inB p t) progB) 22 = U₁ p t := by
    rw [b22, b21, b20, b19, b18, b16, b8, b7, b6, b5, b2, b0, i0, i2, i5, U₁]; push_cast; ring
  have hV₁ : getR (evalR (inB p t) progB) 25 = V₁ p t := by
    rw [b25, b24, b23, b19, b17, b8, b5, b3, b1, i1, i3, i5, V₁]; push_cast; ring
  have hU₂ : getR (evalR (inB p t) progB) 37 = U₂ p t := by
    rw [b37, b36, b35, b33, b32, b31, b29, b28, b26, b11, b9, b8, b7, b6, b5, b4, b2, b0, i0,
      i2, i4, i5, U₂]
    push_cast; ring
  have hV₂ : getR (evalR (inB p t) progB) 41 = V₂ p t := by
    rw [b41, b40, b39, b38, b34, b32, b30, b28, b27, b11, b9, b8, b7, b6, b5, b4, b3, b1, i1,
      i3, i4, i5, V₂]
    push_cast; ring
  have h44 : getR (evalR (inB p t) progB) 44 = U₀ p t ^ 2 + V₀ p t ^ 2 := by
    rw [b44, b43, b42, hU₀, hV₀]
  have h45 : getR (evalR (inB p t) progB) 45 = √(U₀ p t ^ 2 + V₀ p t ^ 2) := by
    rw [b45, h44]
  have h49 : getR (evalR (inB p t) progB) 49 = √(U₁ p t ^ 2 + V₁ p t ^ 2) := by
    rw [b49, b48, b47, b46, hU₁, hV₁]
  have h58 : getR (evalR (inB p t) progB) 58 = Real.arctan (V₁ p t / U₁ p t) := by
    rw [b58, b57, hU₁, hV₁]
  refine ⟨hU₀, hV₀, hU₁, hV₁, hU₂, hV₂, h44, h45, h49, ?_, h58, ?_, ?_⟩
  · rw [b56, b55, b54, b53, b52, b51, b50, h44, h45, h49]; push_cast; ring
  · rw [b61, h58, b60, b59, hU₀, hV₀]
  · rw [b63, h58, b62]

/-- The results of `progD`: `D = V₂`. -/
theorem resD_eq (p : Fin 3 → ℝ) (t : ℝ) : getR (evalR (inB p t) progD) 17 = V₂ p t := by
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17⟩ :=
    progD_steps (inB p t)
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := inB_vals p t
  rw [d17, d16, d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d1, i1, i3, i4, i5, V₂]
  push_cast; ring

/-! ### The Fuller flow along the control `ζ`, rotated by `ζ` -/

theorem cos_two_thirds_pi : Real.cos (2 / 3 * Real.pi) = -1 / 2 := by
  rw [show 2 / 3 * Real.pi = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

theorem sin_two_thirds_pi : Real.sin (2 / 3 * Real.pi) = √3 / 2 := by
  rw [show 2 / 3 * Real.pi = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]

theorem cellPoint_reim (p : Fin 3 → ℝ) :
    (cellPoint p 0).re = (1 - p 0) * Real.cos (p 2 - p 1) ∧
    (cellPoint p 0).im = (1 - p 0) * Real.sin (p 2 - p 1) ∧
    (cellPoint p 1).re = p 0 * Real.cos (p 2) ∧
    (cellPoint p 1).im = p 0 * Real.sin (p 2) ∧
    (cellPoint p 2).re = -2 * (1 - p 0) * p 0 * Real.sin (p 1) ∧
    (cellPoint p 2).im = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cellPoint, Matrix.cons_val_zero, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  · simp only [cellPoint, Matrix.cons_val_zero, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  · simp only [cellPoint, Matrix.cons_val_one, Matrix.cons_val_zero, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
  · simp only [cellPoint, Matrix.cons_val_one, Matrix.cons_val_zero, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_im]
  · exact Complex.ofReal_re _
  · exact Complex.ofReal_im _

theorem zeta_flow (p : Fin 3 → ℝ) (t : ℝ) :
    (ζ * flow t (cellPoint p) ζ 0).re = U₀ p t ∧ (ζ * flow t (cellPoint p) ζ 0).im = V₀ p t ∧
    (ζ * flow t (cellPoint p) ζ 1).re = U₁ p t ∧ (ζ * flow t (cellPoint p) ζ 1).im = V₁ p t ∧
    (ζ * flow t (cellPoint p) ζ 2).re = U₂ p t ∧ (ζ * flow t (cellPoint p) ζ 2).im = V₂ p t := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := cellPoint_reim p
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e1 : Real.cos (p 2 - p 1 + 2 / 3 * Real.pi) =
      Real.cos (p 2 - p 1) * (-1 / 2) - Real.sin (p 2 - p 1) * (√3 / 2) := by
    rw [Real.cos_add, cos_two_thirds_pi, sin_two_thirds_pi]
  have e2 : Real.sin (p 2 - p 1 + 2 / 3 * Real.pi) =
      Real.sin (p 2 - p 1) * (-1 / 2) + Real.cos (p 2 - p 1) * (√3 / 2) := by
    rw [Real.sin_add, cos_two_thirds_pi, sin_two_thirds_pi]
  have e3 : Real.cos (p 2 + 2 / 3 * Real.pi) =
      Real.cos (p 2) * (-1 / 2) - Real.sin (p 2) * (√3 / 2) := by
    rw [Real.cos_add, cos_two_thirds_pi, sin_two_thirds_pi]
  have e4 : Real.sin (p 2 + 2 / 3 * Real.pi) =
      Real.sin (p 2) * (-1 / 2) + Real.cos (p 2) * (√3 / 2) := by
    rw [Real.sin_add, cos_two_thirds_pi, sin_two_thirds_pi]
  have f0 : flow t (cellPoint p) ζ 0 = cellPoint p 0 - I * t * ζ := rfl
  have f1 : flow t (cellPoint p) ζ 1 = cellPoint p 1 + cellPoint p 0 * t - I * t ^ 2 * ζ / 2 := rfl
  have f2 : flow t (cellPoint p) ζ 2 =
      cellPoint p 2 + cellPoint p 1 * t + cellPoint p 0 * t ^ 2 / 2 - I * t ^ 3 * ζ / 6 := rfl
  rw [f0, f1, f2]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, ζ_re, ζ_im, c0, c1, c2, c3, c4, c5, U₀, V₀, U₁, V₁, U₂,
    V₂, cx₁, cy₁, cx₂, cy₂, cκ, e1, e2, e3, e4]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals norm_num
  all_goals ring_nf
  all_goals (try simp only [hs3])
  all_goals ring_nf

/-- The imaginary part `Y₂ = r₂ sin θ₂ t + r₁ sin θ₁ t²/2 + t³/12` of `z₃(t)`. -/
theorem flow_two_im (p : Fin 3 → ℝ) (t : ℝ) :
    (flow t (cellPoint p) ζ 2).im = p 0 * Real.sin (p 2) * t +
      (1 - p 0) * Real.sin (p 2 - p 1) * t ^ 2 / 2 + t ^ 3 / 12 := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := cellPoint_reim p
  have f2 : flow t (cellPoint p) ζ 2 =
      cellPoint p 2 + cellPoint p 1 * t + cellPoint p 0 * t ^ 2 / 2 - Complex.I * t ^ 3 * ζ / 6 :=
    rfl
  rw [f2]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, Complex.sub_im, Complex.add_im,
    Complex.div_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, ζ_re, ζ_im, c0, c1, c2, c3, c5]
  norm_num
  ring

/-- The Hamiltonian gain of the control `1` over `ζ` along the control `ζ`:
`H_F(z(t), 1) - H_F(z(t), ζ) = √3 V₂`. -/
theorem ham_one_sub_ham_ζ (p : Fin 3 → ℝ) (t : ℝ) :
    ham (flow t (cellPoint p) ζ) 1 - ham (flow t (cellPoint p) ζ) ζ = √3 * V₂ p t := by
  obtain ⟨-, -, -, -, -, h⟩ := zeta_flow p t
  rw [← h]
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [ham, RR_eq_re_mul_add_im_mul, Complex.mul_im, ζ_re, ζ_im, Complex.one_re,
    Complex.one_im]
  ring_nf
  rw [hs3]
  ring

/-- The gain of `ζ²` over `ζ`: `H_F(z(t), ζ²) - H_F(z(t), ζ) = -√3 Y₂`. -/
theorem ham_ζ_sq_sub_ham_ζ (p : Fin 3 → ℝ) (t : ℝ) :
    ham (flow t (cellPoint p) ζ) (ζ ^ 2) - ham (flow t (cellPoint p) ζ) ζ =
      -(√3 * (flow t (cellPoint p) ζ 2).im) := by
  simp only [ham, RR_eq_re_mul_add_im_mul, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im]
  ring

/-! ### Enclosures of the inputs -/

/-- The real box with index `m`. -/
def cellSet (m : Fin 3 → ℕ) : Set (Fin 3 → ℝ) :=
  {p | ∀ i : Fin 3, (gridPt i (m i) : ℝ) ≤ p i ∧ p i ≤ gridPt i (m i + 1)}

theorem mem_ival {a b : ℚ} {x : ℝ} (h1 : (a : ℝ) ≤ x) (h2 : x ≤ b) : Mem prec (ival a b) x :=
  ⟨(mem_ofRat prec a).1.trans h1, h2.trans (mem_ofRat prec b).2⟩

theorem boxEnv_encl {m : Fin 3 → ℕ} {p : Fin 3 → ℝ} (hp : p ∈ cellSet m) :
    ∀ k, Mem prec (nth (boxEnv (m 0) (m 1) (m 2)) k zero) (inA p k) := by
  intro k
  rcases k with _ | _ | _ | k
  · exact mem_ival (hp 0).1 (hp 0).2
  · exact mem_ival (hp 1).1 (hp 1).2
  · exact mem_ival (hp 2).1 (hp 2).2
  · have : inA p (k + 3) = 0 := by simp [inA]
    rw [this]; exact mem_zero prec

/-- The inputs of `progB` are enclosed by `envB`. -/
theorem envB_encl {va : ℕ → DyadicInterval} {p : Fin 3 → ℝ}
    (hva : ∀ i < 22, Mem prec (va i) (getR (resA p) i)) {T : DyadicInterval} {t : ℝ}
    (ht : Mem prec T t) : ∀ k, Mem prec (nth (envB va T) k zero) (inB p t k) := by
  intro k
  rcases k with _ | _ | _ | _ | _ | _ | k
  · exact hva 16 (by norm_num)
  · exact hva 17 (by norm_num)
  · exact hva 18 (by norm_num)
  · exact hva 19 (by norm_num)
  · exact hva 21 (by norm_num)
  · exact ht
  · have : inB p t (k + 6) = 0 := by simp [inB]
    rw [this]; exact mem_zero prec

theorem wf_progA : wfFrom 0 progA = true := by decide +kernel

theorem wf_progB : wfFrom 0 progB = true := by decide +kernel

theorem wf_progD : wfFrom 0 progD = true := by decide +kernel

theorem inA_update (p : Fin 3 → ℝ) (j : Fin 3) (s : ℝ) :
    inA (Function.update p j s) = Function.update (inA p) j s := by
  funext k
  unfold inA
  by_cases hk : k < 3
  · rw [dite_eq_left hk]
    by_cases hkj : k = j
    · subst hkj
      simp [Function.update]
    · have : (⟨k, hk⟩ : Fin 3) ≠ j := fun h ↦ hkj (by rw [← h])
      rw [Function.update_of_ne this, Function.update_of_ne hkj, dite_eq_left hk]
  · have hkj : k ≠ j := fun h ↦ hk (h ▸ j.2)
    rw [dite_eq_right hk, Function.update_of_ne hkj, dite_eq_right hk]

theorem inB_update (p : Fin 3 → ℝ) (t s : ℝ) : Function.update (inB p t) 5 s = inB p s := by
  funext k
  by_cases hk : k = 5
  · subst hk; simp [inB]
  · rw [Function.update_of_ne hk]
    simp [inB, hk]

/-- **The results of `progA` on a box**, with their derivatives in the cell coordinates
(`hasDerivAt_update_of_evalV`). -/
theorem passA_sound {m : Fin 3 → ℕ} {p : Fin 3 → ℝ} (hp : p ∈ cellSet m)
    (hok : (passA (boxEnv (m 0) (m 1) (m 2))).2 = true) {i : ℕ} (hi : i < 22) :
    Mem prec (resA' (passA (boxEnv (m 0) (m 1) (m 2))).1 i).1 (getR (resA p) i) ∧
      (resA' (passA (boxEnv (m 0) (m 1) (m 2))).1 i).2.length = 3 ∧
      ∀ j : Fin 3, ∃ d, HasDerivAt (fun s ↦ getR (resA (Function.update p j s)) i) d (p j) ∧
        Mem prec (nth (resA' (passA (boxEnv (m 0) (m 1) (m 2))).1 i).2 j zero) d := by
  obtain ⟨h1, h2, h3⟩ := hasDerivAt_update_of_evalV (x := inA p) (le_refl 3) (boxEnv_encl hp)
    wf_progA hok i hi
  refine ⟨h1, h2, fun j ↦ ?_⟩
  obtain ⟨d, hd, hm⟩ := h3 j j.2
  refine ⟨d, ?_, hm⟩
  have e : inA p j = p j := by simp [inA]
  rw [e] at hd
  simpa only [resA, inA_update] using hd

/-- The facts on the results of `progA` used by `progB`. -/
def AFacts (p : Fin 3 → ℝ) (RA : List DualV) : Prop :=
  ∀ i < 22, Mem prec (resA' RA i).1 (getR (resA p) i) ∧ (resA' RA i).2.length = 3 ∧
    ∀ j : Fin 3, ∃ d, HasDerivAt (fun s ↦ getR (resA (Function.update p j s)) i) d (p j) ∧
      Mem prec (nth (resA' RA i).2 j zero) d

theorem nth_append_lt {α : Type*} {l : List α} {i : ℕ} (h : i < l.length) (l' : List α) (d : α) :
    nth (l ++ l') i d = nth l i d := by
  induction l generalizing i with
  | nil => simp at h
  | cons b l ih => cases i <;> simp_all [nth]

theorem nth_append_length {α : Type*} (l : List α) (a : α) (d : α) :
    nth (l ++ [a]) l.length d = a := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa [nth] using ih

/-- The curves of the inputs of `progB`: `j < 3`, the cell coordinate `j` moves; `j = 3`, the
time. -/
noncomputable def curveB (p : Fin 3 → ℝ) (t : ℝ) (j : ℕ) (s : ℝ) : ℕ → ℝ :=
  if h : j < 3 then inB (Function.update p ⟨j, h⟩ s) t else inB p s

/-- The base points of the curves. -/
noncomputable def baseB (p : Fin 3 → ℝ) (t : ℝ) (j : ℕ) : ℝ := if h : j < 3 then p ⟨j, h⟩ else t

theorem denvB_eq (RA : List DualV) : denvB RA = [(resA' RA 16).2 ++ [zero],
    (resA' RA 17).2 ++ [zero], (resA' RA 18).2 ++ [zero], (resA' RA 19).2 ++ [zero],
    (resA' RA 21).2 ++ [zero], [zero, zero, zero, one prec]] := rfl

/-- The derivatives of the inputs of `progB` along the four curves, enclosed by `denvB`. -/
theorem exists_derivB {p : Fin 3 → ℝ} {RA : List DualV} (hRA : AFacts p RA) (t : ℝ) (j k : ℕ) :
    ∃ d : ℝ, j < 4 → HasDerivAt (fun s ↦ curveB p t j s k) d (baseB p t j) ∧
      Mem prec (nth (nth (denvB RA) k (zeros 4)) j zero) d := by
  -- the inputs `k < 5`: results of `progA`
  have hA : ∀ k i, k < 5 → aOut.getD k 0 = i → i < 22 →
      nth (denvB RA) k (zeros 4) = (resA' RA i).2 ++ [zero] := by
    intro k i hk hki _
    rcases k with _ | _ | _ | _ | _ | k
    all_goals first | (subst hki; rfl) | omega
  have hin : ∀ k i, k < 5 → aOut.getD k 0 = i → ∀ (q : Fin 3 → ℝ) (t' : ℝ),
      inB q t' k = getR (resA q) i := by
    intro k i hk hki q t'
    simp only [inB, ite_eq_left hk, hki]
  have hcoord : ∀ k i, k < 5 → aOut.getD k 0 = i → i < 22 → ∃ d : ℝ, j < 4 →
      HasDerivAt (fun s ↦ curveB p t j s k) d (baseB p t j) ∧
        Mem prec (nth (nth (denvB RA) k (zeros 4)) j zero) d := by
    intro k i hk hki hi
    obtain ⟨-, hl, hd⟩ := hRA i hi
    rw [hA k i hk hki hi]
    by_cases hj : j < 3
    · obtain ⟨d, hd1, hd2⟩ := hd ⟨j, hj⟩
      refine ⟨d, fun _ ↦ ⟨?_, ?_⟩⟩
      · simp only [curveB, baseB, dite_eq_left hj, hin k i hk hki]
        exact hd1
      · rw [nth_append_lt (by rw [hl]; exact hj)]
        exact hd2
    · refine ⟨0, fun hj4 ↦ ⟨?_, ?_⟩⟩
      · simp only [curveB, baseB, dite_eq_right hj, hin k i hk hki]
        exact hasDerivAt_const _ _
      · have : j = 3 := by omega
        subst this
        rw [← hl, nth_append_length]
        exact mem_zero prec
  rcases k with _ | _ | _ | _ | _ | _ | k
  · exact hcoord 0 16 (by norm_num) rfl (by norm_num)
  · exact hcoord 1 17 (by norm_num) rfl (by norm_num)
  · exact hcoord 2 18 (by norm_num) rfl (by norm_num)
  · exact hcoord 3 19 (by norm_num) rfl (by norm_num)
  · exact hcoord 4 21 (by norm_num) rfl (by norm_num)
  · -- the time
    rw [denvB_eq]
    by_cases hj : j < 3
    · refine ⟨0, fun _ ↦ ⟨?_, ?_⟩⟩
      · have e : (fun s ↦ curveB p t j s 5) = fun _ ↦ t := by
          funext s; simp [curveB, dite_eq_left hj, inB]
        rw [e]; exact hasDerivAt_const _ _
      · rcases j with _ | _ | _ | j
        · exact mem_zero prec
        · exact mem_zero prec
        · exact mem_zero prec
        · omega
    · refine ⟨1, fun hj4 ↦ ⟨?_, ?_⟩⟩
      · have e : (fun s ↦ curveB p t j s 5) = fun s ↦ s := by
          funext s; simp [curveB, dite_eq_right hj, inB]
        rw [e]; simp only [baseB, dite_eq_right hj]; exact hasDerivAt_id _
      · have : j = 3 := by omega
        subst this
        exact mem_one prec
  · refine ⟨0, fun _ ↦ ⟨?_, ?_⟩⟩
    · have e : (fun s ↦ curveB p t j s (k + 6)) = fun _ ↦ 0 := by
        funext s; by_cases hj : j < 3 <;> simp [curveB, hj, inB]
      rw [e]; exact hasDerivAt_const _ _
    · have e : nth (denvB RA) (k + 6) (zeros 4) = zeros 4 := by rw [denvB_eq]; rfl
      rw [e]
      by_cases hj : j < 4
      · rw [zeros, nth_replicate hj]; exact mem_zero prec
      · have e2 : ∀ (l : List DyadicInterval) (i : ℕ), l.length ≤ i → nth l i zero = zero := by
          intro l i hi
          induction l generalizing i with
          | nil => rfl
          | cons b l ih' => cases i <;> simp_all
        rw [e2 _ _ (by simp [zeros]; omega)]; exact mem_zero prec

/-- **The results of `progB` on a piece**, with their derivatives in the cell coordinates
(through `progA`) and in the time (`evalV_sound` along `curveB`). -/
theorem passB_sound {p : Fin 3 → ℝ} {RA : List DualV} (hRA : AFacts p RA) {T : DyadicInterval}
    {t : ℝ} (ht : Mem prec T t) (hok : (passB RA T).2 = true) {o : ℕ} (ho : o < 64) :
    Mem prec (pv RA T o) (getR (resB p t) o) ∧
      (∀ j : Fin 3, ∃ d, HasDerivAt (fun s ↦ getR (resB (Function.update p j s) t) o) d (p j) ∧
        Mem prec (pd RA T j o) d) ∧
      ∃ d, HasDerivAt (fun s ↦ getR (resB p s) o) d t ∧ Mem prec (pd RA T 3 o) d := by
  choose γ' hγ' using exists_derivB hRA t
  have hx : ∀ j < 4, curveB p t j (baseB p t j) = inB p t := by
    intro j _
    by_cases hj : j < 3
    · simp only [curveB, baseB, dite_eq_left hj, Function.update_eq_self]
    · simp only [curveB, baseB, dite_eq_right hj]
  have hdenv : ∀ k, (nth (denvB RA) k (zeros 4)).length = 4 ∧
      ∀ j < 4, Mem prec (nth (nth (denvB RA) k (zeros 4)) j zero) (γ' j k) := by
    intro k
    refine ⟨?_, fun j hj ↦ (hγ' j k hj).2⟩
    have hl : ∀ i < 22, ((resA' RA i).2 ++ [zero]).length = 4 := fun i hi ↦ by
      rw [List.length_append, (hRA i hi).2.1]; rfl
    rw [denvB_eq]
    rcases k with _ | _ | _ | _ | _ | _ | k
    · exact hl 16 (by norm_num)
    · exact hl 17 (by norm_num)
    · exact hl 18 (by norm_num)
    · exact hl 19 (by norm_num)
    · exact hl 21 (by norm_num)
    · rfl
    · rfl
  have hva : ∀ i < 22, Mem prec ((fun i ↦ (resA' RA i).1) i) (getR (resA p) i) :=
    fun i hi ↦ (hRA i hi).1
  obtain ⟨h1, -, h3⟩ := evalV_sound (m := 4) (γ := curveB p t) (s₀ := baseB p t) hx
    (fun j hj k ↦ (hγ' j k hj).1) (envB_encl hva ht) hdenv wf_progB hok o ho
  refine ⟨h1, fun j ↦ ?_, ?_⟩
  · obtain ⟨d, hd, hm⟩ := h3 j (by omega)
    refine ⟨d, ?_, hm⟩
    have e : ∀ s, curveB p t j s = inB (Function.update p j s) t := fun s ↦ by
      simp only [curveB, dite_eq_left j.2]
    simp only [e, baseB, dite_eq_left j.2] at hd
    exact hd
  · obtain ⟨d, hd, hm⟩ := h3 3 (by omega)
    refine ⟨d, ?_, hm⟩
    have e : ∀ s, curveB p t 3 s = inB p s := fun s ↦ by simp [curveB]
    simp only [e, baseB, show ¬ (3 < 3) by omega, dite_eq_right, not_false_eq_true] at hd
    exact hd


/-! ### Soundness of the box check -/

/-- The partial derivatives of the result `o` in the direction `j` lie in `P` on `S × [tl, th]`. -/
def DerivIn (S : Set (Fin 3 → ℝ)) (tl th : ℝ) (o : ℕ) (j : Fin 3) (P : Set ℝ) : Prop :=
  ∀ p ∈ S, ∀ t ∈ Icc tl th, ∃ d,
    HasDerivAt (fun s ↦ getR (resB (Function.update p j s) t) o) d (p j) ∧ d ∈ P

/-- The time derivatives of the result `o` lie in `P` on `S × [tl, th]`. -/
def DerivTimeIn (S : Set (Fin 3 → ℝ)) (tl th : ℝ) (o : ℕ) (P : Set ℝ) : Prop :=
  ∀ p ∈ S, ∀ t ∈ Icc tl th, ∃ d, HasDerivAt (fun s ↦ getR (resB p s) o) d t ∧ d ∈ P

/-- The cell coordinate `i` of the image, `G_i = ` result `outs (i + 1)` of `progB`. -/
noncomputable def Gf (i : ℕ) (p : Fin 3 → ℝ) (t : ℝ) : ℝ := getR (resB p t) (outs.getD (i + 1) 0)

/-- The bound `L_{ij}` as a real number. -/
noncomputable def lB (i j : ℕ) : ℝ := (((lBound.getD i []).getD j 0 : ℚ) : ℝ)

/-- The facts certified on one box `S` with the enclosure `[tl, th]` of the switching time. -/
structure BoxFacts (S : Set (Fin 3 → ℝ)) (tl th : ℝ) : Prop where
  tl_pos : 0 < tl
  tl_lt : tl < th
  neg : ∀ p ∈ S, ∀ t ∈ Icc 0 tl, V₂ p t < 0
  pos : ∀ p ∈ S, 0 < V₂ p th
  vals : ∀ p ∈ S, ∀ t ∈ Icc tl th, U₀ p t < 0 ∧ 0 < V₀ p t ∧ U₁ p t < 0 ∧ 0 < V₁ p t ∧
    U₂ p t < 0 ∧ 0 < Gf 1 p t
  dt : DerivTimeIn S tl th 41 {d | 0 < d}
  lip : ∀ i j : Fin 3, ∃ Qu Qt Pu Pt : Set ℝ, DerivIn S tl th (outs.getD ((i : ℕ) + 1) 0) j Qu ∧
    DerivTimeIn S tl th (outs.getD ((i : ℕ) + 1) 0) Qt ∧ DerivIn S tl th 41 j Pu ∧
    DerivTimeIn S tl th 41 Pt ∧ (∀ q ∈ Qu, ∀ e ∈ Qt, ∀ α ∈ Pu, ∀ β ∈ Pt, |q - e * α / β| ≤ lB i j) ∧
    ∀ β ∈ Pt, 0 < β

theorem mem_hullL {p : ℕ} :
    ∀ {l : List DyadicInterval} {a : DyadicInterval}, a ∈ l → ∀ x, Mem p a x → Mem p (hullL l) x
  | [], _, h, _, _ => by simp at h
  | [b], a, h, x, hx => by
    simp only [List.mem_singleton] at h
    subst h; exact hx
  | b :: c :: l, a, h, x, hx => by
    change Mem p (hull b (hullL (c :: l))) x
    rcases List.mem_cons.1 h with rfl | h
    · exact mem_hull_left _ hx
    · exact mem_hull_right _ (mem_hullL h x hx)

/-- A time of `[tl, th]` lies in one of the pieces. -/
theorem exists_piece {tl th : ℚ} {t : ℝ} (ht : t ∈ Icc (tl : ℝ) th) :
    ∃ m < nPieces, Mem prec (piece tl th m) t := by
  obtain ⟨m, hm, h1, h2⟩ := exists_mem_uniform_cell ht (n := nPieces) (by decide)
  refine ⟨m, hm, mem_ival ?_ ?_⟩ <;> push_cast <;> assumption

theorem negOn_sound {va : ℕ → DyadicInterval} {p : Fin 3 → ℝ}
    (hva : ∀ i < 22, Mem prec (va i) (getR (resA p) i)) {a b : ℚ} (h : negOn va a b = true)
    {t : ℝ} (ht1 : (a : ℝ) ≤ t) (ht2 : t ≤ b) : V₂ p t < 0 := by
  unfold negOn at h
  simp only [Bool.and_eq_true] at h
  have := evalT_sound (envB_encl hva (mem_ival ht1 ht2)) wf_progD h.1 17 (by decide)
  rw [resD_eq] at this
  exact neg_of_hiNeg h.2 this

theorem posAt_sound {va : ℕ → DyadicInterval} {p : Fin 3 → ℝ}
    (hva : ∀ i < 22, Mem prec (va i) (getR (resA p) i)) {a : ℚ} (h : posAt va a = true) :
    0 < V₂ p a := by
  unfold posAt at h
  simp only [Bool.and_eq_true] at h
  have := evalT_sound (envB_encl hva (mem_ival le_rfl le_rfl)) wf_progD h.1 17 (by decide)
  rw [resD_eq] at this
  exact pos_of_loPos h.2 this

/-- **Soundness of the box check.** -/
theorem boxFacts {m : Fin 3 → ℕ} {c : BoxCert} (h : checkBox (m 0) (m 1) (m 2) c = true) :
    BoxFacts (cellSet m) c.tl c.th := by
  unfold checkBox at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hA, h⟩ := h
  set RA := (passA (boxEnv (m 0) (m 1) (m 2))).1 with hRAdef
  have hRA : ∀ p ∈ cellSet m, AFacts p RA := fun p hp i hi ↦ passA_sound hp hA hi
  have hva : ∀ p ∈ cellSet m, ∀ i < 22, Mem prec ((fun i ↦ (resA' RA i).1) i)
      (getR (resA p) i) := fun p hp i hi ↦ (hRA p hp i hi).1
  simp only [checkBoxWith, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨htl, htlth⟩, hneg⟩, hpos⟩, hvals⟩, hdt⟩, hcombo⟩ := h
  -- the facts of `progB` on the pieces
  have hB : ∀ p ∈ cellSet m, ∀ t ∈ Icc (c.tl : ℝ) c.th, ∃ k < nPieces,
      valuesOk RA (piece c.tl c.th k) = true ∧ ∀ o < 64,
      Mem prec (pv RA (piece c.tl c.th k) o) (getR (resB p t) o) ∧
      (∀ j : Fin 3, ∃ d, HasDerivAt (fun s ↦ getR (resB (Function.update p j s) t) o) d (p j) ∧
        Mem prec (pd RA (piece c.tl c.th k) j o) d) ∧
      ∃ d, HasDerivAt (fun s ↦ getR (resB p s) o) d t ∧
        Mem prec (pd RA (piece c.tl c.th k) 3 o) d := by
    intro p hp t ht
    obtain ⟨k, hk, htk⟩ := exists_piece ht
    have hv := hvals k (List.mem_range.2 hk)
    refine ⟨k, hk, hv, fun o ho ↦ ?_⟩
    have hok : (passB RA (piece c.tl c.th k)).2 = true := by
      simp only [valuesOk, Bool.and_eq_true] at hv
      exact hv.1.1.1.1.1.1
    exact passB_sound (hRA p hp) htk hok ho
  have hmem : ∀ j o (k : ℕ), k < nPieces →
      ∀ x, Mem prec (pd RA (piece c.tl c.th k) j o) x → Mem prec (hd RA c.tl c.th j o) x :=
    fun j o k hk x hx ↦ mem_hullL (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩) x hx
  have htime : ∀ o < 64, DerivTimeIn (cellSet m) c.tl c.th o
      {d | Mem prec (hd RA c.tl c.th 3 o) d} := by
    intro o ho p hp t ht
    obtain ⟨k, hk, -, hf⟩ := hB p hp t ht
    obtain ⟨-, -, d, hd1, hd2⟩ := hf o ho
    exact ⟨d, hd1, hmem 3 o k hk d hd2⟩
  have hcoord : ∀ o < 64, ∀ j : Fin 3, DerivIn (cellSet m) c.tl c.th o j
      {d | Mem prec (hd RA c.tl c.th j o) d} := by
    intro o ho j p hp t ht
    obtain ⟨k, hk, -, hf⟩ := hB p hp t ht
    obtain ⟨-, hj, -⟩ := hf o ho
    obtain ⟨d, hd1, hd2⟩ := hj j
    exact ⟨d, hd1, hmem j o k hk d hd2⟩
  have hdt' := htime 41 (by norm_num)
  refine ⟨by exact_mod_cast htl, by exact_mod_cast htlth, ?_, ?_, ?_, ?_, ?_⟩
  · -- `D < 0` on `[0, tl]`
    intro p hp t ht
    exact negOn_sound (hva p hp) hneg (by simpa using ht.1) ht.2
  · -- `D > 0` at `th`
    intro p hp
    exact posAt_sound (hva p hp) hpos
  · -- the signs on `[tl, th]`
    intro p hp t ht
    obtain ⟨k, -, hv, hf⟩ := hB p hp t ht
    simp only [valuesOk, Bool.and_eq_true] at hv
    obtain ⟨⟨⟨⟨⟨⟨-, h13⟩, h15⟩, h22⟩, h25⟩, h37⟩, h61⟩ := hv
    obtain ⟨r13, r15, r22, r25, r37, -⟩ := resB_vals p t
    have m13 := (hf 13 (by norm_num)).1
    have m15 := (hf 15 (by norm_num)).1
    have m22 := (hf 22 (by norm_num)).1
    have m25 := (hf 25 (by norm_num)).1
    have m37 := (hf 37 (by norm_num)).1
    have m61 := (hf 61 (by norm_num)).1
    rw [r13] at m13
    rw [r15] at m15
    rw [r22] at m22
    rw [r25] at m25
    rw [r37] at m37
    exact ⟨neg_of_hiNeg h13 m13, pos_of_loPos h15 m15, neg_of_hiNeg h22 m22, pos_of_loPos h25 m25,
      neg_of_hiNeg h37 m37, pos_of_loPos h61 m61⟩
  · -- `∂_t D > 0`
    intro p hp t ht
    obtain ⟨d, hd, hdm⟩ := hdt' p hp t ht
    exact ⟨d, hd, pos_of_loPos hdt hdm⟩
  · -- the Jacobian bounds
    intro i j
    have hij := hcombo i (by fin_cases i <;> simp) j (by fin_cases j <;> simp)
    have ho : outs.getD ((i : ℕ) + 1) 0 < 64 := by fin_cases i <;> decide
    have hnz : nz (hd RA c.tl c.th 3 41) = true := by
      unfold nz; rw [Bool.or_eq_true]; exact Or.inl hdt
    refine ⟨{d | Mem prec (hd RA c.tl c.th j (outs.getD ((i : ℕ) + 1) 0)) d},
      {d | Mem prec (hd RA c.tl c.th 3 (outs.getD ((i : ℕ) + 1) 0)) d},
      {d | Mem prec (hd RA c.tl c.th j 41) d}, {d | Mem prec (hd RA c.tl c.th 3 41) d},
      hcoord _ ho j, htime _ ho, hcoord 41 (by norm_num) j, hdt',
      fun q hq e he α hα β hβ ↦ ?_, fun β hβ ↦ pos_of_loPos hdt hβ⟩
    exact abs_le_of_magLe hij (mem_sub hq (mem_divT hnz (mem_mul he hα) hβ))


/-! ### The switching time on a box -/

section Switch

variable {S : Set (Fin 3 → ℝ)} {tl th : ℝ}

theorem BoxFacts.hasDerivAt_V₂ (hF : BoxFacts S tl th) {p : Fin 3 → ℝ} (hp : p ∈ S) {t : ℝ}
    (ht : t ∈ Icc tl th) : ∃ d, HasDerivAt (V₂ p) d t ∧ 0 < d := by
  obtain ⟨d, hd, hd0⟩ := hF.dt p hp t ht
  have e : (fun s ↦ getR (resB p s) 41) = V₂ p := funext fun s ↦ (resB_vals p s).2.2.2.2.2.1
  rw [e] at hd
  exact ⟨d, hd, hd0⟩

/-- `D = V₂` is increasing in the time on `[tl, th]`. -/
theorem BoxFacts.lt_of_lt (hF : BoxFacts S tl th) {p : Fin 3 → ℝ} (hp : p ∈ S) {a b : ℝ}
    (ha : a ∈ Icc tl th) (hb : b ∈ Icc tl th) (hab : a < b) : V₂ p a < V₂ p b := by
  obtain ⟨d, hd, e⟩ := exists_eq_mul_sub_of_hasDerivAt (f := V₂ p) (a := a) (b := b)
    (P := fun d ↦ 0 < d) fun s hs ↦ hF.hasDerivAt_V₂ hp (uIcc_subset_Icc ha hb hs)
  have : 0 < d * (b - a) := mul_pos hd (by linarith)
  linarith

/-- The switch: a root of `D` in `(tl, th)`. -/
theorem BoxFacts.exists_root (hF : BoxFacts S tl th) {p : Fin 3 → ℝ} (hp : p ∈ S) :
    ∃ τ ∈ Ioo tl th, V₂ p τ = 0 := by
  have hc : ContinuousOn (V₂ p) (Icc tl th) := fun t ht ↦ by
    obtain ⟨d, hd, -⟩ := hF.hasDerivAt_V₂ hp ht
    exact hd.continuousAt.continuousWithinAt
  have h1 : V₂ p tl < 0 := hF.neg p hp tl ⟨hF.tl_pos.le, le_rfl⟩
  have h2 := hF.pos p hp
  obtain ⟨τ, hτ, e⟩ := intermediate_value_Ioo hF.tl_lt.le hc ⟨h1, h2⟩
  exact ⟨τ, hτ, e⟩

/-- On the first big open cell, the first control is `ζ`, and on a box with the certified facts
the first switching time is the root of `D` in `(tl, th)`: the control `1` beats `ζ` exactly when
`D > 0` (`ham_one_sub_ham_ζ`), and `ζ²` never does (`ham_ζ_sq_sub_ham_ζ`, `Y₂ > 0`). -/
theorem BoxFacts.firstSwitchTime_eq (hF : BoxFacts S tl th) (hS : S ⊆ openBoxOne)
    (hY : ∀ p ∈ S, ∀ t, 0 < t → 0 < (flow t (cellPoint p) ζ 2).im) {p : Fin 3 → ℝ} (hp : p ∈ S)
    {τ : ℝ} (hτ : τ ∈ Ioo tl th) (h0 : V₂ p τ = 0) : firstSwitchTime (cellPoint p) = τ := by
  have hfc : firstControl (cellPoint p) = ζ := definition15_1_2.2.2.2.2.2.1 p (hS hp)
  have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  -- the beaten times are the times with `D > 0`
  have key : ∀ t, 0 < t → ((∃ v ∈ VT, ham (flow t (cellPoint p) ζ) ζ <
      ham (flow t (cellPoint p) ζ) v) ↔ 0 < V₂ p t) := by
    intro t ht
    constructor
    · rintro ⟨v, hv, hlt⟩
      rcases mem_VT.1 hv with rfl | rfl | rfl
      · have := ham_one_sub_ham_ζ p t
        by_contra hc
        push Not at hc
        nlinarith
      · exact absurd hlt (lt_irrefl _)
      · have := ham_ζ_sq_sub_ham_ζ p t
        have hy := hY p hp t ht
        nlinarith
    · intro hD
      refine ⟨1, one_mem_VT, ?_⟩
      have := ham_one_sub_ham_ζ p t
      nlinarith [mul_pos hs3 hD]
  unfold firstSwitchTime
  rw [hfc]
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · refine ⟨th, hF.tl_pos.trans hF.tl_lt, (key th (hF.tl_pos.trans hF.tl_lt)).2 (hF.pos p hp)⟩
  · rintro a ⟨ha, hbeat⟩
    have hD := (key a ha).1 hbeat
    by_contra hlt
    push Not at hlt
    rcases le_total a tl with h | h
    · linarith [hF.neg p hp a ⟨ha.le, h⟩]
    · have := hF.lt_of_lt hp ⟨h, (hlt.trans hτ.2).le⟩ ⟨hτ.1.le, hτ.2.le⟩ hlt
      linarith
  · intro w hw
    have hτ0 : 0 < τ := hF.tl_pos.trans hτ.1
    rcases le_or_gt w th with h | h
    · refine ⟨(τ + w) / 2, ⟨by linarith, (key _ (by linarith)).2 ?_⟩, by linarith⟩
      have := hF.lt_of_lt hp ⟨hτ.1.le, hτ.2.le⟩ ⟨by linarith [hτ.1], by linarith⟩
        (show τ < (τ + w) / 2 by linarith)
      linarith
    · have hth : 0 < th := hF.tl_pos.trans hF.tl_lt
      exact ⟨th, ⟨hth, (key th hth).2 (hF.pos p hp)⟩, h⟩

end Switch

/-! ### The map in coordinates -/

/-- The Fuller–Poincaré map in cell coordinates near `q_out`: the coordinates of the switching
point, rotated back to the wall `𝒲₀` by `ζ`. -/
noncomputable def g (p : Fin 3 → ℝ) : Fin 3 → ℝ := cellCoords (ζ • poincare (cellPoint p))

theorem arg_eq_arctan_add_pi {z : ℂ} (hre : z.re < 0) (him : 0 ≤ z.im) :
    Complex.arg z = Real.arctan (z.im / z.re) + Real.pi := by
  have h1 : Real.pi / 2 < Complex.arg z := by
    have hn : ¬ |Complex.arg z| ≤ Real.pi / 2 := fun h ↦
      (not_le.2 hre) (Complex.abs_arg_le_pi_div_two_iff.1 h)
    push Not at hn
    rwa [abs_of_nonneg (Complex.arg_nonneg_iff.2 him)] at hn
  have h2 := Complex.arg_le_pi z
  have ht : Real.tan (Complex.arg z - Real.pi) = z.im / z.re := by
    rw [Real.tan_periodic.sub_eq, Complex.tan_arg]
  have := Real.arctan_tan (x := Complex.arg z - Real.pi) (by linarith) (by linarith)
  rw [ht] at this
  linarith

theorem norm_eq_sqrt (z : ℂ) : ‖z‖ = √(z.re ^ 2 + z.im ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]; ring_nf

/-- **The map on a certified box**: the switch is the root `τ` of `D`, the image class is the class
of `g p`, and `g p` is `(G₀, G₁, G₂)` at `(p, τ)`. -/
theorem BoxFacts.g_spec {S : Set (Fin 3 → ℝ)} {tl th : ℝ} (hF : BoxFacts S tl th)
    (hS : S ⊆ openBoxOne) (hY : ∀ p ∈ S, ∀ t, 0 < t → 0 < (flow t (cellPoint p) ζ 2).im)
    {p : Fin 3 → ℝ} (hp : p ∈ S) :
    firstSwitchTime (cellPoint p) ∈ Ioo tl th ∧ V₂ p (firstSwitchTime (cellPoint p)) = 0 ∧
      poincareAngZero (cellClass p) = cellClass (g p) ∧
      ∀ i : Fin 3, g p i = Gf i p (firstSwitchTime (cellPoint p)) := by
  obtain ⟨τ, hτ, h0⟩ := hF.exists_root hp
  have hτe := hF.firstSwitchTime_eq hS hY hp hτ h0
  rw [hτe]
  refine ⟨hτ, h0, ?_, ?_⟩
  all_goals
    have hpo := hS hp
    have hdom : p ∈ cellDomain := ⟨⟨hpo.1.1.le, hpo.1.2.le⟩, ⟨hpo.2.1.1.le, hpo.2.1.2.le⟩,
      ⟨by linarith [hpo.2.2.1, Real.pi_pos], hpo.2.2.2.le⟩⟩
    have hz := cellPoint_mem_sectionZero hdom
    have hw := poincare_mem_sectionZero hz
    have hfc : firstControl (cellPoint p) = ζ := definition15_1_2.2.2.2.2.2.1 p hpo
    have hpw : poincare (cellPoint p) = flow τ (cellPoint p) ζ := by
      rw [poincare, hfc, hτe]
    obtain ⟨e0r, e0i, e1r, e1i, e2r, e2i⟩ := zeta_flow p τ
    obtain ⟨vU₀, vV₀, vU₁, vV₁, vU₂, -⟩ := hF.vals p hp τ ⟨hτ.1.le, hτ.2.le⟩
  · -- the class
    have hζw : ζ • poincare (cellPoint p) ∈ sectionZero := by
      have e := classOf_smul_scale ζ_mem_VT one_pos hw
      refine ⟨fun h ↦ hw.1 ?_, ?_, ?_⟩
      · have := congrArg (fun z ↦ ζ⁻¹ • z) h
        simp only [smul_zero, inv_smul_smul₀ (show ζ ≠ 0 from fun h ↦ by
          simpa [h] using norm_ζ)] at this
        exact this
      · exact mul_mem_walls ζ_mem_VT hw.2.1
      · have := (hamMax_smul_scale_and_tau ζ_mem_VT one_pos (poincare (cellPoint p))).1
        rw [scale_one, one_pow, one_mul] at this
        rw [this, hw.2.2]
    have him : ((ζ • poincare (cellPoint p)) 2).im = 0 := by
      rw [Pi.smul_apply, smul_eq_mul, hpw, e2i, h0]
    have hre : ((ζ • poincare (cellPoint p)) 2).re < 0 := by
      rw [Pi.smul_apply, smul_eq_mul, hpw, e2r]; exact vU₂
    have hc := (cellClass_cellCoords hζw him hre).2
    have hcl := classOf_smul_scale ζ_mem_VT one_pos hw
    rw [scale_one] at hcl
    change poincareAngZero (classOf (cellPoint p)) = cellClass (g p)
    rw [poincareAngZero_classOf hz, g, hc, hcl]
  · -- the coordinates
    obtain ⟨-, -, -, -, -, -, -, h45, h49, h56, h58, h61, h63⟩ := resB_vals p τ
    have hz0 : (ζ • poincare (cellPoint p)) 0 = ζ * flow τ (cellPoint p) ζ 0 := by
      rw [Pi.smul_apply, smul_eq_mul, hpw]
    have hz1 : (ζ • poincare (cellPoint p)) 1 = ζ * flow τ (cellPoint p) ζ 1 := by
      rw [Pi.smul_apply, smul_eq_mul, hpw]
    have ha : ‖(ζ • poincare (cellPoint p)) 0‖ = √(U₀ p τ ^ 2 + V₀ p τ ^ 2) := by
      rw [hz0, norm_eq_sqrt, e0r, e0i]
    have hb : ‖(ζ • poincare (cellPoint p)) 1‖ = √(U₁ p τ ^ 2 + V₁ p τ ^ 2) := by
      rw [hz1, norm_eq_sqrt, e1r, e1i]
    have harg0 : Complex.arg ((ζ • poincare (cellPoint p)) 0) =
        Real.arctan (V₀ p τ / U₀ p τ) + Real.pi := by
      rw [arg_eq_arctan_add_pi (by rw [hz0, e0r]; exact vU₀) (by rw [hz0, e0i]; exact vV₀.le),
        hz0, e0r, e0i]
    have harg1 : Complex.arg ((ζ • poincare (cellPoint p)) 1) =
        Real.arctan (V₁ p τ / U₁ p τ) + Real.pi := by
      rw [arg_eq_arctan_add_pi (by rw [hz1, e1r]; exact vU₁) (by rw [hz1, e1i]; exact vV₁.le),
        hz1, e1r, e1i]
    intro i
    fin_cases i
    · -- `r₂ = s² b` with `s = 2/(a + √(a² + 4b))`
      change (if ‖(ζ • poincare (cellPoint p)) 1‖ = 0 then ‖(ζ • poincare (cellPoint p)) 0‖⁻¹
        else (-‖(ζ • poincare (cellPoint p)) 0‖ + √(‖(ζ • poincare (cellPoint p)) 0‖ ^ 2 +
          4 * ‖(ζ • poincare (cellPoint p)) 1‖)) / (2 * ‖(ζ • poincare (cellPoint p)) 1‖)) ^ 2 *
        ‖(ζ • poincare (cellPoint p)) 1‖ = Gf 0 p τ
      have hbpos : 0 < √(U₁ p τ ^ 2 + V₁ p τ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
      rw [ha, hb, ite_eq_right hbpos.ne', show Gf 0 p τ = getR (resB p τ) 56 from rfl, h56]
      set a := √(U₀ p τ ^ 2 + V₀ p τ ^ 2)
      set b := √(U₁ p τ ^ 2 + V₁ p τ ^ 2)
      have ha0 : 0 ≤ a := Real.sqrt_nonneg _
      have ha2 : a ^ 2 = U₀ p τ ^ 2 + V₀ p τ ^ 2 := Real.sq_sqrt (by positivity)
      rw [← ha2]
      set R := √(a ^ 2 + 4 * b)
      have hR2 : R ^ 2 = a ^ 2 + 4 * b := Real.sq_sqrt (by positivity)
      have hR0 : 0 ≤ R := Real.sqrt_nonneg _
      have hRa : 0 < a + R := by nlinarith
      have e : (-a + R) / (2 * b) = 2 / (a + R) := by
        rw [div_eq_div_iff (by positivity) hRa.ne']
        nlinarith
      rw [e]
      field_simp
      ring
    · -- `ψ = arg z₂ - arg z₁` reduced to `[0, 2π)`
      change toIcoMod Real.two_pi_pos 0 (Complex.arg ((ζ • poincare (cellPoint p)) 1) -
        Complex.arg ((ζ • poincare (cellPoint p)) 0)) = Gf 1 p τ
      have hG : Gf 1 p τ = Real.arctan (V₁ p τ / U₁ p τ) - Real.arctan (V₀ p τ / U₀ p τ) := h61
      rw [harg1, harg0, hG, show Real.arctan (V₁ p τ / U₁ p τ) + Real.pi -
        (Real.arctan (V₀ p τ / U₀ p τ) + Real.pi) = Real.arctan (V₁ p τ / U₁ p τ) -
          Real.arctan (V₀ p τ / U₀ p τ) by ring, toIcoMod_eq_self]
      obtain ⟨-, -, -, -, -, hG1⟩ := hF.vals p hp τ ⟨hτ.1.le, hτ.2.le⟩
      rw [hG] at hG1
      have := Real.arctan_lt_pi_div_two (V₁ p τ / U₁ p τ)
      have := Real.neg_pi_div_two_lt_arctan (V₀ p τ / U₀ p τ)
      constructor <;> linarith [Real.pi_pos]
    · change Complex.arg ((ζ • poincare (cellPoint p)) 1) = Gf 2 p τ
      rw [harg1]
      exact h63.symm

/-! ### The box `B` and its subdivision -/

/-- The lower corner `(0.25, 0.15, 2.85)` of `B`. -/
noncomputable def bLoR : Fin 3 → ℝ := ![1 / 4, 3 / 20, 57 / 20]

/-- The upper corner `(0.29, 0.19, 2.98)` of `B`. -/
noncomputable def bHiR : Fin 3 → ℝ := ![29 / 100, 19 / 100, 149 / 50]

theorem gridPt_eq (i : Fin 3) (k : ℕ) : (gridPt i k : ℝ) =
    bLoR i + k * (bHiR i - bLoR i) / (nGrid.getD i 1 : ℕ) := by
  fin_cases i <;> simp [gridPt, bLo, bHi, nGrid, bLoR, bHiR]

theorem nGrid_pos (i : Fin 3) : 0 < nGrid.getD i 1 := by fin_cases i <;> decide

theorem bLoR_lt_bHiR (i : Fin 3) : bLoR i < bHiR i := by
  fin_cases i <;> norm_num [bLoR, bHiR]

theorem gridPt_mono (i : Fin 3) : Monotone fun k : ℕ ↦ (gridPt i k : ℝ) := by
  intro a b hab
  simp only [gridPt_eq]
  have h := bLoR_lt_bHiR i
  have hn : (0 : ℝ) < (nGrid.getD i 1 : ℕ) := by exact_mod_cast nGrid_pos i
  gcongr

theorem gridPt_zero (i : Fin 3) : (gridPt i 0 : ℝ) = bLoR i := by simp [gridPt_eq]

theorem gridPt_last (i : Fin 3) : (gridPt i (nGrid.getD i 1) : ℝ) = bHiR i := by
  have hn : ((nGrid.getD i 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (nGrid_pos i).ne'
  rw [gridPt_eq]; field_simp; ring

theorem mem_Icc_iff' {p : Fin 3 → ℝ} : p ∈ Icc bLoR bHiR ↔ ∀ i, bLoR i ≤ p i ∧ p i ≤ bHiR i := by
  simp only [mem_Icc, Pi.le_def]
  exact ⟨fun h i ↦ ⟨h.1 i, h.2 i⟩, fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩⟩

/-- Every point of `B` lies in a box of the subdivision. -/
theorem exists_cell {p : Fin 3 → ℝ} (hp : p ∈ Icc bLoR bHiR) :
    ∃ m : Fin 3 → ℕ, (∀ i, m i < nGrid.getD i 1) ∧ p ∈ cellSet m := by
  have h : ∀ i : Fin 3, ∃ k < nGrid.getD i 1, (gridPt i k : ℝ) ≤ p i ∧ p i ≤ gridPt i (k + 1) := by
    intro i
    obtain ⟨k, hk, h1, h2⟩ := exists_mem_uniform_cell (mem_Icc_iff'.1 hp i) (nGrid_pos i)
    refine ⟨k, hk, ?_, ?_⟩
    · rw [gridPt_eq]; exact h1
    · rw [gridPt_eq]; push_cast; exact h2
  choose m hm hmp using h
  exact ⟨m, hm, hmp⟩

theorem cellSet_subset {m : Fin 3 → ℕ} (hm : ∀ i, m i < nGrid.getD i 1) :
    cellSet m ⊆ Icc bLoR bHiR := by
  intro p hp
  refine mem_Icc_iff'.2 fun i ↦ ⟨?_, ?_⟩
  · rw [← gridPt_zero]; exact (gridPt_mono i (Nat.zero_le _)).trans (hp i).1
  · rw [← gridPt_last]; exact (hp i).2.trans (gridPt_mono i (hm i))

theorem update_mem_cellSet {m : Fin 3 → ℕ} {p : Fin 3 → ℝ} (hp : p ∈ cellSet m) (j : Fin 3)
    {u : ℝ} (hu : (gridPt j (m j) : ℝ) ≤ u ∧ u ≤ gridPt j (m j + 1)) :
    Function.update p j u ∈ cellSet m := by
  intro i
  by_cases h : i = j
  · subst h; simpa using hu
  · rw [Function.update_of_ne h]; exact hp i

/-- **`B` lies in the open first big cell.** -/
theorem Icc_subset_openBoxOne : Icc bLoR bHiR ⊆ openBoxOne := by
  intro p hp
  have h := mem_Icc_iff'.1 hp
  have hpi := Real.pi_gt_d2
  obtain ⟨h0, h0'⟩ := h 0
  obtain ⟨h1, h1'⟩ := h 1
  obtain ⟨h2, h2'⟩ := h 2
  norm_num [bLoR, bHiR] at h0 h0' h1 h1' h2 h2'
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- `Y₂ = Im z₃(t) > 0` for `t > 0` on `B` (so `ζ²` never beats `ζ`). -/
theorem flow_two_im_pos {p : Fin 3 → ℝ} (hp : p ∈ Icc bLoR bHiR) {t : ℝ} (ht : 0 < t) :
    0 < (flow t (cellPoint p) ζ 2).im := by
  have hpo := Icc_subset_openBoxOne hp
  have h := mem_Icc_iff'.1 hp
  have hpi := Real.pi_gt_d2
  obtain ⟨h1, h1'⟩ := h 1
  obtain ⟨h2, h2'⟩ := h 2
  norm_num [bLoR, bHiR] at h1 h1' h2 h2'
  have hs2 : 0 < Real.sin (p 2) := Real.sin_pos_of_pos_of_lt_pi hpo.2.2.1 hpo.2.2.2
  have hs1 : 0 < Real.sin (p 2 - p 1) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [flow_two_im]
  have := hpo.1.1
  have := hpo.1.2
  have : 0 < 1 - p 0 := by linarith
  positivity

/-- The certified facts on every box of the subdivision. -/
theorem boxFacts_cell {m : Fin 3 → ℕ} (hm : ∀ i, m i < nGrid.getD i 1) :
    BoxFacts (cellSet m) (certs.getD (boxIndex (m 0) (m 1) (m 2)) ⟨0, 0⟩).tl
      (certs.getD (boxIndex (m 0) (m 1) (m 2)) ⟨0, 0⟩).th :=
  boxFacts (checkBox_all (hm 0) (hm 1) (hm 2))

/-- The map on `B`: the switch, the class identity and the coordinates. -/
theorem g_spec_B {p : Fin 3 → ℝ} (hp : p ∈ Icc bLoR bHiR) :
    poincareAngZero (cellClass p) = cellClass (g p) ∧
      ∀ i : Fin 3, g p i = Gf i p (firstSwitchTime (cellPoint p)) := by
  obtain ⟨m, hm, hpm⟩ := exists_cell hp
  obtain ⟨-, -, h1, h2⟩ := (boxFacts_cell hm).g_spec
    ((cellSet_subset hm).trans Icc_subset_openBoxOne)
    (fun q hq t ht ↦ flow_two_im_pos (cellSet_subset hm hq) ht) hpm
  exact ⟨h1, h2⟩

/-! ### The Lipschitz bound -/

/-- **The entries of the Jacobian, on one box.** -/
theorem box_lip {m : Fin 3 → ℕ} (hm : ∀ i, m i < nGrid.getD i 1) (i j : Fin 3)
    {p : Fin 3 → ℝ} (hp : p ∈ cellSet m) {y : ℝ} (hy : Function.update p j y ∈ cellSet m) :
    |g (Function.update p j y) i - g p i| ≤ lB i j * |y - p j| := by
  have hF := boxFacts_cell hm
  set c := certs.getD (boxIndex (m 0) (m 1) (m 2)) ⟨0, 0⟩
  have hS := (cellSet_subset hm).trans Icc_subset_openBoxOne
  have hY : ∀ q ∈ cellSet m, ∀ t, 0 < t → 0 < (flow t (cellPoint q) ζ 2).im :=
    fun q hq t ht ↦ flow_two_im_pos (cellSet_subset hm hq) ht
  obtain ⟨Qu, Qt, Pu, Pt, hQu, hQt, hPu, hPt, hcombo, hPt0⟩ := hF.lip i j
  have hmem : ∀ u ∈ Icc (gridPt j (m j) : ℝ) (gridPt j (m j + 1)),
      Function.update p j u ∈ cellSet m := fun u hu ↦ update_mem_cellSet hp j hu
  have key := abs_sub_le_of_implicit
    (F := fun u t ↦ getR (resB (Function.update p j u) t) 41)
    (G := fun u t ↦ Gf i (Function.update p j u) t)
    (τ := fun u ↦ firstSwitchTime (cellPoint (Function.update p j u)))
    (L := lB i j) (Pu := Pu) (Pt := Pt) (Qu := Qu) (Qt := Qt)
    (fun u hu t ht ↦ by
      have := hPu _ (hmem u hu) t ht
      simp only [Function.update_idem, Function.update_self] at this
      exact this)
    (fun u hu t ht ↦ hPt _ (hmem u hu) t ht)
    (fun u hu t ht ↦ by
      have := hQu _ (hmem u hu) t ht
      simp only [Function.update_idem, Function.update_self] at this
      exact this)
    (fun u hu t ht ↦ hQt _ (hmem u hu) t ht)
    hcombo (fun β hβ ↦ (hPt0 β hβ).ne')
    (fun u hu ↦ by
      obtain ⟨h1, h2, -, -⟩ := hF.g_spec hS hY (hmem u hu)
      refine ⟨⟨h1.1.le, h1.2.le⟩, ?_⟩
      rw [(resB_vals _ _).2.2.2.2.2.1]
      exact h2)
    (p j) ⟨(hp j).1, (hp j).2⟩ y (by simpa using hy j)
  beta_reduce at key
  rw [Function.update_eq_self] at key
  obtain ⟨-, -, -, hgy⟩ := hF.g_spec hS hY hy
  obtain ⟨-, -, -, hgp⟩ := hF.g_spec hS hY hp
  rw [hgy i, hgp i]
  exact key

/-- **One coordinate at a time, across the boxes.** -/
theorem coord_lip {r : Fin 3 → ℝ} (hr : r ∈ Icc bLoR bHiR) (i j : Fin 3) {y : ℝ}
    (hy : bLoR j ≤ y ∧ y ≤ bHiR j) :
    |g (Function.update r j y) i - g r i| ≤ lB i j * |y - r j| := by
  obtain ⟨m, hm, hrm⟩ := exists_cell hr
  have hgrid := abs_sub_le_of_grid (φ := fun u ↦ g (Function.update r j u) i) (L := lB i j)
    (gridPt_mono j) (nGrid.getD j 1) (fun k hk u hu v hv ↦ by
      -- `update r j u`, `update r j v` lie in the box with index `k` in the coordinate `j`
      have hm' : ∀ i', Function.update m j k i' < nGrid.getD i' 1 := by
        intro i'
        by_cases h : i' = j
        · subst h; simpa using hk
        · rw [Function.update_of_ne h]; exact hm i'
      have hrv : Function.update r j v ∈ cellSet (Function.update m j k) := by
        intro i'
        by_cases h : i' = j
        · subst h; simpa using hv
        · simp only [Function.update_of_ne h]
          exact hrm i'
      have hru : Function.update (Function.update r j v) j u ∈
          cellSet (Function.update m j k) := by
        intro i'
        by_cases h : i' = j
        · subst h; simpa using hu
        · simp only [Function.update_of_ne h]
          exact hrm i'
      have := box_lip hm' i j hrv hru
      simp only [Function.update_idem, Function.update_self] at this
      exact this)
  have h1 := hgrid y ⟨by rw [gridPt_zero]; exact hy.1, by rw [gridPt_last]; exact hy.2⟩ (r j)
    ⟨by rw [gridPt_zero]; exact (mem_Icc_iff'.1 hr j).1,
      by rw [gridPt_last]; exact (mem_Icc_iff'.1 hr j).2⟩
  simp only [Function.update_eq_self] at h1
  exact h1

theorem update_mem_B {r : Fin 3 → ℝ} (hr : r ∈ Icc bLoR bHiR) (j : Fin 3) {y : ℝ}
    (hy : bLoR j ≤ y ∧ y ≤ bHiR j) : Function.update r j y ∈ Icc bLoR bHiR := by
  refine mem_Icc_iff'.2 fun i ↦ ?_
  by_cases h : i = j
  · subst h; simpa using hy
  · rw [Function.update_of_ne h]; exact mem_Icc_iff'.1 hr i

/-- **The entrywise bound on `B`**: `|g_i(q) - g_i(p)| ≤ Σ_j L_{ij} |q_j - p_j|`. -/
theorem g_entry_bound {p q : Fin 3 → ℝ} (hp : p ∈ Icc bLoR bHiR) (hq : q ∈ Icc bLoR bHiR)
    (i : Fin 3) : |g q i - g p i| ≤ ∑ j : Fin 3, lB i j * |q j - p j| := by
  have hq' := mem_Icc_iff'.1 hq
  set r₁ := Function.update p 0 (q 0)
  set r₂ := Function.update r₁ 1 (q 1)
  have hr₁ : r₁ ∈ Icc bLoR bHiR := update_mem_B hp 0 (hq' 0)
  have hr₂ : r₂ ∈ Icc bLoR bHiR := update_mem_B hr₁ 1 (hq' 1)
  have hr₃ : Function.update r₂ 2 (q 2) = q := by
    funext k; fin_cases k <;> simp [r₂, r₁]
  have e1 : |g r₁ i - g p i| ≤ lB i 0 * |q 0 - p 0| := coord_lip hp i 0 (hq' 0)
  have e2 : |g r₂ i - g r₁ i| ≤ lB i 1 * |q 1 - p 1| := by
    have := coord_lip hr₁ i 1 (hq' 1)
    have hr₁1 : r₁ 1 = p 1 := by simp [r₁]
    rwa [hr₁1] at this
  have e3 : |g q i - g r₂ i| ≤ lB i 2 * |q 2 - p 2| := by
    have := coord_lip hr₂ i 2 (hq' 2)
    have hr₂2 : r₂ 2 = p 2 := by simp [r₂, r₁]
    rwa [hr₂2, hr₃] at this
  rw [Fin.sum_univ_three]
  calc |g q i - g p i| ≤ |g q i - g r₂ i| + |g r₂ i - g r₁ i| + |g r₁ i - g p i| := by
        have := abs_sub_le (g q i) (g r₂ i) (g p i)
        have := abs_sub_le (g r₂ i) (g r₁ i) (g p i)
        linarith
    _ ≤ lB i 2 * |q 2 - p 2| + lB i 1 * |q 1 - p 1| + lB i 0 * |q 0 - p 0| := by
        gcongr
    _ = lB i (0 : Fin 3) * |q 0 - p 0| + lB i (1 : Fin 3) * |q 1 - p 1| +
        lB i (2 : Fin 3) * |q 2 - p 2| := by
        simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
        ring

theorem lB_nonneg (i j : Fin 3) : 0 ≤ lB i j := by
  fin_cases i <;> fin_cases j <;> norm_num [lB, lBound]

theorem lB_rows (i : Fin 3) : ∑ j : Fin 3, lB i j ≤ 1 / 2 := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> norm_num [lB, lBound]

/-- **`g` is `1/2`-Lipschitz on `B`** (sup metric of the cell coordinates). -/
theorem lipschitzOnWith_g : LipschitzOnWith (1 / 2) g (Icc bLoR bHiR) := by
  refine lipschitzOnWith_of_abs_sub_le (L := fun i j ↦ lB i j) (fun i j ↦ lB_nonneg i j)
    (fun i ↦ by simpa using lB_rows i) fun p hp q hq i ↦ ?_
  exact g_entry_bound hq hp i

/-! ### The image of `B` -/

/-- The center `(0.27, 0.17, 2.915)` of `B`. -/
noncomputable def cR : Fin 3 → ℝ := ![27 / 100, 17 / 100, 583 / 200]

theorem cR_eq (k : Fin 3) : cR k = ((cPt.getD k 0 : ℚ) : ℝ) := by
  fin_cases k <;> norm_num [cR, cPt]

theorem cR_mem : cR ∈ Icc bLoR bHiR := by
  refine mem_Icc_iff'.2 fun i ↦ ?_
  fin_cases i <;> norm_num [cR, bLoR, bHiR]

theorem cR_cell : cR ∈ cellSet ![1, 1, 2] := by
  intro i
  rw [cR_eq]
  fin_cases i <;> norm_num [gridPt, bLo, bHi, nGrid, cPt]

/-- **The center**: an enclosure of `g(c)` with `g(c) ± Σ_j L_{ij} r_j ⊆ B`. -/
theorem center_facts (i : Fin 3) : ∃ I : DyadicInterval, Mem prec I (g cR i) ∧
    ((bLo.getD i 0 : ℚ) : ℝ) ≤ (I.lo : ℝ) / 2 ^ prec - (spread i : ℝ) ∧
    (I.hi : ℝ) / 2 ^ prec + (spread i : ℝ) ≤ ((bHi.getD i 0 : ℚ) : ℝ) := by
  have h := checkCenter_eq_true
  simp only [checkCenter, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, ⟨hk1, hk2, hk3⟩⟩, ⟨⟨⟨⟨hLA, hneg⟩, hpos⟩, hLB⟩, hG⟩⟩ := h
  -- the box of the center and its switching time
  have hm : ∀ i', (![1, 1, 2] : Fin 3 → ℕ) i' < nGrid.getD i' 1 := by
    intro i'; fin_cases i' <;> decide
  have hF := boxFacts_cell hm
  have hS := (cellSet_subset hm).trans Icc_subset_openBoxOne
  have hY : ∀ q ∈ cellSet ![1, 1, 2], ∀ t, 0 < t → 0 < (flow t (cellPoint q) ζ 2).im :=
    fun q hq t ht ↦ flow_two_im_pos (cellSet_subset hm hq) ht
  obtain ⟨hτ, h0, -, hg⟩ := hF.g_spec hS hY cR_cell
  set τ := firstSwitchTime (cellPoint cR)
  set ck := certs.getD (boxIndex ((![1, 1, 2] : Fin 3 → ℕ) 0) ((![1, 1, 2] : Fin 3 → ℕ) 1)
    ((![1, 1, 2] : Fin 3 → ℕ) 2)) ⟨0, 0⟩
  have hck : ck = certs.getD (boxIndex cBox.1 cBox.2.1 cBox.2.2) ⟨0, 0⟩ := rfl
  rw [← hck] at hk1 hk3
  -- `progA` at the center
  have henvA : ∀ k, Mem prec (nth [ival (cPt.getD 0 0) (cPt.getD 0 0),
      ival (cPt.getD 1 0) (cPt.getD 1 0), ival (cPt.getD 2 0) (cPt.getD 2 0)] k zero)
      (inA cR k) := by
    intro k
    rcases k with _ | _ | _ | k
    · exact mem_ival (le_of_eq (cR_eq 0).symm) (le_of_eq (cR_eq 0))
    · exact mem_ival (le_of_eq (cR_eq 1).symm) (le_of_eq (cR_eq 1))
    · exact mem_ival (le_of_eq (cR_eq 2).symm) (le_of_eq (cR_eq 2))
    · have : inA cR (k + 3) = 0 := by simp [inA]
      rw [this]; exact mem_zero prec
  have hva := evalT_sound henvA wf_progA hLA
  have hva' : ∀ i < 22, Mem prec ((fun i ↦ resT (evalT prec [ival (cPt.getD 0 0) (cPt.getD 0 0),
      ival (cPt.getD 1 0) (cPt.getD 1 0), ival (cPt.getD 2 0) (cPt.getD 2 0)] progA).1 22 i) i)
      (getR (resA cR) i) := fun i hi ↦ hva i hi
  -- the sign of `D` at the ends of `[tl_c, th_c]`
  have hneg' : V₂ cR cCert.tl < 0 := negOn_sound hva' hneg le_rfl le_rfl
  have hpos' : 0 < V₂ cR cCert.th := posAt_sound hva' hpos
  have hk1' : (ck.tl : ℝ) ≤ cCert.tl := by exact_mod_cast hk1
  have hk2' : (cCert.tl : ℝ) < cCert.th := by exact_mod_cast hk2
  have hk3' : (cCert.th : ℝ) ≤ ck.th := by exact_mod_cast hk3
  -- `τ ∈ [tl_c, th_c]`
  have hτc : (cCert.tl : ℝ) ≤ τ ∧ τ ≤ cCert.th := by
    constructor
    · by_contra hc
      push Not at hc
      have := hF.lt_of_lt cR_cell ⟨hτ.1.le, hτ.2.le⟩ ⟨hk1', hk2'.le.trans hk3'⟩ hc
      linarith
    · by_contra hc
      push Not at hc
      have := hF.lt_of_lt cR_cell ⟨hk1'.trans hk2'.le, hk3'⟩ ⟨hτ.1.le, hτ.2.le⟩ hc
      linarith
  have hGi := hG i (by fin_cases i <;> simp)
  have ho : outs.getD ((i : ℕ) + 1) 0 < 64 := by fin_cases i <;> decide
  set I := resT (evalT prec (envB (fun i ↦ resT (evalT prec [ival (cPt.getD 0 0) (cPt.getD 0 0),
    ival (cPt.getD 1 0) (cPt.getD 1 0), ival (cPt.getD 2 0) (cPt.getD 2 0)] progA).1 22 i)
    (ival cCert.tl cCert.th)) progB).1 64 (outs.getD ((i : ℕ) + 1) 0) with hI
  refine ⟨I, ?_, ?_, ?_⟩
  · rw [hg i]
    exact evalT_sound (envB_encl hva' (mem_ival hτc.1 hτc.2)) wf_progB hLB _ ho
  · have := hGi.1
    have h' : ((bLo.getD i 0 : ℚ) : ℝ) ≤ (((I.lo : ℚ) / 2 ^ prec - spread i : ℚ) : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    exact h'
  · have := hGi.2
    have h' : (((I.hi : ℚ) / 2 ^ prec + spread i : ℚ) : ℝ) ≤ ((bHi.getD i 0 : ℚ) : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    exact h'

theorem abs_sub_cR_le {p : Fin 3 → ℝ} (hp : p ∈ Icc bLoR bHiR) (j : Fin 3) :
    |p j - cR j| ≤ ((bRad j : ℚ) : ℝ) := by
  have h := mem_Icc_iff'.1 hp j
  rw [abs_le]
  fin_cases j <;> norm_num [cR, bLoR, bHiR, bRad, bLo, bHi] at h ⊢ <;> constructor <;> linarith

theorem sum_lB_rad (i : Fin 3) : ∑ j : Fin 3, lB i j * ((bRad j : ℚ) : ℝ) = (spread i : ℝ) := by
  fin_cases i <;> norm_num [lB, lBound, bRad, bLo, bHi, spread, Fin.sum_univ_three,
    List.range_succ]

/-- **`g` maps `B` into itself.** -/
theorem mapsTo_g : MapsTo g (Icc bLoR bHiR) (Icc bLoR bHiR) := by
  intro p hp
  refine mem_Icc_iff'.2 fun i ↦ ?_
  obtain ⟨I, hI, hlo, hhi⟩ := center_facts i
  have hb := g_entry_bound cR_mem hp i
  have hsp : ∑ j : Fin 3, lB i j * |p j - cR j| ≤ (spread i : ℝ) := by
    rw [← sum_lB_rad]
    exact Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_left (abs_sub_cR_le hp j) (lB_nonneg i j)
  obtain ⟨h1, h2⟩ := abs_le.1 (hb.trans hsp)
  have elo : ((bLo.getD i 0 : ℚ) : ℝ) = bLoR i := by fin_cases i <;> norm_num [bLo, bLoR]
  have ehi : ((bHi.getD i 0 : ℚ) : ℝ) = bHiR i := by fin_cases i <;> norm_num [bHi, bHiR]
  rw [elo] at hlo
  rw [ehi] at hhi
  constructor <;> linarith [hI.1, hI.2]

/-- **The contraction on `B`** (the contraction part of `DOutContracts` with the witnesses
`lo = (0.25, 0.15, 2.85)`, `hi = (0.29, 0.19, 2.98)`, `κ = 1/2`): `B` lies in the open first big
cell, and the Fuller–Poincaré map is, on `B`, a map `g` of `B` into itself that is `1/2`-Lipschitz
in the sup metric of the cell coordinates. -/
theorem contraction_on_B :
    Icc bLoR bHiR ⊆ openBoxOne ∧
      ∃ g : (Fin 3 → ℝ) → Fin 3 → ℝ, MapsTo g (Icc bLoR bHiR) (Icc bLoR bHiR) ∧
        LipschitzOnWith (1 / 2) g (Icc bLoR bHiR) ∧
        ∀ p ∈ Icc bLoR bHiR, poincareAngZero (cellClass p) = cellClass (g p) :=
  ⟨Icc_subset_openBoxOne, g, mapsTo_g, lipschitzOnWith_g, fun _ hp ↦ (g_spec_B hp).1⟩

/-- **The contraction part of `DOutContracts`**, in its shape: a box `[lo, hi]` in the open first
big cell, `κ < 1`, and a `κ`-Lipschitz self-map `g` of the box that is the Fuller–Poincaré map in
coordinates (the remaining parts of `DOutContracts`, `F(𝒟₀₀) ⊆ 𝒟₀₀` and `F²(𝒟₀₀) ⊆ B`, are not
certified here). -/
theorem contraction_part :
    ∃ (lo hi : Fin 3 → ℝ) (κ : NNReal), κ < 1 ∧ Icc lo hi ⊆ openBoxOne ∧
      ∃ g : (Fin 3 → ℝ) → Fin 3 → ℝ, MapsTo g (Icc lo hi) (Icc lo hi) ∧
        LipschitzOnWith κ g (Icc lo hi) ∧
        ∀ p ∈ Icc lo hi, poincareAngZero (cellClass p) = cellClass (g p) :=
  ⟨bLoR, bHiR, 1 / 2, by norm_num, contraction_on_B⟩

end SmoothedPolygons.TriFuller.ContractionBox
