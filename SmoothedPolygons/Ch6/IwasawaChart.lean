module

public import SmoothedPolygons.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Iwasawa chart: the universal cover of `SL₂(ℝ)` in coordinates

To apply the maximum principle (proved on open subsets of a vector space, `External.Pontryagin`)
to the Reinhardt problem, the state space `SL₂(ℝ) × 𝔥*` is covered by one chart: the Iwasawa
coordinates `π(s, r, θ) = n_s a_r k_θ`, with `n_s = [[1, s], [0, 1]]`,
`a_r = diag(e^r, e^{-r})` and `k_θ = exp(θJ)` the rotation by `θ` (`iwasawa`). The map
`π : ℝ³ → SL₂(ℝ)` is smooth, onto (the Iwasawa decomposition, proved in
`SmoothedPolygons/Ch4/AdjointOrbit.lean` as the private `orb_iwasawa`), and identifies points
exactly when `s, r` agree and the angles differ by a multiple of `2π`; it is the universal
covering. Continuous curves in `SL₂(ℝ)` lift through `π` (path lifting through `ℝ → S¹` in the
angle; `s, r` are explicit), uniquely given the initial point.

The left-invariant field `g ↦ gX` lifts to `iwasawaField p X`: with `W = k_θ X k_θ⁻¹`,
`s' = e^{2r}(W₀₁ + W₁₀)`, `r' = W₀₀`, `θ' = W₁₀` (from `g⁻¹g' = k⁻¹(s'e^{-2r}E + r'H)k + θ'J`).
So a curve `g` with `g' = gX` lifts to a solution of `p' = iwasawaField p X`, and conversely
(`isIntegralCurve_lift`, `isIntegralCurve_iwasawa`).

This chart is the formalization's device (reading of the book's "smooth manifold `M`", §6.2,
TeX 4670; departure D1 of the Layer 1 plan); the book applies the PMP on `SL₂(ℝ) × 𝔰𝔩₂(ℝ)`
directly. Inventory §3.4 (`notes/plan_ch5_8_16/inventory.md`) explains why neither
`SL₂(ℝ) × 𝔰𝔩₂(ℝ)` nor `Mat₂ × 𝔥*` can be used as the state space (spurious multipliers, E21).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory
open scoped ContDiff

/-- The rotation `k_θ = exp(θJ) = [[cos θ, -sin θ], [sin θ, cos θ]]`. -/
noncomputable def iwasawaK (θ : ℝ) : Mat2 :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- The Iwasawa chart `π(s, r, θ) = n_s a_r k_θ` of `SL₂(ℝ)`, with `n_s = [[1, s], [0, 1]]`,
`a_r = diag(e^r, e^{-r})` and `k_θ` the rotation by `θ`; the point is `p = (s, r, θ)`. -/
noncomputable def iwasawa (p : ℝ × ℝ × ℝ) : Mat2 :=
  !![1, p.1; 0, 1] * !![Real.exp p.2.1, 0; 0, Real.exp (-p.2.1)] * iwasawaK p.2.2

/-- The lift of the left-invariant field `g ↦ gX` through the Iwasawa chart: with
`W = k_θ X k_θ⁻¹`, `(s', r', θ') = (e^{2r}(W₀₁ + W₁₀), W₀₀, W₁₀)`. -/
noncomputable def iwasawaField (p : ℝ × ℝ × ℝ) (X : Mat2) : ℝ × ℝ × ℝ :=
  (Real.exp (2 * p.2.1) * ((iwasawaK p.2.2 * X * iwasawaK (-p.2.2)) 0 1 +
      (iwasawaK p.2.2 * X * iwasawaK (-p.2.2)) 1 0),
    (iwasawaK p.2.2 * X * iwasawaK (-p.2.2)) 0 0, (iwasawaK p.2.2 * X * iwasawaK (-p.2.2)) 1 0)

/-- `π(0) = I`. -/
theorem iwasawa_zero : iwasawa 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iwasawa, iwasawaK, Matrix.mul_apply, Fin.sum_univ_two]

/-- `π` takes its values in `SL₂(ℝ)`. -/
theorem det_iwasawa (p : ℝ × ℝ × ℝ) : (iwasawa p).det = 1 := by
  rw [iwasawa, Matrix.det_mul, Matrix.det_mul]
  simp [iwasawaK, Matrix.det_fin_two, ← Real.exp_add, ← sq, Real.cos_sq_add_sin_sq]

/-- The entries of `π` are smooth. -/
theorem contDiff_iwasawa (i j : Fin 2) : ContDiff ℝ ∞ (fun p ↦ iwasawa p i j) := by
  sorry

/-- The Iwasawa decomposition: `π` is onto `SL₂(ℝ)` (from `orb_iwasawa`,
`SmoothedPolygons/Ch4/AdjointOrbit.lean`). -/
theorem iwasawa_surjective (g : Mat2) (hg : g.det = 1) : ∃ p, iwasawa p = g := by
  sorry

/-- The fibres of `π`: `π(p) = π(p')` if and only if `s, r` agree and the angles differ by a
multiple of `2π` (so `π` is the universal covering of `SL₂(ℝ)`). -/
theorem iwasawa_eq_iwasawa_iff (p p' : ℝ × ℝ × ℝ) :
    iwasawa p = iwasawa p' ↔
      p.1 = p'.1 ∧ p.2.1 = p'.2.1 ∧ ∃ n : ℤ, p'.2.2 = p.2.2 + 2 * Real.pi * n := by
  sorry

/-- The lifted field represents the left-invariant field: for traceless `X`,
`Dπ(p)(iwasawaField p X) = π(p) X`, entry by entry. -/
theorem fderiv_iwasawa_iwasawaField (p : ℝ × ℝ × ℝ) {X : Mat2} (hX : X.trace = 0) (i j : Fin 2) :
    fderiv ℝ (fun p ↦ iwasawa p i j) p (iwasawaField p X) = (iwasawa p * X) i j := by
  sorry

/-- **Path lifting** through the Iwasawa chart: a continuous curve in `SL₂(ℝ)` on `[0, T]` lifts
to a continuous curve in `ℝ³` from any point over its initial point. -/
theorem exists_continuousOn_lift {T : ℝ} (hT : 0 ≤ T) {g : ℝ → Mat2}
    (hg : ContinuousOn g (Icc 0 T)) (hdet : ∀ t ∈ Icc 0 T, (g t).det = 1) {p₀ : ℝ × ℝ × ℝ}
    (hp₀ : iwasawa p₀ = g 0) :
    ∃ p : ℝ → ℝ × ℝ × ℝ, ContinuousOn p (Icc 0 T) ∧ p 0 = p₀ ∧
      ∀ t ∈ Icc 0 T, iwasawa (p t) = g t := by
  sorry

/-- Uniqueness of lifts: two continuous curves on `[0, T]` with the same image under `π` and the
same initial point agree. -/
theorem eqOn_of_iwasawa_eq {T : ℝ} {p p' : ℝ → ℝ × ℝ × ℝ} (hp : ContinuousOn p (Icc 0 T))
    (hp' : ContinuousOn p' (Icc 0 T)) (h : ∀ t ∈ Icc 0 T, iwasawa (p t) = iwasawa (p' t))
    (h0 : p 0 = p' 0) : EqOn p p' (Icc 0 T) := by
  sorry

/-- The lift of a solution of `g' = gX` (Carathéodory) is a solution of
`p' = iwasawaField p X`, for `X` continuous and traceless. -/
theorem isIntegralCurve_lift {T : ℝ} (hT : 0 ≤ T) {g X : ℝ → Mat2}
    (hg : IsIntegralCurve g (fun t ↦ g t * X t) T) (hX : ContinuousOn X (Icc 0 T))
    (hXtr : ∀ t ∈ Icc 0 T, (X t).trace = 0) {p : ℝ → ℝ × ℝ × ℝ} (hp : ContinuousOn p (Icc 0 T))
    (hpg : ∀ t ∈ Icc 0 T, iwasawa (p t) = g t) :
    IntervalIntegrable (fun t ↦ iwasawaField (p t) (X t)) volume 0 T ∧
      ∀ t ∈ Icc 0 T, p t = p 0 + ∫ r in (0 : ℝ)..t, iwasawaField (p r) (X r) := by
  sorry

/-- Conversely, the image under `π` of a solution of `p' = iwasawaField p X` (Carathéodory), `X`
traceless, solves `g' = gX`. -/
theorem isIntegralCurve_iwasawa {T : ℝ} (hT : 0 ≤ T) {X : ℝ → Mat2}
    (hXtr : ∀ t ∈ Icc 0 T, (X t).trace = 0) {p : ℝ → ℝ × ℝ × ℝ} (hp : ContinuousOn p (Icc 0 T))
    (hint : IntervalIntegrable (fun t ↦ iwasawaField (p t) (X t)) volume 0 T)
    (hpeq : ∀ t ∈ Icc 0 T, p t = p 0 + ∫ r in (0 : ℝ)..t, iwasawaField (p r) (X r)) :
    IsIntegralCurve (fun t ↦ iwasawa (p t)) (fun t ↦ iwasawa (p t) * X t) T := by
  sorry

end SmoothedPolygons
