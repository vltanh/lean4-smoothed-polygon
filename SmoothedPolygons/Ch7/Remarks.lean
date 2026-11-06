module

public import SmoothedPolygons.Ch7.StrongTransversality
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Remarks on the smoothed polygons (Remarks 7.5.2 and 7.6.4)

* Remark 7.5.2: along the strong lift of Theorem 7.5.1 (normalized by `λ_cost = -1`),
  `d(y₀) = det Λ₁(t) = λ₁² det Λ₁₀` is a constant of motion with an explicit formula; it is strictly
  increasing in `y₀ ∈ (1/√3, 1)` with range `(0, 9/4)`, so it determines `y₀`.
* Remark 7.6.4: the smoothed `(6k - 2)`-gons of Remark 7.6.2, with `k` allowed to be real, tend to a
  rectangle of area `√12` as `k → 1⁺`.

## The smoothed `(6k - 2)`-gons (Remark 7.6.2)

The book specifies them by the control mode sequence `((1, t_sw), (2, t_sw), …, (3k - 1, t_sw))`
(`eqn:3k+2`), the initial point `z₀ = i y₀` with `y₀ > 1`, the switching time
`t_sw = -ln(4/(3y₀² + 1))/(√3 y₀)` and the initial control `e₂`. As in `eqn:3k+1` (where the mode
`-i` is the control `R⁻ⁱ · e₃`), the mode `m` is the control `R^m · e₃`; so the controls are
`e₂, e₁, e₃, e₂, …` (`R · e₃ = e₂`, `R · e₂ = e₁`, `R · e₁ = e₃`, `R_conj_controlMatrix_vertex`),
and the terminal time is `t_f = (3k - 1) t_sw`.

The book does not display the condition that fixes `y₀` in terms of `k` ("the changes are minor").
It is the analogue of Lemma 7.5.5 (`eqn:theta-k`): with control `e₂`, `z(t_sw) = R · z₀`, the
trajectory is `g(t) = (g_sw R)ⁱ g₀(t - i t_sw) R⁻ⁱ` on the `i`-th switching interval, and
`g(t_f) = R` reads `(g_sw R)^{3k-1} = R^{3k} = (-1)ᵏ`; since `tr(g_sw R) = 4/(3y₀² + 1)`, the choice
of eigenvalues of Lemma 7.5.5 gives `4/(3y₀² + 1) = 2 cos(πk/(3k - 1))` (checked numerically:
`g(t_f) = R` for `k = 2, 3`). For real `k > 1` this defines `y₀(k) > 1`; as `k → 1⁺`,
`y₀(k) → ∞`, which is how the `(6k - 2)`-gon "degenerates" at `k = 1`. For non-integral `k`, the
trajectory on `[0, t_f]` does not satisfy the boundary condition `g(t_f) = R` ("smoothed rectangles
that do not quite satisfy the boundary conditions").
-/

@[expose] public section

namespace SmoothedPolygons

open Filter Topology Matrix

/-! ### Remark 7.5.2 -/

/-- The constant of motion of Remark 7.5.2,
`d(y₀) = (-1 + 2y₀² + 3y₀⁴)(3 + 6y₀² - (1 + 3y₀²) ℓ(y₀))² / (144 y₀⁸)`, where
`ℓ(y₀) = ln(4/(3y₀² + 1))`. -/
noncomputable def detConstOfMotion (y0 : ℝ) : ℝ :=
  (-1 + 2 * y0 ^ 2 + 3 * y0 ^ 4) *
    (3 + 6 * y0 ^ 2 - (1 + 3 * y0 ^ 2) * Real.log (4 / (3 * y0 ^ 2 + 1))) ^ 2 / (144 * y0 ^ 8)

/-- `det(λ₁ Λ₁₀) = d(y₀)`: the algebra of Remark 7.5.2. -/
private lemma r3_strongL₁_sq_det (y0 : ℝ) (hy0 : 0 < y0) :
    strongL₁ y0 ^ 2 * (Λ₁₀ y0).det = detConstOfMotion y0 := by
  have h3' : √3 ≠ 0 := by positivity
  have hy : y0 ≠ 0 := hy0.ne'
  have h13 : 1 + 3 * y0 ^ 2 ≠ 0 := by positivity
  simp only [strongL₁, ellSw, Λ₁₀, detConstOfMotion, Matrix.det_smul, Matrix.det_fin_two_of,
    Fintype.card_fin]
  field_simp
  ring_nf

/-- **Remark 7.5.2** (`rem:det-lambda1`, label of this formalization). Let `y₀ ∈ (1/√3, 1)` and
let `(Λ₁, Λ_R, λ_cost = -1)` be the costate lift of Theorem 7.5.1 (`IsStrongLift`). Then
`d = d(y₀) := det Λ₁(t) = λ₁² det Λ₁₀` is a constant of motion, equal to
`(-1 + 2y₀² + 3y₀⁴)(3 + 6y₀² - (1 + 3y₀²) ℓ(y₀))² / (144 y₀⁸)` with `ℓ(y₀) = ln(4/(3y₀² + 1))`, for
all times `t ∈ [0, t_sw]`. The function `d` is monotonic increasing in `y₀ ∈ (1/√3, 1)` with range
`(0, 9/4)`; thus the determinant uniquely determines the parameter `y₀` of the triangle.

Reading: "monotonic increasing" is strict monotonicity (`StrictMonoOn`), which is what the last
sentence (`d` determines `y₀`, `Set.InjOn`) needs; the remark is about the lift normalized by
`λ_cost = -1` (for the lift `c (Λ₁, Λ_R, -1)` the determinant is `c² d(y₀)`). -/
theorem remark7_5_2 :
    (∀ y0 : ℝ, 1 / √3 < y0 → y0 < 1 → ∀ Λ₁ ΛR : ℝ → Mat2, IsStrongLift y0 Λ₁ ΛR (-1) →
      ∀ t ∈ Set.Icc 0 (switchTime y0),
        (Λ₁ t).det = strongL₁ y0 ^ 2 * (Λ₁₀ y0).det ∧ (Λ₁ t).det = detConstOfMotion y0) ∧
    StrictMonoOn detConstOfMotion (Set.Ioo (1 / √3) 1) ∧
    detConstOfMotion '' Set.Ioo (1 / √3) 1 = Set.Ioo 0 (9 / 4) ∧
    Set.InjOn detConstOfMotion (Set.Ioo (1 / √3) 1) := by
  have hmono : StrictMonoOn detConstOfMotion (Set.Ioo (1 / √3) 1) := by
    sorry
  refine ⟨fun y0 hy0 hy1 Λ₁ ΛR h t ht ↦ ?_, hmono, ?_, hmono.injOn⟩
  · have hy0' : 0 < y0 := lt_trans (by positivity) hy0
    have hdet1 : (segG y0 t).det = 1 := (seg_solution y0 0 hy0').2.2.2.2 t
    have hΛ : (Λ₁ t).det = strongL₁ y0 ^ 2 * (Λ₁₀ y0).det := by
      rw [(strongLift_unique y0 hy0 hy1 Λ₁ ΛR (-1) h t ht).1, neg_neg, one_smul, strongΛ₁,
        Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, hdet1, Ring.inverse_one,
        Matrix.det_smul, Fintype.card_fin]
      ring
    exact ⟨hΛ, hΛ.trans (r3_strongL₁_sq_det y0 hy0')⟩
  · sorry

/-! ### The smoothed `(6k - 2)`-gons (Remark 7.6.2) and Remark 7.6.4 -/

/-- The switching time `t_sw = -ln(4/(3y₀² + 1))/(√3 y₀)` of the smoothed `(6k - 2)`-gon
(Remark 7.6.2; positive for `y₀ > 1`). -/
noncomputable def minusSwitchTime (y0 : ℝ) : ℝ := -Real.log (4 / (3 * y0 ^ 2 + 1)) / (√3 * y0)

/-- The control of the smoothed `(6k - 2)`-gon with switching time `τ` (`eqn:3k+2`): on the
`i`-th switching interval `[iτ, (i+1)τ)` it is the mode `i + 1`, the vertex `R^{i+1} · e₃ = Rⁱ · e₂`
of `U_T`; so the controls are `e₂, e₁, e₃, e₂, …`, that is, `Pi.single ((1 + 2i) mod 3) 1`. -/
noncomputable def minusPolygonControlAt (τ t : ℝ) : Fin 3 → ℝ :=
  Pi.single (⟨(1 + 2 * ⌊t / τ⌋₊) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) 1

/-- The angle `πk/(3k - 1)` of the smoothed `(6k - 2)`-gon, for real `k`. -/
noncomputable def minusθ (k : ℝ) : ℝ := Real.pi * k / (3 * k - 1)

/-- The height `y₀(k)` of the initial point `z₀ = i y₀` of the smoothed `(6k - 2)`-gon, for real
`k > 1`: the positive solution of `4/(3y₀² + 1) = 2 cos(πk/(3k - 1))` (the analogue of
`eqn:theta-k`, see the module docstring). -/
noncomputable def minusY₀ (k : ℝ) : ℝ := √((2 / Real.cos (minusθ k) - 1) / 3)

/-- The terminal time `t_f = (3k - 1) t_sw` of the smoothed `(6k - 2)`-gon, for real `k`. -/
noncomputable def minusTf (k : ℝ) : ℝ := (3 * k - 1) * minusSwitchTime (minusY₀ k)

/-- **Remark 7.6.4** (`rem:6k-2-rectangle`, label of this formalization). When `k = 1`, the
smoothed `(6k - 2)`-gon degenerates to a rectangle with corners and area `√12`. Allowing `k` to be
non-integral, for small values of `k > 1`, we obtain smoothed rectangles (that do not quite
satisfy the boundary conditions); the figure (TeX 6435: "the shape appears to be tending to a
rectangle of area `√12` as `k ↦ 1`").

Reading. At `k = 1` the closing condition `4/(3y₀² + 1) = 2 cos(π/2) = 0` has no solution
(`y₀ = ∞`), so "when `k = 1`" is read as the limit `k → 1⁺` of the interpolated `(6k - 2)`-gons:
for real `k > 1`, the state trajectory `(g_k, X_k)` on `[0, t_f(k)]` with the control of
`eqn:3k+2`, switching time `t_sw(y₀(k))`, `g_k(0) = I` and `X_k(0) = Φ(i y₀(k))` (Remark 7.6.2).
The claims: (1) its cost, the area of §3.2, tends to `√12`; (2) its six arcs
`σ_j([0, t_f(k)])`, `σ_j(t) = g_k(t) s_j*`, tend in the Hausdorff distance to the boundary of a
rectangle (image of `[-a, a] × [-b, b]` under a Euclidean motion) of area `4ab = √12`. (The
rectangle is `[-1, 1] × [-√3/2, √3/2]`, by the figure; the statement only asserts a rectangle, as
the remark does. Hausdorff convergence does not depend on the metric of `ℝ²`, Mathlib's being the
sup metric.) The trajectories are quantified universally; they exist and are unique. -/
theorem remark7_6_4 (g X : ℝ → ℝ → Mat2)
    (hgX : ∀ k : ℝ, 1 < k →
      IsStateTrajectory (minusTf k) (minusPolygonControlAt (minusSwitchTime (minusY₀ k)))
        (g k) (X k) ∧ g k 0 = 1 ∧ X k 0 = Φ 0 (minusY₀ k)) :
    Tendsto (fun k ↦ reinhardtCost (minusTf k) (X k)) (𝓝[>] 1) (𝓝 √12) ∧
      ∃ (A : Mat2) (c : Fin 2 → ℝ) (a b : ℝ), A ∈ Matrix.orthogonalGroup (Fin 2) ℝ ∧
        0 < a ∧ 0 < b ∧ 4 * a * b = √12 ∧
        Tendsto (fun k ↦ Metric.hausdorffEDist
            (⋃ j : ZMod 6, (fun t ↦ g k t *ᵥ sixthRoot j) '' Set.Icc 0 (minusTf k))
            (frontier ((fun x ↦ A *ᵥ x + c) '' {x : Fin 2 → ℝ | |x 0| ≤ a ∧ |x 1| ≤ b})))
          (𝓝[>] 1) (𝓝 0) := by
  sorry

end SmoothedPolygons
