module

public import SmoothedPolygons.Ch2.Mahler
public import External.Shifrin
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Boundary parameterization of the minimizer (§2.4)

The regularity of the multi-curve that parameterizes the boundary of a worst disk `K_min`
(Lemmas 2.4.2 and 2.4.3, Corollary 2.4.4), the star conditions and the curvature constraint for
a convex disk whose boundary is parameterized by a multi-curve (Lemmas 2.4.5 and 2.4.6), and the
balanced Reinhardt problem in circle representation (Problem 2.4.8). Multi-points, multi-curves
(Definition 2.4.1) and balanced pairs (Definition 2.4.7) are in `SmoothedPolygons.Ch2.MultiCurve`.

Conventions. As in §2.4, a parameterization of the boundary traverses it counterclockwise (the
*positive orientation*); for a curve `γ` on the boundary of a centrally symmetric convex disk, this
is `det(γ, γ') > 0`. Curves are defined on `ℝ`; `deriv` is the derivative, and the second
derivative `deriv (deriv γ)` is used only almost everywhere (where it exists). Euclidean norms are
written out: `‖v‖² = v₀² + v₁²`.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set

/-- `γ : ℝ → ℝ²` is a positively oriented regular `C¹` curve parameterizing the boundary of `K`
(§2.4): `γ` is `C¹` with nonvanishing derivative, its image is the boundary of `K`, and it turns
counterclockwise about the origin. -/
def IsPositiveBoundaryParam (K : Set (Fin 2 → ℝ)) (γ : ℝ → Fin 2 → ℝ) : Prop :=
  ContDiff ℝ 1 γ ∧ (∀ t, deriv γ t ≠ 0) ∧ range γ = frontier K ∧
    ∀ t, 0 < det2 (γ t) (deriv γ t)

/-- The boundary of `K` is parameterized by the `C¹` regular multi-curve `σ` (§2.4,
Lemmas 2.4.5 and 2.4.6): each `σ_j` is a positively oriented regular `C¹` parameterization of the
boundary of `K`, and `j ↦ σ_j(t)` is a multi-point for every `t`. -/
def IsBoundaryMultiCurve (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) : Prop :=
  (∀ j, IsPositiveBoundaryParam K (σ j)) ∧ ∀ t, IsMultiPoint fun j ↦ σ j t

/-! ### Regularity of multi-curves -/

/-- **Lemma 2.4.2** (Hales 2011; `lem:sigma2:c1`). Let `K = K_min ∈ 𝔎_ccs` be a centrally symmetric
convex disk that has the worst greatest packing density. Consider a `C⁰` multi-curve
parameterization `σ` of its boundary. If `t ↦ σ₀(t)` is a positively oriented `C¹` regular curve
parameterizing the boundary of `K`, then so is `σ_j(t)` for `j = 1, …, 5`. -/
theorem lemma2_4_2 {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hσc : ∀ j, Continuous (σ j)) (hσm : ∀ t, IsMultiPoint fun j ↦ σ j t)
    (hσK : ∀ j t, σ j t ∈ frontier K) (hσ₀ : IsPositiveBoundaryParam K (σ 0)) :
    ∀ j, IsPositiveBoundaryParam K (σ j) := by
  sorry

/-- **Lemma 2.4.3** (Hales 2011, Lemmas 17 and 18; `lem:tangents-lipschitz`). Let `σ` be a `C¹`
multi-curve parameterization of the boundary of `K = K_min ∈ 𝔎_ccs`, giving worst greatest packing
density. Assume that the curve `σ₀` is parameterized according to arclength. Then the tangents
`σ_j'` are Lipschitz continuous for all `j`. -/
theorem lemma2_4_3 {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hσ : ∀ j, ContDiff ℝ 1 (σ j)) (hσm : ∀ t, IsMultiPoint fun j ↦ σ j t)
    (hσK : ∀ j t, σ j t ∈ frontier K) (hσ₀ : range (σ 0) = frontier K)
    (harc : ∀ t, deriv (σ 0) t 0 ^ 2 + deriv (σ 0) t 1 ^ 2 = 1) :
    ∀ j, ∃ C, LipschitzWith C (deriv (σ j)) := by
  sorry

/-- **Corollary 2.4.4** (`lem:multi-curve-c2`). Under the hypotheses of Lemma 2.4.3, the functions
`σ_j'(t)` are differentiable almost everywhere. -/
theorem corollary2_4_4 {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hσ : ∀ j, ContDiff ℝ 1 (σ j)) (hσm : ∀ t, IsMultiPoint fun j ↦ σ j t)
    (hσK : ∀ j t, σ j t ∈ frontier K) (hσ₀ : range (σ 0) = frontier K)
    (harc : ∀ t, deriv (σ 0) t 0 ^ 2 + deriv (σ 0) t 1 ^ 2 = 1) :
    ∀ j, ∀ᵐ t, DifferentiableAt ℝ (deriv (σ j)) t := by
  intro j
  obtain ⟨C, hC⟩ := lemma2_4_3 hK hσ hσm hσK hσ₀ harc j
  exact LipschitzWith.ae_differentiableAt (μ := volume) hC

/-! ### Convexity of multi-curves -/

/-- **Lemma 2.4.5** (star conditions; `lem:star-conditions`). Let `K ∈ 𝔎_ccs` be a convex disk with
boundary parameterized by the `C¹` regular multi-curve `σ`. At a given time `t`, let
`j ↦ s_j = σ_j(t)` be a multi-point on the boundary of `K`. Then for each `j` and time `t`, the
tangent `σ_j'(t)` points into the open cone with apex `s_j` and bounding rays through `s_{j+1}` and
`s_j + s_{j+1}`: `σ_j'(t) = α (s_{j+1} - s_j) + β s_{j+1}` with `α, β > 0`. -/
theorem lemma2_4_5 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hσ : IsBoundaryMultiCurve K σ) (j : ZMod 6) (t : ℝ) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      deriv (σ j) t = α • (σ (j + 1) t - σ j t) + β • σ (j + 1) t := by
  sorry

/-- **Lemma 2.4.6** (curvature constraint; `lem:local-curvature-constrt`, equation
`eqn:local-convexity`). Consider a convex disk `K ∈ 𝔎_ccs` with boundary parameterized by a `C¹`
regular multi-curve `σ` with Lipschitz continuous derivative. Then almost everywhere
`det(σ_j'(t), σ_j''(t)) ≥ 0` for `j ∈ ℤ/6ℤ`. -/
theorem lemma2_4_6 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hσ : IsBoundaryMultiCurve K σ) (hlip : ∀ j, ∃ C, LipschitzWith C (deriv (σ j)))
    (j : ZMod 6) : ∀ᵐ t, 0 ≤ det2 (deriv (σ j) t) (deriv (deriv (σ j)) t) := by
  sorry

/-! ### The balanced Reinhardt problem -/

/-- **Problem 2.4.8** (balanced Reinhardt problem in circle representation;
`pbm:reinhardt-reduction-2`). Describe those `K_min ∈ 𝔎_bal` in circle representation for which
`area(K_min) = inf {area(K) | K ∈ 𝔎_bal in circle representation}`. This predicate says that `K`
is such a minimizer: it is a balanced disk in circle representation whose area is at most that of
every balanced disk in circle representation. -/
def IsBalancedCircleMinimizer (K : Set (Fin 2 → ℝ)) : Prop :=
  (∃ σ tf, IsBalancedPair K σ tf ∧ IsCircleRepresentation σ) ∧
    ∀ K' σ' tf', IsBalancedPair K' σ' tf' → IsCircleRepresentation σ' → volume K ≤ volume K'

end SmoothedPolygons
