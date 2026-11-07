module

public import SmoothedPolygons.Ch3.StateDynamics

/-!
# Re-centering a balanced disk at a time `t₀` (proof of Theorem 5.0.2)

The proof of Theorem 5.0.2 applies Theorem 5.0.6, a statement about the multi-point `s_j*` at time
`0` of a balanced disk in circle representation, at every time `t₀` of the boundary trajectory
(TeX 4486–4489: "If any point of the trajectory `(g, X)` passes through a point `X = Φ(z)` …").
That step needs the re-centered disk, which the book does not state: for a balanced pair `(K, σ)`
with `σ_j(t) = g(t) s_j*` and `σ_j(t + t_f) = σ_{j+1}(t)`, the pair

  `K' = g(t₀)⁻¹ K`, `σ'_j(t) = g(t₀)⁻¹ σ_j(t + t₀) = g'(t) s_j*`, `g'(t) = g(t₀)⁻¹ g(t + t₀)`,

is again a balanced pair, in circle representation, with the same shift relation, the same area
(`det g(t₀) = 1`), and `g'⁻¹ g'' = X(· + t₀)`: its `X` at time `0` is `X(t₀)`
(`IsBalancedPair.recenter`).

## Proof (to be written)

`det g = 1` (the multi-point condition gives `det(g s₀*, g s₁*) = det(s₀*, s₁*)`), so `g(t₀)` is
invertible and area-preserving. Each condition of `IsBalancedPair` is invariant under a linear map
of determinant one (`IsCCSDisk`, `C¹` and regularity, Lipschitz derivatives, multi-points, the sign
of `det(σ', σ'')`, the star condition) and under a time shift (periodicity; injectivity on
`[0, 6t_f)` follows from injectivity on one period and periodicity, as in `oct_injOn_shift` of
`SmoothedPolygons/Ch7/SmoothedPolygonDisk.lean`; the image of a period is the image of any
period). The curve `g` is `C¹` with `det g = 1` (the private helper `sd_balanced` of
`SmoothedPolygons/Ch3/StateDynamics.lean`, behind Corollary 3.1.6, proves it; here it must be
re-derived, e.g. from the columns `g e₀ = σ₀` and `g e₁ = (2σ₁ - σ₀)/√3` of `g`), so
`derivEntrywise` commutes with the constant left factor and the time shift. Size: 250–450 lines.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix

/-- **Re-centering a balanced disk** (used without statement in the proof of Theorem 5.0.2,
TeX 4486–4489). Let `(K, σ)` be a balanced pair with `σ_j(t) = g(t) s_j*`, and `t₀ ∈ ℝ`. Then
`K' = g(t₀)⁻¹ K` with `σ'_j(t) = g(t₀)⁻¹ σ_j(t + t₀)` is a balanced pair in circle
representation, with `σ'_j(t) = g'(t) s_j*` for `g'(t) = g(t₀)⁻¹ g(t + t₀)`,
`g'(t)⁻¹ g''(t) = g(t + t₀)⁻¹ g'(t + t₀)`, and `area(K') = area(K)`. -/
theorem IsBalancedPair.recenter {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hKσ : IsBalancedPair K σ tf) {g : ℝ → Mat2} (hg : ∀ j t, σ j t = g t *ᵥ sixthRoot j)
    (t₀ : ℝ) :
    IsBalancedPair ((fun v ↦ (g t₀)⁻¹ *ᵥ v) '' K) (fun j t ↦ (g t₀)⁻¹ *ᵥ σ j (t + t₀)) tf ∧
      IsCircleRepresentation (fun j t ↦ (g t₀)⁻¹ *ᵥ σ j (t + t₀)) ∧
      (∀ j t, (g t₀)⁻¹ *ᵥ σ j (t + t₀) = ((g t₀)⁻¹ * g (t + t₀)) *ᵥ sixthRoot j) ∧
      (∀ t, ((g t₀)⁻¹ * g (t + t₀))⁻¹ * derivEntrywise (fun s ↦ (g t₀)⁻¹ * g (s + t₀)) t =
        (g (t + t₀))⁻¹ * derivEntrywise g (t + t₀)) ∧
      volume ((fun v ↦ (g t₀)⁻¹ *ᵥ v) '' K) = volume K := by
  sorry

end SmoothedPolygons
