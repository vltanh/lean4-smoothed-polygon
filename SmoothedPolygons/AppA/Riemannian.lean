module

public import SmoothedPolygons.Ch4.AdjointOrbit

/-!
# The Riemannian metric on the coadjoint orbit (Appendix A.11)
-/

@[expose] public section

namespace SmoothedPolygons

/-- **Lemma A.11.1** (`lem:riemannian`). The symmetric bilinear form on `T_z𝔥` determined by the
trace form on `𝔭_X = X^⊥ ≅ T_X O_J` (via `r ↦ [Y_z(r), X]`, Lemma 4.2.4) is twice the invariant
Riemannian metric of the upper half-plane: `⟨[Y_z(r), X], [Y_z(r'), X]⟩ = 2(r₁r₁' + r₂r₂')/y²`. -/
theorem lemmaA_11_1 (x y r₁ r₂ r₁' r₂' : ℝ) (hy : 0 < y) :
    traceForm (tangentLift x y r₁ r₂ * Φ x y - Φ x y * tangentLift x y r₁ r₂)
        (tangentLift x y r₁' r₂' * Φ x y - Φ x y * tangentLift x y r₁' r₂') =
      2 * (r₁ * r₁' + r₂ * r₂') / y ^ 2 := by
  sorry

end SmoothedPolygons
