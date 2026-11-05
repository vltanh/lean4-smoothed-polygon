module

public import SmoothedPolygons.Ch3.ControlSets

/-!
# Lie algebra dynamics (§3.4)

Elementary identities in `𝔰𝔩₂(ℝ)` (Lemma 3.4.1) and the control-dependent dynamics
`X' = [Z_u, X]/⟨Z_u, X⟩` (Theorem 3.4.2).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Matrix

/-- **Lemma 3.4.1** (`lem:sl2-lemmas`). For matrices in `𝔰𝔩₂(ℝ)`:
1. `⟨X, X⟩ = -2 det X`;
2. if `det(s_j, X s_j) = det(s_j, Y s_j)` for `j = 0, 1, 2` and a multi-point `s`, then `X = Y`;
3. `XY + YX = ⟨X, Y⟩ I₂`;
4. `⟨X, [Y, Z]⟩ = ⟨[X, Y], Z⟩`. -/
theorem lemma3_4_1 :
    (∀ X : Mat2, X.trace = 0 → traceForm X X = -2 * X.det) ∧
    (∀ X Y : Mat2, X.trace = 0 → Y.trace = 0 → ∀ s : ZMod 6 → Fin 2 → ℝ, IsMultiPoint s →
      (∀ j ∈ ({0, 1, 2} : Finset (ZMod 6)), det2 (s j) (X *ᵥ s j) = det2 (s j) (Y *ᵥ s j)) →
      X = Y) ∧
    (∀ X Y : Mat2, X.trace = 0 → Y.trace = 0 → X * Y + Y * X = traceForm X Y • (1 : Mat2)) ∧
    (∀ X Y Z : Mat2, X.trace = 0 → Y.trace = 0 → Z.trace = 0 →
      traceForm X (Y * Z - Z * Y) = traceForm (X * Y - Y * X) Z) := by
  sorry

/-- **Theorem 3.4.2** (`thm:X-dynamics-sl2`). Let `g : [0, t_f] → SL₂(ℝ)` be `C¹` with Lipschitz
derivative, `X = g⁻¹g'` with `det X = 1` (the parameterization of Proposition 3.1.9), satisfying the
star inequalities and the curvature conditions `κ_j ≥ 0` almost everywhere, and let `u` be the
control variables (Definition 3.3.2). Then almost everywhere `X' = [Z_u, X]/⟨Z_u, X⟩`. -/
theorem theorem3_4_2 (tf : ℝ) (g g' : ℝ → Mat2)
    (hg : ∀ t ∈ Set.Icc 0 tf, HasDerivWithinAtEntrywise g (g' t) (Set.Icc 0 tf) t)
    (hdet : ∀ t ∈ Set.Icc 0 tf, (g t).det = 1) (hLip : LipschitzOnEntrywise g' (Set.Icc 0 tf))
    (X : ℝ → Mat2) (hX : ∀ t, X t = (g t)⁻¹ * g' t) (hX1 : ∀ t ∈ Set.Icc 0 tf, (X t).det = 1)
    (hstar : ∀ t ∈ Set.Icc 0 tf, 0 < ρ₀ (X t) ∧ 0 < ρ₁ (X t) ∧ 0 < ρ₂ (X t))
    (hcurv : ∀ᵐ t, t ∈ Set.Ioo 0 tf → ∀ j, 0 ≤ stateCurvature (X t) (derivEntrywise X t) j)
    (u : ℝ → Fin 3 → ℝ)
    (hu : ∀ t, u t = controlVariables (stateCurvature (X t) (derivEntrywise X t))) :
    ∀ᵐ t, t ∈ Set.Ioo 0 tf → HasDerivAtEntrywise X
      ((traceForm (controlMatrix (u t)) (X t))⁻¹ •
        (controlMatrix (u t) * X t - X t * controlMatrix (u t))) t := by
  sorry

end SmoothedPolygons
