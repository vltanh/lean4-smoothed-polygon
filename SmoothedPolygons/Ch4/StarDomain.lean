module

public import SmoothedPolygons.Ch3.ControlSets
public import SmoothedPolygons.Ch4.AdjointOrbit

/-!
# The star domain and the half-plane control problem (§4.4–§4.6)

The star inequalities on `X = Φ(x + iy)` cut out the ideal triangle `𝔥*` (Theorem 4.4.1); the
dynamics of `X` becomes an ODE for `(x, y)` (Problem 4.5.1, Lemma 4.5.2); and the dihedral group of
the hexagon acts compatibly on the controls, the star functions and the upper half-plane (§4.6).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- The star domain `𝔥* = {x + iy | y > 0, -1/√3 < x < 1/√3, x² + y² > 1/3}`, an ideal
triangle in the upper half-plane (`eqn:star`), as a subset of `ℝ × ℝ`. -/
def starDomain : Set (ℝ × ℝ) :=
  {p | 0 < p.2 ∧ -(1 / √3) < p.1 ∧ p.1 < 1 / √3 ∧ 1 / 3 < p.1 ^ 2 + p.2 ^ 2}

/-- **Theorem 4.4.1** (`prop:star-domain`). The star inequalities on `X = Φ(x + iy)` hold exactly
on the ideal triangle `𝔥*`; so the state space of the control problem is `SL₂(ℝ) × 𝔥*`.
(`Φ(z)` always has trace zero and determinant one.) -/
theorem theorem4_4_1 (x y : ℝ) (hy : 0 < y) : IsStarState (Φ x y) ↔ (x, y) ∈ starDomain := by
  sorry

/-- The right-hand side `f₁(x, y; u) = y(2ax + b - cx² + cy²)/(2ax + b - cx² - cy²)` of the
half-plane control problem (Problem 4.5.1), where `Z_u = [[a, b], [c, -a]]`.

Problem 4.5.1 prints `a = (u₂ - u₁)/√3`, the negative of the entry `(u₁ - u₂)/√3` of `Z_u` in
`eqn:trisystem-Z0` to which it refers; with the printed sign Lemma 4.5.2 fails. The entries of
`Z_u` are used here. -/
noncomputable def halfPlaneF₁ (x y : ℝ) (u : Fin 3 → ℝ) : ℝ :=
  y * (2 * controlMatrix u 0 0 * x + controlMatrix u 0 1 - controlMatrix u 1 0 * x ^ 2 +
      controlMatrix u 1 0 * y ^ 2) /
    (2 * controlMatrix u 0 0 * x + controlMatrix u 0 1 - controlMatrix u 1 0 * x ^ 2 -
      controlMatrix u 1 0 * y ^ 2)

/-- The right-hand side `f₂(x, y; u) = 2y²(a - cx)/(2ax + b - cx² - cy²)` of the half-plane control
problem (Problem 4.5.1), where `Z_u = [[a, b], [c, -a]]` (see `halfPlaneF₁` for the sign of `a`). -/
noncomputable def halfPlaneF₂ (x y : ℝ) (u : Fin 3 → ℝ) : ℝ :=
  2 * y ^ 2 * (controlMatrix u 0 0 - controlMatrix u 1 0 * x) /
    (2 * controlMatrix u 0 0 * x + controlMatrix u 0 1 - controlMatrix u 1 0 * x ^ 2 -
      controlMatrix u 1 0 * y ^ 2)

/-- **Lemma 4.5.2** (`lem:X-dynamics`). If `X = Φ(x + iy)` follows `X' = [Z_u, X]/⟨Z_u, X⟩`, then
`x' = f₁(x, y; u)` and `y' = f₂(x, y; u)`; moreover `T Φ(f₁, f₂)` is the class of
`Z_u/⟨Z_u, X⟩` (`eqn:tangent-map-f1f2`): `[Y_z(f₁, f₂), X] = [Z_u/⟨Z_u, X⟩, X]`. -/
theorem lemma4_5_2 (x y : ℝ → ℝ) (u : Fin 3 → ℝ) (t x' y' : ℝ)
    (hstar : (x t, y t) ∈ starDomain) (hu : u ∈ controlSimplex)
    (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t)
    (hX : HasDerivAtEntrywise (fun s ↦ Φ (x s) (y s))
      (controlP u (Φ (x t) (y t)) * Φ (x t) (y t) - Φ (x t) (y t) * controlP u (Φ (x t) (y t))) t) :
    x' = halfPlaneF₁ (x t) (y t) u ∧ y' = halfPlaneF₂ (x t) (y t) u ∧
      tangentLift (x t) (y t) x' y' * Φ (x t) (y t) -
          Φ (x t) (y t) * tangentLift (x t) (y t) x' y' =
        controlP u (Φ (x t) (y t)) * Φ (x t) (y t) -
          Φ (x t) (y t) * controlP u (Φ (x t) (y t)) := by
  sorry

/-! ### Dihedral symmetry (§4.6) -/

/-- The reflection `S = [[-1, 0], [0, 1]]` across the vertical axis (§4.6). -/
def reflS : Mat2 := !![-1, 0; 0, 1]

/-- §4.6: the rotation `R` permutes the control matrices of the vertices of `U_T`:
`R Z_{e₃} R⁻¹ = Z_{e₂}`, `R Z_{e₂} R⁻¹ = Z_{e₁}`, `R Z_{e₁} R⁻¹ = Z_{e₃}`. -/
theorem R_conj_controlMatrix_vertex :
    R * controlMatrix (vertex 2) * R⁻¹ = controlMatrix (vertex 1) ∧
      R * controlMatrix (vertex 1) * R⁻¹ = controlMatrix (vertex 0) ∧
      R * controlMatrix (vertex 0) * R⁻¹ = controlMatrix (vertex 2) := by
  sorry

/-- §4.6: the rotation permutes the star functions, `ρ_j(R X R⁻¹) = ρ_{j-1}(X)` (indices mod 3),
for `X ∈ 𝔰𝔩₂(ℝ)`. -/
theorem ρ_R_conj (X : Mat2) (hX : X.trace = 0) :
    ρ₀ (R * X * R⁻¹) = ρ₂ X ∧ ρ₁ (R * X * R⁻¹) = ρ₀ X ∧ ρ₂ (R * X * R⁻¹) = ρ₁ X := by
  sorry

/-- §4.6: the reflection acts on `Φ` by `z ↦ -z̄`: `ε_S S Φ(z) S⁻¹ = Φ(-z̄)`, where
`ε_S = det S = -1`. -/
theorem reflS_conj_Φ (x y : ℝ) (hy : 0 < y) : -(reflS * Φ x y * reflS⁻¹) = Φ (-x) y := by
  sorry

/-- §4.6: the reflection permutes the star functions, `ρ_j(ε_S S X S⁻¹) = ρ_{1-j}(X)`
(indices mod 3), for `X ∈ 𝔰𝔩₂(ℝ)`. -/
theorem ρ_reflS_conj (X : Mat2) (hX : X.trace = 0) :
    ρ₀ (-(reflS * X * reflS⁻¹)) = ρ₁ X ∧ ρ₁ (-(reflS * X * reflS⁻¹)) = ρ₀ X ∧
      ρ₂ (-(reflS * X * reflS⁻¹)) = ρ₂ X := by
  sorry

/-- §4.6: the reflection acts on the control matrices of the vertices by
`-S Z_{e₂} S⁻¹ = Z_{e₃}`, `-S Z_{e₃} S⁻¹ = Z_{e₂}`, `-S Z_{e₁} S⁻¹ = Z_{e₁}`. -/
theorem reflS_conj_controlMatrix_vertex :
    -(reflS * controlMatrix (vertex 1) * reflS⁻¹) = controlMatrix (vertex 2) ∧
      -(reflS * controlMatrix (vertex 2) * reflS⁻¹) = controlMatrix (vertex 1) ∧
      -(reflS * controlMatrix (vertex 0) * reflS⁻¹) = controlMatrix (vertex 0) := by
  sorry

end SmoothedPolygons
