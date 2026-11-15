module

public import SmoothedPolygons.Ch14.ArcCostate

/-!
# Chapter 14, N4: the normal form of the cleared switching numerators (Theorem 1.3)

`notes/n4/proof.md` §1.3: along the `e₂`-arc from a phase point with `X₀ ∈ 𝔥*` and `H(e₂) = 0`,
each cleared switching numerator is an exponential sum with exactly four terms and three
universal coefficients, in the time `τ = t/ε`:
`(√3/(8ε³)) N₂₁(t) = f(τ) = -1 + A e^{-τ} + B e^{-2τ} + Y τ e^{-τ}`,
`(√3/(8ε³)) N₂₃(t) = g(τ) = -1 + A' e^{τ} + B' e^{2τ} - Y' τ e^{τ}`,
with `B = Y - 1 + q`, `A = 1 + f₀ - B`, `B' = Y' - 1 + p`, `A' = 1 + g₀ - B'` (`ArcParams.f`,
`ArcParams.g`). On a section point `g₀ = 0` and `f₀ = -(√3/(3ε³Y')) ⟨Λ̂₀, X₀⟩` (1.5). Part of the
reduction of N4 to (INV) (`ArcRegionInvariant`).

**Departure from the paper.** The book computes the unstable curve numerically (Figure 14.2,
TeX 11951–11991); the formalization proves N4 from (INV) by the exact structure of the arcs (see
`SmoothedPolygons/Ch14/ArcParams.lean`). This sharpens the earlier description of the numerators
(`SmoothedPolygons/Ch14/UnstableCurve.lean`, module docstring: "exponential polynomials
`Σ c_{mk} t^m e^{2kωt}`, `m ≤ 2`, `|k| ≤ 3`"): only four terms occur.

## Statements

* `arcF0`, `arcG0`, `arcQ`, `arcP`, `arcParams`: the arc parameters of a phase point
  (`f₀ = (√3/(8ε³)) N₂₁(q)`, `g₀ = (√3/(8ε³)) N₂₃(q)`, `q = -(√3/(6ε)) ⟨Λ̂₀, V_e⟩`,
  `p = (2/(√3 ε)) ⟨Λ̂₀, V_f⟩`, `Λ̂₀ = Λ₁(0) + (3/2) J`).
* `arcParams_Y'` (`Y'` of the parameters is `1 + ρ₀/ε`), `arcParams_radius` (`r = X₁₁`).
* **Theorem 1.3** (`arc_normalForm`). Equivalently (1.4) (`ArcParams.f_eq`, `ArcParams.g_eq`).
* **(1.5)** on section points: `frame_section_costateR` (`Λ_R` in the frame:
  `m_h = -ε h₀`, `m_f = h₀ x_f`, `m_e = h₀ (1 - ε²)/x_f`, `h₀ = ⟨Λ̂₀, X₀⟩`), `arcG0_eq_zero`,
  `arcF0_eq_reducedHam`, `arcParams_A'` (`A' = 2 - Y' - p`), `arcF0_pos_iff` (P1, `f₀ > 0`, says
  that the reduced Hamiltonian `⟨Λ₁ + (3/2) J, X⟩` is negative at the section point).

## Proofs (the route, proof.md §1.3)

1. `arcParams_Y'`: (1.3) (`arcEps_sq_mul_arcY_mul_arcY'`). `arcParams_radius`:
   `X00_eq_arcRadius`.
2. Theorem 1.3. By `switchingNum_iso_vertexFlow_one`, `(√3/(8ε³)) N₂₁(t) = -(√3/(12ε²)) u φ_e(t)`
   with `u = e^{-t/ε}`. By `hasDerivAt_arcPhi`, `traceForm_iso_vfM_arcVe` and the fundamental
   theorem of calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt`, the integrand is
   continuous), with `L_e = ⟨Λ₁(0), V_e⟩`,
   `φ_e(t) = φ_e(0) - 2ε(1 - u) L_e + √3(2x_e t + x_e²(1 - u) + 4ε²(u⁻¹ - 1))`
   (`∫₀ᵗ u = ε(1 - u)`, `∫₀ᵗ u⁻¹ = ε(u⁻¹ - 1)`). Multiplying by `-(√3/(12ε²)) u` gives four terms:
   the constant `-1`, the term `-(x_e/(2ε²)) t u = Y τ u` (`x_e = -2εY`), a `u²` and a `u` term.
   At `t = 0` the sum is `f₀` (definition of `arcF0`), so the `u` coefficient is `1 + f₀ - B`
   once the `u²` coefficient is `B`; the `u²` coefficient is `-(√3/(6ε))(L_e - √3 x_e²/(2ε))`,
   and with `Λ₁(0) = Λ̂₀ - (3/2) J` and `⟨J, V_e⟩ = -(4ε/√3)(Y² - Y + 1)` (from (1.2),
   `traceForm_ofFrame`, `x_e = -2εY`) it is `Y - 1 + q`. The `N₂₃` computation is the same with
   `φ_f`, `V_f`, `u⁻¹`, `⟨J, V_f⟩ = (ε/√3)(Y'² - Y' + 1)`; `g(0) = g₀` fixes the `e^{τ}`
   coefficient. All coefficient identities are polynomial in `ε, Y, Y', x_e, x_f` modulo
   `x_e = -2εY`, `x_f = εY'/2`, `ε² Y Y' = 1 + ε²` (`linear_combination`).
3. (1.5): on a section point the three linear conditions `⟨X, Λ_R⟩ = 0`,
   `⟨Λ_R, Z_{e₂}⟩ = ⟨X, Z_{e₂}⟩ h₀`, `⟨Λ_R, Z_{e₃}⟩ = ⟨X, Z_{e₃}⟩ h₀` (`H(e₂) = H(e₃) = 0`,
   `hamiltonian_eq_traceForm_sub`; `H(e₂) = H(e₃) - χ₂₃`, `hamiltonian_sub_eq_switchingFn`) read
   `-2ε m_h + x_e m_f + x_f m_e = 0`, `m_h = -ε h₀`, `2m_h + 4m_f = (-2ε + 4x_f) h₀` in the frame,
   whence `frame_section_costateR`. Then `N₂₁(q) = -(2/3)(ε m_e + x_e m_h) = -8h₀/(3Y')`
   (`x_e x_f = -(1 + ε²)`), which is (1.5); `N₂₃(q) = χ₂₃ ⟨X, Z_{e₂}⟩⟨X, Z_{e₃}⟩ = 0`.
   `A' = 1 + g₀ - B' = 2 - Y' - p`.

Checked against a literal model of the Lean definitions (`notes/n4f/check1.py`: the normal form
to `10⁻¹⁷` at several times on a chart point near `W^u` and on a generic phase point with
`H(e₂) = 0`; (1.5) and the frame of `Λ_R` on the chart point).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- `f₀ = (√3/(8ε³)) N₂₁(q)`, the value at `τ = 0` of the normalized `N₂₁` (Theorem 1.3). -/
noncomputable def arcF0 (q : iso_PhasePt) : ℝ := √3 / (8 * arcEps q ^ 3) * switchingNum 1 0 q

/-- `g₀ = (√3/(8ε³)) N₂₃(q)`, the value at `τ = 0` of the normalized `N₂₃`; `0` on the section. -/
noncomputable def arcG0 (q : iso_PhasePt) : ℝ := √3 / (8 * arcEps q ^ 3) * switchingNum 1 2 q

/-- `q = -(√3/(6ε)) ⟨Λ̂₀, V_e⟩`, `Λ̂₀ = Λ₁(0) + (3/2) J` (Theorem 1.3): `B = Y - 1 + q`. -/
noncomputable def arcQ (q : iso_PhasePt) : ℝ :=
  -(√3 / (6 * arcEps q)) * traceForm (q.2.1 + (3 / 2 : ℝ) • J) (arcVe q.1)

/-- `p = (2/(√3 ε)) ⟨Λ̂₀, V_f⟩` (Theorem 1.3): `B' = Y' - 1 + p`. -/
noncomputable def arcP (q : iso_PhasePt) : ℝ :=
  2 / (√3 * arcEps q) * traceForm (q.2.1 + (3 / 2 : ℝ) • J) (arcVf q.1)

/-- **The arc parameters** `(ε, Y, f₀, g₀, q, p)` of a phase point (proof.md §1.3, §2.1). -/
noncomputable def arcParams (q : iso_PhasePt) : ArcParams :=
  ⟨arcEps q, arcY q, arcF0 q, arcG0 q, arcQ q, arcP q⟩

variable {q : iso_PhasePt}

/-- `Y'` of the parameters is `1 + ρ₀(X₀)/ε` ((1.3)). -/
theorem arcParams_Y' (hX : IsStarState q.1) : (arcParams q).Y' = arcY' q := by
  sorry

/-- The radius of the parameters is the chart radius `r = X₁₁`. -/
theorem arcParams_radius (hX : IsStarState q.1) : (arcParams q).radius = q.1 0 0 := by
  sorry

/-- **Theorem 1.3** (the normal form). Let `q` be a phase point with `X₀` a star state, `Λ₁(0)`,
`Λ_R(0)` traceless and `H(e₂)(q) = 0`. Along the `e₂`-flow from `q`, with `τ = t/ε`,
`(√3/(8ε³)) N₂₁(t) = f(τ) = -1 + A e^{-τ} + B e^{-2τ} + Y τ e^{-τ}` and
`(√3/(8ε³)) N₂₃(t) = g(τ) = -1 + A' e^{τ} + B' e^{2τ} - Y' τ e^{τ}`, with `B = Y - 1 + q`,
`A = 1 + f₀ - B`, `B' = Y' - 1 + p`, `A' = 1 + g₀ - B'` (`ArcParams.f`, `ArcParams.g`). -/
theorem arc_normalForm (hX : IsStarState q.1) (hL : q.2.1.trace = 0) (hR : q.2.2.trace = 0)
    (hH : phaseHam q (vertex 1) = 0) (t : ℝ) :
    √3 / (8 * arcEps q ^ 3) * switchingNum 1 0 (iso_vertexFlow 1 q t) =
        (arcParams q).f (t / arcEps q) ∧
      √3 / (8 * arcEps q ^ 3) * switchingNum 1 2 (iso_vertexFlow 1 q t) =
        (arcParams q).g (t / arcEps q) := by
  sorry

/-- **`Λ_R` on a section point, in the frame** (proof.md, before (1.5)): with
`h₀ = ⟨Λ̂₀, X₀⟩` (`reducedHam`), `m_h = -ε h₀`, `m_f = h₀ x_f`, `m_e = h₀ (1 - ε²)/x_f`. -/
theorem frame_section_costateR (hq : IsArcSectionPt q) :
    frameH q.2.2 = -arcEps q * reducedHam q.2.1 q.1 ∧
      frameF q.2.2 = frameF q.1 * reducedHam q.2.1 q.1 ∧
      frameE q.2.2 = (1 - arcEps q ^ 2) * reducedHam q.2.1 q.1 / frameF q.1 := by
  sorry

/-- **(1.5)**: on a section point `g₀ = 0` (`χ₂₃ = 0`). -/
theorem arcG0_eq_zero (hq : IsArcSectionPt q) : arcG0 q = 0 := by
  sorry

/-- **(1.5)**: on a section point `f₀ = -(√3/(3ε³Y')) ⟨Λ̂₀, X₀⟩`. -/
theorem arcF0_eq_reducedHam (hq : IsArcSectionPt q) :
    arcF0 q = -(√3 / (3 * arcEps q ^ 3 * arcY' q)) * reducedHam q.2.1 q.1 := by
  sorry

/-- **(1.5)**: on a section point `A' = 2 - Y' - p`. -/
theorem arcParams_A' (hq : IsArcSectionPt q) : (arcParams q).A' = 2 - arcY' q - arcP q := by
  sorry

/-- **(1.5)**: P1 (`f₀ > 0`) says that the reduced Hamiltonian `⟨Λ₁ + (3/2) J, X⟩` is negative at
the section point. -/
theorem arcF0_pos_iff (hq : IsArcSectionPt q) : 0 < arcF0 q ↔ reducedHam q.2.1 q.1 < 0 := by
  sorry

end SmoothedPolygons
