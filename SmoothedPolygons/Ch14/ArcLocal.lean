module

public import SmoothedPolygons.Ch14.ArcConditions

/-!
# Chapter 14, N4: near the fixed point every chart point lies in `𝒢*` (Lemma 5.1)

`notes/n4/proof.md` §5.1. Near the outward fixed point `(0, x̃_out)` of the extended
Reinhardt–Poincaré map (Lemma 14.3.1), every chart point `p = (r, x̃)` with `r > 0` is mapped by
the Lie algebra chart (`lieChart`, §14.1) to a point of the region `𝒢*` (`arcRegion`: P1, P2, P4,
E and `r > 0`). The arc parameters, rescaled by their natural powers of `r`, are rational
functions of `(r, x̃)` that extend continuously to `r = 0`, where they are linear in `x̃`; at
`x̃_out` they have the signs that `𝒢*` asks for. This is the first point of the orbit in the
reduction of N4 to (INV) (Theorem 5.2, `SmoothedPolygons/Ch14/ArcRegionInvariant.lean`).

**Departure from the paper.** The book computes the unstable curve numerically (Figure 14.2,
TeX 11951–11991); the formalization proves N4 from (INV) by the exact structure of the arcs (see
`SmoothedPolygons/Ch14/ArcParams.lean`). This lemma replaces the location of the curve near the
divisor by a neighbourhood of the fixed point.

## Statements

* `eventually_isArcSectionPt_lieChart`: near `(0, x̃)` (any `x̃`), chart points with `r > 0` are
  section points.
* `tendsto_arcParams_lieChart` (the limits at the divisor, for any `x̃ = (x̃₂₁, ℓ̃₁₁, ℓ̃₂₁)`):
  `f₀/r³ → -3(ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁)`, `q/r² → √3 ℓ̃₁₁ + ℓ̃₂₁`, `p/r² → -2ℓ̃₂₁`,
  `(Y - 2)/r → √3 - 3x̃₂₁`, `(Y' - 2)/r → 2√3`. In Fuller coordinates
  (`fullerOfChart x̃ = (z₁, z₂, z₃)`): `f₀/r³ → -18 z₃` (positive strictly inside the wall
  `𝒲₀ = ℝ_{≤0}`), `p/r² → 12 Im z₂`, `q/r² → 6(√3 Re z₂ - Im z₂)`.
* `xTildeOut_arcSigns`: at `x̃_out`, `ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁ < 0`, `√3 ℓ̃₁₁ + ℓ̃₂₁ < 0`, `ℓ̃₂₁ < 0`,
  `x̃₂₁ < -√3/3` (values `-2.2114`, `-9.6173`, `-1.1264`, `-2.3889`; so `f₀/r³ → 6.6343`,
  `q/r² → -9.6173`, `p/r² → 2.2528`, `(Y - 2)/r → 8.8986`, `λ_lb → (√3 - 3x̃₂₁)/(2√3) = 2.569`).
* **Lemma 5.1** (`exists_nhds_lieChart_mem_arcRegion`).

## Proofs (the route, proof.md Lemma 5.1)

1. `eventually_isArcSectionPt_lieChart`: for `r > 0` small and `x̃` bounded, `(r, x̃) ∈ H*`
   (`lieChartDomain`: `√3 - 1/r < x̃₂₁`, `ℓ̃₂₁ r² < 3/2`), so `lieChart_spec` gives the blow-up
   constraints, `H(e₂) = 0`, `χ₂₃ = 0`; `H(e₃) = H(e₂) - χ₂₃ = 0`; `det Λ₁ = 9/4`; and
   `X = lieX r x̃₂₁ → J`, whose star functions are `1/√3 > 0` (continuity of `ρ₀, ρ₁, ρ₂`).
2. `tendsto_arcParams_lieChart`: on section points `f₀ = -(√3/(3ε³Y')) ⟨Λ̂, X⟩`
   (`arcF0_eq_reducedHam`), and `ε`, `Y`, `Y'`, `x_e`, `x_f`, `⟨Λ̂, X⟩`, `⟨Λ̂, V_e⟩`, `⟨Λ̂, V_f⟩`
   are explicit rational functions of `(r, x̃)` (`lieX`, `lieΛ₁`). After division by the power of
   `r` they are rational functions with a denominator that does not vanish at `r = 0`
   (`notes/n4f/local_rational.py`, sympy):
   `(Y' - 2)/r = 2√3/(1 + r x̃₂₁ - √3 r)`,
   `(Y - 2)/r = -(3r x̃₂₁² - 2√3 r x̃₂₁ - 3r + 6x̃₂₁ - 2√3)/(2(1 + r x̃₂₁)(1 + r x̃₂₁ - √3 r))`,
   `p/r² = 2 N_p/((2ℓ̃₂₁ r² - 3)(1 + r x̃₂₁ - √3 r)²)` with `N_p(0) = 3ℓ̃₂₁`,
   `f₀/r³ = 3 N_f/(2(2ℓ̃₂₁ r² - 3)(1 + r x̃₂₁)²(1 + r x̃₂₁ - √3 r)²)` with
   `N_f(0) = 6ℓ̃₁₁ + 6ℓ̃₂₁ x̃₂₁`, and the analogous formula for `q/r²` (denominator
   `2(2ℓ̃₂₁ r² - 3)(1 + r x̃₂₁)²(1 + r x̃₂₁ - √3 r)²`, numerator `-6√3 ℓ̃₁₁ - 6ℓ̃₂₁` at `r = 0`).
   The cancellation of `r³` in `⟨Λ̂, X⟩` comes from `det Λ₁ = 9/4` (`⟨Λ̃₁, J⟩ = O(r²)`).
   Prove each identity for `r > 0` near `0` (`field_simp`, `ring`), then take the limit of the
   continuous right side (`ContinuousAt.tendsto`, `tendsto_nhdsWithin_of_tendsto_nhds`).
   Compare `eventually_isSwitch_reinSwitchTime` (`SmoothedPolygons/Ch14/AnalyticExtension.lean`)
   for the same pattern.
3. `xTildeOut_arcSigns`: `xTildeOut = fullerChartInv qOutCart` with `qOutCart = equilExact rScale`
   explicit rational functions of `r_scale`, and `6.27 < r_scale < 6.28` (`rScale_bounds`); the four
   expressions are rational in `r_scale` with margins `≥ 1.1` (compare the private
   `l6c_xTildeOut_bounds` of `SmoothedPolygons/Ch14/Asymptotics.lean`).
4. Lemma 5.1: by steps 2 and 3, the limits of `f₀/r³`, `-q/r²`, `p/r²` at `(0, x̃_out)` are
   positive, and the limit of `((Y - 2) - (Y - 1)(Y' - 2))/r` is
   `(√3 - 3x̃₂₁) - 2√3 > 0` (`Y - 1 → 1`); so all four hold for `r > 0` near the fixed point
   (`Filter.Tendsto.eventually_const_lt`), and `r > 0`,
   step 1 give the rest. A neighbourhood `V` of `chartPtOut` comes from
   `mem_nhdsWithin` (`{p | 0 < p.1}` is open).

The limits and the values at `x̃_out` were computed in `notes/n4f/local_limits.py`; they agree with
the research's values along `W^u` (`notes/n4/identities.py`: `6.6342738`, `-9.6173146`,
`2.2527998`, `8.8986195`, `2√3`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- Near `(0, x̃)`, chart points with `r > 0` are section points. -/
theorem eventually_isArcSectionPt_lieChart (x : Fin 3 → ℝ) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), x), 0 < p.1 → IsArcSectionPt (lieChart p) := by
  sorry

/-- **The arc parameters at the divisor** (proof.md §5.1): for chart points `p = (r, x̃) → (0, x̃)`
with `r > 0`, `f₀/r³ → -3(ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁)`, `q/r² → √3 ℓ̃₁₁ + ℓ̃₂₁`, `p/r² → -2ℓ̃₂₁`,
`(Y - 2)/r → √3 - 3x̃₂₁` and `(Y' - 2)/r → 2√3` (`x̃ = (x̃₂₁, ℓ̃₁₁, ℓ̃₂₁)`). -/
theorem tendsto_arcParams_lieChart (x : Fin 3 → ℝ) :
    Tendsto (fun p : ℝ × (Fin 3 → ℝ) ↦ arcF0 (lieChart p) / p.1 ^ 3)
        (𝓝[{p | 0 < p.1}] ((0 : ℝ), x)) (𝓝 (-3 * (x 1 + x 2 * x 0))) ∧
      Tendsto (fun p : ℝ × (Fin 3 → ℝ) ↦ arcQ (lieChart p) / p.1 ^ 2)
        (𝓝[{p | 0 < p.1}] ((0 : ℝ), x)) (𝓝 (√3 * x 1 + x 2)) ∧
      Tendsto (fun p : ℝ × (Fin 3 → ℝ) ↦ arcP (lieChart p) / p.1 ^ 2)
        (𝓝[{p | 0 < p.1}] ((0 : ℝ), x)) (𝓝 (-2 * x 2)) ∧
      Tendsto (fun p : ℝ × (Fin 3 → ℝ) ↦ (arcY (lieChart p) - 2) / p.1)
        (𝓝[{p | 0 < p.1}] ((0 : ℝ), x)) (𝓝 (√3 - 3 * x 0)) ∧
      Tendsto (fun p : ℝ × (Fin 3 → ℝ) ↦ (arcY' (lieChart p) - 2) / p.1)
        (𝓝[{p | 0 < p.1}] ((0 : ℝ), x)) (𝓝 (2 * √3)) := by
  sorry

/-- **The signs at `x̃_out`** (proof.md §5.1): `ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁ < 0` (P1), `√3 ℓ̃₁₁ + ℓ̃₂₁ < 0`
(P2), `ℓ̃₂₁ < 0` (P4), `x̃₂₁ < -√3/3` (E), at `x̃_out ≈ (-2.3889, -4.9022, -1.1264)`. -/
theorem xTildeOut_arcSigns :
    xTildeOut 1 + xTildeOut 2 * xTildeOut 0 < 0 ∧ √3 * xTildeOut 1 + xTildeOut 2 < 0 ∧
      xTildeOut 2 < 0 ∧ xTildeOut 0 < -(√3 / 3) := by
  sorry

/-- **Lemma 5.1** (proof.md §5.1). There is a neighbourhood `V` of the fixed point `(0, x̃_out)`
such that every chart point of `V` with `r > 0` is mapped by the chart into the region `𝒢*`. -/
theorem exists_nhds_lieChart_mem_arcRegion :
    ∃ V ∈ 𝓝 chartPtOut, ∀ p ∈ V, 0 < p.1 → lieChart p ∈ arcRegion := by
  sorry

end SmoothedPolygons
