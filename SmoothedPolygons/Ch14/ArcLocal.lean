module

public import SmoothedPolygons.Ch14.ArcConditions

/-!
# Chapter 14, N4: near the fixed point every chart point lies in `𝒢*` (Lemma 5.1)

Part of the formalization's proof of N4 (`UnstableCurveLeavesStarDomain`, Figure 14.2) without
computer assistance. **Departure from the paper**, by the user's decision: the book reads N4 off a
computed figure (Figure 14.2, TeX 11951–11991; REPORT.md E88); the formalization proves it from
the exact structure of the Reinhardt flow along an `e₂`-arc and an invariant region (see
`SmoothedPolygons/Ch14/ArcParams.lean`, and `SmoothedPolygons/Ch14/ArcRegionInvariant.lean` for
the numbering of the steps). This lemma replaces the location of the curve near the divisor by a
neighbourhood of the fixed point.

This file is §5.1. Near the outward fixed point `(0, x̃_out)` of the extended
Reinhardt–Poincaré map (Lemma 14.3.1), every chart point `p = (r, x̃)` with `r > 0` is mapped by
the Lie algebra chart (`lieChart`, §14.1) to a point of the region `𝒢*` (`arcRegion`: P1, P2, P4,
E and `r > 0`). The arc parameters, rescaled by their natural powers of `r`, are rational
functions of `(r, x̃)` that extend continuously to `r = 0`, where they are linear in `x̃`; at
`x̃_out` they have the signs that `𝒢*` asks for. This is the first point of the orbit in the
reduction of N4 to (INV) (Theorem 5.2, `SmoothedPolygons/Ch14/ArcRegionInvariant.lean`).

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

## Proofs (the route, Lemma 5.1)

1. `eventually_isArcSectionPt_lieChart`: for `r > 0` small and `x̃` bounded, `(r, x̃) ∈ H*`
   (`lieChartDomain`: `√3 - 1/r < x̃₂₁`, `ℓ̃₂₁ r² < 3/2`), so `lieChart_spec` gives the blow-up
   constraints, `H(e₂) = 0`, `χ₂₃ = 0`; `H(e₃) = H(e₂) - χ₂₃ = 0`; `det Λ₁ = 9/4`; and
   `X = lieX r x̃₂₁ → J`, whose star functions are `1/√3 > 0` (continuity of `ρ₀, ρ₁, ρ₂`).
2. `tendsto_arcParams_lieChart`: on section points `f₀ = -(√3/(3ε³Y')) ⟨Λ̂, X⟩`
   (`arcF0_eq_reducedHam`), and `ε`, `Y`, `Y'`, `x_e`, `x_f`, `⟨Λ̂, X⟩`, `⟨Λ̂, V_e⟩`, `⟨Λ̂, V_f⟩`
   are explicit rational functions of `(r, x̃)` (`lieX`, `lieΛ₁`). After division by the power of
   `r` they are rational functions with a denominator that does not vanish at `r = 0`
   (computed with sympy):
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
   for the same pattern. In the proof the right sides are kept in factored form, with
   `Λ̂ = r² Λ̃₁`, `Λ̃₁ = [[ℓ̃₁₁, (2r²ℓ̃₁₁² + 3ℓ̃₂₁)/(3 - 2r²ℓ̃₂₁)], [ℓ̃₂₁, -ℓ̃₁₁]]`
   (`det Λ₁ = 9/4`): `q/r² = -(√3/(6ε)) ⟨Λ̃₁, V_e⟩`, `p/r² = (2/(√3 ε)) ⟨Λ̃₁, V_f⟩`,
   `f₀/r³ = -(√3/(3ε³Y')) K` with `⟨Λ̃₁, X⟩ = r K` and `K(0) = 2(ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁)`; their
   continuity at `r = 0` is `fun_prop` after unfolding the entries.
3. `xTildeOut_arcSigns`: the enclosures `|x̃_out - (-2.39, -4.90, -1.12)| < 0.01` of
   Remark 14.2.1 (`remark14_2_1`, from `xTildeOut = fullerChartInv qOutCart`,
   `qOutCart = equilExact rScale` and the fine bounds on `r_scale`) give the four signs with
   margins `≥ 1.1` (`nlinarith` with the product `(ℓ̃₂₁ + 1.13)(-2.38 - x̃₂₁) > 0` for the
   first, `√3 < 2` for the last).
4. Lemma 5.1: by steps 2 and 3, the limits of `f₀/r³`, `-q/r²`, `p/r²` at `(0, x̃_out)` are
   positive, and the limit of `((Y - 2) - (Y - 1)(Y' - 2))/r` is
   `(√3 - 3x̃₂₁) - 2√3 > 0` (`Y - 1 → 1`); so all four hold for `r > 0` near the fixed point
   (`Filter.Tendsto.eventually_const_lt`), and `r > 0`,
   step 1 give the rest. A neighbourhood `V` of `chartPtOut` comes from
   `mem_nhdsWithin` (`{p | 0 < p.1}` is open).

The limits and the values at `x̃_out` were also computed with sympy; they agree with the values
along `W^u` computed numerically (`6.6342738`, `-9.6173146`, `2.2527998`, `8.8986195`, `2√3`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-! ### The chart near the divisor in coordinates -/

/-- The star functions of `lieX r x̃₂₁`. -/
private theorem ρ_lieX (r a : ℝ) :
    ρ₀ (lieX r a) = (1 + r * a + √3 * r) / √3 ∧ ρ₁ (lieX r a) = (1 + r * a - √3 * r) / √3 ∧
      ρ₂ (lieX r a) = (3 * (1 + r ^ 2) / (1 + r * a) - (1 + r * a)) / (2 * √3) := by
  refine ⟨by simp [ρ₀, lieX], by simp [ρ₁, lieX], ?_⟩
  simp [ρ₂, lieX]
  ring

/-- The three local conditions near `(0, x̃)`: `1 + r x̃₂₁ - √3 r > 0` (`ρ₁ > 0` and
`x̃₂₁ > √3 - 1/r`), `ℓ̃₂₁ r² < 3/2` and `(1 + r x̃₂₁)² < 3 (1 + r²)` (`ρ₂ > 0`); each holds at
`r = 0`. -/
private theorem eventually_section_conditions (x : Fin 3 → ℝ) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), x), 0 < 1 + p.1 * p.2 0 - √3 * p.1 ∧ p.2 2 * p.1 ^ 2 < 3 / 2 ∧
      (1 + p.1 * p.2 0) ^ 2 < 3 * (1 + p.1 ^ 2) := by
  have c1 : ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) ↦ 1 + p.1 * p.2 0 - √3 * p.1) ((0 : ℝ), x) := by
    fun_prop
  have c2 : ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) ↦ p.2 2 * p.1 ^ 2) ((0 : ℝ), x) := by fun_prop
  have c3 : ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) ↦ 3 * (1 + p.1 ^ 2) - (1 + p.1 * p.2 0) ^ 2)
      ((0 : ℝ), x) := by fun_prop
  have e1 : ∀ᶠ p in 𝓝 ((0 : ℝ), x), 0 < 1 + p.1 * p.2 0 - √3 * p.1 :=
    c1.tendsto.eventually_const_lt (by simp)
  have e2 : ∀ᶠ p in 𝓝 ((0 : ℝ), x), p.2 2 * p.1 ^ 2 < 3 / 2 :=
    c2.tendsto.eventually_lt_const (by norm_num)
  have e3 : ∀ᶠ p in 𝓝 ((0 : ℝ), x), 0 < 3 * (1 + p.1 ^ 2) - (1 + p.1 * p.2 0) ^ 2 :=
    c3.tendsto.eventually_const_lt (by norm_num)
  filter_upwards [e1, e2, e3] with p h1 h2 h3
  exact ⟨h1, h2, by linarith⟩

/-- The local conditions, with `r > 0`, in the punctured neighbourhood `r > 0`. -/
private theorem eventually_nhdsWithin_section_conditions (x : Fin 3 → ℝ) :
    ∀ᶠ p in 𝓝[{p : ℝ × (Fin 3 → ℝ) | 0 < p.1}] ((0 : ℝ), x), 0 < p.1 ∧
      0 < 1 + p.1 * p.2 0 - √3 * p.1 ∧ p.2 2 * p.1 ^ 2 < 3 / 2 ∧
      (1 + p.1 * p.2 0) ^ 2 < 3 * (1 + p.1 ^ 2) := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_section_conditions x)]
    with p hp h
  exact ⟨hp, h⟩

/-- Under the local conditions, the chart point is a section point (step 1 of the route). -/
private theorem isArcSectionPt_lieChart_of_conditions {p : ℝ × (Fin 3 → ℝ)} (hr : 0 < p.1)
    (h1 : 0 < 1 + p.1 * p.2 0 - √3 * p.1) (h2 : p.2 2 * p.1 ^ 2 < 3 / 2)
    (h3 : (1 + p.1 * p.2 0) ^ 2 < 3 * (1 + p.1 ^ 2)) : IsArcSectionPt (lieChart p) := by
  have hs3 : 0 < √3 := by positivity
  have hdom : p ∈ lieChartDomain := by
    refine ⟨hr, ?_, h2⟩
    have e : √3 - 1 / p.1 = (√3 * p.1 - 1) / p.1 := by field_simp
    rw [e, div_lt_iff₀ hr]
    linarith
  obtain ⟨⟨trX, trL, trR, detX, detL, tfXR, -, -⟩, hH, hχ, -, -, -⟩ := lieChart_spec hdom
  have hH3 : hamiltonian (-1) (lieChart p).2.1 (lieChart p).2.2 (lieChart p).1 (vertex 2) = 0 := by
    have := hamiltonian_sub_eq_switchingFn (lieChart p).2.1 (lieChart p).2.2 (lieChart p).1 1 2
    linarith
  obtain ⟨e0, e1, e2⟩ := ρ_lieX p.1 (p.2 0)
  have hc : 0 < 1 + p.1 * p.2 0 := by nlinarith
  refine ⟨⟨⟨trX, trL, trR, detX, tfXR, hH3, hχ⟩, detL⟩, trX, detX, ?_, ?_, ?_⟩
  · change 0 < ρ₀ (lieX p.1 (p.2 0))
    rw [e0]
    exact div_pos (by nlinarith) hs3
  · change 0 < ρ₁ (lieX p.1 (p.2 0))
    rw [e1]
    exact div_pos h1 hs3
  · change 0 < ρ₂ (lieX p.1 (p.2 0))
    rw [e2]
    refine div_pos ?_ (by positivity)
    rw [sub_pos, lt_div_iff₀ hc]
    nlinarith

/-- `Λ̃₁` with `Λ₁ + (3/2) J = r² Λ̃₁` in the chart (`Λ̃₁(0) = [[ℓ̃₁₁, ℓ̃₂₁], [ℓ̃₂₁, -ℓ̃₁₁]]`). -/
private noncomputable def lieLamTilde (r l m : ℝ) : Mat2 :=
  !![l, (2 * r ^ 2 * l ^ 2 + 3 * m) / (3 - 2 * r ^ 2 * m); m, -l]

/-- `Λ̂ = Λ₁ + (3/2) J = r² Λ̃₁` (`det Λ₁ = 9/4`). -/
private theorem lieΛ₁_add_three_halves_smul_J {r l m : ℝ} (hd : 3 - 2 * r ^ 2 * m ≠ 0) :
    lieΛ₁ r l m + (3 / 2 : ℝ) • J = r ^ 2 • lieLamTilde r l m := by
  have hd' : 3 - r ^ 2 * 2 * m ≠ 0 := fun h ↦ hd (by linarith)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [lieΛ₁, lieLamTilde, J, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, smul_eq_mul, Fin.zero_eta, Fin.mk_one] <;>
    field_simp <;> ring

private theorem traceForm_smul_left (c : ℝ) (A B : Mat2) :
    traceForm (c • A) B = c * traceForm A B := by
  simp [traceForm, Matrix.trace_smul]

/-- The cancellation behind `f₀ = O(r³)`: `⟨Λ̃₁, X⟩ = r K` with `K` regular at `r = 0`,
`K(0) = 2 (ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁)`. -/
private noncomputable def lieLamTildePairingDivR (r a l m : ℝ) : ℝ :=
  2 * l + (6 * m * a + r * (3 * m * a ^ 2 + 2 * l ^ 2 * (1 + r * a) ^ 2 + 2 * m ^ 2 - 3 * m +
    2 * r ^ 2 * m ^ 2)) / ((1 + r * a) * (3 - 2 * r ^ 2 * m))

private theorem traceForm_lieLamTilde_lieX {r a l m : ℝ} (hc : 1 + r * a ≠ 0)
    (hd : 3 - 2 * r ^ 2 * m ≠ 0) :
    traceForm (lieLamTilde r l m) (lieX r a) = r * lieLamTildePairingDivR r a l m := by
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, lieLamTilde, lieX,
    lieLamTildePairingDivR, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  have hd' : 3 - r ^ 2 * 2 * m ≠ 0 := fun h ↦ hd (by linarith)
  field_simp
  ring

private theorem sqrt_three_pow_two_three_four : √3 ^ 2 = 3 ∧ √3 ^ 3 = 3 * √3 ∧ √3 ^ 4 = 9 := by
  have h : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  exact ⟨h, by rw [pow_succ, h], by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h]; norm_num⟩

/-- A limit along `r > 0` from an eventual identity with a function continuous at `(0, x̃)`. -/
private theorem tendsto_of_eventuallyEq_of_continuousAt {x : Fin 3 → ℝ}
    {Q G : ℝ × (Fin 3 → ℝ) → ℝ} {L : ℝ}
    (hQ : ∀ᶠ p in 𝓝[{p : ℝ × (Fin 3 → ℝ) | 0 < p.1}] ((0 : ℝ), x), G p = Q p)
    (hG : ContinuousAt G ((0 : ℝ), x)) (hL : G ((0 : ℝ), x) = L) :
    Tendsto Q (𝓝[{p : ℝ × (Fin 3 → ℝ) | 0 < p.1}] ((0 : ℝ), x)) (𝓝 L) := by
  rw [← hL]
  exact (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' hQ

/-- Near `(0, x̃)`, chart points with `r > 0` are section points. -/
theorem eventually_isArcSectionPt_lieChart (x : Fin 3 → ℝ) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), x), 0 < p.1 → IsArcSectionPt (lieChart p) := by
  filter_upwards [eventually_section_conditions x] with p ⟨h1, h2, h3⟩ hr
  exact isArcSectionPt_lieChart_of_conditions hr h1 h2 h3

/-! ### The five limits (step 2 of the route) -/

/-- `f₀/r³ → -3(ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁)`: on section points `f₀ = -(√3/(3ε³Y')) ⟨Λ̂, X⟩` (1.5),
`⟨Λ̂, X⟩ = r² ⟨Λ̃₁, X⟩ = r³ K`. -/
private theorem tendsto_arcF0_lieChart_div_pow_three (x : Fin 3 → ℝ) :
    Tendsto (fun p : ℝ × (Fin 3 → ℝ) ↦ arcF0 (lieChart p) / p.1 ^ 3)
      (𝓝[{p | 0 < p.1}] ((0 : ℝ), x)) (𝓝 (-3 * (x 1 + x 2 * x 0))) := by
  refine tendsto_of_eventuallyEq_of_continuousAt (G := fun p : ℝ × (Fin 3 → ℝ) ↦
    -(√3 / (3 * ρ₁ (lieX p.1 (p.2 0)) ^ 3 * (1 + ρ₀ (lieX p.1 (p.2 0)) / ρ₁ (lieX p.1 (p.2 0))))) *
      lieLamTildePairingDivR p.1 (p.2 0) (p.2 1) (p.2 2)) ?_ ?_ ?_
  · filter_upwards [eventually_nhdsWithin_section_conditions x] with p ⟨hr, h1, h2, h3⟩
    have hd : 3 - 2 * p.1 ^ 2 * p.2 2 ≠ 0 := by
      have : 0 < 3 - 2 * p.1 ^ 2 * p.2 2 := by linarith
      exact this.ne'
    have hc : 1 + p.1 * p.2 0 ≠ 0 := by
      have : 0 < 1 + p.1 * p.2 0 := by nlinarith [Real.sqrt_nonneg 3]
      exact this.ne'
    rw [arcF0_eq_reducedHam (isArcSectionPt_lieChart_of_conditions hr h1 h2 h3)]
    change _ = -(√3 / (3 * ρ₁ (lieX p.1 (p.2 0)) ^ 3 * (1 + ρ₀ (lieX p.1 (p.2 0)) /
      ρ₁ (lieX p.1 (p.2 0))))) * traceForm (lieΛ₁ p.1 (p.2 1) (p.2 2) + (3 / 2 : ℝ) • J)
        (lieX p.1 (p.2 0)) / p.1 ^ 3
    rw [lieΛ₁_add_three_halves_smul_J hd, traceForm_smul_left, traceForm_lieLamTilde_lieX hc hd]
    have hr' : p.1 ≠ 0 := hr.ne'
    field_simp
  · simp only [lieLamTildePairingDivR, lieX, ρ₀, ρ₁, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    fun_prop (disch := (simp; try positivity))
  · obtain ⟨-, -, h4⟩ := sqrt_three_pow_two_three_four
    simp only [lieLamTildePairingDivR, lieX, ρ₀, ρ₁, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    ring_nf
    rw [h4]
    ring

/-- `q/r² → √3 ℓ̃₁₁ + ℓ̃₂₁`: `q/r² = -(√3/(6ε)) ⟨Λ̃₁, V_e⟩`. -/
private theorem tendsto_arcQ_lieChart_div_sq (x : Fin 3 → ℝ) :
    Tendsto (fun p : ℝ × (Fin 3 → ℝ) ↦ arcQ (lieChart p) / p.1 ^ 2)
      (𝓝[{p | 0 < p.1}] ((0 : ℝ), x)) (𝓝 (√3 * x 1 + x 2)) := by
  refine tendsto_of_eventuallyEq_of_continuousAt
    (G := fun p : ℝ × (Fin 3 → ℝ) ↦ -(√3 / (6 * ρ₁ (lieX p.1 (p.2 0)))) *
      traceForm (lieLamTilde p.1 (p.2 1) (p.2 2)) (arcVe (lieX p.1 (p.2 0)))) ?_ ?_ ?_
  · filter_upwards [eventually_nhdsWithin_section_conditions x] with p ⟨hr, _, h2, _⟩
    have hd : 3 - 2 * p.1 ^ 2 * p.2 2 ≠ 0 := by
      have : 0 < 3 - 2 * p.1 ^ 2 * p.2 2 := by linarith
      exact this.ne'
    change _ = -(√3 / (6 * ρ₁ (lieX p.1 (p.2 0)))) * traceForm (lieΛ₁ p.1 (p.2 1) (p.2 2) +
      (3 / 2 : ℝ) • J) (arcVe (lieX p.1 (p.2 0))) / p.1 ^ 2
    rw [lieΛ₁_add_three_halves_smul_J hd, traceForm_smul_left]
    have hr' : p.1 ≠ 0 := hr.ne'
    field_simp
  · simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, lieLamTilde,
      lieX, arcVe, ofFrame, frameE, ρ₁, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    fun_prop (disch := (simp; try positivity))
  · obtain ⟨h2, h3, h4⟩ := sqrt_three_pow_two_three_four
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, lieLamTilde,
      lieX, arcVe, ofFrame, frameE, ρ₁, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    ring_nf
    rw [h2, h3, h4]
    ring

/-- `p/r² → -2ℓ̃₂₁`: `p/r² = (2/(√3 ε)) ⟨Λ̃₁, V_f⟩`. -/
private theorem tendsto_arcP_lieChart_div_sq (x : Fin 3 → ℝ) :
    Tendsto (fun p : ℝ × (Fin 3 → ℝ) ↦ arcP (lieChart p) / p.1 ^ 2)
      (𝓝[{p | 0 < p.1}] ((0 : ℝ), x)) (𝓝 (-2 * x 2)) := by
  refine tendsto_of_eventuallyEq_of_continuousAt
    (G := fun p : ℝ × (Fin 3 → ℝ) ↦ 2 / (√3 * ρ₁ (lieX p.1 (p.2 0))) *
      traceForm (lieLamTilde p.1 (p.2 1) (p.2 2)) (arcVf (lieX p.1 (p.2 0)))) ?_ ?_ ?_
  · filter_upwards [eventually_nhdsWithin_section_conditions x] with p ⟨hr, _, h2, _⟩
    have hd : 3 - 2 * p.1 ^ 2 * p.2 2 ≠ 0 := by
      have : 0 < 3 - 2 * p.1 ^ 2 * p.2 2 := by linarith
      exact this.ne'
    change _ = 2 / (√3 * ρ₁ (lieX p.1 (p.2 0))) * traceForm (lieΛ₁ p.1 (p.2 1) (p.2 2) +
      (3 / 2 : ℝ) • J) (arcVf (lieX p.1 (p.2 0))) / p.1 ^ 2
    rw [lieΛ₁_add_three_halves_smul_J hd, traceForm_smul_left]
    have hr' : p.1 ≠ 0 := hr.ne'
    field_simp
  · simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, lieLamTilde,
      lieX, arcVf, ofFrame, frameF, ρ₁, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    fun_prop (disch := (simp; try positivity))
  · simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, lieLamTilde,
      lieX, arcVf, ofFrame, frameF, ρ₁, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    ring

/-- `(Y - 2)/r → √3 - 3x̃₂₁`. -/
private theorem tendsto_arcY_lieChart_sub_two_div (x : Fin 3 → ℝ) :
    Tendsto (fun p : ℝ × (Fin 3 → ℝ) ↦ (arcY (lieChart p) - 2) / p.1)
      (𝓝[{p | 0 < p.1}] ((0 : ℝ), x)) (𝓝 (√3 - 3 * x 0)) := by
  refine tendsto_of_eventuallyEq_of_continuousAt (G := fun p : ℝ × (Fin 3 → ℝ) ↦
    (3 * p.1 - 3 * p.2 0 * (2 + p.1 * p.2 0) + 2 * √3 * (1 + p.1 * p.2 0)) /
      (2 * (1 + p.1 * p.2 0) * (1 + p.1 * p.2 0 - √3 * p.1))) ?_ ?_ ?_
  · filter_upwards [eventually_nhdsWithin_section_conditions x] with p ⟨hr, h1, _, _⟩
    have hc : 1 + p.1 * p.2 0 ≠ 0 := by
      have : 0 < 1 + p.1 * p.2 0 := by nlinarith [Real.sqrt_nonneg 3]
      exact this.ne'
    change _ = (1 + ρ₂ (lieX p.1 (p.2 0)) / ρ₁ (lieX p.1 (p.2 0)) - 2) / p.1
    simp only [ρ₂, ρ₁, lieX, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    have hs : √3 ≠ 0 := by positivity
    have hr' : p.1 ≠ 0 := hr.ne'
    have he : 1 + p.1 * p.2 0 - √3 * p.1 ≠ 0 := h1.ne'
    have he' : 1 + p.1 * p.2 0 - p.1 * √3 ≠ 0 := fun h ↦ he (by linarith)
    field_simp
    ring
  · fun_prop (disch := (simp; try positivity))
  · simp only
    field_simp
    ring

/-- `(Y' - 2)/r → 2√3`. -/
private theorem tendsto_arcY'_lieChart_sub_two_div (x : Fin 3 → ℝ) :
    Tendsto (fun p : ℝ × (Fin 3 → ℝ) ↦ (arcY' (lieChart p) - 2) / p.1)
      (𝓝[{p | 0 < p.1}] ((0 : ℝ), x)) (𝓝 (2 * √3)) := by
  refine tendsto_of_eventuallyEq_of_continuousAt (G := fun p : ℝ × (Fin 3 → ℝ) ↦
    2 * √3 / (1 + p.1 * p.2 0 - √3 * p.1)) ?_ ?_ ?_
  · filter_upwards [eventually_nhdsWithin_section_conditions x] with p ⟨hr, h1, _, _⟩
    change _ = (1 + ρ₀ (lieX p.1 (p.2 0)) / ρ₁ (lieX p.1 (p.2 0)) - 2) / p.1
    simp only [ρ₀, ρ₁, lieX, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    have hs : √3 ≠ 0 := by positivity
    have hr' : p.1 ≠ 0 := hr.ne'
    have he : 1 + p.1 * p.2 0 - √3 * p.1 ≠ 0 := h1.ne'
    have he' : 1 + p.1 * p.2 0 - p.1 * √3 ≠ 0 := fun h ↦ he (by linarith)
    field_simp
    ring
  · fun_prop (disch := (simp; try positivity))
  · simp

/-- **The arc parameters at the divisor** (§5.1): for chart points `p = (r, x̃) → (0, x̃)`
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
  exact ⟨tendsto_arcF0_lieChart_div_pow_three x, tendsto_arcQ_lieChart_div_sq x,
    tendsto_arcP_lieChart_div_sq x, tendsto_arcY_lieChart_sub_two_div x,
    tendsto_arcY'_lieChart_sub_two_div x⟩

/-- **The signs at `x̃_out`** (§5.1): `ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁ < 0` (P1), `√3 ℓ̃₁₁ + ℓ̃₂₁ < 0`
(P2), `ℓ̃₂₁ < 0` (P4), `x̃₂₁ < -√3/3` (E), at `x̃_out ≈ (-2.3889, -4.9022, -1.1264)`. -/
theorem xTildeOut_arcSigns :
    xTildeOut 1 + xTildeOut 2 * xTildeOut 0 < 0 ∧ √3 * xTildeOut 1 + xTildeOut 2 < 0 ∧
      xTildeOut 2 < 0 ∧ xTildeOut 0 < -(√3 / 3) := by
  obtain ⟨b0, b1, b2, -⟩ := remark14_2_1
  rw [abs_lt] at b0 b1 b2
  norm_num at b0 b1 b2
  have hs3 : √3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hs0 : 0 < √3 := by positivity
  refine ⟨?_, ?_, by linarith, by linarith⟩
  · nlinarith [mul_pos (by linarith : 0 < xTildeOut 2 + 113 / 100)
      (by linarith : 0 < -(238 / 100) - xTildeOut 0)]
  · nlinarith [mul_pos hs0 (by linarith : 0 < -xTildeOut 1)]

/-- **Lemma 5.1** (§5.1). There is a neighbourhood `V` of the fixed point `(0, x̃_out)`
such that every chart point of `V` with `r > 0` is mapped by the chart into the region `𝒢*`. -/
theorem exists_nhds_lieChart_mem_arcRegion :
    ∃ V ∈ 𝓝 chartPtOut, ∀ p ∈ V, 0 < p.1 → lieChart p ∈ arcRegion := by
  obtain ⟨s1, s2, s3, s4⟩ := xTildeOut_arcSigns
  obtain ⟨t1, t2, t3, t4, t5⟩ := tendsto_arcParams_lieChart xTildeOut
  have hs3 : 0 < √3 := by positivity
  have hr : Tendsto (fun p : ℝ × (Fin 3 → ℝ) ↦ p.1)
      (𝓝[{p : ℝ × (Fin 3 → ℝ) | 0 < p.1}] ((0 : ℝ), xTildeOut)) (𝓝 0) :=
    (continuous_fst.tendsto ((0 : ℝ), xTildeOut)).mono_left nhdsWithin_le_nhds
  have hY1 : Tendsto (fun p : ℝ × (Fin 3 → ℝ) ↦ arcY (lieChart p) - 1)
      (𝓝[{p : ℝ × (Fin 3 → ℝ) | 0 < p.1}] ((0 : ℝ), xTildeOut)) (𝓝 1) := by
    have h := (t4.mul hr).const_add 1
    rw [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hp' : p.1 ≠ 0 := (show 0 < p.1 from hp).ne'
    field_simp
    ring
  have hE := hY1.mul t5
  rw [one_mul] at hE
  have ev1 : ∀ᶠ p in 𝓝[{p : ℝ × (Fin 3 → ℝ) | 0 < p.1}] ((0 : ℝ), xTildeOut),
      0 < arcF0 (lieChart p) / p.1 ^ 3 := t1.eventually_const_lt (by linarith)
  have ev2 : ∀ᶠ p in 𝓝[{p : ℝ × (Fin 3 → ℝ) | 0 < p.1}] ((0 : ℝ), xTildeOut),
      arcQ (lieChart p) / p.1 ^ 2 < 0 := t2.eventually_lt_const s2
  have ev3 : ∀ᶠ p in 𝓝[{p : ℝ × (Fin 3 → ℝ) | 0 < p.1}] ((0 : ℝ), xTildeOut),
      0 < arcP (lieChart p) / p.1 ^ 2 := t3.eventually_const_lt (by linarith)
  have ev4 := hE.eventually_lt t4 (by linarith)
  have hsec : ∀ᶠ p in 𝓝[{p : ℝ × (Fin 3 → ℝ) | 0 < p.1}] ((0 : ℝ), xTildeOut),
      0 < p.1 → IsArcSectionPt (lieChart p) :=
    nhdsWithin_le_nhds (eventually_isArcSectionPt_lieChart xTildeOut)
  have hall : ∀ᶠ p in 𝓝[{p : ℝ × (Fin 3 → ℝ) | 0 < p.1}] ((0 : ℝ), xTildeOut),
      lieChart p ∈ arcRegion := by
    filter_upwards [self_mem_nhdsWithin, hsec, ev1, ev2, ev3, ev4] with p hp hs e1 e2 e3 e4
    have hp : 0 < p.1 := hp
    refine ⟨hs hp, ?_, ?_, ?_, ?_, ?_⟩
    · change 0 < lieX p.1 (p.2 0) 0 0
      simpa [lieX] using hp
    · have h := mul_pos e1 (pow_pos hp 3)
      rwa [div_mul_cancel₀ _ (pow_ne_zero 3 hp.ne')] at h
    · have h := mul_neg_of_neg_of_pos e2 (pow_pos hp 2)
      rw [div_mul_cancel₀ _ (pow_ne_zero 2 hp.ne')] at h
      exact h.le
    · have h := mul_pos e3 (pow_pos hp 2)
      rwa [div_mul_cancel₀ _ (pow_ne_zero 2 hp.ne')] at h
    · have h := mul_lt_mul_of_pos_right e4 hp
      rw [mul_assoc, div_mul_cancel₀ _ hp.ne', div_mul_cancel₀ _ hp.ne'] at h
      exact h.le
  exact ⟨_, eventually_nhdsWithin_iff.1 hall, fun p hp hr ↦ hp hr⟩

end SmoothedPolygons
