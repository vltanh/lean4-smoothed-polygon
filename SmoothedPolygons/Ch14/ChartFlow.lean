module

public import SmoothedPolygons.Ch14.LieChart
public import SmoothedPolygons.Ch7.Isolated.VertexFlow
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Chapter 14 §14.2: the vertex flow from the Lie algebra chart, expanded in `r₀` (helpers)

Helpers for `SmoothedPolygons/Ch14/Asymptotics.lean` (agent `l6c`): the estimates behind
Lemmas 14.2.3–14.2.4 of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX 11720–11758,
"Use the explicit solutions on both sides and expand as a series in the parameter `r₀`").

## The route

Write `X = J + A`, `Λ₁ = -(3/2) J + B`, `Λ_R = C`. Along the constant control `e₂` the matrix
`P = Z_{e₂}/⟨Z_{e₂}, X₀⟩` is constant (Lemma 7.1.1, `ivf_controlP_vfX`) and the extremal equations
(`iso_vertexFlow_solution`) read `A' = [P, X]`, `B' = [Λ₁, X]`,
`C' = [P, C] - ⟨C, P⟩ [P, X] - [B, X]`. With the weights `A ~ r`, `B ~ r²`, `C ~ r³`, `t ~ r` the
leading part is the chain `A' = [P₀, J]`, `B' = -(3/2) [J, A]`, `C' = [J, B]`
(`P₀ = Z_{e₂}/⟨Z_{e₂}, J⟩ = -(3/2) Z_{e₂}`), whose solution from the leading terms
`Ã = [[1, x̃₂₁], [x̃₂₁, -1]]`, `B̃ = [[ℓ̃₁₁, ℓ̃₂₁], [ℓ̃₂₁, -ℓ̃₁₁]]`,
`C̃ = 2(ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁) [[0, 1], [1, 0]]` of the chart is the explicit matrix polynomial
`chartXF`, `chartBF`, `chartCF` in `(r, t)`. Under the Cayley coordinate `cayleyZ` this chain is
the Fuller system (13.2.2) with control `ζ` (`cayleyZ [J, M] = -2i cayleyZ M`,
`cayleyZ [P₀, J]/2 = -iζ`), which is how the Fuller flow appears in `Asymptotics.lean`.

* **The chart in closed form** (`l6c_lieX_eq`, `l6c_lieΛ₁_eq`, `l6c_lieChart_ΛR`):
  `X = J + r X̃(r)`, `Λ₁ = -(3/2) J + r² Λ̃₁(r)`, and `Λ_R = r³ h̃(r) N(r)` with
  `h = ⟨Λ₁ + (3/2) J, X⟩ = r³ h̃(r)` and `N(r) = [[r, (1 - r²)/(1 + r x̃₂₁)], [1 + r x̃₂₁, -r]]`
  (the dual-basis formula `sl2Dual` evaluated). All of `X̃`, `Λ̃₁`, `h̃ N` and `P` are rational in
  `r`, regular at `r = 0`, with values `Ã`, `B̃`, `C̃`, `P₀` there; differentiability gives the
  initial errors `O(r²)`, `O(r³)`, `O(r⁴)`, `O(r)` (`l6c_static_X`, `l6c_static_B`,
  `norm_lieChart_ΛR_sub_le`, `l6c_static_P`).
* **Three Grönwall steps** (`l6c_step_X`, `l6c_step_B`, `l6c_step_C`): the errors
  `X - XF`, `Λ₁ + (3/2) J - BF`, `Λ_R - CF` satisfy linear differential inequalities
  `‖E'‖ ≤ K ‖E‖ + O(r^k)` for `|t| ≤ S r`, solved in turn by the two-sided Grönwall inequality
  `l6c_gronwall` (Mathlib's `norm_le_gronwallBound_of_norm_deriv_right_le`, also backward in time).
  The result is `chartFlow_estimates`.
* **Switching functions near `J`**: `P_{e_k}(X)` is Lipschitz near `J` (`norm_controlP_sub_le`),
  `⟨M, P_{e_k}(J)⟩ = -2 RR(ζ^k, cayleyZ M)` for symmetric traceless `M`
  (`traceForm_controlP_J`), and on the chart `H(Z₀₁₀) = χ₂₃ = 0` (`lieChart_section`).
* **The first control** (TeX 11706–11718): the derivative of `χ₂₃` along the `e₂`-flow at
  `t = 0` (`hasDerivAt_chi23`) is `-4√3 ℓ̃₂₁ r² + O(r³)`, positive for small `r` when
  `ℓ̃₂₁ < 0` (`eventually_chi23Deriv_pos`); the Hamiltonian is maximized over the simplex at
  a vertex when `⟨X, Z_{e_m}⟩ < 0` for all `m` (`hamiltonian_le_of_vertices`).
* **`q_out`**: its coordinates (13.5.1), `H_F(q_out, ζ) = 0` (`ham_qOutCart`).

*Departure from the paper:* the book expands the closed-form solutions (matrix exponentials and
quadratures) in a power series in `r₀`; the Grönwall comparison gives the same leading terms with
a remainder bound, without expanding the quadratures. Norms of matrices are the `L^∞` operator
norm (`open scoped Matrix.Norms.Operator`).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology Asymptotics
open TriFuller
open scoped Matrix.Norms.Operator

/-! ### Norms of `2 × 2` matrices -/

theorem abs_apply_le_opNorm (A : Mat2) (i j : Fin 2) : |A i j| ≤ ‖A‖ := by
  simpa only [Real.norm_eq_abs] using Matrix.norm_apply_le_linfty_opNorm A i j

private theorem l6c_norm_le (A : Mat2) : ‖A‖ ≤ |A 0 0| + |A 0 1| + |A 1 0| + |A 1 1| := by
  have hle : ((Finset.univ : Finset (Fin 2)).sup fun i ↦ ∑ j : Fin 2, ‖A i j‖₊) ≤
      ‖A 0 0‖₊ + ‖A 0 1‖₊ + ‖A 1 0‖₊ + ‖A 1 1‖₊ := by
    refine Finset.sup_le fun i _ ↦ ?_
    fin_cases i
    · simp only [Fin.sum_univ_two, Fin.zero_eta, Fin.isValue]
      rw [add_assoc]; exact le_add_right le_rfl
    · simp only [Fin.sum_univ_two, Fin.mk_one, Fin.isValue]
      calc ‖A 1 0‖₊ + ‖A 1 1‖₊ ≤ ‖A 0 0‖₊ + ‖A 0 1‖₊ + (‖A 1 0‖₊ + ‖A 1 1‖₊) :=
            le_add_left le_rfl
        _ = _ := by ring
  rw [Matrix.linfty_opNorm_def]
  have := NNReal.coe_le_coe.2 hle
  push_cast at this
  simpa only [coe_nnnorm, Real.norm_eq_abs] using this

private theorem l6c_norm_br (A B : Mat2) : ‖A * B - B * A‖ ≤ 2 * ‖A‖ * ‖B‖ := by
  calc ‖A * B - B * A‖ ≤ ‖A * B‖ + ‖B * A‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖A‖ * ‖B‖ := by ring

theorem abs_traceForm_le_opNorm (A B : Mat2) : |traceForm A B| ≤ 2 * ‖A‖ * ‖B‖ := by
  have h := norm_mul_le A B
  have h0 := abs_apply_le_opNorm (A * B) 0 0
  have h1 := abs_apply_le_opNorm (A * B) 1 1
  rw [traceForm, Matrix.trace_fin_two]
  calc |(A * B) 0 0 + (A * B) 1 1| ≤ |(A * B) 0 0| + |(A * B) 1 1| := abs_add_le _ _
    _ ≤ 2 * ‖A‖ * ‖B‖ := by linarith

theorem norm_cayleyZ_le_opNorm (A : Mat2) : ‖cayleyZ A‖ ≤ 2 * ‖A‖ := by
  have h := Complex.norm_le_abs_re_add_abs_im (cayleyZ A)
  have h0 := abs_apply_le_opNorm A 0 0
  have h1 := abs_apply_le_opNorm A 0 1
  have h2 := abs_apply_le_opNorm A 1 0
  have hre : (cayleyZ A).re = (A 0 1 + A 1 0) / 2 := rfl
  have him : (cayleyZ A).im = A 0 0 := rfl
  rw [hre, him] at h
  have : |(A 0 1 + A 1 0) / 2| ≤ ‖A‖ := by
    rw [abs_div, abs_two]
    have := abs_add_le (A 0 1) (A 1 0)
    linarith
  linarith

private theorem l6c_gronwallBound_le {δ K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound δ K ε x ≤ (δ + ε * x) * Real.exp (K * x) := by
  rcases eq_or_lt_of_le hK with rfl | hK'
  · simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hK'.ne']
    have he : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have h1 := Real.add_one_le_exp (-(K * x))
      have h2 : Real.exp (-(K * x)) * Real.exp (K * x) = 1 := by
        rw [← Real.exp_add]; simp
      have h3 := Real.exp_pos (K * x)
      nlinarith
    have : ε / K * (Real.exp (K * x) - 1) ≤ ε * x * Real.exp (K * x) := by
      calc ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (K * x * Real.exp (K * x)) :=
            mul_le_mul_of_nonneg_left he (div_nonneg hε hK)
        _ = ε * x * Real.exp (K * x) := by field_simp
    nlinarith

/-- **Grönwall, two-sided**: a curve differentiable everywhere whose derivative is bounded by
`K ‖E‖ + ε` between `0` and `T` satisfies `‖E T‖ ≤ (δ + ε |T|) e^{K |T|}`. -/
private theorem l6c_gronwall {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {E E' : ℝ → F}
    {T K δ ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (hE : ∀ t, HasDerivAt E (E' t) t)
    (h0 : ‖E 0‖ ≤ δ) (hb : ∀ t ∈ uIcc 0 T, ‖E' t‖ ≤ K * ‖E t‖ + ε) :
    ‖E T‖ ≤ (δ + ε * |T|) * Real.exp (K * |T|) := by
  have key : ∀ {E E' : ℝ → F} {T : ℝ}, 0 ≤ T → (∀ t, HasDerivAt E (E' t) t) → ‖E 0‖ ≤ δ →
      (∀ t ∈ Icc 0 T, ‖E' t‖ ≤ K * ‖E t‖ + ε) → ‖E T‖ ≤ (δ + ε * T) * Real.exp (K * T) := by
    intro E E' T hT hE h0 hb
    have := norm_le_gronwallBound_of_norm_deriv_right_le (f := E) (f' := E') (a := 0) (b := T)
      (fun t _ ↦ (hE t).continuousAt.continuousWithinAt) (fun t _ ↦ (hE t).hasDerivWithinAt) h0
      (fun t ht ↦ hb t (Ico_subset_Icc_self ht)) T ⟨hT, le_rfl⟩
    rw [sub_zero] at this
    exact this.trans (l6c_gronwallBound_le hK hε)
  rcases le_total 0 T with hT | hT
  · rw [abs_of_nonneg hT]
    exact key hT hE h0 fun t ht ↦ hb t (by rw [uIcc_of_le hT]; exact ht)
  · rw [abs_of_nonpos hT]
    have hE' : ∀ t, HasDerivAt (fun s ↦ E (-s)) ((-1 : ℝ) • E' (-t)) t := fun t ↦
      (hE (-t)).scomp t (hasDerivAt_neg t)
    have := key (E := fun s ↦ E (-s)) (T := -T) (by linarith) hE' (by simpa using h0)
      (fun t ht ↦ by
        rw [norm_smul, norm_neg, norm_one, one_mul]
        exact hb (-t) (by rw [uIcc_of_ge hT]; constructor <;> linarith [ht.1, ht.2]))
    simpa using this

/-- `[A, B]`. -/
def matLie (A B : Mat2) : Mat2 := A * B - B * A

noncomputable def chartP0 : Mat2 := (-(3 / 2) : ℝ) • controlMatrix (vertex 1)
def chartA (x : Fin 3 → ℝ) : Mat2 := !![1, x 0; x 0, -1]
def chartB (x : Fin 3 → ℝ) : Mat2 := !![x 1, x 2; x 2, -x 1]
def chartC (x : Fin 3 → ℝ) : Mat2 := !![0, 2 * (x 1 + x 2 * x 0); 2 * (x 1 + x 2 * x 0), 0]

noncomputable def chartXF (x : Fin 3 → ℝ) (r t : ℝ) : Mat2 :=
  J + r • chartA x + t • matLie chartP0 J

noncomputable def chartBF (x : Fin 3 → ℝ) (r t : ℝ) : Mat2 :=
  r ^ 2 • chartB x - (3 / 2 * r * t) • matLie J (chartA x) -
    (3 / 4 * t ^ 2) • matLie J (matLie chartP0 J)

noncomputable def chartCF (x : Fin 3 → ℝ) (r t : ℝ) : Mat2 :=
  r ^ 3 • chartC x + (r ^ 2 * t) • matLie J (chartB x) -
    (3 / 4 * r * t ^ 2) • matLie J (matLie J (chartA x)) -
    (1 / 4 * t ^ 3) • matLie J (matLie J (matLie chartP0 J))

private theorem l6c_hasDerivAt_XF (x : Fin 3 → ℝ) (r t : ℝ) :
    HasDerivAt (chartXF x r) (matLie chartP0 J) t := by
  have h := HasDerivAt.const_add (J + r • chartA x) ((hasDerivAt_id t).smul_const (matLie chartP0
      J))
  exact h.congr_deriv (one_smul ℝ _)

private theorem l6c_hasDerivAt_BF (x : Fin 3 → ℝ) (r t : ℝ) :
    HasDerivAt (chartBF x r) ((-(3 / 2) : ℝ) • matLie J (chartXF x r t - J)) t := by
  have h1 := ((hasDerivAt_id t).const_mul (3 / 2 * r)).smul_const (matLie J (chartA x))
  have h2 := ((hasDerivAt_pow 2 t).const_mul (3 / 4 : ℝ)).smul_const
    (matLie J (matLie chartP0 J))
  have h := ((hasDerivAt_const t (r ^ 2 • chartB x)).fun_sub h1).fun_sub h2
  refine h.congr_deriv ?_
  ext i j
  simp [chartXF, matLie, Matrix.mul_add, Matrix.add_mul, 
    Matrix.mul_sub, Matrix.sub_mul]
  ring

private theorem l6c_hasDerivAt_CF (x : Fin 3 → ℝ) (r t : ℝ) :
    HasDerivAt (chartCF x r) (matLie J (chartBF x r t)) t := by
  have h1 := ((hasDerivAt_id t).const_mul (r ^ 2)).smul_const (matLie J (chartB x))
  have h2 := ((hasDerivAt_pow 2 t).const_mul (3 / 4 * r)).smul_const
    (matLie J (matLie J (chartA x)))
  have h3 := ((hasDerivAt_pow 3 t).const_mul (1 / 4 : ℝ)).smul_const
    (matLie J (matLie J (matLie chartP0 J)))
  have h := (((hasDerivAt_const t (r ^ 3 • chartC x)).fun_add h1).fun_sub h2).fun_sub h3
  refine h.congr_deriv ?_
  ext i j
  simp [chartBF, matLie, 
    Matrix.mul_sub, Matrix.sub_mul]
  ring

/-! ### The chart in closed form -/

private noncomputable def l6c_Xt (x0 r : ℝ) : Mat2 := !![1, (x0 - r) / (1 + r * x0); x0, -1]
noncomputable def chartL12 (x1 x2 r : ℝ) : ℝ := (3 / 2 * x2 + r ^ 2 * x1 ^ 2) / (3 / 2 - r ^ 2 * x2)
private noncomputable def l6c_Lt (x1 x2 r : ℝ) : Mat2 := !![x1, chartL12 x1 x2 r; x2, -x1]
noncomputable def chartHt (x : Fin 3 → ℝ) (r : ℝ) : ℝ :=
  r * (x 1 ^ 2 + x 2 ^ 2) / (3 / 2 - r ^ 2 * x 2) + 2 * x 1 + chartL12 (x 1) (x 2) r * x 0 +
    x 2 * (x 0 - r) / (1 + r * x 0)
noncomputable def chartN (x0 r : ℝ) : Mat2 := !![r, (1 - r ^ 2) / (1 + r * x0); 1 + r * x0, -r]

private theorem l6c_lieX_eq {r x0 : ℝ} (h : 1 + r * x0 ≠ 0) : lieX r x0 = J + r • l6c_Xt x0 r := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lieX, J, l6c_Xt]
  field_simp
  ring

private theorem l6c_lieΛ₁_eq {r x1 x2 : ℝ} (h : 3 / 2 - r ^ 2 * x2 ≠ 0) :
    lieΛ₁ r x1 x2 = (-(3 / 2) : ℝ) • J + r ^ 2 • l6c_Lt x1 x2 r := by
  have h' : 3 - r ^ 2 * 2 * x2 ≠ 0 := fun h0 ↦ h (by linarith)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lieΛ₁, J, l6c_Lt, chartL12]
  field_simp
  ring

private theorem l6c_reducedHam_eq {r : ℝ} {x : Fin 3 → ℝ} (h1 : 1 + r * x 0 ≠ 0)
    (h2 : 3 / 2 - r ^ 2 * x 2 ≠ 0) :
    reducedHam (lieΛ₁ r (x 1) (x 2)) (lieX r (x 0)) = r ^ 3 * chartHt x r := by
  have h' : 3 - r ^ 2 * 2 * x 2 ≠ 0 := fun h0 ↦ h2 (by linarith)
  simp [reducedHam, traceForm, lieΛ₁, lieX, J, chartHt, chartL12, Matrix.trace_fin_two,
    ]
  field_simp
  ring

private theorem l6c_sl2Dual_eq (r x0 hh : ℝ) (h : 1 + r * x0 ≠ 0) :
    sl2Dual (lieX r x0) (controlMatrix (vertex 1)) (controlMatrix (vertex 2)) 0
      (traceForm (lieX r x0) (controlMatrix (vertex 1)) * hh)
      (traceForm (lieX r x0) (controlMatrix (vertex 2)) * hh) = hh • chartN x0 r := by
  have hs0 : √3 ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [sl2Dual, lieX, chartN, traceForm, controlMatrix, vertex, Matrix.trace_fin_two]
    field_simp
    ring

private theorem l6c_lieChart_ΛR {r : ℝ} {x : Fin 3 → ℝ} (h1 : 1 + r * x 0 ≠ 0)
    (h2 : 3 / 2 - r ^ 2 * x 2 ≠ 0) :
    (lieChart (r, x)).2.2 = r ^ 3 • (chartHt x r • chartN (x 0) r) := by
  change lieΛR _ _ = _
  rw [lieΛR, l6c_sl2Dual_eq _ _ _ h1, l6c_reducedHam_eq h1 h2, smul_smul]

private theorem l6c_traceForm_Z1_lieX (r x0 : ℝ) :
    traceForm (controlMatrix (vertex 1)) (lieX r x0) = 2 * r / √3 - 2 / 3 * (1 + r * x0) := by
  simp [traceForm, controlMatrix, vertex, lieX, Matrix.trace_fin_two]
  ring

private theorem l6c_Xt_zero (x : Fin 3 → ℝ) : l6c_Xt (x 0) 0 = chartA x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [l6c_Xt, chartA]

private theorem l6c_Lt_zero (x : Fin 3 → ℝ) : l6c_Lt (x 1) (x 2) 0 = chartB x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [l6c_Lt, chartB, chartL12]

private theorem l6c_htN_zero (x : Fin 3 → ℝ) : chartHt x 0 • chartN (x 0) 0 = chartC x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chartHt, chartN, chartC, chartL12] <;> ring

/-! ### Lipschitz bounds at `0` from differentiability -/

private theorem l6c_exists_norm_sub_le {G : ℝ → Mat2}
    (hG : ∀ i j, DifferentiableAt ℝ (fun r ↦ G r i j) 0) :
    ∃ C, ∀ᶠ r in 𝓝 (0 : ℝ), ‖G r - G 0‖ ≤ C * |r| := by
  have key : ∀ i j, ∃ C, ∀ᶠ r in 𝓝 (0 : ℝ), |G r i j - G 0 i j| ≤ C * |r| := fun i j ↦ by
    obtain ⟨C, hC⟩ := (hG i j).isBigO_sub.bound
    exact ⟨C, hC.mono fun r hr ↦ by simpa only [Real.norm_eq_abs, sub_zero] using hr⟩
  obtain ⟨C00, h00⟩ := key 0 0
  obtain ⟨C01, h01⟩ := key 0 1
  obtain ⟨C10, h10⟩ := key 1 0
  obtain ⟨C11, h11⟩ := key 1 1
  refine ⟨C00 + C01 + C10 + C11, (h00.and (h01.and (h10.and h11))).mono fun r hr ↦ ?_⟩
  obtain ⟨a, b, c, d⟩ := hr
  calc ‖G r - G 0‖ ≤ |(G r - G 0) 0 0| + |(G r - G 0) 0 1| + |(G r - G 0) 1 0| +
        |(G r - G 0) 1 1| := l6c_norm_le _
    _ ≤ C00 * |r| + C01 * |r| + C10 * |r| + C11 * |r| := by
        simp only [Matrix.sub_apply]; linarith
    _ = (C00 + C01 + C10 + C11) * |r| := by ring

private theorem l6c_eventually_ne {f : ℝ → ℝ} (hf : ContinuousAt f 0) (h0 : f 0 ≠ 0) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), f r ≠ 0 :=
  (hf.eventually_ne h0).filter_mono nhdsWithin_le_nhds

/-- The chart conditions `1 + r x̃₂₁ ≠ 0`, `3/2 - r² ℓ̃₂₁ ≠ 0`, `0 < r < 1` hold for small
`r > 0`. -/
theorem eventually_chart_conditions (x : Fin 3 → ℝ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r < 1 ∧ 1 + r * x 0 ≠ 0 ∧ 3 / 2 - r ^ 2 * x 2 ≠ 0 := by
  refine eventually_mem_nhdsWithin.and ((show ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 1 from
    Ioo_mem_nhdsGT (by norm_num)).mono fun r hr ↦ hr.2) |>.and
    ((l6c_eventually_ne (f := fun r ↦ 1 + r * x 0) (by fun_prop)
    (by norm_num)).and (l6c_eventually_ne (f := fun r ↦ 3 / 2 - r ^ 2 * x 2) (by fun_prop)
    (by norm_num))) |>.mono fun r ⟨⟨h0, h1⟩, h2, h3⟩ ↦ ⟨h0, h1, h2, h3⟩

private theorem l6c_static_P (x : Fin 3 → ℝ) :
    ∃ C, ∀ᶠ r in 𝓝[>] (0 : ℝ), ‖iso_vfP 1 (lieChart (r, x)) - chartP0‖ ≤ C * r := by
  set G : ℝ → Mat2 := fun r ↦ (2 * r / √3 - 2 / 3 * (1 + r * x 0))⁻¹ • controlMatrix (vertex 1)
  have hG0 : G 0 = chartP0 := by
    simp only [G, chartP0]; norm_num
  obtain ⟨C, hC⟩ := l6c_exists_norm_sub_le (G := G) fun i j ↦ by
    simp only [G, Matrix.smul_apply, smul_eq_mul]
    exact ((by fun_prop : DifferentiableAt ℝ (fun r : ℝ ↦ 2 * r / √3 - 2 / 3 * (1 + r * x 0)) 0).inv
      (by norm_num)).mul_const _
  refine ⟨C, (eventually_mem_nhdsWithin.and (hC.filter_mono nhdsWithin_le_nhds)).mono
    fun r ⟨hr, h⟩ ↦ ?_⟩
  have hP : iso_vfP 1 (lieChart (r, x)) = G r := by
    simp only [iso_vfP, controlP, lieChart, G]
    rw [l6c_traceForm_Z1_lieX]
  rw [hP, ← hG0]
  calc ‖G r - G 0‖ ≤ C * |r| := h
    _ = C * r := by rw [abs_of_pos (show (0 : ℝ) < r from hr)]

private theorem l6c_static_X (x : Fin 3 → ℝ) :
    ∃ C, ∀ᶠ r in 𝓝[>] (0 : ℝ), ‖(lieChart (r, x)).1 - chartXF x r 0‖ ≤ C * r ^ 2 := by
  obtain ⟨C, hC⟩ := l6c_exists_norm_sub_le (G := l6c_Xt (x 0)) fun i j ↦ by
    fin_cases i <;> fin_cases j <;>
      simp only [l6c_Xt, Fin.isValue, Fin.zero_eta, Fin.mk_one, of_apply, cons_val', cons_val_zero,
        cons_val_one, cons_val_fin_one, differentiableAt_const]
    fun_prop (disch := norm_num)
  refine ⟨C, ((eventually_chart_conditions x).and (hC.filter_mono nhdsWithin_le_nhds)).mono
    fun r ⟨⟨hr0, _, h1, _⟩, h⟩ ↦ ?_⟩
  have e : (lieChart (r, x)).1 - chartXF x r 0 = r • (l6c_Xt (x 0) r - l6c_Xt (x 0) 0) := by
    rw [show (lieChart (r, x)).1 = lieX r (x 0) from rfl, l6c_lieX_eq h1, l6c_Xt_zero, chartXF]
    simp only [zero_smul, add_zero, smul_sub]
    abel
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
  calc r * ‖l6c_Xt (x 0) r - l6c_Xt (x 0) 0‖ ≤ r * (C * |r|) := mul_le_mul_of_nonneg_left h hr0.le
    _ = C * r ^ 2 := by rw [abs_of_pos hr0]; ring

private theorem l6c_static_B (x : Fin 3 → ℝ) :
    ∃ C, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖(lieChart (r, x)).2.1 + (3 / 2 : ℝ) • J - chartBF x r 0‖ ≤ C * r ^ 3 := by
  obtain ⟨C, hC⟩ := l6c_exists_norm_sub_le (G := l6c_Lt (x 1) (x 2)) fun i j ↦ by
    fin_cases i <;> fin_cases j <;>
      simp only [l6c_Lt, Fin.isValue, chartL12, Fin.zero_eta, Fin.mk_one, of_apply, cons_val',
        cons_val_zero, cons_val_one, cons_val_fin_one, differentiableAt_const]
    fun_prop (disch := norm_num)
  refine ⟨C, ((eventually_chart_conditions x).and (hC.filter_mono nhdsWithin_le_nhds)).mono
    fun r ⟨⟨hr0, _, _, h2⟩, h⟩ ↦ ?_⟩
  have e : (lieChart (r, x)).2.1 + (3 / 2 : ℝ) • J - chartBF x r 0 =
      r ^ 2 • (l6c_Lt (x 1) (x 2) r - l6c_Lt (x 1) (x 2) 0) := by
    rw [show (lieChart (r, x)).2.1 = lieΛ₁ r (x 1) (x 2) from rfl, l6c_lieΛ₁_eq h2, l6c_Lt_zero,
      chartBF]
    simp only [mul_zero, zero_smul, sub_zero, smul_sub, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    module
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc r ^ 2 * ‖l6c_Lt (x 1) (x 2) r - l6c_Lt (x 1) (x 2) 0‖ ≤ r ^ 2 * (C * |r|) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = C * r ^ 3 := by rw [abs_of_pos hr0]; ring

theorem norm_lieChart_ΛR_sub_le (x : Fin 3 → ℝ) :
    ∃ C, ∀ᶠ r in 𝓝[>] (0 : ℝ), ‖(lieChart (r, x)).2.2 - chartCF x r 0‖ ≤ C * r ^ 4 := by
  obtain ⟨C, hC⟩ := l6c_exists_norm_sub_le (G := fun r ↦ chartHt x r • chartN (x 0) r)
    fun i j ↦ by
      fin_cases i <;> fin_cases j <;>
        simp only [chartHt, Fin.isValue, chartL12, chartN, Fin.zero_eta, Fin.mk_one,
          Matrix.smul_apply, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one,
          smul_eq_mul, mul_neg, differentiableAt_fun_neg_iff] <;>
        fun_prop (disch := norm_num)
  refine ⟨C, ((eventually_chart_conditions x).and (hC.filter_mono nhdsWithin_le_nhds)).mono
    fun r ⟨⟨hr0, _, h1, h2⟩, h⟩ ↦ ?_⟩
  have e : (lieChart (r, x)).2.2 - chartCF x r 0 =
      r ^ 3 • (chartHt x r • chartN (x 0) r - chartHt x 0 • chartN (x 0) 0) := by
    rw [l6c_lieChart_ΛR h1 h2, l6c_htN_zero, chartCF]
    simp only [mul_zero, zero_smul, sub_zero, add_zero, smul_sub, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc r ^ 3 * ‖chartHt x r • chartN (x 0) r - chartHt x 0 • chartN (x 0) 0‖ ≤ r ^ 3 * (C * |r|) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = C * r ^ 4 := by rw [abs_of_pos hr0]; ring

/-! ### Bounds on the approximants -/

theorem norm_chartXF_sub_J_le (x : Fin 3 → ℝ) {S r t : ℝ} (hr : 0 ≤ r) (ht : |t| ≤ S * r) :
    ‖chartXF x r t - J‖ ≤ (‖chartA x‖ + S * ‖matLie chartP0 J‖) * r := by
  have e : chartXF x r t - J = r • chartA x + t • matLie chartP0 J := by
    simp only [chartXF]; abel
  rw [e]
  calc ‖r • chartA x + t • matLie chartP0 J‖ ≤ ‖r • chartA x‖ + ‖t • matLie chartP0 J‖ :=
        norm_add_le _ _
    _ = r * ‖chartA x‖ + |t| * ‖matLie chartP0 J‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr]
    _ ≤ r * ‖chartA x‖ + (S * r) * ‖matLie chartP0 J‖ := by gcongr
    _ = (‖chartA x‖ + S * ‖matLie chartP0 J‖) * r := by ring

private theorem l6c_norm_smul_le {c d : ℝ} (A : Mat2) (h : |c| ≤ d) : ‖c • A‖ ≤ d * ‖A‖ := by
  rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

private theorem l6c_norm_BF (x : Fin 3 → ℝ) {S r t : ℝ} (hr : 0 ≤ r) (ht : |t| ≤ S * r) :
    ‖chartBF x r t‖ ≤ (‖chartB x‖ + 3 / 2 * S * ‖matLie J (chartA x)‖ +
      3 / 4 * S ^ 2 * ‖matLie J (matLie chartP0 J)‖) * r ^ 2 := by
  have ht0 := abs_nonneg t
  have h1 := l6c_norm_smul_le (chartB x) (show |r ^ 2| ≤ r ^ 2 from (abs_of_nonneg
    (by positivity)).le)
  have h2 := l6c_norm_smul_le (matLie J (chartA x)) (show |3 / 2 * r * t| ≤ 3 / 2 * S * r ^ 2 by
    rw [abs_mul, abs_mul, abs_of_nonneg hr, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    nlinarith)
  have h3 := l6c_norm_smul_le (matLie J (matLie chartP0 J))
    (show |3 / 4 * t ^ 2| ≤ 3 / 4 * S ^ 2 * r ^ 2 by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4), abs_pow]
      have := pow_le_pow_left₀ ht0 ht 2
      nlinarith)
  unfold chartBF
  calc _ ≤ ‖r ^ 2 • chartB x‖ + ‖(3 / 2 * r * t) • matLie J (chartA x)‖ +
        ‖(3 / 4 * t ^ 2) • matLie J (matLie chartP0 J)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by nlinarith

theorem norm_chartCF_le (x : Fin 3 → ℝ) {S r t : ℝ} (hr : 0 ≤ r) (ht : |t| ≤ S * r) :
    ‖chartCF x r t‖ ≤ (‖chartC x‖ + S * ‖matLie J (chartB x)‖ +
      3 / 4 * S ^ 2 * ‖matLie J (matLie J (chartA x))‖ +
      1 / 4 * S ^ 3 * ‖matLie J (matLie J (matLie chartP0 J))‖) * r ^ 3 := by
  have ht0 := abs_nonneg t
  have ht2 := pow_le_pow_left₀ ht0 ht 2
  have ht3 := pow_le_pow_left₀ ht0 ht 3
  have h1 := l6c_norm_smul_le (chartC x) (show |r ^ 3| ≤ r ^ 3 from (abs_of_nonneg
    (by positivity)).le)
  have h2 := l6c_norm_smul_le (matLie J (chartB x)) (show |r ^ 2 * t| ≤ S * r ^ 3 by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ r ^ 2)]
    have := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ r ^ 2)
    nlinarith)
  have h3 := l6c_norm_smul_le (matLie J (matLie J (chartA x)))
    (show |3 / 4 * r * t ^ 2| ≤ 3 / 4 * S ^ 2 * r ^ 3 by
      rw [abs_mul, abs_mul, abs_of_nonneg hr, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4),
        abs_pow]
      have := mul_le_mul_of_nonneg_left ht2 hr
      nlinarith)
  have h4 := l6c_norm_smul_le (matLie J (matLie J (matLie chartP0 J)))
    (show |1 / 4 * t ^ 3| ≤ 1 / 4 * S ^ 3 * r ^ 3 by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), abs_pow]
      nlinarith)
  unfold chartCF
  calc _ ≤ ‖r ^ 3 • chartC x‖ + ‖(r ^ 2 * t) • matLie J (chartB x)‖ +
        ‖(3 / 4 * r * t ^ 2) • matLie J (matLie J (chartA x))‖ +
        ‖(1 / 4 * t ^ 3) • matLie J (matLie J (matLie chartP0 J))‖ :=
        (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by nlinarith

/-! ### The three Grönwall steps -/

private theorem l6c_abs_le_of_mem_uIcc {s t : ℝ} (hs : s ∈ uIcc 0 t) : |s| ≤ |t| := by
  rcases Set.mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith

/-- Along the vertex flow `e₂`, `P = Z_{e₂}/⟨Z_{e₂}, X⟩` is constant, so `X' = [P, X]`. -/
private theorem l6c_hasDerivAt_flowX (q : iso_PhasePt) (t : ℝ) :
    HasDerivAt (fun s ↦ (iso_vertexFlow 1 q s).1)
      (matLie (iso_vfP 1 q) (iso_vertexFlow 1 q t).1) t := by
  have h := (iso_vertexFlow_solution 1 q t).1
  have hc : controlP (vertex 1) (iso_vertexFlow 1 q t).1 = iso_vfP 1 q := ivf_controlP_vfX 1 q t
  rw [hc] at h
  exact h.hasDerivAt

private theorem l6c_hasDerivAt_flowΛ₁ (q : iso_PhasePt) (t : ℝ) :
    HasDerivAt (fun s ↦ (iso_vertexFlow 1 q s).2.1)
      (matLie (iso_vertexFlow 1 q t).2.1 (iso_vertexFlow 1 q t).1) t :=
  (iso_vertexFlow_solution 1 q t).2.1.hasDerivAt

theorem hasDerivAt_vertexFlow_ΛR (q : iso_PhasePt) (t : ℝ) :
    HasDerivAt (fun s ↦ (iso_vertexFlow 1 q s).2.2)
      (matLie (iso_vfP 1 q) (iso_vertexFlow 1 q t).2.2 -
        traceForm (iso_vertexFlow 1 q t).2.2 (iso_vfP 1 q) •
          matLie (iso_vfP 1 q) (iso_vertexFlow 1 q t).1 -
        matLie ((iso_vertexFlow 1 q t).2.1 + (3 / 2 : ℝ) • J) (iso_vertexFlow 1 q t).1) t := by
  have h := (iso_vertexFlow_solution 1 q t).2.2.1
  have hc : controlP (vertex 1) (iso_vertexFlow 1 q t).1 = iso_vfP 1 q := ivf_controlP_vfX 1 q t
  rw [costateRHS, hc] at h
  refine h.hasDerivAt.congr_deriv ?_
  ext i j
  simp [matLie, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_add, Matrix.add_mul,
    ]
  ring

private theorem l6c_step_X (x : Fin 3 → ℝ) {S : ℝ} (hS : 0 ≤ S) (Cp C2 : ℝ) :
    ∃ K, ∀ r, 0 < r → r ≤ 1 → ‖iso_vfP 1 (lieChart (r, x)) - chartP0‖ ≤ Cp * r →
      ‖(lieChart (r, x)).1 - chartXF x r 0‖ ≤ C2 * r ^ 2 →
      ∀ t, |t| ≤ S * r → ‖(iso_vertexFlow 1 (lieChart (r, x)) t).1 - chartXF x r t‖ ≤ K * r ^ 2 :=
          by
  set Kp := ‖chartP0‖ + |Cp|
  set a := ‖chartA x‖ + S * ‖matLie chartP0 J‖
  refine ⟨(|C2| + (2 * |Cp| * ‖J‖ + 2 * Kp * a) * S) * Real.exp (2 * Kp * S),
    fun r hr hr1 hP hX0 t ht ↦ ?_⟩
  set q := lieChart (r, x)
  set P := iso_vfP 1 q
  have hPn : ‖P‖ ≤ Kp := by
    have := norm_le_insert' P chartP0
    have : Cp * r ≤ |Cp| := by
      calc Cp * r ≤ |Cp| * r := mul_le_mul_of_nonneg_right (le_abs_self _) hr.le
        _ ≤ |Cp| * 1 := mul_le_mul_of_nonneg_left hr1 (abs_nonneg _)
        _ = |Cp| := mul_one _
    linarith
  have hKp : 0 ≤ Kp := by positivity
  have ha : 0 ≤ a := by positivity
  set E : ℝ → Mat2 := fun s ↦ (iso_vertexFlow 1 q s).1 - chartXF x r s
  have hE : ∀ s, HasDerivAt E (matLie P (iso_vertexFlow 1 q s).1 - matLie chartP0 J) s :=
    fun s ↦ (l6c_hasDerivAt_flowX q s).sub (l6c_hasDerivAt_XF x r s)
  have hb : ∀ s ∈ uIcc 0 t, ‖matLie P (iso_vertexFlow 1 q s).1 - matLie chartP0 J‖ ≤
      2 * Kp * ‖E s‖ + (2 * |Cp| * ‖J‖ + 2 * Kp * a) * r := by
    intro s hs
    have hs' : |s| ≤ S * r := (l6c_abs_le_of_mem_uIcc hs).trans ht
    have e : matLie P (iso_vertexFlow 1 q s).1 - matLie chartP0 J =
        matLie P (E s) + matLie (P - chartP0) J + matLie P (chartXF x r s - J) := by
      simp only [E, matLie]; noncomm_ring
    rw [e]
    have h1 := l6c_norm_br P (E s)
    have h2 := l6c_norm_br (P - chartP0) J
    have h3 := l6c_norm_br P (chartXF x r s - J)
    have h4 := norm_chartXF_sub_J_le x hr.le hs'
    have hPP : ‖P - chartP0‖ ≤ |Cp| * r :=
      hP.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hr.le)
    calc _ ≤ ‖matLie P (E s)‖ + ‖matLie (P - chartP0) J‖ + ‖matLie P (chartXF x r s - J)‖ :=
          norm_add₃_le
      _ ≤ 2 * Kp * ‖E s‖ + 2 * (|Cp| * r) * ‖J‖ + 2 * Kp * (a * r) := by
          refine add_le_add (add_le_add (h1.trans ?_) (h2.trans ?_)) (h3.trans ?_)
          · gcongr
          · gcongr
          · gcongr
      _ = _ := by ring
  have hE0 : ‖E 0‖ ≤ |C2| * r ^ 2 := by
    have : E 0 = (lieChart (r, x)).1 - chartXF x r 0 := by
      simp only [E, q, ivf_vertexFlow_zero]
    rw [this]
    exact hX0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hg := l6c_gronwall (T := t) (by positivity) (by positivity) hE hE0 hb
  have ht' : |t| ≤ S := ht.trans (by nlinarith)
  calc ‖E t‖ ≤ (|C2| * r ^ 2 + (2 * |Cp| * ‖J‖ + 2 * Kp * a) * r * |t|) *
        Real.exp (2 * Kp * |t|) := hg
    _ ≤ (|C2| * r ^ 2 + (2 * |Cp| * ‖J‖ + 2 * Kp * a) * r * (S * r)) *
        Real.exp (2 * Kp * S) := by
        gcongr
    _ = _ := by ring

private theorem l6c_step_B (x : Fin 3 → ℝ) {S : ℝ} (hS : 0 ≤ S) (KX C3 : ℝ) :
    ∃ K, ∀ r, 0 < r → r ≤ 1 →
      (∀ t, |t| ≤ S * r →
        ‖(iso_vertexFlow 1 (lieChart (r, x)) t).1 - chartXF x r t‖ ≤ KX * r ^ 2) →
      ‖(lieChart (r, x)).2.1 + (3 / 2 : ℝ) • J - chartBF x r 0‖ ≤ C3 * r ^ 3 →
      ∀ t, |t| ≤ S * r →
        ‖(iso_vertexFlow 1 (lieChart (r, x)) t).2.1 + (3 / 2 : ℝ) • J - chartBF x r t‖ ≤
          K * r ^ 3 := by
  set a := ‖chartA x‖ + S * ‖matLie chartP0 J‖
  set b := ‖chartB x‖ + 3 / 2 * S * ‖matLie J (chartA x)‖ +
    3 / 4 * S ^ 2 * ‖matLie J (matLie chartP0 J)‖
  set Kx := ‖J‖ + a + |KX|
  refine ⟨(|C3| + (2 * b * Kx + 3 * ‖J‖ * |KX|) * S) * Real.exp (2 * Kx * S),
    fun r hr hr1 hX hB0 t ht ↦ ?_⟩
  set q := lieChart (r, x)
  have ha : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hKx : 0 ≤ Kx := by positivity
  have hXF : ∀ s, |s| ≤ S * r → ‖(iso_vertexFlow 1 q s).1 - chartXF x r s‖ ≤ |KX| * r ^ 2 :=
    fun s hs ↦ (hX s hs).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hXn : ∀ s, |s| ≤ S * r → ‖(iso_vertexFlow 1 q s).1‖ ≤ Kx := by
    intro s hs
    have h1 := hXF s hs
    have h2 := norm_chartXF_sub_J_le x hr.le hs
    have e : (iso_vertexFlow 1 q s).1 = ((iso_vertexFlow 1 q s).1 - chartXF x r s) +
        (chartXF x r s - J) + J := by abel
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    calc ‖(iso_vertexFlow 1 q s).1‖ ≤ ‖(iso_vertexFlow 1 q s).1 - chartXF x r s‖ +
          ‖chartXF x r s - J‖ + ‖J‖ := by
          rw [e]; exact norm_add₃_le.trans (le_of_eq (by abel_nf))
      _ ≤ |KX| * 1 + a * 1 + ‖J‖ := by
          gcongr
          · exact h1.trans (mul_le_mul_of_nonneg_left hr2 (abs_nonneg _))
          · exact h2.trans (mul_le_mul_of_nonneg_left hr1 ha)
      _ = Kx := by ring
  set E : ℝ → Mat2 := fun s ↦ (iso_vertexFlow 1 q s).2.1 + (3 / 2 : ℝ) • J - chartBF x r s
  have hE : ∀ s, HasDerivAt E (matLie (iso_vertexFlow 1 q s).2.1 (iso_vertexFlow 1 q s).1 -
      (-(3 / 2) : ℝ) • matLie J (chartXF x r s - J)) s :=
    fun s ↦ ((l6c_hasDerivAt_flowΛ₁ q s).add_const _).sub (l6c_hasDerivAt_BF x r s)
  have hb : ∀ s ∈ uIcc 0 t, ‖matLie (iso_vertexFlow 1 q s).2.1 (iso_vertexFlow 1 q s).1 -
      (-(3 / 2) : ℝ) • matLie J (chartXF x r s - J)‖ ≤
      2 * Kx * ‖E s‖ + (2 * b * Kx + 3 * ‖J‖ * |KX|) * r ^ 2 := by
    intro s hs
    have hs' : |s| ≤ S * r := (l6c_abs_le_of_mem_uIcc hs).trans ht
    have e : matLie (iso_vertexFlow 1 q s).2.1 (iso_vertexFlow 1 q s).1 -
        (-(3 / 2) : ℝ) • matLie J (chartXF x r s - J) =
        matLie (E s + chartBF x r s) (iso_vertexFlow 1 q s).1 -
          (3 / 2 : ℝ) • matLie J ((iso_vertexFlow 1 q s).1 - chartXF x r s) := by
      simp only [E, matLie, smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul, add_mul, mul_add,
        smul_sub]
      module
    rw [e]
    have h1 := l6c_norm_br (E s + chartBF x r s) (iso_vertexFlow 1 q s).1
    have h2 := l6c_norm_br J ((iso_vertexFlow 1 q s).1 - chartXF x r s)
    have h3 := l6c_norm_BF x hr.le hs'
    have h4 := hXn s hs'
    have h5 := hXF s hs'
    have h6 := norm_add_le (E s) (chartBF x r s)
    calc _ ≤ ‖matLie (E s + chartBF x r s) (iso_vertexFlow 1 q s).1‖ +
          ‖(3 / 2 : ℝ) • matLie J ((iso_vertexFlow 1 q s).1 - chartXF x r s)‖ := norm_sub_le _ _
      _ ≤ 2 * (‖E s‖ + b * r ^ 2) * Kx + 3 / 2 * (2 * ‖J‖ * (|KX| * r ^ 2)) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
          gcongr
          · exact h1.trans (by gcongr; exact h6.trans (by gcongr))
          · exact h2.trans (by gcongr)
      _ = _ := by ring
  have hE0 : ‖E 0‖ ≤ |C3| * r ^ 3 := by
    have : E 0 = (lieChart (r, x)).2.1 + (3 / 2 : ℝ) • J - chartBF x r 0 := by
      simp only [E, q, ivf_vertexFlow_zero]
    rw [this]
    exact hB0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hg := l6c_gronwall (T := t) (by positivity) (by positivity) hE hE0 hb
  have ht' : |t| ≤ S := ht.trans (by nlinarith)
  calc ‖E t‖ ≤ (|C3| * r ^ 3 + (2 * b * Kx + 3 * ‖J‖ * |KX|) * r ^ 2 * |t|) *
        Real.exp (2 * Kx * |t|) := hg
    _ ≤ (|C3| * r ^ 3 + (2 * b * Kx + 3 * ‖J‖ * |KX|) * r ^ 2 * (S * r)) *
        Real.exp (2 * Kx * S) := by
        gcongr
    _ = _ := by ring

private theorem l6c_step_C (x : Fin 3 → ℝ) {S : ℝ} (hS : 0 ≤ S) (Cp KX KB C4 : ℝ) :
    ∃ K, ∀ r, 0 < r → r ≤ 1 → ‖iso_vfP 1 (lieChart (r, x)) - chartP0‖ ≤ Cp * r →
      (∀ t, |t| ≤ S * r →
        ‖(iso_vertexFlow 1 (lieChart (r, x)) t).1 - chartXF x r t‖ ≤ KX * r ^ 2) →
      (∀ t, |t| ≤ S * r →
        ‖(iso_vertexFlow 1 (lieChart (r, x)) t).2.1 + (3 / 2 : ℝ) • J - chartBF x r t‖ ≤
          KB * r ^ 3) →
      ‖(lieChart (r, x)).2.2 - chartCF x r 0‖ ≤ C4 * r ^ 4 →
      ∀ t, |t| ≤ S * r →
        ‖(iso_vertexFlow 1 (lieChart (r, x)) t).2.2 - chartCF x r t‖ ≤ K * r ^ 4 := by
  set Kp := ‖chartP0‖ + |Cp|
  set a := ‖chartA x‖ + S * ‖matLie chartP0 J‖
  set b := ‖chartB x‖ + 3 / 2 * S * ‖matLie J (chartA x)‖ +
    3 / 4 * S ^ 2 * ‖matLie J (matLie chartP0 J)‖
  set c := ‖chartC x‖ + S * ‖matLie J (chartB x)‖ +
      3 / 4 * S ^ 2 * ‖matLie J (matLie J (chartA x))‖ +
      1 / 4 * S ^ 3 * ‖matLie J (matLie J (matLie chartP0 J))‖
  set Kx := ‖J‖ + a + |KX|
  set K3 := 2 * Kp + 4 * Kp ^ 2 * Kx
  set e3 := K3 * c + 2 * ‖J‖ * |KB| + 2 * (|KB| + b) * (|KX| + a)
  refine ⟨(|C4| + e3 * S) * Real.exp (K3 * S), fun r hr hr1 hP hX hB hC0 t ht ↦ ?_⟩
  set q := lieChart (r, x)
  set P := iso_vfP 1 q
  have ha : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hKp : 0 ≤ Kp := by positivity
  have hKx : 0 ≤ Kx := by positivity
  have hK3 : 0 ≤ K3 := by positivity
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hPn : ‖P‖ ≤ Kp := by
    have := norm_le_insert' P chartP0
    have : Cp * r ≤ |Cp| := by
      calc Cp * r ≤ |Cp| * r := mul_le_mul_of_nonneg_right (le_abs_self _) hr.le
        _ ≤ |Cp| * 1 := mul_le_mul_of_nonneg_left hr1 (abs_nonneg _)
        _ = |Cp| := mul_one _
    linarith
  have hXF : ∀ s, |s| ≤ S * r → ‖(iso_vertexFlow 1 q s).1 - chartXF x r s‖ ≤ |KX| * r ^ 2 :=
    fun s hs ↦ (hX s hs).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hBF : ∀ s, |s| ≤ S * r →
      ‖(iso_vertexFlow 1 q s).2.1 + (3 / 2 : ℝ) • J - chartBF x r s‖ ≤ |KB| * r ^ 3 :=
    fun s hs ↦ (hB s hs).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hXJ : ∀ s, |s| ≤ S * r → ‖(iso_vertexFlow 1 q s).1 - J‖ ≤ (|KX| + a) * r := by
    intro s hs
    have h1 := hXF s hs
    have h2 := norm_chartXF_sub_J_le x hr.le hs
    calc ‖(iso_vertexFlow 1 q s).1 - J‖ ≤ ‖(iso_vertexFlow 1 q s).1 - chartXF x r s‖ +
          ‖chartXF x r s - J‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ |KX| * r ^ 2 + a * r := add_le_add h1 h2
      _ ≤ (|KX| + a) * r := by
          have : r ^ 2 ≤ r := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left this (abs_nonneg KX)]
  have hXn : ∀ s, |s| ≤ S * r → ‖(iso_vertexFlow 1 q s).1‖ ≤ Kx := by
    intro s hs
    have h1 := hXJ s hs
    calc ‖(iso_vertexFlow 1 q s).1‖ ≤ ‖(iso_vertexFlow 1 q s).1 - J‖ + ‖J‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ (|KX| + a) * 1 + ‖J‖ := by
          gcongr; exact h1.trans (mul_le_mul_of_nonneg_left hr1 (by positivity))
      _ = Kx := by ring
  have hBn : ∀ s, |s| ≤ S * r →
      ‖(iso_vertexFlow 1 q s).2.1 + (3 / 2 : ℝ) • J‖ ≤ (|KB| + b) * r ^ 2 := by
    intro s hs
    have h1 := hBF s hs
    have h2 := l6c_norm_BF x hr.le hs
    calc ‖(iso_vertexFlow 1 q s).2.1 + (3 / 2 : ℝ) • J‖ ≤
          ‖(iso_vertexFlow 1 q s).2.1 + (3 / 2 : ℝ) • J - chartBF x r s‖ + ‖chartBF x r s‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ |KB| * r ^ 3 + b * r ^ 2 := add_le_add h1 h2
      _ ≤ (|KB| + b) * r ^ 2 := by
          have : r ^ 3 ≤ r ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left this (abs_nonneg KB)]
  set E : ℝ → Mat2 := fun s ↦ (iso_vertexFlow 1 q s).2.2 - chartCF x r s
  set E' : ℝ → Mat2 := fun s ↦ (matLie P (iso_vertexFlow 1 q s).2.2 -
      traceForm (iso_vertexFlow 1 q s).2.2 P • matLie P (iso_vertexFlow 1 q s).1 -
      matLie ((iso_vertexFlow 1 q s).2.1 + (3 / 2 : ℝ) • J) (iso_vertexFlow 1 q s).1) -
      matLie J (chartBF x r s)
  have hE : ∀ s, HasDerivAt E (E' s) s :=
    fun s ↦ (hasDerivAt_vertexFlow_ΛR q s).sub (l6c_hasDerivAt_CF x r s)
  have hb : ∀ s ∈ uIcc 0 t, ‖E' s‖ ≤ K3 * ‖E s‖ + e3 * r ^ 3 := by
    intro s hs
    have hs' : |s| ≤ S * r := (l6c_abs_le_of_mem_uIcc hs).trans ht
    have e : E' s = matLie P (iso_vertexFlow 1 q s).2.2 -
        traceForm (iso_vertexFlow 1 q s).2.2 P • matLie P (iso_vertexFlow 1 q s).1 +
        matLie J ((iso_vertexFlow 1 q s).2.1 + (3 / 2 : ℝ) • J - chartBF x r s) -
        matLie ((iso_vertexFlow 1 q s).2.1 + (3 / 2 : ℝ) • J) ((iso_vertexFlow 1 q s).1 - J) := by
      simp only [E', matLie, smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul, add_mul, mul_add,
        smul_sub]
      module
    set L := (iso_vertexFlow 1 q s).2.2
    set X := (iso_vertexFlow 1 q s).1
    set B := (iso_vertexFlow 1 q s).2.1 + (3 / 2 : ℝ) • J
    have hL : ‖L‖ ≤ ‖E s‖ + c * r ^ 3 := by
      have h := norm_chartCF_le x hr.le hs'
      calc ‖L‖ ≤ ‖L - chartCF x r s‖ + ‖chartCF x r s‖ := norm_le_norm_sub_add _ _
        _ ≤ ‖E s‖ + c * r ^ 3 := add_le_add le_rfl h
    have h1 : ‖matLie P L‖ ≤ 2 * Kp * ‖L‖ :=
      (l6c_norm_br P L).trans (by gcongr)
    have h2 : ‖traceForm L P • matLie P X‖ ≤ 4 * Kp ^ 2 * Kx * ‖L‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have ht1 := abs_traceForm_le_opNorm L P
      have ht2 := l6c_norm_br P X
      have hXs := hXn s hs'
      calc |traceForm L P| * ‖matLie P X‖ ≤ (2 * ‖L‖ * Kp) * (2 * Kp * Kx) := by
            gcongr
            · exact ht1.trans (by gcongr)
            · exact ht2.trans (by gcongr)
        _ = 4 * Kp ^ 2 * Kx * ‖L‖ := by ring
    have h3 : ‖matLie J (B - chartBF x r s)‖ ≤ 2 * ‖J‖ * |KB| * r ^ 3 := by
      have := l6c_norm_br J (B - chartBF x r s)
      have h' := hBF s hs'
      calc _ ≤ 2 * ‖J‖ * ‖B - chartBF x r s‖ := this
        _ ≤ 2 * ‖J‖ * (|KB| * r ^ 3) := by gcongr
        _ = _ := by ring
    have h4 : ‖matLie B (X - J)‖ ≤ 2 * (|KB| + b) * (|KX| + a) * r ^ 3 := by
      have := l6c_norm_br B (X - J)
      have hB' := hBn s hs'
      have hX' := hXJ s hs'
      calc _ ≤ 2 * ‖B‖ * ‖X - J‖ := this
        _ ≤ 2 * ((|KB| + b) * r ^ 2) * ((|KX| + a) * r) := by gcongr
        _ = _ := by ring
    rw [e]
    calc _ ≤ ‖matLie P L‖ + ‖traceForm L P • matLie P X‖ + ‖matLie J (B - chartBF x r s)‖ +
          ‖matLie B (X - J)‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
          exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ 2 * Kp * ‖L‖ + 4 * Kp ^ 2 * Kx * ‖L‖ + 2 * ‖J‖ * |KB| * r ^ 3 +
          2 * (|KB| + b) * (|KX| + a) * r ^ 3 := by gcongr
      _ = K3 * ‖L‖ + (2 * ‖J‖ * |KB| + 2 * (|KB| + b) * (|KX| + a)) * r ^ 3 := by ring
      _ ≤ K3 * (‖E s‖ + c * r ^ 3) + (2 * ‖J‖ * |KB| + 2 * (|KB| + b) * (|KX| + a)) * r ^ 3 := by
          gcongr
      _ = K3 * ‖E s‖ + e3 * r ^ 3 := by ring
  have hE0 : ‖E 0‖ ≤ |C4| * r ^ 4 := by
    have : E 0 = (lieChart (r, x)).2.2 - chartCF x r 0 := by
      simp only [E, q, ivf_vertexFlow_zero]
    rw [this]
    exact hC0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have he3 : 0 ≤ e3 := by positivity
  have hg := l6c_gronwall (T := t) hK3 (by positivity) hE hE0 hb
  have ht' : |t| ≤ S := ht.trans (by nlinarith)
  calc ‖E t‖ ≤ (|C4| * r ^ 4 + e3 * r ^ 3 * |t|) * Real.exp (K3 * |t|) := hg
    _ ≤ (|C4| * r ^ 4 + e3 * r ^ 3 * (S * r)) * Real.exp (K3 * S) := by
        refine mul_le_mul (add_le_add le_rfl (mul_le_mul_of_nonneg_left ht
          (mul_nonneg he3 (pow_nonneg hr.le 3)))) (Real.exp_le_exp.2
          (mul_le_mul_of_nonneg_left ht' hK3)) (Real.exp_pos _).le ?_
        exact add_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hr.le 4))
          (mul_nonneg (mul_nonneg he3 (pow_nonneg hr.le 3)) (mul_nonneg hS hr.le))
    _ = _ := by ring

/-- **The rescaled vertex flow from the chart** (the core of Lemmas 14.2.3–14.2.4): for fixed
`x̃` and `S ≥ 0`, uniformly for `|t| ≤ S r`, the `e₂`-flow from `lieChart (r, x̃)` satisfies
`X(t) = XF + O(r²)`, `Λ₁(t) + (3/2) J = BF + O(r³)`, `Λ_R(t) = CF + O(r⁴)`. -/
theorem chartFlow_estimates (x : Fin 3 → ℝ) {S : ℝ} (hS : 0 ≤ S) :
    ∃ C, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ t, |t| ≤ S * r →
      ‖(iso_vertexFlow 1 (lieChart (r, x)) t).1 - chartXF x r t‖ ≤ C * r ^ 2 ∧
      ‖(iso_vertexFlow 1 (lieChart (r, x)) t).2.1 + (3 / 2 : ℝ) • J - chartBF x r t‖ ≤
        C * r ^ 3 ∧
      ‖(iso_vertexFlow 1 (lieChart (r, x)) t).2.2 - chartCF x r t‖ ≤ C * r ^ 4 := by
  obtain ⟨Cp, hCp⟩ := l6c_static_P x
  obtain ⟨C2, hC2⟩ := l6c_static_X x
  obtain ⟨C3, hC3⟩ := l6c_static_B x
  obtain ⟨C4, hC4⟩ := norm_lieChart_ΛR_sub_le x
  obtain ⟨KX, hKX⟩ := l6c_step_X x hS Cp C2
  obtain ⟨KB, hKB⟩ := l6c_step_B x hS KX C3
  obtain ⟨KC, hKC⟩ := l6c_step_C x hS Cp KX KB C4
  refine ⟨max KX (max KB KC), ((eventually_chart_conditions x).and (hCp.and (hC2.and (hC3.and
      hC4)))).mono
    fun r ⟨⟨hr0, hr1, _, _⟩, hP, hX0, hB0, hC0⟩ t ht ↦ ?_⟩
  have hX := hKX r hr0 hr1.le hP hX0
  have hB := hKB r hr0 hr1.le hX hB0
  have hC := hKC r hr0 hr1.le hP hX hB hC0
  refine ⟨(hX t ht).trans ?_, (hB t ht).trans ?_, (hC t ht).trans ?_⟩ <;>
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-! ### Algebra of the Cayley coordinate and the approximants -/

/-- `cayleyZ` is additive. -/
theorem cayleyZ_add (A B : Mat2) : cayleyZ (A + B) = cayleyZ A + cayleyZ B := by
  apply Complex.ext <;> simp [cayleyZ]
  ring

/-- `cayleyZ` commutes with subtraction. -/
theorem cayleyZ_sub (A B : Mat2) : cayleyZ (A - B) = cayleyZ A - cayleyZ B := by
  apply Complex.ext <;> simp [cayleyZ]
  ring

/-- `cayleyZ` is `ℝ`-linear. -/
theorem cayleyZ_smul (c : ℝ) (A : Mat2) : cayleyZ (c • A) = (c : ℂ) * cayleyZ A := by
  apply Complex.ext <;> simp [cayleyZ]
  ring

/-- The Cayley coordinate of `J` vanishes (the singular locus). -/
theorem cayleyZ_J : cayleyZ J = 0 := by
  apply Complex.ext <;> simp [cayleyZ, J]

/-- `√3² = 3`. -/
private theorem l6c_sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- `[P₀, J] = [[1, √3], [√3, -1]]` (so `cayleyZ [P₀, J]/2 = -iζ`). -/
theorem matLie_chartP0_J : matLie chartP0 J = !![1, √3; √3, -1] := by
  have h := l6c_sqrt3_sq
  have h0 : √3 ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matLie, chartP0, J, controlMatrix, vertex] <;> field_simp <;>
    linarith

/-- `[J, M]` for `M = [[a, b], [c, d]]`. -/
theorem matLie_J_of (a b c d : ℝ) :
    matLie J !![a, b; c, d] = !![-c - b, a - d; a - d, b + c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matLie, J]
  ring

/-- The approximant `XF` in coordinates. -/
theorem chartXF_eq (x : Fin 3 → ℝ) (r t : ℝ) :
    chartXF x r t = !![r + t, -1 + r * x 0 + t * √3; 1 + r * x 0 + t * √3, -r - t] := by
  rw [chartXF, matLie_chartP0_J]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chartA, J]
  ring

/-- `XF` at `t = 0`. -/
private theorem l6c_XF_zero (x : Fin 3 → ℝ) (r : ℝ) : chartXF x r 0 = J + r • chartA x := by
  simp [chartXF]

/-- `BF` at `t = 0`. -/
private theorem l6c_BF_zero (x : Fin 3 → ℝ) (r : ℝ) : chartBF x r 0 = r ^ 2 • chartB x := by
  simp [chartBF]

/-- `CF` at `t = 0`. -/
private theorem l6c_CF_zero (x : Fin 3 → ℝ) (r : ℝ) : chartCF x r 0 = r ^ 3 • chartC x := by
  simp [chartCF]

/-! ### The switching functions near the singular locus -/

/-- The trace form is additive in its second argument. -/
theorem traceForm_sub_right (M A B : Mat2) :
    traceForm M (A - B) = traceForm M A - traceForm M B := by
  simp only [traceForm, Matrix.mul_sub, Matrix.trace_sub]

/-- The trace form is additive in its first argument. -/
private theorem l6c_traceForm_add_left (A B M : Mat2) :
    traceForm (A + B) M = traceForm A M + traceForm B M := by
  simp only [traceForm, Matrix.add_mul, Matrix.trace_add]

/-- `RR(a - b, c) = RR(a, c) - RR(b, c)`. -/
theorem RR_sub_left (a b c : ℂ) : RR (a - b) c = RR a c - RR b c := by
  simp only [RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im]; ring

/-- `⟨Z_{e_k}, J⟩ = -2/3` for each vertex. -/
private theorem l6c_traceForm_vertex_J (k : Fin 3) : traceForm (controlMatrix (vertex k)) J = -(2 /
    3) := by
  fin_cases k <;> simp [traceForm, controlMatrix, vertex, J, Matrix.trace_fin_two,
    ] <;> norm_num

/-- `P_{e_k}(J) = -(3/2) Z_{e_k}`. -/
private theorem l6c_controlP_J (k : Fin 3) :
    controlP (vertex k) J = (-(3 / 2) : ℝ) • controlMatrix (vertex k) := by
  rw [controlP, l6c_traceForm_vertex_J]; norm_num

/-- `⟨M, P_{e_k}(J)⟩ = -2 RR(ζ^k, cayleyZ M)` for symmetric traceless `M`. -/
theorem traceForm_controlP_J (k : Fin 3) {M : Mat2} (h1 : M 1 0 = M 0 1)
    (h2 : M 1 1 = -M 0 0) :
    traceForm M (controlP (vertex k) J) = -2 * RR (ζ ^ (k : ℕ)) (cayleyZ M) := by
  have h3 := l6c_sqrt3_sq
  have h0 : √3 ≠ 0 := by positivity
  rw [l6c_controlP_J, RR_eq_re_mul_add_im_mul]
  fin_cases k <;>
    simp [traceForm, controlMatrix, vertex, Matrix.trace_fin_two, Matrix.mul_apply, cayleyZ,
      h1, h2, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im] <;> field_simp <;> ring_nf <;> simp only [h3] <;>
    ring_nf

/-- The approximant `CF` is symmetric and traceless. -/
theorem chartCF_symm (x : Fin 3 → ℝ) (r t : ℝ) :
    chartCF x r t 1 0 = chartCF x r t 0 1 ∧ chartCF x r t 1 1 = -chartCF x r t 0 0 := by
  rw [chartCF, matLie_chartP0_J, chartA, chartB, chartC]
  simp only [matLie_J_of]
  constructor <;> simp
  ring

/-- `P_{e_k}(X) = Z_{e_k}/⟨Z_{e_k}, X⟩` is Lipschitz near `X = J`. -/
theorem norm_controlP_sub_le (k : Fin 3) {X : Mat2}
    (h : 2 * ‖controlMatrix (vertex k)‖ * ‖X - J‖ ≤ 1 / 3) :
    ‖controlP (vertex k) X - controlP (vertex k) J‖ ≤
      9 * ‖controlMatrix (vertex k)‖ ^ 2 * ‖X - J‖ := by
  set Z := controlMatrix (vertex k)
  have hJ := l6c_traceForm_vertex_J k
  have hd : |traceForm Z X - traceForm Z J| ≤ 2 * ‖Z‖ * ‖X - J‖ := by
    rw [← traceForm_sub_right]; exact abs_traceForm_le_opNorm Z (X - J)
  rw [hJ] at hd
  have hX : 1 / 3 ≤ |traceForm Z X| := by
    have := abs_le.1 (hd.trans h)
    rw [abs_of_neg (by linarith)]
    linarith
  have hX0 : traceForm Z X ≠ 0 := fun h0 ↦ by rw [h0, abs_zero] at hX; norm_num at hX
  have e : controlP (vertex k) X - controlP (vertex k) J =
      ((traceForm Z X)⁻¹ - (-(2 / 3) : ℝ)⁻¹) • Z := by
    rw [sub_smul]; simp only [controlP, Z, hJ]
  rw [e, norm_smul, Real.norm_eq_abs]
  have hinv : (traceForm Z X)⁻¹ - (-(2 / 3) : ℝ)⁻¹ =
      (-(2 / 3) - traceForm Z X) / (traceForm Z X * (-(2 / 3))) := by
    field_simp
    ring
  have habs : |(traceForm Z X)⁻¹ - (-(2 / 3) : ℝ)⁻¹| ≤ 9 / 2 * (2 * ‖Z‖ * ‖X - J‖) := by
    rw [hinv, abs_div, abs_mul, abs_sub_comm]
    rw [div_le_iff₀ (by positivity)]
    have h23 : |(-(2 / 3) : ℝ)| = 2 / 3 := by norm_num
    rw [h23]
    have hpos : 0 ≤ 2 * ‖Z‖ * ‖X - J‖ := by positivity
    nlinarith
  calc |(traceForm Z X)⁻¹ - (-(2 / 3) : ℝ)⁻¹| * ‖Z‖ ≤ 9 / 2 * (2 * ‖Z‖ * ‖X - J‖) * ‖Z‖ :=
        mul_le_mul_of_nonneg_right habs (norm_nonneg _)
    _ = 9 * ‖Z‖ ^ 2 * ‖X - J‖ := by ring

/-- `⟨N, Z_{e_k}⟩ = ⟨X, Z_{e_k}⟩` for `k = 2, 3` (the vertices with `(Z_{e_k})₂₁ = 0`). -/
private theorem l6c_traceForm_N (x0 r : ℝ) (k : Fin 3) (hk : k ≠ 0) :
    traceForm (chartN x0 r) (controlMatrix (vertex k)) =
      traceForm (lieX r x0) (controlMatrix (vertex k)) := by
  fin_cases k
  · exact absurd rfl hk
  all_goals simp [traceForm, chartN, lieX, controlMatrix, vertex, Matrix.trace_fin_two,
    ]

/-- On the chart, `H(Z₀₁₀) = 0` and `χ₂₃ = 0` ((14.1.3)), from the closed forms. -/
theorem lieChart_section {r : ℝ} {x : Fin 3 → ℝ} (h1 : 1 + r * x 0 ≠ 0)
    (h2 : 3 / 2 - r ^ 2 * x 2 ≠ 0)
    (h3 : traceForm (lieX r (x 0)) (controlMatrix (vertex 1)) ≠ 0)
    (h4 : traceForm (lieX r (x 0)) (controlMatrix (vertex 2)) ≠ 0) :
    hamiltonian (-1) (lieChart (r, x)).2.1 (lieChart (r, x)).2.2 (lieChart (r, x)).1
      (vertex 1) = 0 ∧ switchingFn 1 2 (lieChart (r, x)).2.2 (lieChart (r, x)).1 = 0 := by
  have hR := l6c_lieChart_ΛR h1 h2
  have hH := l6c_reducedHam_eq h1 h2
  have hX : (lieChart (r, x)).1 = lieX r (x 0) := rfl
  have hL : (lieChart (r, x)).2.1 = lieΛ₁ r (x 1) (x 2) := rfl
  have hsymm : ∀ A B : Mat2, traceForm A B = traceForm B A := fun A B ↦ Matrix.trace_mul_comm A B
  have hN1 := l6c_traceForm_N (x 0) r 1 (by decide)
  have hN2 := l6c_traceForm_N (x 0) r 2 (by decide)
  have hsm : ∀ (c : ℝ) (A B : Mat2), traceForm (c • A) B = c * traceForm A B := fun c A B ↦ by
    simp [traceForm, Matrix.trace_smul]
  constructor
  · rw [hamiltonian, hR, hX, hL]
    have e : traceForm (lieΛ₁ r (x 1) (x 2) - (3 / 2 * -1 : ℝ) • J) (lieX r (x 0)) =
        reducedHam (lieΛ₁ r (x 1) (x 2)) (lieX r (x 0)) := by
      rw [reducedHam]; congr 1; module
    rw [e, hH, hsm, hsm, hN1]
    field_simp
    ring
  · have hsm' : ∀ (c : ℝ) (A B : Mat2), traceForm A (c • B) = c * traceForm A B := fun c A B ↦ by
      simp [traceForm, Matrix.trace_smul]
    have hN1' : traceForm (controlMatrix (vertex 1)) (chartN (x 0) r) =
        traceForm (controlMatrix (vertex 1)) (lieX r (x 0)) := by rw [hsymm, hN1, hsymm]
    have hN2' : traceForm (controlMatrix (vertex 2)) (chartN (x 0) r) =
        traceForm (controlMatrix (vertex 2)) (lieX r (x 0)) := by rw [hsymm, hN2, hsymm]
    have h3' : traceForm (controlMatrix (vertex 1)) (lieX r (x 0)) ≠ 0 := by rwa [hsymm]
    have h4' : traceForm (controlMatrix (vertex 2)) (lieX r (x 0)) ≠ 0 := by rwa [hsymm]
    rw [switchingFn, hR, hX, traceForm_sub_right, controlP, controlP, hsm', hsm', hsm, hsm,
      hsm, hsm, hsymm (chartN _ _), hsymm (chartN _ _), hN1', hN2']
    field_simp
    ring

/-- A continuous function vanishing at `0` is eventually small to the right of `0`. -/
private theorem l6c_eventually_lt_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ r in 𝓝[>] (0 : ℝ), f r < ε :=
  ((hf.tendsto 0).eventually (gt_mem_nhds (by rwa [h0]))).filter_mono nhdsWithin_le_nhds

/-- `⟨X(r, x̃), Z_{e_k}⟩ < -1/3` for small `r > 0` (it tends to `⟨J, Z_{e_k}⟩ = -2/3`). -/
theorem eventually_traceForm_lieX_lt (x : Fin 3 → ℝ) (k : Fin 3) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), traceForm (lieX r (x 0)) (controlMatrix (vertex k)) < -(1 / 3) := by
  obtain ⟨C, hC⟩ := l6c_static_X x
  set Z := controlMatrix (vertex k)
  have hsmall := l6c_eventually_lt_of_continuous
    (f := fun r ↦ 2 * ((|C| * r ^ 2 + |r| * ‖chartA x‖) * ‖Z‖)) (by fun_prop) (by simp)
    (by norm_num : (0 : ℝ) < 1 / 3)
  refine ((hC.and hsmall).and eventually_mem_nhdsWithin).mono fun r ⟨⟨h, hs⟩, hr⟩ ↦ ?_
  have hr0 : (0 : ℝ) < r := hr
  have hJ : traceForm J Z = -(2 / 3) := by
    rw [show traceForm J Z = traceForm Z J from Matrix.trace_mul_comm _ _]
    exact l6c_traceForm_vertex_J k
  have hXJ : ‖lieX r (x 0) - J‖ ≤ |C| * r ^ 2 + |r| * ‖chartA x‖ := by
    have e : lieX r (x 0) - J = ((lieChart (r, x)).1 - chartXF x r 0) + r • chartA x := by
      simp only [lieChart, chartXF, zero_smul, add_zero]; abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add (h.trans ?_) ?_)
    · gcongr; exact le_abs_self _
    · rw [norm_smul, Real.norm_eq_abs]
  have hd : |traceForm (lieX r (x 0)) Z - traceForm J Z| ≤ 2 * ‖lieX r (x 0) - J‖ * ‖Z‖ := by
    have : traceForm (lieX r (x 0)) Z - traceForm J Z = traceForm (lieX r (x 0) - J) Z := by
      simp [traceForm, Matrix.sub_mul, Matrix.trace_sub]
    rw [this]; exact abs_traceForm_le_opNorm _ _
  have : 2 * ‖lieX r (x 0) - J‖ * ‖Z‖ < 1 / 3 := by
    calc 2 * ‖lieX r (x 0) - J‖ * ‖Z‖ ≤ 2 * ((|C| * r ^ 2 + |r| * ‖chartA x‖) * ‖Z‖) := by
          rw [← mul_assoc]; gcongr
      _ < 1 / 3 := hs
  rw [hJ] at hd
  have := (abs_le.1 hd).2
  linarith

/-! ### The first control: the derivative of `χ₂₃` at `t = 0` -/

/-- The derivative of the trace form along two curves. -/
private theorem l6c_hasDerivAt_traceForm {A B : ℝ → Mat2} {A' B' : Mat2} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s ↦ traceForm (A s) (B s)) (traceForm A' (B t) + traceForm (A t) B') t := by
  have h := hA.hasDerivAtEntrywise.mul hB.hasDerivAtEntrywise
  have h2 := (h 0 0).add (h 1 1)
  simp only [traceForm, Matrix.trace_fin_two]
  refine h2.congr_deriv ?_
  simp only [Matrix.add_apply]
  ring

/-- The derivative at `t = 0` of `χ₂₃` along the `e₂`-flow from `q`. -/
noncomputable def chi23Deriv (q : iso_PhasePt) : ℝ :=
  traceForm (matLie (iso_vfP 1 q) q.2.2 - traceForm q.2.2 (iso_vfP 1 q) •
      matLie (iso_vfP 1 q) q.1 - matLie (q.2.1 + (3 / 2 : ℝ) • J) q.1)
      (controlP (vertex 2) q.1 - iso_vfP 1 q) +
    traceForm q.2.2 ((-traceForm (controlMatrix (vertex 2)) (matLie (iso_vfP 1 q) q.1) /
      traceForm (controlMatrix (vertex 2)) q.1 ^ 2) • controlMatrix (vertex 2))

/-- The derivative at `t = 0` of `χ₂₃` along the `e₂`-flow. -/
theorem hasDerivAt_chi23 (q : iso_PhasePt)
    (hg : traceForm (controlMatrix (vertex 2)) q.1 ≠ 0) :
    HasDerivAt (fun t ↦ switchingFn 1 2 (iso_vertexFlow 1 q t).2.2 (iso_vertexFlow 1 q t).1)
      (chi23Deriv q) 0 := by
  set P := iso_vfP 1 q
  set Z := controlMatrix (vertex 2)
  have h0 := ivf_vertexFlow_zero 1 q
  have hX := l6c_hasDerivAt_flowX q 0
  have hR := hasDerivAt_vertexFlow_ΛR q 0
  rw [h0] at hX hR
  have hg' : HasDerivAt (fun t ↦ traceForm Z (iso_vertexFlow 1 q t).1)
      (traceForm Z (matLie P q.1)) 0 := by
    have := l6c_hasDerivAt_traceForm (hasDerivAt_const (0 : ℝ) Z) hX
    simp only [h0] at this
    refine this.congr_deriv ?_
    simp [traceForm, P]
  have hg0 : traceForm Z (iso_vertexFlow 1 q 0).1 ≠ 0 := by rwa [h0]
  have hQ := ((hg'.inv hg0).smul_const Z).sub_const P
  have hf := l6c_hasDerivAt_traceForm hR hQ
  have e : (fun t ↦ switchingFn 1 2 (iso_vertexFlow 1 q t).2.2 (iso_vertexFlow 1 q t).1) =
      fun t ↦ traceForm (iso_vertexFlow 1 q t).2.2
        ((traceForm Z (iso_vertexFlow 1 q t).1)⁻¹ • Z - P) := by
    funext t
    have hc : controlP (vertex 1) (iso_vertexFlow 1 q t).1 = P := ivf_controlP_vfX 1 q t
    rw [switchingFn, hc]
    rfl
  rw [e]
  refine hf.congr_deriv ?_
  simp only [Pi.inv_apply, h0, controlP, Z, P, chi23Deriv]

/-- The leading term of `χ₂₃'(0)`: `⟨[J, B̃], P_{e₃}(J) - P_{e₂}(J)⟩ = -4√3 ℓ̃₂₁`. -/
private theorem l6c_traceForm_W (x : Fin 3 → ℝ) :
    traceForm (matLie J (chartB x)) (controlP (vertex 2) J - controlP (vertex 1) J) =
      -4 * √3 * x 2 := by
  have hW : matLie J (chartB x) = !![-x 2 - x 2, x 1 - -x 1; x 1 - -x 1, x 2 + x 2] := by
    rw [chartB, matLie_J_of]
  have h1 : (matLie J (chartB x)) 1 0 = (matLie J (chartB x)) 0 1 := by rw [hW]; simp
  have h2 : (matLie J (chartB x)) 1 1 = -(matLie J (chartB x)) 0 0 := by rw [hW]; simp
  rw [traceForm_sub_right, traceForm_controlP_J 2 h1 h2, traceForm_controlP_J 1 h1 h2,
    hW]
  simp [RR_eq_re_mul_add_im_mul, cayleyZ, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im]
  ring

/-- `χ₂₃` increases along the `e₂`-flow from the chart, for small `r`, when `ℓ̃₂₁ < 0`:
the derivative at `t = 0` is `-4√3 ℓ̃₂₁ r² + O(r³)`. -/
theorem eventually_chi23Deriv_pos (x : Fin 3 → ℝ) (hx2 : x 2 < 0) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < chi23Deriv (lieChart (r, x)) := by
  obtain ⟨Cp, hCp⟩ := l6c_static_P x
  obtain ⟨C2, hC2⟩ := l6c_static_X x
  obtain ⟨C3, hC3⟩ := l6c_static_B x
  obtain ⟨C4, hC4⟩ := norm_lieChart_ΛR_sub_le x
  set Z := controlMatrix (vertex 2)
  set W := matLie J (chartB x)
  set T0 := -4 * √3 * x 2
  have hT0 : 0 < T0 := by
    have : 0 < √3 := by positivity
    have : 0 < √3 * -x 2 := mul_pos this (by linarith)
    linarith [show T0 = 4 * (√3 * -x 2) by simp only [T0]; ring]
  set Cx := |C2| + ‖chartA x‖
  set Kx := ‖J‖ + Cx
  set CR := |C4| + ‖chartC x‖
  set Kp := ‖chartP0‖ + |Cp|
  set e1 := 2 * Kp * CR + 4 * Kp ^ 2 * Kx * CR + 2 * |C3| * Kx + 2 * ‖chartB x‖ * Cx
  set e2 := 9 * ‖Z‖ ^ 2 * Cx + |Cp|
  set e3 := ‖controlP (vertex 2) J‖ + ‖chartP0‖ + e2
  set e4 := 9 * (2 * ‖Z‖ * (2 * Kp * Kx)) * ‖Z‖
  set K := 2 * ‖W‖ * e2 + 2 * e1 * e3 + 2 * CR * e4
  have hCx : 0 ≤ Cx := by positivity
  have hK : 0 ≤ K := by positivity
  set δ := min 1 (min (1 / (6 * ‖Z‖ * Cx + 1)) (T0 / (K + 1)))
  have hδ : 0 < δ := lt_min one_pos (lt_min (by positivity) (by positivity))
  filter_upwards [hCp, hC2, hC3, hC4, eventually_traceForm_lieX_lt x 2,
    (show ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 δ from Ioo_mem_nhdsGT hδ)] with r hP hX hB hC hg hr
  have hr0 : 0 < r := hr.1
  have hr1 : r ≤ 1 := hr.2.le.trans (min_le_left _ _)
  have hrZ : r * (6 * ‖Z‖ * Cx + 1) ≤ 1 := by
    have := hr.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    rwa [le_div_iff₀ (by positivity)] at this
  have hrK : r * (K + 1) ≤ T0 := by
    have := hr.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    rwa [le_div_iff₀ (by positivity)] at this
  set q := lieChart (r, x)
  set P := iso_vfP 1 q
  set X := q.1
  set B := q.2.1 + (3 / 2 : ℝ) • J
  set L := q.2.2
  -- basic bounds
  have hr2 : r ^ 2 ≤ r := by
    calc r ^ 2 = r * r := sq r
      _ ≤ r * 1 := by gcongr
      _ = r := mul_one r
  have hXJ : ‖X - J‖ ≤ Cx * r := by
    have e : X - J = (q.1 - chartXF x r 0) + r • chartA x := by
      rw [l6c_XF_zero]; abel
    rw [e]
    calc _ ≤ ‖q.1 - chartXF x r 0‖ + ‖r • chartA x‖ := norm_add_le _ _
      _ ≤ |C2| * r + r * ‖chartA x‖ := by
          refine add_le_add (hX.trans ?_) ?_
          · have : r ^ 2 ≤ r := hr2
            calc C2 * r ^ 2 ≤ |C2| * r ^ 2 := by gcongr; exact le_abs_self _
              _ ≤ |C2| * r := by gcongr
          · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
      _ = Cx * r := by ring
  have hXn : ‖X‖ ≤ Kx := by
    calc ‖X‖ ≤ ‖X - J‖ + ‖J‖ := norm_le_norm_sub_add _ _
      _ ≤ Cx * 1 + ‖J‖ := by gcongr; exact hXJ.trans (by gcongr)
      _ = Kx := by ring
  have hBB : ‖B - r ^ 2 • chartB x‖ ≤ |C3| * r ^ 3 := by
    rw [← l6c_BF_zero]; exact hB.trans (by gcongr; exact le_abs_self _)
  have hL : ‖L‖ ≤ CR * r ^ 3 := by
    have h4 : r ^ 4 ≤ r ^ 3 := by
      calc r ^ 4 = r ^ 3 * r := by ring
        _ ≤ r ^ 3 * 1 := by gcongr
        _ = r ^ 3 := mul_one _
    calc ‖L‖ ≤ ‖L - chartCF x r 0‖ + ‖chartCF x r 0‖ := norm_le_norm_sub_add _ _
      _ ≤ |C4| * r ^ 3 + r ^ 3 * ‖chartC x‖ := by
          refine add_le_add (hC.trans ?_) ?_
          · calc C4 * r ^ 4 ≤ |C4| * r ^ 4 := by gcongr; exact le_abs_self _
              _ ≤ |C4| * r ^ 3 := by gcongr
          · rw [l6c_CF_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      _ = CR * r ^ 3 := by ring
  have hPP : ‖P - chartP0‖ ≤ |Cp| * r := hP.trans (by gcongr; exact le_abs_self _)
  have hPn : ‖P‖ ≤ Kp := by
    calc ‖P‖ ≤ ‖P - chartP0‖ + ‖chartP0‖ := norm_le_norm_sub_add _ _
      _ ≤ |Cp| * 1 + ‖chartP0‖ := by gcongr; exact hPP.trans (by gcongr)
      _ = Kp := by ring
  have hZs : 2 * ‖Z‖ * ‖X - J‖ ≤ 1 / 3 := by
    have h6 : 6 * (‖Z‖ * Cx * r) + r ≤ 1 := by
      linarith [show r * (6 * ‖Z‖ * Cx + 1) = 6 * (‖Z‖ * Cx * r) + r by ring]
    calc 2 * ‖Z‖ * ‖X - J‖ ≤ 2 * ‖Z‖ * (Cx * r) := by gcongr
      _ = 2 * (‖Z‖ * Cx * r) := by ring
      _ ≤ 1 / 3 := by linarith
  have hQ : ‖controlP (vertex 2) X - controlP (vertex 2) J‖ ≤ 9 * ‖Z‖ ^ 2 * Cx * r :=
    (norm_controlP_sub_le 2 hZs).trans (by
      calc 9 * ‖Z‖ ^ 2 * ‖X - J‖ ≤ 9 * ‖Z‖ ^ 2 * (Cx * r) := by gcongr
        _ = 9 * ‖Z‖ ^ 2 * Cx * r := by ring)
  have hg0 : traceForm Z X < -(1 / 3) := by
    rw [show traceForm Z X = traceForm X Z from Matrix.trace_mul_comm _ _]; exact hg
  -- the decomposition of the derivative
  set Q := controlP (vertex 2) X
  set Q' := (-traceForm Z (matLie P X) / traceForm Z X ^ 2) • Z
  set E1 := matLie P L - traceForm L P • matLie P X - matLie (B - r ^ 2 • chartB x) X -
    r ^ 2 • matLie (chartB x) (X - J)
  set E2 := (Q - controlP (vertex 2) J) - (P - chartP0)
  have hD : chi23Deriv q = r ^ 2 * T0 + r ^ 2 * traceForm W E2 + traceForm E1 (Q - P) +
      traceForm L Q' := by
    have hP0 : chartP0 = controlP (vertex 1) J := (l6c_controlP_J 1).symm
    have eR : matLie P L - traceForm L P • matLie P X - matLie B X = r ^ 2 • W + E1 := by
      simp only [E1, W, matLie, smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul, smul_sub]
      module
    have eQ : Q - P = (controlP (vertex 2) J - controlP (vertex 1) J) + E2 := by
      simp only [E2, hP0]; abel
    have hW := l6c_traceForm_W x
    simp only [chi23Deriv]
    rw [eR, eQ, l6c_traceForm_add_left]
    have hsm : ∀ (c : ℝ) (A B : Mat2), traceForm (c • A) B = c * traceForm A B := fun c A B ↦ by
      simp [traceForm, Matrix.trace_smul]
    have hadd : ∀ A B C : Mat2, traceForm A (B + C) = traceForm A B + traceForm A C :=
      fun A B C ↦ by simp [traceForm, Matrix.mul_add, Matrix.trace_add]
    rw [hsm, hadd, hadd, hW]
    ring
  -- the error bounds
  have hE1 : ‖E1‖ ≤ e1 * r ^ 3 := by
    have h1 : ‖matLie P L‖ ≤ 2 * ‖P‖ * ‖L‖ := l6c_norm_br P L
    have h2 : ‖traceForm L P • matLie P X‖ ≤ 2 * (CR * r ^ 3) * Kp * (2 * Kp * Kx) := by
      rw [norm_smul, Real.norm_eq_abs]
      have ha := abs_traceForm_le_opNorm L P
      have hb : ‖matLie P X‖ ≤ 2 * ‖P‖ * ‖X‖ := l6c_norm_br P X
      calc |traceForm L P| * ‖matLie P X‖ ≤ (2 * ‖L‖ * ‖P‖) * (2 * ‖P‖ * ‖X‖) := by gcongr
        _ ≤ 2 * (CR * r ^ 3) * Kp * (2 * Kp * Kx) := by gcongr
    have h3 : ‖matLie (B - r ^ 2 • chartB x) X‖ ≤ 2 * ‖B - r ^ 2 • chartB x‖ * ‖X‖ :=
      l6c_norm_br (B - r ^ 2 • chartB x) X
    have h4 : ‖r ^ 2 • matLie (chartB x) (X - J)‖ ≤ r ^ 2 * (2 * ‖chartB x‖ * (Cx * r)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have : ‖matLie (chartB x) (X - J)‖ ≤ 2 * ‖chartB x‖ * ‖X - J‖ :=
        l6c_norm_br (chartB x) (X - J)
      gcongr
      exact this.trans (by gcongr)
    calc ‖E1‖ ≤ ‖matLie P L‖ + ‖traceForm L P • matLie P X‖ +
          ‖matLie (B - r ^ 2 • chartB x) X‖ + ‖r ^ 2 • matLie (chartB x) (X - J)‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
          exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ 2 * Kp * (CR * r ^ 3) + 2 * (CR * r ^ 3) * Kp * (2 * Kp * Kx) +
          2 * (|C3| * r ^ 3) * Kx + r ^ 2 * (2 * ‖chartB x‖ * (Cx * r)) := by
          refine add_le_add (add_le_add (add_le_add (h1.trans ?_) h2) (h3.trans ?_)) h4
          · gcongr
          · gcongr
      _ = e1 * r ^ 3 := by simp only [e1]; ring
  have hE2 : ‖E2‖ ≤ e2 * r := by
    calc ‖E2‖ ≤ ‖Q - controlP (vertex 2) J‖ + ‖P - chartP0‖ := norm_sub_le _ _
      _ ≤ 9 * ‖Z‖ ^ 2 * Cx * r + |Cp| * r := add_le_add hQ hPP
      _ = e2 * r := by simp only [e2]; ring
  have hQP : ‖Q - P‖ ≤ e3 := by
    have e : Q - P = (controlP (vertex 2) J - chartP0) + E2 := by simp only [E2]; abel
    rw [e]
    have he2 : e2 * r ≤ e2 := mul_le_of_le_one_right (by positivity) hr1
    calc _ ≤ ‖controlP (vertex 2) J - chartP0‖ + ‖E2‖ := norm_add_le _ _
      _ ≤ (‖controlP (vertex 2) J‖ + ‖chartP0‖) + e2 := add_le_add (norm_sub_le _ _)
          (hE2.trans he2)
      _ = e3 := by simp only [e3]
  have hQ' : ‖Q'‖ ≤ e4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_pow]
    have hg1 : 1 / 3 ≤ |traceForm Z X| := by rw [abs_of_neg (by linarith)]; linarith
    have hgn : |traceForm Z (matLie P X)| ≤ 2 * ‖Z‖ * (2 * Kp * Kx) := by
      have ha := abs_traceForm_le_opNorm Z (matLie P X)
      have hb : ‖matLie P X‖ ≤ 2 * ‖P‖ * ‖X‖ := l6c_norm_br P X
      exact ha.trans (by gcongr; exact hb.trans (by gcongr))
    have hsq : 1 / 9 ≤ |traceForm Z X| ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) hg1 2
      norm_num at this ⊢
      linarith
    calc |traceForm Z (matLie P X)| / |traceForm Z X| ^ 2 * ‖Z‖ ≤
        (2 * ‖Z‖ * (2 * Kp * Kx)) / (1 / 9) * ‖Z‖ := by gcongr
      _ = e4 := by simp only [e4]; ring
  have hA := abs_traceForm_le_opNorm W E2
  have hB := abs_traceForm_le_opNorm E1 (Q - P)
  have hC' := abs_traceForm_le_opNorm L Q'
  have hbound : r ^ 2 * |traceForm W E2| + |traceForm E1 (Q - P)| + |traceForm L Q'| ≤
      K * r ^ 3 := by
    calc r ^ 2 * |traceForm W E2| + |traceForm E1 (Q - P)| + |traceForm L Q'| ≤
        r ^ 2 * (2 * ‖W‖ * (e2 * r)) + 2 * (e1 * r ^ 3) * e3 + 2 * (CR * r ^ 3) * e4 := by
          refine add_le_add (add_le_add ?_ (hB.trans ?_)) (hC'.trans ?_)
          · gcongr; exact hA.trans (by gcongr)
          · gcongr
          · gcongr
      _ = K * r ^ 3 := by simp only [K]; ring
  rw [hD]
  have h1 := neg_abs_le (traceForm W E2)
  have h2 := neg_abs_le (traceForm E1 (Q - P))
  have h3 := neg_abs_le (traceForm L Q')
  have hr2' : 0 ≤ r ^ 2 := by positivity
  have h4 : -(r ^ 2 * |traceForm W E2|) ≤ r ^ 2 * traceForm W E2 := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left h1 hr2'
  have h5 : r ^ 2 * (K * r + r) ≤ r ^ 2 * T0 :=
    mul_le_mul_of_nonneg_left (by linarith [show r * (K + 1) = K * r + r by ring]) hr2'
  have h5' : r ^ 2 * (K * r + r) = K * r ^ 3 + r ^ 3 := by ring
  have h6 : 0 < r ^ 3 := by positivity
  linarith

/-! ### The maximum over the control simplex -/

theorem hamiltonian_le_of_vertices (lam : ℝ) (Λ₁ ΛR X : Mat2)
    (hd : ∀ m : Fin 3, traceForm X (controlMatrix (vertex m)) < 0) (c : ℝ)
    (hv : ∀ m : Fin 3, hamiltonian lam Λ₁ ΛR X (vertex m) ≤ c) :
    ∀ v ∈ controlSimplex, hamiltonian lam Λ₁ ΛR X v ≤ c := by
  intro v hv'
  have hlin : ∀ M : Mat2, traceForm M (controlMatrix v) =
      v 0 * traceForm M (controlMatrix (vertex 0)) + v 1 * traceForm M (controlMatrix (vertex 1)) +
        v 2 * traceForm M (controlMatrix (vertex 2)) := fun M ↦ by
    rw [poly_controlMatrix_eq v]
    simp only [poly_traceForm_add_right, poly_traceForm_smul_right]
  have hD : traceForm X (controlMatrix v) < 0 := by
    rw [hlin]
    obtain ⟨⟨h0, -⟩, ⟨h1, -⟩, ⟨h2, -⟩⟩ := hv'.1 0, hv'.1 1, hv'.1 2
    have hs := hv'.2
    have a0 := mul_le_mul_of_nonneg_left (le_max_left (traceForm X (controlMatrix (vertex 0)))
      (max (traceForm X (controlMatrix (vertex 1))) (traceForm X (controlMatrix (vertex 2))))) h0
    have a1 := mul_le_mul_of_nonneg_left ((le_max_left (traceForm X (controlMatrix (vertex 1)))
      (traceForm X (controlMatrix (vertex 2)))).trans (le_max_right
        (traceForm X (controlMatrix (vertex 0))) _)) h1
    have a2 := mul_le_mul_of_nonneg_left ((le_max_right (traceForm X (controlMatrix (vertex 1)))
      (traceForm X (controlMatrix (vertex 2)))).trans (le_max_right
        (traceForm X (controlMatrix (vertex 0))) _)) h2
    have hμ : max (traceForm X (controlMatrix (vertex 0)))
        (max (traceForm X (controlMatrix (vertex 1)))
          (traceForm X (controlMatrix (vertex 2)))) < 0 :=
      max_lt (hd 0) (max_lt (hd 1) (hd 2))
    nlinarith
  set A0 := traceForm (Λ₁ - (3 / 2 * lam) • J) X
  have ha : ∀ m, traceForm ΛR (controlMatrix (vertex m)) ≤
      (A0 - c) * traceForm X (controlMatrix (vertex m)) := by
    intro m
    have := hv m
    unfold hamiltonian at this
    have h' : A0 - c ≤ traceForm ΛR (controlMatrix (vertex m)) /
        traceForm X (controlMatrix (vertex m)) := by linarith
    exact (le_div_iff_of_neg (hd m)).1 h'
  unfold hamiltonian
  have hle : A0 - c ≤ traceForm ΛR (controlMatrix v) / traceForm X (controlMatrix v) := by
    rw [le_div_iff_of_neg hD, hlin, hlin]
    have h0 := mul_le_mul_of_nonneg_left (ha 0) (hv'.1 0).1
    have h1 := mul_le_mul_of_nonneg_left (ha 1) (hv'.1 1).1
    have h2 := mul_le_mul_of_nonneg_left (ha 2) (hv'.1 2).1
    nlinarith
  linarith

/-- The trace form is continuous. -/
private theorem l6c_continuous_traceForm : Continuous (fun p : Mat2 × Mat2 ↦ traceForm p.1 p.2) :=
  (continuous_fst.matrix_mul continuous_snd).matrix_trace

/-- Continuity of a switching function along continuous curves, where the denominators
`⟨Z_{e_k}, X⟩` do not vanish. -/
theorem continuousAt_switchingFn {L X : ℝ → Mat2} (hL : Continuous L) (hX : Continuous X)
    (i j : Fin 3) {t₀ : ℝ} (hi : traceForm (controlMatrix (vertex i)) (X t₀) ≠ 0)
    (hj : traceForm (controlMatrix (vertex j)) (X t₀) ≠ 0) :
    ContinuousAt (fun t ↦ switchingFn i j (L t) (X t)) t₀ := by
  have hc : ∀ k : Fin 3, Continuous (fun t ↦ traceForm (controlMatrix (vertex k)) (X t)) :=
    fun k ↦ (continuous_const.matrix_mul hX).matrix_trace
  have hP : ∀ k : Fin 3, traceForm (controlMatrix (vertex k)) (X t₀) ≠ 0 →
      ContinuousAt (fun t ↦ controlP (vertex k) (X t)) t₀ := fun k hk ↦
    ((hc k).continuousAt.inv₀ hk).smul continuousAt_const
  exact l6c_continuous_traceForm.continuousAt.comp (f := fun t ↦ (L t, (controlP (vertex j) (X t) -
    controlP (vertex i) (X t)))) (hL.continuousAt.prodMk ((hP j hj).sub (hP i hi)))

/-! ### The representative of `q_out` -/

/-- The real coordinates of the representative (13.5.1) of `q_out` that enter `x̃_out`. -/
theorem qOutCart_coords :
    (qOutCart 0).re = -1 ∧ (qOutCart 0).im = (-1 + rScale) / (√3 * (1 + rScale)) ∧
    (qOutCart 1).re = -((-1 + rScale ^ 3) / (√3 * (1 + rScale ^ 3))) ∧
    (qOutCart 1).im = (1 - 3 * rScale - 2 * rScale ^ 2 - 3 * rScale ^ 3 + rScale ^ 4) /
      (3 * (1 + rScale + rScale ^ 3 + rScale ^ 4)) := by
  simp only [qOutCart, equilExact, Matrix.cons_val_zero, Matrix.cons_val_one, 
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.one_re,
    Complex.one_im]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- An enclosure of `√3`. -/
theorem sqrt_three_fine_bounds : 1.7320508075 < √3 ∧ √3 < 1.7320508076 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `H_F(q_out, ζ) = H_F(q_out, ζ²) = 0 > H_F(q_out, 1)` (from `H_F⁺(q_out) = 0` and `z₃ < 0`). -/
theorem ham_qOutCart : ham qOutCart ζ = 0 ∧ ham qOutCart (ζ ^ 2) = 0 ∧
    ham qOutCart 1 < 0 := by
  obtain ⟨-, hq2, hq2'⟩ := qOutCart_normalization
  have hm := hamMax_qOutCart
  have e1 : ham qOutCart (ζ ^ 2) = ham qOutCart ζ := by
    simp only [ham, RR_eq_re_mul_add_im_mul, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, hq2]; ring
  have e2 : ham qOutCart 1 = ham qOutCart ζ + 3 / 2 * (qOutCart 2).re := by
    simp only [ham, RR_eq_re_mul_add_im_mul, ζ_re, ζ_im, hq2, Complex.one_re, Complex.one_im]
    ring
  have hlt : ham qOutCart 1 < ham qOutCart ζ := by rw [e2]; linarith
  rw [hamMax, e1, max_self, max_eq_right hlt.le] at hm
  exact ⟨hm, e1.trans hm, hm ▸ hlt⟩

end SmoothedPolygons
