module

public import SmoothedPolygons.Ch8.EdgeProblem
public import SmoothedPolygons.AppA.Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The switching function of the edge problem at a double zero (Lemma 8.1.5)

Lemma 8.1.5 (`lem:lambda2-Landau`, TeX 6908–7015): at a zero of the switching function `λ₂` of the
edge problem where also `λ₂' = 0` (normalized as in (8.1.8)), `λ₂(t) = C tⁿ + O(tⁿ⁺¹)` with
`C ≠ 0` and `n ∈ {2, 3}`, whatever the control; so that zero is isolated. Used by Theorem 8.1.4.

Notes on the statement:
* The book's Landau notation is two-sided (TeX 6903–6907): `f₁ = O(f₂)` on some `(-t₁, t₁)`, i.e.
  `Asymptotics.IsBigO` at `𝓝 0`. The proof applies Corollary A.1.3 on both sides of `0`
  (gap G14; `l3st_corollaryA_1_3_two_sided`).
* The constant `C` printed for `x₀ ≠ 0`, `-x₀(1 + y₀)/y₀²` (TeX 6934, 6973), is wrong: the
  computation gives `C = -2x₀/y₀` (gap G5; the intermediate line TeX 6970 already gives
  `(x² - x₀²)/y² = 2x₀t/y₀ + O(t²)`). The statement only claims `C ≠ 0`, which holds with the
  correct value.

The proof follows the book's steps: the Taylor expansions of the comparison functions
(`l3c_taylor`, with the two-sided Landau calculus `l3c_O_mul`, `l3c_O_integral`), the bounds of
the coefficients where the denominator of `f₂` stays away from `0` (`l3c_coef_bounds`), and the
Gronwall step for the error `v` (`l3c_gronwall`, through Corollary A.1.3 in its two-sided form
`l3st_corollaryA_1_3_two_sided`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Asymptotics
open scoped Interval

/-! ### Landau notation at `0` with powers of `t` -/

/-- `O(sⁱ) · O(sʲ) = O(sᵏ)`, `k = i + j`. -/
private lemma l3c_O_mul {f g : ℝ → ℝ} {i j k : ℕ} (hf : f =O[𝓝 0] fun s ↦ s ^ i)
    (hg : g =O[𝓝 0] fun s ↦ s ^ j) (hk : i + j = k) :
    (fun s ↦ f s * g s) =O[𝓝 0] fun s ↦ s ^ k := by
  subst hk
  exact (hf.mul hg).congr_right fun s ↦ (pow_add s i j).symm

/-- `O(sʲ) ⊆ O(sⁱ)` near `0` when `i ≤ j`. -/
private lemma l3c_O_mono {f : ℝ → ℝ} {i j : ℕ} (hf : f =O[𝓝 0] fun s ↦ s ^ j) (hij : i ≤ j) :
    f =O[𝓝 0] fun s ↦ s ^ i := by
  rcases hij.eq_or_lt with rfl | h
  · exact hf
  · exact hf.trans (isLittleO_pow_pow h).isBigO

private lemma l3c_O_id : (fun s : ℝ ↦ s) =O[𝓝 0] fun s ↦ s ^ 1 := by
  simpa using isBigO_refl (fun s : ℝ ↦ s) (𝓝 0)

/-- A function with a limit at `0` is `O(1) = O(s⁰)`. -/
private lemma l3c_O_zero_of_tendsto {f : ℝ → ℝ} {c : ℝ} (h : Tendsto f (𝓝 0) (𝓝 c)) :
    f =O[𝓝 0] fun s ↦ s ^ 0 := by
  simpa using h.isBigO_one ℝ

/-- For `s` between `0` and `t`, `|s| ≤ |t|`. -/
private lemma l3c_abs_le_of_mem_uIoc {s t : ℝ} (hs : s ∈ Ι (0 : ℝ) t) : |s| ≤ |t| := by
  rcases le_total 0 t with h0 | h0
  · rw [uIoc_of_le h0] at hs
    rw [abs_of_pos hs.1, abs_of_nonneg h0]
    exact hs.2
  · rw [uIoc_of_ge h0] at hs
    rw [abs_of_nonpos hs.2, abs_of_nonpos h0]
    linarith [hs.1]

/-- **Integration of Landau terms**: if `g = O(sᵏ)` near `0` (two-sided), then
`∫₀ᵗ g = O(tᵏ⁺¹)`. No integrability is needed: `|∫₀ᵗ g| ≤ (sup_{Ι 0 t} |g|) |t|`. -/
private lemma l3c_O_integral {g : ℝ → ℝ} {k : ℕ} (h : g =O[𝓝 0] fun s ↦ s ^ k) :
    (fun t ↦ ∫ s in (0 : ℝ)..t, g s) =O[𝓝 0] fun t ↦ t ^ (k + 1) := by
  obtain ⟨c, hc0, hc⟩ := h.exists_nonneg
  rw [isBigOWith_iff] at hc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hc
  refine IsBigO.of_bound c (Metric.eventually_nhds_iff.2 ⟨ε, hε, fun t ht ↦ ?_⟩)
  have hs : ∀ s ∈ Ι (0 : ℝ) t, ‖g s‖ ≤ c * |t| ^ k := by
    intro s hs
    have hst := l3c_abs_le_of_mem_uIoc hs
    have ht' : |t| < ε := by simpa [Real.dist_eq] using ht
    have := hball (y := s) (by rw [Real.dist_eq, sub_zero]; exact hst.trans_lt ht')
    calc ‖g s‖ ≤ c * ‖s ^ k‖ := this
      _ ≤ c * |t| ^ k := by rw [norm_pow, Real.norm_eq_abs]; gcongr
  calc ‖∫ s in (0 : ℝ)..t, g s‖ ≤ c * |t| ^ k * |t - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hs
    _ = c * ‖t ^ (k + 1)‖ := by rw [sub_zero, norm_pow, Real.norm_eq_abs, pow_succ]; ring

/-! ### The comparison functions -/

/-- The comparison function `λ̃₁(t) = ∫₀ᵗ 2x/y` of the proof of Lemma 8.1.5. -/
private noncomputable def l3c_cmp₁ (x y : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, 2 * x s / y s

/-- The comparison function `λ̃₂(t) = -∫₀ᵗ ((x² - x₀²)/y² + λ̃₁)` of the proof of Lemma 8.1.5. -/
private noncomputable def l3c_cmp₂ (x₀ : ℝ) (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  -∫ s in (0 : ℝ)..t, ((x s ^ 2 - x₀ ^ 2) / y s ^ 2 + l3c_cmp₁ x y s)

/-- **The Taylor expansions of the proof of Lemma 8.1.5** (TeX 6964–6982). On `[-τ, τ]` let
`x = x₀ + ∫₀ᵗ y` with `y` continuous and positive and `|y - y₀| ≤ M|t|` (`y = y₀ + O(t)`, `y'`
being bounded). Then `x = x₀ + y₀t + O(t²)` and
* if `x₀ ≠ 0`: `(x² - x₀²)/y² = 2x₀t/y₀ + O(t²)`, `λ̃₁ = 2x₀t/y₀ + O(t²)`, and
  `λ̃₂ = -2x₀t²/y₀ + O(t³)` (the book's constant `-x₀(1 + y₀)/y₀²` is a slip, gap G5);
* if `x₀ = 0`: `x = y₀t + O(t²)`, `λ̃₁ = t² + O(t³)`, and `λ̃₂ = -2t³/3 + O(t⁴)`. -/
private lemma l3c_taylor {x y : ℝ → ℝ} {x₀ y₀ τ M : ℝ} (hτ : 0 < τ) (hy₀ : 0 < y₀)
    (hxc : ContinuousOn x (Icc (-τ) τ)) (hyc : ContinuousOn y (Icc (-τ) τ))
    (hypos : ∀ s ∈ Icc (-τ) τ, 0 < y s) (hx : ∀ t ∈ Icc (-τ) τ, x t = x₀ + ∫ s in (0 : ℝ)..t, y s)
    (hyM : ∀ t ∈ Icc (-τ) τ, |y t - y₀| ≤ M * |t|) :
    (x₀ ≠ 0 → (fun t ↦ l3c_cmp₂ x₀ x y t - -2 * x₀ / y₀ * t ^ 2) =O[𝓝 0] fun t ↦ t ^ 3) ∧
      (x₀ = 0 → (fun t ↦ l3c_cmp₂ x₀ x y t - -2 / 3 * t ^ 3) =O[𝓝 0] fun t ↦ t ^ 4) := by
  set K := Icc (-τ) τ with hK
  have hKn : K ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith) hτ
  have h0K : (0 : ℝ) ∈ K := ⟨by linarith, hτ.le⟩
  have hsub : ∀ t ∈ K, uIcc 0 t ⊆ K := fun t ht ↦ uIcc_subset_Icc h0K ht
  have hy0 : y 0 = y₀ := by
    have := hyM 0 h0K
    rw [abs_zero, mul_zero] at this
    linarith [abs_nonneg (y 0 - y₀), abs_sub_le_iff.1 (le_antisymm this (abs_nonneg _)).le]
  -- the continuous integrands are interval integrable on `0..t`, `t ∈ K`
  have hq : ContinuousOn (fun s ↦ 2 * x s / y s) K :=
    (continuousOn_const.mul hxc).div hyc fun s hs ↦ (hypos s hs).ne'
  have hq1 : ContinuousOn (l3c_cmp₁ x y) K := by
    have := intervalIntegral.continuousOn_primitive_interval' (μ := volume) (hq.mono (uIcc_of_le
      (by linarith : -τ ≤ τ)).subset).intervalIntegrable
      (by rw [uIcc_of_le (by linarith)]; exact h0K)
    rwa [uIcc_of_le (by linarith)] at this
  have hg : ContinuousOn (fun s ↦ (x s ^ 2 - x₀ ^ 2) / y s ^ 2 + l3c_cmp₁ x y s) K :=
    (((hxc.pow 2).sub continuousOn_const).div (hyc.pow 2)
      fun s hs ↦ pow_ne_zero 2 (hypos s hs).ne').add hq1
  -- `y = y₀ + O(t)`
  have hb : (fun s ↦ y s - y₀) =O[𝓝 0] fun s ↦ s ^ 1 :=
    IsBigO.of_bound M (Filter.mem_of_superset hKn fun s hs ↦ by
      simpa [Real.norm_eq_abs] using hyM s hs)
  -- `x = x₀ + y₀ t + O(t²)`
  have ha : (fun s ↦ x s - x₀ - y₀ * s) =O[𝓝 0] fun s ↦ s ^ 2 := by
    refine (l3c_O_integral hb).congr' (eventuallyEq_of_mem hKn fun t ht ↦ ?_) EventuallyEq.rfl
    rw [intervalIntegral.integral_sub ((hyc.mono (hsub t ht)).intervalIntegrable)
      (intervalIntegrable_const (μ := volume)), intervalIntegral.integral_const, smul_eq_mul,
      hx t ht]
    ring
  have hd : (fun s ↦ x s - x₀) =O[𝓝 0] fun s ↦ s ^ 1 :=
    ((l3c_O_mono ha (by norm_num)).add (l3c_O_id.const_mul_left y₀)).congr_left fun s ↦ by ring
  have hyinv : (fun s ↦ (y s)⁻¹) =O[𝓝 0] fun s ↦ s ^ 0 := by
    have hyc0 : ContinuousAt y 0 := hyc.continuousAt hKn
    exact l3c_O_zero_of_tendsto ((hyc0.tendsto.inv₀ (by rw [hy0]; exact hy₀.ne')))
  have hyK : ∀ s ∈ K, y s ≠ 0 := fun s hs ↦ (hypos s hs).ne'
  -- splitting `λ̃₁(t) - ∫₀ᵗ p = ∫₀ᵗ (2x/y - p)` and `λ̃₂(t) + ∫₀ᵗ p = -∫₀ᵗ (g - p)`
  have hsplit₁ : ∀ (p : ℝ → ℝ), Continuous p → ∀ t ∈ K,
      ∫ s in (0 : ℝ)..t, (2 * x s / y s - p s) = l3c_cmp₁ x y t - ∫ s in (0 : ℝ)..t, p s :=
    fun p hp t ht ↦ intervalIntegral.integral_sub ((hq.mono (hsub t ht)).intervalIntegrable)
      (hp.intervalIntegrable _ _)
  have hsplit₂ : ∀ (p : ℝ → ℝ), Continuous p → ∀ t ∈ K,
      -∫ s in (0 : ℝ)..t, ((x s ^ 2 - x₀ ^ 2) / y s ^ 2 + l3c_cmp₁ x y s - p s) =
        l3c_cmp₂ x₀ x y t + ∫ s in (0 : ℝ)..t, p s := by
    intro p hp t ht
    rw [intervalIntegral.integral_sub ((hg.mono (hsub t ht)).intervalIntegrable)
      (hp.intervalIntegrable _ _), l3c_cmp₂]
    ring
  constructor
  · intro hx₀
    -- `2x/y = 2x₀/y₀ + O(t)`, so `λ̃₁ = 2x₀t/y₀ + O(t²)`
    have h1 : (fun s ↦ 2 * x s / y s - 2 * x₀ / y₀) =O[𝓝 0] fun s ↦ s ^ 1 := by
      refine (l3c_O_mul (hyinv.const_mul_left (2 / y₀))
        ((hd.const_mul_left y₀).sub (hb.const_mul_left x₀)) (by norm_num)).congr'
        (eventuallyEq_of_mem hKn fun s hs ↦ ?_) EventuallyEq.rfl
      have := hyK s hs
      field_simp
      ring
    have h1' : (fun t ↦ l3c_cmp₁ x y t - 2 * x₀ / y₀ * t) =O[𝓝 0] fun t ↦ t ^ 2 := by
      refine (l3c_O_integral h1).congr' (eventuallyEq_of_mem hKn fun t ht ↦ ?_)
        EventuallyEq.rfl
      rw [hsplit₁ (fun _ ↦ 2 * x₀ / y₀) continuous_const t ht, intervalIntegral.integral_const,
        smul_eq_mul]
      ring
    -- `(x² - x₀²)/y² = 2x₀t/y₀ + O(t²)`
    have h2 : (fun s ↦ (x s ^ 2 - x₀ ^ 2) / y s ^ 2 - 2 * x₀ / y₀ * s) =O[𝓝 0]
        fun s ↦ s ^ 2 := by
      have hN : (fun s ↦ 2 * x₀ * y₀ * (x s - x₀ - y₀ * s) + y₀ * ((x s - x₀) * (x s - x₀)) -
          4 * x₀ * y₀ * (s * (y s - y₀)) - 2 * x₀ * (s * (y s - y₀) * (y s - y₀))) =O[𝓝 0]
          fun s ↦ s ^ 2 :=
        (((ha.const_mul_left _).add ((l3c_O_mul hd hd rfl).const_mul_left _)).sub
          ((l3c_O_mul l3c_O_id hb rfl).const_mul_left _)).sub
          ((l3c_O_mono (l3c_O_mul (l3c_O_mul l3c_O_id hb rfl) hb rfl) (by norm_num)).const_mul_left
            _)
      refine (l3c_O_mul ((l3c_O_mul hyinv hyinv rfl).const_mul_left y₀⁻¹) hN rfl).congr'
        (eventuallyEq_of_mem hKn fun s hs ↦ ?_) EventuallyEq.rfl
      have := hyK s hs
      field_simp
      ring
    -- the integrand of `λ̃₂` is `4x₀t/y₀ + O(t²)`, so `λ̃₂ = -2x₀t²/y₀ + O(t³)`
    have h3 : (fun s ↦ (x s ^ 2 - x₀ ^ 2) / y s ^ 2 + l3c_cmp₁ x y s - 4 * x₀ / y₀ * s) =O[𝓝 0]
        fun s ↦ s ^ 2 := (h2.add h1').congr_left fun s ↦ by ring
    refine (l3c_O_integral h3).neg_left.congr' (eventuallyEq_of_mem hKn fun t ht ↦ ?_)
      EventuallyEq.rfl
    rw [hsplit₂ (fun s ↦ 4 * x₀ / y₀ * s) (continuous_const.mul continuous_id) t ht,
      intervalIntegral.integral_const_mul, integral_id]
    ring
  · intro hx₀
    subst hx₀
    -- `2x/y = 2t + O(t²)`, so `λ̃₁ = t² + O(t³)`
    have h1 : (fun s ↦ 2 * x s / y s - 2 * s) =O[𝓝 0] fun s ↦ s ^ 2 := by
      refine (l3c_O_mul (hyinv.const_mul_left 2) (ha.sub (l3c_O_mul l3c_O_id hb rfl)) rfl).congr'
        (eventuallyEq_of_mem hKn fun s hs ↦ ?_) EventuallyEq.rfl
      have := hyK s hs
      field_simp
      ring
    have h1' : (fun t ↦ l3c_cmp₁ x y t - t ^ 2) =O[𝓝 0] fun t ↦ t ^ 3 := by
      refine (l3c_O_integral h1).congr' (eventuallyEq_of_mem hKn fun t ht ↦ ?_)
        EventuallyEq.rfl
      rw [hsplit₁ (fun s ↦ 2 * s) (continuous_const.mul continuous_id) t ht,
        intervalIntegral.integral_const_mul, integral_id]
      ring
    -- `x²/y² = t² + O(t³)`
    have h2 : (fun s ↦ (x s ^ 2 - 0 ^ 2) / y s ^ 2 - s ^ 2) =O[𝓝 0] fun s ↦ s ^ 3 := by
      have hp : (fun s ↦ x s + s * y s) =O[𝓝 0] fun s ↦ s ^ 1 :=
        ((hd.add (l3c_O_id.const_mul_left y₀)).add (l3c_O_mono (l3c_O_mul l3c_O_id hb rfl)
          (by norm_num))).congr_left fun s ↦ by ring
      have hm : (fun s ↦ x s - s * y s) =O[𝓝 0] fun s ↦ s ^ 2 :=
        (ha.sub (l3c_O_mul l3c_O_id hb rfl)).congr_left fun s ↦ by ring
      refine (l3c_O_mul (l3c_O_mul hyinv hyinv rfl) (l3c_O_mul hm hp rfl) rfl).congr'
        (eventuallyEq_of_mem hKn fun s hs ↦ ?_) EventuallyEq.rfl
      have := hyK s hs
      field_simp
      ring
    -- the integrand of `λ̃₂` is `2t² + O(t³)`, so `λ̃₂ = -2t³/3 + O(t⁴)`
    have h3 : (fun s ↦ (x s ^ 2 - 0 ^ 2) / y s ^ 2 + l3c_cmp₁ x y s - 2 * s ^ 2) =O[𝓝 0]
        fun s ↦ s ^ 3 := (h2.add h1').congr_left fun s ↦ by ring
    refine (l3c_O_integral h3).neg_left.congr' (eventuallyEq_of_mem hKn fun t ht ↦ ?_)
      EventuallyEq.rfl
    rw [hsplit₂ (fun s ↦ 2 * s ^ 2) (continuous_const.mul (continuous_pow 2)) t ht,
      intervalIntegral.integral_const_mul, integral_pow]
    ring

/-! ### The coefficients of the costate equations and the Gronwall step -/

/-- `-f₂ₓ = 12 y² u_e²/(1 - 2√3 x u_e)²`, the coefficient of `λ₂` in `λ₁'` (8.1.7). -/
private noncomputable def l3c_fx (x y u : ℝ) : ℝ := 12 * y ^ 2 * u ^ 2 / (1 - 2 * √3 * x * u) ^ 2

/-- `f₂ᵧ = 4√3 y u_e/(-1 + 2√3 x u_e)`, the coefficient of `-λ₂` in `λ₂'` (8.1.7). -/
private noncomputable def l3c_fy (x y u : ℝ) : ℝ := 4 * √3 * y * u / (-1 + 2 * √3 * x * u)

/-- **The coefficients are bounded** where the denominator `-1 + 2√3 x u_e` of `f₂` stays away
from `0` (TeX 6996–6998): if `|u| ≤ ½`, `0 < y ≤ Y` and `√3|x| ≤ 1 - δ` with `δ > 0`, then
`|-1 + 2√3 x u| ≥ δ`, `|f₂| ≤ √3 Y²/δ`, `|f₂ₓ| ≤ 3Y²/δ²` and `|f₂ᵧ| ≤ 2√3 Y/δ`. -/
private lemma l3c_coef_bounds {x y u Y δ : ℝ} (hu : |u| ≤ 1 / 2) (hy : 0 < y) (hyY : y ≤ Y)
    (hδ : 0 < δ) (hx : √3 * |x| ≤ 1 - δ) :
    |edgeF₂ x y u| ≤ √3 * Y ^ 2 / δ ∧ |l3c_fx x y u| ≤ 3 * Y ^ 2 / δ ^ 2 ∧
      |l3c_fy x y u| ≤ 2 * √3 * Y / δ := by
  have h3 : 0 < √3 := by positivity
  have hxu : |2 * √3 * x * u| ≤ 1 - δ := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2), abs_of_pos h3]
    have := mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 2 * √3 * |x|)
    linarith
  have hD : δ ≤ |-1 + 2 * √3 * x * u| := by
    rw [abs_le] at hxu
    rw [abs_of_neg (by linarith)]
    linarith
  have hY : 0 ≤ Y := hy.le.trans hyY
  have hy2 : y ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hy.le hyY 2
  have hu2 : u ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg u]
  refine ⟨?_, ?_, ?_⟩
  · rw [edgeF₂, abs_div]
    refine div_le_div₀ (by positivity) ?_ hδ hD
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2), abs_of_pos h3,
      abs_of_nonneg (sq_nonneg y)]
    have := mul_le_mul_of_nonneg_left (mul_le_mul hy2 hu (abs_nonneg u) (sq_nonneg Y))
      (by positivity : (0 : ℝ) ≤ 2 * √3)
    linarith
  · rw [l3c_fx, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 12 * y ^ 2 * u ^ 2),
      abs_of_nonneg (sq_nonneg _), show (1 - 2 * √3 * x * u) ^ 2 = |-1 + 2 * √3 * x * u| ^ 2 by
      rw [sq_abs]; ring]
    refine div_le_div₀ (by positivity) ?_ (by positivity) (pow_le_pow_left₀ hδ.le hD 2)
    have := mul_le_mul hy2 hu2 (sq_nonneg u) (sq_nonneg Y)
    linarith
  · rw [l3c_fy, abs_div]
    refine div_le_div₀ (by positivity) ?_ hδ hD
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos h3,
      abs_of_pos hy]
    have := mul_le_mul_of_nonneg_left (mul_le_mul hyY hu (abs_nonneg u) hY)
      (by positivity : (0 : ℝ) ≤ 4 * √3)
    linarith

/-- The integral estimate behind `‖v‖ ≤ C₁|t|ⁿ⁺¹/(n + 1) + C₀|∫₀ᵗ ‖v‖|` (TeX 7000–7006): if
`|f| ≤ c w + d` between `0` and `t` with `w ≥ 0` integrable, then
`|∫₀ᵗ f| ≤ c |∫₀ᵗ w| + d |t|`. -/
private lemma l3c_abs_integral_le {f w : ℝ → ℝ} {t c d : ℝ}
    (hw : IntervalIntegrable w volume 0 t) (hw0 : ∀ s, 0 ≤ w s)
    (h : ∀ s ∈ Ι (0 : ℝ) t, |f s| ≤ c * w s + d) :
    |∫ s in (0 : ℝ)..t, f s| ≤ c * |∫ s in (0 : ℝ)..t, w s| + d * |t| := by
  have hg : IntervalIntegrable (fun s ↦ c * w s + d) volume 0 t :=
    (hw.const_mul c).add intervalIntegrable_const
  rcases le_total 0 t with h0 | h0
  · have h1 := intervalIntegral.norm_integral_le_of_norm_le (f := f) h0
      (ae_of_all _ fun s hs ↦ by rw [Real.norm_eq_abs]; exact h s (by rwa [uIoc_of_le h0])) hg
    rw [intervalIntegral.integral_add (hw.const_mul c) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
      sub_zero] at h1
    rw [abs_of_nonneg (intervalIntegral.integral_nonneg h0 fun s _ ↦ hw0 s), abs_of_nonneg h0]
    simpa [Real.norm_eq_abs, mul_comm] using h1
  · have h1 := intervalIntegral.norm_integral_le_of_norm_le (f := f) h0
      (ae_of_all _ fun s hs ↦ by rw [Real.norm_eq_abs]; exact h s (by rwa [uIoc_of_ge h0]))
      hg.symm
    rw [intervalIntegral.integral_add (hw.symm.const_mul c) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at h1
    rw [intervalIntegral.integral_symm t 0, abs_neg, intervalIntegral.integral_symm t 0, abs_neg,
      abs_of_nonneg (intervalIntegral.integral_nonneg h0 fun s _ ↦ hw0 s), abs_of_nonpos h0]
    simpa [Real.norm_eq_abs, mul_comm] using h1

/-- **The Gronwall step of Lemma 8.1.5** (TeX 6942–7015). On `[-τ, τ]` let `λ₁, λ₂` solve the
costate equations (8.1.7) with `λ_cost = -1`, `λ₃ = x₀²` and `λ₁(0) = λ₂(0) = 0`, with bounded
measurable coefficients `|f₂ₓ| ≤ A`, `|f₂ᵧ| ≤ B`. If `λ̃₂ = C tⁿ + O(tⁿ⁺¹)`, then
`λ₂ = C tⁿ + O(tⁿ⁺¹)`: the error `v = (λ₁ - λ̃₁, λ₂ - λ̃₂)` solves `v₁' = -f₂ₓ λ₂`,
`v₂' = -v₁ - f₂ᵧ λ₂` (that is, `v' = -Av - λ̃₂ b`), so `w = |v₁| + |v₂|` satisfies
`w ≤ (A + B)K|t|ⁿ⁺¹ + (1 + A + B)|∫₀ᵗ w|` near `0` (with `|λ̃₂| ≤ K|t|ⁿ`), and Gronwall's
inequality (Corollary A.1.3, two-sided) gives `w = O(|t|ⁿ⁺¹)`. -/
private lemma l3c_gronwall {x y ue l₁ l₂ : ℝ → ℝ} {x₀ τ A B C : ℝ} {n : ℕ} (hτ : 0 < τ)
    (hxc : ContinuousOn x (Icc (-τ) τ)) (hyc : ContinuousOn y (Icc (-τ) τ))
    (hl1c : ContinuousOn l₁ (Icc (-τ) τ)) (hl2c : ContinuousOn l₂ (Icc (-τ) τ))
    (hypos : ∀ s ∈ Icc (-τ) τ, 0 < y s)
    (ha : ∀ s ∈ Icc (-τ) τ, |l3c_fx (x s) (y s) (ue s)| ≤ A)
    (hb : ∀ s ∈ Icc (-τ) τ, |l3c_fy (x s) (y s) (ue s)| ≤ B)
    (ham : AEStronglyMeasurable (fun s ↦ l3c_fx (x s) (y s) (ue s))
      (volume.restrict (Icc (-τ) τ)))
    (hbm : AEStronglyMeasurable (fun s ↦ l3c_fy (x s) (y s) (ue s))
      (volume.restrict (Icc (-τ) τ)))
    (hl1 : ∀ t ∈ Icc (-τ) τ,
      l₁ t = ∫ s in (0 : ℝ)..t, edgeCostateRHS₁ (-1) (l₂ s) (x s) (y s) (ue s))
    (hl2 : ∀ t ∈ Icc (-τ) τ,
      l₂ t = ∫ s in (0 : ℝ)..t, edgeCostateRHS₂ (-1) (l₁ s) (l₂ s) (x₀ ^ 2) (x s) (y s) (ue s))
    (hcmp : (fun t ↦ l3c_cmp₂ x₀ x y t - C * t ^ n) =O[𝓝 0] fun t ↦ t ^ (n + 1)) :
    (fun t ↦ l₂ t - C * t ^ n) =O[𝓝 0] fun t ↦ t ^ (n + 1) := by
  set K := Icc (-τ) τ with hK
  have h0K : (0 : ℝ) ∈ K := ⟨by linarith, hτ.le⟩
  have hsub : ∀ t ∈ K, uIcc 0 t ⊆ K := fun t ht ↦ uIcc_subset_Icc h0K ht
  have hA : 0 ≤ A := (abs_nonneg _).trans (ha 0 h0K)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb 0 h0K)
  -- continuity of the comparison functions on `K`
  have hq : ContinuousOn (fun s ↦ 2 * x s / y s) K :=
    (continuousOn_const.mul hxc).div hyc fun s hs ↦ (hypos s hs).ne'
  have hKu : uIcc (-τ) τ = K := uIcc_of_le (by linarith)
  have hq1 : ContinuousOn (l3c_cmp₁ x y) K := by
    have := intervalIntegral.continuousOn_primitive_interval' (μ := volume)
      (hq.mono hKu.subset).intervalIntegrable (by rw [hKu]; exact h0K)
    rwa [hKu] at this
  have hg : ContinuousOn (fun s ↦ (x s ^ 2 - x₀ ^ 2) / y s ^ 2 + l3c_cmp₁ x y s) K :=
    (((hxc.pow 2).sub continuousOn_const).div (hyc.pow 2)
      fun s hs ↦ pow_ne_zero 2 (hypos s hs).ne').add hq1
  have hq2 : ContinuousOn (l3c_cmp₂ x₀ x y) K := by
    have := (intervalIntegral.continuousOn_primitive_interval' (μ := volume)
      (hg.mono hKu.subset).intervalIntegrable (by rw [hKu]; exact h0K)).neg
    rw [hKu] at this
    exact this
  -- the products `λ₂ f₂ₓ`, `λ₂ f₂ᵧ` are integrable
  have hbdd : ∀ (F : ℝ → ℝ) (M : ℝ), AEStronglyMeasurable F (volume.restrict K) →
      (∀ s ∈ K, |F s| ≤ M) → ∀ t ∈ K, IntervalIntegrable (fun s ↦ l₂ s * F s) volume 0 t := by
    intro F M hFm hFM t ht
    have hsub' : Ι (0 : ℝ) t ⊆ K := uIoc_subset_uIcc.trans (hsub t ht)
    have : IntervalIntegrable F volume 0 t :=
      (intervalIntegrable_const (μ := volume) (c := M)).mono_fun'
        (hFm.mono_measure (Measure.restrict_mono hsub' le_rfl))
        ((ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun s hs ↦ by
          simpa [Real.norm_eq_abs] using hFM s (hsub' hs)))
    exact this.continuousOn_mul (hl2c.mono (hsub t ht))
  have hia := hbdd _ A ham ha
  have hib := hbdd _ B hbm hb
  -- the error `v = (λ₁ - λ̃₁, λ₂ - λ̃₂)` in integral form
  have hv1 : ∀ t ∈ K, l₁ t - l3c_cmp₁ x y t =
      ∫ s in (0 : ℝ)..t, l₂ s * l3c_fx (x s) (y s) (ue s) := by
    intro t ht
    have hR : (fun s ↦ edgeCostateRHS₁ (-1) (l₂ s) (x s) (y s) (ue s)) =
        fun s ↦ l₂ s * l3c_fx (x s) (y s) (ue s) + 2 * x s / y s := by
      funext s; simp only [edgeCostateRHS₁, l3c_fx]; ring
    rw [hl1 t ht, hR, intervalIntegral.integral_add (hia t ht)
      ((hq.mono (hsub t ht)).intervalIntegrable), l3c_cmp₁]
    ring
  have hv2 : ∀ t ∈ K, l₂ t - l3c_cmp₂ x₀ x y t =
      ∫ s in (0 : ℝ)..t, (-(l₁ s - l3c_cmp₁ x y s) - l₂ s * l3c_fy (x s) (y s) (ue s)) := by
    intro t ht
    have hc : ContinuousOn (fun s ↦ x₀ ^ 2 / y s ^ 2 - l₁ s - x s ^ 2 / y s ^ 2) K :=
      ((continuousOn_const.div (hyc.pow 2) fun s hs ↦ pow_ne_zero 2 (hypos s hs).ne').sub
        hl1c).sub ((hxc.pow 2).div (hyc.pow 2) fun s hs ↦ pow_ne_zero 2 (hypos s hs).ne')
    have hR : (fun s ↦ edgeCostateRHS₂ (-1) (l₁ s) (l₂ s) (x₀ ^ 2) (x s) (y s) (ue s)) =
        fun s ↦ (x₀ ^ 2 / y s ^ 2 - l₁ s - x s ^ 2 / y s ^ 2) -
          l₂ s * l3c_fy (x s) (y s) (ue s) := by
      funext s; simp only [edgeCostateRHS₂, l3c_fy]; ring
    rw [hl2 t ht, l3c_cmp₂, sub_neg_eq_add, ← intervalIntegral.integral_add
      (by rw [hR]; exact ((hc.mono (hsub t ht)).intervalIntegrable).sub (hib t ht))
      ((hg.mono (hsub t ht)).intervalIntegrable)]
    congr 1
    funext s
    simp only [edgeCostateRHS₂, l3c_fy]
    ring
  -- `λ̃₂ = O(tⁿ)`: `|λ̃₂| ≤ K₂|t|ⁿ` on `[-τ', τ']`
  have hc2 : (fun t ↦ l3c_cmp₂ x₀ x y t) =O[𝓝 0] fun t ↦ t ^ n :=
    ((l3c_O_mono hcmp (Nat.le_succ n)).add (isBigO_const_mul_self C (fun t : ℝ ↦ t ^ n) _)
      ).congr_left fun t ↦ by ring
  obtain ⟨K₂, hK₂0, hK₂⟩ := hc2.exists_nonneg
  rw [isBigOWith_iff] at hK₂
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hK₂
  set τ' := min τ (ε / 2) with hτ'
  have hτ'0 : 0 < τ' := lt_min hτ (by positivity)
  set K' := Icc (-τ') τ' with hK'
  have hK'K : K' ⊆ K := Icc_subset_Icc (by simp [τ']) (min_le_left _ _)
  have hlt : ∀ s ∈ K', |l3c_cmp₂ x₀ x y s| ≤ K₂ * |s| ^ n := by
    intro s hs
    have h1 : |s| < ε := (abs_le.2 ⟨hs.1, hs.2⟩).trans_lt
      ((min_le_right _ _).trans_lt (by linarith))
    have := hball (y := s) (by rwa [Real.dist_eq, sub_zero])
    simpa [Real.norm_eq_abs, abs_pow] using this
  -- the Gronwall inequality for `w = |v₁| + |v₂|`
  set w : ℝ → ℝ := fun s ↦ |l₁ s - l3c_cmp₁ x y s| + |l₂ s - l3c_cmp₂ x₀ x y s| with hw
  have hwc : ContinuousOn w K' :=
    (((hl1c.sub hq1).abs).add ((hl2c.sub hq2).abs)).mono hK'K
  have hw0 : ∀ s, 0 ≤ w s := fun s ↦ by positivity
  have h0K' : (0 : ℝ) ∈ K' := ⟨by linarith, hτ'0.le⟩
  have hgron : ∀ t ∈ K',
      w t ≤ (A + B) * K₂ * |t| ^ (n + 1) + (1 + A + B) * |∫ s in (0 : ℝ)..t, w s| := by
    intro t ht
    have hsub' : ∀ s ∈ Ι (0 : ℝ) t, s ∈ K' ∧ |s| ≤ |t| := fun s hs ↦
      ⟨uIcc_subset_Icc h0K' ht (uIoc_subset_uIcc hs), l3c_abs_le_of_mem_uIoc hs⟩
    have hwi : IntervalIntegrable w volume 0 t :=
      (hwc.mono (uIcc_subset_Icc h0K' ht)).intervalIntegrable
    have hl2b : ∀ s ∈ Ι (0 : ℝ) t, |l₂ s| ≤ w s + K₂ * |t| ^ n := by
      intro s hs
      obtain ⟨hsK, hst⟩ := hsub' s hs
      have h1 : |l₂ s| ≤ |l₂ s - l3c_cmp₂ x₀ x y s| + |l3c_cmp₂ x₀ x y s| := by
        simpa using abs_add_le (l₂ s - l3c_cmp₂ x₀ x y s) (l3c_cmp₂ x₀ x y s)
      have h2 := hlt s hsK
      have h3 : K₂ * |s| ^ n ≤ K₂ * |t| ^ n := by gcongr
      simp only [w]
      linarith [abs_nonneg (l₁ s - l3c_cmp₁ x y s)]
    have e1 : |l₁ t - l3c_cmp₁ x y t| ≤
        A * |∫ s in (0 : ℝ)..t, w s| + A * (K₂ * |t| ^ n) * |t| := by
      rw [hv1 t (hK'K ht)]
      refine l3c_abs_integral_le hwi hw0 fun s hs ↦ ?_
      rw [abs_mul]
      have := ha s (hK'K (hsub' s hs).1)
      calc |l₂ s| * |l3c_fx (x s) (y s) (ue s)| ≤ (w s + K₂ * |t| ^ n) * A :=
            mul_le_mul (hl2b s hs) this (abs_nonneg _)
              (by linarith [hw0 s, hl2b s hs, abs_nonneg (l₂ s)])
        _ = A * w s + A * (K₂ * |t| ^ n) := by ring
    have e2 : |l₂ t - l3c_cmp₂ x₀ x y t| ≤
        (1 + B) * |∫ s in (0 : ℝ)..t, w s| + B * (K₂ * |t| ^ n) * |t| := by
      rw [hv2 t (hK'K ht)]
      refine l3c_abs_integral_le (c := 1 + B) hwi hw0 fun s hs ↦ ?_
      have hb' := hb s (hK'K (hsub' s hs).1)
      have h1 : |l₂ s * l3c_fy (x s) (y s) (ue s)| ≤ (w s + K₂ * |t| ^ n) * B := by
        rw [abs_mul]
        exact mul_le_mul (hl2b s hs) hb' (abs_nonneg _)
          (by linarith [hw0 s, hl2b s hs, abs_nonneg (l₂ s)])
      have h2 : |-(l₁ s - l3c_cmp₁ x y s) - l₂ s * l3c_fy (x s) (y s) (ue s)| ≤
          |l₁ s - l3c_cmp₁ x y s| + |l₂ s * l3c_fy (x s) (y s) (ue s)| := by
        have := abs_sub (-(l₁ s - l3c_cmp₁ x y s)) (l₂ s * l3c_fy (x s) (y s) (ue s))
        rwa [abs_neg] at this
      have h3 : |l₁ s - l3c_cmp₁ x y s| ≤ w s := by
        simp only [w]; linarith [abs_nonneg (l₂ s - l3c_cmp₂ x₀ x y s)]
      linarith
    have : w t = |l₁ t - l3c_cmp₁ x y t| + |l₂ t - l3c_cmp₂ x₀ x y t| := rfl
    rw [this, pow_succ]
    linarith
  have hwO := l3st_corollaryA_1_3_two_sided hτ'0 (Nat.succ_pos n) hwc (fun s _ ↦ hw0 s)
    (by positivity) (by positivity) hgron
  -- `λ₂ - C tⁿ = v₂ + (λ̃₂ - C tⁿ)`
  have hv2O : (fun t ↦ l₂ t - l3c_cmp₂ x₀ x y t) =O[𝓝 0] fun t ↦ t ^ (n + 1) := by
    have h1 : (fun t ↦ l₂ t - l3c_cmp₂ x₀ x y t) =O[𝓝 0] w :=
      IsBigO.of_bound' (Eventually.of_forall fun t ↦ by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw0 t)]
        simp only [w]; linarith [abs_nonneg (l₁ t - l3c_cmp₁ x y t)])
    exact isBigO_abs_right.1 ((h1.trans hwO).congr_right fun t ↦ (abs_pow t (n + 1)).symm)
  exact (hv2O.add hcmp).congr_left fun t ↦ by ring

/-- **Lemma 8.1.5** (`lem:lambda2-Landau`). Fix `λ_cost = -1`, `λ₃ = -λ_cost x₀² = x₀²` with
`|x₀| < 1/√3`, and `y₀ > 0`. Let `t₁ > 0`, let `u_e : (-t₁, t₁) → [-½, ½]` be any measurable
function, and let `x, y, λ₁, λ₂` solve the state equations (8.1.3) and the costate equations
(8.1.7) on `(-t₁, t₁)` with `(x, y)(0) = (x₀, y₀)` and `(λ₁, λ₂)(0) = (0, 0)` (continuous
solutions in integral form, with the state in the state space `y > 0`, `|x| < 1/√3` of
Definition 8.1.1). Then there are an integer `n ≥ 2` and a real `C ≠ 0`, depending on `(x₀, y₀)`
but not on the control `u_e`, such that `λ₂(t) = C tⁿ + O(tⁿ⁺¹)` (two-sided, TeX 6903–6907). In
particular `t = 0` is an isolated zero of `λ₂`.

Proof (the book's, TeX 6932–7015):
1. `n = 2` if `x₀ ≠ 0`, `n = 3` if `x₀ = 0`; `C = -2x₀/y₀` if `x₀ ≠ 0` (gap G5: the printed
   `-x₀(1 + y₀)/y₀²` is a slip) and `C = -2/3` if `x₀ = 0`.
2. Comparison functions `λ̃₁(t) = ∫₀ᵗ 2x/y`, `λ̃₂(t) = -∫₀ᵗ ((x² - x₀²)/y² + λ̃₁)`.
3. The Taylor expansions `y = y₀ + O(t)` (`y'` is bounded), `x = x₀ + y₀ t + O(t²)` give
   `λ̃₂ = C tⁿ + O(tⁿ⁺¹)`.
4. The error `v = (λ₁ - λ̃₁, λ₂ - λ̃₂)` solves `v' = -A v - λ̃₂ b` with
   `A = [[0, f₂ₓ], [1, f₂ᵧ]]`, `b = (f₂ₓ, f₂ᵧ)` evaluated along the trajectory; `‖A‖ ≤ C₀` near
   `0` (the denominator `-1 + 2√3 x u_e` stays away from `0`), so `‖v‖' ≤ ‖v'‖ ≤ C₁|t|ⁿ + C₀‖v‖`
   (Cauchy–Schwarz) and `‖v‖ ≤ C₁|t|ⁿ⁺¹/(n + 1) + C₀|∫₀ᵗ ‖v‖|`.
5. Gronwall (Corollary A.1.3, two-sided, `l3st_corollaryA_1_3_two_sided`): `‖v‖ = O(tⁿ⁺¹)`, so
   `|λ₂ - C tⁿ| ≤ ‖v‖ + |λ̃₂ - C tⁿ| = O(tⁿ⁺¹)`.
6. `C ≠ 0` and `λ₂ = C tⁿ + O(tⁿ⁺¹)` give `λ₂(t) ≠ 0` for small `t ≠ 0`.

In the formal proof, `[-τ, τ]` (the book's `(-t₂, t₂)`) is chosen by continuity at `0` so that
`|x - x₀| < δ/√3` and `|y - y₀| < y₀/2` there, with `δ = (1 - √3|x₀|)/2`; then
`-1 + 2√3 x u_e ≤ -δ` and the coefficients are bounded (`l3c_coef_bounds`). Steps 2–3 are
`l3c_taylor`, steps 4–5 `l3c_gronwall`. Two inessential changes in step 4: the norm is
`‖v‖ = |v₁| + |v₂|` instead of the Euclidean one, and the inequality `‖v‖' ≤ ‖v'‖` is used in its
integrated form `‖v(t)‖ ≤ |∫₀ᵗ ‖v'‖|` (`l3c_abs_integral_le`), which avoids differentiating the
norm; the Gronwall inequality obtained is the book's,
`‖v‖ ≤ C₁|t|ⁿ⁺¹ + C₀|∫₀ᵗ ‖v‖|`. -/
theorem lemma8_1_5 {x₀ y₀ : ℝ} (hx₀ : |x₀| < 1 / √3) (hy₀ : 0 < y₀) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ C : ℝ, C ≠ 0 ∧
      ∀ (t₁ : ℝ) (ue x y l₁ l₂ : ℝ → ℝ), 0 < t₁ → Measurable ue →
        (∀ t ∈ Ioo (-t₁) t₁, ue t ∈ edgeControlSet) →
        (∀ t ∈ Ioo (-t₁) t₁, 0 < y t ∧ |x t| < 1 / √3) →
        ContinuousOn x (Ioo (-t₁) t₁) → ContinuousOn y (Ioo (-t₁) t₁) →
        ContinuousOn l₁ (Ioo (-t₁) t₁) → ContinuousOn l₂ (Ioo (-t₁) t₁) →
        (∀ t ∈ Ioo (-t₁) t₁, x t = x₀ + ∫ s in (0 : ℝ)..t, y s) →
        (∀ t ∈ Ioo (-t₁) t₁, y t = y₀ + ∫ s in (0 : ℝ)..t, edgeF₂ (x s) (y s) (ue s)) →
        (∀ t ∈ Ioo (-t₁) t₁,
          l₁ t = ∫ s in (0 : ℝ)..t, edgeCostateRHS₁ (-1) (l₂ s) (x s) (y s) (ue s)) →
        (∀ t ∈ Ioo (-t₁) t₁,
          l₂ t = ∫ s in (0 : ℝ)..t,
            edgeCostateRHS₂ (-1) (l₁ s) (l₂ s) (x₀ ^ 2) (x s) (y s) (ue s)) →
        (fun t ↦ l₂ t - C * t ^ n) =O[𝓝 0] (fun t ↦ t ^ (n + 1)) ∧
          ∀ᶠ t in 𝓝[≠] 0, l₂ t ≠ 0 := by
  have h3 : 0 < √3 := by positivity
  -- step 1: `n` and `C`, with the expansion `λ̃₂ = C tⁿ + O(tⁿ⁺¹)` of steps 2–3
  obtain ⟨n, hn, C, hC, hT⟩ : ∃ n : ℕ, 2 ≤ n ∧ ∃ C : ℝ, C ≠ 0 ∧
      ∀ (x y : ℝ → ℝ) (τ M : ℝ), 0 < τ → ContinuousOn x (Icc (-τ) τ) →
        ContinuousOn y (Icc (-τ) τ) → (∀ s ∈ Icc (-τ) τ, 0 < y s) →
        (∀ t ∈ Icc (-τ) τ, x t = x₀ + ∫ s in (0 : ℝ)..t, y s) →
        (∀ t ∈ Icc (-τ) τ, |y t - y₀| ≤ M * |t|) →
        (fun t ↦ l3c_cmp₂ x₀ x y t - C * t ^ n) =O[𝓝 0] fun t ↦ t ^ (n + 1) := by
    by_cases hx0 : x₀ = 0
    · exact ⟨3, by norm_num, -2 / 3, by norm_num, fun x y τ M hτ hxc hyc hyp hx hyM ↦
        (l3c_taylor hτ hy₀ hxc hyc hyp hx hyM).2 hx0⟩
    · exact ⟨2, le_rfl, -2 * x₀ / y₀, div_ne_zero (mul_ne_zero (by norm_num) hx0) hy₀.ne',
        fun x y τ M hτ hxc hyc hyp hx hyM ↦ (l3c_taylor hτ hy₀ hxc hyc hyp hx hyM).1 hx0⟩
  refine ⟨n, hn, C, hC, ?_⟩
  intro t₁ ue x y l₁ l₂ ht₁ hmeas hue _ hxc hyc hl1c hl2c hx hy hl1 hl2
  have hUn : Ioo (-t₁) t₁ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) ht₁
  have h0U : (0 : ℝ) ∈ Ioo (-t₁) t₁ := ⟨by linarith, ht₁⟩
  have hx0 : x 0 = x₀ := by rw [hx 0 h0U, intervalIntegral.integral_same, add_zero]
  have hy0 : y 0 = y₀ := by rw [hy 0 h0U, intervalIntegral.integral_same, add_zero]
  -- a symmetric interval `[-τ, τ]` on which `|x - x₀| < δ/√3` and `|y - y₀| < y₀/2`, where
  -- `δ = (1 - √3|x₀|)/2`: there the denominator of `f₂` stays below `-δ`
  have hδ : 0 < (1 - √3 * |x₀|) / 2 := by
    have : √3 * |x₀| < √3 * (1 / √3) := mul_lt_mul_of_pos_left hx₀ h3
    rw [mul_one_div_cancel h3.ne'] at this
    linarith
  set δ := (1 - √3 * |x₀|) / 2 with hδdef
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.1 (hxc.continuousAt hUn) (δ / √3)
    (by positivity)
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.continuousAt_iff.1 (hyc.continuousAt hUn) (y₀ / 2)
    (by positivity)
  set τ := min (min δ₁ δ₂) t₁ / 2 with hτdef
  have hτ : 0 < τ := by positivity
  have hτ₁ : τ < δ₁ := by
    have := min_le_left (min δ₁ δ₂) t₁; have := min_le_left δ₁ δ₂; linarith
  have hτ₂ : τ < δ₂ := by
    have := min_le_left (min δ₁ δ₂) t₁; have := min_le_right δ₁ δ₂; linarith
  have hτ₃ : τ < t₁ := by have := min_le_right (min δ₁ δ₂) t₁; linarith
  set K := Icc (-τ) τ with hK
  have habs : ∀ s ∈ K, |s| ≤ τ := fun s hs ↦ abs_le.2 ⟨hs.1, hs.2⟩
  have hKU : K ⊆ Ioo (-t₁) t₁ := fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h0K : (0 : ℝ) ∈ K := ⟨by linarith, hτ.le⟩
  have hxK : ∀ s ∈ K, √3 * |x s| ≤ 1 - δ := by
    intro s hs
    have h1 := hδ₁' (x := s) (by rw [Real.dist_eq, sub_zero]; linarith [habs s hs])
    rw [Real.dist_eq, hx0] at h1
    have h2 : |x s| ≤ |x₀| + δ / √3 := by linarith [abs_sub_abs_le_abs_sub (x s) x₀]
    calc √3 * |x s| ≤ √3 * (|x₀| + δ / √3) := by gcongr
      _ = √3 * |x₀| + δ := by field_simp
      _ = 1 - δ := by rw [hδdef]; ring
  have hyK : ∀ s ∈ K, y₀ / 2 < y s ∧ y s ≤ 3 * y₀ / 2 := by
    intro s hs
    have h1 := hδ₂' (x := s) (by rw [Real.dist_eq, sub_zero]; linarith [habs s hs])
    rw [Real.dist_eq, hy0, abs_lt] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hypos : ∀ s ∈ K, 0 < y s := fun s hs ↦ by linarith [(hyK s hs).1]
  have hueK : ∀ s ∈ K, |ue s| ≤ 1 / 2 := fun s hs ↦ by
    have := hue s (hKU hs)
    simp only [edgeControlSet, mem_Icc] at this
    exact abs_le.2 this
  -- step 4: the coefficients are bounded on `[-τ, τ]`
  have hbd := fun s (hs : s ∈ K) ↦
    l3c_coef_bounds (hueK s hs) (hypos s hs) (hyK s hs).2 hδ (hxK s hs)
  -- `y = y₀ + O(t)`: `|y - y₀| ≤ M|t|`, `M = √3 (3y₀/2)²/δ`
  have hyM : ∀ t ∈ K, |y t - y₀| ≤ √3 * (3 * y₀ / 2) ^ 2 / δ * |t| := by
    intro t ht
    rw [hy t (hKU ht), add_sub_cancel_left]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (f := fun s ↦ edgeF₂ (x s) (y s) (ue s)) (C := √3 * (3 * y₀ / 2) ^ 2 / δ)
      fun s hs ↦ (hbd s (uIcc_subset_Icc h0K ht (uIoc_subset_uIcc hs))).1
    simpa [Real.norm_eq_abs] using this
  -- steps 2–3: the expansion of the comparison function `λ̃₂`
  have hTK := hT x y τ _ hτ (hxc.mono hKU) (hyc.mono hKU) hypos (fun t ht ↦ hx t (hKU ht)) hyM
  -- the coefficients are measurable
  have hxm : AEMeasurable x (volume.restrict K) := (hxc.mono hKU).aemeasurable measurableSet_Icc
  have hym : AEMeasurable y (volume.restrict K) := (hyc.mono hKU).aemeasurable measurableSet_Icc
  have hum : AEMeasurable ue (volume.restrict K) := hmeas.aemeasurable
  have ham : AEStronglyMeasurable (fun s ↦ l3c_fx (x s) (y s) (ue s)) (volume.restrict K) := by
    have : AEMeasurable (fun s ↦ l3c_fx (x s) (y s) (ue s)) (volume.restrict K) := by
      unfold l3c_fx; fun_prop
    exact this.aestronglyMeasurable
  have hbm : AEStronglyMeasurable (fun s ↦ l3c_fy (x s) (y s) (ue s)) (volume.restrict K) := by
    have : AEMeasurable (fun s ↦ l3c_fy (x s) (y s) (ue s)) (volume.restrict K) := by
      unfold l3c_fy; fun_prop
    exact this.aestronglyMeasurable
  -- steps 4–5: the error and Gronwall's inequality
  have hmain := l3c_gronwall hτ (hxc.mono hKU) (hyc.mono hKU) (hl1c.mono hKU) (hl2c.mono hKU)
    hypos (fun s hs ↦ (hbd s hs).2.1) (fun s hs ↦ (hbd s hs).2.2) ham hbm
    (fun t ht ↦ hl1 t (hKU ht)) (fun t ht ↦ hl2 t (hKU ht)) hTK
  refine ⟨hmain, ?_⟩
  -- step 6: `C ≠ 0`, so the zero at `t = 0` is isolated
  obtain ⟨c, -, hc⟩ := hmain.exists_nonneg
  rw [isBigOWith_iff] at hc
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), c * |t| < |C| := by
    have : Tendsto (fun t : ℝ ↦ c * |t|) (𝓝 0) (𝓝 (c * |0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    rw [abs_zero, mul_zero] at this
    exact this.eventually (gt_mem_nhds (abs_pos.2 hC))
  filter_upwards [nhdsWithin_le_nhds hc, nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin]
    with t h1 h2 h3 h0
  have ht0 : 0 < |t| := abs_pos.2 h3
  rw [h0, zero_sub, norm_neg, norm_mul, norm_pow, norm_pow, Real.norm_eq_abs,
    Real.norm_eq_abs, pow_succ] at h1
  have h4 : 0 < |t| ^ n := pow_pos ht0 n
  nlinarith [mul_lt_mul_of_pos_right h2 h4]

end SmoothedPolygons
