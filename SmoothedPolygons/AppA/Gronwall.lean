module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Order.Basic
import OptimalControl.ODE.Caratheodory

/-!
# Gronwall's inequality (Appendix A.1)

Appendix A.1 (`sec:gronwall`, TeX 13075–13146) gives two versions of Gronwall's inequality,
cited without proof from Amann (*Ordinary Differential Equations*, p. 90; Lemma A.1.1) and Clarke
(*Functional Analysis, Calculus of Variations and Optimal Control*, Th. 6.41; Lemma A.1.2), and
the corollary that Chapter 8 uses (Corollary A.1.3, `thm:Gronwall`, TeX 13134):
`x(t) ≤ C tⁿ + C₁ ∫₀ᵗ x` on `[0, t₁]` implies `x(t) = O(tⁿ)` as `t → 0⁺`.

The corollary is stated on `[0, t₁]` but Chapter 8 applies it on two-sided intervals `(-t₁, t₁)`
(Lemma 8.1.5, TeX 7008; Theorem 8.3.1, TeX 7539, 7572), with the time reversal left implicit
(REPORT.md, E61). `corollaryA_1_3` is the book's statement; `corollaryA_1_3_two_sided`
is the two-sided form that Chapter 8 uses, obtained by applying the corollary to `t ↦ x(t)` and to
`t ↦ x(-t)`.

The book's Lemmas A.1.1 and A.1.2 are not stated here: the corollary is the only part of
Appendix A.1 cited by a proof (TeX 7008, 7539, 7572). Its proof uses, in place of Lemma A.1.1,
the integral Gronwall inequality of the OptimalControl package
(`ControlSystem.le_mul_exp_of_le_add_integral`: `φ ≤ C + L ∫ₐᵗ φ` implies `φ(t) ≤ C e^{L(t-a)}`),
which is Lemma A.1.1 with `ψ₁` constant and `ψ₂ = L`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology Asymptotics MeasureTheory

set_option linter.unusedVariables false in
/-- **Corollary A.1.3** (`thm:Gronwall`). Let `x : [0, t₁] → ℝ` be a nonnegative continuous
function, `n` a positive integer and `C, C₁` nonnegative real numbers with
`x(t) ≤ C tⁿ + C₁ ∫₀ᵗ x` for all `t ∈ [0, t₁]`. Then `x(t) = O(tⁿ)` for `t ≥ 0` near `0`.

Proof (the book gives none; this is the route through Lemma A.1.1 with constant data): for
`τ ∈ (0, t₁]`, on `[0, τ]` the hypothesis gives `x(t) ≤ C τⁿ + C₁ ∫₀ᵗ x`, so Gronwall's inequality
(`ControlSystem.le_mul_exp_of_le_add_integral`, Lemma A.1.1 with `ψ₁ = C τⁿ`, `ψ₂ = C₁`) gives
`x(t) ≤ C τⁿ e^{C₁ t}` there; at `t = τ`, `x(τ) ≤ (C e^{C₁ t₁}) τⁿ`. The hypothesis `0 < n`
(the book's "positive integer") is not used: the bound holds for `n = 0` as well. -/
theorem corollaryA_1_3 {x : ℝ → ℝ} {t₁ C C₁ : ℝ} {n : ℕ} (ht₁ : 0 < t₁) (hn : 0 < n)
    (hx : ContinuousOn x (Icc 0 t₁)) (hx0 : ∀ t ∈ Icc 0 t₁, 0 ≤ x t) (hC : 0 ≤ C)
    (hC₁ : 0 ≤ C₁) (h : ∀ t ∈ Icc 0 t₁, x t ≤ C * t ^ n + C₁ * ∫ s in (0 : ℝ)..t, x s) :
    x =O[𝓝[≥] 0] fun t ↦ t ^ n := by
  -- for `τ ∈ [0, t₁]`, Gronwall on `[0, τ]` with the constant `C τⁿ` gives `x(τ) ≤ C τⁿ e^{C₁ τ}`
  have hbound : ∀ τ ∈ Icc 0 t₁, x τ ≤ C * Real.exp (C₁ * t₁) * τ ^ n := by
    intro τ hτ
    have hsub : Icc 0 τ ⊆ Icc 0 t₁ := Icc_subset_Icc_right hτ.2
    have hg := ControlSystem.le_mul_exp_of_le_add_integral (a := 0) (b := τ) (C := C * τ ^ n)
      hC₁ (hx.mono hsub) (fun t ht ↦ hx0 t (hsub ht)) (fun t ht ↦ (h t (hsub ht)).trans (by
        gcongr <;> linarith [ht.1, ht.2])) τ ⟨hτ.1, le_rfl⟩
    rw [sub_zero] at hg
    calc x τ ≤ C * τ ^ n * Real.exp (C₁ * τ) := hg
      _ ≤ C * τ ^ n * Real.exp (C₁ * t₁) := by
        have := pow_nonneg hτ.1 n
        gcongr
        exact hτ.2
      _ = C * Real.exp (C₁ * t₁) * τ ^ n := by ring
  refine Asymptotics.IsBigO.of_bound (C * Real.exp (C₁ * t₁)) ?_
  filter_upwards [Icc_mem_nhdsGE ht₁] with τ hτ
  rw [Real.norm_of_nonneg (hx0 τ hτ), Real.norm_of_nonneg (pow_nonneg hτ.1 n)]
  exact hbound τ hτ

/-- **Corollary A.1.3, two-sided** (the form in which Lemma 8.1.5 and the proof of Theorem 8.3.1
use it, TeX 7008, 7539, 7572; E61). Let `x` be nonnegative and continuous on `[-t₁, t₁]`,
`n` a positive integer, `C, C₁ ≥ 0`, and `x(t) ≤ C |t|ⁿ + C₁ |∫₀ᵗ x|` for `t ∈ [-t₁, t₁]`. Then
`x(t) = O(|t|ⁿ)` near `0`.

Proof: `corollaryA_1_3` applied to `x` on `[0, t₁]` and to `t ↦ x(-t)` on `[0, t₁]` (for
`t ≤ 0`, `|∫₀ᵗ x| = ∫₀^{-t} x(-s) ds`), and `𝓝 0 = 𝓝[≤] 0 ⊔ 𝓝[≥] 0`. -/
theorem corollaryA_1_3_two_sided {x : ℝ → ℝ} {t₁ C C₁ : ℝ} {n : ℕ} (ht₁ : 0 < t₁)
    (hn : 0 < n) (hx : ContinuousOn x (Icc (-t₁) t₁)) (hx0 : ∀ t ∈ Icc (-t₁) t₁, 0 ≤ x t)
    (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (h : ∀ t ∈ Icc (-t₁) t₁, x t ≤ C * |t| ^ n + C₁ * |∫ s in (0 : ℝ)..t, x s|) :
    x =O[𝓝 0] fun t ↦ |t| ^ n := by
  have hsub : Icc 0 t₁ ⊆ Icc (-t₁) t₁ := Icc_subset_Icc_left (by linarith)
  have hmem : ∀ t ∈ Icc 0 t₁, -t ∈ Icc (-t₁) t₁ := fun t ht ↦
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  -- `t ≥ 0`: Corollary A.1.3 for `x` on `[0, t₁]`, where `|∫₀ᵗ x| = ∫₀ᵗ x`
  have hR : x =O[𝓝[≥] 0] fun t ↦ t ^ n := corollaryA_1_3 ht₁ hn (hx.mono hsub)
    (fun t ht ↦ hx0 t (hsub ht)) hC hC₁ fun t ht ↦ by
      have hnn : 0 ≤ ∫ s in (0 : ℝ)..t, x s := intervalIntegral.integral_nonneg ht.1
        fun s hs ↦ hx0 s (hsub ⟨hs.1, hs.2.trans ht.2⟩)
      simpa only [abs_of_nonneg ht.1, abs_of_nonneg hnn] using h t (hsub ht)
  -- `t ≤ 0`: Corollary A.1.3 for `t ↦ x(-t)` on `[0, t₁]`, where `|∫₀^{-t} x| = ∫₀ᵗ x(-s) ds`
  have hL : (fun t ↦ x (-t)) =O[𝓝[≥] 0] fun t ↦ t ^ n := corollaryA_1_3 ht₁ hn
    (hx.comp continuous_neg.continuousOn hmem) (fun t ht ↦ hx0 _ (hmem t ht)) hC hC₁
    fun t ht ↦ by
      have h1 := h (-t) (hmem t ht)
      have hnn : 0 ≤ ∫ s in (0 : ℝ)..t, x (-s) := intervalIntegral.integral_nonneg ht.1
        fun s hs ↦ hx0 _ (hmem s ⟨hs.1, hs.2.trans ht.2⟩)
      have hint : ∫ s in (0 : ℝ)..-t, x s = -∫ s in (0 : ℝ)..t, x (-s) := by
        rw [intervalIntegral.integral_comp_neg, neg_zero, intervalIntegral.integral_symm]
      rwa [hint, abs_neg, abs_neg, abs_of_nonneg hnn, abs_of_nonneg ht.1] at h1
  have hneg : Tendsto (fun t : ℝ ↦ -t) (𝓝[≤] 0) (𝓝[≥] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_neg.tendsto' 0 0 neg_zero).mono_left
      nhdsWithin_le_nhds), eventually_nhdsWithin_of_forall fun t ht ↦ neg_nonneg.2 ht⟩
  have hL' : x =O[𝓝[≤] 0] fun t ↦ |t| ^ n := by
    refine (hL.comp_tendsto hneg).congr' (Eventually.of_forall fun t ↦ by simp)
      (eventually_nhdsWithin_of_forall fun t ht ↦ ?_)
    simp only [Function.comp_apply, abs_of_nonpos (show t ≤ 0 from ht)]
  have hR' : x =O[𝓝[≥] 0] fun t ↦ |t| ^ n :=
    hR.congr' (Eventually.of_forall fun _ ↦ rfl) (eventually_nhdsWithin_of_forall fun t ht ↦ by
      simp only [abs_of_nonneg (show 0 ≤ t from ht)])
  rw [← nhdsLE_sup_nhdsGE]
  exact hL'.sup hR'

end SmoothedPolygons
