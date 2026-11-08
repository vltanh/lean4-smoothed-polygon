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
(inventory, gap G14). `corollaryA_1_3` is the book's statement; `l3st_corollaryA_1_3_two_sided`
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

/-- **Corollary A.1.3** (`thm:Gronwall`). Let `x : [0, t₁] → ℝ` be a nonnegative continuous
function, `n` a positive integer and `C, C₁` nonnegative real numbers with
`x(t) ≤ C tⁿ + C₁ ∫₀ᵗ x` for all `t ∈ [0, t₁]`. Then `x(t) = O(tⁿ)` for `t ≥ 0` near `0`.

Proof (the book gives none; this is the route through Lemma A.1.1 with constant data): for
`τ ∈ (0, t₁]`, on `[0, τ]` the hypothesis gives `x(t) ≤ C τⁿ + C₁ ∫₀ᵗ x`, so Gronwall's inequality
(`ControlSystem.le_mul_exp_of_le_add_integral`, Lemma A.1.1 with `ψ₁ = C τⁿ`, `ψ₂ = C₁`) gives
`x(t) ≤ C τⁿ e^{C₁ t}` there; at `t = τ`, `x(τ) ≤ (C e^{C₁ t₁}) τⁿ`. Expected size: 40–80 lines. -/
theorem corollaryA_1_3 {x : ℝ → ℝ} {t₁ C C₁ : ℝ} {n : ℕ} (ht₁ : 0 < t₁) (hn : 0 < n)
    (hx : ContinuousOn x (Icc 0 t₁)) (hx0 : ∀ t ∈ Icc 0 t₁, 0 ≤ x t) (hC : 0 ≤ C)
    (hC₁ : 0 ≤ C₁) (h : ∀ t ∈ Icc 0 t₁, x t ≤ C * t ^ n + C₁ * ∫ s in (0 : ℝ)..t, x s) :
    x =O[𝓝[≥] 0] fun t ↦ t ^ n := by
  sorry

/-- **Corollary A.1.3, two-sided** (the form in which Lemma 8.1.5 and the proof of Theorem 8.3.1
use it, TeX 7008, 7539, 7572; gap G14). Let `x` be nonnegative and continuous on `[-t₁, t₁]`,
`n` a positive integer, `C, C₁ ≥ 0`, and `x(t) ≤ C |t|ⁿ + C₁ |∫₀ᵗ x|` for `t ∈ [-t₁, t₁]`. Then
`x(t) = O(|t|ⁿ)` near `0`.

Proof: `corollaryA_1_3` applied to `x` on `[0, t₁]` and to `t ↦ x(-t)` on `[0, t₁]` (for
`t ≤ 0`, `|∫₀ᵗ x| = ∫₀^{-t} x(-s) ds`), and `𝓝 0 = 𝓝[≥] 0 ⊔ 𝓝[≤] 0`. Expected size: 30–60 lines. -/
theorem l3st_corollaryA_1_3_two_sided {x : ℝ → ℝ} {t₁ C C₁ : ℝ} {n : ℕ} (ht₁ : 0 < t₁)
    (hn : 0 < n) (hx : ContinuousOn x (Icc (-t₁) t₁)) (hx0 : ∀ t ∈ Icc (-t₁) t₁, 0 ≤ x t)
    (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (h : ∀ t ∈ Icc (-t₁) t₁, x t ≤ C * |t| ^ n + C₁ * |∫ s in (0 : ℝ)..t, x s|) :
    x =O[𝓝 0] fun t ↦ |t| ^ n := by
  sorry

end SmoothedPolygons
