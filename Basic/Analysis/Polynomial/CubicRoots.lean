module

public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Positive roots of real cubics with given coefficient signs

Descartes's rule of signs for the sign patterns of real cubics `a t³ + b t² + c t + d` that occur
in the switching functions of the Fuller system, with elementary proofs:

* the pattern `+ + + -` (from the constant term up): if `a₀, a₁, a₂ ≥ 0` and the cubic vanishes at
  `T > 0`, then `T³ f(t) = a₀(T³ - t³) + a₁ t T (T² - t²) + a₂ t² T² (T - t)`, so `f ≥ 0` on
  `[0, T]`, `f > 0` on `[0, T)` and `f < 0` on `(T, ∞)` when `a₀ > 0` (`cubic_nonneg_of_le_root`,
  `cubic_pos_of_lt_root`, `cubic_neg_of_root_lt`);
* `a < 0 < c, d`: a unique positive root, at which the cubic changes sign
  (`exists_pos_root_cubic_of_neg_of_pos_of_pos`; `t² P(s) - s² P(t) > 0` for `0 ≤ s < t`);
* `a, d > 0 > c`: a negative root `r₀` splits off, `P = (t - r₀) q`, and
  `Δ(P) = Δ(q) q(r₀)²` with `q(r₀) > 0` (`exists_neg_root_cubic_factor`), so the discriminant
  decides between two positive roots (`exists_roots_cubic_of_discr_nonneg`,
  `Polynomial.card_roots_filter_pos_eq_two`) and none (`cubic_nonneg_of_discr_nonpos`).

The discriminant is Mathlib's `Polynomial.discr`, which for a cubic is `Cubic.discr`
(`Cubic.discr_toPoly`). Mathlib's Descartes's rule of signs
(`Polynomial.roots_countP_pos_le_signVariations`) bounds the number of positive roots from above;
the exact counts here are proved directly.
-/

@[expose] public section

open Polynomial

/-- **The sign of a cubic below a positive root**, for the sign pattern `+ + + -`: if
`f(t) = a₀ + a₁t + a₂t² + a₃t³` with `a₀, a₁, a₂ ≥ 0` vanishes at `T > 0`, then
`T³ f(t) = a₀(T³ - t³) + a₁ t T (T² - t²) + a₂ t² T² (T - t)`, so `f ≥ 0` on `[0, T]`. -/
theorem cubic_nonneg_of_le_root {a0 a1 a2 a3 T t : ℝ} (h0 : 0 ≤ a0) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2)
    (hT : 0 < T) (hroot : a0 + a1 * T + a2 * T ^ 2 + a3 * T ^ 3 = 0) (ht0 : 0 ≤ t)
    (htT : t ≤ T) : 0 ≤ a0 + a1 * t + a2 * t ^ 2 + a3 * t ^ 3 := by
  have key : T ^ 3 * (a0 + a1 * t + a2 * t ^ 2 + a3 * t ^ 3) =
      a0 * (T ^ 3 - t ^ 3) + a1 * t * T * (T ^ 2 - t ^ 2) + a2 * t ^ 2 * T ^ 2 * (T - t) := by
    linear_combination t ^ 3 * hroot
  have h3 : 0 ≤ T ^ 3 - t ^ 3 := sub_nonneg.2 (pow_le_pow_left₀ ht0 htT 3)
  have h2' : 0 ≤ T ^ 2 - t ^ 2 := sub_nonneg.2 (pow_le_pow_left₀ ht0 htT 2)
  have hrhs : 0 ≤ a0 * (T ^ 3 - t ^ 3) + a1 * t * T * (T ^ 2 - t ^ 2) +
      a2 * t ^ 2 * T ^ 2 * (T - t) :=
    add_nonneg (add_nonneg (mul_nonneg h0 h3) (mul_nonneg (mul_nonneg (mul_nonneg h1 ht0) hT.le)
      h2')) (mul_nonneg (by positivity) (sub_nonneg.2 htT))
  by_contra hneg
  have := mul_neg_of_pos_of_neg (pow_pos hT 3) (not_le.1 hneg)
  linarith

/-- **The same cubic is positive before its root** when `a₀ > 0`: `f > 0` on `[0, T)`, by the same
identity `T³ f(t) = a₀(T³ - t³) + a₁ t T (T² - t²) + a₂ t² T² (T - t)`. -/
theorem cubic_pos_of_lt_root {c₀ c₁ c₂ c₃ T t : ℝ} (h₀ : 0 < c₀) (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂)
    (hT : c₀ + c₁ * T + c₂ * T ^ 2 + c₃ * T ^ 3 = 0) (ht : 0 ≤ t) (htT : t < T) :
    0 < c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3 := by
  have hT0 : 0 < T := ht.trans_lt htT
  have key : T ^ 3 * (c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3) =
      c₀ * (T ^ 3 - t ^ 3) + c₁ * t * T * (T ^ 2 - t ^ 2) + c₂ * t ^ 2 * T ^ 2 * (T - t) := by
    linear_combination t ^ 3 * hT
  have e1 : 0 < T ^ 3 - t ^ 3 := by
    have := pow_lt_pow_left₀ htT ht (by norm_num : (3 : ℕ) ≠ 0)
    linarith
  have e2 : 0 ≤ T ^ 2 - t ^ 2 := by
    have := pow_le_pow_left₀ ht htT.le 2
    linarith
  have e3 : 0 < c₀ * (T ^ 3 - t ^ 3) := mul_pos h₀ e1
  have e4 : 0 ≤ c₁ * t * T * (T ^ 2 - t ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg h₁ ht) hT0.le) e2
  have e5 : 0 ≤ c₂ * t ^ 2 * T ^ 2 * (T - t) :=
    mul_nonneg (mul_nonneg (mul_nonneg h₂ (sq_nonneg t)) (sq_nonneg T)) (by linarith)
  have hpos : 0 < T ^ 3 * (c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3) := by
    rw [key]
    linarith
  exact pos_of_mul_pos_right hpos (by positivity)

/-- **The same cubic is negative after its root** `T` (with `a₀ > 0`). -/
theorem cubic_neg_of_root_lt {a0 a1 a2 a3 T t : ℝ} (h0 : 0 < a0) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2)
    (hT : 0 < T) (hroot : a0 + a1 * T + a2 * T ^ 2 + a3 * T ^ 3 = 0) (hTt : T < t) :
    a0 + a1 * t + a2 * t ^ 2 + a3 * t ^ 3 < 0 := by
  have ht0 : 0 < t := hT.trans hTt
  have key : T ^ 3 * (a0 + a1 * t + a2 * t ^ 2 + a3 * t ^ 3) =
      a0 * (T ^ 3 - t ^ 3) + a1 * t * T * (T ^ 2 - t ^ 2) + a2 * t ^ 2 * T ^ 2 * (T - t) := by
    linear_combination t ^ 3 * hroot
  have h3 : T ^ 3 - t ^ 3 < 0 := sub_neg.2 (pow_lt_pow_left₀ hTt hT.le (by norm_num))
  have h2' : T ^ 2 - t ^ 2 < 0 := sub_neg.2 (pow_lt_pow_left₀ hTt hT.le (by norm_num))
  have hrhs : a0 * (T ^ 3 - t ^ 3) + a1 * t * T * (T ^ 2 - t ^ 2) +
      a2 * t ^ 2 * T ^ 2 * (T - t) < 0 := by
    have e1 := mul_neg_of_pos_of_neg h0 h3
    have e2 : a1 * t * T * (T ^ 2 - t ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h2'.le
    have e3 : a2 * t ^ 2 * T ^ 2 * (T - t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  by_contra hnn
  have := mul_nonneg (pow_pos hT 3).le (not_lt.1 hnn)
  linarith

/-- The cubic `a t³ + b t² + c t + d` with `a < 0 < c, d` (one sign change) has a unique positive
root `T`, positive on `[0, T)` and negative on `(T, ∞)`: `t² P(s) - s² P(t) =
(t - s)(d (t + s) + c t s - a s² t²) > 0` for `0 ≤ s < t`. -/
theorem exists_pos_root_cubic_of_neg_of_pos_of_pos {a b c d : ℝ} (ha : a < 0) (hc : 0 < c)
    (hd : 0 < d) :
    ∃ T > 0, a * T ^ 3 + b * T ^ 2 + c * T + d = 0 ∧
      (∀ t, 0 ≤ t → t < T → 0 < a * t ^ 3 + b * t ^ 2 + c * t + d) ∧
      ∀ t, T < t → a * t ^ 3 + b * t ^ 2 + c * t + d < 0 := by
  set f : ℝ → ℝ := fun t ↦ a * t ^ 3 + b * t ^ 2 + c * t + d with hf
  have key : ∀ s t, 0 ≤ s → s < t → s ^ 2 * f t < t ^ 2 * f s := by
    intro s t hs hst
    have e : t ^ 2 * f s - s ^ 2 * f t =
        (t - s) * (d * (t + s) + c * t * s - a * s ^ 2 * t ^ 2) := by
      simp only [hf]; ring
    have h1 : 0 < d * (t + s) := mul_pos hd (by linarith)
    have h2 : 0 ≤ c * t * s := mul_nonneg (mul_nonneg hc.le (by linarith)) hs
    have h3 : 0 ≤ -a * s ^ 2 * t ^ 2 := by
      have : 0 ≤ -a := by linarith
      positivity
    have : 0 < (t - s) * (d * (t + s) + c * t * s - a * s ^ 2 * t ^ 2) :=
      mul_pos (by linarith) (by linarith)
    linarith
  set M := 1 + (|b| + c + d) / (-a) with hM
  have hM0 : 0 ≤ (|b| + c + d) / (-a) := div_nonneg (by positivity) (by linarith)
  have hM1 : 1 ≤ M := by linarith
  have haM : a * M = a - (|b| + c + d) := by
    rw [hM, mul_add, mul_one, mul_div_assoc', div_neg, mul_comm a, mul_div_assoc,
      div_self ha.ne, mul_one]
    ring
  have hfM : f M < 0 := by
    simp only [hf]
    have h1 : b * M ^ 2 ≤ |b| * M ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self b) (sq_nonneg M)
    have hM2 : 1 ≤ M ^ 2 := by nlinarith
    have h2 : c * M ≤ c * M ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hc.le
    have h3 : d ≤ d * M ^ 2 := le_mul_of_one_le_right hd.le hM2
    have h4 : a * M ^ 3 + |b| * M ^ 2 + c * M ^ 2 + d * M ^ 2 = a * M ^ 2 := by
      have : a * M ^ 3 = (a * M) * M ^ 2 := by ring
      rw [this, haM]; ring
    have h5 : a * M ^ 2 < 0 := mul_neg_of_neg_of_pos ha (by positivity)
    linarith
  obtain ⟨T, hT, hfT⟩ : ∃ T ∈ Set.Icc 0 M, f T = 0 :=
    intermediate_value_Icc' (show (0 : ℝ) ≤ M by linarith)
      (by fun_prop : Continuous f).continuousOn ⟨hfM.le, by simp only [hf]; linarith⟩
  have hf0 : f 0 = d := by simp only [hf]; ring
  have hT0 : 0 < T := by
    rcases hT.1.eq_or_lt with h | h
    · rw [← h, hf0] at hfT; linarith
    · exact h
  refine ⟨T, hT0, hfT, fun t ht htT ↦ ?_, fun t ht ↦ ?_⟩
  · have := key t T ht htT
    rw [hfT, mul_zero] at this
    exact pos_of_mul_pos_right this (by positivity)
  · have := key T t hT0.le ht
    rw [hfT, mul_zero] at this
    exact neg_of_mul_neg_right this (by positivity)

/-- The discriminant of a real cubic polynomial (Mathlib's `Polynomial.discr`) is `Cubic.discr`,
`b² c² - 4 a c³ - 4 b³ d - 27 a² d² + 18 a b c d`. -/
theorem Cubic.discr_toPoly (P : Cubic ℝ) (ha : P.a ≠ 0) : P.toPoly.discr = P.discr := by
  rw [discr_of_degree_eq_three (Cubic.degree_of_a_ne_zero ha), Cubic.coeff_eq_a,
    Cubic.coeff_eq_b, Cubic.coeff_eq_c, Cubic.coeff_eq_d, Cubic.discr]

/-- The cubic `a t³ + b t² + c t + d` with `a > 0 > c` and `d > 0`: it has a negative root `r₀`
(intermediate value theorem), and `P = (t - r₀) q` with `q = a t² + β t + γ`, `β < 0 < γ`,
`q(r₀) > 0`, and the discriminant is `Δ(P) = Δ(q) q(r₀)²`. -/
theorem exists_neg_root_cubic_factor {a b c d : ℝ} (ha : 0 < a) (hc : c < 0) (hd : 0 < d) :
    ∃ r₀ β γ : ℝ, r₀ < 0 ∧ β < 0 ∧ 0 < γ ∧ 0 < a * r₀ ^ 2 + β * r₀ + γ ∧
      b = β - a * r₀ ∧ c = γ - β * r₀ ∧ d = -(γ * r₀) ∧
      b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 + 18 * a * b * c * d =
        (β ^ 2 - 4 * a * γ) * (a * r₀ ^ 2 + β * r₀ + γ) ^ 2 := by
  set f : ℝ → ℝ := fun t ↦ a * t ^ 3 + b * t ^ 2 + c * t + d with hf
  set M := 1 + (|b| + |c| + d) / a with hM
  have hM0 : 0 ≤ (|b| + |c| + d) / a := by positivity
  have hM1 : 1 ≤ M := by linarith
  have haM : a * M = a + (|b| + |c| + d) := by
    rw [hM, mul_add, mul_one, mul_div_assoc', mul_comm a, mul_div_assoc, div_self ha.ne',
      mul_one]
  have hfM : f (-M) < 0 := by
    simp only [hf]
    have h1 : b * M ^ 2 ≤ |b| * M ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self b) (sq_nonneg M)
    have h2 : -c * M ≤ |c| * M ^ 2 :=
      (mul_le_mul_of_nonneg_right (neg_le_abs c) (by linarith)).trans
        (mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg c))
    have hM2 : 1 ≤ M ^ 2 := by nlinarith
    have h3 : d ≤ d * M ^ 2 := le_mul_of_one_le_right hd.le hM2
    have h4 : -(a * M ^ 3) + |b| * M ^ 2 + |c| * M ^ 2 + d * M ^ 2 = -(a * M ^ 2) := by
      have : a * M ^ 3 = (a * M) * M ^ 2 := by ring
      rw [this, haM]; ring
    have h5 : 0 < a * M ^ 2 := mul_pos ha (by positivity)
    linarith
  obtain ⟨r₀, hr₀, hfr₀⟩ : ∃ r₀ ∈ Set.Icc (-M) 0, f r₀ = 0 :=
    intermediate_value_Icc (show -M ≤ 0 by linarith) (by fun_prop : Continuous f).continuousOn
      ⟨hfM.le, by simp only [hf]; linarith⟩
  have hf0 : f 0 = d := by simp only [hf]; ring
  have hr₀0 : r₀ < 0 := by
    rcases hr₀.2.lt_or_eq with h | h
    · exact h
    · rw [h, hf0] at hfr₀; linarith
  obtain ⟨β, hβ⟩ : ∃ β, b = β - a * r₀ := ⟨b + a * r₀, by ring⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, c = γ - β * r₀ := ⟨c + β * r₀, by ring⟩
  have hdγ : d = -(γ * r₀) := by
    simp only [hf] at hfr₀
    rw [hβ, hγ] at hfr₀
    linear_combination hfr₀
  have hγ0 : 0 < γ := by nlinarith
  have hβ0 : β < 0 := by nlinarith
  refine ⟨r₀, β, γ, hr₀0, hβ0, hγ0, ?_, hβ, hγ, hdγ, ?_⟩
  · nlinarith [mul_pos_of_neg_of_neg hβ0 hr₀0, sq_pos_of_neg hr₀0]
  · subst hβ hγ hdγ
    ring

/-- With the signs of `exists_neg_root_cubic_factor`: if `Δ ≤ 0`, the cubic is `≥ 0` on `[0, ∞)`,
and `> 0` if `Δ < 0` (`q` has no real root, or a double one; `t - r₀ > 0`). -/
theorem cubic_nonneg_of_discr_nonpos {a b c d : ℝ} (ha : 0 < a) (hc : c < 0) (hd : 0 < d)
    (hD : b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 +
      18 * a * b * c * d ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ a * t ^ 3 + b * t ^ 2 + c * t + d ∧
      (b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 + 18 * a * b * c * d < 0 →
        0 < a * t ^ 3 + b * t ^ 2 + c * t + d) := by
  obtain ⟨r₀, β, γ, hr₀, -, -, hq₀, hβ, hγ, hdγ, hΔ⟩ :=
    exists_neg_root_cubic_factor (b := b) ha hc hd
  have hfac : a * t ^ 3 + b * t ^ 2 + c * t + d = (t - r₀) * (a * t ^ 2 + β * t + γ) := by
    rw [hβ, hγ, hdγ]; ring
  have hq4 : 4 * a * (a * t ^ 2 + β * t + γ) = (2 * a * t + β) ^ 2 - (β ^ 2 - 4 * a * γ) := by
    ring
  have hsq : 0 < (a * r₀ ^ 2 + β * r₀ + γ) ^ 2 := by positivity
  have hδ : β ^ 2 - 4 * a * γ ≤ 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_pos h hsq]
  rw [hfac, hΔ]
  constructor
  · have : 0 ≤ a * t ^ 2 + β * t + γ := by nlinarith [sq_nonneg (2 * a * t + β)]
    exact mul_nonneg (by linarith) this
  · intro hneg
    have hδ' : β ^ 2 - 4 * a * γ < 0 := by
      by_contra h
      push Not at h
      nlinarith [mul_nonneg h hsq.le]
    have : 0 < a * t ^ 2 + β * t + γ := by nlinarith [sq_nonneg (2 * a * t + β)]
    exact mul_pos (by linarith) this

/-- With the signs of `exists_neg_root_cubic_factor`: if `Δ ≥ 0`, the cubic is
`a (t - r₀)(t - r₁)(t - r₂)` with `r₀ < 0 < r₁ ≤ r₂` (Descartes's rule of signs for this sign
pattern), and `r₁ < r₂` if `Δ > 0`. -/
theorem exists_roots_cubic_of_discr_nonneg {a b c d : ℝ} (ha : 0 < a) (hc : c < 0) (hd : 0 < d)
    (hD : 0 ≤ b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 +
      18 * a * b * c * d) :
    ∃ r₀ r₁ r₂ : ℝ, r₀ < 0 ∧ 0 < r₁ ∧ r₁ ≤ r₂ ∧
      (0 < b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 +
        18 * a * b * c * d → r₁ < r₂) ∧
      b = a * -(r₀ + r₁ + r₂) ∧ c = a * (r₀ * r₁ + r₀ * r₂ + r₁ * r₂) ∧
      d = a * -(r₀ * r₁ * r₂) := by
  obtain ⟨r₀, β, γ, hr₀, hβ0, hγ0, hq₀, hβ, hγ, hdγ, hΔ⟩ :=
    exists_neg_root_cubic_factor (b := b) ha hc hd
  have hsq : 0 < (a * r₀ ^ 2 + β * r₀ + γ) ^ 2 := by positivity
  have hδ : 0 ≤ β ^ 2 - 4 * a * γ := by
    by_contra h
    push Not at h
    nlinarith [mul_neg_of_neg_of_pos h hsq]
  set s := √(β ^ 2 - 4 * a * γ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = β ^ 2 - 4 * a * γ := Real.sq_sqrt hδ
  have hsβ : s < -β := by nlinarith [mul_pos ha hγ0]
  refine ⟨r₀, (-β - s) / (2 * a), (-β + s) / (2 * a), hr₀, by apply div_pos <;> linarith,
    by apply div_le_div_of_nonneg_right <;> linarith, fun hpos ↦ ?_, ?_, ?_, ?_⟩
  · have hδ' : 0 < β ^ 2 - 4 * a * γ := by
      by_contra h
      push Not at h
      nlinarith [mul_le_mul_of_nonneg_right h hsq.le]
    have : 0 < s := Real.sqrt_pos.2 hδ'
    apply div_lt_div_of_pos_right _ (by linarith)
    linarith
  · rw [hβ]; field_simp; ring
  · rw [hγ]; field_simp; linear_combination hss
  · rw [hdγ]; field_simp; linear_combination (-r₀) * hss

/-- The positive roots of `a (t - r₀)(t - r₁)(t - r₂)` with `r₀ < 0 < r₁ ≤ r₂`, counted with
multiplicity: two. -/
theorem Polynomial.card_roots_filter_pos_eq_two {a r₀ r₁ r₂ : ℝ} (ha : a ≠ 0) (h₀ : r₀ < 0)
    (h₁ : 0 < r₁) (h₁₂ : r₁ ≤ r₂) :
    ((C a * (X - C r₀) * (X - C r₁) * (X - C r₂)).roots.filter (fun t ↦ 0 < t)).card = 2 := by
  have h12 : (X - C r₁) * (X - C r₂) ≠ 0 := mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  rw [mul_assoc, mul_assoc, roots_C_mul _ ha, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) h12),
    roots_mul h12, roots_X_sub_C, roots_X_sub_C, roots_X_sub_C, Multiset.filter_add,
    Multiset.filter_add, Multiset.filter_singleton, Multiset.filter_singleton,
    Multiset.filter_singleton]
  simp [not_lt.2 h₀.le, h₁, h₁.trans_le h₁₂]
