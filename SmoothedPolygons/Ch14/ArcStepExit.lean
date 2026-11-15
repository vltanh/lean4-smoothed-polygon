module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import SmoothedPolygons.Ch14.ArcStepClosed

/-!
# Chapter 14, N4: the exit criterion for the next arc (the proof of (INV), III)

`notes/inv/inv.md` Proposition 5, Lemma 6 and the two transcendental inputs of the proof:
* `two_mul_sub_one_div_add_one_le_log`: `log s ≥ 2(s - 1)/(s + 1)` for `s ≥ 1`;
* `log_sixteen_div_five_gt`: `log(16/5) > 297/256`;
* `qNew_le_f0New` (Proposition 5): on every switching arc,
  `f₀,new ≥ q_new (1 - 1/Y_new)`; it needs neither E nor the relation, only `F(log s) = 0`;
* `f_pos_of_Y_ge` (Lemma 6, the parameter part): if `Y ≥ 16/5`, `f₀ > 0` and
  `f₀ ≥ q (1 - 1/Y)`, then `f > 0` on `[0, log Y)`, so the arc exits before switching
  (`arcLeavesStarDomain_of_Y_ge`, `SmoothedPolygons/Ch14/ArcConditions.lean`).
Part of the proof of (INV) (`arcRegionInvariant`, `SmoothedPolygons/Ch14/ArcRegionInvariant.lean`).

**Departure from the paper.** The book computes the unstable curve numerically (Figure 14.2,
TeX 11951–11991); the formalization proves N4 from (INV) by the exact structure of the arcs (see
`SmoothedPolygons/Ch14/ArcParams.lean`), and (INV) by the argument of `notes/inv/inv.md`.

## Notation

As in `SmoothedPolygons/Ch14/ArcStepClosed.lean`; `x = Y - 2`, `y = Y' - 2`, `z = s - Y + 1`
(inv.md's `a, b, c`), `N_Y = Y' s² - 2s + Y` (the numerator of `Y_new`),
`φ(s) = (Y' - 1) s³ - (2Y' + 1) s² + (2Y + 1) s - (Y - 1)`, and (inv.md (1.1))
`b_Y(y) = Y log y - (y - 1) - (Y - 1)(y - 1)/y`, so that `F(log y) = f₀ + b_Y(y) - q (y - 1)/y`.
The identities are checked exactly in `notes/inv/verify.py` §5–§6, `notes/n4rev/t8_inv_exact.py`,
and as written here (with the certificates) in `notes/n4s2/docs_check.py`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set

/-- **`log s ≥ 2(s - 1)/(s + 1)` for `s ≥ 1`** (inv.md §5, used in Proposition 5).

Route: for `s = 1` both sides are `0`. For `s > 1`, `Real.hasSum_log_one_add_inv` with
`a = 1/(s - 1)` (`1 + a⁻¹ = s`, `1/(2a + 1) = (s - 1)/(s + 1)`) writes `log s` as a series of
nonnegative terms `2/(2k + 1) · ((s - 1)/(s + 1))^{2k + 1}` whose first term is the bound
(`sum_le_hasSum (Finset.range 1)`). Alternatively: `h(s) = log s - 2(s - 1)/(s + 1)` has `h(1) = 0`
and `h'(s) = (s - 1)²/(s (s + 1)²) ≥ 0`. -/
theorem two_mul_sub_one_div_add_one_le_log {s : ℝ} (hs : 1 ≤ s) :
    2 * (s - 1) / (s + 1) ≤ Real.log s := by
  rcases hs.lt_or_eq with hs | rfl
  · have ha : 0 < 1 / (s - 1) := one_div_pos.2 (by linarith)
    have h := Real.hasSum_log_one_add_inv ha
    rw [show 1 + (1 / (s - 1))⁻¹ = s by field_simp; ring] at h
    have h0 := sum_le_hasSum (Finset.range 1) (fun k _ => by positivity) h
    rw [Finset.sum_range_one] at h0
    have e2 : 2 * (1 / (s - 1)) + 1 = (s + 1) / (s - 1) := by
      have : s - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [e2, one_div_div] at h0
    norm_num at h0
    rw [mul_div_assoc]
    linarith
  · simp

/-- **`log(16/5) > 297/256`** (inv.md Lemma 6: `g(16/5) > 0`, i.e.
`log(16/5) > (Y - 1)(2Y - 1)/Y²` at `Y = 16/5`, which is `297/256 = 1.16016`).

Route: `Real.hasSum_log_one_add_inv` with `a = 5/11` (`1 + a⁻¹ = 16/5`, `1/(2a + 1) = 11/21`;
this is `log(16/5) = 2 atanh(11/21)`); the terms are nonnegative, so the partial sum of the first
four, `2 (x + x³/3 + x⁵/5 + x⁷/7)` at `x = 11/21`, which is `73269045344/63038098935 = 1.16230`,
is a lower bound (`sum_le_hasSum (Finset.range 4)`, then `norm_num [Finset.sum_range_succ]`).
The true value is `1.16315`. -/
theorem log_sixteen_div_five_gt : 297 / 256 < Real.log (16 / 5) := by
  have h := Real.hasSum_log_one_add_inv (by norm_num : (0 : ℝ) < 5 / 11)
  rw [show (1 : ℝ) + (5 / 11)⁻¹ = 16 / 5 by norm_num] at h
  have h0 := sum_le_hasSum (Finset.range 4) (fun k _ => by positivity) h
  norm_num [Finset.sum_range_succ] at h0
  linarith

/-! ### Real-number lemmas for Proposition 5 (inv.md §5)

In `x = Y - 2`, `y = Y' - 2`, `z = s - Y + 1`, `w = 1 - z` (so `Y = 2 + x`, `Y' = 2 + y`,
`s = 1 + x + z`), with `N_Y = Y' s² - 2s + Y`. -/

/-- The Bernstein form of `τ_q` in `z, w` (`w = 1 - z`): the lists of `ArcParams.qNew_le_f0New`,
each coefficient written `C(n, k) * β_k`. -/
private theorem n4h_bern_tq (x y z w : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    0 ≤
      (2 * w ^ 4 + 4 * 4 * z * w ^ 3 + 6 * 8 * z ^ 2 * w ^ 2 + 4 * 14 * z ^ 3 * w + 18 * z ^ 4) +
      y * (4 * w ^ 4 + 4 * (15 / 2) * z * w ^ 3 + 6 * 13 * z ^ 2 * w ^ 2 + 4 * 20 * z ^ 3 * w +
        24 * z ^ 4) +
      y ^ 2 * (2 * w ^ 4 + 4 * (13 / 4) * z * w ^ 3 + 6 * 5 * z ^ 2 * w ^ 2 + 4 * 7 * z ^ 3 * w +
        8 * z ^ 4) +
      x * (9 * w ^ 3 + 3 * (55 / 3) * z * w ^ 2 + 3 * (91 / 3) * z ^ 2 * w + 33 * z ^ 3) +
      x * y * (16 * w ^ 3 + 3 * (80 / 3) * z * w ^ 2 + 3 * (116 / 3) * z ^ 2 * w + 40 * z ^ 3) +
      x * y ^ 2 * (6 * w ^ 3 + 3 * 9 * z * w ^ 2 + 3 * 12 * z ^ 2 * w + 12 * z ^ 3) +
      x ^ 2 * (16 * w ^ 2 + 2 * 24 * z * w + 20 * z ^ 2) +
      x ^ 2 * y * (20 * w ^ 2 + 2 * 27 * z * w + 22 * z ^ 2) +
      x ^ 2 * y ^ 2 * (6 * w ^ 2 + 2 * (15 / 2) * z * w + 6 * z ^ 2) +
      x ^ 3 * (8 * w + 4 * z) +
      x ^ 3 * y * (8 * w + 4 * z) +
      x ^ 3 * y ^ 2 * (2 * w + 1 * z) := by
  positivity

/-- The Bernstein form of `U` in `z, w` (`w = 1 - z`), the terms `x^i y^j` with `i ≤ 1`. -/
private theorem n4h_bern_U₀ (x y z w : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hw : 0 ≤ w) :
    0 ≤
      (6 * 1 * z * w ^ 5 + 15 * (56 / 15) * z ^ 2 * w ^ 4 + 20 * (48 / 5) * z ^ 3 * w ^ 3 +
        15 * (102 / 5) * z ^ 4 * w ^ 2 + 6 * (116 / 3) * z ^ 5 * w + 72 * z ^ 6) +
      y * (4 * w ^ 6 + 6 * (25 / 3) * z * w ^ 5 + 15 * (236 / 15) * z ^ 2 * w ^ 4 +
        20 * (273 / 10) * z ^ 3 * w ^ 3 + 15 * (656 / 15) * z ^ 4 * w ^ 2 +
        6 * (196 / 3) * z ^ 5 * w + 96 * z ^ 6) +
      y ^ 2 * (4 * w ^ 6 + 6 * (19 / 3) * z * w ^ 5 + 15 * (29 / 3) * z ^ 2 * w ^ 4 +
        20 * (141 / 10) * z ^ 3 * w ^ 3 + 15 * (292 / 15) * z ^ 4 * w ^ 2 +
        6 * (76 / 3) * z ^ 5 * w + 32 * z ^ 6) +
      x * (4 * w ^ 5 + 5 * (67 / 5) * z * w ^ 4 + 10 * (321 / 10) * z ^ 2 * w ^ 3 +
        10 * (641 / 10) * z ^ 3 * w ^ 2 + 5 * (572 / 5) * z ^ 4 * w + 204 * z ^ 5) +
      x * y * (28 * w ^ 5 + 5 * (253 / 5) * z * w ^ 4 + 10 * (422 / 5) * z ^ 2 * w ^ 3 +
        10 * (648 / 5) * z ^ 3 * w ^ 2 + 5 * 184 * z ^ 4 * w + 256 * z ^ 5) +
      x * y ^ 2 * (18 * w ^ 5 + 5 * (136 / 5) * z * w ^ 4 + 10 * (391 / 10) * z ^ 2 * w ^ 3 +
        10 * (264 / 5) * z ^ 3 * w ^ 2 + 5 * (332 / 5) * z ^ 4 * w + 80 * z ^ 5) := by
  positivity

/-- The Bernstein form of `U` in `z, w` (`w = 1 - z`), the terms `x^i y^j` with `i ≥ 2`. -/
private theorem n4h_bern_U₁ (x y z w : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hw : 0 ≤ w) :
    0 ≤
      x ^ 2 * (20 * w ^ 4 + 4 * (89 / 2) * z * w ^ 3 + 6 * 83 * z ^ 2 * w ^ 2 +
        4 * (275 / 2) * z ^ 3 * w + 230 * z ^ 4) +
      x ^ 2 * y * (67 * w ^ 4 + 4 * (431 / 4) * z * w ^ 3 + 6 * (475 / 3) * z ^ 2 * w ^ 2 +
        4 * (423 / 2) * z ^ 3 * w + 272 * z ^ 4) +
      x ^ 2 * y ^ 2 * (32 * w ^ 4 + 4 * (181 / 4) * z * w ^ 3 + 6 * (119 / 2) * z ^ 2 * w ^ 2 +
        4 * (143 / 2) * z ^ 3 * w + 80 * z ^ 4) +
      x ^ 3 * (33 * w ^ 3 + 3 * 57 * z * w ^ 2 + 3 * (257 / 3) * z ^ 2 * w + 129 * z ^ 3) +
      x ^ 3 * y * (73 * w ^ 3 + 3 * (307 / 3) * z * w ^ 2 + 3 * (380 / 3) * z ^ 2 * w +
        144 * z ^ 3) +
      x ^ 3 * y ^ 2 * (28 * w ^ 3 + 3 * (107 / 3) * z * w ^ 2 + 3 * (121 / 3) * z ^ 2 * w +
        40 * z ^ 3) +
      x ^ 4 * (22 * w + 36 * z) +
      x ^ 4 * y * (37 * w ^ 2 + 2 * (83 / 2) * z * w + 38 * z ^ 2) +
      x ^ 4 * y ^ 2 * (12 * w ^ 2 + 2 * (25 / 2) * z * w + 10 * z ^ 2) +
      x ^ 5 * (5 * w + 4 * z) +
      x ^ 5 * y * (7 * w + 4 * z) +
      x ^ 5 * y ^ 2 * (2 * w + 1 * z) := by
  positivity

/-- inv.md §5: `τ_q = -Y' s (s - 1) N_Y + Y (Y' s - 1)(Y' s² - 1) ≥ 0` for `Y, Y' ≥ 2`,
`Y - 1 ≤ s ≤ Y` (the Bernstein certificate in `z ∈ [0, 1]`). -/
private theorem n4h_tq_nonneg {Y Y' s : ℝ} (ha : 0 ≤ Y - 2) (hb : 0 ≤ Y' - 2)
    (hs1 : Y - 1 ≤ s) (hs2 : s ≤ Y) :
    0 ≤ -Y' * s * (s - 1) * (Y' * s ^ 2 - 2 * s + Y) + Y * (Y' * s - 1) * (Y' * s ^ 2 - 1) := by
  obtain ⟨x, rfl⟩ : ∃ x, Y = 2 + x := ⟨Y - 2, by ring⟩
  obtain ⟨y, rfl⟩ : ∃ y, Y' = 2 + y := ⟨Y' - 2, by ring⟩
  obtain ⟨z, rfl⟩ : ∃ z, s = 1 + x + z := ⟨s - 1 - x, by ring⟩
  have := n4h_bern_tq x y z (1 - z) (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

/-- inv.md §5: `U = s (s + 1) T₀' + τ_f (s - 1) z - s τ_q z ≥ 0` for `Y, Y' ≥ 2`,
`Y - 1 ≤ s ≤ Y`, with `T₀' = s (YY' - Y - Y')(s - 1) N_Y - Y (Y' s - 1) φ(s)` and
`τ_f = Y' s² (Y' s - 2)(s - Y)` (the Bernstein certificate in `z ∈ [0, 1]`). -/
private theorem n4h_U_nonneg {Y Y' s : ℝ} (ha : 0 ≤ Y - 2) (hb : 0 ≤ Y' - 2)
    (hs1 : Y - 1 ≤ s) (hs2 : s ≤ Y) :
    0 ≤ s * (s + 1) * (s * (Y * Y' - Y - Y') * (s - 1) * (Y' * s ^ 2 - 2 * s + Y) -
        Y * (Y' * s - 1) * ((Y' - 1) * s ^ 3 - (2 * Y' + 1) * s ^ 2 + (2 * Y + 1) * s - (Y - 1))) +
      Y' * s ^ 2 * (Y' * s - 2) * (s - Y) * (s - 1) * (s - Y + 1) -
      s * (-Y' * s * (s - 1) * (Y' * s ^ 2 - 2 * s + Y) + Y * (Y' * s - 1) * (Y' * s ^ 2 - 1)) *
        (s - Y + 1) := by
  obtain ⟨x, rfl⟩ : ∃ x, Y = 2 + x := ⟨Y - 2, by ring⟩
  obtain ⟨y, rfl⟩ : ∃ y, Y' = 2 + y := ⟨Y' - 2, by ring⟩
  obtain ⟨z, rfl⟩ : ∃ z, s = 1 + x + z := ⟨s - 1 - x, by ring⟩
  have := n4h_bern_U₀ x y z (1 - z) (by linarith) (by linarith) (by linarith) (by linarith)
  have := n4h_bern_U₁ x y z (1 - z) (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

/-- inv.md Proposition 5 in the log-free form: `T_b = s Ψ(s) N_Y - Y (Y' s - 1) Φ(s) ≥ 0` (with
the definitions of `Ψ`, `Φ` unfolded) for `Y, Y' ≥ 2`, `1 < s`, `Y - 1 ≤ s ≤ Y`, `p ≥ 0` and the
two bounds `s (s + 1) f₀ ≤ (s - 1)² z`, `(s + 1)(-q) ≤ (s - 1) z` (`z = s - Y + 1`). By (5.3),
`s (s + 1) T_b - (s - 1) U = τ_f (s (s + 1) f₀ - (s - 1)² z) + s τ_q ((s + 1) q + (s - 1) z)
+ s (s + 1) τ_p p`, a polynomial identity (used by `linarith` after expansion), and every term on
the right is `≥ 0`. -/
private theorem n4h_Tb_core {Y Y' s f0 q p : ℝ} (ha : 0 ≤ Y - 2) (hb : 0 ≤ Y' - 2)
    (hs0 : 1 < s) (hs1 : Y - 1 ≤ s) (hs2 : s ≤ Y) (h4 : 0 ≤ p)
    (hb1 : s * (s + 1) * f0 ≤ (s - 1) ^ 2 * (s - Y + 1))
    (hb2 : (s + 1) * (-q) ≤ (s - 1) * (s - Y + 1)) :
    0 ≤ s * ((Y * (Y' - 1 + p) - Y') * s ^ 2 +
        (Y' * (1 + f0 - (Y - 1 + q)) + Y * (2 - Y' - p)) * s + (Y' * (Y - 1 + q) - Y)) *
        (Y' * s ^ 2 - 2 * s + Y) -
      Y * (Y' * s - 1) * ((Y' - 1 + p) * s ^ 4 - 3 * Y' * s ^ 3 +
        (Y' * (1 + f0 - (Y - 1 + q)) + Y * (2 - Y' - p) + 2 * Y * Y' + 2) * s ^ 2 - 3 * Y * s +
        (Y - 1 + q)) := by
  have htq := n4h_tq_nonneg ha hb hs1 hs2
  have hU := n4h_U_nonneg ha hb hs1 hs2
  have htf : Y' * s ^ 2 * (Y' * s - 2) * (s - Y) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg s))
      (by nlinarith)) (by linarith)
  have htp : 0 ≤ Y * s ^ 2 * (Y - s) * ((1 + Y') * s - 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg s)) (by linarith))
      (by nlinarith)
  have t1 := mul_nonneg_of_nonpos_of_nonpos htf
    (by linarith : s * (s + 1) * f0 - (s - 1) ^ 2 * (s - Y + 1) ≤ 0)
  have t2 := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ s) htq)
    (by linarith : (0:ℝ) ≤ (s + 1) * q + (s - 1) * (s - Y + 1))
  have t3 := mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ s * (s + 1)) htp) h4
  have t4 := mul_nonneg (by linarith : (0:ℝ) ≤ s - 1) hU
  have hss : 0 < s * (s + 1) := by positivity
  by_contra h
  push Not at h
  linarith [mul_neg_of_pos_of_neg hss h]

/-- `g(Y) ≥ 0` for `Y ≥ 16/5`, cleared of `1/Y`: `Y² log Y ≥ Y (Y - 1) + (Y - 1)²`. -/
private theorem n4h_g_nonneg {Y : ℝ} (hY : 16 / 5 ≤ Y) :
    Y * (Y - 1) + (Y - 1) ^ 2 ≤ Y ^ 2 * Real.log Y := by
  have hY0 : 0 < Y := by linarith
  have e : Real.log Y = Real.log (16 / 5) + Real.log (5 * Y / 16) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    ring
  have h1 := Real.one_sub_inv_le_log_of_pos (by positivity : (0:ℝ) < 5 * Y / 16)
  have h2 := log_sixteen_div_five_gt
  rw [inv_div] at h1
  have h3 : Y ^ 2 * (1 - 16 / (5 * Y)) = Y ^ 2 - 16 / 5 * Y := by field_simp
  have h4 : Y ^ 2 * (297 / 256 + (1 - 16 / (5 * Y))) ≤ Y ^ 2 * Real.log Y := by
    rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg Y)
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Y - 16 / 5)
    (by positivity : (0:ℝ) ≤ 41 / 256 * Y + 5 / 16)]

namespace ArcParams

variable (a : ArcParams)

/-- **inv.md Proposition 5** (the next arc never switches unless `Y_new < Y_*`). Let `Y - 2 ≥ 0`,
`Y' - 2 ≥ 0`, `f₀ ≥ 0 ≥ q`, `p ≥ 0`, `1 < s < Y`, `s ≥ Y - 1` and `F(log s) = 0` (`s` is the
switch). Then `f₀,new ≥ q_new (1 - 1/Y_new)`. Neither E nor the relation is used.

Route (inv.md §5; `x = Y - 2`, `y = Y' - 2`, `z = s - Y + 1 ∈ [0, 1]`):
1. **(5.1).** `N_Y > 0` (`N_Y ≥ 2s² - 2s + Y > 0`), `1 - 1/Y_new = s (Y' s - 1)/N_Y`, and
   `f₀,new - q_new (1 - 1/Y_new) = s T_b/(Y (Y - s)² N_Y)` with
   `T_b := s Ψ(s) N_Y - Y (Y' s - 1) Φ(s)`. So the claim is `T_b ≥ 0`.
2. **(5.2), (3.1), (5.3).** `Ψ(s) = (YY' - Y - Y')(s - 1)² + Y' s f₀ - Y'(s - 1) q + Y s (s - 1) p`,
   `Φ(s) = (s - 1) φ(s) + Y' s² f₀ - (Y' s² - 1) q + s² (s² - Y) p`, hence
   `T_b = T₀ + τ_f f₀ + τ_q q + τ_p p` with
   `τ_f = Y' s² (Y' s - 2)(s - Y) ≤ 0`, `τ_p = Y s² (Y - s)((1 + Y') s - 2) ≥ 0`,
   `τ_q = -Y' s (s - 1) N_Y + Y (Y' s - 1)(Y' s² - 1)`,
   `T₀ = s (YY' - Y - Y')(s - 1)² N_Y - Y (Y' s - 1)(s - 1) φ(s)`.
3. **The switching identity.** `F(log s) = -s + A + B/s + Y log s = f₀ + b_Y(s) - q (s - 1)/s`
   (`F_log`-style unfolding, `Real.exp_log`). With `log s ≥ 2(s - 1)/(s + 1)`
   (`two_mul_sub_one_div_add_one_le_log`) and the identity (5.4)
   `(s - 1) + (Y - 1)(s - 1)/s - 2Y(s - 1)/(s + 1) = (s - 1)² z/(s (s + 1))`:
   `f₀ + (-q)(s - 1)/s = -b_Y(s) ≤ (s - 1)² z/(s (s + 1))`, so
   `0 ≤ f₀ ≤ (s - 1)² z/(s (s + 1))` and `0 ≤ -q ≤ (s - 1) z/(s + 1)`.
4. With `τ_q ≥ 0` (step 5), `τ_f ≤ 0`, `τ_p p ≥ 0`:
   `T_b ≥ T₀ + τ_f (s - 1)² z/(s (s + 1)) - τ_q (s - 1) z/(s + 1) = (s - 1) U/(s (s + 1))`,
   `U := s (s + 1) T₀' + τ_f (s - 1) z - s τ_q z`, `T₀' := T₀/(s - 1)
   = s (YY' - Y - Y')(s - 1) N_Y - Y (Y' s - 1) φ(s)` (a polynomial).
5. **The Bernstein certificates of `τ_q ≥ 0` and `U ≥ 0`** for `x, y ≥ 0`, `z ∈ [0, 1]`. In
   `(x, y, z)` (`Y = 2 + x`, `Y' = 2 + y`, `s = 1 + x + z`) write
   `P = Σ_{i,j} x^i y^j Σ_{k=0}^{n} β^{ij}_k C(n, k) z^k (1 - z)^{n - k}` (`n` = list length - 1);
   every `β ≥ 0`, so `P ≥ 0` (`ring` for the expansion, then `positivity`). Lists
   `x^i y^j: [β₀, …, βₙ]`:
   `τ_q`: `x⁰y⁰ [2, 4, 8, 14, 18]`; `x⁰y¹ [4, 15/2, 13, 20, 24]`; `x⁰y² [2, 13/4, 5, 7, 8]`;
   `x¹y⁰ [9, 55/3, 91/3, 33]`; `x¹y¹ [16, 80/3, 116/3, 40]`; `x¹y² [6, 9, 12, 12]`;
   `x²y⁰ [16, 24, 20]`; `x²y¹ [20, 27, 22]`; `x²y² [6, 15/2, 6]`; `x³y⁰ [8, 4]`; `x³y¹ [8, 4]`;
   `x³y² [2, 1]`.
   `U`: `x⁰y⁰ [0, 1, 56/15, 48/5, 102/5, 116/3, 72]`;
   `x⁰y¹ [4, 25/3, 236/15, 273/10, 656/15, 196/3, 96]`;
   `x⁰y² [4, 19/3, 29/3, 141/10, 292/15, 76/3, 32]`; `x¹y⁰ [4, 67/5, 321/10, 641/10, 572/5, 204]`;
   `x¹y¹ [28, 253/5, 422/5, 648/5, 184, 256]`; `x¹y² [18, 136/5, 391/10, 264/5, 332/5, 80]`;
   `x²y⁰ [20, 89/2, 83, 275/2, 230]`; `x²y¹ [67, 431/4, 475/3, 423/2, 272]`;
   `x²y² [32, 181/4, 119/2, 143/2, 80]`; `x³y⁰ [33, 57, 257/3, 129]`;
   `x³y¹ [73, 307/3, 380/3, 144]`; `x³y² [28, 107/3, 121/3, 40]`; `x⁴y⁰ [22, 36]`;
   `x⁴y¹ [37, 83/2, 38]`; `x⁴y² [12, 25/2, 10]`; `x⁵y⁰ [5, 4]`; `x⁵y¹ [7, 4]`; `x⁵y² [2, 1]`.
6. `T_b ≥ (s - 1) U/(s (s + 1)) ≥ 0` (`s > 1`), and step 1.
Margin (numerical): `U ≥ 4.1 (x + y + z)` on `x ∈ [0, 3]`; at the cusp `s → Y`,
`T_b(Y) = Y (YY' - 1)² B`. -/
theorem qNew_le_f0New (ha : 0 ≤ a.Y - 2) (hb : 0 ≤ a.Y' - 2) (h1 : 0 ≤ a.f0) (h2 : a.q ≤ 0)
    (h4 : 0 ≤ a.p) {s : ℝ} (hs0 : 1 < s) (hs1 : a.Y - 1 ≤ s) (hs2 : s < a.Y)
    (hFs : a.F (Real.log s) = 0) : a.qNew s * (1 - 1 / a.YNew s) ≤ a.f0New s := by
  have hs : 0 < s := by linarith
  have hY0 : 0 < a.Y := by linarith
  have hYs : 0 < a.Y - s := by linarith
  have hN : 0 < a.Y' * s ^ 2 - 2 * s + a.Y := by nlinarith
  -- step 3, the switching identity: `F(log s) = 0` reads
  -- `s f₀ - (s - 1) q = (s - 1)(s + Y - 1) - Y s log s`
  have hF : s * a.f0 - (s - 1) * a.q = (s - 1) * (s + a.Y - 1) - a.Y * s * Real.log s := by
    unfold F f at hFs
    rw [Real.exp_log hs, show -2 * Real.log s = -(2 * Real.log s) by ring, Real.exp_neg,
      Real.exp_neg, show 2 * Real.log s = Real.log s + Real.log s by ring, Real.exp_add,
      Real.exp_log hs] at hFs
    unfold A B at hFs
    field_simp at hFs
    linear_combination hFs
  have hlog := two_mul_sub_one_div_add_one_le_log hs0.le
  have hlog' : 2 * (s - 1) ≤ (s + 1) * Real.log s := by
    rw [div_le_iff₀ (by linarith)] at hlog; linarith
  -- `s (s + 1) f₀ + (s + 1)(s - 1)(-q) ≤ (s - 1)² z` (inv.md (5.4))
  have hb0 : s * (s + 1) * a.f0 + (s + 1) * (s - 1) * (-a.q) ≤
      (s - 1) ^ 2 * (s - a.Y + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog' (by positivity : (0:ℝ) ≤ a.Y * s)]
  have hq0 : 0 ≤ (s + 1) * (s - 1) * (-a.q) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hf0 : 0 ≤ s * (s + 1) * a.f0 := mul_nonneg (by positivity) h1
  have hb1 : s * (s + 1) * a.f0 ≤ (s - 1) ^ 2 * (s - a.Y + 1) := by linarith
  have hb2 : (s + 1) * (-a.q) ≤ (s - 1) * (s - a.Y + 1) := by
    have h' : (s - 1) * ((s + 1) * (-a.q)) ≤ (s - 1) * ((s - 1) * (s - a.Y + 1)) := by
      linarith
    exact le_of_mul_le_mul_left h' (by linarith)
  have hT : 0 ≤ s * a.Psi s * (a.Y' * s ^ 2 - 2 * s + a.Y) - a.Y * (a.Y' * s - 1) * a.Phi s :=
    n4h_Tb_core ha hb hs0 hs1 hs2.le h4 hb1 hb2
  have e : a.f0New s - a.qNew s * (1 - 1 / a.YNew s) =
      s * (s * a.Psi s * (a.Y' * s ^ 2 - 2 * s + a.Y) - a.Y * (a.Y' * s - 1) * a.Phi s) /
        (a.Y * (a.Y - s) ^ 2 * (a.Y' * s ^ 2 - 2 * s + a.Y)) := by
    unfold f0New qNew YNew
    set N := a.Y' * s ^ 2 - 2 * s + a.Y with hNdef
    have hN' : N ≠ 0 := hN.ne'
    have hYs' : a.Y - s ≠ 0 := hYs.ne'
    field_simp
    ring
  have : 0 ≤ s * (s * a.Psi s * (a.Y' * s ^ 2 - 2 * s + a.Y) - a.Y * (a.Y' * s - 1) * a.Phi s) /
        (a.Y * (a.Y - s) ^ 2 * (a.Y' * s ^ 2 - 2 * s + a.Y)) :=
    div_nonneg (mul_nonneg hs.le hT) (by positivity)
  linarith

/-- **inv.md Lemma 6, the parameter part** (the exit criterion). If `Y ≥ 16/5`, `f₀ > 0` and
`f₀ ≥ q (1 - 1/Y)` (no sign condition on `q`), then `f > 0` on `[0, log Y)`: the arc does not
switch before it leaves the star domain.

Route (inv.md §6): for `τ ∈ [0, log Y)` put `y = e^{τ} ∈ [1, Y)`; `f(τ) = e^{-τ} F(τ)` and
`F(τ) = f₀ + b_Y(y) - q (y - 1)/y` ((1.1), `Real.log_exp`), so it suffices that this is `> 0`.
1. `g(Y) := b_Y(Y) = Y log Y - (Y - 1) - (Y - 1)²/Y ≥ 0` for `Y ≥ 16/5`:
   `g(Y) = Y h(Y)`, `h(Y) = log Y - (Y - 1)(2Y - 1)/Y²`, `h'(Y) = (Y - 1)(Y - 2)/Y³ > 0` for
   `Y > 2`, and `h(16/5) = log(16/5) - 297/256 > 0` (`log_sixteen_div_five_gt`). (inv.md argues
   with `g'(Y) = log Y - 1 + 1/Y² > 0`; either works.)
2. `b_Y'(y) = -(y - 1)(y - (Y - 1))/y²` and `b_Y(1) = 0`: `b_Y` increases on `[1, Y - 1]` and
   decreases on `[Y - 1, Y]`, so `b_Y ≥ min(b_Y(1), b_Y(Y)) = min(0, g(Y)) = 0` on `[1, Y]`.

In Lean, the monotonicity arguments of steps 1–2 are replaced by three inequalities for `log`, with
the same conclusions (`g(Y) ≥ 0`, `b_Y ≥ 0` on `[1, Y]`):
* step 1: `log Y = log(16/5) + log(5Y/16)` and `log t ≥ 1 - 1/t` give
  `Y² log Y - Y(Y - 1) - (Y - 1)² ≥ (Y - 16/5)((41/256) Y + 5/16) ≥ 0`;
* step 2 on `[1, Y - 1]`: `log y ≥ 2(y - 1)/(y + 1)` (`two_mul_sub_one_div_add_one_le_log`)
  gives `(y + 1) y b_Y(y) ≥ (y - 1)²(Y - 1 - y) ≥ 0`;
* step 2 on `[Y - 1, Y]`: `log t ≤ sinh(log t) = (t - 1/t)/2` at `t = Y/y ≥ 1`
  (`Real.self_le_sinh_iff`, `Real.sinh_log`) gives
  `2Y y b_Y(y) ≥ 2Y y g(Y) + (Y - y)(Y y - Y² + 2Y - 2)`, and `Y y - Y² + 2Y - 2 ≥ Y - 2 > 0`.
3. If `q ≤ 0`: `F(τ) ≥ f₀ - q (y - 1)/y ≥ f₀ > 0`. If `q > 0`: `(y - 1)/y = 1 - 1/y < 1 - 1/Y`, so
   `F(τ) ≥ f₀ - q (y - 1)/y > f₀ - q (1 - 1/Y) ≥ 0`. -/
theorem f_pos_of_Y_ge (hY : 16 / 5 ≤ a.Y) (h1 : 0 < a.f0) (hq : a.q * (1 - 1 / a.Y) ≤ a.f0)
    {τ : ℝ} (hτ : τ ∈ Ico 0 (Real.log a.Y)) : 0 < a.f τ := by
  obtain ⟨hτ0, hτY⟩ := hτ
  have hY0 : 0 < a.Y := by linarith
  set y := Real.exp τ with hydef
  have hy1 : 1 ≤ y := Real.one_le_exp hτ0
  have hyY : y < a.Y := by rw [← Real.exp_log hY0]; exact Real.exp_lt_exp.2 hτY
  have hy0 : 0 < y := by positivity
  have hτlog : Real.log y = τ := Real.log_exp τ
  -- `f(τ) = (f₀ + b_Y(y) - q (y - 1)/y)/y`, `b_Y(y) = Y τ - (y - 1) - (Y - 1)(y - 1)/y` ((1.1))
  have e : a.f τ = (a.f0 + (a.Y * τ * y - (y - 1) * y - (a.Y - 1) * (y - 1)) / y -
      a.q * (y - 1) / y) / y := by
    unfold f A B
    rw [Real.exp_neg, show -2 * τ = -(2 * τ) by ring, Real.exp_neg, two_mul, Real.exp_add]
    field_simp
    ring
  -- `b_Y ≥ 0` on `[1, Y]`
  have hb : 0 ≤ a.Y * τ * y - (y - 1) * y - (a.Y - 1) * (y - 1) := by
    rcases le_total y (a.Y - 1) with hyl | hyl
    · -- on `[1, Y - 1]`: `log y ≥ 2(y - 1)/(y + 1)`, and
      -- `(y + 1) b ≥ 2Y y (y - 1) - (y - 1)(y + 1)(y + Y - 1) = (y - 1)²(Y - 1 - y)`
      have hl := two_mul_sub_one_div_add_one_le_log hy1
      rw [hτlog, div_le_iff₀ (by linarith)] at hl
      have : 0 ≤ (y - 1) ^ 2 * (a.Y - 1 - y) := mul_nonneg (sq_nonneg _) (by linarith)
      have h' : 0 ≤ (y + 1) * (a.Y * τ * y - (y - 1) * y - (a.Y - 1) * (y - 1)) := by
        nlinarith [mul_le_mul_of_nonneg_left hl (by positivity : (0:ℝ) ≤ a.Y * y)]
      exact nonneg_of_mul_nonneg_right h' (by linarith)
    · -- on `[Y - 1, Y]`: compare with `g(Y) ≥ 0`, using `log t ≤ (t - 1/t)/2` at `t = Y/y ≥ 1`
      have ht : 1 ≤ a.Y / y := by rw [le_div_iff₀ hy0]; linarith
      have hsinh := Real.self_le_sinh_iff.2 (Real.log_nonneg ht)
      rw [Real.sinh_log (by linarith)] at hsinh
      have hlt : Real.log (a.Y / y) = Real.log a.Y - τ := by
        rw [Real.log_div hY0.ne' hy0.ne', hτlog]
      rw [hlt] at hsinh
      have hs' : 2 * a.Y * y * (Real.log a.Y - τ) ≤ a.Y ^ 2 - y ^ 2 := by
        have : (a.Y / y - (a.Y / y)⁻¹) / 2 * (2 * a.Y * y) = a.Y ^ 2 - y ^ 2 := by
          field_simp
        nlinarith [mul_le_mul_of_nonneg_right hsinh (by positivity : (0:ℝ) ≤ 2 * a.Y * y)]
      have hg := n4h_g_nonneg hY
      have hP : 0 ≤ (a.Y - y) * (a.Y * y - a.Y ^ 2 + 2 * a.Y - 2) :=
        mul_nonneg (by linarith) (by nlinarith)
      -- `2Y b ≥ 2y (Y² log Y - Y(Y - 1) - (Y - 1)²) + (Y - y)(Y y - Y² + 2Y - 2)`
      have h' : 0 ≤ 2 * a.Y * (a.Y * τ * y - (y - 1) * y - (a.Y - 1) * (y - 1)) := by
        nlinarith [mul_le_mul_of_nonneg_left hg (by positivity : (0:ℝ) ≤ 2 * y)]
      exact nonneg_of_mul_nonneg_right h' (by linarith)
  rw [e]
  apply div_pos _ hy0
  rcases le_or_gt a.q 0 with hq0 | hq0
  · have : 0 ≤ -a.q * (y - 1) / y := div_nonneg (mul_nonneg (by linarith) (by linarith)) hy0.le
    have : 0 ≤ (a.Y * τ * y - (y - 1) * y - (a.Y - 1) * (y - 1)) / y := div_nonneg hb hy0.le
    have e2 : -a.q * (y - 1) / y = -(a.q * (y - 1) / y) := by ring
    linarith
  · -- `(y - 1)/y = 1 - 1/y < 1 - 1/Y`
    have hlt : a.q * (y - 1) / y < a.q * (1 - 1 / a.Y) := by
      rw [mul_div_assoc]
      apply mul_lt_mul_of_pos_left _ hq0
      rw [div_lt_iff₀ hy0]
      have : 1 / a.Y * y < 1 := by rw [div_mul_eq_mul_div, one_mul, div_lt_one hY0]; exact hyY
      nlinarith
    have : 0 ≤ (a.Y * τ * y - (y - 1) * y - (a.Y - 1) * (y - 1)) / y := div_nonneg hb hy0.le
    linarith

end ArcParams

end SmoothedPolygons
