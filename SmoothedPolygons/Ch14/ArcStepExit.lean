module

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
  sorry

/-- **`log(16/5) > 297/256`** (inv.md Lemma 6: `g(16/5) > 0`, i.e.
`log(16/5) > (Y - 1)(2Y - 1)/Y²` at `Y = 16/5`, which is `297/256 = 1.16016`).

Route: `Real.hasSum_log_one_add_inv` with `a = 5/11` (`1 + a⁻¹ = 16/5`, `1/(2a + 1) = 11/21`;
this is `log(16/5) = 2 atanh(11/21)`); the terms are nonnegative, so the partial sum of the first
four, `2 (x + x³/3 + x⁵/5 + x⁷/7)` at `x = 11/21`, which is `73269045344/63038098935 = 1.16230`,
is a lower bound (`sum_le_hasSum (Finset.range 4)`, then `norm_num [Finset.sum_range_succ]`).
The true value is `1.16315`. -/
theorem log_sixteen_div_five_gt : 297 / 256 < Real.log (16 / 5) := by
  sorry

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
  sorry

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
3. If `q ≤ 0`: `F(τ) ≥ f₀ - q (y - 1)/y ≥ f₀ > 0`. If `q > 0`: `(y - 1)/y = 1 - 1/y < 1 - 1/Y`, so
   `F(τ) ≥ f₀ - q (y - 1)/y > f₀ - q (1 - 1/Y) ≥ 0`. -/
theorem f_pos_of_Y_ge (hY : 16 / 5 ≤ a.Y) (h1 : 0 < a.f0) (hq : a.q * (1 - 1 / a.Y) ≤ a.f0)
    {τ : ℝ} (hτ : τ ∈ Ico 0 (Real.log a.Y)) : 0 < a.f τ := by
  sorry

end ArcParams

end SmoothedPolygons
