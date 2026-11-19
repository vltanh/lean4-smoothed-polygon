module

public import SmoothedPolygons.Ch14.ArcStepClosed

/-!
# Chapter 14, the unstable curve: one step from the region `𝒢*` (§6 of the note)

Part of the formalization's proof, without computer assistance, of the fact behind Figure 14.2
(`UnstableCurveLeavesStarDomain`, `SmoothedPolygons/Ch14/UnstableCurve.lean`). **Departure from
the paper**, by the user's decision: the book reads the fact off a computed figure (Figure 14.2,
TeX 11951–11991; REPORT.md E88). The proof is written up in `docs/unstable-curve.pdf` (the
note); this file holds the real-number lemmas of its §6, statements about real numbers only (no
flows). With `s = e^{τ_sw}` the switch of a point of `𝒢*` and `F(q)` the next point:

* **Lemma 6.1** (`q_nonpos_of_relT`, `f0_ge_of_relT`): the relation `R̃ = 0` (`relT`, Proposition
  3.1 of the note) is a sign test. At a section point with `Y ≥ 2`, `Y' > 2`, `f₀ ≥ 0`, `p ≥ 0`
  and `2p < (2Y' - 1)(Y' - 2)`, (i) `(Y - 2)(Y' - 2) ≤ 3` forces `q ≤ 0`, and (ii)
  `f₀ ≥ q (1 - 1/Y)` always.
* **Lemma 6.2** (`pNew_lt`, `two_lt_YNew`): `p` is small at the next point,
  `2p_new < (2Y'_new - 1)(Y'_new - 2)`, and `Y_new > 2`; so Lemma 6.1 applies at `F(q)`.
* **Lemma 6.3** (`YNew_ge`, with `E_new_iff`): if `ψ(s) < 0`, i.e. the expansion condition fails at
  `F(q)`, then `Y_new ≥ 16/5`.

The three are assembled in `arcRegionInvariant_sharp`
(`SmoothedPolygons/Ch14/ArcRegionInvariant.lean`, Theorem 6.5 of the note); Lemma 6.4 (the exit
criterion) is `arcLeavesStarDomain_of_Y_ge` (`SmoothedPolygons/Ch14/ArcConditions.lean`).

## Notation

As in `SmoothedPolygons/Ch14/ArcStepClosed.lean`: `a : ArcParams`, `Y' = (1 + ε²)/(ε² Y)`,
`B = Y - 1 + q`, `p_new = (s² - Y s + B)/(Y - s)²` (`pNew`), `Y'_new = Y/(Y - s)` (`YNew'`),
`Y_new = (Y' s² - 2s + Y)/(Y - s)` (`YNew`), `ψ(s) = -3Y' s³ + (2YY' + 2) s² - Y²` (`psiE`).
Every identity below is a polynomial identity (`ring` or `linear_combination`).
-/

@[expose] public section

namespace SmoothedPolygons

/-! ### Lemma 6.1 on real numbers -/

/-- **Lemma 6.1 on real numbers** (the relation as a sign test). Let `W` stand for `Y'`, and let
`R̃ = (W(f₀ - q) - Y p)² - 4pq + 2(YW - 1)((W - 2) q + (Y - 2) p) + 2W(3 - (Y - 2)(W - 2)) f₀ = 0`.
If `Y ≥ 2`, `W > 2`, `f₀ ≥ 0`, `p ≥ 0` and `2p < (2W - 1)(W - 2)`, then
(i) `(Y - 2)(W - 2) ≤ 3` implies `q ≤ 0`, and (ii) `q (1 - 1/Y) ≤ f₀`.

Route (the note, Lemma 6.1). Write `a = Y - 2`, `b = W - 2`, `M = (YW - 1) b - 2p`.
1. `M > 0`: `(YW - 1) b - (2W - 1) b = (Y - 2) W b ≥ 0`, and `(2W - 1) b > 2p`.
2. `R̃ = 0` rearranged: `2W(ab - 3) f₀ = 2qM + (W(f₀ - q) - Yp)² + 2(YW - 1) a p`.
3. If `q > 0`, the right side is `> 0`, so `ab > 3` (this is (i)) and `W(ab - 3) f₀ ≥ qM`. Then
   `W(ab - 3)(Y f₀ - (Y - 1) q) ≥ q D` with
   `D = Y M - W(Y - 1)(ab - 3) = Y((2W - 1) b - 2p) + abW + 3W(Y - 1) > 0`, so
   `(Y - 1) q ≤ Y f₀`, which is (ii). If `q ≤ 0`, (ii) is clear. -/
private theorem relation_sign_test {Y W f0 q p : ℝ}
    (hR : (W * (f0 - q) - Y * p) ^ 2 - 4 * p * q +
      2 * (Y * W - 1) * ((W - 2) * q + (Y - 2) * p) + 2 * W * (3 - (Y - 2) * (W - 2)) * f0 = 0)
    (hY : 2 ≤ Y) (hW : 2 < W) (h1 : 0 ≤ f0) (h4 : 0 ≤ p) (hp : 2 * p < (2 * W - 1) * (W - 2)) :
    ((Y - 2) * (W - 2) ≤ 3 → q ≤ 0) ∧ q * (1 - 1 / Y) ≤ f0 := by
  have hWb : 0 ≤ W * (W - 2) := mul_nonneg (by linarith) (by linarith)
  -- step 1: `M = (YW - 1)(W - 2) - 2p > 0`
  have hM : 0 < (Y * W - 1) * (W - 2) - 2 * p := by
    nlinarith [mul_nonneg (sub_nonneg.2 hY) hWb]
  -- step 2: the relation rearranged
  have key : 2 * W * ((Y - 2) * (W - 2) - 3) * f0 =
      2 * q * ((Y * W - 1) * (W - 2) - 2 * p) + (W * (f0 - q) - Y * p) ^ 2 +
        2 * (Y * W - 1) * (Y - 2) * p := by
    linear_combination (-1 : ℝ) * hR
  have hYW : 0 ≤ Y * W - 1 := by nlinarith
  have hS := sq_nonneg (W * (f0 - q) - Y * p)
  have hA : 0 ≤ 2 * (Y * W - 1) * (Y - 2) * p :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hYW) (sub_nonneg.2 hY)) h4
  -- step 3: a positive `q` forces `W (ab - 3) f₀ ≥ q M > 0`
  have hk : ∀ _ : 0 < q, q * ((Y * W - 1) * (W - 2) - 2 * p) ≤
      W * ((Y - 2) * (W - 2) - 3) * f0 := fun _ ↦ by nlinarith
  have hpos : ∀ _ : 0 < q, 0 < (Y - 2) * (W - 2) - 3 := by
    intro hq
    have h0 : 0 < W * ((Y - 2) * (W - 2) - 3) * f0 := lt_of_lt_of_le (mul_pos hq hM) (hk hq)
    by_contra h
    push Not at h
    have : W * ((Y - 2) * (W - 2) - 3) * f0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) h1
    linarith
  refine ⟨fun hab ↦ ?_, ?_⟩
  · by_contra hq
    push Not at hq
    linarith [hpos hq]
  · have hY0 : 0 < Y := by linarith
    have e : q * (1 - 1 / Y) = q * (Y - 1) / Y := by field_simp
    rw [e, div_le_iff₀ hY0]
    rcases le_or_gt q 0 with hq | hq
    · nlinarith
    · have hab := hpos hq
      have hD : 0 < Y * ((Y * W - 1) * (W - 2) - 2 * p) -
          W * (Y - 1) * ((Y - 2) * (W - 2) - 3) := by
        have e2 : Y * ((Y * W - 1) * (W - 2) - 2 * p) - W * (Y - 1) * ((Y - 2) * (W - 2) - 3) =
            Y * ((2 * W - 1) * (W - 2) - 2 * p) + (Y - 2) * (W - 2) * W + 3 * W * (Y - 1) := by
          ring
        rw [e2]
        have : 0 < Y * ((2 * W - 1) * (W - 2) - 2 * p) := mul_pos hY0 (by linarith)
        have : 0 ≤ (Y - 2) * (W - 2) * W :=
          mul_nonneg (mul_nonneg (sub_nonneg.2 hY) (by linarith)) (by linarith)
        have : 0 < 3 * W * (Y - 1) := mul_pos (by linarith) (by linarith)
        linarith
      have hYk := mul_le_mul_of_nonneg_left (hk hq) hY0.le
      have h3 : 0 < W * ((Y - 2) * (W - 2) - 3) * (Y * f0 - q * (Y - 1)) := by
        nlinarith [mul_pos hq hD]
      have h4' : 0 < Y * f0 - q * (Y - 1) :=
        pos_of_mul_pos_right h3 (mul_pos (by linarith) hab).le
      linarith

/-! ### Lemma 6.3 on real numbers -/

/-- A cubic `-3Y' t³ + C t² - K` with `Y' > 0` increases and then decreases on `(0, ∞)`, so on
`[u, v] ⊂ (0, ∞)` it is at least the smaller of its values at the ends. -/
private theorem cubic_nonneg_between {Y' C K u s v : ℝ} (hY' : 0 < Y') (hu : 0 < u) (hus : u ≤ s)
    (hsv : s ≤ v) (h1 : 0 ≤ -3 * Y' * u ^ 3 + C * u ^ 2 - K)
    (h2 : 0 ≤ -3 * Y' * v ^ 3 + C * v ^ 2 - K) : 0 ≤ -3 * Y' * s ^ 3 + C * s ^ 2 - K := by
  by_cases hc : 3 * Y' * (s ^ 2 + s * u + u ^ 2) ≤ C * (s + u)
  · have e : (-3 * Y' * s ^ 3 + C * s ^ 2 - K) - (-3 * Y' * u ^ 3 + C * u ^ 2 - K) =
        (s - u) * (C * (s + u) - 3 * Y' * (s ^ 2 + s * u + u ^ 2)) := by ring
    have := mul_nonneg (sub_nonneg.2 hus) (sub_nonneg.2 hc)
    linarith
  · push Not at hc
    have hsu : 0 < s + u := by linarith
    have hm : 0 < 3 * Y' * (s + u + v) - C := by
      have e : (s + u) * (3 * Y' * (s + u + v) - C) =
          (3 * Y' * (s ^ 2 + s * u + u ^ 2) - C * (s + u)) + 3 * Y' * (s * u + (s + u) * v) := by
        ring
      have : 0 ≤ 3 * Y' * (s * u + (s + u) * v) := by
        have : 0 ≤ s * u + (s + u) * v := by
          have : 0 ≤ s := by linarith
          have : 0 ≤ v := by linarith
          positivity
        positivity
      have h0 : 0 < (s + u) * (3 * Y' * (s + u + v) - C) := by linarith
      exact pos_of_mul_pos_right h0 hsu.le
    have hg : 0 ≤ 3 * Y' * (s ^ 2 + s * v + v ^ 2) - C * (s + v) := by
      have e : 3 * Y' * (s ^ 2 + s * v + v ^ 2) - C * (s + v) =
          (3 * Y' * (s ^ 2 + s * u + u ^ 2) - C * (s + u)) +
            (v - u) * (3 * Y' * (s + u + v) - C) := by ring
      have := mul_nonneg (by linarith : (0:ℝ) ≤ v - u) hm.le
      linarith
    have e : (-3 * Y' * s ^ 3 + C * s ^ 2 - K) - (-3 * Y' * v ^ 3 + C * v ^ 2 - K) =
        (v - s) * (3 * Y' * (s ^ 2 + s * v + v ^ 2) - C * (s + v)) := by ring
    have := mul_nonneg (sub_nonneg.2 hsv) hg
    linarith

/-- Lemma 6.3 of the note on real numbers. -/
private theorem YNew_ge_unfolded {Y Y' s : ℝ} (hY : 2 < Y) (hY' : 2 < Y') (hs1 : Y - 1 ≤ s)
    (hs2 : s < Y)
    (hpsi : -3 * Y' * s ^ 3 + (2 * Y * Y' + 2) * s ^ 2 - Y ^ 2 < 0) :
    16 / 5 ≤ (Y' * s ^ 2 - 2 * s + Y) / (Y - s) := by
  have hYs : 0 < Y - s := by linarith
  rw [le_div_iff₀ hYs]
  by_contra hlt
  push Not at hlt
  -- `χ(s) = Y' s² + (6/5) s - (11/5) Y < 0`
  set χ : ℝ → ℝ := fun t => Y' * t ^ 2 + 6 / 5 * t - 11 / 5 * Y with hχ
  have hχs : χ s < 0 := by simp only [hχ]; linarith
  have hχY : 0 < χ Y := by
    simp only [hχ]
    nlinarith
  have hχmono : ∀ u v, 0 ≤ u → u ≤ v → χ u ≤ χ v := by
    intro u v hu huv
    simp only [hχ]
    have e : (Y' * v ^ 2 + 6 / 5 * v - 11 / 5 * Y) - (Y' * u ^ 2 + 6 / 5 * u - 11 / 5 * Y) =
        (v - u) * (Y' * (u + v) + 6 / 5) := by ring
    have : 0 ≤ (v - u) * (Y' * (u + v) + 6 / 5) :=
      mul_nonneg (by linarith) (by nlinarith)
    linarith
  -- the root `t ∈ [s, Y]` of `χ`
  obtain ⟨t, ⟨hst, htY⟩, hχt⟩ : ∃ t ∈ Set.Icc s Y, χ t = 0 := by
    have hc : ContinuousOn χ (Set.Icc s Y) := by
      simp only [hχ]; fun_prop
    exact intermediate_value_Icc hs2.le hc ⟨hχs.le, hχY.le⟩
  -- `t ≤ (17/28) Y`, since `χ((17/28) Y) = Y((289/784) Y Y' - 103/70) > 0`
  have ht17 : t ≤ 17 / 28 * Y := by
    by_contra h
    push Not at h
    have h17 : 0 < χ (17 / 28 * Y) := by
      simp only [hχ]
      have : 4 < Y * Y' := by nlinarith
      nlinarith
    have := hχmono (17 / 28 * Y) t (by positivity) h.le
    linarith
  -- `ψ(t) = (2Y - 3t) χ(t) + (1/5)(28t - 17Y)(t - Y) ≥ 0`
  have hψt : 0 ≤ -3 * Y' * t ^ 3 + (2 * Y * Y' + 2) * t ^ 2 - Y ^ 2 := by
    have e : -3 * Y' * t ^ 3 + (2 * Y * Y' + 2) * t ^ 2 - Y ^ 2 =
        (2 * Y - 3 * t) * χ t + 1 / 5 * ((17 * Y - 28 * t) * (Y - t)) := by
      simp only [hχ]; ring
    rw [e, hχt, mul_zero, zero_add]
    have : 0 ≤ (17 * Y - 28 * t) * (Y - t) := mul_nonneg (by linarith) (by linarith)
    linarith
  -- `ψ(Y - 1) > 0`: `χ(Y - 1) < 0` forces `Y - 2 < 1/3`
  have hψ1 : 0 ≤ -3 * Y' * (Y - 1) ^ 3 + (2 * Y * Y' + 2) * (Y - 1) ^ 2 - Y ^ 2 := by
    have hχ1 : χ (Y - 1) < 0 := lt_of_le_of_lt (hχmono (Y - 1) s (by linarith) hs1) hχs
    simp only [hχ] at hχ1
    have hx3 : Y - 2 < 1 / 3 := by
      by_contra h
      push Not at h
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Y' - 2) (sq_nonneg (Y - 1))]
    have e : -3 * Y' * (Y - 1) ^ 3 + (2 * Y * Y' + 2) * (Y - 1) ^ 2 - Y ^ 2 =
        (Y - 2) * (2 - (Y - 2) - 2 * (Y - 2) ^ 2) + (Y' - 2) * (Y - 1) ^ 2 * (1 - (Y - 2)) := by
      ring
    rw [e]
    have : 0 ≤ (Y - 2) * (2 - (Y - 2) - 2 * (Y - 2) ^ 2) :=
      mul_nonneg (by linarith) (by nlinarith)
    have : 0 ≤ (Y' - 2) * (Y - 1) ^ 2 * (1 - (Y - 2)) :=
      mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith)
    linarith
  have := cubic_nonneg_between (by linarith : (0:ℝ) < Y') (by linarith : (0:ℝ) < Y - 1) hs1 hst
    hψ1 hψt
  linarith


namespace ArcParams

variable (a : ArcParams)

/-- **Lemma 6.1 (i)** of the note (the relation as a sign test). At parameters with `R̃ = 0`
(`relT`; at a section point, `arcParams_rel` and `rel_eq`), `Y ≥ 2`, `Y' > 2`, `f₀ ≥ 0`,
`p ≥ 0`, `2p < (2Y' - 1)(Y' - 2)` and `(Y - 2)(Y' - 2) ≤ 3`: `q ≤ 0`. With `p` small, the relation
leaves no room for `q > 0`. See `relation_sign_test` for the route. -/
theorem q_nonpos_of_relT (hR : a.relT = 0) (hY : 2 ≤ a.Y) (hY' : 2 < a.Y') (h1 : 0 ≤ a.f0)
    (h4 : 0 ≤ a.p) (hp : 2 * a.p < (2 * a.Y' - 1) * (a.Y' - 2))
    (hab : (a.Y - 2) * (a.Y' - 2) ≤ 3) : a.q ≤ 0 :=
  (relation_sign_test (by unfold relT at hR; linear_combination hR) hY hY' h1 h4 hp).1 hab

/-- **Lemma 6.1 (ii)** of the note: under the hypotheses of `q_nonpos_of_relT` except
`(Y - 2)(Y' - 2) ≤ 3`, `f₀ ≥ q (1 - 1/Y)`, the hypothesis of the exit criterion (Lemma 6.4,
`arcLeavesStarDomain_of_Y_ge`). -/
theorem f0_ge_of_relT (hR : a.relT = 0) (hY : 2 ≤ a.Y) (hY' : 2 < a.Y') (h1 : 0 ≤ a.f0)
    (h4 : 0 ≤ a.p) (hp : 2 * a.p < (2 * a.Y' - 1) * (a.Y' - 2)) :
    a.q * (1 - 1 / a.Y) ≤ a.f0 :=
  (relation_sign_test (by unfold relT at hR; linear_combination hR) hY hY' h1 h4 hp).2

/-- **Lemma 6.2** of the note (`p` is small at the next point). If `q ≤ 0`, `s > 1` and
`Y - 1 ≤ s < Y`, then `2 p_new < (2Y'_new - 1)(Y'_new - 2)`.

Route. `2Y'_new - 1 = (Y + s)/(Y - s)` and `Y'_new - 2 = (2s - Y)/(Y - s)`. With
`c = s - Y + 1 ∈ [0, 1)`, the numerator of `p_new` is `s² - Y s + B = q + (s - 1) c ≤ (s - 1) c`
(as `q ≤ 0`), and
`2(s - 1) c ≤ 2(2s - Y) c < (2s - Y)(Y + s)`, because `s - 1 ≤ 2s - Y`, `2c < Y + s` and
`2s - Y > 0`. Divide by `(Y - s)²`. -/
theorem pNew_lt (h2 : a.q ≤ 0) {s : ℝ} (hs1 : 1 < s) (hsY1 : a.Y - 1 ≤ s)
    (hsY : s < a.Y) : 2 * a.pNew s < (2 * a.YNew' s - 1) * (a.YNew' s - 2) := by
  have hd : 0 < a.Y - s := by linarith
  have hd2 : 0 < (a.Y - s) ^ 2 := by positivity
  have e1 : 2 * a.pNew s = 2 * (s ^ 2 - a.Y * s + a.B) / (a.Y - s) ^ 2 := by
    unfold pNew; ring
  have e2 : (2 * a.YNew' s - 1) * (a.YNew' s - 2) =
      (a.Y + s) * (2 * s - a.Y) / (a.Y - s) ^ 2 := by
    unfold YNew'
    field_simp
    ring
  rw [e1, e2, div_lt_div_iff_of_pos_right hd2]
  have hc0 : 0 ≤ s - a.Y + 1 := by linarith
  have hpos : 0 < (2 * s - a.Y) * (a.Y + s - 2 * (s - a.Y + 1)) :=
    mul_pos (by linarith) (by linarith)
  unfold B
  nlinarith [mul_nonneg hc0 hc0]

/-- **Lemma 6.2**, second part: `Y_new > 2`. If `Y ≥ 2`, `Y' > 2`, `s > 1` and `Y - 1 ≤ s < Y`, then
`Y_new - 2 = (Y' s² - Y)/(Y - s) > 0`, since `Y' s² > 2s² ≥ 2(Y - 1)² ≥ Y`
(`2(Y - 1)² - Y = (2Y - 1)(Y - 2)`). -/
theorem two_lt_YNew (hY : 2 ≤ a.Y) (hY' : 2 < a.Y') {s : ℝ} (hs1 : 1 < s) (hsY1 : a.Y - 1 ≤ s)
    (hsY : s < a.Y) : 2 < a.YNew s := by
  have hd : 0 < a.Y - s := by linarith
  unfold YNew
  rw [lt_div_iff₀ hd]
  have hss : (a.Y - 1) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by linarith) hsY1 2
  have hs2 : 0 < s ^ 2 := by positivity
  nlinarith [mul_lt_mul_of_pos_right hY' hs2, mul_nonneg (by linarith : (0:ℝ) ≤ 2 * a.Y - 1)
    (sub_nonneg.2 hY)]

/-- **Lemma 6.3** of the note (the expansion condition carries over unless `Y_new ≥ 16/5`).
By `E_new_iff`, the expansion condition fails at the image exactly when `ψ(s) < 0`. If `Y > 2`,
`Y' > 2`, `Y - 1 ≤ s < Y` and `ψ(s) < 0`, then `Y_new = (Y' s² - 2s + Y)/(Y - s) ≥ 16/5`.

Route (the note, Lemma 6.3; `x = Y - 2`, `y = Y' - 2`, `N_Y(s) = Y' s² - 2s + Y`). Suppose
`Y_new(s) < 16/5`.
1. `Y_new` increases on `[1, Y)`: for `1 ≤ s' ≤ s < Y`,
   `N_Y(s)(Y - s') - N_Y(s')(Y - s) = (s - s')(Y'(Y(s + s') - s s') - Y)` and
   `Y'(Y(s + s') - s s') - Y ≥ Y(Y' s - 1) > 0` (`dY_new/ds = (Y' s(2Y - s) - Y)/(Y - s)²`).
2. `ψ'(s) = s(4YY' + 4 - 9Y' s)`: `ψ` increases on `(0, m]` and decreases on `[m, ∞)`,
   `m = (4YY' + 4)/(9Y')`, so on an interval `[s₁, s₂] ⊂ (0, ∞)`, `ψ ≥ min(ψ(s₁), ψ(s₂))`
   (algebraically: `ψ(u) - ψ(v) = (u - v)(-3Y'(u² + uv + v²) + (2YY' + 2)(u + v))`).
3. `χ(s) := Y' s² + (6/5) s - (11/5) Y = (Y - s)(Y_new(s) - 16/5)` increases on `(0, ∞)` and has
   one positive root `s_χ < Y` (`χ(0) < 0 < χ(Y)`); `χ(s) < 0`, so `Y - 1 ≤ s < s_χ`.
4. At `s_χ`: `Y_new = 16/5`, and E at the image reads `Y'_new ≤ 28/11`, i.e. `s_χ ≤ (17/28) Y`,
   i.e. `χ((17/28) Y) ≥ 0`; `χ((17/28) Y) = Y((289/784) YY' - 103/70)` and
   `YY' > 4 > 5768/1445 = (103/70)(784/289)`. So E holds at the image at `s_χ`, i.e.
   `ψ(s_χ) ≥ 0` (`E_new_iff`). (Directly:
   `ψ(s_χ) = (Y - s_χ)²((Y_new - 2) - (Y_new - 1)(Y'_new - 2))` with `Y_new = 16/5`.)
5. At `Y - 1`: `Y_new(Y - 1) = 2 + 3x + 2x² + y(1 + x)² ≤ Y_new(s) < 16/5` (step 1) forces
   `3x + 2x² < 6/5`, so `x < 1/3` (`3/3 + 2/9 = 11/9 > 6/5`), and
   `ψ(Y - 1) = x(2 - x - 2x²) + y(1 + x)²(1 - x) > 0`.
6. By step 2 on `[Y - 1, s_χ]`, `ψ(s) ≥ 0`: a contradiction.
Margin (numerical): the infimum of `Y_new` over `{ψ(s) < 0, s ≥ Y - 1}` is `3.21525` (Fuller corner
`Y = Y' = 2`, `s = (1 + √7)/3`); `16/5` is used because it exceeds the root `Y_* = 3.16258` of
`β_Y(Y) = Y log Y - (Y - 1) - (Y - 1)²/Y` (Lemma 6.4).

In Lean (`YNew_ge_unfolded`), step 1 is used through `χ` only: `χ` increases on `[0, ∞)`
(`χ(v) - χ(u) = (v - u)(Y'(u + v) + 6/5)`), so `χ(Y - 1) ≤ χ(s) < 0` in step 5. The root
`s_χ ∈ [s, Y]` comes from the intermediate value theorem, and step 4 uses the direct form
`ψ(s_χ) = (2Y - 3s_χ) χ(s_χ) + (1/5)(17Y - 28 s_χ)(Y - s_χ)` with `s_χ ≤ (17/28) Y`. Step 2 is
`cubic_nonneg_between`. -/
theorem YNew_ge (hY : 2 < a.Y) (hY' : 2 < a.Y') {s : ℝ} (hs1 : a.Y - 1 ≤ s) (hs2 : s < a.Y)
    (hpsi : a.psiE s < 0) : 16 / 5 ≤ a.YNew s :=
  YNew_ge_unfolded hY hY' hs1 hs2 hpsi


end ArcParams

end SmoothedPolygons
