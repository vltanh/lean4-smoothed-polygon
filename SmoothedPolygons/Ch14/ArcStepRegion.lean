module

public import SmoothedPolygons.Ch14.ArcStepClosed

/-!
# Chapter 14, N4: E at the image decides the next point (the proof of (INV), II)

Part of the formalization's proof of N4 (`UnstableCurveLeavesStarDomain`, Figure 14.2) without
computer assistance. **Departure from the paper**, by the user's decision: the book reads N4 off a
computed figure (Figure 14.2, TeX 11951–11991; REPORT.md E88); the formalization proves it from
the exact structure of the Reinhardt flow along an `e₂`-arc (see
`SmoothedPolygons/Ch14/ArcParams.lean`) and the invariance of a region, the single-step statement
(INV) (`arcRegionInvariant`, `SmoothedPolygons/Ch14/ArcRegionInvariant.lean`, where the numbering
of the steps is listed).

This file holds INV Propositions 3 and 4: statements about real numbers only (no flows). With
`s = e^{τ_sw}` the switch of a point of `𝒢*` and `ψ(s)` the cubic of INV Corollary 1.2 (`psiE`,
`E_new_iff`):
* if `ψ(s) ≥ 0` (E holds at the image), then `Φ(s) ≤ 0`, i.e. P2 holds at the image
  (`Phi_nonpos`, INV Proposition 3), so the image is again in `𝒢*`;
* if `ψ(s) < 0` (E fails at the image), then `Y_new ≥ 16/5` (`YNew_ge`, INV Proposition 4), and
  the next arc exits (INV Lemma 6, `SmoothedPolygons/Ch14/ArcStepExit.lean`).

## Notation

As in `SmoothedPolygons/Ch14/ArcStepClosed.lean`; the real variables are `x = Y - 2`, `y = Y' - 2`,
`z = s - Y + 1` (the structure is `a`), and `σ = s - 1 = x + z`.
`φ(s) = (Y' - 1) s³ - (2Y' + 1) s² + (2Y + 1) s - (Y - 1)`,
`Q(s) = (2Y' - 1) s² - (YY' + Y' + 1) s + 2Y`. Every identity below is a polynomial identity
(`ring` or `linear_combination`); all were also checked exactly with sympy, twice independently
and once as written here (with the certificate).
-/

@[expose] public section

namespace SmoothedPolygons

/-! ### Real-number lemmas (INV §3–§4)

INV Proposition 3 is proved in the variables `x = Y - 2`, `y = Y' - 2`, `z = s - Y + 1` (so
`Y = 2 + x`, `Y' = 2 + y`, `s = 1 + x + z`). -/

/-- The Bernstein form of `K̃` on the triangle `T`, in `λ₀ = l0`, `λ₁ = x`, `λ₂ = w`
(all `≥ 0`; `λ₀ + λ₁ + λ₂ = 1` on `T`). -/
private theorem n4h_bernK (l0 x w : ℝ) (h0 : 0 ≤ l0) (hx : 0 ≤ x) (hw : 0 ≤ w) :
    0 ≤ 2 / 3 * w ^ 6 + 6 * x * w ^ 5 + 1069 / 54 * x ^ 2 * w ^ 4 + 841 / 27 * x ^ 3 * w ^ 3 +
      479 / 18 * x ^ 4 * w ^ 2 + 46 / 3 * x ^ 5 * w + 6 * x ^ 6 + 8 / 3 * l0 * w ^ 5 +
      68 / 3 * l0 * x * w ^ 4 + 1862 / 27 * l0 * x ^ 2 * w ^ 3 + 883 / 9 * l0 * x ^ 3 * w ^ 2 +
      209 / 3 * l0 * x ^ 4 * w + 22 * l0 * x ^ 5 + 4 * l0 ^ 2 * w ^ 4 +
      100 / 3 * l0 ^ 2 * x * w ^ 3 + 90 * l0 ^ 2 * x ^ 2 * w ^ 2 + 302 / 3 * l0 ^ 2 * x ^ 3 * w +
      83 / 2 * l0 ^ 2 * x ^ 4 + 8 / 3 * l0 ^ 3 * w ^ 3 + 145 / 6 * l0 ^ 3 * x * w ^ 2 +
      317 / 6 * l0 ^ 3 * x ^ 2 * w + 34 * l0 ^ 3 * x ^ 3 + 2 / 3 * l0 ^ 4 * w ^ 2 +
      9 * l0 ^ 4 * x * w + 12 * l0 ^ 4 * x ^ 2 + 3 / 2 * l0 ^ 5 * x := by
  positivity

/-- INV §3 step 7: `K̃(x, z) ≥ 0` on the triangle `T = {x ≥ 0, z ≥ 0, x + 3z ≤ 1}` (the
Bernstein form with `λ₀ = 1 - x - 3z`, `λ₁ = x`, `λ₂ = 3z`). -/
private theorem n4h_Kt_nonneg {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) (hl0 : 0 ≤ 1 - x - 3 * z) :
    0 ≤ 2 * x ^ 6 + 6 * x ^ 5 * z + x ^ 5 / 2 + 6 * x ^ 4 * z ^ 2 - 13 / 2 * x ^ 4 * z -
      7 / 2 * x ^ 4 + 2 * x ^ 3 * z ^ 3 - 25 / 2 * x ^ 3 * z ^ 2 - 41 / 2 * x ^ 3 * z + x ^ 3 -
      11 / 2 * x ^ 2 * z ^ 3 - 18 * x ^ 2 * z ^ 2 - 7 / 2 * x ^ 2 * z + 9 / 2 * x ^ 2 -
      9 / 2 * x * z ^ 3 + 9 / 2 * x * z ^ 2 + 9 / 2 * x * z + 3 / 2 * x + 6 * z ^ 2 := by
  have := n4h_bernK (1 - x - 3 * z) x (3 * z) hl0 hx (by linarith)
  linarith

/-- INV §3 step 6: `K = k₀ + k₁ y + k₂ y² ≥ 0` for `0 ≤ y ≤ x/(1 + x)` on `T`, with
`k₀ = (3/2)(x + 2z)²`, `k₁ = (1/2)(1 + σ) L₁`, `k₂ = (1 + σ)² L₂ ≤ 0`, `σ = x + z`. By concavity
in `y`: `x (1 + x) K = (1 + x)(x - (1 + x) y) k₀ + y K̃ + x k₂ y ((1 + x) y - x)`. -/
private theorem n4h_K_nonneg {x y z : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hl0 : 0 ≤ 1 - x - 3 * z) (hE : (1 + x) * y ≤ x) :
    0 ≤ 3 / 2 * (x + 2 * z) ^ 2 + 1 / 2 * (1 + (x + z)) *
        (2 * x ^ 3 + 4 * x ^ 2 * z - 5 * x ^ 2 + 2 * x * z ^ 2 - 18 * x * z - 9 * z ^ 2 - 6 * z +
          3) * y +
      (1 + (x + z)) ^ 2 * (x * (x + z - 1) - 2 * z) * y ^ 2 := by
  have hL2 : x * (x + z - 1) - 2 * z ≤ 0 := by nlinarith
  have hk2 : (1 + (x + z)) ^ 2 * (x * (x + z - 1) - 2 * z) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hL2
  have hKt := n4h_Kt_nonneg hx.le hz hl0
  have t1 : 0 ≤ (1 + x) * (x - (1 + x) * y) * (3 / 2 * (x + 2 * z) ^ 2) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  have t2 := mul_nonneg hy hKt
  have t3 : 0 ≤ x * ((1 + (x + z)) ^ 2 * (x * (x + z - 1) - 2 * z) * (y * ((1 + x) * y - x))) :=
    mul_nonneg hx.le (mul_nonneg_of_nonpos_of_nonpos hk2
      (mul_nonpos_of_nonneg_of_nonpos hy (by linarith)))
  have hxx : 0 < x * (1 + x) := by positivity
  by_contra h
  push Not at h
  -- `x (1 + x) K = t₁ + t₂ + t₃` is a polynomial identity, used by `linarith` after expansion
  linarith [mul_neg_of_pos_of_neg hxx h]

/-- INV §3 steps 2–4 as one identity, modulo `R̃ = 0`:
`(s - 1) P₁ - (3 - xy) Φ(s) = C π(s) + (s²/2) W + s² p D` with
`C = (3 - xy)(Y' s² - 1) + s² y (YY' - 1)` (the coefficient of `-q`),
`W = (Y'(f₀ - q) - Y p)² - 4pq` and `D = (YY' - 1) x - (3 - xy)(s² - Y)`. -/
private theorem n4h_Phi_key {x y z f0 q p : ℝ}
    (hR : ((2 + y) * (f0 - q) - (2 + x) * p) ^ 2 - 4 * p * q +
      2 * ((2 + x) * (2 + y) - 1) * ((2 + y - 2) * q + (2 + x - 2) * p) +
      2 * (2 + y) * (3 - (2 + x - 2) * (2 + y - 2)) * f0 = 0) :
    (x + z) * ((3 - x * y) * (1 + x + z) * ((2 * (2 + y) - 1) * (1 + x + z) ^ 2 -
        ((2 + x) * (2 + y) + (2 + y) + 1) * (1 + x + z) + 2 * (2 + x)) +
        (1 + x + z) ^ 2 * y * z * ((2 + x) * (2 + y) - 1)) -
      (3 - x * y) * ((2 + y - 1 + p) * (1 + x + z) ^ 4 - 3 * (2 + y) * (1 + x + z) ^ 3 +
        ((2 + y) * (1 + f0 - (2 + x - 1 + q)) + (2 + x) * (2 - (2 + y) - p) +
          2 * (2 + x) * (2 + y) + 2) * (1 + x + z) ^ 2 - 3 * (2 + x) * (1 + x + z) +
        (2 + x - 1 + q)) =
      ((3 - x * y) * ((2 + y) * (1 + x + z) ^ 2 - 1) +
        (1 + x + z) ^ 2 * y * ((2 + x) * (2 + y) - 1)) *
        ((1 + x + z) ^ 2 - (2 + x) * (1 + x + z) + (2 + x - 1 + q)) +
      (1 + x + z) ^ 2 / 2 * (((2 + y) * (f0 - q) - (2 + x) * p) ^ 2 - 4 * p * q) +
      (1 + x + z) ^ 2 * p * (((2 + x) * (2 + y) - 1) * x -
        (3 - x * y) * ((1 + x + z) ^ 2 - (2 + x))) := by
  linear_combination (-(1 + x + z) ^ 2 / 2) * hR

/-- INV (3.4)–(3.5): `P₁ = (3 - xy) s Q(s) + s² y z (YY' - 1) = -(3/2) ψ(s) - K`. -/
private theorem n4h_P1_eq (x y z : ℝ) :
    (3 - x * y) * (1 + x + z) * ((2 * (2 + y) - 1) * (1 + x + z) ^ 2 -
        ((2 + x) * (2 + y) + (2 + y) + 1) * (1 + x + z) + 2 * (2 + x)) +
        (1 + x + z) ^ 2 * y * z * ((2 + x) * (2 + y) - 1) =
      -(3 / 2) * (-3 * (2 + y) * (1 + x + z) ^ 3 + (2 * (2 + x) * (2 + y) + 2) * (1 + x + z) ^ 2 -
        (2 + x) ^ 2) -
      (3 / 2 * (x + 2 * z) ^ 2 + 1 / 2 * (1 + (x + z)) *
        (2 * x ^ 3 + 4 * x ^ 2 * z - 5 * x ^ 2 + 2 * x * z ^ 2 - 18 * x * z - 9 * z ^ 2 - 6 * z +
          3) * y +
      (1 + (x + z)) ^ 2 * (x * (x + z - 1) - 2 * z) * y ^ 2) := by
  ring

/-- INV §3 step 1 (the range): `ψ(s) ≥ 0` forces `2Y - 3s = 1 - x - 3z > 0`, by
`ψ(s) + (Y - s)² = s (Y' s - 1)(2Y - 3s)`. -/
private theorem n4h_range {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 ≤ z) (hz1 : z < 1)
    (hpsi : 0 ≤ -3 * (2 + y) * (1 + x + z) ^ 3 + (2 * (2 + x) * (2 + y) + 2) * (1 + x + z) ^ 2 -
        (2 + x) ^ 2) : 0 < 1 - x - 3 * z := by
  have hid : (-3 * (2 + y) * (1 + x + z) ^ 3 + (2 * (2 + x) * (2 + y) + 2) * (1 + x + z) ^ 2 -
        (2 + x) ^ 2) + (1 - z) ^ 2 =
      (1 + x + z) * ((2 + y) * (1 + x + z) - 1) * (1 - x - 3 * z) := by ring
  have hpos : 0 < (1 + x + z) * ((2 + y) * (1 + x + z) - 1) := by
    apply mul_pos (by linarith); nlinarith
  have hsq : 0 < (1 - z) ^ 2 := by
    have : 0 < 1 - z := by linarith
    positivity
  by_contra h
  push Not at h
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hpos.le h]

/-- INV Proposition 3 on real numbers (`Phi_nonpos` with the definitions unfolded). `f₀ ≥ 0`
is not needed: in the identity `n4h_Phi_key` the `f₀`-terms of the budget cancel. -/
private theorem n4h_Phi_core {Y Y' f0 q p s : ℝ} (ha : 0 < Y - 2) (hb : 0 < Y' - 2)
    (hE : (Y - 1) * (Y' - 2) ≤ Y - 2) (h2 : q ≤ 0) (h4 : 0 ≤ p)
    (hR : (Y' * (f0 - q) - Y * p) ^ 2 - 4 * p * q +
      2 * (Y * Y' - 1) * ((Y' - 2) * q + (Y - 2) * p) +
      2 * Y' * (3 - (Y - 2) * (Y' - 2)) * f0 = 0)
    (hs1 : Y - 1 ≤ s) (hs2 : s < Y) (hpi : 0 ≤ s ^ 2 - Y * s + (Y - 1 + q))
    (hpsi : 0 ≤ -3 * Y' * s ^ 3 + (2 * Y * Y' + 2) * s ^ 2 - Y ^ 2) :
    (Y' - 1 + p) * s ^ 4 - 3 * Y' * s ^ 3 +
      (Y' * (1 + f0 - (Y - 1 + q)) + Y * (2 - Y' - p) + 2 * Y * Y' + 2) * s ^ 2 -
      3 * Y * s + (Y - 1 + q) ≤ 0 := by
  obtain ⟨x, rfl⟩ : ∃ x, Y = 2 + x := ⟨Y - 2, by ring⟩
  obtain ⟨y, rfl⟩ : ∃ y, Y' = 2 + y := ⟨Y' - 2, by ring⟩
  obtain ⟨z, rfl⟩ : ∃ z, s = 1 + x + z := ⟨s - 1 - x, by ring⟩
  have hx : 0 < x := by linarith
  have hy : 0 < y := by linarith
  have hz : 0 ≤ z := by linarith
  have hz1 : z < 1 := by linarith
  have hE' : (1 + x) * y ≤ x := by linarith
  -- step 1, the range: `(x, z) ∈ T`, `s² - Y < x`, `y < 1/2`, `3 - xy > 0`
  have hl0 := n4h_range hx hy hz hz1 hpsi
  have hx1 : x < 1 := by linarith
  have hy2 : 2 * y < 1 := by nlinarith only [hE', hx1, hx, hy]
  have hxy : x * y < 1 / 2 := by nlinarith only [mul_lt_mul_of_pos_right hx1 hy, hy2]
  have h3xy : 0 < 3 - x * y := by linarith
  have hsY : (1 + x + z) ^ 2 - (2 + x) < x := by nlinarith only [hl0, hz, hx, hx1]
  -- steps 6–7: `K ≥ 0`
  have hK := n4h_K_nonneg hx hy.le hz hl0.le hE'
  -- steps 2–4: the terms of `n4h_Phi_key` are `≥ 0`
  have hC : 0 ≤ (3 - x * y) * ((2 + y) * (1 + x + z) ^ 2 - 1) +
      (1 + x + z) ^ 2 * y * ((2 + x) * (2 + y) - 1) := by
    have : 0 ≤ (2 + y) * (1 + x + z) ^ 2 - 1 := by nlinarith only [hx, hy, hz]
    have : 0 ≤ (2 + x) * (2 + y) - 1 := by nlinarith only [hx, hy]
    positivity
  have hW : 0 ≤ ((2 + y) * (f0 - q) - (2 + x) * p) ^ 2 - 4 * p * q := by
    linarith [sq_nonneg ((2 + y) * (f0 - q) - (2 + x) * p), mul_nonneg h4 (neg_nonneg.2 h2)]
  have hD : 0 ≤ ((2 + x) * (2 + y) - 1) * x - (3 - x * y) * ((1 + x + z) ^ 2 - (2 + x)) := by
    nlinarith only [mul_lt_mul_of_pos_left hsY h3xy,
      mul_nonneg hx.le (by positivity : (0:ℝ) ≤ 2 * x + 2 * y + 2 * x * y)]
  have key := n4h_Phi_key (z := z) hR
  rw [n4h_P1_eq] at key
  have t1 := mul_nonneg hC hpi
  have t2 := mul_nonneg (by positivity : (0:ℝ) ≤ (1 + x + z) ^ 2 / 2) hW
  have t3 := mul_nonneg (mul_nonneg (sq_nonneg (1 + x + z)) h4) hD
  have t4 := mul_nonneg (by linarith : (0:ℝ) ≤ x + z)
    (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3 / 2) hpsi) hK)
  -- step 8: `(3 - xy) Φ(s) ≤ (s - 1) P₁ = -(s - 1)((3/2) ψ(s) + K) ≤ 0`
  have hfin : (3 - x * y) * ((2 + y - 1 + p) * (1 + x + z) ^ 4 - 3 * (2 + y) * (1 + x + z) ^ 3 +
      ((2 + y) * (1 + f0 - (2 + x - 1 + q)) + (2 + x) * (2 - (2 + y) - p) +
        2 * (2 + x) * (2 + y) + 2) * (1 + x + z) ^ 2 - 3 * (2 + x) * (1 + x + z) +
      (2 + x - 1 + q)) ≤ 0 := by
    linarith
  by_contra h
  push Not at h
  linarith [mul_pos h3xy h]

/-- A cubic `-3Y' t³ + C t² - K` with `Y' > 0` increases and then decreases on `(0, ∞)`, so on
`[u, v] ⊂ (0, ∞)` it is at least the smaller of its values at the ends. -/
private theorem n4h_cubic_between {Y' C K u s v : ℝ} (hY' : 0 < Y') (hu : 0 < u) (hus : u ≤ s)
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

/-- INV Proposition 4 on real numbers. -/
private theorem n4h_YNew_core {Y Y' s : ℝ} (hY : 2 < Y) (hY' : 2 < Y') (hs1 : Y - 1 ≤ s)
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
  have := n4h_cubic_between (by linarith : (0:ℝ) < Y') (by linarith : (0:ℝ) < Y - 1) hs1 hst
    hψ1 hψt
  linarith

namespace ArcParams

variable (a : ArcParams)

/-- **INV Proposition 3** (E at the image implies P2 at the image). Let `Y - 2 > 0`,
`Y' - 2 > 0`, E (`(Y - 1)(Y' - 2) ≤ Y - 2`), P2 and P4 in the weak form (`q ≤ 0`, `p ≥ 0`), the
relation `R̃ = 0`, `Y - 1 ≤ s < Y`, `π(s) = s² - Y s + B ≥ 0` and `ψ(s) ≥ 0`. Then
`Φ(s) ≤ 0`; sharper, `(3 - xy) Φ(s) ≤ (s - 1) P₁ ≤ -(3/2)(s - 1) ψ(s) ≤ 0` with
`P₁ = (3 - xy) s Q(s) + s² y z (YY' - 1)`.

Route (INV §3; `x = Y - 2`, `y = Y' - 2`, `z = s - Y + 1`, `σ = s - 1 = x + z`):
1. **Range.** `x > 0`, `y > 0`, `(1 + x) y ≤ x` (E). From `ψ(s) + (Y - s)² = s (Y' s - 1)(2Y - 3s)`
   and `ψ(s) ≥ 0`, `s ≥ Y - 1 > 1`, `Y' s > 1`: `3s < 2Y`. With `s ≥ Y - 1`: `Y < 3`, so `x < 1`,
   and `z ≥ 0`, `x + 3z < 1` (`3z = 3s - 3Y + 3 < 3 - Y = 1 - x`): `(x, z)` lies in the triangle
   `T = {x ≥ 0, z ≥ 0, x + 3z ≤ 1}`. Also `s² - Y < x`, from `s² < 4Y²/9 ≤ 2(Y - 1)`
   (`(2Y - 3)(Y - 3) ≤ 0`), and `y ≤ x/(1 + x) < 1/2`, so `xy < 1/2` and `3 - xy > 0`;
   `YY' - 1 - (3 - xy) = 2x + 2y + 2xy ≥ 0`.
2. **The budget (INV (2.3)).** `R̃ = 0` (`relT`) rearranged:
   `2(YY' - 1) y (-q) = (Y'(f₀ - q) - Y p)² + 4p(-q) + 2(YY' - 1) x p + 2Y'(3 - xy) f₀`, hence
   `(YY' - 1) y (-q) ≥ (YY' - 1) x p + Y'(3 - xy) f₀`.
3. **Identities** (INV (3.1)–(3.3)).
   (3.1) `Φ(s) = (s - 1) φ(s) + Y' s² f₀ - (Y' s² - 1) q + s² (s² - Y) p`;
   (3.2) `s² - Y s + B = q + (s - 1) z`; (3.3) `φ(s) + z (Y' s² - 1) = s Q(s)`.
4. **The bound on `Φ`.** `(3 - xy)(s² - Y) p ≤ (3 - xy) x p ≤ (YY' - 1) x p` (step 1, `p ≥ 0`), so
   by step 2 `(3 - xy)(Y' s² f₀ + s²(s² - Y) p) ≤ s² (Y'(3 - xy) f₀ + (YY' - 1) x p)
   ≤ s² (YY' - 1) y (-q)`. By (3.2) and `π(s) ≥ 0`, `0 ≤ -q ≤ (s - 1) z`, and the coefficient
   `(3 - xy)(Y' s² - 1) + s² (YY' - 1) y` of `-q` is `≥ 0`. With (3.1) and (3.3):
   `(3 - xy) Φ(s) ≤ (s - 1)[(3 - xy)(φ(s) + z(Y' s² - 1)) + s² y z (YY' - 1)] = (s - 1) P₁`.
5. **INV (3.4)–(3.5).** In `(x, y, z)` (`Y = 2 + x`, `Y' = 2 + y`, `s = 1 + σ`):
   `Q = -y(1 + x) - σ(1 + 2x + xy - y) + (3 + 2y) σ²`, and
   `-P₁ = (3/2) ψ(s) + K`, `K = (3/2)(x + 2z)² + (y/2)(1 + σ) L₁ + y² (1 + σ)² L₂`,
   `L₁ = 2x³ + 4x²z - 5x² + 2xz² - 18xz - 9z² - 6z + 3`, `L₂ = x(x + z - 1) - 2z`
   (`P₁ = (3 - xy)(1 + σ) Q + (1 + σ)² y z ((2 + x)(2 + y) - 1)`; `ring`).
6. **`K ≥ 0`.** On `T`, `x + z ≤ 1`, so `L₂ ≤ 0`: `K = k₀ + k₁ y + k₂ y²` is concave in `y`
   (`k₂ = (1 + σ)² L₂ ≤ 0`). With `y₁ = x/(1 + x) > 0` and `0 ≤ y ≤ y₁`:
   `y₁ K(y) = (y₁ - y) K(0) + y K(y₁) + y₁ k₂ y (y - y₁)` (the last term `≥ 0`),
   `K(0) = (3/2)(x + 2z)² ≥ 0`, and `(1 + x)² K(y₁) = K̃(x, z)` with
   `K̃ = 2x⁶ + 6x⁵z + (1/2)x⁵ + 6x⁴z² - (13/2)x⁴z - (7/2)x⁴ + 2x³z³ - (25/2)x³z² - (41/2)x³z + x³
   - (11/2)x²z³ - 18x²z² - (7/2)x²z + (9/2)x² - (9/2)xz³ + (9/2)xz² + (9/2)xz + (3/2)x + 6z²`.
7. **The Bernstein certificate of `K̃ ≥ 0` on `T`.** With `λ₀ = 1 - x - 3z`, `λ₁ = x`, `λ₂ = 3z`
   (`λ₀ + λ₁ + λ₂ = 1`, all `≥ 0` on `T`), homogenized to degree 6,
   `K̃ = Σ_{i+j+k=6} c_{ijk} λ₀^i λ₁^j λ₂^k` with (`ijk:c_{ijk}`; the 2 missing ones, `600`, `501`,
   are `0`):
   `006:2/3, 015:6, 024:1069/54, 033:841/27, 042:479/18, 051:46/3, 060:6, 105:8/3, 114:68/3,
   123:1862/27, 132:883/9, 141:209/3, 150:22, 204:4, 213:100/3, 222:90, 231:302/3, 240:83/2,
   303:8/3, 312:145/6, 321:317/6, 330:34, 402:2/3, 411:9, 420:12, 510:3/2`.
   Lean: the expansion is `ring` (substitute `λ₀ + λ₁ + λ₂ = 1` by writing each degree-`< 6`
   monomial of `K̃` times `(λ₀ + λ₁ + λ₂)^{6 - deg}`), then `positivity`.
8. `(3 - xy) Φ(s) ≤ (s - 1) P₁ = -(s - 1)((3/2) ψ(s) + K) ≤ 0` and `3 - xy > 0`.
Margins (numerical, for orientation): `-P₁ ≥ 0.80 (x + y + z)` on the region; the bound is within
20% of `q_new` at images.

In Lean (`n4h_Phi_core`), steps 2–4 are one identity modulo `R̃ = 0` (`linear_combination`):
`(s - 1) P₁ - (3 - xy) Φ(s) = C π(s) + (s²/2)((Y'(f₀ - q) - Y p)² - 4pq)
+ s² p ((YY' - 1) x - (3 - xy)(s² - Y))`, `C = (3 - xy)(Y' s² - 1) + s² y (YY' - 1)`, and each term
on the right is `≥ 0` by step 1. The `f₀`-terms of the budget cancel in it, so `f₀ ≥ 0` (P1,
assumed in INV Proposition 3) is not needed, and the statement omits it. -/
theorem Phi_nonpos (ha : 0 < a.Y - 2) (hb : 0 < a.Y' - 2) (hE : (a.Y - 1) * (a.Y' - 2) ≤ a.Y - 2)
    (h2 : a.q ≤ 0) (h4 : 0 ≤ a.p) (hR : a.relT = 0) {s : ℝ}
    (hs1 : a.Y - 1 ≤ s) (hs2 : s < a.Y) (hpi : 0 ≤ s ^ 2 - a.Y * s + a.B)
    (hpsi : 0 ≤ a.psiE s) : a.Phi s ≤ 0 :=
  n4h_Phi_core ha hb hE h2 h4 hR hs1 hs2 hpi hpsi

/-- **INV Proposition 4** (E fails at the image implies `Y_new ≥ 16/5`). If `Y > 2`, `Y' > 2`,
`Y - 1 ≤ s < Y` and `ψ(s) < 0`, then `Y_new = (Y' s² - 2s + Y)/(Y - s) ≥ 16/5`.

Route (INV §4; `x = Y - 2`, `y = Y' - 2`, `N_Y(s) = Y' s² - 2s + Y`). Suppose `Y_new(s) < 16/5`.
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
`g(Y) = Y log Y - (Y - 1) - (Y - 1)²/Y` (INV Lemma 6).

In Lean (`n4h_YNew_core`), step 1 is used through `χ` only: `χ` increases on `[0, ∞)`
(`χ(v) - χ(u) = (v - u)(Y'(u + v) + 6/5)`), so `χ(Y - 1) ≤ χ(s) < 0` in step 5. The root
`s_χ ∈ [s, Y]` comes from the intermediate value theorem, and step 4 uses the direct form
`ψ(s_χ) = (2Y - 3s_χ) χ(s_χ) + (1/5)(17Y - 28 s_χ)(Y - s_χ)` with `s_χ ≤ (17/28) Y`. Step 2 is
`n4h_cubic_between`. -/
theorem YNew_ge (hY : 2 < a.Y) (hY' : 2 < a.Y') {s : ℝ} (hs1 : a.Y - 1 ≤ s) (hs2 : s < a.Y)
    (hpsi : a.psiE s < 0) : 16 / 5 ≤ a.YNew s :=
  n4h_YNew_core hY hY' hs1 hs2 hpsi

end ArcParams

end SmoothedPolygons
