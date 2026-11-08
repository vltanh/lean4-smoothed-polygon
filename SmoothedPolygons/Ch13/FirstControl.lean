module

public import SmoothedPolygons.Ch13.Symmetry
public import Basic.Analysis.Polynomial.SignNearZero

/-!
# Chapter 13: walls, the first control and the switching times

§13.2 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Walls" and "Switching Times",
TeX 10910–11068, and the most recent control, TeX 10880–10906):

* the walls (TeX 10910–10926): at a switch between `ζ` and `ζ²` the maximum condition reads
  `RR(z₃, ζ) = RR(z₃, ζ²) ≥ RR(z₃, 1)`, whose solution set is `ℝ_{≤0}`
  (`RR_eq_and_le_iff_mem_wall_zero`), and switching can only occur when `z₃ ∈ 𝒲`
  (`mem_walls_of_maximizers`);
* Lemma 13.2.6 (`lem:first-control`): the first control is the lexicographic maximum of the
  control vectors, with the tie rule `{ζ^i, ζ^{i+1}} ↦ ζ^i`; with it, the first control exists and
  is unique (`l4st_exists_isFirstControl`, `IsFirstControl.unique`);
* Corollary 13.2.7 (`cor:10`): `t_sw < 10 r` when `|z_i| ≤ r^i`;
* Lemma 13.2.8 (unlabelled): `χ_{ζ,ζ²} + χ_{ζ²,ζ} = 0`;
* Lemma 13.2.5 (`lem:first-negative-control`): the most recent control and switching time by
  time reversal;
* the basic properties of the first switching time: `0 < t_sw` for `z⁰ ≠ 0` (TeX 10750–10753:
  "`t = 0` is an isolated zero of the relevant switching function"), the first control is optimal
  on `[0, t_sw]`, and it is beaten at times arbitrarily close to `t_sw` from the right;
* the first-control trajectory of `z⁰ ≠ 0` does not reach `0` on `[0, t_sw]`
  (`flow_firstControl_ne_zero`; Lemma 13.3.1 covers only `z₃⁰ ∈ 𝒲`).

The informal corollary after Lemma 13.2.8 (TeX 11063–11067: switching back and forth between `ζ`
and `ζ²` happens at consecutive roots of one cubic, and after its largest root the control switches
to `1`) is not a numbered result and is not used later; it is not formalized.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex MeasureTheory Set TriFuller

namespace TriFuller

/-! ### Helpers: `ζ`, `RR` and the switching polynomials -/

private lemma l4c_sqrt3_mul_self : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

/-- `RR(ua, ub) = RR(a, b)` for `|u| = 1` (the invariance behind the rotation (13.2.7)). -/
private lemma l4c_RR_mul_mul {u : ℂ} (hu : ‖u‖ = 1) (a b : ℂ) : RR (u * a) (u * b) = RR a b := by
  have h : u.re * u.re + u.im * u.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hu]; norm_num
  rw [RR_eq_re_mul_add_im_mul, RR_eq_re_mul_add_im_mul]
  simp only [Complex.mul_re, Complex.mul_im]
  linear_combination (a.re * b.re + a.im * b.im) * h

/-- `V_T = {u, uζ, uζ²}` for every `u ∈ V_T`. -/
private lemma l4c_mem_VT_iff {u : ℂ} (hu : u ∈ VT) {v : ℂ} :
    v ∈ VT ↔ v = u ∨ v = u * ζ ∨ v = u * ζ ^ 2 := by
  constructor
  · intro hv
    have hn := norm_eq_one_of_mem_VT hu
    have hc := conj_mem_VT hu
    have hw : starRingEnd ℂ u * v ∈ VT := mul_mem_VT hc hv
    have huu : u * starRingEnd ℂ u = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; norm_num
    have hv' : v = u * (starRingEnd ℂ u * v) := by rw [← mul_assoc, huu, one_mul]
    rcases mem_VT.1 hw with h | h | h <;> rw [h] at hv' <;> simp_all
  · rintro (rfl | rfl | rfl)
    · exact hu
    · exact mul_mem_VT hu ζ_mem_VT
    · exact mul_mem_VT hu ζ_sq_mem_VT

private lemma l4c_exists_pow_of_mem_VT {u : ℂ} (hu : u ∈ VT) : ∃ i : ℕ, u = ζ ^ i := by
  rcases mem_VT.1 hu with rfl | rfl | rfl
  exacts [⟨0, (pow_zero _).symm⟩, ⟨1, (pow_one _).symm⟩, ⟨2, rfl⟩]

private lemma l4c_ζ_ne_zero : ζ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [ζ_re, Complex.zero_re] at this
  norm_num at this

/-- `RR(ζ - 1, -i) = -√3/2`. -/
private lemma l4c_RR_ζ_sub_one : RR (ζ - 1) (-I) = -(√3 / 2) := by
  rw [RR_eq_re_mul_add_im_mul]; simp [ζ_re, ζ_im]

/-- `RR(ζ² - 1, -i) = √3/2`. -/
private lemma l4c_RR_ζ_sq_sub_one : RR (ζ ^ 2 - 1) (-I) = √3 / 2 := by
  rw [RR_eq_re_mul_add_im_mul]; simp [ζ_sq_re, ζ_sq_im]

/-- The cubic coefficient of the switching function from `u` to `uζ` propagated with `u`:
`RR(uζ - u, -iu) = -√3/2`. -/
private lemma l4c_RR_mul_ζ_sub {u : ℂ} (hu : ‖u‖ = 1) : RR (u * ζ - u) (-I * u) = -(√3 / 2) := by
  rw [show u * ζ - u = u * (ζ - 1) by ring, show -I * u = u * (-I) by ring, l4c_RR_mul_mul hu,
    l4c_RR_ζ_sub_one]

/-- The cubic coefficient of the switching function from `u` to `uζ²` propagated with `u`:
`RR(uζ² - u, -iu) = √3/2`. -/
private lemma l4c_RR_mul_ζ_sq_sub {u : ℂ} (hu : ‖u‖ = 1) :
    RR (u * ζ ^ 2 - u) (-I * u) = √3 / 2 := by
  rw [show u * ζ ^ 2 - u = u * (ζ ^ 2 - 1) by ring, show -I * u = u * (-I) by ring,
    l4c_RR_mul_mul hu, l4c_RR_ζ_sq_sub_one]

/-- `RR(d, i d) = 0`. -/
private lemma l4c_RR_I_mul_self (d : ℂ) (c : ℝ) : RR d (I * c * d) = 0 := by
  rw [RR_eq_re_mul_add_im_mul]; simp [Complex.mul_re, Complex.mul_im]; ring

/-- The third coordinate of (13.2.2) seen through `RR(d, ·)`: a cubic polynomial in `t`. -/
private lemma l4c_RR_flow (d : ℂ) (t : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    RR d (flow t z u 2) = RR d (z 2) + RR d (z 1) * t + RR d (z 0) * t ^ 2 / 2 +
      RR d (-I * u) * t ^ 3 / 6 := by
  simp only [RR_eq_re_mul_add_im_mul]
  simp [flow, Complex.mul_re, Complex.mul_im, pow_succ]
  ring

/-- The part of `H_F` that depends on the control: `H_F(w, v) - H_F(w, v') = RR(v - v', w₃)`. -/
private lemma l4c_ham_sub (w : Fin 3 → ℂ) (v v' : ℂ) : ham w v - ham w v' = RR (v - v') (w 2) := by
  simp only [ham, RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im]; ring

/-- The switching polynomial: `H_F(z(t, z⁰, u), v) - H_F(z(t, z⁰, u), v')` as a cubic in `t`
(TeX 10755–10784, up to the factor `√3`). -/
theorem ham_flow_sub_ham_flow (t : ℝ) (z : Fin 3 → ℂ) (u v v' : ℂ) :
    ham (flow t z u) v - ham (flow t z u) v' = RR (v - v') (z 2) + RR (v - v') (z 1) * t +
      RR (v - v') (z 0) * t ^ 2 / 2 + RR (v - v') (-I * u) * t ^ 3 / 6 := by
  rw [l4c_ham_sub, l4c_RR_flow]

private lemma l4c_continuous_ham_flow_sub (z : Fin 3 → ℂ) (u v v' : ℂ) :
    Continuous fun t : ℝ ↦ ham (flow t z u) v - ham (flow t z u) v' := by
  simp_rw [ham_flow_sub_ham_flow]
  fun_prop

/-- The control vectors seen through `RR`: `v(z, v) - v(z, v') = (RR(v - v', z₃), RR(v - v', z₂),
RR(v - v', z₁))`. -/
theorem controlVector_sub_apply (z : Fin 3 → ℂ) (v v' : ℂ) :
    (controlVector z v - controlVector z v') 0 = RR (v - v') (z 2) ∧
      (controlVector z v - controlVector z v') 1 = RR (v - v') (z 1) ∧
      (controlVector z v - controlVector z v') 2 = RR (v - v') (z 0) := by
  simp only [controlVector, Pi.sub_apply, RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im]
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> ring

/-! ### Helpers: the sign of a cubic near `0⁺` and the lexicographic order -/

/-- A cubic with a nonzero leading coefficient does not vanish identically on any `(0, δ]`. -/
private lemma l4c_cubic_ne_zero {a b c d : ℝ} (hd : d ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t ∈ Ioc 0 δ, a + b * t + c * t ^ 2 + d * t ^ 3 ≠ 0 := by
  have key : ∀ {a b c d : ℝ}, (0 < a ∨ (a = 0 ∧ 0 < b) ∨ (a = 0 ∧ b = 0 ∧ 0 < c) ∨
      (a = 0 ∧ b = 0 ∧ c = 0 ∧ 0 < d)) → ∃ t ∈ Ioc 0 δ, a + b * t + c * t ^ 2 + d * t ^ 3 ≠ 0 := by
    intro a b c d h
    obtain ⟨ε, hε, h⟩ := exists_forall_Ioc_cubic_pos h
    exact ⟨min δ ε, ⟨lt_min hδ hε, min_le_left _ _⟩,
      (h _ ⟨lt_min hδ hε, min_le_right _ _⟩).ne'⟩
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · obtain ⟨t, ht, h⟩ := key (a := -a) (b := -b) (c := -c) (d := -d) (Or.inl (by linarith))
    exact ⟨t, ht, fun h' ↦ h (by linear_combination -h')⟩
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · obtain ⟨t, ht, h⟩ := key (a := -0) (b := -b) (c := -c) (d := -d)
        (Or.inr (Or.inl ⟨by simp, by linarith⟩))
      exact ⟨t, ht, fun h' ↦ h (by linear_combination -h')⟩
    · rcases lt_trichotomy c 0 with hc | rfl | hc
      · obtain ⟨t, ht, h⟩ := key (a := -0) (b := -0) (c := -c) (d := -d)
          (Or.inr (Or.inr (Or.inl ⟨by simp, by simp, by linarith⟩)))
        exact ⟨t, ht, fun h' ↦ h (by linear_combination -h')⟩
      · rcases hd.lt_or_gt with hd | hd
        · obtain ⟨t, ht, h⟩ := key (a := -0) (b := -0) (c := -0) (d := -d)
            (Or.inr (Or.inr (Or.inr ⟨by simp, by simp, by simp, by linarith⟩)))
          exact ⟨t, ht, fun h' ↦ h (by linear_combination -h')⟩
        · exact key (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, hd⟩)))
      · exact key (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hc⟩)))
    · exact key (Or.inr (Or.inl ⟨rfl, hb⟩))
  · exact key (Or.inl ha)

/-- A cubic with a positive leading coefficient is positive somewhere on `(0, ∞)`. -/
private lemma l4c_cubic_pos_somewhere {a b c d : ℝ} (hd : 0 < d) :
    ∃ T > 0, 0 < a + b * T + c * T ^ 2 + d * T ^ 3 := by
  set M := |a| + |b| + |c|
  have hM : 0 ≤ M := by positivity
  set T := 1 + M / d
  have hT : 1 ≤ T := by have : 0 ≤ M / d := by positivity
                        linarith
  have hdT : d * T = d + M := by simp only [T]; field_simp
  refine ⟨T, by linarith, ?_⟩
  have h1 : -|a| ≤ a := neg_abs_le a
  have h2 : -(|b| * T) ≤ b * T := by
    have := neg_abs_le b; nlinarith
  have h3 : -(|c| * T ^ 2) ≤ c * T ^ 2 := by
    have := neg_abs_le c; nlinarith [sq_nonneg T]
  have hT2 : 1 ≤ T ^ 2 := by nlinarith
  have hTT : T ≤ T ^ 2 := by nlinarith
  have hd3 : d * T ^ 3 = (d + M) * T ^ 2 := by rw [← hdT]; ring
  have : |a| + |b| * T + |c| * T ^ 2 ≤ M * T ^ 2 := by
    simp only [M]; nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg c]
  nlinarith [sq_nonneg T]

/-- The first nonzero entry of a vector of `ℝ³`. -/
private lemma l4c_lexPos_iff (x : Fin 3 → ℝ) :
    LexPos x ↔ 0 < x 0 ∨ (x 0 = 0 ∧ 0 < x 1) ∨ (x 0 = 0 ∧ x 1 = 0 ∧ 0 < x 2) := by
  constructor
  · rintro ⟨k, hk, hpos⟩
    fin_cases k
    · exact Or.inl hpos
    · exact Or.inr (Or.inl ⟨hk 0 (by decide), hpos⟩)
    · exact Or.inr (Or.inr ⟨hk 0 (by decide), hk 1 (by decide), hpos⟩)
  · rintro (h | ⟨h0, h1⟩ | ⟨h0, h1, h2⟩)
    · exact ⟨0, fun j hj ↦ absurd hj (Fin.not_lt_zero j), h⟩
    · refine ⟨1, fun j hj ↦ ?_, h1⟩
      fin_cases j
      · exact h0
      · exact absurd hj (by decide)
      · exact absurd hj (by decide)
    · refine ⟨2, fun j hj ↦ ?_, h2⟩
      fin_cases j
      · exact h0
      · exact h1
      · exact absurd hj (by decide)

/-- The lexicographic order of the book is the order of `Lex (Fin 3 → ℝ)`, a linear order. -/
private lemma l4c_lexLt_iff (v w : Fin 3 → ℝ) : LexLt v w ↔ toLex v < toLex w := by
  change LexPos (w - v) ↔ ∃ i, (∀ j, j < i → v j = w j) ∧ v i < w i
  simp only [LexPos, Pi.sub_apply, sub_eq_zero, sub_pos]
  exact exists_congr fun i ↦ and_congr_left' (forall₂_congr fun j _ ↦ eq_comm)

/-- If `v(z⁰, v) ≺ v(z⁰, w)`, then `w` beats `v` along every constant-control trajectory from `z⁰`
for small `t ≥ 0` (strictly for `t > 0`): the first three Taylor coefficients of the switching
function are the entries of `v(z⁰, w) - v(z⁰, v)` (up to `1/2`), the first nonzero one positive. -/
private lemma l4c_eventually_of_lexLt {z : Fin 3 → ℂ} {v w : ℂ}
    (h : LexLt (controlVector z v) (controlVector z w)) (u : ℂ) :
    ∃ ε > 0, (∀ t ∈ Icc 0 ε, ham (flow t z u) v ≤ ham (flow t z u) w) ∧
      ∀ t ∈ Ioc 0 ε, ham (flow t z u) v < ham (flow t z u) w := by
  obtain ⟨h0, h1, h2⟩ := controlVector_sub_apply z w v
  have hl := (l4c_lexPos_iff _).1 h
  rw [h0, h1, h2] at hl
  obtain ⟨ε, hε, hpos⟩ := exists_forall_Ioc_cubic_pos (a := RR (w - v) (z 2))
    (b := RR (w - v) (z 1)) (c := RR (w - v) (z 0) / 2) (d := RR (w - v) (-I * u) / 6) (by
      rcases hl with hl | ⟨ha, hb⟩ | ⟨ha, hb, hc⟩
      · exact Or.inl hl
      · exact Or.inr (Or.inl ⟨ha, hb⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨ha, hb, by linarith⟩)))
  have hlt : ∀ t ∈ Ioc 0 ε, ham (flow t z u) v < ham (flow t z u) w := by
    intro t ht
    have := hpos t ht
    have hf := ham_flow_sub_ham_flow t z u w v
    linarith
  refine ⟨ε, hε, fun t ht ↦ ?_, hlt⟩
  rcases ht.1.eq_or_lt with rfl | ht0
  · rw [flow_zero]
    have := l4c_ham_sub z w v
    rcases hl with hl | ⟨ha, -⟩ | ⟨ha, -⟩ <;> linarith
  · exact (hlt t ⟨ht0, ht.2⟩).le

/-- A property of controls holding for small `ε` holds for all three controls at once. -/
private lemma l4c_exists_eps_VT {P : ℂ → ℝ → Prop} (hmono : ∀ v ε ε', ε' ≤ ε → P v ε → P v ε')
    (h : ∀ v ∈ VT, ∃ ε > 0, P v ε) : ∃ ε > 0, ∀ v ∈ VT, P v ε := by
  obtain ⟨ε₁, h₁, p₁⟩ := h 1 one_mem_VT
  obtain ⟨ε₂, h₂, p₂⟩ := h ζ ζ_mem_VT
  obtain ⟨ε₃, h₃, p₃⟩ := h (ζ ^ 2) ζ_sq_mem_VT
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min h₁ (lt_min h₂ h₃), fun v hv ↦ ?_⟩
  rcases mem_VT.1 hv with rfl | rfl | rfl
  · exact hmono _ _ _ (min_le_left _ _) p₁
  · exact hmono _ _ _ ((min_le_right _ _).trans (min_le_left _ _)) p₂
  · exact hmono _ _ _ ((min_le_right _ _).trans (min_le_right _ _)) p₃

/-! ### Walls -/

/-- The wall between `ζ` and `ζ²` (TeX 10912–10918): `RR(w, ζ) = RR(w, ζ²) ≥ RR(w, 1)` if and only
if `w ∈ ℝ_{≤0} = 𝒲₀`. -/
theorem RR_eq_and_le_iff_mem_wall_zero (w : ℂ) :
    (RR w ζ = RR w (ζ ^ 2) ∧ RR w 1 ≤ RR w ζ) ↔ w ∈ wall 0 := by
  have h3 : 0 < √3 := by positivity
  simp only [RR_eq_re_mul_add_im_mul, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, Complex.one_re,
    Complex.one_im, wall, pow_zero, mul_one, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have hy : w.im = 0 := by
      have : w.im * √3 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right h3.ne'
    refine ⟨w.re, by rw [hy] at h2; linarith, ?_⟩
    apply Complex.ext <;> simp [hy]
  · rintro ⟨s, hs, rfl⟩
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    constructor <;> nlinarith

/-- "Switching of controls can only occur when `z₃ ∈ 𝒲`" (TeX 10925–10926): if two distinct
controls of `V_T` both maximize `RR(w, ·)` over `V_T`, then `w ∈ 𝒲`. (The rotation by `ζ^k` takes
the wall `𝒲₀` to `𝒲_k`; `RR_eq_and_le_iff_mem_wall_zero`.) -/
theorem mem_walls_of_maximizers {w u v : ℂ} (hu : u ∈ VT) (hv : v ∈ VT) (huv : u ≠ v)
    (hmu : ∀ x ∈ VT, RR w x ≤ RR w u) (hmv : ∀ x ∈ VT, RR w x ≤ RR w v) : w ∈ walls := by
  have h3 := l4c_sqrt3_mul_self
  -- the wall between `1` and `ζ` is `𝒲₂`, the wall between `1` and `ζ²` is `𝒲₁`
  have hA : RR w 1 = RR w ζ → RR w (ζ ^ 2) ≤ RR w 1 → w ∈ wall 2 := by
    simp only [RR_eq_re_mul_add_im_mul, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, Complex.one_re,
      Complex.one_im]
    intro e f
    have hy : w.im = √3 * w.re := by linear_combination (-2 * √3 / 3) * e - (w.im / 3) * h3
    refine ⟨-2 * w.re, by nlinarith, ?_⟩
    apply Complex.ext <;>
      simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul, ζ_sq_re, ζ_sq_im] <;>
      linarith
  have hB : RR w 1 = RR w (ζ ^ 2) → RR w ζ ≤ RR w 1 → w ∈ wall 1 := by
    simp only [RR_eq_re_mul_add_im_mul, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, Complex.one_re,
      Complex.one_im]
    intro e f
    have hy : w.im = -(√3 * w.re) := by linear_combination (2 * √3 / 3) * e - (w.im / 3) * h3
    refine ⟨-2 * w.re, by nlinarith, ?_⟩
    apply Complex.ext <;>
      simp only [pow_one, Complex.re_ofReal_mul, Complex.im_ofReal_mul, ζ_re, ζ_im] <;>
      linarith
  have hC : RR w ζ = RR w (ζ ^ 2) → RR w 1 ≤ RR w ζ → w ∈ wall 0 := fun e f ↦
    (RR_eq_and_le_iff_mem_wall_zero w).1 ⟨e, f⟩
  have m1 := one_mem_VT
  have m2 := ζ_mem_VT
  have m3 := ζ_sq_mem_VT
  simp only [walls, Set.mem_union]
  rcases mem_VT.1 hu with rfl | rfl | rfl <;> rcases mem_VT.1 hv with rfl | rfl | rfl
  · exact absurd rfl huv
  · exact Or.inr (hA (le_antisymm (hmv 1 m1) (hmu ζ m2)) (hmu _ m3))
  · exact Or.inl (Or.inr (hB (le_antisymm (hmv 1 m1) (hmu _ m3)) (hmu ζ m2)))
  · exact Or.inr (hA (le_antisymm (hmu 1 m1) (hmv ζ m2)) (hmv _ m3))
  · exact absurd rfl huv
  · exact Or.inl (Or.inl (hC (le_antisymm (hmv ζ m2) (hmu _ m3)) (hmu 1 m1)))
  · exact Or.inl (Or.inr (hB (le_antisymm (hmu 1 m1) (hmv _ m3)) (hmv ζ m2)))
  · exact Or.inl (Or.inl (hC (le_antisymm (hmu ζ m2) (hmv _ m3)) (hmv 1 m1)))
  · exact absurd rfl huv

/-! ### The first control -/

/-- The first control is unique: two first controls of the same point coincide.

Proof: if `u ≠ u'` were both first controls, comparing the maximum conditions along the two
trajectories (`RR(u - u', z₃(t, z⁰, u)) ≥ 0 ≥ RR(u - u', z₃(t, z⁰, u'))` for small `t ≥ 0`) and
using `RR(u - u', -i(u - u')) = 0` forces all four Taylor coefficients of `RR(u - u', z₃(t, z⁰, u))`
to vanish, while its cubic coefficient is `RR(u - u', -iu)/6 = ±√3/12 ≠ 0`. -/
theorem IsFirstControl.unique {z : Fin 3 → ℂ} {u u' : ℂ} (hu : IsFirstControl z u)
    (hu' : IsFirstControl z u') : u = u' := by
  by_contra hne
  obtain ⟨huV, ε, hε, hmax⟩ := hu
  obtain ⟨hu'V, ε', hε', hmax'⟩ := hu'
  -- `RR(u' - u, z₃(t, z⁰, u))` vanishes for small `t ≥ 0`
  have hzero : ∀ t ∈ Icc 0 (min ε ε'), RR (u' - u) (flow t z u 2) = 0 := by
    intro t ht
    have h1 := hmax t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩ u' hu'V
    have h2 := hmax' t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩ u huV
    have e1 := l4c_ham_sub (flow t z u) u' u
    have e2 := l4c_ham_sub (flow t z u') u u'
    -- `z₃(t, z⁰, u) - z₃(t, z⁰, u') = i(t³/6)(u' - u)` and `RR(d, i c d) = 0`
    have hf : flow t z u 2 = flow t z u' 2 + I * ((t ^ 3 / 6 : ℝ) : ℂ) * (u' - u) := by
      simp [flow]; ring
    have key : RR (u' - u) (flow t z u 2) = -RR (u - u') (flow t z u' 2) := by
      have := l4c_RR_I_mul_self (u' - u) (t ^ 3 / 6)
      rw [hf]
      simp only [RR_eq_re_mul_add_im_mul, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im] at this ⊢
      linarith
    linarith
  -- its cubic coefficient `RR(u' - u, -iu)` is `±√3/2`
  have hcub : RR (u' - u) (-I * u) ≠ 0 := by
    have hn := norm_eq_one_of_mem_VT huV
    have h3 : 0 < √3 := by positivity
    rcases (l4c_mem_VT_iff huV).1 hu'V with rfl | rfl | rfl
    · exact absurd rfl hne
    · rw [l4c_RR_mul_ζ_sub hn]; linarith
    · rw [l4c_RR_mul_ζ_sq_sub hn]; linarith
  obtain ⟨t, ht, hne'⟩ := l4c_cubic_ne_zero (a := RR (u' - u) (z 2)) (b := RR (u' - u) (z 1))
    (c := RR (u' - u) (z 0) / 2) (div_ne_zero hcub (by norm_num : (6 : ℝ) ≠ 0))
    (lt_min hε hε')
  apply hne'
  have := hzero t ⟨ht.1.le, ht.2⟩
  rw [l4c_RR_flow] at this
  linear_combination this

private lemma l4c_conj_mem_VT {u : ℂ} : starRingEnd ℂ u ∈ VT ↔ u ∈ VT :=
  ⟨fun h ↦ by simpa using conj_mem_VT h, fun h ↦ conj_mem_VT h⟩

/-- Time reversal of the Hamiltonian along constant-control trajectories:
`H_F(z(s, τ(z⁰), ū), v̄) = H_F(z(-s, z⁰, u), v)` (`tau_flow_neg`, `ham_tau`). -/
private lemma l4c_ham_flow_tau (s : ℝ) (z : Fin 3 → ℂ) (u v : ℂ) :
    ham (flow s (tau z) (starRingEnd ℂ u)) (starRingEnd ℂ v) = ham (flow (-s) z u) v := by
  rw [← tau_flow_neg, ham_tau, Complex.conj_conj]

/-- `u` is the most recent control of `z⁰` if and only if `ū` is the first control of `τ(z⁰)`
(the time reversal, TeX 10891–10906). -/
private lemma l4c_isMostRecentControl_iff {z : Fin 3 → ℂ} {u : ℂ} :
    IsMostRecentControl z u ↔ IsFirstControl (tau z) (starRingEnd ℂ u) := by
  constructor
  · rintro ⟨hu, ε, hε, h⟩
    refine ⟨l4c_conj_mem_VT.2 hu, ε, hε, fun s hs v hv ↦ ?_⟩
    have := h (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ (starRingEnd ℂ v)
      (l4c_conj_mem_VT.2 hv)
    rwa [← l4c_ham_flow_tau, ← l4c_ham_flow_tau, Complex.conj_conj] at this
  · rintro ⟨hu, ε, hε, h⟩
    refine ⟨l4c_conj_mem_VT.1 hu, ε, hε, fun t ht v hv ↦ ?_⟩
    have := h (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ (starRingEnd ℂ v)
      (l4c_conj_mem_VT.2 hv)
    rwa [l4c_ham_flow_tau, l4c_ham_flow_tau, neg_neg] at this

/-- The most recent control is unique (the time reversal of `IsFirstControl.unique`). -/
private theorem l4st_isMostRecentControl_unique {z : Fin 3 → ℂ} {u u' : ℂ}
    (hu : IsMostRecentControl z u) (hu' : IsMostRecentControl z u') : u = u' := by
  have := IsFirstControl.unique (l4c_isMostRecentControl_iff.1 hu)
    (l4c_isMostRecentControl_iff.1 hu')
  simpa using congrArg (starRingEnd ℂ) this

/-! ### Helpers: `V_{T,max}` -/

/-- `V_{T,max}` is nonempty (the lexicographic order is a linear order). -/
private lemma l4c_lexMaxControls_nonempty (z : Fin 3 → ℂ) : ∃ u, u ∈ lexMaxControls z := by
  classical
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image ({1, ζ, ζ ^ 2} : Finset ℂ)
    (fun u ↦ toLex (controlVector z u)) ⟨1, by simp⟩
  have hmem : ∀ v, v ∈ ({1, ζ, ζ ^ 2} : Finset ℂ) ↔ v ∈ VT := fun v ↦ by simp [VT]
  refine ⟨u, (hmem u).1 hu, fun v hv hlt ↦ ?_⟩
  rw [l4c_lexLt_iff] at hlt
  exact absurd hlt (not_lt.2 (hmax v ((hmem v).2 hv)))

private lemma l4c_lexMaxControls_subset {z : Fin 3 → ℂ} : lexMaxControls z ⊆ VT :=
  fun _ hv ↦ hv.1

/-- Two elements of `V_{T,max}` have the same control vector ("if two vectors have the same
lexicographical order then the two vectors are equal"). -/
private lemma l4c_controlVector_eq {z : Fin 3 → ℂ} {u v : ℂ} (hu : u ∈ lexMaxControls z)
    (hv : v ∈ lexMaxControls z) : controlVector z u = controlVector z v := by
  have h1 := hu.2 v hv.1
  have h2 := hv.2 u hu.1
  rw [l4c_lexLt_iff] at h1 h2
  exact toLex.injective (le_antisymm (not_lt.1 h2) (not_lt.1 h1))

/-- A control outside `V_{T,max}` has a control vector below that of any element of `V_{T,max}`. -/
private lemma l4c_lexLt_of_notMem {z : Fin 3 → ℂ} {u v : ℂ} (hu : u ∈ lexMaxControls z)
    (hv : v ∈ VT) (hvm : v ∉ lexMaxControls z) : LexLt (controlVector z v) (controlVector z u) := by
  have : ∃ w ∈ VT, LexLt (controlVector z v) (controlVector z w) := by
    by_contra h
    push Not at h
    exact hvm ⟨hv, h⟩
  obtain ⟨w, hw, hlt⟩ := this
  have := hu.2 w hw
  rw [l4c_lexLt_iff] at hlt this ⊢
  exact lt_of_lt_of_le hlt (not_lt.1 this)

/-- Steps 2–3 of the proof of Lemma 13.2.6: if `u ∈ V_{T,max}` and the only other possible element
of `V_{T,max}` is `uζ`, then `u` is the first control. A control outside `V_{T,max}` is beaten by
a lower-order term of the switching function (step 2); if `uζ ∈ V_{T,max}`, the first three
coefficients of the switching function vanish and the cubic one,
`RR(uζ - u, -iu)/6 = -√3/12 < 0`, decides (step 3; `RR(ua, ub) = RR(a, b)` replaces the book's
rotation to `u = 1`). -/
private lemma l4c_isFirstControl_of_mem {z : Fin 3 → ℂ} {u : ℂ} (hu : u ∈ lexMaxControls z)
    (hnext : ∀ v ∈ lexMaxControls z, v ≠ u → v = u * ζ) : IsFirstControl z u := by
  have huV : u ∈ VT := hu.1
  have hn := norm_eq_one_of_mem_VT huV
  have hall : ∀ v ∈ VT, ∃ ε > 0, ∀ t ∈ Icc 0 ε, ham (flow t z u) v ≤ ham (flow t z u) u := by
    intro v hv
    by_cases hvm : v ∈ lexMaxControls z
    · by_cases hvu : v = u
      · exact ⟨1, one_pos, fun t _ ↦ hvu ▸ le_rfl⟩
      · have hv' := hnext v hvm hvu
        have hcv := l4c_controlVector_eq hvm hu
        obtain ⟨h0, h1, h2⟩ := controlVector_sub_apply z v u
        rw [hcv, sub_self, Pi.zero_apply] at h0 h1 h2
        refine ⟨1, one_pos, fun t ht ↦ ?_⟩
        have e := ham_flow_sub_ham_flow t z u v u
        rw [← h0, ← h1, ← h2, hv', l4c_RR_mul_ζ_sub hn] at e
        have : 0 ≤ t ^ 3 := pow_nonneg ht.1 3
        have h3 : 0 < √3 := by positivity
        rw [hv']
        nlinarith
    · obtain ⟨ε, hε, h, -⟩ := l4c_eventually_of_lexLt (l4c_lexLt_of_notMem hu hv hvm) u
      exact ⟨ε, hε, h⟩
  obtain ⟨ε, hε, h⟩ := l4c_exists_eps_VT
    (P := fun v ε ↦ ∀ t ∈ Icc 0 ε, ham (flow t z u) v ≤ ham (flow t z u) u)
    (fun v ε ε' hle h t ht ↦ h t ⟨ht.1, ht.2.trans hle⟩) hall
  exact ⟨huV, ε, hε, fun t ht v hv ↦ h v hv t ht⟩

/-- The first control lies in `V_T` (the junk value `1` too). -/
theorem firstControl_mem_VT (z : Fin 3 → ℂ) : firstControl z ∈ VT := by
  unfold firstControl
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_mem_VT

/-- `u ζ²` eventually beats `u` along `t ↦ z(t, z⁰, u)`: the cubic coefficient of the switching
function from `u` to `u/ζ = uζ²` is `RR(uζ² - u, -iu)/6 = √3/12 > 0`. So the set defining the
first switching time is nonempty. -/
private lemma l4c_switch_exists (z : Fin 3 → ℂ) {u : ℂ} (hu : u ∈ VT) :
    ∃ t > 0, ham (flow t z u) u < ham (flow t z u) (u * ζ ^ 2) := by
  obtain ⟨T, hT, h⟩ := l4c_cubic_pos_somewhere (a := RR (u * ζ ^ 2 - u) (z 2))
    (b := RR (u * ζ ^ 2 - u) (z 1)) (c := RR (u * ζ ^ 2 - u) (z 0) / 2)
    (d := RR (u * ζ ^ 2 - u) (-I * u) / 6)
    (by rw [l4c_RR_mul_ζ_sq_sub (norm_eq_one_of_mem_VT hu)]; positivity)
  refine ⟨T, hT, ?_⟩
  have := ham_flow_sub_ham_flow T z u (u * ζ ^ 2) u
  linarith

/-- The set defining the first switching time is nonempty and bounded below by `0`. -/
private lemma l4c_switchSet (z : Fin 3 → ℂ) :
    BddBelow {t : ℝ | 0 < t ∧ ∃ v ∈ VT,
      ham (flow t z (firstControl z)) (firstControl z) < ham (flow t z (firstControl z)) v} ∧
    {t : ℝ | 0 < t ∧ ∃ v ∈ VT,
      ham (flow t z (firstControl z)) (firstControl z) <
        ham (flow t z (firstControl z)) v}.Nonempty := by
  have hu := firstControl_mem_VT z
  obtain ⟨T, hT, h⟩ := l4c_switch_exists z hu
  exact ⟨⟨0, fun t ht ↦ ht.1.le⟩, T, hT, _, mul_mem_VT hu ζ_sq_mem_VT, h⟩

end TriFuller

/-- **Lemma 13.2.6** (`lem:first-control`, TeX 10955–11009). Let `z⁰ ∈ ℂ³ ∖ 0` and let
`V_{T,max} ⊆ V_T` be the set of controls whose control vectors `v(z⁰, u)` are maximal in the
lexicographic order. Then
* if `V_{T,max} = {u}`, then `u` is the first control;
* if `V_{T,max} = {ζ^i, ζ^{i+1}}` has two elements, then the first control is `ζ^i`;
* `V_{T,max} ≠ V_T`.

Proof. Step 1 is the book's:
1. Two vectors that are equal in the lexicographic order are equal; if `V_{T,max} = V_T`, the
   three control vectors are equal, `RR(z_j⁰, 1) = RR(z_j⁰, ζ) = RR(z_j⁰, ζ²)`, and
   `1 + ζ + ζ² = 0` (the three vertices span `ℂ` over `ℝ`) forces `z⁰ = 0`.
   (In coordinates: `RR(w, 1) = RR(w, ζ) = RR(w, ζ²)` forces `w = 0`.)

Departure from the paper (the direction of steps 2–3). The book's argument (TeX 10978–10995)
proves the *necessary* direction: the first control, if it exists, maximizes the lexicographic
order ("In this way, the first control must maximize the lexicographical order"), and in the tie
case `V_{T,max} = {ζ^i, ζ^{i+1}}` it cannot be `ζ^{i+1}` (by contradiction, from the sign of the
cubic term). The statement asserts the *sufficient* direction, that the lexicographic maximizer
`u` is the first control, which in the semantic sense of `IsFirstControl` means that the constant
control `u` is optimal along its own trajectory on some `[0, ε]`; the book never shows this. The
formalization proves it from the same Taylor expansion:
2. The switching function `RR(u - v, z₃(t, z⁰, u))`, with
   `z₃(t) = z₃⁰ + z₂⁰ t + z₁⁰ t²/2 - iut³/6` (13.2.2), has the Taylor coefficients
   `RR(z₃⁰, u - v)`, `RR(z₂⁰, u - v)`, `RR(z₁⁰, u - v)/2`, `RR(-iu, u - v)/6`, and its sign for
   small `t > 0` is the sign of the first nonzero one. If `V_{T,max} = {u}`, for each `v ≠ u` the
   first nonzero coefficient among the first three is positive (`v(z⁰, v) ≺ v(z⁰, u)`), so `u`
   maximizes on some `[0, ε]`.
3. If `V_{T,max} = {ζ^i, ζ^{i+1}}`, the first three coefficients for the pair vanish and the cubic
   one decides: with the control `ζ^i`, `RR(-iζ^i t³/3!, ζ^i - ζ^{i+1}) = t³/(4√3) > 0`, so `ζ^i`
   maximizes on some `[0, ε]` (the third control is beaten as in step 2). The book's rotation to
   `i = 0` (Lemma 13.2.2, (13.2.7)) is done inside the computation, by `RR(ua, ub) = RR(a, b)` for
   `|u| = 1`: `RR(-iζ^i, ζ^i - ζ^{i+1}) = RR(-i, 1 - ζ)`.

Steps 2–3 are the private lemma `l4c_isFirstControl_of_mem`. The book's necessary direction is
`firstControl_mem_lexMaxControls` (and the local uniqueness of extremals, `l4d_local_unique` in
`SmoothedPolygons/Ch13/Extremals.lean`), and the uniqueness of the first control is proved
generically (`IsFirstControl.unique`). -/
theorem lemma13_2_6 {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    (∀ u : ℂ, lexMaxControls z = {u} → IsFirstControl z u) ∧
      (∀ i : ℕ, lexMaxControls z = {ζ ^ i, ζ ^ (i + 1)} → IsFirstControl z (ζ ^ i)) ∧
      lexMaxControls z ≠ VT := by
  refine ⟨fun u h ↦ ?_, fun i h ↦ ?_, fun h ↦ ?_⟩
  · -- step 2: `u` beats the other two controls by a lower-order term
    refine l4c_isFirstControl_of_mem (by rw [h]; rfl) fun v hv hvu ↦ ?_
    rw [h] at hv
    exact absurd hv hvu
  · -- step 3: the tie between `ζ^i` and `ζ^{i+1}` is broken by the cubic term
    refine l4c_isFirstControl_of_mem (by rw [h]; exact Or.inl rfl) fun v hv hvu ↦ ?_
    rw [h] at hv
    rcases hv with rfl | hv
    · exact absurd rfl hvu
    · rw [Set.mem_singleton_iff.1 hv, pow_succ]
  · -- step 1: if the three control vectors are equal, then `z⁰ = 0`
    apply hz
    have hmem : ∀ v ∈ VT, v ∈ lexMaxControls z := fun v hv ↦ h ▸ hv
    have e1 := l4c_controlVector_eq (hmem 1 one_mem_VT) (hmem ζ ζ_mem_VT)
    have e2 := l4c_controlVector_eq (hmem 1 one_mem_VT) (hmem _ ζ_sq_mem_VT)
    have key : ∀ w : ℂ, RR w 1 = RR w ζ → RR w 1 = RR w (ζ ^ 2) → w = 0 := by
      intro w f g
      simp only [RR_eq_re_mul_add_im_mul, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, Complex.one_re,
        Complex.one_im] at f g
      have h3 : 0 < √3 := by positivity
      have hy : w.im = 0 := by
        have : w.im * √3 = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_right h3.ne'
      apply Complex.ext
      · rw [hy] at f; rw [Complex.zero_re]; linarith
      · simpa using hy
    funext j
    fin_cases j
    · exact key _ (by simpa [controlVector] using congrFun e1 2)
        (by simpa [controlVector] using congrFun e2 2)
    · exact key _ (by simpa [controlVector] using congrFun e1 1)
        (by simpa [controlVector] using congrFun e2 1)
    · exact key _ (by simpa [controlVector] using congrFun e1 0)
        (by simpa [controlVector] using congrFun e2 0)

namespace TriFuller

/-- Every `z⁰ ≠ 0` has a first control (Lemma 13.2.6: `V_{T,max}` is nonempty, and it is a
singleton or a pair `{ζ^i, ζ^{i+1}}` since it is not `V_T`). -/
private theorem l4st_exists_isFirstControl {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    ∃ u, IsFirstControl z u := by
  obtain ⟨ha, hb, hc⟩ := lemma13_2_6 hz
  obtain ⟨u, hu⟩ := l4c_lexMaxControls_nonempty z
  have hVT := fun v ↦ l4c_mem_VT_iff hu.1 (v := v)
  obtain ⟨i, rfl⟩ := l4c_exists_pow_of_mem_VT hu.1
  have h3 : ζ ^ i * ζ ^ 2 * ζ = ζ ^ i := by
    rw [mul_assoc, ← pow_succ, ζ_pow_three, mul_one]
  by_cases h1 : ζ ^ i * ζ ∈ lexMaxControls z <;> by_cases h2 : ζ ^ i * ζ ^ 2 ∈ lexMaxControls z
  · -- `V_{T,max} = V_T`, excluded
    refine absurd (Set.Subset.antisymm l4c_lexMaxControls_subset fun v hv ↦ ?_) hc
    rcases (hVT v).1 hv with rfl | rfl | rfl <;> assumption
  · -- `V_{T,max} = {ζ^i, ζ^{i+1}}`
    refine ⟨_, hb i (Set.ext fun v ↦ ⟨fun hv ↦ ?_, ?_⟩)⟩
    · rcases (hVT v).1 hv.1 with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (pow_succ ζ i).symm
      · exact absurd hv h2
    · rintro (rfl | hv)
      · exact hu
      · rw [Set.mem_singleton_iff.1 hv, pow_succ]; exact h1
  · -- `V_{T,max} = {ζ^{i+2}, ζ^{i+3}}`
    refine ⟨_, hb (i + 2) (Set.ext fun v ↦ ⟨fun hv ↦ ?_, ?_⟩)⟩
    · rcases (hVT v).1 hv.1 with rfl | rfl | rfl
      · exact Or.inr (by rw [pow_succ, pow_add, h3]; exact Set.mem_singleton _)
      · exact absurd hv h1
      · exact Or.inl (pow_add ζ i 2).symm
    · rintro (rfl | hv)
      · rw [pow_add]; exact h2
      · rw [Set.mem_singleton_iff.1 hv, pow_succ, pow_add, h3]; exact hu
  · -- `V_{T,max} = {ζ^i}`
    refine ⟨ζ ^ i, ha (ζ ^ i) (Set.ext fun v ↦ ⟨fun hv ↦ ?_, ?_⟩)⟩
    · rcases (hVT v).1 hv.1 with rfl | rfl | rfl
      · exact Set.mem_singleton _
      · exact absurd hv h1
      · exact absurd hv h2
    · rintro rfl; exact hu

/-- For `z⁰ ≠ 0`, `firstControl z⁰` is the first control of `z⁰`. -/
theorem isFirstControl_firstControl {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    IsFirstControl z (firstControl z) := by
  have h := l4st_exists_isFirstControl hz
  rw [firstControl, dite_eq_left h]
  exact h.choose_spec

/-- For `z⁰ ≠ 0`, `firstControl z⁰ = u` if and only if `u` is the first control of `z⁰`. -/
theorem firstControl_eq_iff {z : Fin 3 → ℂ} (hz : z ≠ 0) {u : ℂ} :
    firstControl z = u ↔ IsFirstControl z u :=
  ⟨fun h ↦ h ▸ isFirstControl_firstControl hz,
    fun h ↦ IsFirstControl.unique (isFirstControl_firstControl hz) h⟩

/-- "In this way, the first control must maximize the lexicographical order" (TeX 10990–10991):
the first control of `z⁰ ≠ 0` lies in `V_{T,max}`. -/
theorem firstControl_mem_lexMaxControls {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    firstControl z ∈ lexMaxControls z := by
  obtain ⟨huV, ε, hε, hmax⟩ := isFirstControl_firstControl hz
  refine ⟨huV, fun v hv hlt ↦ ?_⟩
  -- a control with a larger control vector would beat the first control for small `t > 0`
  obtain ⟨ε', hε', -, hlt'⟩ := l4c_eventually_of_lexLt hlt (firstControl z)
  exact absurd (hmax _ ⟨(lt_min hε hε').le, min_le_left _ _⟩ v hv)
    (not_le.2 (hlt' _ ⟨lt_min hε hε', min_le_right _ _⟩))

/-- For `z⁰ ≠ 0`, `t = 0` is not a limit of switching times: `t_sw > 0` (TeX 10750–10753). -/
theorem firstSwitchTime_pos {z : Fin 3 → ℂ} (hz : z ≠ 0) : 0 < firstSwitchTime z := by
  obtain ⟨-, ε, hε, hmax⟩ := isFirstControl_firstControl hz
  refine hε.trans_le (le_csInf (l4c_switchSet z).2 ?_)
  rintro t ⟨ht, v, hv, hlt⟩
  by_contra! hle
  exact absurd (hmax t ⟨ht.le, hle.le⟩ v hv) (not_le.2 hlt)

/-- The first control is optimal along its trajectory on the closed interval `[0, t_sw]`. -/
theorem firstControl_maximizes {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    ∀ t ∈ Icc 0 (firstSwitchTime z), ∀ v ∈ VT,
      ham (flow t z (firstControl z)) v ≤ ham (flow t z (firstControl z)) (firstControl z) := by
  obtain ⟨-, ε, hε, hmax⟩ := isFirstControl_firstControl hz
  have hpos := firstSwitchTime_pos hz
  intro t ht v hv
  -- on `[0, t_sw)` by the definition of `t_sw`, then at `t_sw` by continuity
  have hIco : Ico 0 (firstSwitchTime z) ⊆ {s | ham (flow s z (firstControl z)) v -
      ham (flow s z (firstControl z)) (firstControl z) ≤ 0} := by
    intro s hs
    simp only [Set.mem_ofPred_eq, sub_nonpos]
    rcases hs.1.eq_or_lt with rfl | hs0
    · exact hmax 0 ⟨le_rfl, hε.le⟩ v hv
    · by_contra! hlt
      exact notMem_of_lt_csInf hs.2 (l4c_switchSet z).1 ⟨hs0, v, hv, hlt⟩
  have hcl := (isClosed_le (l4c_continuous_ham_flow_sub z _ v _)
    continuous_const).closure_subset_iff.2 hIco
  rw [closure_Ico hpos.ne] at hcl
  simpa [sub_nonpos] using hcl ht

/-- The trajectory switches at `t_sw`: the first control is beaten at times arbitrarily close to
`t_sw` from the right (in fact on a whole interval `(t_sw, t_sw + ε)`, the switching functions
being polynomials). -/
theorem firstControl_beaten {z : Fin 3 → ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ Ioo (firstSwitchTime z) (firstSwitchTime z + ε), ∃ v ∈ VT,
      ham (flow t z (firstControl z)) (firstControl z) < ham (flow t z (firstControl z)) v := by
  obtain ⟨hbdd, hne⟩ := l4c_switchSet z
  obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right (firstSwitchTime z) hε)
  have hle : firstSwitchTime z ≤ s := csInf_le hbdd hs
  rcases hle.eq_or_lt with heq | hlt
  · -- at `t_sw` itself the first control is still optimal
    obtain ⟨-, v, hv, hlt'⟩ := hs
    have := firstControl_maximizes hz s ⟨(firstSwitchTime_pos hz).le.trans hle,
      heq ▸ le_rfl⟩ v hv
    exact absurd hlt' (not_lt.2 this)
  · exact ⟨s, ⟨hlt, hslt⟩, hs.2⟩

/-- **The first-control trajectory does not reach the singular locus up to `t_sw`**: for
`z⁰ ≠ 0` with first control `u₀` and `t ∈ [0, t_sw]`, `z(t, z⁰, u₀) ≠ 0`. (Lemma 13.3.1,
`lemma13_3_1`, gives `z(t) ≠ 0` for every `t`, but only when `z₃⁰ ∈ 𝒲`; here `z₃⁰` is arbitrary.)

Proof route: `z(0, z⁰, u₀) = z⁰ ≠ 0` (`flow_zero`). Suppose `z(S, z⁰, u₀) = 0` with
`0 < S ≤ t_sw`. By the flow property (`flow_add`), `z(t, z⁰, u₀) = z(t - S, 0, u₀)`, whose
third coordinate is `-iu₀(t - S)³/6` by (13.2.2). The control `u₀ζ` lies in `V_T`
(`isFirstControl_firstControl`, `mul_mem_VT`), and
`H_F(z(t), u₀ζ) - H_F(z(t), u₀) = RR(u₀ζ - u₀, -iu₀(t - S)³/6) = -(√3/12)(t - S)³`
(`|u₀| = 1` and `RR(ζ - 1, -i) = -√3/2`), which is `> 0` for `t < S`: `u₀ζ` strictly beats `u₀` at
every `t ∈ (0, S) ⊆ [0, t_sw]`, against `firstControl_maximizes`. -/
theorem flow_firstControl_ne_zero {z : Fin 3 → ℂ} (hz : z ≠ 0) {t : ℝ}
    (ht : t ∈ Icc 0 (firstSwitchTime z)) : flow t z (firstControl z) ≠ 0 := by
  intro h0
  rcases ht.1.eq_or_lt with rfl | hS
  · exact hz (by rw [← flow_zero z (firstControl z)]; exact h0)
  · -- at `t/2 ∈ (0, S)`, `z(t/2) = z(-t/2, 0, u₀)` and `u₀ζ` strictly beats `u₀`
    have huV := firstControl_mem_VT z
    have hn := norm_eq_one_of_mem_VT huV
    have hflow : flow (t / 2) z (firstControl z) = flow (-(t / 2)) 0 (firstControl z) := by
      have := flow_add t (-(t / 2)) z (firstControl z)
      rwa [h0, show t + -(t / 2) = t / 2 by ring] at this
    have hmax := firstControl_maximizes hz (t / 2) ⟨by linarith, by linarith [ht.2]⟩
      (firstControl z * ζ) (mul_mem_VT huV ζ_mem_VT)
    rw [hflow] at hmax
    have e := ham_flow_sub_ham_flow (-(t / 2)) 0 (firstControl z) (firstControl z * ζ)
      (firstControl z)
    rw [l4c_RR_mul_ζ_sub hn] at e
    simp only [Pi.zero_apply, RR_eq_re_mul_add_im_mul, Complex.zero_re, Complex.zero_im, mul_zero,
      add_zero, zero_mul, zero_add] at e
    have h3 : 0 < √3 := by positivity
    have : 0 < (t / 2) ^ 3 := by positivity
    nlinarith

end TriFuller

/-- **Corollary 13.2.7** (`cor:10`, TeX 11011–11045). Let `z ∈ ℂ³ ∖ 0` satisfy `|z_i| ≤ r^i` for
`i = 1, 2, 3`, and let `u` be the first control. Then the switching function from `u` to `u/ζ`
has a positive root less than `10r`. In particular, the first switching time `t_sw` is less than
`10r`.

Proof (the book's): by rotation (Lemma 13.2.2) take `u = ζ`.
1. Claim: `v(z, ζ) ≻ v(z, 1)` strictly. It is `⪰` because `ζ` is the first control
   (`firstControl_mem_lexMaxControls`); if the vectors were equal, `V_{T,max} = {1, ζ}` by
   Lemma 13.2.6 (c), and Lemma 13.2.6 (b) would make `1` the first control
   (`IsFirstControl.unique`).
2. `√3 χ(t) = RR(ζ - 1, z₃(t)) = -t³/(4√3) + Σ_{k=0}^{2} RR(ζ - 1, z_{3-k}) t^k/k!`: the leading
   coefficient is negative and, by the claim, the lowest nonzero coefficient is positive, so there
   is a positive root (intermediate value theorem).
3. For `t ≥ 10r`, `t⁻³ Σ_{k=0}^{2} |RR(ζ - 1, z_{3-k})| t^k/k! ≤ √3 Σ 10^{k-3}/k! < 1/(4√3)`
   (`|ζ - 1| = √3`, `|z_{3-k}| ≤ r^{3-k}`; the book's first `<` should be `≤`, and the final strict
   inequality `0.0611·√3 < 1/(4√3)` holds), so `χ(t) < 0`: the root is below `10r`, and `χ < 0`
   near `10r` makes `u/ζ` beat `u` before `10r`, so `t_sw < 10r`.

In the formalization, the reduction to `u = ζ` is done inside the computations (`u/ζ = uζ²` and
`RR(ua, ub) = RR(a, b)` for `|u| = 1`); the bound of step 3 is used at `t = 10r`, where it gives
`χ(10r) < 0`; the root is found in `(t₀, 10r)` by the intermediate value theorem, `t₀` a small
time with `χ(t₀) > 0`; and `t_sw < 10r` because `u/ζ` beats `u` at `10r` (so `t_sw ≤ 10r`) while
`u` is still optimal at `t_sw` (`firstControl_maximizes`). -/
theorem corollary13_2_7 {z : Fin 3 → ℂ} (hz : z ≠ 0) {r : ℝ} (h₁ : ‖z 0‖ ≤ r)
    (h₂ : ‖z 1‖ ≤ r ^ 2) (h₃ : ‖z 2‖ ≤ r ^ 3) {u : ℂ} (hu : IsFirstControl z u) :
    (∃ t, 0 < t ∧ t < 10 * r ∧ switchingFunction u (u - u / ζ) t z = 0) ∧
      firstSwitchTime z < 10 * r := by
  have huV := hu.1
  have hn := norm_eq_one_of_mem_VT huV
  have hu0 : u ≠ 0 := by rintro rfl; simp at hn
  have hfc : firstControl z = u := (firstControl_eq_iff hz).2 hu
  have hdiv : u / ζ = u * ζ ^ 2 := by
    rw [div_eq_iff l4c_ζ_ne_zero, mul_assoc, ← pow_succ, ζ_pow_three, mul_one]
  have hwV : u / ζ ∈ VT := hdiv ▸ mul_mem_VT huV ζ_sq_mem_VT
  have hmaxu : u ∈ lexMaxControls z := hfc ▸ firstControl_mem_lexMaxControls hz
  -- the claim: `v(z, u/ζ) ≺ v(z, u)` strictly
  have hclaim : LexLt (controlVector z (u / ζ)) (controlVector z u) := by
    have hle := hmaxu.2 (u / ζ) hwV
    rw [l4c_lexLt_iff] at hle ⊢
    rcases (not_lt.1 hle).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      -- otherwise `V_{T,max} = {u/ζ, u}` and Lemma 13.2.6 makes `u/ζ` the first control
      have heq' : controlVector z (u / ζ) = controlVector z u := toLex.injective heq
      have hwmax : u / ζ ∈ lexMaxControls z :=
        ⟨hwV, fun v hv ↦ by rw [heq']; exact hmaxu.2 v hv⟩
      obtain ⟨-, hb, hc⟩ := lemma13_2_6 hz
      obtain ⟨i, hi⟩ := l4c_exists_pow_of_mem_VT hwV
      have hi1 : ζ ^ (i + 1) = u := by rw [pow_succ, ← hi, div_mul_cancel₀ _ l4c_ζ_ne_zero]
      have hset : lexMaxControls z = {ζ ^ i, ζ ^ (i + 1)} := by
        ext v
        refine ⟨fun hv ↦ ?_, ?_⟩
        · rcases (l4c_mem_VT_iff huV).1 hv.1 with rfl | rfl | rfl
          · exact Or.inr hi1.symm
          · refine absurd (Set.Subset.antisymm l4c_lexMaxControls_subset fun x hx ↦ ?_) hc
            rcases (l4c_mem_VT_iff huV).1 hx with rfl | rfl | rfl
            · exact hmaxu
            · exact hv
            · exact hdiv ▸ hwmax
          · exact Or.inl (by rw [← hdiv, hi])
        · rintro (rfl | hv)
          · rw [← hi]; exact hwmax
          · rw [Set.mem_singleton_iff.1 hv, hi1]; exact hmaxu
      have := IsFirstControl.unique (hb i hset) hu
      rw [← hi, div_eq_iff l4c_ζ_ne_zero] at this
      exact ζ_ne_one (mul_left_cancel₀ hu0 (this.symm.trans (mul_one u).symm))
  -- `r > 0`
  have hr : 0 < r := by
    rcases ((norm_nonneg (z 0)).trans h₁).eq_or_lt with h | h
    · subst h
      refine absurd (funext fun j ↦ ?_) hz
      fin_cases j
      · exact norm_le_zero_iff.1 h₁
      · exact norm_le_zero_iff.1 (by simpa using h₂)
      · exact norm_le_zero_iff.1 (by simpa using h₃)
    · exact h
  -- `√3 χ(t) = H_F(z(t), u) - H_F(z(t), u/ζ)`
  have hχ : ∀ t, switchingFunction u (u - u / ζ) t z =
      (ham (flow t z u) u - ham (flow t z u) (u / ζ)) / √3 := fun t ↦ by
    rw [switchingFunction, l4c_ham_sub]
  -- the lowest nonzero coefficient is positive: `χ > 0` on some `(0, ε]`
  obtain ⟨ε, hε, -, hpos⟩ := l4c_eventually_of_lexLt hclaim u
  -- the bound on the lower-order terms: `χ(10r) < 0`
  have hneg : ham (flow (10 * r) z u) u < ham (flow (10 * r) z u) (u / ζ) := by
    have hd : ‖u / ζ - u‖ = √3 := by
      have hnorm : ‖ζ ^ 2 - 1‖ = √3 := by
        rw [Complex.norm_def, Complex.normSq_apply]
        congr 1
        simp only [Complex.sub_re, Complex.sub_im, ζ_sq_re, ζ_sq_im, Complex.one_re,
          Complex.one_im]
        linear_combination (1 / 4 : ℝ) * l4c_sqrt3_mul_self
      rw [hdiv, show u * ζ ^ 2 - u = u * (ζ ^ 2 - 1) by ring, norm_mul, hn, one_mul, hnorm]
    have hbound : ∀ w : ℂ, -(√3 * ‖w‖) ≤ RR (u / ζ - u) w := by
      intro w
      have h1 : |RR (u / ζ - u) w| ≤ ‖u / ζ - u‖ * ‖w‖ := by
        rw [RR]
        calc |(starRingEnd ℂ (u / ζ - u) * w).re| ≤ ‖starRingEnd ℂ (u / ζ - u) * w‖ :=
              Complex.abs_re_le_norm _
          _ = ‖u / ζ - u‖ * ‖w‖ := by rw [norm_mul, Complex.norm_conj]
      rw [hd] at h1
      linarith [neg_abs_le (RR (u / ζ - u) w)]
    have hcub : RR (u / ζ - u) (-I * u) = √3 / 2 := by rw [hdiv, l4c_RR_mul_ζ_sq_sub hn]
    have e := ham_flow_sub_ham_flow (10 * r) z u (u / ζ) u
    rw [hcub] at e
    have h3 : 0 ≤ √3 := Real.sqrt_nonneg 3
    have hA : -(√3 * r ^ 3) ≤ RR (u / ζ - u) (z 2) :=
      (neg_le_neg (mul_le_mul_of_nonneg_left h₃ h3)).trans (hbound _)
    have hB : -(√3 * r ^ 2) * (10 * r) ≤ RR (u / ζ - u) (z 1) * (10 * r) :=
      mul_le_mul_of_nonneg_right ((neg_le_neg (mul_le_mul_of_nonneg_left h₂ h3)).trans
        (hbound _)) (by positivity)
    have hC : -(√3 * r) * (10 * r) ^ 2 ≤ RR (u / ζ - u) (z 0) * (10 * r) ^ 2 :=
      mul_le_mul_of_nonneg_right ((neg_le_neg (mul_le_mul_of_nonneg_left h₁ h3)).trans
        (hbound _)) (by positivity)
    have hpos3 : 0 < √3 * r ^ 3 := by positivity
    nlinarith
  constructor
  · -- a positive root below `10r`, by the intermediate value theorem
    set t₀ := min ε (5 * r)
    have ht₀ : 0 < t₀ := lt_min hε (by linarith)
    have h₀ := hpos t₀ ⟨ht₀, min_le_left _ _⟩
    have hcont : ContinuousOn (fun t ↦ switchingFunction u (u - u / ζ) t z) (Icc t₀ (10 * r)) := by
      simp_rw [hχ]
      exact ((l4c_continuous_ham_flow_sub z u u (u / ζ)).div_const _).continuousOn
    have h3 : 0 < √3 := by positivity
    have hf1 : switchingFunction u (u - u / ζ) (10 * r) z ≤ 0 := by
      rw [hχ]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) h3.le
    have hf2 : 0 ≤ switchingFunction u (u - u / ζ) t₀ z := by
      rw [hχ]; exact div_nonneg (by linarith) h3.le
    obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc' (by linarith [min_le_right ε (5 * r)]) hcont
      ⟨hf1, hf2⟩
    replace ht0 : switchingFunction u (u - u / ζ) t z = 0 := ht0
    refine ⟨t, ht₀.trans_le ht.1, lt_of_le_of_ne ht.2 ?_, ht0⟩
    rintro rfl
    rw [hχ, div_eq_zero_iff] at ht0
    rcases ht0 with h | h
    · linarith
    · exact h3.ne' h
  · -- `u/ζ` beats `u` at `10r`, so `t_sw ≤ 10r`, and `u` is still optimal at `t_sw`
    have hS : 10 * r ∈ {t : ℝ | 0 < t ∧ ∃ v ∈ VT,
        ham (flow t z (firstControl z)) (firstControl z) <
          ham (flow t z (firstControl z)) v} := ⟨by positivity, u / ζ, hwV, by rw [hfc]; exact hneg⟩
    have hle : firstSwitchTime z ≤ 10 * r := csInf_le (l4c_switchSet z).1 hS
    refine lt_of_le_of_ne hle fun heq ↦ ?_
    have := firstControl_maximizes hz (10 * r) ⟨by positivity, heq.ge⟩ (u / ζ) hwV
    rw [hfc] at this
    exact absurd hneg (not_lt.2 this)

set_option linter.unusedVariables false in
/-- **Lemma 13.2.8** (`lem:switching-antisymmetry`, label of this formalization; unlabelled, TeX
11047–11061). Fix `z⁰ ∈ ℂ³ ∖ 0` with `z₃⁰ ∈ ℝ_{≤0}`, the wall between the control modes `ζ` and
`ζ²`. Then the switching functions with initial condition `z⁰`
at `t = 0` satisfy `χ_{ζ,ζ²}(t) + χ_{ζ²,ζ}(t) = 0` for all `t`, where `χ_{ij} = χ^i_{ij}` is
computed with its own control.

Proof (book: "an easy computation"): the two cubics differ only in their `t³` terms, and the sum is
`(1/√3) RR(ζ - ζ², -i(ζ - ζ²)) t³/6 = 0`. The hypotheses `z⁰ ≠ 0` and `z₃⁰ ∈ ℝ_{≤0}` are not used
(the identity holds for every `z⁰`; REPORT.md, E64 and Section 5); the statement is kept as
printed. -/
theorem lemma13_2_8 {z : Fin 3 → ℂ} (hz : z ≠ 0) (h₃ : z 2 ∈ wall 0) (t : ℝ) :
    switchingFunction ζ (ζ - ζ ^ 2) t z + switchingFunction (ζ ^ 2) (ζ ^ 2 - ζ) t z = 0 := by
  -- the two cubics differ only in their `t³` terms, and `RR(d, -i c d) = 0`
  have key : ∀ a b : ℂ, RR (a - b) (flow t z a 2) + RR (b - a) (flow t z b 2) = 0 := by
    intro a b
    have := l4c_RR_I_mul_self (a - b) (-(t ^ 3 / 6))
    simp only [RR_eq_re_mul_add_im_mul] at this ⊢
    simp only [flow, Matrix.cons_val, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at this ⊢
    simp [pow_succ] at this ⊢
    nlinarith [this]
  simp only [switchingFunction]
  rw [← add_div, key, zero_div]

/-- **Lemma 13.2.5** (`lem:first-negative-control`, TeX 10891–10906). For each `t ∈ ℝ`,
`τ(z(-t, z⁰, u)) = z(t, τ(z⁰), ū)`. Also, the most recent control of `z⁰` is `u` if `ū` is the
first control of `τ(z⁰)`. Moreover, the most recent switching time for the initial condition
`z⁰ ∈ ℂ³ ∖ 0` is `-t_sw`, where `t_sw` is the first positive switching time of `τ(z⁰)`.

Proof (book: "follows from the time-reversal symmetry (Lemma 13.2.3)"): the first identity is
`tau_flow_neg` (a polynomial identity). With `H_F(τ w, v) = H_F(w, v̄)` (`ham_tau`) and
`conj V_T = V_T`, the maximum condition for `ū` along `s ↦ z(s, τ(z⁰), ū)` on `[0, ε]` is the
maximum condition for `u` along `t ↦ z(t, z⁰, u)` on `[-ε, 0]`, which gives the second assertion;
with the uniqueness of the first and most recent controls
(`IsFirstControl.unique`, `l4st_isMostRecentControl_unique`) and the existence of the first
control of `τ(z⁰) ≠ 0` (Lemma 13.2.6), the sets defining `mostRecentSwitchTime z⁰` and
`firstSwitchTime (τ z⁰)` are opposite, which gives the third.

Departure from the paper (route): Lemma 13.2.3 (`lemma13_2_3`) is about solutions with
`H_F = 0` (13.2.6), and Lemma 13.2.5 concerns every `z⁰` (the Hamiltonian need not vanish), so the
proof uses the substitution behind Lemma 13.2.3 (`tau_flow_neg`, `ham_tau`) for
constant controls instead of the lemma itself. -/
theorem lemma13_2_5 :
    (∀ (t : ℝ) (z : Fin 3 → ℂ) (u : ℂ), tau (flow (-t) z u) = flow t (tau z) (starRingEnd ℂ u)) ∧
      (∀ (z : Fin 3 → ℂ) (u : ℂ), IsFirstControl (tau z) (starRingEnd ℂ u) →
        IsMostRecentControl z u) ∧
      ∀ z : Fin 3 → ℂ, z ≠ 0 → mostRecentSwitchTime z = -firstSwitchTime (tau z) := by
  refine ⟨tau_flow_neg, fun z u h ↦ l4c_isMostRecentControl_iff.2 h, fun z hz ↦ ?_⟩
  have hτ : tau z ≠ 0 := fun h ↦ hz (by
    rw [← tau_tau z, h]; funext j; fin_cases j <;> simp [tau])
  -- the most recent control `u` of `z⁰` is the conjugate of the first control of `τ(z⁰)`
  have hmr : IsMostRecentControl z (starRingEnd ℂ (firstControl (tau z))) := by
    rw [l4c_isMostRecentControl_iff, Complex.conj_conj]
    exact isFirstControl_firstControl hτ
  have hex : ∃ u, IsMostRecentControl z u := ⟨_, hmr⟩
  have hmrc : mostRecentControl z = starRingEnd ℂ (firstControl (tau z)) := by
    rw [mostRecentControl, dite_eq_left hex]
    exact l4st_isMostRecentControl_unique hex.choose_spec hmr
  have hfc : firstControl (tau z) = starRingEnd ℂ (mostRecentControl z) := by
    rw [hmrc, Complex.conj_conj]
  -- the two sets are opposite
  unfold mostRecentSwitchTime firstSwitchTime
  rw [hfc, ← Real.sSup_neg]
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_neg]
  constructor
  · rintro ⟨ht, v, hv, hlt⟩
    refine ⟨by linarith, starRingEnd ℂ v, l4c_conj_mem_VT.2 hv, ?_⟩
    rwa [l4c_ham_flow_tau, l4c_ham_flow_tau, neg_neg]
  · rintro ⟨ht, v, hv, hlt⟩
    refine ⟨by linarith, starRingEnd ℂ v, l4c_conj_mem_VT.2 hv, ?_⟩
    rwa [← Complex.conj_conj v, l4c_ham_flow_tau, l4c_ham_flow_tau, neg_neg] at hlt

end SmoothedPolygons
