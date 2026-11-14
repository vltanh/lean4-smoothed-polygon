module

public import SmoothedPolygons.Ch13.FixedPoints

/-!
# Chapter 13: Lemma 13.5.2 (the two fixed points) and Remark 13.5.3

Lemma 13.5.2 of Hales–Vajjha, *Packings of Smoothed Polygons* (`lem:qout`, TeX 11298–11387):
`F_ang` has exactly two fixed points in `Ξ_𝒲/V_T` at which the Hamiltonian vanishes, `q_out` and
`q_in = τ(q_out)`, the switching points of the outward and inward triangular spirals, with the
scaling factor `r_scale`, the unique real root greater than `1` of the palindromic polynomial
`P`. And Remark 13.5.3 (TeX 11389–11400): the iterates of `F` along the spirals.

The book's proof, step by step, with the helper statements of this file:
1. A fixed point of `F_ang` in `Ξ_𝒲/V_T` lifts to `z⁰` with `F(z⁰) = ζ₁ (r z₁⁰, r² z₂⁰, r³ z₃⁰)`
   for some `r > 0`, `ζ₁ ∈ V_T` (the fixed-point condition `eqn:fixed-point` (13.5.2)).
2. Solving the linear equations (13.2.2) gives `z⁰` in terms of `(t_sw, u, r, ζ₁)`
   (`fixedPointCandidate`, `l4st_eq_fixedPointCandidate`; TeX 11353–11358). (The book also notes
   `z₃⁰ ≠ 0`; the argument below does not need it.)
3. The maximum principle gives `z₃⁰ ū ζ₁² ∈ ℝ_{≤0}` (TeX 11359–11372; the book's displayed
   inequalities are garbled, REPORT.md, E67, the final condition is right), whence
   `(r, ζ₁) ∈ {(1, ζ), (r_scale, ζ²), (1/r_scale, ζ²)}` (`l4st_fixedPoint_cases`). In detail:
   `ζ₁ = 1` is impossible, since the first control of `F(z⁰)`, which is `ζ₁ u` by the equivariance
   of `F` (Lemmas 13.2.1, 13.2.2), differs from `u` (the control switches at `t_sw`); this
   exclusion is not in the book. The proof uses the maximum condition at `t = t_sw` for the
   outgoing control `u` and the incoming control `ζ₁ u`: both maximize `RR(·, z₃(t_sw))`, which
   puts `ū ζ₁ z₃(t_sw) = r³ z₃⁰ ū ζ₁²` on the wall `𝒲₀ = ℝ_{≤0}`
   (`RR_eq_and_le_iff_mem_wall_zero`). By (13.5.2) and the equivariance, the condition for the
   incoming control `ζ₁ u` at `t_sw` is the book's condition at `t = 0`. With step 2 this reads
   `6 s ζ₁ D(r, ζ₁) + i r³ t_sw³ N(r, ζ₁) = 0` for some `s ≤ 0`, where
   `D(r, w) = (rw - 1)(r²w - 1)(r³w - 1)` and `N(r, w) = 1 + 2rw + 2r²w + r³w²`. Combining it with
   its complex conjugate (`l4i_core`, identities in `ℤ[r, ζ]` modulo `ζ² + ζ + 1`): the imaginary
   part gives `(r - 1) P(r) = 0` and the real part `12 s |D|² = ±√3 r³ t_sw³ (r + 1)(r² + r + 1)
   Q₆(r)` with `Q₆(r) = r⁶ - r⁵ - r⁴ - r³ - r² - r + 1`, `+` for `ζ₁ = ζ` and `-` for `ζ₁ = ζ²`.
   Since `Q₆ = P + 4r⁵ + 6r⁴ + 4r³ + 6r² + 4r > 0` at the roots of `P` and `Q₆(1) = -3`, the sign
   selects exactly the three cases. These steps do not assume `z₃⁰ ∈ 𝒲` (the wall condition comes
   from `t = t_sw`).
4. `r = 1` is rejected because `H_F ≠ 0` there (`l4st_hamMax_ne_zero_of_r_eq_one`: by
   homogeneity, `H_F(z⁰, u) = t_sw³ H_F(z⁰(1, ζ, 1, 1), 1) = t_sw³/(4√3)`, the book's `1/(4√3)` in
   the normalization `t_sw = 1`).
5. The two remaining solutions are, up to the virial group, `qOutCart` and `τ(qOutCart)`
   (`l4st_fixedPointCandidate_virialEquiv`), which are fixed points with `H_F⁺ = 0`
   (`SmoothedPolygons/Ch13/FixedPoints.lean`: the verification the book leaves out, REPORT.md, E67)
   and are distinct (`l4st_qOut_ne_qIn`). The book identifies the solutions with (13.5.1) by
   substitution ("choosing the first control `u = ζ₁²`"); here `qOutCart` and `τ(qOutCart)` satisfy
   the fixed-point equation (`poincare_qOutCart`, `poincare_tau_qOutCart`), so by step 2
   they are candidates for their own first control and switching time, and the candidates for
   different `(u, t_sw)` differ by the virial group (they are homogeneous in `u` and `t_sw`).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set

namespace TriFuller

/-- The solution `z⁰` of the fixed-point equations `z_j(t, z⁰, u) = r^j w z_j⁰` (`j = 1, 2, 3`) of
(13.5.2), from the linear equations (13.2.2) (TeX 11353–11358):
`z₁⁰ = -itu/(rw - 1)`, `z₂⁰ = -it²u(rw + 1)/(2(rw - 1)(r²w - 1))`,
`z₃⁰ = -it³u(1 + 2rw + 2r²w + r³w²)/(6(rw - 1)(r²w - 1)(r³w - 1))`. -/
noncomputable def fixedPointCandidate (r : ℝ) (w u : ℂ) (t : ℝ) : Fin 3 → ℂ :=
  ![-I * t * u / (r * w - 1),
    -I * t ^ 2 * u * (r * w + 1) / (2 * (r * w - 1) * (r ^ 2 * w - 1)),
    -I * t ^ 3 * u * (1 + 2 * r * w + 2 * r ^ 2 * w + r ^ 3 * w ^ 2) /
      (6 * (r * w - 1) * (r ^ 2 * w - 1) * (r ^ 3 * w - 1))]

/-! ### Helpers: `ζ`, `RR` and the virial group -/

private lemma l4i_ζ_rel : ζ ^ 2 + ζ + 1 = 0 := by
  rw [ζ_sq_eq_mk, ζ_eq_mk]
  apply Complex.ext <;> simp

private lemma l4i_ζ_sq_sq : (ζ ^ 2) ^ 2 = ζ := by
  rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, ζ_pow_three, one_mul]

private lemma l4i_I_mul : I * (2 * ζ + 1) = -(√3 : ℂ) := by
  rw [ζ_eq_mk]
  apply Complex.ext <;> simp <;> ring

private lemma l4i_ζ_sq_ne_one : ζ ^ 2 ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [ζ_sq_eq_mk] at this
  norm_num at this

/-- `a ζ - 1 ≠ 0` and `a ζ² - 1 ≠ 0` for every real `a` (`ζ`, `ζ²` are not real). -/
private lemma l4i_ofReal_mul_sub_one_ne {w : ℂ} (hw : w = ζ ∨ w = ζ ^ 2) (a : ℝ) :
    (a : ℂ) * w - 1 ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  have h3 : 0 < √3 := by positivity
  rcases hw with rfl | rfl
  · rw [ζ_eq_mk] at h1 h2
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.sub_im, Complex.mul_im, Complex.one_im, Complex.zero_re,
      Complex.zero_im] at h1 h2
    nlinarith
  · rw [ζ_sq_eq_mk] at h1 h2
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.sub_im, Complex.mul_im, Complex.one_im, Complex.zero_re,
      Complex.zero_im] at h1 h2
    nlinarith

private lemma l4i_conj_mul_self {u : ℂ} (hu : u ∈ VT) : starRingEnd ℂ u * u = 1 := by
  rw [← inv_eq_conj_of_mem_VT hu]
  exact inv_mul_cancel₀ (by rintro rfl; simpa using norm_eq_one_of_mem_VT hu)

private lemma l4i_RR_mul_left (c a b : ℂ) : RR (c * a) b = RR a (starRingEnd ℂ c * b) := by
  simp only [RR, map_mul]
  ring_nf

/-- The rescaling `(r z₁, r² z₂, r³ z₃)` of a point `z ≠ 0` by `r > 0` is nonzero. -/
theorem scale_ne_zero {r : ℝ} (hr : 0 < r) {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    scale r z ≠ 0 := by
  intro h
  apply hz
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have h0 : (r : ℂ) * z 0 = 0 := congrFun h 0
  have h1 : (r : ℂ) ^ 2 * z 1 = 0 := congrFun h 1
  have h2 : (r : ℂ) ^ 3 * z 2 = 0 := congrFun h 2
  funext j
  fin_cases j
  · exact (mul_eq_zero.1 h0).resolve_left hr'
  · exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero 2 hr')
  · exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero 3 hr')

private lemma l4i_pow_mem_VT {v : ℂ} (hv : v ∈ VT) (k : ℕ) : v ^ k ∈ VT := by
  induction k with
  | zero => simp [VT]
  | succ k ih => rw [pow_succ]; exact mul_mem_VT ih hv

/-- Two points of `Ξ_𝒲` have the same class in `Ξ_𝒲/V_T` if and only if they differ by a rotation
in `V_T`. -/
theorem mk_eq_mk_iff_exists_mem_VT {ξ η : XiW} :
    (Quotient.mk'' ξ : XiWQuot) = Quotient.mk'' η ↔
      ∃ v ∈ VT, (ξ : Fin 3 → ℂ) = v • (η : Fin 3 → ℂ) := by
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨((g : ℂˣ) : ℂ), (mem_VT_iff_exists_rootsOfUnity _).2 ⟨g, rfl⟩, by rw [← hg]; rfl⟩
  · rintro ⟨v, hv, h⟩
    obtain ⟨g, rfl⟩ := (mem_VT_iff_exists_rootsOfUnity v).1 hv
    exact ⟨g, Subtype.ext h.symm⟩

/-- If the angular parts of `a, b ≠ 0` differ by `v`, then `a = v · (ρ b₁, ρ² b₂, ρ³ b₃)` with
`ρ = φ(a)/φ(b)`. -/
private lemma l4i_eq_smul_scale_of_ang {a b : Fin 3 → ℂ} (ha : a ≠ 0) {v : ℂ}
    (h : ang a = v • ang b) : a = v • scale (weightedNorm a / weightedNorm b) b := by
  conv_lhs => rw [← scale_weightedNorm_ang ha]
  rw [h, ang, scale_smul, scale_scale, div_eq_mul_inv]

/-- The candidate is homogeneous: `z⁰(r, w, u, ρ t') = (u ū') · (ρ z₁⁰, ρ² z₂⁰, ρ³ z₃⁰)` with
`z⁰ = z⁰(r, w, u', t')`, for `u' ∈ V_T`. -/
private lemma l4i_cand_smul_scale {u u' : ℂ} (hu' : u' ∈ VT) (r : ℝ) (w : ℂ) (ρ t' : ℝ) :
    fixedPointCandidate r w u (ρ * t') =
      (u * starRingEnd ℂ u') • scale ρ (fixedPointCandidate r w u' t') := by
  have hc := l4i_conj_mul_self hu'
  funext j
  fin_cases j <;> simp [fixedPointCandidate, scale]
  · linear_combination (I * ρ * t' * u / (r * w - 1)) * hc
  · linear_combination (I * ρ ^ 2 * t' ^ 2 * u * (r * w + 1) /
      (2 * (r * w - 1) * (r ^ 2 * w - 1))) * hc
  · linear_combination (I * ρ ^ 3 * t' ^ 3 * u * (1 + 2 * r * w + 2 * r ^ 2 * w + r ^ 3 * w ^ 2) /
      (6 * (r * w - 1) * (r ^ 2 * w - 1) * (r ^ 3 * w - 1))) * hc

/-- The candidate for `(r, ζ₁) = (1, ζ)`, `u = 1`, `t = 1`:
`z⁰ = (-√3/6 + i/2, √3/12 + i/12, √3/36 - i/12)`, and `H_F(z⁰, 1) = √3/12 = 1/(4√3)`. -/
private lemma l4i_ham_cand_one : ham (fixedPointCandidate 1 ζ 1 1) 1 = √3 / 12 := by
  have s2 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s3 : √3 ^ 3 = 3 * √3 := by rw [pow_succ, s2]
  have s4 : √3 ^ 4 = 9 := by rw [show 4 = 2 * 2 by rfl, pow_mul, s2]; norm_num
  have d : ζ - 1 ≠ 0 := by simpa using l4i_ofReal_mul_sub_one_ne (Or.inl rfl) 1
  have c0 : fixedPointCandidate 1 ζ 1 1 0 = ⟨-(√3 / 6), 1 / 2⟩ := by
    simp only [fixedPointCandidate, Matrix.cons_val_zero, Complex.ofReal_one, one_mul, mul_one]
    rw [div_eq_iff d, ζ_eq_mk]
    apply Complex.ext
    · simp
      linarith
    · simp
      linarith
  have c1 : fixedPointCandidate 1 ζ 1 1 1 = ⟨√3 / 12, 1 / 12⟩ := by
    simp only [fixedPointCandidate, Matrix.cons_val_one, Matrix.cons_val_zero,
      Complex.ofReal_one, one_pow, one_mul, mul_one]
    rw [div_eq_iff (mul_ne_zero (mul_ne_zero two_ne_zero d) d), ζ_eq_mk]
    apply Complex.ext
    · simp
      linarith
    · simp
      linarith
  have c2 : fixedPointCandidate 1 ζ 1 1 2 = ⟨√3 / 36, -(1 / 12)⟩ := by
    simp only [fixedPointCandidate, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Complex.ofReal_one, one_pow, one_mul, mul_one]
    rw [div_eq_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) d) d) d), ζ_eq_mk]
    apply Complex.ext
    · simp [sq]
      linarith
    · simp [sq]
      linarith
  simp only [ham, c0, c1, c2, RR]
  simp
  ring

/-- Step 2 of the proof of Lemma 13.5.2: for `r > 0` and `w ∈ V_T` with `(r, w) ≠ (1, 1)`, the
linear system `z(t, z⁰, u) = w (r z₁⁰, r² z₂⁰, r³ z₃⁰)` has the unique solution
`fixedPointCandidate r w u t` (the determinant `(rw - 1)(r²w - 1)(r³w - 1)` vanishes only for
`r = 1`, `w = 1`). -/
private theorem l4st_eq_fixedPointCandidate {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ VT)
    (hrw : ¬ (r = 1 ∧ w = 1)) {u : ℂ} {t : ℝ} {z : Fin 3 → ℂ}
    (h : flow t z u = w • scale r z) : z = fixedPointCandidate r w u t := by
  -- the determinant `(rw - 1)(r²w - 1)(r³w - 1)` does not vanish
  have hd : ∀ k : ℕ, k ≠ 0 → (r : ℂ) ^ k * w - 1 ≠ 0 := by
    intro k hk
    rcases hw with rfl | rfl | rfl
    · have hr1 : r ≠ 1 := fun h1 ↦ hrw ⟨h1, rfl⟩
      rw [mul_one, sub_ne_zero, ← Complex.ofReal_pow, ← Complex.ofReal_one, Ne,
        Complex.ofReal_inj]
      exact fun h' ↦ hr1 ((pow_eq_one_iff_of_nonneg hr.le hk).1 h')
    · rw [← Complex.ofReal_pow]
      exact l4i_ofReal_mul_sub_one_ne (Or.inl rfl) _
    · rw [← Complex.ofReal_pow]
      exact l4i_ofReal_mul_sub_one_ne (Or.inr rfl) _
  have d1 : (r : ℂ) * w - 1 ≠ 0 := by simpa using hd 1 one_ne_zero
  have d2 := hd 2 two_ne_zero
  have d3 := hd 3 three_ne_zero
  -- the three linear equations (13.2.2)
  have e0 : z 0 - I * t * u = w * (r * z 0) := congrFun h 0
  have e1 : z 1 + z 0 * t - I * t ^ 2 * u / 2 = w * (r ^ 2 * z 1) := congrFun h 1
  have e2 : z 2 + z 1 * t + z 0 * t ^ 2 / 2 - I * t ^ 3 * u / 6 = w * (r ^ 3 * z 2) :=
    congrFun h 2
  have h0 : z 0 * (r * w - 1) = -I * t * u := by linear_combination -e0
  have h1 : z 1 * (2 * (r * w - 1) * (r ^ 2 * w - 1)) = -I * t ^ 2 * u * (r * w + 1) := by
    linear_combination (-2 * (r * w - 1)) * e1 + (2 * t) * h0
  have h2 : z 2 * (6 * (r * w - 1) * (r ^ 2 * w - 1) * (r ^ 3 * w - 1)) =
      -I * t ^ 3 * u * (1 + 2 * r * w + 2 * r ^ 2 * w + r ^ 3 * w ^ 2) := by
    linear_combination (-6 * (r * w - 1) * (r ^ 2 * w - 1)) * e2 + (3 * t) * h1 +
      (3 * t ^ 2 * (r ^ 2 * w - 1)) * h0
  funext j
  fin_cases j
  · exact (eq_div_iff d1).2 h0
  · exact (eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero d1) d2)).2 h1
  · exact (eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) d1) d2) d3)).2 h2

/-- The polynomial identities behind step 3 of the proof of Lemma 13.5.2, in `ℤ[ρ, ζ]` modulo
`ζ² + ζ + 1`. Write `D(ρ, w) = (ρw - 1)(ρ²w - 1)(ρ³w - 1)` and `N(ρ, w) = 1 + 2ρw + 2ρ²w + ρ³w²`.
Multiply `6σζD(ρ, ζ) + iκN(ρ, ζ) = 0` and its conjugate (`ζ̄ = ζ²`) by `ζ²D(ρ, ζ²)` and `ζD(ρ, ζ)`.
The difference gives `κ (ρ - 1)(ρ² + ρ + 1) P(ρ) = 0`, and the sum gives
`12σ |D(ρ, ζ)|² = √3 κ (ρ + 1)(ρ² + ρ + 1) Q₆(ρ)`, with `Q₆(ρ) = ρ⁶ - ρ⁵ - ρ⁴ - ρ³ - ρ² - ρ + 1`,
`|D(ρ, ζ)|² = (ρ² + ρ + 1)(ρ⁴ + ρ² + 1)(ρ⁶ + ρ³ + 1)` and `i(2ζ + 1) = -√3`. -/
private lemma l4i_core {σ κ ρ : ℂ}
    (h : 6 * σ * ζ * ((ρ * ζ - 1) * (ρ ^ 2 * ζ - 1) * (ρ ^ 3 * ζ - 1)) +
      I * κ * (1 + 2 * ρ * ζ + 2 * ρ ^ 2 * ζ + ρ ^ 3 * ζ ^ 2) = 0)
    (hc : 6 * σ * ζ ^ 2 * ((ρ * ζ ^ 2 - 1) * (ρ ^ 2 * ζ ^ 2 - 1) * (ρ ^ 3 * ζ ^ 2 - 1)) -
      I * κ * (1 + 2 * ρ * ζ ^ 2 + 2 * ρ ^ 2 * ζ ^ 2 + ρ ^ 3 * (ζ ^ 2) ^ 2) = 0) :
    I * (κ * ((ρ - 1) * (ρ ^ 2 + ρ + 1) *
        (1 - 5 * ρ - 7 * ρ ^ 2 - 5 * ρ ^ 3 - 7 * ρ ^ 4 - 5 * ρ ^ 5 + ρ ^ 6))) = 0 ∧
      12 * σ * ((ρ ^ 2 + ρ + 1) * (ρ ^ 4 + ρ ^ 2 + 1) * (ρ ^ 6 + ρ ^ 3 + 1)) -
        √3 * κ * ((ρ + 1) * (ρ ^ 2 + ρ + 1) *
          (ρ ^ 6 - ρ ^ 5 - ρ ^ 4 - ρ ^ 3 - ρ ^ 2 - ρ + 1)) = 0 := by
  have rel := l4i_ζ_rel
  have hI := l4i_I_mul
  constructor
  · linear_combination
      (-(ζ ^ 2 * ((ρ * ζ ^ 2 - 1) * (ρ ^ 2 * ζ ^ 2 - 1) * (ρ ^ 3 * ζ ^ 2 - 1)))) * h +
      (ζ * ((ρ * ζ - 1) * (ρ ^ 2 * ζ - 1) * (ρ ^ 3 * ζ - 1))) * hc +
      (I * κ *
        (ζ ^ 8 * (ρ ^ 9) + ζ ^ 7 * (-ρ ^ 9 + 2 * ρ ^ 8 + 2 * ρ ^ 7) + ζ ^ 6 * (ρ ^ 9 - 3 * ρ ^ 8 -
         3 * ρ ^ 7) + ζ ^ 5 * (-2 * ρ ^ 7 - 5 * ρ ^ 6 - 4 * ρ ^ 5 - 2 * ρ ^ 4) + ζ ^ 4 * (-ρ ^ 9 +
         5 * ρ ^ 8 + 7 * ρ ^ 7 + 7 * ρ ^ 6 + 5 * ρ ^ 5 + 3 * ρ ^ 4 - ρ ^ 3) + ζ ^ 3 * (ρ ^ 9 -
         5 * ρ ^ 8 - 7 * ρ ^ 7 - 6 * ρ ^ 6 - 3 * ρ ^ 5 + ρ ^ 4 + 4 * ρ ^ 3 + 2 * ρ ^ 2) +
         ζ ^ 2 * (ρ ^ 3 + ρ ^ 2 + ρ) + ζ * (-ρ ^ 9 + 5 * ρ ^ 8 + 7 * ρ ^ 7 + 6 * ρ ^ 6 +
         2 * ρ ^ 5 - 2 * ρ ^ 4 - 6 * ρ ^ 3 - 7 * ρ ^ 2 - 5 * ρ) + (ρ ^ 9 - 5 * ρ ^ 8 - 7 * ρ ^ 7 -
         6 * ρ ^ 6 - 2 * ρ ^ 5 + 2 * ρ ^ 4 + 6 * ρ ^ 3 + 7 * ρ ^ 2 + 5 * ρ - 1))) * rel
  · linear_combination
      (ζ ^ 2 * ((ρ * ζ ^ 2 - 1) * (ρ ^ 2 * ζ ^ 2 - 1) * (ρ ^ 3 * ζ ^ 2 - 1))) * h +
      (ζ * ((ρ * ζ - 1) * (ρ ^ 2 * ζ - 1) * (ρ ^ 3 * ζ - 1))) * hc -
      (12 * σ *
        (ζ ^ 10 * (ρ ^ 12) + ζ ^ 9 * (-ρ ^ 12 - ρ ^ 11 - ρ ^ 10 - ρ ^ 9) + ζ ^ 8 * (ρ ^ 9 + ρ ^ 8 +
         ρ ^ 7) + ζ ^ 7 * (ρ ^ 12 + ρ ^ 11 + 2 * ρ ^ 10 + 2 * ρ ^ 9 + 2 * ρ ^ 8 + ρ ^ 7) +
         ζ ^ 6 * (-ρ ^ 12 - ρ ^ 11 - 2 * ρ ^ 10 - 2 * ρ ^ 9 - 3 * ρ ^ 8 - 3 * ρ ^ 7 - 3 * ρ ^ 6 -
         2 * ρ ^ 5 - ρ ^ 4) + ζ ^ 5 * (ρ ^ 5 + ρ ^ 4 + ρ ^ 3) + ζ ^ 4 * (ρ ^ 12 + ρ ^ 11 +
         2 * ρ ^ 10 + 2 * ρ ^ 9 + 3 * ρ ^ 8 + 3 * ρ ^ 7 + 3 * ρ ^ 6 + 3 * ρ ^ 5 + 3 * ρ ^ 4 +
         ρ ^ 3 + ρ ^ 2) + ζ ^ 3 * (-ρ ^ 12 - ρ ^ 11 - 2 * ρ ^ 10 - 2 * ρ ^ 9 - 3 * ρ ^ 8 -
         3 * ρ ^ 7 - 3 * ρ ^ 6 - 3 * ρ ^ 5 - 3 * ρ ^ 4 - 2 * ρ ^ 3 - 2 * ρ ^ 2 - ρ) + ζ * (ρ ^ 12 +
         ρ ^ 11 + 2 * ρ ^ 10 + 2 * ρ ^ 9 + 3 * ρ ^ 8 + 3 * ρ ^ 7 + 3 * ρ ^ 6 + 3 * ρ ^ 5 +
         3 * ρ ^ 4 + 2 * ρ ^ 3 + 2 * ρ ^ 2 + ρ + 1) + (-ρ ^ 12 - ρ ^ 11 - 2 * ρ ^ 10 - 2 * ρ ^ 9 -
         3 * ρ ^ 8 - 3 * ρ ^ 7 - 3 * ρ ^ 6 - 3 * ρ ^ 5 - 3 * ρ ^ 4 - 2 * ρ ^ 3 - 2 * ρ ^ 2 - ρ -
         1)) +
        I * κ *
        (ζ ^ 8 * (ρ ^ 9) + ζ ^ 7 * (-ρ ^ 9 + 2 * ρ ^ 8 + 2 * ρ ^ 7) + ζ ^ 6 * (-ρ ^ 9 - 3 * ρ ^ 8 -
         3 * ρ ^ 7) + ζ ^ 5 * (2 * ρ ^ 9 + 2 * ρ ^ 8 - 3 * ρ ^ 6 - 4 * ρ ^ 5 - 2 * ρ ^ 4) +
         ζ ^ 4 * (-ρ ^ 9 - ρ ^ 8 + ρ ^ 7 + 3 * ρ ^ 6 + 3 * ρ ^ 5 + ρ ^ 4 - ρ ^ 3) +
         ζ ^ 3 * (-ρ ^ 9 - ρ ^ 8 + ρ ^ 7 + 4 * ρ ^ 6 + 7 * ρ ^ 5 + 7 * ρ ^ 4 + 6 * ρ ^ 3 +
         2 * ρ ^ 2) + ζ ^ 2 * (2 * ρ ^ 9 + 2 * ρ ^ 8 - 2 * ρ ^ 7 - 8 * ρ ^ 6 - 12 * ρ ^ 5 -
         12 * ρ ^ 4 - 9 * ρ ^ 3 - 3 * ρ ^ 2 + ρ) + ζ * (-ρ ^ 9 - ρ ^ 8 + ρ ^ 7 + 4 * ρ ^ 6 +
         6 * ρ ^ 5 + 6 * ρ ^ 4 + 4 * ρ ^ 3 + ρ ^ 2 - ρ) + (-ρ ^ 9 - ρ ^ 8 + ρ ^ 7 + 4 * ρ ^ 6 +
         6 * ρ ^ 5 + 6 * ρ ^ 4 + 4 * ρ ^ 3 + ρ ^ 2 - ρ - 1))) * rel -
      (κ * ((ρ + 1) * (ρ ^ 2 + ρ + 1) * (ρ ^ 6 - ρ ^ 5 - ρ ^ 4 - ρ ^ 3 - ρ ^ 2 - ρ + 1))) * hI

/-- Step 3 of the proof of Lemma 13.5.2 in real form: if `6sζD(r, ζ) + iKN(r, ζ) = 0` with `s, K, r`
real, then `K (r - 1)(r² + r + 1) P(r) = 0` and
`12 s (r² + r + 1)(r⁴ + r² + 1)(r⁶ + r³ + 1) = √3 K (r + 1)(r² + r + 1) Q₆(r)` (`l4i_core`, with the
complex conjugate of the hypothesis). -/
private lemma l4i_cases_real {s K r : ℝ}
    (h : 6 * (s : ℂ) * ζ * ((r * ζ - 1) * (r ^ 2 * ζ - 1) * (r ^ 3 * ζ - 1)) +
      I * K * (1 + 2 * r * ζ + 2 * r ^ 2 * ζ + r ^ 3 * ζ ^ 2) = 0) :
    K * ((r - 1) * (r ^ 2 + r + 1) * rScalePoly r) = 0 ∧
      12 * s * ((r ^ 2 + r + 1) * (r ^ 4 + r ^ 2 + 1) * (r ^ 6 + r ^ 3 + 1)) =
        √3 * K * ((r + 1) * (r ^ 2 + r + 1) * (r ^ 6 - r ^ 5 - r ^ 4 - r ^ 3 - r ^ 2 - r + 1)) := by
  have hc := congrArg (starRingEnd ℂ) h
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I, map_zero, conj_ζ] at hc
  obtain ⟨h1, h2⟩ := l4i_core h (by linear_combination hc)
  constructor
  · have h1' := (mul_eq_zero.1 h1).resolve_left Complex.I_ne_zero
    unfold rScalePoly
    exact_mod_cast h1'
  · have h2' : (((12 * s * ((r ^ 2 + r + 1) * (r ^ 4 + r ^ 2 + 1) * (r ^ 6 + r ^ 3 + 1)) -
        √3 * K * ((r + 1) * (r ^ 2 + r + 1) * (r ^ 6 - r ^ 5 - r ^ 4 - r ^ 3 - r ^ 2 - r + 1)) :
          ℝ)) : ℂ) = 0 := by
      push_cast
      linear_combination h2
    exact sub_eq_zero.1 (Complex.ofReal_eq_zero.1 h2')

/-- Step 3 of the proof of Lemma 13.5.2 (TeX 11359–11380): if `z⁰ ≠ 0` and
`F(z⁰) = w (r z₁⁰, r² z₂⁰, r³ z₃⁰)` with `r > 0`, `w ∈ V_T`, then
`(r, w) ∈ {(1, ζ), (r_scale, ζ²), (1/r_scale, ζ²)}`. (The book's `z₃⁰ ∈ 𝒲` is not needed: the wall
condition comes from `t = t_sw`.) -/
private theorem l4st_fixedPoint_cases {z : Fin 3 → ℂ} (hz : z ≠ 0) {r : ℝ}
    (hr : 0 < r) {w : ℂ} (hw : w ∈ VT) (h : poincare z = w • scale r z) :
    (r = 1 ∧ w = ζ) ∨ (r = rScale ∧ w = ζ ^ 2) ∨ (r = rScale⁻¹ ∧ w = ζ ^ 2) := by
  set u := firstControl z
  set T := firstSwitchTime z
  have hT : 0 < T := firstSwitchTime_pos hz
  have huV : u ∈ VT := (isFirstControl_firstControl hz).1
  have hFz : poincare z ≠ 0 := poincare_ne_zero hz
  -- the first control of `F(z⁰) = ζ₁ (r z₁⁰, r² z₂⁰, r³ z₃⁰)` is `ζ₁ u` (Lemmas 13.2.1, 13.2.2)
  have hfc : firstControl (poincare z) = w * u := by
    rw [h, (poincare_smul hw (scale_ne_zero hr hz)).1, (poincare_scale hr hz).1]
  -- `ζ₁ = 1` is impossible: the control switches at `t_sw`
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact firstControl_poincare_ne hz (by rw [hfc, one_mul])
  have hw' : w = ζ ∨ w = ζ ^ 2 := by
    rcases hw with rfl | rfl | rfl
    · exact absurd rfl hw1
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- step 2: `z⁰` is the candidate
  have hzc : z = fixedPointCandidate r w u T :=
    l4st_eq_fixedPointCandidate hr hw (fun h' ↦ hw1 h'.2) h
  -- the maximum principle at `t = t_sw`: the control `u` (from `z⁰`) and the next control `ζ₁ u`
  -- (from `F(z⁰)`) both maximize `RR(·, z₃(t_sw))`
  set m := poincare z 2
  have hmU : ∀ v ∈ VT, RR v m ≤ RR u m := by
    intro v hv
    have := firstControl_maximizes hz T ⟨hT.le, le_rfl⟩ v hv
    unfold ham at this
    exact le_of_add_le_add_left this
  have hmW : ∀ v ∈ VT, RR v m ≤ RR (w * u) m := by
    intro v hv
    have := firstControl_maximizes hFz 0 ⟨le_rfl, (firstSwitchTime_pos hFz).le⟩ v hv
    rw [flow_zero, hfc] at this
    unfold ham at this
    exact le_of_add_le_add_left this
  -- hence `ū ζ₁ z₃(t_sw) = r³ z₃⁰ ū ζ₁² ∈ ℝ_{≤0}` (TeX 11372)
  have hshift : ∀ x, RR (starRingEnd ℂ u * w * m) x = RR (u * starRingEnd ℂ w * x) m := by
    intro x
    rw [RR_comm, l4i_RR_mul_left]
    congr 1
    simp
  have hwall : starRingEnd ℂ u * w * m ∈ wall 0 := by
    have hζ3 := ζ_pow_three
    refine (RR_eq_and_le_iff_mem_wall_zero _).1 ?_
    simp only [hshift, mul_one]
    rcases hw' with rfl | rfl
    · rw [conj_ζ, show u * ζ ^ 2 * ζ = u by linear_combination u * hζ3,
        show u * ζ ^ 2 * ζ ^ 2 = ζ * u by linear_combination (u * ζ) * hζ3]
      exact ⟨le_antisymm (hmW u huV) (hmU _ (mul_mem_VT ζ_mem_VT huV)),
        hmU _ (mul_mem_VT huV ζ_sq_mem_VT)⟩
    · rw [map_pow, conj_ζ, l4i_ζ_sq_sq, show u * ζ * ζ = ζ ^ 2 * u by ring,
        show u * ζ * ζ ^ 2 = u by linear_combination u * hζ3]
      exact ⟨le_antisymm (hmU _ (mul_mem_VT ζ_sq_mem_VT huV)) (hmW u huV),
        hmW _ (mul_mem_VT huV ζ_mem_VT)⟩
  obtain ⟨s, hs, hbs⟩ := hwall
  -- with the candidate: `6 s ζ₁ D(r, ζ₁) + i r³ t_sw³ N(r, ζ₁) = 0`
  have hmz : m = w * ((r : ℂ) ^ 3 * z 2) := congrFun h 2
  have hD : (6 * ((r : ℂ) * w - 1) * (r ^ 2 * w - 1) * (r ^ 3 * w - 1)) ≠ 0 := by
    have d1 := l4i_ofReal_mul_sub_one_ne hw' r
    have d2 := l4i_ofReal_mul_sub_one_ne hw' (r ^ 2)
    have d3 := l4i_ofReal_mul_sub_one_ne hw' (r ^ 3)
    push_cast at d2 d3
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) d1) d2) d3
  have hz2 : z 2 * (6 * ((r : ℂ) * w - 1) * (r ^ 2 * w - 1) * (r ^ 3 * w - 1)) =
      -I * T ^ 3 * u * (1 + 2 * r * w + 2 * r ^ 2 * w + r ^ 3 * w ^ 2) := by
    rw [hzc]
    exact div_mul_cancel₀ _ hD
  have hcu := l4i_conj_mul_self huV
  have hw3 : w ^ 3 = 1 := by
    rcases hw' with rfl | rfl
    · exact ζ_pow_three
    · rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, ζ_pow_three, one_pow]
  have key : 6 * (s : ℂ) * w * ((r * w - 1) * (r ^ 2 * w - 1) * (r ^ 3 * w - 1)) +
      I * ((r ^ 3 * T ^ 3 : ℝ) : ℂ) * (1 + 2 * r * w + 2 * r ^ 2 * w + r ^ 3 * w ^ 2) = 0 := by
    rw [hmz, pow_zero, mul_one] at hbs
    push_cast
    linear_combination (-(6 * w * ((r * w - 1) * (r ^ 2 * w - 1) * (r ^ 3 * w - 1)))) * hbs +
      (starRingEnd ℂ u * w ^ 3 * r ^ 3) * hz2 -
      (I * r ^ 3 * T ^ 3 * (1 + 2 * r * w + 2 * r ^ 2 * w + r ^ 3 * w ^ 2) * w ^ 3) * hcu -
      (I * r ^ 3 * T ^ 3 * (1 + 2 * r * w + 2 * r ^ 2 * w + r ^ 3 * w ^ 2)) * hw3
  -- the case analysis on the signs (`l4i_cases_real`)
  have hK : 0 < r ^ 3 * T ^ 3 := by positivity
  have hR : 0 < (r ^ 2 + r + 1) * (r ^ 4 + r ^ 2 + 1) * (r ^ 6 + r ^ 3 + 1) := by positivity
  have hq : 0 < r ^ 2 + r + 1 := by positivity
  have h3 : 0 < √3 := by positivity
  have hsR : 12 * s * ((r ^ 2 + r + 1) * (r ^ 4 + r ^ 2 + 1) * (r ^ 6 + r ^ 3 + 1)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hR.le
  -- `(r - 1) P(r) = 0` from the first identity
  have hrP : ∀ K : ℝ, K ≠ 0 → K * ((r - 1) * (r ^ 2 + r + 1) * rScalePoly r) = 0 →
      r = 1 ∨ rScalePoly r = 0 := by
    intro K hK0 hA
    rcases mul_eq_zero.1 ((mul_eq_zero.1 hA).resolve_left hK0) with h' | h'
    · exact Or.inl (by linarith [(mul_eq_zero.1 h').resolve_right hq.ne'])
    · exact Or.inr h'
  rcases hw' with rfl | rfl
  · -- `ζ₁ = ζ`: `Q₆(r) ≤ 0`, which fails at the roots of `P`, so `r = 1`
    obtain ⟨h1, h2⟩ := l4i_cases_real key
    rcases hrP _ hK.ne' h1 with hr1 | hP
    · exact Or.inl ⟨hr1, rfl⟩
    · exfalso
      -- at a root of `P`, `Q₆(r) = Q₆(r) - P(r) = 4r⁵ + 6r⁴ + 4r³ + 6r² + 4r > 0`
      have hQ : 0 < r ^ 6 - r ^ 5 - r ^ 4 - r ^ 3 - r ^ 2 - r + 1 := by
        unfold rScalePoly at hP
        have : 0 < 4 * r ^ 5 + 6 * r ^ 4 + 4 * r ^ 3 + 6 * r ^ 2 + 4 * r := by positivity
        linarith
      have : 0 < √3 * (r ^ 3 * T ^ 3) *
          ((r + 1) * (r ^ 2 + r + 1) * (r ^ 6 - r ^ 5 - r ^ 4 - r ^ 3 - r ^ 2 - r + 1)) := by
        positivity
      linarith
  · -- `ζ₁ = ζ²`: conjugating gives the same equation for `ζ` with `-r³ t_sw³`; then `Q₆(r) ≥ 0`,
    -- which fails at `r = 1`, so `P(r) = 0`
    have key' : 6 * (s : ℂ) * ζ * ((r * ζ - 1) * (r ^ 2 * ζ - 1) * (r ^ 3 * ζ - 1)) +
        I * ((-(r ^ 3 * T ^ 3) : ℝ) : ℂ) * (1 + 2 * r * ζ + 2 * r ^ 2 * ζ + r ^ 3 * ζ ^ 2) = 0 := by
      have hc := congrArg (starRingEnd ℂ) key
      simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, Complex.conj_ofReal,
        Complex.conj_I, map_zero, conj_ζ, l4i_ζ_sq_sq] at hc
      push_cast at hc ⊢
      linear_combination hc
    obtain ⟨h1, h2⟩ := l4i_cases_real key'
    rcases hrP _ (neg_ne_zero.2 hK.ne') h1 with hr1 | hP
    · exfalso
      subst hr1
      have : 0 < √3 * (1 ^ 3 * T ^ 3) * 18 := by positivity
      norm_num at h2 this
      nlinarith
    · rcases (rScalePoly_eq_zero_iff r).1 hP with h' | h'
      · exact Or.inr (Or.inl ⟨h', rfl⟩)
      · exact Or.inr (Or.inr ⟨h', rfl⟩)

/-- Step 4 of the proof of Lemma 13.5.2 (TeX 11380–11381): the fixed points with `(r, ζ₁) = (1, ζ)`
have `H_F ≠ 0` (`H_F = t_sw³/(4√3)`; the book's `1/(4√3)` for `t_sw = 1`). -/
private theorem l4st_hamMax_ne_zero_of_r_eq_one {z : Fin 3 → ℂ} (hz : z ≠ 0)
    (h : poincare z = ζ • scale 1 z) : hamMax z ≠ 0 := by
  set u := firstControl z
  set T := firstSwitchTime z
  have hT : 0 < T := firstSwitchTime_pos hz
  have huV : u ∈ VT := (isFirstControl_firstControl hz).1
  have hzc : z = fixedPointCandidate 1 ζ u T :=
    l4st_eq_fixedPointCandidate one_pos ζ_mem_VT (fun h' ↦ ζ_ne_one h'.2) h
  -- the first control `u` maximizes `H_F` at `t = 0`, so `H_F⁺(z⁰) = H_F(z⁰, u)`
  have hmax : ∀ v ∈ VT, ham z v ≤ ham z u := fun v hv ↦ by
    simpa only [flow_zero] using firstControl_maximizes hz 0 ⟨le_rfl, hT.le⟩ v hv
  rw [hamMax_eq_of_forall_le huV hmax]
  -- `H_F(z⁰, u) = t_sw³ H_F(z⁰(1, ζ, 1, 1), 1) = t_sw³/(4√3)`
  have e : z = u • scale T (fixedPointCandidate 1 ζ 1 1) := by
    have := l4i_cand_smul_scale (u := u) (u' := 1) (by simp [VT]) 1 ζ T 1
    rw [mul_one, map_one, mul_one] at this
    rw [hzc, this]
  rw [e, show ham (u • scale T (fixedPointCandidate 1 ζ 1 1)) u =
      ham (u • scale T (fixedPointCandidate 1 ζ 1 1)) (u * 1) by rw [mul_one],
    ham_smul_scale (norm_eq_one_of_mem_VT huV), l4i_ham_cand_one]
  positivity

/-- Step 5 of the proof of Lemma 13.5.2: the fixed points with `(r, ζ₁) = (r_scale, ζ²)` are
virial-equivalent to `qOutCart`, those with `(1/r_scale, ζ²)` to `τ(qOutCart)`. -/
private theorem l4st_fixedPointCandidate_virialEquiv {u : ℂ} (hu : u ∈ VT) {t : ℝ} (ht : 0 < t) :
    VirialEquiv qOutCart (fixedPointCandidate rScale (ζ ^ 2) u t) ∧
      VirialEquiv (tau qOutCart) (fixedPointCandidate rScale⁻¹ (ζ ^ 2) u t) := by
  have hs0 : 0 < rScale := by linarith [rScale_spec.1]
  -- a point `q ≠ 0` with `F(q) = ζ² · (r q₁, r² q₂, r³ q₃)` is the candidate for its own first
  -- control and first switching time (step 2), and the candidates are homogeneous
  have key : ∀ {q : Fin 3 → ℂ} {r : ℝ}, q ≠ 0 → 0 < r → poincare q = ζ ^ 2 • scale r q →
      VirialEquiv q (fixedPointCandidate r (ζ ^ 2) u t) := by
    intro q r hq hr hF
    have hT := firstSwitchTime_pos hq
    have hu' := (isFirstControl_firstControl hq).1
    have hqc : q = fixedPointCandidate r (ζ ^ 2) (firstControl q) (firstSwitchTime q) :=
      l4st_eq_fixedPointCandidate hr ζ_sq_mem_VT (fun h' ↦ l4i_ζ_sq_ne_one h'.2) hF
    refine ⟨t / firstSwitchTime q, div_pos ht hT, u * starRingEnd ℂ (firstControl q),
      (mul_mem_VT hu (conj_mem_VT hu')), ?_⟩
    calc fixedPointCandidate r (ζ ^ 2) u t
        = fixedPointCandidate r (ζ ^ 2) u (t / firstSwitchTime q * firstSwitchTime q) := by
          rw [div_mul_cancel₀ _ hT.ne']
      _ = (u * starRingEnd ℂ (firstControl q)) • scale (t / firstSwitchTime q)
            (fixedPointCandidate r (ζ ^ 2) (firstControl q) (firstSwitchTime q)) :=
          l4i_cand_smul_scale hu' _ _ _ _
      _ = (u * starRingEnd ℂ (firstControl q)) • scale (t / firstSwitchTime q) q := by
          rw [← hqc]
  exact ⟨key qOutCart_ne_zero hs0 poincare_qOutCart,
    key tau_qOutCart_ne_zero (inv_pos.2 hs0) poincare_tau_qOutCart⟩

/-- `q_out ≠ q_in` (their spirals have the scaling factors `r_scale ≠ 1/r_scale`). -/
private theorem l4st_qOut_ne_qIn : qOut ≠ qIn := by
  intro h
  obtain ⟨hs1, -⟩ := rScale_spec
  have hs0 : 0 < rScale := by linarith
  have hq := qOutCart_ne_zero
  have hτq := tau_qOutCart_ne_zero
  -- `q_out = q_in` gives `qOutCart = v · (ρ-scaling)(τ qOutCart)` with `v ∈ V_T`, `ρ > 0`
  obtain ⟨v, hv, hξ⟩ := mk_eq_mk_iff_exists_mem_VT.1 h
  set ρ := weightedNorm qOutCart / weightedNorm (tau qOutCart)
  have hρ : 0 < ρ := div_pos (weightedNorm_pos hq) (weightedNorm_pos hτq)
  have heq : qOutCart = v • scale ρ (tau qOutCart) := l4i_eq_smul_scale_of_ang hq hξ
  -- then `F` scales `qOutCart` both by `r_scale` (Lemma 13.5.2) and by `1/r_scale` (the inward
  -- spiral, through the equivariance of `F`)
  have hF : poincare qOutCart = ζ ^ 2 • scale rScale⁻¹ qOutCart := by
    conv_lhs => rw [heq]
    rw [(poincare_smul hv (scale_ne_zero hρ hτq)).2.2, (poincare_scale hρ hτq).2.2,
      poincare_tau_qOutCart]
    conv_rhs => rw [heq]
    rw [scale_smul, scale_scale, scale_smul, scale_scale, smul_smul, smul_smul,
      mul_comm v, mul_comm ρ]
  rw [poincare_qOutCart] at hF
  have h0 := congrFun hF 0
  simp only [scale, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero] at h0
  have hq0 : qOutCart 0 ≠ 0 := by
    intro h'
    have := qOutCart_normalization.1
    rw [h'] at this
    norm_num at this
  have hζ2 : ζ ^ 2 ≠ 0 := pow_ne_zero 2 (by rintro h'; simpa [h'] using ζ_pow_three)
  have : (rScale : ℂ) = (rScale⁻¹ : ℝ) := by
    have := mul_right_cancel₀ hq0 (mul_left_cancel₀ hζ2 h0)
    rw [this, Complex.ofReal_inv]
  have hr : rScale = rScale⁻¹ := Complex.ofReal_injective this
  have : rScale * rScale = 1 :=
    calc rScale * rScale = rScale⁻¹ * rScale := by rw [← hr]
      _ = 1 := inv_mul_cancel₀ hs0.ne'
  nlinarith

end TriFuller

open TriFuller

/-- **Lemma 13.5.2** (`lem:qout`, TeX 11298–11387). The dynamical system `F_ang` has exactly two
fixed points in `Ξ_𝒲/V_T` at which the Hamiltonian vanishes. They are the switching points
`q_out`, `q_in` of outward and inward triangular spirals: `F(qOutCart) = ζ² · (r_scale-scaling)
(qOutCart)` and `F(τ qOutCart) = ζ² · (r_scale⁻¹-scaling)(τ qOutCart)`. They are related by the
time-reversing symmetry, `τ(q_out) = q_in`. After virial rescaling to make the real part of the
first coordinate equal to `-1` (and the third coordinate real and negative), `q_out` takes the
form (13.5.1) (`qOutCart = equilExact r_scale`), where `r = r_scale ≈ 6.27` is the unique real root
greater than `1` of the palindromic polynomial `1 - 5r - 7r² - 5r³ - 7r⁴ - 5r⁵ + r⁶`. The first
switching time of the initial condition (13.5.1) is `t_sw = 2(1 + r + r²)/(√3(r + 1)) ≈ 7.4`.

Proof: the book's, step by step, in the module docstring (`l4st_fixedPoint_cases`,
`l4st_hamMax_ne_zero_of_r_eq_one`, `l4st_fixedPointCandidate_virialEquiv`), with the verification
of the two spirals that the book omits (`firstSwitchTime_qOutCart`,
`poincare_qOutCart`, `hamMax_qOutCart`, `poincare_tau_qOutCart`) and the facts on
`r_scale` (`rScale_spec`, `eq_rScale_of_rScalePoly_eq_zero`, `rScale_bounds`). -/
theorem lemma13_5_2 :
    {x : XiWQuot | poincareAngQuot x = x ∧ hamMaxQuot x = 0} = {qOut, qIn} ∧ qOut ≠ qIn ∧
      poincare qOutCart = ζ ^ 2 • scale rScale qOutCart ∧
      poincare (tau qOutCart) = ζ ^ 2 • scale rScale⁻¹ (tau qOutCart) ∧
      tauQuot qOut = qIn ∧
      qOutCart = equilExact rScale ∧
      ((qOutCart 0).re = -1 ∧ (qOutCart 2).im = 0 ∧ (qOutCart 2).re < 0) ∧
      (1 < rScale ∧ rScalePoly rScale = 0 ∧ ∀ r : ℝ, 1 < r → rScalePoly r = 0 → r = rScale) ∧
      (6.27 < rScale ∧ rScale < 6.28) ∧
      firstSwitchTime qOutCart = 2 * (1 + rScale + rScale ^ 2) / (√3 * (rScale + 1)) ∧
      (7.4 < firstSwitchTime qOutCart ∧ firstSwitchTime qOutCart < 7.41) := by
  have hs0 : 0 < rScale := by linarith [rScale_spec.1]
  refine ⟨?_, l4st_qOut_ne_qIn, poincare_qOutCart, poincare_tau_qOutCart,
    tauQuot_qOut, rfl, qOutCart_normalization,
    ⟨rScale_spec.1, rScale_spec.2, fun r hr hP ↦ eq_rScale_of_rScalePoly_eq_zero hr hP⟩,
    rScale_bounds, firstSwitchTime_qOutCart, firstSwitchTime_qOutCart_bounds⟩
  -- a point `q ≠ 0` with `F(q) = ζ² · (r q₁, r² q₂, r³ q₃)` gives a fixed point of `F_ang`
  have hfix : ∀ {q : Fin 3 → ℂ} (hq : q ≠ 0) (hmem : ang q ∈ XiW) {r : ℝ}, 0 < r →
      poincare q = ζ ^ 2 • scale r q →
      poincareAngQuot (Quotient.mk'' ⟨ang q, hmem⟩) = Quotient.mk'' ⟨ang q, hmem⟩ := by
    intro q hq hmem r hr hF
    change (Quotient.mk'' (poincareAng ⟨ang q, hmem⟩) : XiWQuot) = _
    refine mk_eq_mk_iff_exists_mem_VT.2 ⟨ζ ^ 2, ζ_sq_mem_VT, ?_⟩
    change ang (poincare (ang q)) = ζ ^ 2 • ang q
    rw [ang_poincare_ang hq, hF, (weightedNorm_ang_smul_scale hq hr ζ_sq_mem_VT).2]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hfx, hH⟩
    induction x using Quotient.inductionOn' with | h ξ => ?_
    obtain ⟨hξXi, -⟩ := ξ.2
    have hξ0 : (ξ : Fin 3 → ℂ) ≠ 0 := by
      have := scale_ne_zero_of_mem_Xi one_pos hξXi
      rwa [scale_one] at this
    -- step 1: `F_ang ξ = v ξ` lifts to `F(ξ) = v · (r ξ₁, r² ξ₂, r³ ξ₃)`, `r = φ(F(ξ))`
    change (Quotient.mk'' (poincareAng ξ) : XiWQuot) = Quotient.mk'' ξ at hfx
    obtain ⟨v, hv, hFv⟩ := mk_eq_mk_iff_exists_mem_VT.1 hfx
    have hFξ0 := poincare_ne_zero hξ0
    have hρ := weightedNorm_pos hFξ0
    have hFeq : poincare ξ = v • scale (weightedNorm (poincare ξ)) ξ := by
      conv_lhs => rw [← scale_weightedNorm_ang hFξ0]
      rw [show ang (poincare ξ) = v • (ξ : Fin 3 → ℂ) from hFv, scale_smul]
    have hH' : hamMax ξ = 0 := hH
    have hT := firstSwitchTime_pos hξ0
    have huV := (isFirstControl_firstControl hξ0).1
    -- steps 3–5
    rcases l4st_fixedPoint_cases hξ0 hρ hv hFeq with ⟨hr1, rfl⟩ | ⟨hrs, rfl⟩ | ⟨hrs, rfl⟩
    · rw [hr1] at hFeq
      exact absurd hH' (l4st_hamMax_ne_zero_of_r_eq_one hξ0 hFeq)
    · left
      have hc := l4st_eq_fixedPointCandidate hρ ζ_sq_mem_VT (fun h' ↦ l4i_ζ_sq_ne_one h'.2) hFeq
      rw [hrs] at hc
      obtain ⟨ρ', hρ', v', hv', hv'eq⟩ := (l4st_fixedPointCandidate_virialEquiv huV hT).1
      refine mk_eq_mk_iff_exists_mem_VT.2 ⟨v', hv', ?_⟩
      change (ξ : Fin 3 → ℂ) = v' • ang qOutCart
      rw [← (weightedNorm_ang_smul_scale qOutCart_ne_zero hρ' hv').2, ← hv'eq, ← hc,
        ang_of_mem_Xi hξXi]
    · right
      have hc := l4st_eq_fixedPointCandidate hρ ζ_sq_mem_VT (fun h' ↦ l4i_ζ_sq_ne_one h'.2) hFeq
      rw [hrs] at hc
      obtain ⟨ρ', hρ', v', hv', hv'eq⟩ := (l4st_fixedPointCandidate_virialEquiv huV hT).2
      refine mk_eq_mk_iff_exists_mem_VT.2 ⟨v', hv', ?_⟩
      change (ξ : Fin 3 → ℂ) = v' • ang (tau qOutCart)
      rw [← (weightedNorm_ang_smul_scale tau_qOutCart_ne_zero hρ' hv').2, ← hv'eq, ← hc,
        ang_of_mem_Xi hξXi]
  · rintro (rfl | rfl)
    · exact ⟨hfix qOutCart_ne_zero _ hs0 poincare_qOutCart,
        hamMaxQuot_qOut_qIn.1⟩
    · exact ⟨hfix tau_qOutCart_ne_zero _ (inv_pos.2 hs0) poincare_tau_qOutCart,
        hamMaxQuot_qOut_qIn.2⟩

/-- **Remark 13.5.3** (`rem:spirals`, label of this formalization; unlabelled, TeX 11389–11400). By
the fixed-point equation (13.5.2), the iterates of `F` satisfy
`F^k(q_out) = (r_scale, ζ²)^k · q_out` (the virial action): discrete points on a logarithmic
spiral, moving outward because `r_scale > 1`. Similarly, `F^k(q_in)` are
points on an inward moving logarithmic spiral, `F^k(q_in) = (1/r_scale, ζ²)^k · q_in`.

Proof: induction on `k`, from `F(qOutCart) = ζ² · (r_scale-scaling)(qOutCart)` (Lemma 13.5.2)
and the equivariance of `F` under `V_T` and rescaling (`poincare_smul`,
`poincare_scale`). -/
theorem remark13_5_3 (k : ℕ) :
    poincare^[k] qOutCart = (ζ ^ 2) ^ k • scale (rScale ^ k) qOutCart ∧
      poincare^[k] (tau qOutCart) = (ζ ^ 2) ^ k • scale (rScale⁻¹ ^ k) (tau qOutCart) := by
  have hs0 : 0 < rScale := by linarith [rScale_spec.1]
  have key : ∀ {q : Fin 3 → ℂ} {r : ℝ}, q ≠ 0 → 0 < r → poincare q = ζ ^ 2 • scale r q →
      ∀ k : ℕ, poincare^[k] q = (ζ ^ 2) ^ k • scale (r ^ k) q := by
    intro q r hq hr hF k
    induction k with
    | zero => simp [scale_one]
    | succ k ih =>
      have hrk : 0 < r ^ k := pow_pos hr k
      rw [Function.iterate_succ_apply', ih,
        (poincare_smul (l4i_pow_mem_VT ζ_sq_mem_VT k) (scale_ne_zero hrk hq)).2.2,
        (poincare_scale hrk hq).2.2, hF, scale_smul, scale_scale, smul_smul,
        ← pow_succ, ← pow_succ]
  exact ⟨key qOutCart_ne_zero hs0 lemma13_5_2.2.2.1 k,
    key tau_qOutCart_ne_zero (inv_pos.2 hs0) lemma13_5_2.2.2.2.1 k⟩

end SmoothedPolygons
