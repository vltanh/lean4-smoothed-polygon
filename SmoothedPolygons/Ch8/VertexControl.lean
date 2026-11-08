module

public import SmoothedPolygons.Ch8.Defs
public import SmoothedPolygons.Ch7.ConstantControl
public import SmoothedPolygons.Ch7.Isolated.VertexFlow

/-!
# Constant vertex control does not meet the singular locus (Lemma 8.3.4)

Lemma 8.3.4 (`lem:constant-not-singular`, TeX 7619–7670): an extremal trajectory with constant
control at a vertex of `U_T` does not meet the singular locus. ("This lemma does not rule out the
possibility of a chattering arc converging to the singular locus", TeX 7627–7629: that is the
subject of Part "Mahler" and of the hypothesis `NoChatteringIntoSingularLocus` of
Theorem 16.3.1.)

The book's proof expands the switching functions at a point of `𝒮_sing` to third order. Two slips
(gap G6, checked with sympy): `Λ_R'''(0) = +6 λ_cost [J, P₃]`, not `-6 λ_cost [J, P₃]` (TeX 7648),
and the display TeX 7657–7660 lacks an `=` and the factor `λ_cost`. With
`P_i = Z_{e_i}/⟨J, Z_{e_i}⟩`:
`[J, P₃] ⊥ J, P₃`, `P₁ + P₂ + P₃ = -(3/2) J`, `⟨[J, P₃], P₁⟩ = -2√3 = -⟨[J, P₃], P₂⟩`, and the
control term `-⟨Λ_R(t), P_i⟩` has leading coefficients `(2√3 λ_cost, -2√3 λ_cost, 0) t³` for
`i = 1, 2, 3`. The conclusion is unaffected, and the argument works on either side of the meeting
time separately, which covers a meeting time at an end of the interval (the form in which
Theorem 16.3.1 uses the lemma: "A trajectory cannot reach the singular locus with finitely many
switches", TeX 12818–12819).

## The proof

The book's argument, step by step (`lemma8_3_4`, `l3j_core`):

1. *Constant control.* On the interval the control is the vertex `e_i` almost everywhere, so the
   right-hand sides of the state and costate equations agree almost everywhere with continuous
   functions, and the solution is differentiable with those derivatives
   (`ivf_integral_form_restrict_ae`, FTC). By Lemma 7.1.1 (`lemma7_1_1`), `⟨X, Z_{e_i}⟩` is
   constant, equal to its value `⟨J, Z_{e_i}⟩ = -2/3` at the meeting time, so
   `P = Z_{e_i}/⟨Z_{e_i}, X⟩` is the constant `P_i = Z_{e_i}/⟨J, Z_{e_i}⟩`.
2. *Taylor expansion at the meeting time `t₀`* (`l3j_expansion`), with `s = t - t₀`:
   `X = J + s [P, J] + O(s²)`, `Λ₁ - (3/2) λ_cost J = (3/4) λ_cost s² [J, [P, J]] + O(s³)`
   (so `Λ_{1,cost}(t₀) = Λ_{1,cost}'(t₀) = 0`), and
   `Λ_R = λ_cost s³ [J, P] + O(s⁴)` (so `Λ_R(t₀) = Λ_R'(t₀) = Λ_R''(t₀) = 0` and
   `Λ_R'''(t₀) = 6 λ_cost [J, P]`, gap G6); the cancellation uses
   `[[J, [P, J]], J] = 4 [P, J]` (`J² = -1`).
3. *The algebra* (`l3j_traceForm_bracket_self`, `l3j_pairing`): `⟨[J, P_i], P_i⟩ = 0` and
   `⟨[J, P_i], Z_{e_{i+1}}⟩ = 4√3/3 = -⟨[J, P_i], Z_{e_{i+2}}⟩` (with `P_j = -(3/2) Z_{e_j}` these
   are the book's `⟨[J, P₃], P₁⟩ = -2√3 = -⟨[J, P₃], P₂⟩`).
4. *Maximization.* The maximum condition `H(e_j) ≤ H(e_i)` reads
   `φ_j = ⟨Λ_R, Z_{e_j}⟩ - ⟨Λ_R, P_i⟩ ⟨X, Z_{e_j}⟩ ≤ 0` (as `⟨X, Z_{e_j}⟩ < 0`, Lemma 3.3.4), and
   by steps 2–3, `φ_j = λ_cost s³ ⟨[J, P_i], Z_{e_j}⟩ + O(s⁴)` (`l3j_taylor`). The leading
   coefficients for `j = i + 1, i + 2` are opposite and nonzero, so for `0 < |s|` small one of
   `φ_{i+1}, φ_{i+2}` is positive: on a set of times of positive measure next to `t₀` (on
   whichever side lies in the interval) the maximum condition fails.

"The solutions are analytic" (TeX 7637) is replaced by Taylor expansions with remainder, obtained
by iterating the mean value inequality (`l3j_norm_sub_le`): if `f(t₀) = 0` and
`‖f'(t)‖ ≤ C |t - t₀|ᵏ` then `‖f(t)‖ ≤ C |t - t₀|ᵏ⁺¹`. This needs only the first derivatives of
the solution (which exist because the right-hand sides are continuous), not analyticity nor
higher derivatives; it is cheaper than the explicit solutions of §7.1 (for `Λ_R` these involve
quadratures, `iso_vertexFlow`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-! ### Taylor expansion with remainder by the mean value inequality -/

/-- **One step of the bootstrap.** If `‖f'(x)‖ ≤ C |x - t₀|ᵏ` on `[0, T]`, then
`‖f(x) - f(t₀)‖ ≤ C |x - t₀|ᵏ⁺¹` there (mean value inequality on the segment from `t₀` to `x`). -/
private lemma l3j_norm_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {T t₀ C : ℝ} {k : ℕ}
    (hf : ∀ x ∈ Icc 0 T, HasDerivWithinAt f (f' x) (Icc 0 T) x) (ht₀ : t₀ ∈ Icc 0 T)
    (hb : ∀ x ∈ Icc 0 T, ‖f' x‖ ≤ C * |x - t₀| ^ k) :
    ∀ x ∈ Icc 0 T, ‖f x - f t₀‖ ≤ C * |x - t₀| ^ (k + 1) := by
  intro x hx
  rcases eq_or_ne x t₀ with rfl | hne
  · simp
  have hpos : 0 < |x - t₀| := abs_pos.2 (sub_ne_zero.2 hne)
  have hC : 0 ≤ C :=
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hb x hx)) (pow_pos hpos k)
  have hsub : uIcc t₀ x ⊆ Icc 0 T := ordConnected_Icc.uIcc_subset ht₀ hx
  have key := (convex_uIcc t₀ x).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (C := C * |x - t₀| ^ k)
    (fun y hy ↦ (hf y (hsub hy)).mono hsub)
    (fun y hy ↦ (hb y (hsub hy)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (abs_sub_left_of_mem_uIcc hy) k) hC))
    left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs] at key
  calc ‖f x - f t₀‖ ≤ C * |x - t₀| ^ k * |x - t₀| := key
    _ = C * |x - t₀| ^ (k + 1) := by ring

open scoped Matrix.Norms.Operator in
/-- `‖[A, B]‖ ≤ 2 ‖A‖ ‖B‖` for the operator norm. -/
private lemma l3j_norm_bracket_le (A B : Mat2) : ‖A * B - B * A‖ ≤ 2 * (‖A‖ * ‖B‖) := by
  calc ‖A * B - B * A‖ ≤ ‖A * B‖ + ‖B * A‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * (‖A‖ * ‖B‖) := by ring

open scoped Matrix.Norms.Operator in
/-- `|⟨A, B⟩| ≤ 2 ‖A‖ ‖B‖` for the operator norm (the diagonal entries of `AB` are at most
`‖AB‖`). -/
private lemma l3j_abs_traceForm_le (A B : Mat2) : |traceForm A B| ≤ 2 * (‖A‖ * ‖B‖) := by
  have h0 := Matrix.norm_apply_le_linfty_opNorm (A * B) 0 0
  have h1 := Matrix.norm_apply_le_linfty_opNorm (A * B) 1 1
  rw [Real.norm_eq_abs] at h0 h1
  have hAB := norm_mul_le A B
  unfold traceForm
  rw [Matrix.trace_fin_two]
  calc |(A * B) 0 0 + (A * B) 1 1| ≤ |(A * B) 0 0| + |(A * B) 1 1| := abs_add_le _ _
    _ ≤ 2 * (‖A‖ * ‖B‖) := by linarith

open scoped Matrix.Norms.Operator in
/-- The right-hand side of the costate equation `eqn:lamR` with a constant `P` is bounded by
`‖Λ_R‖` and `‖Λ₁ - (3/2) λ_cost J‖`. -/
private lemma l3j_norm_rhs_le (P R X L : Mat2) (c : ℝ) :
    ‖(P * R - R * P) - traceForm R P • (P * X - X * P) +
        ((-L + c • J) * X - X * (-L + c • J))‖ ≤
      (2 * ‖P‖ + 4 * (‖P‖ * ‖P‖ * ‖X‖)) * ‖R‖ + 2 * (‖L - c • J‖ * ‖X‖) := by
  have e : (-L + c • J) * X - X * (-L + c • J) = -((L - c • J) * X - X * (L - c • J)) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.neg_mul,
      Matrix.mul_neg]
    abel
  rw [e]
  have h1 := l3j_norm_bracket_le P R
  have h4 := l3j_norm_bracket_le (L - c • J) X
  have h5 : ‖traceForm R P • (P * X - X * P)‖ ≤ (2 * (‖R‖ * ‖P‖)) * (2 * (‖P‖ * ‖X‖)) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (l3j_abs_traceForm_le R P) (l3j_norm_bracket_le P X) (norm_nonneg _)
      (by positivity)
  have h6 : ‖(P * R - R * P) - traceForm R P • (P * X - X * P) +
      -((L - c • J) * X - X * (L - c • J))‖ ≤ ‖P * R - R * P‖ +
        ‖traceForm R P • (P * X - X * P)‖ + ‖(L - c • J) * X - X * (L - c • J)‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    gcongr
    exact norm_sub_le _ _
  nlinarith

/-- `[[J, [P, J]], J] = 4 [P, J]` (from `J² = -1`). -/
private lemma l3j_bracket_J (P : Mat2) :
    (J * (P * J - J * P) - (P * J - J * P) * J) * J -
        J * (J * (P * J - J * P) - (P * J - J * P) * J) = (4 : ℝ) • (P * J - J * P) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

/-- `t ↦ c (t - t₀)ⁿ⁺¹` has derivative `c (n + 1) (t - t₀)ⁿ`. -/
private lemma l3j_hasDerivAt_pow (c t₀ t : ℝ) (n : ℕ) :
    HasDerivAt (fun t ↦ c * (t - t₀) ^ (n + 1)) (c * (n + 1) * (t - t₀) ^ n) t := by
  have := (((hasDerivAt_id' t).sub_const t₀).pow (n + 1)).const_mul c
  convert this using 1
  rw [Nat.add_sub_cancel]
  push_cast
  ring

open scoped Matrix.Norms.Operator in
/-- **Taylor expansion at the singular locus** (step 2 of the proof of Lemma 8.3.4). Let
`(X, Λ₁, Λ_R)` solve the state and costate equations on `[0, T]` with a constant `P`, and meet
`𝒮_sing` at `t₀`: `X(t₀) = J`, `Λ₁(t₀) = (3/2) λ_cost J`, `Λ_R(t₀) = 0`. Then
`Λ_R(t) = λ_cost (t - t₀)³ [J, P] + O((t - t₀)⁴)`, i.e. `Λ_R'(t₀) = Λ_R''(t₀) = 0` and
`Λ_R'''(t₀) = 6 λ_cost [J, P]` (gap G6: the book prints `-6`).

The bootstrap (`l3j_norm_sub_le`), with `s = t - t₀`, `Λ_c = Λ₁ - (3/2) λ_cost J`:
`X - J = O(s)`, `X - J - s[P, J] = O(s²)`; `Λ_c = O(s)`, `O(s²)` (from
`Λ₁' = [Λ_c, X] + (3/2) λ_cost [J, X - J]`), `Λ_c - (3/4) λ_cost s² [J, [P, J]] = O(s³)`;
`Λ_R = O(s)`, `O(s²)`, `O(s³)` (from `‖Λ_R'‖ ≤ K₁ ‖Λ_R‖ + K₂ ‖Λ_c‖`), and finally
`Λ_R - λ_cost s³ [J, P] = O(s⁴)`, where the term of order `s²` of `Λ_R'` is
`-(3/4) λ_cost s² [[J, [P, J]], J] = 3 λ_cost s² [J, P]` (`l3j_bracket_J`). -/
private lemma l3j_expansion {T t₀ lam : ℝ} {P : Mat2} {X Λ₁ ΛR : ℝ → Mat2}
    (ht₀ : t₀ ∈ Icc 0 T)
    (hXd : ∀ t ∈ Icc 0 T, HasDerivWithinAt X (P * X t - X t * P) (Icc 0 T) t)
    (h1d : ∀ t ∈ Icc 0 T, HasDerivWithinAt Λ₁ (Λ₁ t * X t - X t * Λ₁ t) (Icc 0 T) t)
    (hRd : ∀ t ∈ Icc 0 T, HasDerivWithinAt ΛR
      ((P * ΛR t - ΛR t * P) - traceForm (ΛR t) P • (P * X t - X t * P) +
        ((-Λ₁ t + (3 / 2 * lam) • J) * X t - X t * (-Λ₁ t + (3 / 2 * lam) • J))) (Icc 0 T) t)
    (hX0 : X t₀ = J) (h10 : Λ₁ t₀ = (3 / 2 * lam) • J) (hR0 : ΛR t₀ = 0) :
    (∃ MX, ∀ t ∈ Icc 0 T, ‖X t‖ ≤ MX) ∧
      ∃ C, ∀ t ∈ Icc 0 T, ‖ΛR t - (lam * (t - t₀) ^ 3) • (J * P - P * J)‖ ≤
        C * |t - t₀| ^ 4 := by
  obtain ⟨MX, hMX⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (fun t ht ↦ (hXd t ht).continuousWithinAt : ContinuousOn X (Icc 0 T))
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (fun t ht ↦ (h1d t ht).continuousWithinAt : ContinuousOn Λ₁ (Icc 0 T))
  obtain ⟨MR, hMR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (fun t ht ↦ (hRd t ht).continuousWithinAt : ContinuousOn ΛR (Icc 0 T))
  refine ⟨⟨MX, hMX⟩, ?_⟩
  have hMX0 : 0 ≤ MX := (norm_nonneg _).trans (hMX t₀ ht₀)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 3 / 2 * lam := ⟨_, rfl⟩
  rw [← hc] at hRd h10
  obtain ⟨A, hA⟩ : ∃ A : Mat2, A = P * J - J * P := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Mat2, B = J * A - A * J := ⟨_, rfl⟩
  have hBJ : B * J - J * B = (4 : ℝ) • A := by rw [hB, hA]; exact l3j_bracket_J P
  -- `X = J + O(s)`
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 2 * (‖P‖ * MX) := ⟨_, rfl⟩
  have hX1 : ∀ t ∈ Icc 0 T, ‖X t - J‖ ≤ C₁ * |t - t₀| ^ 1 := by
    have := l3j_norm_sub_le (k := 0) (C := C₁) hXd ht₀ fun t ht ↦ by
      rw [pow_zero, mul_one, hC₁]
      exact (l3j_norm_bracket_le _ _).trans (by gcongr; exact hMX t ht)
    simpa only [hX0] using this
  -- `X = J + s [P, J] + O(s²)`
  have hX2 : ∀ t ∈ Icc 0 T, ‖X t - (t - t₀) • A - J‖ ≤ 2 * (‖P‖ * C₁) * |t - t₀| ^ 2 := by
    have hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t ↦ X t - (t - t₀) • A)
        (P * (X t - J) - (X t - J) * P) (Icc 0 T) t := by
      intro t ht
      have h2 := ((hasDerivWithinAt_id t (Icc 0 T)).sub_const t₀).smul_const A
      refine ((hXd t ht).sub h2).congr_deriv ?_
      rw [hA, one_smul]
      noncomm_ring
    have hb : ∀ t ∈ Icc 0 T, ‖P * (X t - J) - (X t - J) * P‖ ≤ 2 * (‖P‖ * C₁) * |t - t₀| ^ 1 := by
      intro t ht
      calc _ ≤ 2 * (‖P‖ * ‖X t - J‖) := l3j_norm_bracket_le _ _
        _ ≤ 2 * (‖P‖ * (C₁ * |t - t₀| ^ 1)) := by gcongr; exact hX1 t ht
        _ = 2 * (‖P‖ * C₁) * |t - t₀| ^ 1 := by ring
    simpa only [hX0, sub_self, zero_smul, sub_zero] using l3j_norm_sub_le hd ht₀ hb
  -- `Λ_c = Λ₁ - c J`: one step of the bootstrap
  have hLstep : ∀ (k : ℕ) (a b : ℝ), (∀ t ∈ Icc 0 T, ‖Λ₁ t - c • J‖ ≤ a * |t - t₀| ^ k) →
      (∀ t ∈ Icc 0 T, ‖X t - J‖ ≤ b * |t - t₀| ^ k) →
      ∀ t ∈ Icc 0 T, ‖Λ₁ t - c • J‖ ≤ (2 * MX * a + 2 * |c| * ‖J‖ * b) * |t - t₀| ^ (k + 1) := by
    intro k a b ha hb
    have hb' : ∀ t ∈ Icc 0 T, ‖Λ₁ t * X t - X t * Λ₁ t‖ ≤
        (2 * MX * a + 2 * |c| * ‖J‖ * b) * |t - t₀| ^ k := by
      intro t ht
      have e : Λ₁ t * X t - X t * Λ₁ t = ((Λ₁ t - c • J) * X t - X t * (Λ₁ t - c • J)) +
          c • (J * (X t - J) - (X t - J) * J) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        module
      rw [e]
      have h1 := l3j_norm_bracket_le (Λ₁ t - c • J) (X t)
      have h2 := l3j_norm_bracket_le J (X t - J)
      have hXt := hMX t ht
      have hat := ha t ht
      have hbt := hb t ht
      calc _ ≤ ‖(Λ₁ t - c • J) * X t - X t * (Λ₁ t - c • J)‖ +
            ‖c • (J * (X t - J) - (X t - J) * J)‖ := norm_add_le _ _
        _ ≤ 2 * (a * |t - t₀| ^ k * MX) + |c| * (2 * (‖J‖ * (b * |t - t₀| ^ k))) := by
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
          · exact h1.trans (by gcongr; exact (norm_nonneg _).trans hat)
          · exact h2.trans (by gcongr)
        _ = _ := by ring
    simpa only [h10] using l3j_norm_sub_le h1d ht₀ hb'
  have hL0 : ∀ t ∈ Icc 0 T, ‖Λ₁ t - c • J‖ ≤ (M1 + ‖c • J‖) * |t - t₀| ^ 0 := fun t ht ↦ by
    rw [pow_zero, mul_one]
    exact (norm_sub_le _ _).trans (by gcongr; exact hM1 t ht)
  have hX0' : ∀ t ∈ Icc 0 T, ‖X t - J‖ ≤ (MX + ‖J‖) * |t - t₀| ^ 0 := fun t ht ↦ by
    rw [pow_zero, mul_one]
    exact (norm_sub_le _ _).trans (by gcongr; exact hMX t ht)
  have hL1 := hLstep 0 _ _ hL0 hX0'
  set a₁ := 2 * MX * (M1 + ‖c • J‖) + 2 * |c| * ‖J‖ * (MX + ‖J‖)
  have hL2 := hLstep 1 _ _ hL1 hX1
  set a₂ := 2 * MX * a₁ + 2 * |c| * ‖J‖ * C₁
  -- `Λ_c = (c/2) s² B + O(s³)`
  set C₂ := 2 * (‖P‖ * C₁)
  have hL3 : ∀ t ∈ Icc 0 T, ‖Λ₁ t - (c / 2 * (t - t₀) ^ 2) • B - c • J‖ ≤
      (2 * MX * a₂ + 2 * |c| * ‖J‖ * C₂) * |t - t₀| ^ 3 := by
    have hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t ↦ Λ₁ t - (c / 2 * (t - t₀) ^ 2) • B)
        (((Λ₁ t - c • J) * X t - X t * (Λ₁ t - c • J)) +
          c • (J * (X t - (t - t₀) • A - J) - (X t - (t - t₀) • A - J) * J)) (Icc 0 T) t := by
      intro t ht
      have hq := l3j_hasDerivAt_pow (c / 2) t₀ t 1
      norm_num at hq
      refine ((h1d t ht).sub (hq.hasDerivWithinAt.smul_const B)).congr_deriv ?_
      rw [hB]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      module
    have hb : ∀ t ∈ Icc 0 T, ‖((Λ₁ t - c • J) * X t - X t * (Λ₁ t - c • J)) +
          c • (J * (X t - (t - t₀) • A - J) - (X t - (t - t₀) • A - J) * J)‖ ≤
        (2 * MX * a₂ + 2 * |c| * ‖J‖ * C₂) * |t - t₀| ^ 2 := by
      intro t ht
      have h1 := l3j_norm_bracket_le (Λ₁ t - c • J) (X t)
      have h2 := l3j_norm_bracket_le J (X t - (t - t₀) • A - J)
      have hXt := hMX t ht
      have hat := hL2 t ht
      have hbt := hX2 t ht
      calc _ ≤ ‖(Λ₁ t - c • J) * X t - X t * (Λ₁ t - c • J)‖ +
            ‖c • (J * (X t - (t - t₀) • A - J) - (X t - (t - t₀) • A - J) * J)‖ :=
            norm_add_le _ _
        _ ≤ 2 * (a₂ * |t - t₀| ^ (1 + 1) * MX) + |c| * (2 * (‖J‖ * (C₂ * |t - t₀| ^ 2))) := by
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
          · exact h1.trans (by gcongr; exact (norm_nonneg _).trans hat)
          · exact h2.trans (by gcongr)
        _ = _ := by ring
    simpa only [h10, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_smul, sub_zero] using l3j_norm_sub_le hd ht₀ hb
  set a₃ := 2 * MX * a₂ + 2 * |c| * ‖J‖ * C₂
  -- `Λ_R`: one step of the bootstrap
  set K₁ := 2 * ‖P‖ + 4 * (‖P‖ * ‖P‖ * MX)
  have hRstep : ∀ (k : ℕ) (a b : ℝ), (∀ t ∈ Icc 0 T, ‖ΛR t‖ ≤ a * |t - t₀| ^ k) →
      (∀ t ∈ Icc 0 T, ‖Λ₁ t - c • J‖ ≤ b * |t - t₀| ^ k) →
      ∀ t ∈ Icc 0 T, ‖ΛR t‖ ≤ (K₁ * a + 2 * MX * b) * |t - t₀| ^ (k + 1) := by
    intro k a b ha hb
    have hb' : ∀ t ∈ Icc 0 T, ‖(P * ΛR t - ΛR t * P) - traceForm (ΛR t) P • (P * X t - X t * P) +
        ((-Λ₁ t + c • J) * X t - X t * (-Λ₁ t + c • J))‖ ≤
          (K₁ * a + 2 * MX * b) * |t - t₀| ^ k := by
      intro t ht
      refine (l3j_norm_rhs_le P (ΛR t) (X t) (Λ₁ t) c).trans ?_
      have hat := ha t ht
      have hbt := hb t ht
      have hXt := hMX t ht
      have hK : 2 * ‖P‖ + 4 * (‖P‖ * ‖P‖ * ‖X t‖) ≤ K₁ := by simp only [K₁]; gcongr
      have hK0 : 0 ≤ K₁ := le_trans (by positivity) hK
      have e1 := mul_le_mul hK hat (norm_nonneg _) hK0
      have e2 := mul_le_mul hbt hXt (norm_nonneg _) ((norm_nonneg _).trans hbt)
      calc _ ≤ K₁ * (a * |t - t₀| ^ k) + 2 * ((b * |t - t₀| ^ k) * MX) := by linarith
        _ = _ := by ring
    simpa only [hR0, sub_zero] using l3j_norm_sub_le hRd ht₀ hb'
  have hR0' : ∀ t ∈ Icc 0 T, ‖ΛR t‖ ≤ MR * |t - t₀| ^ 0 := fun t ht ↦ by
    rw [pow_zero, mul_one]; exact hMR t ht
  have hR1 := hRstep 0 _ _ hR0' hL0
  have hR2 := hRstep 1 _ _ hR1 hL1
  have hR3 := hRstep 2 _ _ hR2 hL2
  set b₃ := K₁ * (K₁ * (K₁ * MR + 2 * MX * (M1 + ‖c • J‖)) + 2 * MX * a₁) + 2 * MX * a₂
  -- `Λ_R = λ_cost s³ [J, P] + O(s⁴)`
  have hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt
      (fun t ↦ ΛR t - (lam * (t - t₀) ^ 3) • (J * P - P * J))
      ((P * ΛR t - ΛR t * P) - traceForm (ΛR t) P • (P * X t - X t * P) -
        (c / 2 * (t - t₀) ^ 2) • (B * (X t - J) - (X t - J) * B) -
        ((Λ₁ t - (c / 2 * (t - t₀) ^ 2) • B - c • J) * X t -
          X t * (Λ₁ t - (c / 2 * (t - t₀) ^ 2) • B - c • J))) (Icc 0 T) t := by
    intro t ht
    have hq := l3j_hasDerivAt_pow lam t₀ t 2
    norm_num at hq
    refine ((hRd t ht).sub (hq.hasDerivWithinAt.smul_const (J * P - P * J))).congr_deriv ?_
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.add_mul, Matrix.mul_add]
    rw [hA] at hBJ
    rw [hc]
    linear_combination (norm := module) (-(3 / 4 * lam * (t - t₀) ^ 2)) • hBJ
  have hb : ∀ t ∈ Icc 0 T, ‖(P * ΛR t - ΛR t * P) - traceForm (ΛR t) P • (P * X t - X t * P) -
        (c / 2 * (t - t₀) ^ 2) • (B * (X t - J) - (X t - J) * B) -
        ((Λ₁ t - (c / 2 * (t - t₀) ^ 2) • B - c • J) * X t -
          X t * (Λ₁ t - (c / 2 * (t - t₀) ^ 2) • B - c • J))‖ ≤
      (K₁ * b₃ + |c| * ‖B‖ * C₁ + 2 * MX * a₃) * |t - t₀| ^ 3 := by
    intro t ht
    have hs2 : |c / 2 * (t - t₀) ^ 2| = |c| / 2 * |t - t₀| ^ 2 := by
      rw [abs_mul, abs_div, abs_two, abs_pow]
    have h1 := l3j_norm_bracket_le P (ΛR t)
    have h2 : ‖traceForm (ΛR t) P • (P * X t - X t * P)‖ ≤
        (2 * (‖ΛR t‖ * ‖P‖)) * (2 * (‖P‖ * ‖X t‖)) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (l3j_abs_traceForm_le _ _) (l3j_norm_bracket_le P (X t)) (norm_nonneg _)
        (by positivity)
    have h3 : ‖(c / 2 * (t - t₀) ^ 2) • (B * (X t - J) - (X t - J) * B)‖ ≤
        |c| / 2 * |t - t₀| ^ 2 * (2 * (‖B‖ * (C₁ * |t - t₀| ^ 1))) := by
      rw [norm_smul, Real.norm_eq_abs, hs2]
      gcongr
      exact (l3j_norm_bracket_le _ _).trans (by gcongr; exact hX1 t ht)
    have h4 := l3j_norm_bracket_le (Λ₁ t - (c / 2 * (t - t₀) ^ 2) • B - c • J) (X t)
    have hXt := hMX t ht
    have hRt := hR3 t ht
    have hLt := hL3 t ht
    have hK₁ : 0 ≤ K₁ := by positivity
    calc _ ≤ ‖P * ΛR t - ΛR t * P‖ + ‖traceForm (ΛR t) P • (P * X t - X t * P)‖ +
          ‖(c / 2 * (t - t₀) ^ 2) • (B * (X t - J) - (X t - J) * B)‖ +
          ‖(Λ₁ t - (c / 2 * (t - t₀) ^ 2) • B - c • J) * X t -
            X t * (Λ₁ t - (c / 2 * (t - t₀) ^ 2) • B - c • J)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ K₁ * ‖ΛR t‖ + |c| / 2 * |t - t₀| ^ 2 * (2 * (‖B‖ * (C₁ * |t - t₀| ^ 1))) +
          2 * (‖Λ₁ t - (c / 2 * (t - t₀) ^ 2) • B - c • J‖ * MX) := by
          have h2' : (2 * (‖ΛR t‖ * ‖P‖)) * (2 * (‖P‖ * ‖X t‖)) ≤
              4 * (‖P‖ * ‖P‖ * MX) * ‖ΛR t‖ := by
            have := mul_le_mul_of_nonneg_left hXt
              (by positivity : (0 : ℝ) ≤ 4 * (‖ΛR t‖ * ‖P‖ * ‖P‖))
            nlinarith
          have h4' : 2 * (‖Λ₁ t - (c / 2 * (t - t₀) ^ 2) • B - c • J‖ * ‖X t‖) ≤
              2 * (‖Λ₁ t - (c / 2 * (t - t₀) ^ 2) • B - c • J‖ * MX) := by gcongr
          have : K₁ * ‖ΛR t‖ = 2 * (‖P‖ * ‖ΛR t‖) + 4 * (‖P‖ * ‖P‖ * MX) * ‖ΛR t‖ := by ring
          linarith
      _ ≤ K₁ * (b₃ * |t - t₀| ^ (2 + 1)) +
          |c| / 2 * |t - t₀| ^ 2 * (2 * (‖B‖ * (C₁ * |t - t₀| ^ 1))) +
          2 * ((a₃ * |t - t₀| ^ 3) * MX) := by gcongr
      _ = (K₁ * b₃ + |c| * ‖B‖ * C₁ + 2 * MX * a₃) * |t - t₀| ^ 3 := by ring
  refine ⟨K₁ * b₃ + |c| * ‖B‖ * C₁ + 2 * MX * a₃, fun t ht ↦ ?_⟩
  simpa only [hR0, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_smul, sub_zero] using l3j_norm_sub_le hd ht₀ hb t ht

/-! ### The algebra at the singular locus -/

/-- `⟨[J, P], P⟩ = 0`. -/
private lemma l3j_traceForm_bracket_self (P : Mat2) : traceForm (J * P - P * J) P = 0 := by
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
    J, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  ring

/-- `P_i = Z_{e_i}/⟨Z_{e_i}, J⟩ = -(3/2) Z_{e_i}`, since `⟨Z_{e_i}, J⟩ = -2/3`. -/
private lemma l3j_controlP_J (i : Fin 3) :
    controlP (vertex i) J = (-(3 / 2) : ℝ) • controlMatrix (vertex i) := by
  have h : traceForm (controlMatrix (vertex i)) J = -(2 / 3) := by
    fin_cases i <;>
      simp [traceForm, controlMatrix, vertex, J, Matrix.trace_fin_two] <;> norm_num
  unfold controlP
  rw [h]
  norm_num

/-- **The pairings** (step 3 of the proof of Lemma 8.3.4):
`⟨[J, P_i], Z_{e_{i+1}}⟩ = 4√3/3 = -⟨[J, P_i], Z_{e_{i+2}}⟩`. With `P_j = -(3/2) Z_{e_j}` these
are the book's `⟨[J, P₃], P₁⟩ = -2√3 = -⟨[J, P₃], P₂⟩` (TeX 7653). -/
private lemma l3j_pairing (i : Fin 3) :
    traceForm (J * controlP (vertex i) J - controlP (vertex i) J * J)
        (controlMatrix (vertex (i + 1))) = 4 * √3 / 3 ∧
      traceForm (J * controlP (vertex i) J - controlP (vertex i) J * J)
        (controlMatrix (vertex (i + 2))) = -(4 * √3 / 3) := by
  rw [l3j_controlP_J]
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  fin_cases i <;>
    simp [traceForm, controlMatrix, vertex, J, Matrix.trace_fin_two] <;>
    constructor <;> field_simp <;> linarith

open scoped Matrix.Norms.Operator in
/-- **Expansion of the switching functions** (steps 2–3 of the proof of Lemma 8.3.4). In the
situation of `l3j_expansion`, for every matrix `Z`,
`⟨Λ_R, Z⟩ - ⟨Λ_R, P⟩ ⟨X, Z⟩ = λ_cost (t - t₀)³ ⟨[J, P], Z⟩ + O((t - t₀)⁴)`, using
`⟨[J, P], P⟩ = 0` (`l3j_traceForm_bracket_self`) and the boundedness of `X`. -/
private lemma l3j_taylor {T t₀ lam : ℝ} {P : Mat2} {X Λ₁ ΛR : ℝ → Mat2}
    (ht₀ : t₀ ∈ Icc 0 T)
    (hXd : ∀ t ∈ Icc 0 T, HasDerivWithinAtEntrywise X (P * X t - X t * P) (Icc 0 T) t)
    (h1d : ∀ t ∈ Icc 0 T, HasDerivWithinAtEntrywise Λ₁ (Λ₁ t * X t - X t * Λ₁ t) (Icc 0 T) t)
    (hRd : ∀ t ∈ Icc 0 T, HasDerivWithinAtEntrywise ΛR
      ((P * ΛR t - ΛR t * P) - traceForm (ΛR t) P • (P * X t - X t * P) +
        ((-Λ₁ t + (3 / 2 * lam) • J) * X t - X t * (-Λ₁ t + (3 / 2 * lam) • J))) (Icc 0 T) t)
    (hX0 : X t₀ = J) (h10 : Λ₁ t₀ = (3 / 2 * lam) • J) (hR0 : ΛR t₀ = 0) (Z : Mat2) :
    ∃ C, ∀ t ∈ Icc 0 T, |traceForm (ΛR t) Z - traceForm (ΛR t) P * traceForm (X t) Z -
      lam * (t - t₀) ^ 3 * traceForm (J * P - P * J) Z| ≤ C * |t - t₀| ^ 4 := by
  obtain ⟨⟨MX, hMX⟩, C, hC⟩ := l3j_expansion ht₀ (fun t ht ↦ (hXd t ht).hasDerivWithinAt)
    (fun t ht ↦ (h1d t ht).hasDerivWithinAt) (fun t ht ↦ (hRd t ht).hasDerivWithinAt) hX0 h10
    hR0
  refine ⟨(2 * ‖Z‖ + 4 * (‖P‖ * MX * ‖Z‖)) * C, fun t ht ↦ ?_⟩
  obtain ⟨E, hE⟩ : ∃ E, E = ΛR t - (lam * (t - t₀) ^ 3) • (J * P - P * J) := ⟨_, rfl⟩
  have hEt : ‖E‖ ≤ C * |t - t₀| ^ 4 := hE ▸ hC t ht
  have lin : ∀ M, traceForm (ΛR t) M =
      lam * (t - t₀) ^ 3 * traceForm (J * P - P * J) M + traceForm E M := by
    intro M
    rw [show ΛR t = (lam * (t - t₀) ^ 3) • (J * P - P * J) + E by rw [hE]; abel]
    simp only [traceForm, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
      smul_eq_mul]
  rw [lin Z, lin P, l3j_traceForm_bracket_self]
  have hXt := hMX t ht
  have hMX0 : 0 ≤ MX := (norm_nonneg _).trans hXt
  have h1 := l3j_abs_traceForm_le E Z
  have h2 := l3j_abs_traceForm_le E P
  have h3 : |traceForm (X t) Z| ≤ 2 * (MX * ‖Z‖) :=
    (l3j_abs_traceForm_le (X t) Z).trans (by gcongr)
  calc _ = |traceForm E Z - traceForm E P * traceForm (X t) Z| := by ring_nf
    _ ≤ |traceForm E Z| + |traceForm E P| * |traceForm (X t) Z| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ 2 * (‖E‖ * ‖Z‖) + 2 * (‖E‖ * ‖P‖) * (2 * (MX * ‖Z‖)) := by
        gcongr
    _ = (2 * ‖Z‖ + 4 * (‖P‖ * MX * ‖Z‖)) * ‖E‖ := by ring
    _ ≤ (2 * ‖Z‖ + 4 * (‖P‖ * MX * ‖Z‖)) * (C * |t - t₀| ^ 4) := by gcongr
    _ = _ := by ring

/-! ### The maximization argument -/

/-- **Lemma 8.3.4 after the time shift.** A solution of the state–costate system on `[0, T]`
whose control is almost everywhere the vertex `e_i` does not meet the singular locus at any
`t₀ ∈ [0, T]`: `λ_cost ≠ 0`, `Λ₁(t₀) = (3/2) λ_cost J`, `X(t₀) = J`, `Λ_R(t₀) = 0` is impossible.

Proof (the book's, TeX 7632–7670): steps 1–4 of the module docstring. On the side of `t₀` that
lies in `[0, T]`, for `0 < |t - t₀| < δ`, one of `φ_{i+1}(t), φ_{i+2}(t)` is positive, against
the maximum condition, which holds for almost every `t` (this side has positive measure). -/
private lemma l3j_core {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsStateCostateSolution T u g X Λ₁ ΛR lam) {i : Fin 3}
    (hu : ∀ᵐ t, t ∈ Ioo 0 T → u t = vertex i) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) (hlam : lam ≠ 0)
    (h1 : Λ₁ t₀ = (3 / 2 * lam) • J) (hX : X t₀ = J) (hR : ΛR t₀ = 0) : False := by
  obtain ⟨⟨hT, -, -, hst, -, hXI⟩, -, -, hI1, hIR, hmax⟩ := h
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  have h1c : ContinuousOn Λ₁ (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hI1
  have hRc : ContinuousOn ΛR (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hIR
  have hstar : ∀ t ∈ Icc 0 T, IsStarState (X t) := fun t ht ↦ (hst t ht).2
  have hvm : vertex i ∈ controlSimplex := poly_vertex_mem i
  -- Step 1: the derivatives; `P` is constant (Lemma 7.1.1)
  have hPc := poly_controlP_continuousOn hXc hvm hstar
  have hwX : ContinuousOn (fun t ↦ controlP (vertex i) (X t) * X t -
      X t * controlP (vertex i) (X t)) (Icc 0 T) := (hPc.mul hXc).sub (hXc.mul hPc)
  have hformX := ivf_integral_form_restrict_ae hXI le_rfl hT.le le_rfl hwX (by
    filter_upwards [hu] with t ht htI
    rw [ht htI])
  have hXd := fun t (ht : t ∈ Icc 0 T) ↦
    Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hformX ht (hwX t ht)
  have hconst := lemma7_1_1 _ X _ _ hXd
  obtain ⟨P, hP⟩ : ∃ P, P = controlP (vertex i) J := ⟨_, rfl⟩
  have hPX : ∀ t ∈ Icc 0 T, controlP (vertex i) (X t) = P := by
    intro t ht
    rw [hP]
    unfold controlP
    rw [poly_traceForm_comm _ (X t), hconst t ht, ← hconst t₀ ht₀, hX, poly_traceForm_comm J]
  have hXd' : ∀ t ∈ Icc 0 T, HasDerivWithinAtEntrywise X (P * X t - X t * P) (Icc 0 T) t := by
    intro t ht
    have := hXd t ht
    rwa [hPX t ht] at this
  have hw1 : ContinuousOn (fun t ↦ Λ₁ t * X t - X t * Λ₁ t) (Icc 0 T) :=
    (h1c.mul hXc).sub (hXc.mul h1c)
  have h1d : ∀ t ∈ Icc 0 T, HasDerivWithinAtEntrywise Λ₁ (Λ₁ t * X t - X t * Λ₁ t)
      (Icc 0 T) t :=
    fun t ht ↦ Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hI1 ht (hw1 t ht)
  have hwR := poly_costateRHS_continuousOn lam hvm h1c hRc hXc hstar
  have hformR := ivf_integral_form_restrict_ae hIR le_rfl hT.le le_rfl hwR (by
    filter_upwards [hu] with t ht htI
    rw [ht htI]
    rfl)
  have hRd : ∀ t ∈ Icc 0 T, HasDerivWithinAtEntrywise ΛR
      ((P * ΛR t - ΛR t * P) - traceForm (ΛR t) P • (P * X t - X t * P) +
        ((-Λ₁ t + (3 / 2 * lam) • J) * X t - X t * (-Λ₁ t + (3 / 2 * lam) • J))) (Icc 0 T) t := by
    intro t ht
    have := Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hformR ht (hwR t ht)
    simp only [costateRHS, hPX t ht] at this
    exact this
  -- Steps 2–3: the expansions of `φ_{i+1}` and `φ_{i+2}`
  obtain ⟨Ca, hCa⟩ := l3j_taylor ht₀ hXd' h1d hRd hX h1 hR (controlMatrix (vertex (i + 1)))
  obtain ⟨Cb, hCb⟩ := l3j_taylor ht₀ hXd' h1d hRd hX h1 hR (controlMatrix (vertex (i + 2)))
  obtain ⟨hKa, hKb⟩ := l3j_pairing i
  rw [← hP] at hKa hKb
  rw [hKa] at hCa
  rw [hKb] at hCb
  -- Step 4: the maximum condition gives `φ_j ≤ 0` almost everywhere
  have hφ : ∀ᵐ t, t ∈ Ioo 0 T → ∀ j : Fin 3, traceForm (ΛR t) (controlMatrix (vertex j)) -
      traceForm (ΛR t) P * traceForm (X t) (controlMatrix (vertex j)) ≤ 0 := by
    filter_upwards [hmax, hu] with t hmt hut htI j
    have htc : t ∈ Icc 0 T := Ioo_subset_Icc_self htI
    have hle := (hmt htI).2 (vertex j) (poly_vertex_mem j)
    rw [hut htI] at hle
    simp only [hamiltonian] at hle
    have hneg : traceForm (X t) (controlMatrix (vertex j)) < 0 := by
      rw [poly_traceForm_comm]
      exact poly_traceForm_neg (poly_vertex_mem j) (hstar t htc)
    have hPi : traceForm (ΛR t) (controlMatrix (vertex i)) /
        traceForm (X t) (controlMatrix (vertex i)) = traceForm (ΛR t) P := by
      rw [← hPX t htc]
      unfold controlP
      rw [poly_traceForm_comm (controlMatrix (vertex i)) (X t)]
      simp only [traceForm, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      ring
    have hle' : traceForm (ΛR t) P ≤ traceForm (ΛR t) (controlMatrix (vertex j)) /
        traceForm (X t) (controlMatrix (vertex j)) := by linarith
    rw [le_div_iff_of_neg hneg] at hle'
    linarith
  -- a set of times of positive measure next to `t₀` where one of `φ_{i+1}, φ_{i+2}` is positive
  have hκ : (0 : ℝ) < 4 * √3 / 3 := by positivity
  have hl0 : 0 < |lam| := abs_pos.2 hlam
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = |Ca| + |Cb| + 1 := ⟨_, rfl⟩
  have hCm0 : 0 < Cm := by rw [hCm]; positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = |lam| * (4 * √3 / 3) / (2 * Cm) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hne : (Ioo (t₀ - δ) (t₀ + δ) ∩ Ioo 0 T).Nonempty :=
    mem_closure_iff.1 (by rw [closure_Ioo hT.ne]; exact ht₀) _ isOpen_Ioo
      ⟨by linarith, by linarith⟩
  refine ((isOpen_Ioo.inter isOpen_Ioo).measure_pos volume hne).ne' ?_
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hφ, (countable_singleton t₀).ae_notMem volume] with t hφt ht₀' htW
  obtain ⟨⟨htδ1, htδ2⟩, htI⟩ := htW
  have htc : t ∈ Icc 0 T := Ioo_subset_Icc_self htI
  have hs : t - t₀ ≠ 0 := sub_ne_zero.2 (by simpa using ht₀')
  have hsδ : |t - t₀| < δ := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have ha := hφt htI (i + 1)
  have hb := hφt htI (i + 2)
  have hCat := abs_le.1 (hCa t htc)
  have hCbt := abs_le.1 (hCb t htc)
  have hs4 : 0 ≤ |t - t₀| ^ 4 := by positivity
  have hCa' : Ca * |t - t₀| ^ 4 ≤ Cm * |t - t₀| ^ 4 :=
    mul_le_mul_of_nonneg_right (by rw [hCm]; linarith [le_abs_self Ca, abs_nonneg Cb]) hs4
  have hCb' : Cb * |t - t₀| ^ 4 ≤ Cm * |t - t₀| ^ 4 :=
    mul_le_mul_of_nonneg_right (by rw [hCm]; linarith [le_abs_self Cb, abs_nonneg Ca]) hs4
  have hneg : lam * (t - t₀) ^ 3 * -(4 * √3 / 3) = -(lam * (t - t₀) ^ 3 * (4 * √3 / 3)) := by
    ring
  rw [hneg] at hCbt
  -- `|λ_cost (t - t₀)³ · 4√3/3| ≤ Cm |t - t₀|⁴`
  have hmain : |lam * (t - t₀) ^ 3 * (4 * √3 / 3)| ≤ Cm * |t - t₀| ^ 4 :=
    abs_le.2 ⟨by linarith [hCbt.1], by linarith [hCat.1]⟩
  rw [abs_mul, abs_mul, abs_pow, abs_of_pos hκ] at hmain
  have hs3 : 0 < |t - t₀| ^ 3 := pow_pos (abs_pos.2 hs) 3
  have hlt : Cm * |t - t₀| < |lam| * (4 * √3 / 3) / 2 := by
    calc Cm * |t - t₀| < Cm * δ := mul_lt_mul_of_pos_left hsδ hCm0
      _ = |lam| * (4 * √3 / 3) / 2 := by rw [hδ]; field_simp
  have hL : 0 < |lam| * (4 * √3 / 3) * |t - t₀| ^ 3 := by positivity
  have h5 := mul_lt_mul_of_pos_right hlt hs3
  have h6 : |lam| * (4 * √3 / 3) * |t - t₀| ^ 3 ≤ Cm * |t - t₀| * |t - t₀| ^ 3 := by
    calc _ = |lam| * |t - t₀| ^ 3 * (4 * √3 / 3) := by ring
      _ ≤ Cm * |t - t₀| ^ 4 := hmain
      _ = _ := by ring
  have h7 : |lam| * (4 * √3 / 3) / 2 * |t - t₀| ^ 3 =
      |lam| * (4 * √3 / 3) * |t - t₀| ^ 3 / 2 := by ring
  linarith

/-- **Lemma 8.3.4** (`lem:constant-not-singular`). An extremal lifted trajectory on `[a, b]` whose
control is constant (almost everywhere) at a vertex of `U_T` does not meet the singular locus at
any time of `[a, b]`.

Proof (the book's, TeX 7632–7670, with the sign of G6 corrected): suppose the lift is in `𝒮_sing`
at `t₀ ∈ [a, b]`, with control `e_i`. Then `λ_cost ≠ 0`, `X(t₀) = J`,
`Λ₁(t₀) = (3/2) λ_cost J`, `Λ_R(t₀) = 0` (`l3st_mem_singularLocus_iff`). With constant control,
`P` is constant (Lemma 7.1.1, `lemma7_1_1`), and the state and costate have Taylor expansions
with remainder at `t₀` (the book: "the solutions are analytic"; only first derivatives and the
mean value inequality are used, `l3j_expansion`):
`Λ_{1,cost}'(t₀) = 0`, `Λ_R'(t₀) = Λ_R''(t₀) = 0` and `Λ_R'''(t₀) = 6 λ_cost [J, P_i]`, so the
control-dependent term at `e_j` is
`-⟨Λ_R(t), P_j⟩ = -(t - t₀)³ λ_cost ⟨[J, P_i], P_j⟩ + O((t - t₀)⁴)`,
with `⟨[J, P_i], P_{i+1}⟩ = -⟨[J, P_i], P_{i+2}⟩ = -2√3` and `⟨[J, P_i], P_i⟩ = 0`
(`l3j_pairing`, `l3j_traceForm_bracket_self`). For `t ≠ t₀` near `t₀` on either side, one of
`e_{i+1}, e_{i+2}` gives a strictly larger Hamiltonian than `e_i`, against the maximum condition
for the control `e_i` (which holds almost everywhere); one side of `t₀` lies in `[a, b]`
(`l3j_core`, after the time shift `t ↦ a + t` of `IsExtremalOn`). The book treats `e₃` and the
other vertices "say"; here the three vertices are computed alike. -/
theorem lemma8_3_4 {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) {i : Fin 3}
    (hu : ∀ᵐ t, t ∈ Ioo a b → u t = vertex i) :
    ∀ t ∈ Icc a b, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus := by
  intro t ht hsing
  obtain ⟨hl, h1, hX, hR⟩ := (l3st_mem_singularLocus_iff h ht).1 hsing
  have hu' : ∀ᵐ s, s ∈ Ioo 0 (b - a) → u (a + s) = vertex i := by
    filter_upwards [(measurePreserving_add_left volume a).quasiMeasurePreserving.ae hu]
      with s hs hs'
    exact hs ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
  have e : a + (t - a) = t := by ring
  exact l3j_core h hu' (t₀ := t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩ hl
    (by simp only [e]; exact h1) (by simp only [e]; exact hX) (by simp only [e]; exact hR)

end SmoothedPolygons
