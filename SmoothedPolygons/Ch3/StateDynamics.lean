module

public import SmoothedPolygons.Ch2.MultiCurve
public import Basic.Analysis.Calculus.MatrixEntrywise
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import SmoothedPolygons.AppA.MatrixIdentities
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Analysis.Complex.RealDeriv
public import SmoothedPolygons.Ch3.Jacobi

/-!
# State dynamics in the Lie group (§3.1)

A multi-curve `σ` determines a curve `g` in `SL₂(ℝ)` with `σ_j(t) = g(t) s_j` (Theorem 3.1.1), and
the curve `X = g⁻¹g'` in `𝔰𝔩₂(ℝ)` (Definition 3.1.3, Theorem 3.1.4). For balanced disks, `X`
satisfies the star inequalities (Corollary 3.1.6), and a reparameterization makes `det X = 1`
(Proposition 3.1.9, Corollaries 3.1.10, 3.1.11).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Matrix

/-- `det A · tr(A⁻¹ B)` for `2 × 2` matrices, written out (`A⁻¹ = adj A / det A`): the right side
is the derivative of `det` at `A` in the direction `B` (`HasDerivAtEntrywise.det_fin_two`). -/
private lemma sd_det_mul_trace_inv_mul (A B : Mat2) (h : A.det ≠ 0) :
    A.det * (A⁻¹ * B).trace =
      B 0 0 * A 1 1 + A 0 0 * B 1 1 - (B 0 1 * A 1 0 + A 0 1 * B 1 0) := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
  simp [Matrix.trace_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  field_simp
  ring

/-- If `det g ≡ 1` on `S`, then `g⁻¹g'` is traceless (derivative of `det g` within `S`). -/
private lemma sd_trace_eq_zero_of_det {g : ℝ → Mat2} {g' : Mat2} {S : Set ℝ} {t : ℝ}
    (hS : UniqueDiffWithinAt ℝ S t) (ht : t ∈ S) (hg : HasDerivWithinAtEntrywise g g' S t)
    (hdet : ∀ x ∈ S, (g x).det = 1) : ((g t)⁻¹ * g').trace = 0 := by
  have h2 : HasDerivWithinAt (fun x ↦ (g x).det) 0 S t :=
    (hasDerivWithinAt_const t S (1 : ℝ)).congr (fun x hx ↦ hdet x hx) (hdet t ht)
  have h3 := sd_det_mul_trace_inv_mul (g t) g' (by rw [hdet t ht]; norm_num)
  rw [hdet t ht, one_mul] at h3
  rw [h3, hS.eq_deriv S hg.det_fin_two h2]

/-- `f` is Lipschitz and bounded on `s`. -/
private def sd_LipBdd (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  (∃ K, LipschitzOnWith K f s) ∧ ∃ M, ∀ x ∈ s, |f x| ≤ M

private lemma sd_LipBdd_const (c : ℝ) (s : Set ℝ) : sd_LipBdd (fun _ ↦ c) s :=
  ⟨⟨0, (LipschitzWith.const c).lipschitzOnWith⟩, |c|, fun _ _ ↦ le_rfl⟩

private lemma sd_LipBdd_congr {f g : ℝ → ℝ} {s : Set ℝ} (hf : sd_LipBdd f s)
    (h : Set.EqOn f g s) : sd_LipBdd g s := by
  obtain ⟨⟨K, hK⟩, M, hM⟩ := hf
  exact ⟨⟨K, fun x hx y hy ↦ by rw [← h hx, ← h hy]; exact hK hx hy⟩, M,
    fun x hx ↦ by rw [← h hx]; exact hM x hx⟩

private lemma sd_LipBdd_add {f g : ℝ → ℝ} {s : Set ℝ} (hf : sd_LipBdd f s)
    (hg : sd_LipBdd g s) : sd_LipBdd (fun x ↦ f x + g x) s := by
  obtain ⟨⟨Kf, hKf⟩, Mf, hMf⟩ := hf
  obtain ⟨⟨Kg, hKg⟩, Mg, hMg⟩ := hg
  exact ⟨⟨_, hKf.add hKg⟩, Mf + Mg,
    fun x hx ↦ (abs_add_le _ _).trans (add_le_add (hMf x hx) (hMg x hx))⟩

private lemma sd_LipBdd_neg {f : ℝ → ℝ} {s : Set ℝ} (hf : sd_LipBdd f s) :
    sd_LipBdd (fun x ↦ -f x) s := by
  obtain ⟨⟨Kf, hKf⟩, Mf, hMf⟩ := hf
  exact ⟨⟨_, hKf.neg⟩, Mf, fun x hx ↦ by rw [abs_neg]; exact hMf x hx⟩

private lemma sd_LipBdd_sub {f g : ℝ → ℝ} {s : Set ℝ} (hf : sd_LipBdd f s)
    (hg : sd_LipBdd g s) : sd_LipBdd (fun x ↦ f x - g x) s := by
  simpa only [sub_eq_add_neg] using sd_LipBdd_add hf (sd_LipBdd_neg hg)

/-- The product of two bounded Lipschitz functions is Lipschitz (and bounded). -/
private lemma sd_LipBdd_mul {f g : ℝ → ℝ} {s : Set ℝ} (hf : sd_LipBdd f s)
    (hg : sd_LipBdd g s) : sd_LipBdd (fun x ↦ f x * g x) s := by
  obtain ⟨⟨Kf, hKf⟩, Mf, hMf⟩ := hf
  obtain ⟨⟨Kg, hKg⟩, Mg, hMg⟩ := hg
  refine ⟨⟨_, LipschitzOnWith.of_dist_le' (K := Mf * Kg + Mg * Kf) fun x hx y hy ↦ ?_⟩,
    Mf * Mg, fun x hx ↦ ?_⟩
  · have h1 := hKf.dist_le_mul x hx y hy
    have h2 := hKg.dist_le_mul x hx y hy
    have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf x hx)
    have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg y hy)
    simp only [Real.dist_eq] at h1 h2 ⊢
    calc |f x * g x - f y * g y| = |f x * (g x - g y) + g y * (f x - f y)| := by
          congr 1; ring
      _ ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ Mf * (Kg * |x - y|) + Mg * (Kf * |x - y|) := by
          gcongr
          · exact hMf x hx
          · exact hMg y hy
      _ = (Mf * Kg + Mg * Kf) * |x - y| := by ring
  · rw [abs_mul]
    exact mul_le_mul (hMf x hx) (hMg x hx) (abs_nonneg _) ((abs_nonneg _).trans (hMf x hx))

private lemma sd_LipBdd_div_const {f : ℝ → ℝ} {s : Set ℝ} (hf : sd_LipBdd f s) (c : ℝ) :
    sd_LipBdd (fun x ↦ f x / c) s := by
  simpa only [div_eq_mul_inv] using sd_LipBdd_mul hf (sd_LipBdd_const c⁻¹ s)

/-- On a compact set, a Lipschitz function is bounded. -/
private lemma sd_LipBdd_of_compact {f : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s)
    (hf : ∃ K, LipschitzOnWith K f s) : sd_LipBdd f s := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn hK.continuousOn
  exact ⟨⟨K, hK⟩, M, fun x hx ↦ by simpa [Real.norm_eq_abs] using hM x hx⟩

/-- The matrix `A` with `A s = v` and `A s' = w` (when `det(s, s') ≠ 0`): the matrix with columns
`v, w` times the inverse of the matrix with columns `s, s'`. -/
private noncomputable def sd_mat (v w s s' : Fin 2 → ℝ) : Mat2 :=
  Matrix.of fun i j ↦ (v i * ![s' 1, -s' 0] j - w i * ![s 1, -s 0] j) / det2 s s'

private lemma sd_mat_mulVec_left {v w s s' : Fin 2 → ℝ} (hd : det2 s s' ≠ 0) :
    sd_mat v w s s' *ᵥ s = v := by
  ext i
  simp only [sd_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  simp only [det2]
  ring

private lemma sd_mat_mulVec_right {v w s s' : Fin 2 → ℝ} (hd : det2 s s' ≠ 0) :
    sd_mat v w s s' *ᵥ s' = w := by
  ext i
  simp only [sd_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  simp only [det2]
  ring

/-- A `2 × 2` matrix is determined by its values on a basis `s, s'`. -/
private lemma sd_eq_mat {A : Mat2} {v w s s' : Fin 2 → ℝ} (hd : det2 s s' ≠ 0)
    (h : A *ᵥ s = v) (h' : A *ᵥ s' = w) : A = sd_mat v w s s' := by
  ext i j
  have e := congrFun h i
  have e' := congrFun h' i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e e'
  simp only [sd_mat, Matrix.of_apply]
  rw [eq_div_iff hd]
  fin_cases j
  · simp only [det2, Fin.zero_eta, Matrix.cons_val_zero]
    linear_combination s' 1 * e - s 1 * e'
  · simp only [det2, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    linear_combination -s' 0 * e + s 0 * e'

private lemma sd_det_mat {v w s s' : Fin 2 → ℝ} (hd : det2 s s' ≠ 0) :
    (sd_mat v w s s').det = det2 v w / det2 s s' := by
  simp only [sd_mat, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  field_simp
  simp only [det2]
  ring

/-- The linear relations of a multi-point: every `s_j` is a combination of `s₀, s₂`. -/
private lemma sd_multiPoint_rel {s : ZMod 6 → Fin 2 → ℝ} (hs : IsMultiPoint s) :
    s 1 = s 0 + s 2 ∧ s 3 = -s 0 ∧ s 4 = -(s 0 + s 2) ∧ s 5 = -s 2 := by
  obtain ⟨h0, h3, -⟩ := hs 0
  obtain ⟨-, h4, -⟩ := hs 1
  obtain ⟨-, h5, -⟩ := hs 2
  have e1 : (0 : ZMod 6) + 2 = 2 := rfl
  have e2 : (0 : ZMod 6) + 4 = 4 := rfl
  have e3 : (0 : ZMod 6) + 3 = 3 := rfl
  have e4 : (1 : ZMod 6) + 3 = 4 := rfl
  have e5 : (2 : ZMod 6) + 3 = 5 := rfl
  rw [e1, e2] at h0
  rw [e3] at h3
  rw [e4] at h4
  rw [e5] at h5
  have h1 : s 1 = s 0 + s 2 := by
    rw [h4] at h0
    rw [← sub_eq_zero, ← neg_eq_zero, ← h0]; abel
  exact ⟨h1, h3, by rw [h4, h1], h5⟩

private lemma sd_det2_zero_two {s : ZMod 6 → Fin 2 → ℝ} (hs : IsMultiPoint s) :
    det2 (s 0) (s 2) = √3 / 2 := by
  have h := (hs 0).2.2
  have e : (0 : ZMod 6) + 1 = 1 := rfl
  rw [e, (sd_multiPoint_rel hs).1] at h
  rw [← h]
  simp [det2]
  ring

/-- A matrix sending `s₀, s₂` to `σ₀, σ₂` sends every `s_j` to `σ_j`. -/
private lemma sd_mulVec_all {s σ : ZMod 6 → Fin 2 → ℝ} (hs : IsMultiPoint s)
    (hσ : IsMultiPoint σ) {A : Mat2} (h0 : A *ᵥ s 0 = σ 0) (h2 : A *ᵥ s 2 = σ 2) (j : ZMod 6) :
    σ j = A *ᵥ s j := by
  obtain ⟨s1, s3, s4, s5⟩ := sd_multiPoint_rel hs
  obtain ⟨σ1, σ3, σ4, σ5⟩ := sd_multiPoint_rel hσ
  fin_cases j
  · exact h0.symm
  · change σ 1 = A *ᵥ s 1
    rw [s1, σ1, Matrix.mulVec_add, h0, h2]
  · exact h2.symm
  · change σ 3 = A *ᵥ s 3
    rw [s3, σ3, Matrix.mulVec_neg, h0]
  · change σ 4 = A *ᵥ s 4
    rw [s4, σ4, Matrix.mulVec_neg, Matrix.mulVec_add, h0, h2]
  · change σ 5 = A *ᵥ s 5
    rw [s5, σ5, Matrix.mulVec_neg, h2]

/-- **Theorem 3.1.1** (`thm:defn-g`, Mahler, Hales). A `C^k` multi-curve `σ` on `[0, t_f]` and a
multi-point `s` determine a `C^k` curve `g : [0, t_f] → SL₂(ℝ)` by the conditions
`σ_j(t) = g(t) s_j` for all `j` and `t`; the curve is unique on `[0, t_f]`.
(`C^k` for a matrix-valued curve means that every entry is `C^k`.) -/
theorem theorem3_1_1 (k : ℕ) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ) (hσ : IsMultiCurve k σ tf)
    (s : ZMod 6 → Fin 2 → ℝ) (hs : IsMultiPoint s) :
    ∃ g : ℝ → Mat2, (∀ i j, ContDiffOn ℝ k (fun t ↦ g t i j) (Set.Icc 0 tf)) ∧
      (∀ t ∈ Set.Icc 0 tf, (g t).det = 1 ∧ ∀ j, σ j t = g t *ᵥ s j) ∧
      ∀ g' : ℝ → Mat2, (∀ t ∈ Set.Icc 0 tf, ∀ j, σ j t = g' t *ᵥ s j) →
        Set.EqOn g' g (Set.Icc 0 tf) := by
  have hd : det2 (s 0) (s 2) ≠ 0 := by rw [sd_det2_zero_two hs]; positivity
  refine ⟨fun t ↦ sd_mat (σ 0 t) (σ 2 t) (s 0) (s 2), fun i j ↦ ?_, fun t ht ↦ ⟨?_, ?_⟩,
    fun g' hg' t ht ↦ ?_⟩
  · have h0 : ContDiffOn ℝ k (fun t ↦ σ 0 t i) (Set.Icc 0 tf) := contDiffOn_pi.1 (hσ.1 0) i
    have h2 : ContDiffOn ℝ k (fun t ↦ σ 2 t i) (Set.Icc 0 tf) := contDiffOn_pi.1 (hσ.1 2) i
    exact ((h0.mul contDiffOn_const).sub (h2.mul contDiffOn_const)).div_const _
  · rw [sd_det_mat hd, sd_det2_zero_two hs, sd_det2_zero_two (hσ.2 t ht)]
    exact div_self (by positivity)
  · exact sd_mulVec_all hs (hσ.2 t ht) (sd_mat_mulVec_left hd) (sd_mat_mulVec_right hd)
  · exact sd_eq_mat hd (hg' t ht 0).symm (hg' t ht 2).symm

/-- The derivative `g'` of a matrix-valued curve on `[0, t_f]`, entry by entry, within the
interval. -/
noncomputable def curveDeriv (g : ℝ → Mat2) (tf t : ℝ) : Mat2 :=
  Matrix.of fun i j ↦ derivWithin (fun s ↦ g s i j) (Set.Icc 0 tf) t

/-- **Definition 3.1.3** (`def:X-defn`). For a `C¹` curve `g : [0, t_f] → SL₂(ℝ)`, the curve
`X = g⁻¹ g'` (defined by `g' = gX`). -/
noncomputable def curveX (g : ℝ → Mat2) (tf t : ℝ) : Mat2 := (g t)⁻¹ * curveDeriv g tf t

/-- The curve `g` with `σ_j = g s_j` on `[0, t_f]` is `C¹` there (Theorem 3.1.1). -/
private lemma sd_g_hasDerivWithin {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hσ : IsMultiCurve 1 σ tf) {s : ZMod 6 → Fin 2 → ℝ} (hs : IsMultiPoint s) {g : ℝ → Mat2}
    (hg : ∀ t ∈ Set.Icc 0 tf, ∀ j, σ j t = g t *ᵥ s j) :
    (∀ i j, ContDiffOn ℝ 1 (fun t ↦ g t i j) (Set.Icc 0 tf)) ∧
      ∀ t ∈ Set.Icc 0 tf, HasDerivWithinAtEntrywise g (curveDeriv g tf t) (Set.Icc 0 tf) t := by
  obtain ⟨g₁, hg₁C, -, hg₁u⟩ := theorem3_1_1 1 σ tf hσ s hs
  have hgeq : Set.EqOn g g₁ (Set.Icc 0 tf) := hg₁u g hg
  have hC : ∀ i j, ContDiffOn ℝ 1 (fun t ↦ g t i j) (Set.Icc 0 tf) := fun i j ↦
    (hg₁C i j).congr fun t ht ↦ by rw [hgeq ht]
  exact ⟨hC, fun t ht i j ↦ ((hC i j).differentiableOn one_ne_zero t ht).hasDerivWithinAt⟩

/-- **Theorem 3.1.4** (`thm:defn-X`), parts (1) and (2). Let `K` be a convex disk whose boundary
is parameterized by a regular `C¹` multi-curve `σ`, let `g` be the curve induced by a multi-point
`s` (`σ_j(t) = g(t) s_j`, Theorem 3.1.1), and let `X = g⁻¹g'`. Then `X(t) ∈ 𝔰𝔩₂(ℝ)` and
`σ_j'(t) = Ad_{g(t)}(X(t)) σ_j(t)` for all `j`. Part (3) is `theorem3_1_4_lipschitz`. -/
theorem theorem3_1_4 (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ)
    (tf : ℝ) (htf : 0 < tf) (hσ : IsMultiCurve 1 σ tf)
    (s : ZMod 6 → Fin 2 → ℝ) (hs : IsMultiPoint s) (g : ℝ → Mat2)
    (hg : ∀ t ∈ Set.Icc 0 tf, (g t).det = 1 ∧ ∀ j, σ j t = g t *ᵥ s j) :
    ∀ t ∈ Set.Icc 0 tf, (curveX g tf t).trace = 0 ∧
      ∀ j, derivWithin (σ j) (Set.Icc 0 tf) t = (g t * curveX g tf t * (g t)⁻¹) *ᵥ σ j t := by
  -- the convexity, regularity and boundary hypotheses are not used in the proof
  intro t ht
  obtain ⟨-, hD⟩ := sd_g_hasDerivWithin hσ hs (fun t ht ↦ (hg t ht).2)
  have hu : UniqueDiffWithinAt ℝ (Set.Icc 0 tf) t := uniqueDiffOn_Icc htf t ht
  have hunit : IsUnit (g t).det := by rw [(hg t ht).1]; exact isUnit_one
  refine ⟨sd_trace_eq_zero_of_det hu ht (hD t ht) (fun x hx ↦ (hg x hx).1), fun j ↦ ?_⟩
  have h1 : HasDerivWithinAt (σ j) (curveDeriv g tf t *ᵥ s j) (Set.Icc 0 tf) t :=
    ((hD t ht).mulVec_const (s j)).congr (fun x hx ↦ (hg x hx).2 j) ((hg t ht).2 j)
  rw [h1.derivWithin hu, (hg t ht).2 j, Matrix.mulVec_mulVec, curveX, Matrix.mul_assoc _ (g t)⁻¹,
    Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]

/-- **Theorem 3.1.4** (`thm:defn-X`), part (3): `X` is Lipschitz.

The printed statement asks only for a convex disk with a regular `C¹` multi-curve; part (3) is
false in that generality (the unit disk with `σ_j(t) = Rot(θ(t)) s_j*`, `θ(t) = t + t^{3/2}`, gives
`X = θ' J`, which is not Lipschitz). The proof cites Lemma 2.4.3 (`lem:tangents-lipschitz`), which
gives Lipschitz tangents `σ_j'` for the minimizer `K_min` parameterized by arclength (the standing
assumption of §2.4); Chapter 2 is outside the scope of this formalization, so its conclusion is a
hypothesis here. It holds for balanced disks (Definition 2.4.7, item 2). -/
theorem theorem3_1_4_lipschitz (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ) (htf : 0 < tf)
    (hσ : IsMultiCurve 1 σ tf)
    (hLip : ∀ j, ∃ C, LipschitzOnWith C (derivWithin (σ j) (Set.Icc 0 tf)) (Set.Icc 0 tf))
    (s : ZMod 6 → Fin 2 → ℝ) (hs : IsMultiPoint s) (g : ℝ → Mat2)
    (hg : ∀ t ∈ Set.Icc 0 tf, (g t).det = 1 ∧ ∀ j, σ j t = g t *ᵥ s j) :
    LipschitzOnEntrywise (curveX g tf) (Set.Icc 0 tf) := by
  obtain ⟨hC, hD⟩ := sd_g_hasDerivWithin hσ hs (fun t ht ↦ (hg t ht).2)
  have hd : det2 (s 0) (s 2) ≠ 0 := by rw [sd_det2_zero_two hs]; positivity
  have hcpt : IsCompact (Set.Icc 0 tf) := isCompact_Icc
  -- `X s_j = g⁻¹ σ_j'` on `[0, t_f]`
  have hXs : ∀ t ∈ Set.Icc 0 tf, ∀ j,
      curveX g tf t *ᵥ s j = (g t)⁻¹ *ᵥ derivWithin (σ j) (Set.Icc 0 tf) t := by
    intro t ht j
    have h1 : HasDerivWithinAt (σ j) (curveDeriv g tf t *ᵥ s j) (Set.Icc 0 tf) t :=
      ((hD t ht).mulVec_const (s j)).congr (fun x hx ↦ (hg x hx).2 j) ((hg t ht).2 j)
    rw [h1.derivWithin (uniqueDiffOn_Icc htf t ht), Matrix.mulVec_mulVec, curveX]
  -- `g⁻¹ = adj g` has Lipschitz entries, since `g` is `C¹` on a compact interval
  have hgL : ∀ i j, sd_LipBdd (fun t ↦ g t i j) (Set.Icc 0 tf) := fun i j ↦
    sd_LipBdd_of_compact hcpt ((hC i j).exists_lipschitzOnWith one_ne_zero (convex_Icc 0 tf) hcpt)
  have hginv : ∀ i k, sd_LipBdd (fun t ↦ (g t)⁻¹ i k) (Set.Icc 0 tf) := by
    intro i k
    refine sd_LipBdd_congr (f := fun t ↦ (g t).adjugate i k) ?_ fun t ht ↦ ?_
    · fin_cases i <;> fin_cases k <;>
        simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, adjugate_fin_two, of_apply, cons_val',
          cons_val_zero, cons_val_one, cons_val_fin_one]
      · exact hgL 1 1
      · exact sd_LipBdd_neg (hgL 0 1)
      · exact sd_LipBdd_neg (hgL 1 0)
      · exact hgL 0 0
    · simp [Matrix.inv_def, (hg t ht).1]
  -- `σ_j'` is Lipschitz (hypothesis: Lemma 2.4.3)
  have hσ' : ∀ j k, sd_LipBdd (fun t ↦ derivWithin (σ j) (Set.Icc 0 tf) t k) (Set.Icc 0 tf) :=
    fun j k ↦ by
      obtain ⟨C, hC⟩ := hLip j
      exact sd_LipBdd_of_compact hcpt ⟨_, (LipschitzWith.eval k).comp_lipschitzOnWith hC⟩
  -- hence `X s_j = g⁻¹ σ_j'` is Lipschitz
  have hv : ∀ j i, sd_LipBdd
      (fun t ↦ ((g t)⁻¹ *ᵥ derivWithin (σ j) (Set.Icc 0 tf) t) i) (Set.Icc 0 tf) := by
    intro j i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact sd_LipBdd_add (sd_LipBdd_mul (hginv i 0) (hσ' j 0))
      (sd_LipBdd_mul (hginv i 1) (hσ' j 1))
  -- and `X` is determined by `X s₀` and `X s₂`
  intro i j
  refine (sd_LipBdd_congr (f := fun t ↦ sd_mat ((g t)⁻¹ *ᵥ derivWithin (σ 0) (Set.Icc 0 tf) t)
    ((g t)⁻¹ *ᵥ derivWithin (σ 2) (Set.Icc 0 tf) t) (s 0) (s 2) i j) ?_
    fun t ht ↦ by dsimp only; rw [← sd_eq_mat hd (hXs t ht 0) (hXs t ht 2)]).1
  simp only [sd_mat, Matrix.of_apply]
  exact sd_LipBdd_div_const (sd_LipBdd_sub (sd_LipBdd_mul (hv 0 i) (sd_LipBdd_const _ _))
    (sd_LipBdd_mul (hv 2 i) (sd_LipBdd_const _ _))) _

/-- **Definition 3.1.5** (`eqn:R`). `R = exp(Jπ/3)` is the counterclockwise rotation by `π/3`;
the shared definitions write `R` out, and this is the bridge to the definition by the matrix
exponential. -/
theorem definition3_1_5 : R = NormedSpace.exp ((Real.pi / 3) • J) := by
  have hJ : J.trace = 0 := by simp [J, Matrix.trace_fin_two]
  have hdet : J.det = 1 := by simp [J, Matrix.det_fin_two]
  rw [((lemmaA_6_4 J hJ).2 (Real.pi / 3)).2.1 (by rw [hdet]; norm_num), hdet]
  simp only [Real.sqrt_one, mul_one, div_one, Real.cos_pi_div_three, Real.sin_pi_div_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R, J]

/-- `t ↦ (√(d t))⁻¹` is Lipschitz where `d ≥ δ > 0`: the estimate. -/
private lemma sd_abs_inv_sqrt_sub_le {a b δ : ℝ} (hδ : 0 < δ) (ha : δ ≤ a) (hb : δ ≤ b) :
    |(√a)⁻¹ - (√b)⁻¹| ≤ |a - b| / (2 * √δ ^ 3) := by
  have key : ∀ p q r : ℝ, 0 < r → r ≤ p → r ≤ q →
      |p⁻¹ - q⁻¹| ≤ |p ^ 2 - q ^ 2| / (2 * r ^ 3) := by
    intro p q r hr hp hq
    have hp0 : 0 < p := by linarith
    have hq0 : 0 < q := by linarith
    have e : p⁻¹ - q⁻¹ = (p ^ 2 - q ^ 2) * (-1) / (p * q * (p + q)) := by field_simp; ring
    rw [e, abs_div, abs_mul, abs_neg, abs_one, mul_one,
      abs_of_pos (by positivity : 0 < p * q * (p + q))]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    have h1 : r * r ≤ p * q := mul_le_mul hp hq hr.le hp0.le
    nlinarith
  have h := key (√a) (√b) (√δ) (Real.sqrt_pos.2 hδ) (Real.sqrt_le_sqrt ha) (Real.sqrt_le_sqrt hb)
  rwa [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)] at h

private lemma sd_LipBdd_inv_sqrt {d : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hd : sd_LipBdd d Set.univ)
    (hdδ : ∀ x, δ ≤ d x) : sd_LipBdd (fun x ↦ (√(d x))⁻¹) Set.univ := by
  obtain ⟨⟨K, hK⟩, -⟩ := hd
  refine ⟨⟨_, LipschitzOnWith.of_dist_le' (K := K / (2 * √δ ^ 3)) fun x _ y _ ↦ ?_⟩,
    (√δ)⁻¹, fun x _ ↦ ?_⟩
  · have h1 := hK.dist_le_mul x trivial y trivial
    simp only [Real.dist_eq] at h1 ⊢
    have hr : 0 < √δ := Real.sqrt_pos.2 hδ
    calc _ ≤ |d x - d y| / (2 * √δ ^ 3) := sd_abs_inv_sqrt_sub_le hδ (hdδ x) (hdδ y)
      _ ≤ K * |x - y| / (2 * √δ ^ 3) := by gcongr
      _ = _ := by ring
  · rw [abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 (hδ.trans_le (hdδ x))))]
    exact inv_anti₀ (Real.sqrt_pos.2 hδ) (Real.sqrt_le_sqrt (hdδ x))

private lemma sd_LipBdd_comp {f s : ℝ → ℝ} {K : NNReal} (hf : sd_LipBdd f Set.univ)
    (hs : LipschitzWith K s) : sd_LipBdd (fun x ↦ f (s x)) Set.univ := by
  obtain ⟨⟨Kf, hKf⟩, M, hM⟩ := hf
  exact ⟨⟨Kf * K, ((lipschitzOnWith_univ.1 hKf).comp hs).lipschitzOnWith⟩, M,
    fun x _ ↦ hM (s x) trivial⟩

/-- A `P`-periodic function that is Lipschitz on `[0, 2P]` is Lipschitz and bounded on `ℝ`. -/
private lemma sd_LipBdd_of_periodic {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P)
    (hper : Function.Periodic f P) (hf : ∃ K, LipschitzOnWith K f (Set.Icc 0 (2 * P))) :
    sd_LipBdd f Set.univ := by
  obtain ⟨⟨K, hK⟩, M, hM⟩ := sd_LipBdd_of_compact isCompact_Icc hf
  have hM' : ∀ x, |f x| ≤ M := by
    intro x
    obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ hP x
    rw [hxy]
    exact hM y ⟨hy.1, by linarith [hy.2]⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0)
  -- two points closer than a period: translate both into `[0, 2P]`
  have hclose : ∀ x y, x ≤ y → y - x < P → |f x - f y| ≤ K * |x - y| := by
    intro x y hle hxy
    obtain ⟨n, ⟨hn1, hn2⟩, -⟩ := existsUnique_zsmul_near_of_pos' hP x
    have hx' : x - n • P ∈ Set.Icc 0 (2 * P) := ⟨hn1, by linarith⟩
    have hy' : y - n • P ∈ Set.Icc 0 (2 * P) := ⟨by linarith, by linarith⟩
    have h := hK.dist_le_mul _ hx' _ hy'
    rwa [Real.dist_eq, Real.dist_eq, hper.sub_zsmul_eq, hper.sub_zsmul_eq,
      show x - n • P - (y - n • P) = x - y by ring] at h
  refine ⟨⟨_, LipschitzOnWith.of_dist_le' (K := max (K : ℝ) (2 * M / P)) fun x _ y _ ↦ ?_⟩, M,
    fun x _ ↦ hM' x⟩
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_or_gt P |x - y| with hxy | hxy
  · -- two points at least a period apart: use the bound
    calc |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hM' x, hM' y]
      _ = 2 * M / P * P := by field_simp
      _ ≤ 2 * M / P * |x - y| := by gcongr
      _ ≤ max (K : ℝ) (2 * M / P) * |x - y| := by gcongr; exact le_max_right _ _
  · have h : |f x - f y| ≤ K * |x - y| := by
      rcases le_total x y with hle | hle
      · exact hclose x y hle (by rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hxy; exact hxy)
      · rw [abs_sub_comm (f x), abs_sub_comm x]
        exact hclose y x hle (by rw [abs_of_nonneg (by linarith)] at hxy; exact hxy)
    exact h.trans (by gcongr; exact le_max_left _ _)

/-- An `SL₂(ℝ)` matrix maps multi-points to multi-points. -/
private lemma sd_isMultiPoint_mulVec {s : ZMod 6 → Fin 2 → ℝ} (hs : IsMultiPoint s) {A : Mat2}
    (hA : A.det = 1) : IsMultiPoint fun j ↦ A *ᵥ s j := by
  intro j
  obtain ⟨h1, h2, h3⟩ := hs j
  refine ⟨?_, ?_, ?_⟩
  · simp only [← Matrix.mulVec_add, h1, Matrix.mulVec_zero]
  · simp only [h2, Matrix.mulVec_neg]
  · rw [← h3]
    rw [Matrix.det_fin_two] at hA
    simp only [det2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (s j 0 * s (j + 1) 1 - s j 1 * s (j + 1) 0) * hA

private lemma sd_sixthRoot_zero : sixthRoot 0 = ![1, 0] := by
  simp [sixthRoot]

private lemma sd_sixthRoot_one : sixthRoot 1 = ![1 / 2, √3 / 2] := by
  have : (1 : ZMod 6).val = 1 := rfl
  simp only [sixthRoot, this, Nat.cast_one, mul_one, Real.cos_pi_div_three,
    Real.sin_pi_div_three]

private lemma sd_sixthRoot_two : sixthRoot 2 = ![-(1 / 2), √3 / 2] := by
  have : (2 : ZMod 6).val = 2 := rfl
  have e : Real.pi * ((2 : ℕ) : ℝ) / 3 = Real.pi - Real.pi / 3 := by push_cast; ring
  simp only [sixthRoot, this, e, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three,
    Real.sin_pi_div_three]

private lemma sd_det2_sixthRoot : det2 (sixthRoot 0) (sixthRoot 2) = √3 / 2 := by
  rw [sd_sixthRoot_zero, sd_sixthRoot_two]
  simp [det2]

/-- For a balanced pair with `σ_j = g s_j*`: `g = [σ₀ σ₂][s₀* s₂*]⁻¹` is differentiable,
`det g = 1`, and `X s_j* = g⁻¹ σ_j'` for `X = g⁻¹ g'` (as in Theorem 3.1.4). -/
private lemma sd_balanced {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hKσ : IsBalancedPair K σ tf) {g : ℝ → Mat2} (hg : ∀ t j, σ j t = g t *ᵥ sixthRoot j)
    (t : ℝ) :
    (g t).det = 1 ∧ HasDerivAtEntrywise g (derivEntrywise g t) t ∧
      ∀ j, ((g t)⁻¹ * derivEntrywise g t) *ᵥ sixthRoot j = (g t)⁻¹ *ᵥ deriv (σ j) t := by
  obtain ⟨-, hC, -, hmp, -⟩ := hKσ
  have hd : det2 (sixthRoot 0) (sixthRoot 2) ≠ 0 := by rw [sd_det2_sixthRoot]; positivity
  have hgeq : ∀ u, g u = sd_mat (σ 0 u) (σ 2 u) (sixthRoot 0) (sixthRoot 2) := fun u ↦
    sd_eq_mat hd (hg u 0).symm (hg u 2).symm
  have hdet : (g t).det = 1 := by
    rw [hgeq, sd_det_mat hd, sd_det2_zero_two (hmp t), sd_det2_sixthRoot]
    exact div_self (by positivity)
  have hσd : ∀ j, HasDerivAt (σ j) (deriv (σ j) t) t := fun j ↦
    ((hC j).1.differentiable one_ne_zero t).hasDerivAt
  have hD : HasDerivAtEntrywise g
      (sd_mat (deriv (σ 0) t) (deriv (σ 2) t) (sixthRoot 0) (sixthRoot 2)) t := by
    intro i j
    have h0 := hasDerivAt_pi.1 (hσd 0) i
    have h2 := hasDerivAt_pi.1 (hσd 2) i
    simp only [hgeq, sd_mat, Matrix.of_apply]
    exact ((h0.mul_const _).sub (h2.mul_const _)).div_const _
  rw [← hD.derivEntrywise] at hD
  refine ⟨hdet, hD, fun j ↦ ?_⟩
  have h1 : HasDerivAt (σ j) (derivEntrywise g t *ᵥ sixthRoot j) t := by
    have := hD.mulVec_const (sixthRoot j)
    rwa [show (fun s ↦ g s *ᵥ sixthRoot j) = σ j from funext fun s ↦ (hg s j).symm] at this
  rw [h1.deriv, Matrix.mulVec_mulVec]

/-- **Corollary 3.1.6** (`cor:X-props`). For a balanced disk `K` with boundary parameterization
`σ_j(t) = g(t) s_j*`, the curve `X = g⁻¹g'` satisfies the star inequalities `ρᵢ(X) > 0`; in
particular `√3 |a| < c`, `3b + c < 0`, `0 < c`, `tr(JX) = b - c < 0` for `X = [[a, b], [c, -a]]`,
and `det X > 0`. -/
theorem corollary3_1_6 (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ)
    (hKσ : IsBalancedPair K σ tf) (g : ℝ → Mat2) (hg : ∀ t j, σ j t = g t *ᵥ sixthRoot j) (t : ℝ) :
    0 < ρ₀ ((g t)⁻¹ * derivEntrywise g t) ∧ 0 < ρ₁ ((g t)⁻¹ * derivEntrywise g t) ∧
      0 < ρ₂ ((g t)⁻¹ * derivEntrywise g t) ∧
      √3 * |((g t)⁻¹ * derivEntrywise g t) 0 0| < ((g t)⁻¹ * derivEntrywise g t) 1 0 ∧
      3 * ((g t)⁻¹ * derivEntrywise g t) 0 1 + ((g t)⁻¹ * derivEntrywise g t) 1 0 < 0 ∧
      0 < ((g t)⁻¹ * derivEntrywise g t) 1 0 ∧
      (J * ((g t)⁻¹ * derivEntrywise g t)).trace < 0 ∧
      0 < ((g t)⁻¹ * derivEntrywise g t).det := by
  obtain ⟨hdet, hD, hXs⟩ := sd_balanced hKσ hg t
  have hstar := hKσ.2.2.2.2.2.1
  have hunit : IsUnit (g t).det := by rw [hdet]; exact isUnit_one
  -- `X ∈ 𝔰𝔩₂(ℝ)` since `det g ≡ 1`
  have htr : ((g t)⁻¹ * derivEntrywise g t).trace = 0 :=
    sd_trace_eq_zero_of_det (S := Set.univ) uniqueDiffWithinAt_univ (Set.mem_univ t)
      (hasDerivWithinAtEntrywise_univ.2 hD) fun x _ ↦ (sd_balanced hKσ hg x).1
  set X := (g t)⁻¹ * derivEntrywise g t with hXdef
  have hginv : ∀ j, (g t)⁻¹ *ᵥ σ j t = sixthRoot j := fun j ↦ by
    rw [hg t j, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  -- the star conditions, after cancelling `g(t)`: `X s_j* = α (s_{j+1}* - s_j*) + β s_{j+1}*`
  obtain ⟨α₀, β₀, hα₀, hβ₀, h₀⟩ := hstar 0 t
  obtain ⟨α₁, β₁, hα₁, hβ₁, h₁⟩ := hstar 1 t
  have e01 : (0 : ZMod 6) + 1 = 1 := rfl
  have e12 : (1 : ZMod 6) + 1 = 2 := rfl
  rw [e01] at h₀
  rw [e12] at h₁
  have e₀ : X *ᵥ sixthRoot 0 = α₀ • (sixthRoot 1 - sixthRoot 0) + β₀ • sixthRoot 1 := by
    rw [hXs 0, h₀, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_sub, hginv, hginv]
  have e₁ : X *ᵥ sixthRoot 1 = α₁ • (sixthRoot 2 - sixthRoot 1) + β₁ • sixthRoot 2 := by
    rw [hXs 1, h₁, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_sub, hginv, hginv]
  rw [sd_sixthRoot_zero, sd_sixthRoot_one] at e₀
  rw [sd_sixthRoot_one, sd_sixthRoot_two] at e₁
  have a0 := congrFun e₀ 0
  have a1 := congrFun e₀ 1
  have b0 := congrFun e₁ 0
  have b1 := congrFun e₁ 1
  simp only [mulVec, dotProduct, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd,
    Fin.sum_univ_two, cons_val_zero, mul_one, cons_val_one, cons_val_fin_one, mul_zero, add_zero,
    one_div, sub_cons, head_cons, tail_cons, sub_zero, sub_self, zero_empty, smul_cons,
    smul_eq_mul, smul_empty, Pi.add_apply, smul_zero, mul_neg, Pi.zero_apply, zero_add]
    at a0 a1 b0 b1
  have hd : X 1 1 = -X 0 0 := by rw [Matrix.trace_fin_two] at htr; linarith
  have h3 : (0 : ℝ) < √3 := by positivity
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  -- solving for the coefficients: `ρ₀ = β₀`, `ρ₁ = α₀`, `ρ₂ = α₁`
  have hρ₀ : ρ₀ X = β₀ := by
    unfold ρ₀; rw [div_eq_iff h3.ne']; linear_combination a1 + √3 * a0
  have hρ₁ : ρ₁ X = α₀ := by
    unfold ρ₁; rw [div_eq_iff h3.ne']; linear_combination a1 - √3 * a0
  have hρ₂ : ρ₂ X = α₁ := by
    unfold ρ₂; rw [div_eq_iff (by positivity)]
    linear_combination -2 * √3 * b0 - 2 * b1 + √3 * hd + X 0 1 * hs3
  have h0 : 0 < ρ₀ X := hρ₀ ▸ hβ₀
  have h1 : 0 < ρ₁ X := hρ₁ ▸ hα₀
  have h2 : 0 < ρ₂ X := hρ₂ ▸ hα₁
  have k0 : 0 < X 1 0 + √3 * X 0 0 := by unfold ρ₀ at h0; exact (div_pos_iff_of_pos_right h3).1 h0
  have k1 : 0 < X 1 0 - √3 * X 0 0 := by unfold ρ₁ at h1; exact (div_pos_iff_of_pos_right h3).1 h1
  have k2 : 3 * X 0 1 + X 1 0 < 0 := by
    unfold ρ₂ at h2
    have := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * √3)).1 h2
    linarith
  have k3 : √3 * |X 0 0| < X 1 0 := by
    rcases abs_cases (X 0 0) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
  have k4 : 0 < X 1 0 := lt_of_le_of_lt (by positivity) k3
  refine ⟨h0, h1, h2, k3, k2, k4, ?_, ?_⟩
  · simp [J, Matrix.trace_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    linarith
  · -- `det X = ρ₀ρ₁ + ρ₁ρ₂ + ρ₂ρ₀`
    have : X.det = ρ₀ X * ρ₁ X + ρ₁ X * ρ₂ X + ρ₂ X * ρ₀ X := by
      rw [Matrix.det_fin_two, hd]
      unfold ρ₀ ρ₁ ρ₂
      field_simp
      linear_combination -2 * X 0 1 * X 1 0 * hs3
    rw [this]
    positivity

/-- **Proposition 3.1.9** (`prop:reparam-lipschitz`). Let `(K, σ)` be a balanced pair with
`σ_0` parameterized by arclength, `σ_j = g s_j*`, `X = g⁻¹g'`, and let `t ↦ s(t)` be a
reparameterization (`s' > 0`) such that `X̃(t) = X(s(t)) s'(t)` has `det X̃ = 1`. Then `X̃` is
Lipschitz.

The book defines `X̃` by `g̃' = g̃ X̃` with `g̃ = g ∘ s` and derives `X̃ = X(s) s'` by the chain
rule; the statement takes `X̃` in that derived form. -/
theorem proposition3_1_9 (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ)
    (hKσ : IsBalancedPair K σ tf)
    (g : ℝ → Mat2) (hg : ∀ t j, σ j t = g t *ᵥ sixthRoot j)
    (s s' : ℝ → ℝ) (hs : ∀ t, HasDerivAt s (s' t) t) (hs' : ∀ t, 0 < s' t)
    (hdet : ∀ t, (s' t • ((g (s t))⁻¹ * derivEntrywise g (s t))).det = 1) :
    LipschitzOnEntrywise (fun t ↦ s' t • ((g (s t))⁻¹ * derivEntrywise g (s t))) Set.univ := by
  have hKσ' := hKσ
  obtain ⟨-, hC, hL, hmp, -, -, htf, hper, -, -⟩ := hKσ'
  set P := 6 * tf with hPdef
  have hP : 0 < P := by positivity
  have hT : 0 < 2 * P := by positivity
  have hgdet : ∀ u, (g u).det = 1 := fun u ↦ (sd_balanced hKσ hg u).1
  have hgD : ∀ u, HasDerivAtEntrywise g (derivEntrywise g u) u := fun u ↦
    (sd_balanced hKσ hg u).2.1
  have hdpos : ∀ u, 0 < ((g u)⁻¹ * derivEntrywise g u).det := fun u ↦
    (corollary3_1_6 K σ tf hKσ g hg u).2.2.2.2.2.2.2
  set X : ℝ → Mat2 := fun u ↦ (g u)⁻¹ * derivEntrywise g u with hXdef
  -- `X` is Lipschitz on `[0, 2P]` (Theorem 3.1.4 (3), applied on two periods)
  have hsmp : IsMultiPoint sixthRoot := by
    have hunit : IsUnit (g 0).det := by rw [hgdet 0]; exact isUnit_one
    have h := sd_isMultiPoint_mulVec (hmp 0) (A := (g 0)⁻¹)
      (by rw [Matrix.det_nonsing_inv, hgdet 0]; simp)
    convert h using 1
    funext j
    rw [hg 0 j, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  have hLipT := theorem3_1_4_lipschitz σ (2 * P) hT
    ⟨fun j ↦ (hC j).1.contDiffOn, fun t _ ↦ hmp t⟩
    (fun j ↦ by
      obtain ⟨C, hC'⟩ := hL j
      refine ⟨C, fun x hx y hy ↦ ?_⟩
      rw [((hC j).1.differentiable one_ne_zero x).derivWithin (uniqueDiffOn_Icc hT x hx),
        ((hC j).1.differentiable one_ne_zero y).derivWithin (uniqueDiffOn_Icc hT y hy)]
      exact hC' x y)
    sixthRoot hsmp g (fun t _ ↦ ⟨hgdet t, fun j ↦ hg t j⟩)
  have hcX : ∀ u ∈ Set.Icc 0 (2 * P), curveX g (2 * P) u = X u := by
    intro u hu
    simp only [curveX, hXdef]
    congr 1
    ext i j
    simp only [curveDeriv, derivEntrywise, Matrix.of_apply]
    exact (hgD u i j).differentiableAt.derivWithin (uniqueDiffOn_Icc hT u hu)
  -- `g` and `X` are `P`-periodic (item 6 of the balanced pair)
  have hd : det2 (sixthRoot 0) (sixthRoot 2) ≠ 0 := by rw [sd_det2_sixthRoot]; positivity
  have hgper : ∀ u, g (u + P) = g u := fun u ↦ by
    rw [sd_eq_mat hd (hg (u + P) 0).symm (hg (u + P) 2).symm,
      sd_eq_mat hd (hg u 0).symm (hg u 2).symm, hper 0, hper 2]
  have hXper : ∀ u, X (u + P) = X u := by
    intro u
    simp only [hXdef, hgper]
    congr 1
    ext i j
    simp only [derivEntrywise, Matrix.of_apply]
    rw [← deriv_comp_add_const]
    simp only [hgper]
  -- hence `X` is Lipschitz and bounded on `ℝ`
  have hXL : ∀ i j, sd_LipBdd (fun u ↦ X u i j) Set.univ := by
    intro i j
    refine sd_LipBdd_of_periodic hP (fun u ↦ by simp only [hXper]) ?_
    obtain ⟨C, hC'⟩ := hLipT i j
    exact ⟨C, fun x hx y hy ↦ by simp only [← hcX x hx, ← hcX y hy]; exact hC' hx hy⟩
  -- `det X` is bounded below by a positive constant (continuous, positive, periodic)
  have hdetcont : Continuous fun u ↦ (X u).det := by
    have hc : ∀ i j, Continuous fun u ↦ X u i j := fun i j ↦
      continuousOn_univ.1 (hXL i j).1.choose_spec.continuousOn
    simp only [Matrix.det_fin_two]
    exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
  obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hP.le)
    hdetcont.continuousOn
  set δ := (X u₀).det with hδdef
  have hδ : 0 < δ := hdpos u₀
  have hδle : ∀ u, δ ≤ (X u).det := by
    intro u
    obtain ⟨y, hy, hyu⟩ := Function.Periodic.exists_mem_Ico₀
      (f := fun u ↦ (X u).det) (fun u ↦ by simp only [hXper]) hP u
    rw [hyu]
    exact hmin (Set.Ico_subset_Icc_self hy)
  -- `s' = det(X(s))^{-1/2}`
  have hs'eq : ∀ t, s' t = (√((X (s t)).det))⁻¹ := by
    intro t
    have h := hdet t
    rw [Matrix.det_smul, Fintype.card_fin] at h
    have hpos := hs' t
    have e : (X (s t)).det = ((s' t)⁻¹) ^ 2 := by
      field_simp
      linarith
    rw [e, Real.sqrt_sq (by positivity), inv_inv]
  -- `s` is Lipschitz since `s' ≤ δ^{-1/2}`
  have hsL : LipschitzWith (Real.toNNReal (√δ)⁻¹) s := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun t ↦ (hs t).differentiableAt)
    intro t
    rw [(hs t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos (hs' t), hs'eq t, Real.coe_toNNReal _ (by positivity)]
    exact inv_anti₀ (Real.sqrt_pos.2 hδ) (Real.sqrt_le_sqrt (hδle _))
  -- so `X ∘ s`, `det X(s)` and `s' = det X(s)^{-1/2}` are Lipschitz and bounded
  have hXs : ∀ i j, sd_LipBdd (fun t ↦ X (s t) i j) Set.univ := fun i j ↦
    sd_LipBdd_comp (hXL i j) hsL
  have hdet' : sd_LipBdd (fun t ↦ (X (s t)).det) Set.univ := by
    simp only [Matrix.det_fin_two]
    exact sd_LipBdd_sub (sd_LipBdd_mul (hXs 0 0) (hXs 1 1)) (sd_LipBdd_mul (hXs 0 1) (hXs 1 0))
  have hs'L : sd_LipBdd s' Set.univ :=
    sd_LipBdd_congr (sd_LipBdd_inv_sqrt hδ hdet' fun t ↦ hδle (s t)) fun t _ ↦ (hs'eq t).symm
  -- and `X̃ = s' X(s)` is Lipschitz
  intro i j
  exact (sd_LipBdd_congr (sd_LipBdd_mul hs'L (hXs i j)) fun t _ ↦ by
    simp only [Matrix.smul_apply, smul_eq_mul, hXdef]).1

/-- **Corollary 3.1.10** (`cor:X-diff-ae`). In the parameterization of Proposition 3.1.9 with
`det X̃ = 1`, the curve `X̃` is differentiable almost everywhere (Rademacher's theorem). -/
theorem corollary3_1_10 (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ)
    (hKσ : IsBalancedPair K σ tf)
    (harc : ∀ t, deriv (σ 0) t 0 ^ 2 + deriv (σ 0) t 1 ^ 2 = 1)
    (g : ℝ → Mat2) (hg : ∀ t j, σ j t = g t *ᵥ sixthRoot j)
    (s s' : ℝ → ℝ) (hs : ∀ t, HasDerivAt s (s' t) t) (hs' : ∀ t, 0 < s' t)
    (hdet : ∀ t, (s' t • ((g (s t))⁻¹ * derivEntrywise g (s t))).det = 1) :
    ∀ᵐ t, ∀ i j, DifferentiableAt ℝ
      (fun t ↦ (s' t • ((g (s t))⁻¹ * derivEntrywise g (s t))) i j) t := by
  have hL := proposition3_1_9 K σ tf hKσ g hg s s' hs hs' hdet
  have h : ∀ i j, ∀ᵐ t, DifferentiableAt ℝ
      (fun t ↦ (s' t • ((g (s t))⁻¹ * derivEntrywise g (s t))) i j) t := fun i j ↦ by
    obtain ⟨C, hC⟩ := hL i j
    exact (lipschitzOnWith_univ.1 hC).ae_differentiableAt
  filter_upwards [ae_all_iff.2 fun i ↦ ae_all_iff.2 (h i)] with t ht using ht

/-- **Corollary 3.1.11** (`cor:param-equiv`). For a Lipschitz curve `X` in `𝔰𝔩₂(ℝ)` with
`det X ≠ 0` on `[a, b]` (the setting of Proposition 3.1.9), `det X` is constant if and only if
`X + X⁻¹X' ∈ 𝔰𝔩₂(ℝ)` almost everywhere.

Jacobi's formula (Lemma 3.1.12, `lemma3_1_12`, stated for `GL_n(ℂ)`) is applied to `X` viewed as
a complex matrix. The derivative `X'` exists almost everywhere by Rademacher's theorem, and the
converse uses that the Lipschitz function `det X` is absolutely continuous, hence constant when its
derivative vanishes almost everywhere (left implicit in the book). -/
theorem corollary3_1_11 (X : ℝ → Mat2) (a b : ℝ) (hab : a ≤ b)
    (htr : ∀ t ∈ Set.Icc a b, (X t).trace = 0) (hdet : ∀ t ∈ Set.Icc a b, (X t).det ≠ 0)
    (hLip : LipschitzOnEntrywise X (Set.Icc a b)) :
    (∃ c, ∀ t ∈ Set.Icc a b, (X t).det = c) ↔
      ∀ᵐ t, t ∈ Set.Ioo a b → (X t + (X t)⁻¹ * derivEntrywise X t).trace = 0 := by
  -- Rademacher: `X` is differentiable almost everywhere in `(a, b)`
  have hdiff : ∀ᵐ t, t ∈ Set.Ioo a b → HasDerivAtEntrywise X (derivEntrywise X t) t := by
    have h : ∀ i j, ∀ᵐ t, t ∈ Set.Ioo a b → DifferentiableAt ℝ (fun s ↦ X s i j) t := by
      intro i j
      obtain ⟨C, hC⟩ := hLip i j
      filter_upwards [hC.ae_differentiableWithinAt_of_mem] with t ht hmem
      exact (ht (Set.Ioo_subset_Icc_self hmem)).differentiableAt (Icc_mem_nhds hmem.1 hmem.2)
    filter_upwards [ae_all_iff.2 fun i ↦ ae_all_iff.2 (h i)] with t ht hmem i j
    exact (ht i j hmem).hasDerivAt
  -- Jacobi's formula (Lemma 3.1.12) `det(X)' = det(X) tr(X⁻¹X')`, applied to `X` viewed as a
  -- complex matrix, and `tr X = 0`
  have hjac : ∀ t ∈ Set.Ioo a b, HasDerivAtEntrywise X (derivEntrywise X t) t →
      HasDerivAt (fun s ↦ (X s).det)
        ((X t).det * (X t + (X t)⁻¹ * derivEntrywise X t).trace) t := by
    intro t ht h
    have hdt := hdet t (Set.Ioo_subset_Icc_self ht)
    have hdetC : ∀ s, ((X s).map Complex.ofRealHom).det = ((X s).det : ℂ) := fun s ↦
      (Complex.ofRealHom.map_det (X s)).symm
    have hinvC : ((X t).map Complex.ofRealHom)⁻¹ = (X t)⁻¹.map Complex.ofRealHom := by
      apply Matrix.inv_eq_left_inv
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdt), Matrix.map_one _
        (map_zero Complex.ofRealHom) (map_one Complex.ofRealHom)]
    have hJ := lemma3_1_12 (fun s ↦ (X s).map Complex.ofRealHom)
      ((derivEntrywise X t).map Complex.ofRealHom) t
      (fun i j ↦ by simpa using (h i j).ofReal_comp)
      (by rw [hdetC]; exact (Complex.ofReal_ne_zero.2 hdt).isUnit)
    rw [hinvC, ← Matrix.map_mul, ← AddMonoidHom.map_trace Complex.ofRealHom, hdetC] at hJ
    simp only [hdetC] at hJ
    -- take real parts
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hJ
    simp only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] at hre
    rw [Matrix.trace_add, htr t (Set.Ioo_subset_Icc_self ht), zero_add]
    simpa only [Complex.ofRealHom_eq_coe, ← Complex.ofReal_mul, Complex.ofReal_re] using hre
  constructor
  · rintro ⟨c, hc⟩
    filter_upwards [hdiff] with t ht hmem
    have h0 : HasDerivAt (fun s ↦ (X s).det) 0 t := by
      apply (hasDerivAt_const t c).congr_of_eventuallyEq
      filter_upwards [Icc_mem_nhds hmem.1 hmem.2] with s hs using hc s hs
    exact (mul_eq_zero.1 ((hjac t hmem (ht hmem)).unique h0)).resolve_left
      (hdet t (Set.Ioo_subset_Icc_self hmem))
  · intro h
    have hent : ∀ i j, AbsolutelyContinuousOnInterval (fun s ↦ X s i j) a b := fun i j ↦ by
      obtain ⟨C, hC⟩ := hLip i j
      exact (hC.mono (Set.uIcc_of_le hab).subset).absolutelyContinuousOnInterval
    have hac : AbsolutelyContinuousOnInterval (fun s ↦ (X s).det) a b := by
      simp only [Matrix.det_fin_two]
      exact ((hent 0 0).fun_mul (hent 1 1)).fun_sub ((hent 0 1).fun_mul (hent 1 0))
    have hae : ∀ᵐ t, t ∈ Set.uIcc a b → HasDerivAt (fun s ↦ (X s).det) 0 t := by
      filter_upwards [hdiff, h, (Set.countable_singleton a).ae_notMem volume,
        (Set.countable_singleton b).ae_notMem volume] with t ht1 ht2 hta htb hmem
      rw [Set.uIcc_of_le hab] at hmem
      have hmem' : t ∈ Set.Ioo a b :=
        ⟨lt_of_le_of_ne hmem.1 (Ne.symm hta), lt_of_le_of_ne hmem.2 htb⟩
      simpa [ht2 hmem'] using hjac t hmem' (ht1 hmem')
    obtain ⟨C, hC⟩ := hac.const_of_ae_hasDerivAt_zero hae
    exact ⟨C, fun t ht ↦ hC t (by rwa [Set.uIcc_of_le hab])⟩

end SmoothedPolygons
