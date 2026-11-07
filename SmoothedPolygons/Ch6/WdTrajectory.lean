module

public import SmoothedPolygons.Ch6.WdBoundaryParam
public import SmoothedPolygons.Ch3.LieAlgebraDynamics
public import SmoothedPolygons.Ch3.AreaFormula
public import SmoothedPolygons.Ch3.ControlProblem
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Step B1, part 2: the boundary trajectory of a worst disk

From a balanced pair `(K, σ)` in circle representation (`wd_exists_balancedPair`) to an admissible
trajectory of Problem 3.6.2, along Chapter 3:

* `wd_exists_normalize`: the linear normalization to circle representation (§2.2, §2.4: a
  critical hexagon is mapped to the one with edge midpoints `s_j*`);
* `wd_exists_balancedPair_det_one`: the reparameterization with `det X = 1` (§3.1,
  Proposition 3.1.9:
  `t ↦ s(t)` with `s' = det(X(s))^{-1/2}`, the inverse of `τ(s) = ∫₀ˢ √(det X)`); the result is
  again a balanced pair (Lemmas 2.4.5, 2.4.6 apply to every regular boundary multi-curve, and the
  derivatives stay Lipschitz by Proposition 3.1.9);
* `wd_shift`: in this parameterization, `σ_j(t + t_f) = σ_{j+1}(t)` (§3.5, the derivation of the
  boundary conditions, "the curves `σ_j` close up seamlessly"). The book takes this for granted.
  Proof: the multi-point through a boundary point of a worst disk is unique (Lemma 2.2.7,
  `bdy_eq_hexMidpoint`), so `σ_{j+1}(t) = σ_j(h(t))` for a reparameterization `h` (`h` is `C¹` by
  the inverse function theorem applied to the polar angles); differentiating
  `g(h(t)) = g(t) R` gives `h'(t)² det X(h(t)) = det X(t)`, so `h' = 1`; and `h(0) = t_f` by
  counting the turning of the polar angle (`σ_{j+3} = -σ_j`);
* `wd_isReinhardtAdmissible`: the trajectory `(g, X)`, `X = g⁻¹g'`, with the control of
  Definition 3.3.2 is admissible: the star inequalities (Corollary 3.1.6), `X` Lipschitz
  (Proposition 3.1.9), the dynamics `X' = [Z_u, X]/⟨Z_u, X⟩` almost everywhere (Lemma 3.3.1,
  Theorem 3.4.2) and the boundary conditions `g(0) = I`, `g(t_f) = R`, `X(t_f) = R⁻¹X(0)R` (§3.5,
  from the circle representation and the shift).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Filter Topology Real Matrix

/-! ### Helper lemmas: the curve `g` of a multi-curve -/

/-- The entries of a matrix from its values at `s₀* = (1, 0)` and `s₂* = (-1/2, √3/2)`. -/
lemma wd_entries (A : Mat2) (i : Fin 2) :
    A i 0 = (A *ᵥ sixthRoot 0) i ∧
      A i 1 = 2 / √3 * ((A *ᵥ sixthRoot 2) i + (A *ᵥ sixthRoot 0) i / 2) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [algA_sixthRoot_zero, algA_sixthRoot_two]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  refine ⟨by ring, ?_⟩
  field_simp
  ring

/-- A matrix is determined by its values at `s₀*` and `s₂*`. -/
lemma wd_eq_of_mulVec {A B : Mat2} (h0 : A *ᵥ sixthRoot 0 = B *ᵥ sixthRoot 0)
    (h2 : A *ᵥ sixthRoot 2 = B *ᵥ sixthRoot 2) : A = B := by
  ext i k
  obtain ⟨a0, a1⟩ := wd_entries A i
  obtain ⟨b0, b1⟩ := wd_entries B i
  fin_cases k
  · simp only [Fin.zero_eta, a0, b0, h0]
  · simp only [Fin.mk_one, a1, b1, h0, h2]

/-- For a balanced pair with `σ_j = g s_j*`: `det g = 1`, `g` is differentiable, and
`g' s_j* = σ_j'`. -/
lemma wd_balanced_g {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {T : ℝ} {g : ℝ → Mat2}
    (h : IsBalancedPair K σ T) (hg : ∀ j t, σ j t = g t *ᵥ sixthRoot j) (t : ℝ) :
    (g t).det = 1 ∧ HasDerivAtEntrywise g (derivEntrywise g t) t ∧
      ∀ j, derivEntrywise g t *ᵥ sixthRoot j = deriv (σ j) t := by
  obtain ⟨-, hC, -, hmp, -⟩ := h
  have hσd : ∀ j s, HasDerivAt (σ j) (deriv (σ j) s) s := fun j s ↦
    ((hC j).1.differentiable one_ne_zero s).hasDerivAt
  -- `det g = 1` from `det(σ₀, σ₁) = √3/2`
  have hdet : (g t).det = 1 := by
    have hd := ((hmp t) 0).2.2
    simp only [zero_add] at hd
    have hs := (algA_isMultiPoint_sixthRoot 0).2.2
    simp only [zero_add] at hs
    rw [hg 0 t, hg 1 t, oct_det2_mulVec, hs] at hd
    have h3 : (0 : ℝ) < √3 / 2 := by positivity
    nlinarith
  -- the entries of `g` are those of `σ₀`, `σ₂`
  have hD : HasDerivAtEntrywise g (Matrix.of fun i k ↦ ![deriv (σ 0) t i,
      2 / √3 * (deriv (σ 2) t i + deriv (σ 0) t i / 2)] k) t := by
    intro i k
    have h0 := hasDerivAt_pi.1 (hσd 0 t) i
    have h2 := hasDerivAt_pi.1 (hσd 2 t) i
    have e0 : (fun s ↦ g s i 0) = fun s ↦ σ 0 s i := funext fun s ↦ by
      rw [(wd_entries (g s) i).1, hg]
    have e1 : (fun s ↦ g s i 1) = fun s ↦ 2 / √3 * (σ 2 s i + σ 0 s i / 2) := funext fun s ↦ by
      rw [(wd_entries (g s) i).2, hg, hg]
    fin_cases k
    · simp only [Fin.zero_eta, Matrix.of_apply, Matrix.cons_val_zero]
      rw [e0]; exact h0
    · simp only [Fin.mk_one, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [e1]; exact (h2.add (h0.div_const 2)).const_mul _
  rw [← hD.derivEntrywise] at hD
  refine ⟨hdet, hD, fun j ↦ ?_⟩
  have h1 : HasDerivAt (σ j) (derivEntrywise g t *ᵥ sixthRoot j) t := by
    have := hD.mulVec_const (sixthRoot j)
    rwa [show (fun s ↦ g s *ᵥ sixthRoot j) = σ j from funext fun s ↦ (hg j s).symm] at this
  exact h1.deriv.symm

/-! ### Helper lemmas: bounded Lipschitz functions -/

/-- `f` is Lipschitz and bounded on `ℝ`. -/
def wd_LipBdd (f : ℝ → ℝ) : Prop := (∃ K, LipschitzWith K f) ∧ ∃ M, ∀ x, |f x| ≤ M

lemma wd_LipBdd_const (c : ℝ) : wd_LipBdd fun _ ↦ c :=
  ⟨⟨0, LipschitzWith.const c⟩, |c|, fun _ ↦ le_rfl⟩

lemma wd_LipBdd_add {f g : ℝ → ℝ} (hf : wd_LipBdd f) (hg : wd_LipBdd g) :
    wd_LipBdd fun x ↦ f x + g x := by
  obtain ⟨⟨Kf, hKf⟩, Mf, hMf⟩ := hf
  obtain ⟨⟨Kg, hKg⟩, Mg, hMg⟩ := hg
  exact ⟨⟨_, hKf.add hKg⟩, Mf + Mg, fun x ↦ (abs_add_le _ _).trans (add_le_add (hMf x) (hMg x))⟩

/-- The product of two bounded Lipschitz functions is Lipschitz (and bounded). -/
lemma wd_LipBdd_mul {f g : ℝ → ℝ} (hf : wd_LipBdd f) (hg : wd_LipBdd g) :
    wd_LipBdd fun x ↦ f x * g x := by
  obtain ⟨⟨Kf, hKf⟩, Mf, hMf⟩ := hf
  obtain ⟨⟨Kg, hKg⟩, Mg, hMg⟩ := hg
  have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf 0)
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  refine ⟨⟨Real.toNNReal (Mf * Kg + Mg * Kf), LipschitzWith.of_dist_le' fun x y ↦ ?_⟩,
    Mf * Mg, fun x ↦ ?_⟩
  · have h1 := hKf.dist_le_mul x y
    have h2 := hKg.dist_le_mul x y
    simp only [Real.dist_eq] at h1 h2 ⊢
    calc |f x * g x - f y * g y| = |f x * (g x - g y) + g y * (f x - f y)| := by
          congr 1; ring
      _ ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ Mf * (Kg * |x - y|) + Mg * (Kf * |x - y|) := by
          gcongr
          · exact hMf x
          · exact hMg y
      _ = (Mf * Kg + Mg * Kf) * |x - y| := by ring
  · rw [abs_mul]
    exact mul_le_mul (hMf x) (hMg x) (abs_nonneg _) hMf0

lemma wd_LipBdd_lipschitzWith {f : ℝ → ℝ} (hf : wd_LipBdd f) : ∃ K, LipschitzWith K f := hf.1

/-- A continuous periodic function is bounded. -/
lemma wd_bdd_of_periodic {f : ℝ → ℝ} (hf : Continuous f) {P : ℝ} (hP : 0 < P)
    (hper : Function.Periodic f P) : ∃ M, ∀ x, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := 0) (b := P)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨M, fun x ↦ ?_⟩
  obtain ⟨y, hy, hyx⟩ := hper.exists_mem_Ico₀ hP x
  rw [hyx]
  simpa [Real.norm_eq_abs] using hM y (Ico_subset_Icc_self hy)

/-- The composition of a bounded Lipschitz function with a Lipschitz function. -/
lemma wd_LipBdd_comp {f S : ℝ → ℝ} {K : NNReal} (hf : wd_LipBdd f) (hS : LipschitzWith K S) :
    wd_LipBdd fun t ↦ f (S t) := by
  obtain ⟨⟨Kf, hKf⟩, M, hM⟩ := hf
  exact ⟨⟨_, hKf.comp hS⟩, M, fun t ↦ hM (S t)⟩

/-- A periodic function with a continuous periodic derivative is Lipschitz and bounded. -/
lemma wd_LipBdd_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f') {P : ℝ} (hP : 0 < P) (hper : Function.Periodic f P)
    (hper' : Function.Periodic f' P) : wd_LipBdd f := by
  obtain ⟨M', hM'⟩ := wd_bdd_of_periodic hf' hP hper'
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t ↦ (hf t).continuousAt
  refine ⟨⟨Real.toNNReal M', lipschitzWith_of_nnnorm_deriv_le
    (fun t ↦ (hf t).differentiableAt) fun t ↦ ?_⟩, wd_bdd_of_periodic hfc hP hper⟩
  rw [(hf t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  exact (hM' t).trans (Real.le_coe_toNNReal M')

/-- A curve in the plane whose two coordinates are Lipschitz is Lipschitz. -/
lemma wd_lipschitzWith_pi {f : ℝ → Fin 2 → ℝ} (h : ∀ i, ∃ K, LipschitzWith K fun t ↦ f t i) :
    ∃ K, LipschitzWith K f := by
  choose K hK using h
  refine ⟨K 0 + K 1, LipschitzWith.of_dist_le_mul fun x y ↦
    (dist_pi_le_iff (by positivity)).2 fun i ↦ ?_⟩
  refine ((hK i).dist_le_mul x y).trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
  push_cast
  fin_cases i
  · simp
  · simp

/-- The curve `g` of a multi-curve: `σ_j(t) = g(t) s_j*` (Theorem 3.1.1). -/
lemma wd_exists_g {σ : ZMod 6 → ℝ → Fin 2 → ℝ} (hm : ∀ t, IsMultiPoint fun j ↦ σ j t) :
    ∃ g : ℝ → Mat2, ∀ j t, σ j t = g t *ᵥ sixthRoot j := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨fun t ↦ Matrix.of fun i k ↦ ![σ 0 t i, 2 / √3 * (σ 2 t i + σ 0 t i / 2)] k,
    fun j t ↦ ?_⟩
  set A : Mat2 := Matrix.of fun i k ↦ ![σ 0 t i, 2 / √3 * (σ 2 t i + σ 0 t i / 2)] k
  have h0 : A *ᵥ sixthRoot 0 = σ 0 t := by
    ext i
    rw [algA_sixthRoot_zero]
    simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h2 : A *ᵥ sixthRoot 2 = σ 2 t := by
    ext i
    rw [algA_sixthRoot_two]
    simp only [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have e : 2 / √3 * (√3 / 2) = (1 : ℝ) := by field_simp
    linear_combination (σ 2 t i + σ 0 t i / 2) * e
  have hrec : ∀ k, A *ᵥ sixthRoot (k + 1) = A *ᵥ sixthRoot k + A *ᵥ sixthRoot (k + 2) := fun k ↦ by
    rw [bdy_mp_succ algA_isMultiPoint_sixthRoot k, Matrix.mulVec_add]
  have h1 : A *ᵥ sixthRoot 1 = σ 1 t := by
    have := hrec 0
    rw [zero_add, zero_add] at this
    rw [this, h0, h2, ← zero_add (1 : ZMod 6), bdy_mp_succ (hm t) 0]
    rfl
  exact bdy_seq_eq (x := fun k ↦ σ k t) (y := fun k ↦ A *ᵥ sixthRoot k)
    (fun k ↦ bdy_mp_succ (hm t) k) hrec h0.symm h1.symm j

/-! ### Helper lemmas: polar angles and multi-points -/

/-- A star curve starting in the direction `θ₀` is `r(t) e(θ₀ + φ(t))`, with `φ` its continuous
angle (`PlaneCurve.sc_angle`). -/
lemma wd_polar {γ : ℝ → Fin 2 → ℝ} {P : ℝ} (hγ : PlaneCurve.IsStarCurve γ P) {θ₀ : ℝ}
    (h0 : γ 0 = rein_dir θ₀) (t : ℝ) :
    ∃ r : ℝ, 0 < r ∧ γ t = r • rein_dir (θ₀ + PlaneCurve.sc_angle γ t) := by
  have e := hγ.sc_toC_eq t
  rw [h0] at e
  refine ⟨Real.exp (PlaneCurve.sc_log γ t).re, Real.exp_pos _, ?_⟩
  apply PlaneCurve.sc_toC_injective
  have hdir : ∀ θ : ℝ, PlaneCurve.sc_toC (rein_dir θ) = Complex.exp (θ * Complex.I) := fun θ ↦ by
    rw [Complex.exp_mul_I]
    simp [PlaneCurve.sc_toC, rein_dir, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [e, PlaneCurve.sc_toC_smul, hdir, hdir, ← Complex.exp_add, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [PlaneCurve.sc_angle]

/-- The boundary point in the opposite direction: `rein_bd K (θ + π) = -rein_bd K θ`. -/
lemma wd_bd_add_pi {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (θ : ℝ) :
    rein_bd K (θ + π) = -rein_bd K θ := by
  rw [rein_bd, rein_bd, rein_dir_add_pi, gauge_neg (fun x hx ↦ hK.2.2.2 x hx), smul_neg]

/-- **The multi-point through a boundary point of a worst disk is unique** (Lemma 2.2.7,
`bdy_eq_hexMidpoint`). -/
lemma wd_multiPoint_eq {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) {s s' : ZMod 6 → Fin 2 → ℝ}
    (hs : IsMultiPoint s) (hs' : IsMultiPoint s') (hsK : ∀ j, s j ∈ frontier K)
    (hs'K : ∀ j, s' j ∈ frontier K) (h0 : s 0 = s' 0) : ∀ j, s j = s' j := by
  obtain ⟨v, hv, hvK, hv0⟩ := bdy_exists_hexagon hK (hsK 0)
  intro j
  rw [bdy_eq_hexMidpoint hK hv hvK hs hsK hv0.symm j,
    bdy_eq_hexMidpoint hK hv hvK hs' hs'K (h0.symm.trans hv0.symm) j]

/-- The shift of a multi-point is a multi-point. -/
lemma wd_isMultiPoint_shift {s : ZMod 6 → Fin 2 → ℝ} (hs : IsMultiPoint s) :
    IsMultiPoint fun j ↦ s (j + 1) := by
  intro j
  obtain ⟨h1, h2, h3⟩ := hs (j + 1)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [show j + 2 + 1 = j + 1 + 2 by ring, show j + 4 + 1 = j + 1 + 4 by ring] using h1
  · simpa only [show j + 3 + 1 = j + 1 + 3 by ring] using h2
  · exact h3

/-! ### Helper lemmas: integral curves of Lipschitz curves -/

/-- **FTC for Lipschitz curves.** A curve whose entries are Lipschitz on `[0, T]` and which has
entrywise derivative `V(t)` at almost every `t ∈ (0, T)` is an integral curve of `V`. -/
lemma wd_isIntegralCurve_of_lipschitz {X V : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (hL : LipschitzOnEntrywise X (Icc 0 T))
    (hd : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAtEntrywise X (V t) t) : IsIntegralCurve X V T := by
  intro i j
  obtain ⟨C, hC⟩ := hL i j
  have hac : ∀ t ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun s ↦ X s i j) 0 t := fun t ht ↦
    (hC.mono (by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
      ).absolutelyContinuousOnInterval
  have hae : ∀ t ∈ Icc 0 T, ∀ᵐ s, s ∈ uIoc 0 t → deriv (fun s ↦ X s i j) s = V s i j := by
    intro t ht
    filter_upwards [hd, (countable_singleton T).ae_notMem volume] with s hs hsT hst
    rw [uIoc_of_le ht.1] at hst
    exact (hs ⟨hst.1, lt_of_le_of_ne (hst.2.trans ht.2) hsT⟩ i j).deriv
  have hint : ∀ t ∈ Icc 0 T, IntervalIntegrable (fun s ↦ V s i j) volume 0 t := fun t ht ↦
    (hac t ht).intervalIntegrable_deriv.congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).2 (hae t ht))
  refine ⟨hint T ⟨hT, le_rfl⟩, fun t ht ↦ ?_⟩
  rw [← intervalIntegral.integral_congr_ae (hae t ht), (hac t ht).integral_deriv_eq_sub]
  ring

/-- A linear combination of Lipschitz functions is Lipschitz. -/
lemma wd_lipschitzWith_lincomb {f h : ℝ → ℝ} {Kf Kh : NNReal} (hf : LipschitzWith Kf f)
    (hh : LipschitzWith Kh h) (a b : ℝ) : ∃ K, LipschitzWith K fun x ↦ a * f x + b * h x := by
  refine ⟨Real.toNNReal (|a| * Kf + |b| * Kh), LipschitzWith.of_dist_le' fun x y ↦ ?_⟩
  have h1 := hf.dist_le_mul x y
  have h2 := hh.dist_le_mul x y
  simp only [Real.dist_eq] at h1 h2 ⊢
  calc |a * f x + b * h x - (a * f y + b * h y)| = |a * (f x - f y) + b * (h x - h y)| := by
        congr 1; ring
    _ ≤ |a| * |f x - f y| + |b| * |h x - h y| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |a| * (Kf * |x - y|) + |b| * (Kh * |x - y|) := by gcongr
    _ = (|a| * Kf + |b| * Kh) * |x - y| := by ring

/-- `det(σ', σ'') = κ`: for `σ = g s` with `g' = gX`, `det g = det X = 1`, the curvature
`det(gXs, g(X² + X')s)` is `det(s, (X + X⁻¹X')s)` (`eqn:state-dep-curvature`). -/
lemma wd_det2_curv {A Y Y' : Mat2} (hA : A.det = 1) (hY : Y.det = 1) (s : Fin 2 → ℝ) :
    det2 ((A * Y) *ᵥ s) ((A * (Y * Y + Y')) *ᵥ s) = det2 s ((Y + Y⁻¹ * Y') *ᵥ s) := by
  have hYY : Y * Y + Y' = Y * (Y + Y⁻¹ * Y') := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (by rw [hY]; exact isUnit_one),
      Matrix.one_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, oct_det2_mulVec, hA, one_mul, hYY,
    ← Matrix.mulVec_mulVec, oct_det2_mulVec, hY, one_mul]

/-- **The linear normalization** (§2.2, §2.4): a worst disk has a linear image, by a matrix of
positive determinant, with a critical hexagon whose edge midpoints are the sixth roots of unity
`s_j*` (critical hexagons are invariant under orientation-preserving linear maps,
`bdy_isLeastAreaHexagon_image`). -/
theorem wd_exists_normalize {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) :
    ∃ A : Mat2, 0 < A.det ∧ ∃ v, IsLeastAreaHexagon ((fun x ↦ A *ᵥ x) '' K) v ∧
      ∀ j, hexMidpoint v j = sixthRoot j := by
  -- a critical hexagon (Lemma 2.2.7)
  obtain ⟨φ, -, -, hφv⟩ := (lemma2_2_7 hK).2
  obtain ⟨v, hv, -⟩ := hφv 0
  have hcpos : 0 < det2 (hexMidpoint v 0) (hexMidpoint v 1) := by
    have := bdy_det2_hexMidpoint_pos hv.1 0; rwa [zero_add] at this
  have hs3 : det2 (sixthRoot 0) (sixthRoot 1) = √3 / 2 := (bdy_isMultiPoint_sixthRoot 0).2.2
  have hspos : 0 < det2 (sixthRoot 0) (sixthRoot 1) := by rw [hs3]; positivity
  -- the linear map `e` with `e m₀ = s₀*`, `e m₁ = s₁*`
  set e := bdy_normalize hcpos.ne' hspos.ne'
  have hδ : 0 < det2 (sixthRoot 0) (sixthRoot 1) / det2 (hexMidpoint v 0) (hexMidpoint v 1) :=
    div_pos hspos hcpos
  have hA := bdy_normalize_det2 hcpos.ne' hspos.ne'
  have hAm : ∀ i, e (hexMidpoint v i) = sixthRoot i := by
    refine bdy_seq_eq (fun k ↦ ?_) (fun k ↦ bdy_mp_succ bdy_isMultiPoint_sixthRoot k)
      (bdy_normalize_zero hcpos.ne' hspos.ne') (bdy_normalize_one hcpos.ne' hspos.ne')
    rw [bdy_hexMidpoint_succ hv.1 k, map_add]
  -- its matrix
  set M : Mat2 := LinearMap.toMatrix' (e : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) with hM
  have hMv : ∀ x, M *ᵥ x = e x := fun x ↦ by
    rw [hM, LinearMap.toMatrix'_mulVec]; rfl
  refine ⟨M, ?_, fun i ↦ e (v i), ?_, fun i ↦ by rw [bdy_hexMidpoint_comp, hAm]⟩
  · rw [hM, LinearMap.det_toMatrix', bdy_linearMap_det e hA]; exact hδ
  · have him : (fun x ↦ M *ᵥ x) '' K = e '' K := by simp only [hMv]
    rw [him]
    exact bdy_isLeastAreaHexagon_image e hδ hA hv

/-- **The reparameterization with `det X = 1`** (Proposition 3.1.9). A balanced pair `(K, σ)` in
circle representation has a reparameterization `σ' = σ ∘ s` that is again a balanced pair in
circle representation, with `σ'_j = g s_j*` and `det(g⁻¹g') = 1` everywhere. -/
theorem wd_exists_balancedPair_det_one {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    {tf : ℝ} (h : IsBalancedPair K σ tf) (hc : IsCircleRepresentation σ) :
    ∃ (σ' : ZMod 6 → ℝ → Fin 2 → ℝ) (T : ℝ) (g : ℝ → Mat2), IsBalancedPair K σ' T ∧
      IsCircleRepresentation σ' ∧ (∀ j t, σ' j t = g t *ᵥ sixthRoot j) ∧
      ∀ t, ((g t)⁻¹ * derivEntrywise g t).det = 1 := by
  have h' := h
  obtain ⟨hK, hC, -, hmp, -, -, htf, hper, hinj, himg⟩ := h'
  obtain ⟨g, hg⟩ := wd_exists_g hmp
  set P₀ := 6 * tf with hP₀
  have hP₀pos : 0 < P₀ := by positivity
  have hgb := wd_balanced_g h hg
  set X : ℝ → Mat2 := fun t ↦ (g t)⁻¹ * derivEntrywise g t with hX_def
  have hdetpos : ∀ t, 0 < (X t).det := fun t ↦
    (corollary3_1_6 K σ tf h g (fun t j ↦ hg j t) t).2.2.2.2.2.2.2
  -- continuity and periodicity of `g`, `g'` and `X = g⁻¹g'`
  have hσd : ∀ j, Continuous (deriv (σ j)) := fun j ↦ (hC j).1.continuous_deriv le_rfl
  have hg'0 : ∀ t i, derivEntrywise g t i 0 = deriv (σ 0) t i := fun t i ↦ by
    rw [(wd_entries (derivEntrywise g t) i).1, (hgb t).2.2]
  have hg'1 : ∀ t i, derivEntrywise g t i 1 =
      2 / √3 * (deriv (σ 2) t i + deriv (σ 0) t i / 2) := fun t i ↦ by
    rw [(wd_entries (derivEntrywise g t) i).2, (hgb t).2.2, (hgb t).2.2]
  have hg'c : Continuous (derivEntrywise g) := continuous_iff_entrywise.2 fun i k ↦ by
    fin_cases k
    · simp only [Fin.zero_eta, hg'0]; exact (continuous_apply i).comp (hσd 0)
    · simp only [Fin.mk_one, hg'1]
      exact continuous_const.mul (((continuous_apply i).comp (hσd 2)).add
        (((continuous_apply i).comp (hσd 0)).div_const 2))
  have hgc : Continuous g := continuous_iff_entrywise.2 fun i j ↦
    continuous_iff_continuousAt.2 fun t ↦ ((hgb t).2.1 i j).continuousAt
  have hinv : ∀ t, (g t)⁻¹ = (g t).adjugate := fun t ↦ by
    rw [Matrix.inv_def, (hgb t).1, Ring.inverse_one, one_smul]
  have hXc : Continuous X := by
    have : X = fun t ↦ (g t).adjugate * derivEntrywise g t := funext fun t ↦ by
      simp only [hX_def, hinv]
    rw [this]
    exact hgc.matrix_adjugate.mul hg'c
  have hgper : ∀ t, g (t + P₀) = g t := fun t ↦
    wd_eq_of_mulVec (by rw [← hg, ← hg, hper]) (by rw [← hg, ← hg, hper])
  have hσdper : ∀ j t, deriv (σ j) (t + P₀) = deriv (σ j) t := fun j t ↦ by
    rw [← deriv_comp_add_const]
    congr 1
    funext s
    exact hper j s
  have hg'per : ∀ t, derivEntrywise g (t + P₀) = derivEntrywise g t := fun t ↦ by
    ext i k
    fin_cases k
    · simp only [Fin.zero_eta, hg'0, hσdper]
    · simp only [Fin.mk_one, hg'1, hσdper]
  have hXper : ∀ t, X (t + P₀) = X t := fun t ↦ by simp only [hX_def, hgper, hg'per]
  -- the time `ℓ(s) = ∫₀ˢ √(det X)` and its inverse `S` (Proposition 3.1.9)
  set δ : ℝ → ℝ := fun t ↦ √((X t).det) with hδ_def
  have hδpos : ∀ t, 0 < δ t := fun t ↦ Real.sqrt_pos.2 (hdetpos t)
  have hdetc : Continuous fun t ↦ (X t).det := by
    simp only [Matrix.det_fin_two]
    have hc := continuous_iff_entrywise.1 hXc
    exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
  have hδc : Continuous δ := hdetc.sqrt
  have hδper : ∀ t, δ (t + P₀) = δ t := fun t ↦ by simp only [hδ_def, hXper]
  set ℓ : ℝ → ℝ := fun θ ↦ ∫ s in (0 : ℝ)..θ, δ s with hℓ_def
  have hℓ : ∀ θ, HasDerivAt ℓ (δ θ) θ := fun θ ↦ (hδc.integral_hasStrictDerivAt 0 θ).hasDerivAt
  have hℓ0 : ℓ 0 = 0 := by simp [hℓ_def]
  have hℓm : StrictMono ℓ := strictMono_of_deriv_pos fun θ ↦ by
    rw [(hℓ θ).deriv]; exact hδpos θ
  have hℓper : ∀ θ, ℓ (θ + P₀) = ℓ θ + ℓ P₀ := by
    have hd : ∀ θ, HasDerivAt (fun θ ↦ ℓ (θ + P₀) - ℓ θ) 0 θ := fun θ ↦ by
      have := (HasDerivAt.comp_add_const θ P₀ (hℓ (θ + P₀))).sub (hℓ θ)
      rwa [hδper, sub_self] at this
    intro θ
    have hc := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt)
      (fun s ↦ (hd s).deriv) θ 0
    simp only [zero_add, hℓ0, sub_zero] at hc
    linarith
  obtain ⟨hLpos, S, hSc, hSm, hS0, -, hℓS, hSL, hSd⟩ :=
    wd_exists_inverse hℓ hδpos hℓ0 hP₀pos hℓper
  set L := ℓ P₀ with hL_def
  have hSL' : S L = P₀ := by have := hSL 0; rwa [zero_add, hS0, zero_add] at this
  set S' : ℝ → ℝ := fun t ↦ (δ (S t))⁻¹ with hS'_def
  have hS'pos : ∀ t, 0 < S' t := fun t ↦ inv_pos.2 (hδpos _)
  have hS'c : Continuous S' := (hδc.comp hSc).inv₀ fun t ↦ (hδpos _).ne'
  -- `det(S' X(S)) = 1`
  have hdet1 : ∀ t, (S' t • X (S t)).det = 1 := fun t ↦ by
    rw [Matrix.det_smul, Fintype.card_fin, hS'_def]
    simp only [hδ_def]
    rw [inv_pow, Real.sq_sqrt (hdetpos _).le, inv_mul_cancel₀ (hdetpos _).ne']
  -- the reparameterized curves
  set σ' : ZMod 6 → ℝ → Fin 2 → ℝ := fun j t ↦ σ j (S t) with hσ'_def
  set G : ℝ → Mat2 := fun t ↦ g (S t) with hG_def
  have hG : ∀ j t, σ' j t = G t *ᵥ sixthRoot j := fun j t ↦ hg j (S t)
  have hGd : ∀ t, HasDerivAtEntrywise G (S' t • derivEntrywise g (S t)) t := fun t ↦
    ((hgb (S t)).2.1).scomp (hSd t)
  have hGdet : ∀ t, ((G t)⁻¹ * derivEntrywise G t).det = 1 := fun t ↦ by
    rw [(hGd t).derivEntrywise, Matrix.mul_smul]
    exact hdet1 t
  have hσ'd : ∀ j t, HasDerivAt (σ' j) (S' t • deriv (σ j) (S t)) t := fun j t ↦
    (((hC j).1.differentiable one_ne_zero (S t)).hasDerivAt).scomp t (hSd t)
  have hσ'deriv : ∀ j, deriv (σ' j) = fun t ↦ S' t • deriv (σ j) (S t) := fun j ↦
    funext fun t ↦ (hσ'd j t).deriv
  have hσ'C : ∀ j, ContDiff ℝ 1 (σ' j) := fun j ↦ contDiff_one_iff_deriv.2
    ⟨fun t ↦ (hσ'd j t).differentiableAt, by rw [hσ'deriv]; exact hS'c.smul ((hσd j).comp hSc)⟩
  have hσ'reg : ∀ j t, deriv (σ' j) t ≠ 0 := fun j t ↦ by
    rw [hσ'deriv]; exact smul_ne_zero (hS'pos t).ne' ((hC j).2 _)
  -- the boundary
  have hσK : ∀ j t, σ j t ∈ frontier K := fun j t ↦ by
    obtain ⟨y, hy, hyt⟩ := Function.Periodic.exists_mem_Ico₀ (hper j) hP₀pos t
    rw [hyt, ← himg j]
    exact mem_image_of_mem _ hy
  have himg' : ∀ j, σ' j '' Ico 0 L = frontier K := by
    intro j
    refine Subset.antisymm (image_subset_iff.2 fun t _ ↦ hσK j (S t)) fun x hx ↦ ?_
    rw [← himg j] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨ℓ y, ⟨?_, hℓm hy.2⟩, by simp only [hσ'_def, hℓS]⟩
    rw [← hℓ0]
    exact hℓm.monotone hy.1
  have hinj' : ∀ j, InjOn (σ' j) (Ico 0 L) := by
    intro j a ha b hb hab
    have hmem : ∀ r ∈ Ico 0 L, S r ∈ Ico 0 P₀ := fun r hr ↦
      ⟨by rw [← hS0]; exact hSm.monotone hr.1, by rw [← hSL']; exact hSm hr.2⟩
    exact hSm.injective (hinj j (hmem a ha) (hmem b hb) hab)
  have hper' : ∀ j t, σ' j (t + L) = σ' j t := fun j t ↦ by simp only [hσ'_def, hSL, hper]
  have hpar : ∀ j, IsPositiveBoundaryParam K (σ' j) := fun j ↦
    ⟨hσ'C j, hσ'reg j, Subset.antisymm (range_subset_iff.2 fun t ↦ hσK j (S t))
      (by rw [← himg' j]; exact image_subset_range _ _), fun t ↦ by
        rw [hσ'deriv, rein_det2_smul_right]
        exact mul_pos (hS'pos t) (oct_det2_deriv_pos h j (S t))⟩
  have hmp' : ∀ t, IsMultiPoint fun j ↦ σ' j t := fun t ↦ hmp (S t)
  have hbm : IsBoundaryMultiCurve K σ' := ⟨hpar, hmp'⟩
  -- the derivatives `σ'_j' = G X̃ s_j*` are Lipschitz: `G` and `X̃ = S' X(S)` are bounded and
  -- Lipschitz (Proposition 3.1.9)
  set Xt : ℝ → Mat2 := fun t ↦ S' t • X (S t) with hXt_def
  have hXtL : LipschitzOnEntrywise Xt univ := proposition3_1_9 K σ tf h g (fun t j ↦ hg j t) S S'
    hSd hS'pos hdet1
  have hXtc : Continuous Xt := hS'c.smul (hXc.comp hSc)
  have hXtper : ∀ t, Xt (t + L) = Xt t := fun t ↦ by
    simp only [hXt_def, hS'_def, hSL, hδper, hXper]
  have hXtB : ∀ a b, wd_LipBdd fun t ↦ Xt t a b := fun a b ↦ by
    obtain ⟨C, hC'⟩ := hXtL a b
    exact ⟨⟨C, lipschitzOnWith_univ.1 hC'⟩, wd_bdd_of_periodic
      ((continuous_iff_entrywise.1 hXtc) a b) hLpos fun t ↦ by simp only [hXtper]⟩
  -- `S` is Lipschitz: `S' = 1/δ(S)` is bounded
  obtain ⟨m, hm0, hmle⟩ : ∃ m, 0 < m ∧ ∀ t, m ≤ δ t := by
    obtain ⟨u₀, -, hu₀⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hP₀pos.le)
      hδc.continuousOn
    refine ⟨δ u₀, hδpos u₀, fun t ↦ ?_⟩
    obtain ⟨y, hy, hyt⟩ := Function.Periodic.exists_mem_Ico₀ hδper hP₀pos t
    rw [hyt]
    exact hu₀ (Ico_subset_Icc_self hy)
  have hSlip : LipschitzWith (Real.toNNReal m⁻¹) S := lipschitzWith_of_nnnorm_deriv_le
    (fun t ↦ (hSd t).differentiableAt) fun t ↦ by
      rw [(hSd t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 (hδpos _)), Real.coe_toNNReal _ (inv_pos.2 hm0).le]
      exact inv_anti₀ hm0 (hmle _)
  have hgB : ∀ a b, wd_LipBdd fun t ↦ G t a b := fun a b ↦ by
    refine wd_LipBdd_comp (f := fun s ↦ g s a b) ?_ hSlip
    exact wd_LipBdd_of_hasDerivAt (fun s ↦ (hgb s).2.1 a b)
      ((continuous_iff_entrywise.1 hg'c) a b) hP₀pos (fun s ↦ by simp only [hgper])
      (fun s ↦ by simp only [hg'per])
  have hσ'' : ∀ j t, deriv (σ' j) t = (G t * Xt t) *ᵥ sixthRoot j := fun j t ↦ by
    have e : derivEntrywise g (S t) = g (S t) * X (S t) := by
      simp only [hX_def]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (by rw [(hgb (S t)).1]; exact isUnit_one),
        Matrix.one_mul]
    rw [hσ'deriv]
    dsimp only
    rw [← (hgb (S t)).2.2, e]
    simp only [hXt_def, hG_def, Matrix.mul_smul, Matrix.smul_mulVec]
  have hlip : ∀ j, ∃ C, LipschitzWith C (deriv (σ' j)) := by
    intro j
    refine wd_lipschitzWith_pi fun i ↦ ?_
    have e : (fun t ↦ deriv (σ' j) t i) = fun t ↦
        (G t i 0 * Xt t 0 0 + G t i 1 * Xt t 1 0) * sixthRoot j 0 +
          (G t i 0 * Xt t 0 1 + G t i 1 * Xt t 1 1) * sixthRoot j 1 := funext fun t ↦ by
      rw [hσ'' j t]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
    rw [e]
    refine wd_LipBdd_lipschitzWith (wd_LipBdd_add (wd_LipBdd_mul (wd_LipBdd_add ?_ ?_)
      (wd_LipBdd_const _)) (wd_LipBdd_mul (wd_LipBdd_add ?_ ?_) (wd_LipBdd_const _)))
    · exact wd_LipBdd_mul (hgB i 0) (hXtB 0 0)
    · exact wd_LipBdd_mul (hgB i 1) (hXtB 1 0)
    · exact wd_LipBdd_mul (hgB i 0) (hXtB 0 1)
    · exact wd_LipBdd_mul (hgB i 1) (hXtB 1 1)
  have h6 : 6 * (L / 6) = L := by ring
  refine ⟨σ', L / 6, G, ⟨hK, fun j ↦ ⟨hσ'C j, hσ'reg j⟩, hlip, hmp', lemma2_4_6 hK hbm hlip,
    fun j t ↦ lemma2_4_5 hK hbm j t, by positivity, ?_, ?_, ?_⟩, fun j ↦ ?_, hG, hGdet⟩
  · rw [h6]; exact hper'
  · rw [h6]; exact hinj'
  · rw [h6]; exact himg'
  · simp only [hσ'_def, hS0]; exact hc j

/-- **The shift relation** (§3.5). For a balanced pair `(K, σ)` in circle representation with
`K` a worst disk, parameterized with `det X = 1` (`σ_j = g s_j*`, `X = g⁻¹g'`), the curves follow
one another: `σ_j(t + t_f) = σ_{j+1}(t)`. -/
theorem wd_shift {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {T : ℝ} {g : ℝ → Mat2}
    (hK : IsWorstDisk K) (h : IsBalancedPair K σ T) (hc : IsCircleRepresentation σ)
    (hg : ∀ j t, σ j t = g t *ᵥ sixthRoot j) (hdet : ∀ t, ((g t)⁻¹ * derivEntrywise g t).det = 1) :
    ∀ j t, σ j (t + T) = σ (j + 1) t := by
  have hK1 := hK.1
  have hgb := wd_balanced_g h hg
  have h' := h
  obtain ⟨-, -, -, hmp, -, -, hT, hper, -, himg⟩ := h'
  set P := 6 * T with hP_def
  have hP : 0 < P := by positivity
  have hs0 := oct_isStarCurve h 0
  have hs1 := oct_isStarCurve h 1
  set A := PlaneCurve.sc_angle (σ 0) with hA_def
  set B := PlaneCurve.sc_angle (σ 1) with hB_def
  have hσK : ∀ j t, σ j t ∈ frontier K := fun j t ↦ by
    obtain ⟨y, hy, hyt⟩ := Function.Periodic.exists_mem_Ico₀ (hper j) hP t
    rw [hyt, ← himg j]
    exact mem_image_of_mem _ hy
  -- polar forms: `σ₀(t) = rein_bd K (A t)`, `σ₁(t) = rein_bd K (π/3 + B t)`
  have hdir0 : σ 0 0 = rein_dir 0 := by
    rw [hc]; ext i; fin_cases i <;> simp [sixthRoot, rein_dir]
  have hdir1 : σ 1 0 = rein_dir (π / 3) := by
    rw [hc]
    have : (1 : ZMod 6).val = 1 := rfl
    ext i; fin_cases i <;> simp [sixthRoot, rein_dir, this]
  have hA : ∀ t, σ 0 t = rein_bd K (A t) := fun t ↦ by
    obtain ⟨r, hr, e⟩ := wd_polar hs0 hdir0 t
    rw [zero_add] at e
    exact rein_eq_bd hK1 (hσK 0 t) hr e
  have hB : ∀ t, σ 1 t = rein_bd K (π / 3 + B t) := fun t ↦ by
    obtain ⟨r, hr, e⟩ := wd_polar hs1 hdir1 t
    exact rein_eq_bd hK1 (hσK 1 t) hr e
  -- the inverse of the angle `A`
  have hAd := hs0.sc_hasDerivAt_angle
  have hApos := hs0.sc_logDeriv_im_pos
  have hAper : ∀ t, A (t + P) = A t + 2 * π := fun t ↦ by
    rw [hA_def, hs0.sc_angle_add_period, hs0.sc_angle_period]
  obtain ⟨-, Ai, -, -, -, hAAi, -, -, hAid⟩ :=
    wd_exists_inverse hAd hApos PlaneCurve.sc_angle_zero hP hAper
  -- the reparameterization `hh` with `σ₀(hh t) = σ₁(t)`
  set hh : ℝ → ℝ := fun t ↦ Ai (π / 3 + B t) with hh_def
  have hAhh : ∀ t, A (hh t) = π / 3 + B t := fun t ↦ hAAi _
  have hhσ : ∀ t, σ 0 (hh t) = σ 1 t := fun t ↦ by rw [hA, hAhh, hB]
  -- multi-point uniqueness: `σ_j(hh t) = σ_{j+1}(t)`, so `g(hh t) = g(t) R`
  have hmul : ∀ t j, σ j (hh t) = σ (j + 1) t := fun t ↦
    wd_multiPoint_eq hK (hmp (hh t)) (wd_isMultiPoint_shift (hmp t)) (fun j ↦ hσK j _)
      (fun j ↦ hσK _ t) (by rw [hhσ, zero_add])
  have hgh : ∀ t, g (hh t) = g t * R := fun t ↦ wd_eq_of_mulVec
    (by rw [← hg, hmul, hg, ← Matrix.mulVec_mulVec, oct_R_mulVec_sixthRoot])
    (by rw [← hg, hmul, hg, ← Matrix.mulVec_mulVec, oct_R_mulVec_sixthRoot])
  -- `hh` is differentiable with a positive derivative
  have hBd := hs1.sc_hasDerivAt_angle
  set c : ℝ → ℝ := fun t ↦
    ((PlaneCurve.sc_logDeriv (σ 0) (hh t)).im)⁻¹ * (PlaneCurve.sc_logDeriv (σ 1) t).im
    with hc_def
  have hhd : ∀ t, HasDerivAt hh (c t) t := fun t ↦
    (hAid (π / 3 + B t)).comp t ((hBd t).const_add _)
  have hcpos : ∀ t, 0 < c t := fun t ↦
    mul_pos (inv_pos.2 (hApos _)) (hs1.sc_logDeriv_im_pos t)
  -- differentiating `g(hh t) = g(t) R`: `hh' g'(hh t) = g'(t) R`; determinants give `hh' = 1`
  have hg'det : ∀ s, (derivEntrywise g s).det = 1 := fun s ↦ by
    have e : derivEntrywise g s = g s * ((g s)⁻¹ * derivEntrywise g s) := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (by rw [(hgb s).1]; exact isUnit_one),
        Matrix.one_mul]
    rw [e, Matrix.det_mul, (hgb s).1, hdet s, one_mul]
  have hRdet : R.det = 1 := by
    have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    simp only [R, Matrix.det_fin_two_of]
    linear_combination h3 / 4
  have hc1 : ∀ t, c t = 1 := fun t ↦ by
    have e1 : HasDerivAtEntrywise (fun s ↦ g (hh s)) (c t • derivEntrywise g (hh t)) t :=
      ((hgb (hh t)).2.1).scomp (hhd t)
    have e2 : HasDerivAtEntrywise (fun s ↦ g s * R) (derivEntrywise g t * R) t :=
      (hgb t).2.1.mul_const R
    rw [show (fun s ↦ g (hh s)) = fun s ↦ g s * R from funext hgh] at e1
    have heq := congrArg Matrix.det (e1.unique e2)
    rw [Matrix.det_smul, Fintype.card_fin, hg'det, Matrix.det_mul, hg'det, hRdet] at heq
    have := hcpos t
    nlinarith
  -- so `hh(t) = t + T₀`
  set T₀ := hh 0 with hT₀_def
  have hhT : ∀ t, hh t = t + T₀ := fun t ↦ by
    have hd : ∀ s, HasDerivAt (fun s ↦ hh s - s) 0 s := fun s ↦ by
      have := (hhd s).sub (hasDerivAt_id s)
      rwa [hc1, sub_self] at this
    have := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt) (fun s ↦ (hd s).deriv)
      t 0
    simp only [sub_zero] at this
    linarith
  have hshift0 : ∀ j t, σ j (t + T₀) = σ (j + 1) t := fun j t ↦ by rw [← hhT, hmul]
  -- `6 T₀ = 6 T`: the angle `A(t + T₀) - A(t)` stays in `(0, π)`, so `A(t + 3T₀) = A(t) + π`
  have hAT : ∀ t, A (t + T₀) = π / 3 + B t := fun t ↦ by rw [← hhT, hAhh]
  set D : ℝ → ℝ := fun t ↦ A (t + T₀) - A t with hD_def
  have hA0 : A 0 = 0 := PlaneCurve.sc_angle_zero
  have hB0 : B 0 = 0 := PlaneCurve.sc_angle_zero
  have hD0 : D 0 = π / 3 := by
    have := hAT 0
    simp only [hD_def]
    rw [this, hA0, hB0]
    ring
  have hsin : ∀ t, 0 < Real.sin (D t) := fun t ↦ by
    have hd : det2 (σ 0 t) (σ 1 t) = √3 / 2 := by simpa using ((hmp t) 0).2.2
    rw [← zero_add (1 : ZMod 6), ← hshift0 0 t, hA, hA] at hd
    exact (rein_det2_bd_pos_iff hK1 _ _).1 (by rw [hd]; positivity)
  have hDc : Continuous D :=
    (hs0.sc_continuous_angle.comp (continuous_id.add continuous_const)).sub
      hs0.sc_continuous_angle
  have hDmem : ∀ t, 0 < D t ∧ D t < π := by
    intro t
    have hπ := Real.pi_pos
    by_contra hcon
    have hor : D t ≤ 0 ∨ π ≤ D t := by
      by_contra h''
      push Not at h''
      exact hcon h''
    rcases hor with h1 | h1
    · obtain ⟨u, -, hu⟩ := intermediate_value_uIcc (a := 0) (b := t) hDc.continuousOn
        (show (0 : ℝ) ∈ uIcc (D 0) (D t) from
          mem_uIcc.2 (Or.inr ⟨h1, by rw [hD0]; positivity⟩))
      have := hsin u
      rw [hu, Real.sin_zero] at this
      exact lt_irrefl _ this
    · obtain ⟨u, -, hu⟩ := intermediate_value_uIcc (a := 0) (b := t) hDc.continuousOn
        (show π ∈ uIcc (D 0) (D t) from mem_uIcc.2 (Or.inl ⟨by rw [hD0]; linarith, h1⟩))
      have := hsin u
      rw [hu, Real.sin_pi] at this
      exact lt_irrefl _ this
  have h3 : ∀ t, A (t + 3 * T₀) = A t + π := fun t ↦ by
    have e : σ 0 (t + T₀ + T₀ + T₀) = -σ 0 t := by
      rw [hshift0, hshift0, hshift0]
      have := ((hmp t) 0).2.1
      simp only [zero_add] at this
      rw [show (0 : ZMod 6) + 1 + 1 + 1 = 3 from rfl]
      exact this
    rw [hA, hA, ← wd_bd_add_pi hK1] at e
    obtain ⟨k, hk⟩ := rein_bd_inj hK1 e
    have b1 := hDmem t
    have b2 := hDmem (t + T₀)
    have b3 := hDmem (t + T₀ + T₀)
    simp only [hD_def] at b1 b2 b3
    have hπ := Real.pi_pos
    have hk0 : k = 0 := by
      have h1 : (k : ℝ) < 1 := by nlinarith
      have h2 : (-1 : ℝ) < k := by nlinarith
      have : k < 1 := by exact_mod_cast h1
      have : -1 < k := by exact_mod_cast h2
      omega
    rw [hk0, Int.cast_zero, zero_mul, add_zero] at hk
    rw [show t + 3 * T₀ = t + T₀ + T₀ + T₀ by ring]
    linarith
  have h6 : A (6 * T₀) = A P := by
    have e1 : A (3 * T₀) = π := by have := h3 0; rwa [zero_add, hA0, zero_add] at this
    have e2 := h3 (3 * T₀)
    rw [show 3 * T₀ + 3 * T₀ = 6 * T₀ by ring, e1] at e2
    have e3 : A P = 2 * π := hs0.sc_angle_period
    rw [e2, e3]
    ring
  have hTT : T₀ = T := by
    have := hs0.sc_strictMono_angle.injective h6
    rw [hP_def] at this
    linarith
  intro j t
  rw [← hTT]
  exact hshift0 j t

/-- **The boundary trajectory of a balanced disk is admissible** (Chapter 3: Corollary 3.1.6,
Proposition 3.1.9, Lemma 3.3.1, Theorem 3.4.2, §3.5). For a balanced pair `(K, σ)` in circle
representation with `σ_j = g s_j*`, `det(g⁻¹g') = 1` and `σ_j(t + T) = σ_{j+1}(t)`, the trajectory
`(g, g⁻¹g')` with the control variables of Definition 3.3.2 (made a fixed point of `U_T` on the
null set where they are undefined) is admissible for Problem 3.6.2. -/
theorem wd_isReinhardtAdmissible {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {T : ℝ}
    {g : ℝ → Mat2} (h : IsBalancedPair K σ T) (hc : IsCircleRepresentation σ)
    (hg : ∀ j t, σ j t = g t *ᵥ sixthRoot j) (hdet : ∀ t, ((g t)⁻¹ * derivEntrywise g t).det = 1)
    (hshift : ∀ j t, σ j (t + T) = σ (j + 1) t) :
    ∃ u : ℝ → Fin 3 → ℝ, IsReinhardtAdmissible T u g fun t ↦ (g t)⁻¹ * derivEntrywise g t := by
  classical
  have hT : 0 < T := h.2.2.2.2.2.2.1
  have hσL := h.2.2.1
  have hcurv := h.2.2.2.2.1
  set X : ℝ → Mat2 := fun t ↦ (g t)⁻¹ * derivEntrywise g t with hX_def
  have hgb := wd_balanced_g h hg
  have hunit : ∀ t, IsUnit (g t).det := fun t ↦ by rw [(hgb t).1]; exact isUnit_one
  have hgX : ∀ t, g t * X t = derivEntrywise g t := fun t ↦ by
    simp only [hX_def]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hunit t), Matrix.one_mul]
  have hgd : ∀ t, HasDerivAtEntrywise g (g t * X t) t := fun t ↦ by
    rw [hgX]; exact (hgb t).2.1
  have hgc : Continuous g := continuous_iff_entrywise.2 fun i j ↦
    continuous_iff_continuousAt.2 fun t ↦ ((hgb t).2.1 i j).continuousAt
  -- the star states (Corollary 3.1.6)
  have htr : ∀ t, (X t).trace = 0 := fun t ↦
    oct_trace_eq_zero (s := univ) univ_mem (hgd t) fun x _ ↦ (hgb x).1
  have hρ : ∀ t, 0 < ρ₀ (X t) ∧ 0 < ρ₁ (X t) ∧ 0 < ρ₂ (X t) := fun t ↦ by
    obtain ⟨h0, h1, h2, -⟩ := corollary3_1_6 K σ T h g (fun t j ↦ hg j t) t
    exact ⟨h0, h1, h2⟩
  -- `X` is Lipschitz (Proposition 3.1.9, with the trivial reparameterization)
  have hXL : LipschitzOnEntrywise X univ := by
    have := proposition3_1_9 K σ T h g (fun t j ↦ hg j t) id (fun _ ↦ 1) (fun t ↦ hasDerivAt_id t)
      (fun _ ↦ one_pos) (fun t ↦ by simpa using hdet t)
    simpa using this
  have hXc : Continuous X := continuous_iff_entrywise.2 fun i j ↦ by
    obtain ⟨C, hC⟩ := hXL i j
    exact continuousOn_univ.1 hC.continuousOn
  -- `g'` is Lipschitz: its entries are those of `σ₀'` and `σ₂'`
  have hg'L : LipschitzOnEntrywise (derivEntrywise g) (Icc 0 T) := by
    intro i k
    obtain ⟨C0, hC0⟩ := hσL 0
    obtain ⟨C2, hC2⟩ := hσL 2
    have l0 : LipschitzWith (1 * C0) fun t ↦ deriv (σ 0) t i := (LipschitzWith.eval i).comp hC0
    have l2 : LipschitzWith (1 * C2) fun t ↦ deriv (σ 2) t i := (LipschitzWith.eval i).comp hC2
    have e0 : (fun t ↦ derivEntrywise g t i 0) = fun t ↦ deriv (σ 0) t i := funext fun t ↦ by
      rw [(wd_entries (derivEntrywise g t) i).1, (hgb t).2.2]
    have e1 : (fun t ↦ derivEntrywise g t i 1) =
        fun t ↦ 2 / √3 * deriv (σ 2) t i + 1 / √3 * deriv (σ 0) t i := funext fun t ↦ by
      rw [(wd_entries (derivEntrywise g t) i).2, (hgb t).2.2, (hgb t).2.2]; ring
    fin_cases k
    · exact ⟨1 * C0, by simp only [Fin.zero_eta]; rw [e0]; exact l0.lipschitzOnWith⟩
    · obtain ⟨C, hC⟩ := wd_lipschitzWith_lincomb l2 l0 (2 / √3) (1 / √3)
      exact ⟨C, by simp only [Fin.mk_one]; rw [e1]; exact hC.lipschitzOnWith⟩
  -- the curvatures `κ_j ≥ 0` almost everywhere (item 4 of Definition 2.4.7): where `X` is
  -- differentiable, `κ_j = det(σ_{2j}', σ_{2j}'')`
  have hXdiff : ∀ᵐ t, HasDerivAtEntrywise X (derivEntrywise X t) t := by
    have : ∀ i j, ∀ᵐ t, DifferentiableAt ℝ (fun s ↦ X s i j) t := fun i j ↦ by
      obtain ⟨C, hC⟩ := hXL i j
      exact (lipschitzOnWith_univ.1 hC).ae_differentiableAt
    filter_upwards [ae_all_iff.2 fun i ↦ ae_all_iff.2 (this i)] with t ht i j
    exact (ht i j).hasDerivAt
  have hκ : ∀ᵐ t, t ∈ Ioo 0 T → ∀ j, 0 ≤ stateCurvature (X t) (derivEntrywise X t) j := by
    filter_upwards [hXdiff, hcurv 0, hcurv 2, hcurv 4] with t hXt h0 h2 h4 _ j
    have hσ1 : ∀ k, deriv (σ k) t = (g t * X t) *ᵥ sixthRoot k := fun k ↦ by
      rw [hgX, (hgb t).2.2]
    have hdd : ∀ k, deriv (deriv (σ k)) t =
        (g t * (X t * X t + derivEntrywise X t)) *ᵥ sixthRoot k := by
      intro k
      have hfun : deriv (σ k) = fun s ↦ (g s * X s) *ᵥ sixthRoot k := funext fun s ↦ by
        rw [hgX, (hgb s).2.2]
      have hd := ((hgd t).mul hXt).mulVec_const (sixthRoot k)
      rw [hfun, hd.deriv]
      simp only [Matrix.mul_add, Matrix.mul_assoc]
    have key : ∀ k, det2 (deriv (σ k) t) (deriv (deriv (σ k)) t) =
        det2 (sixthRoot k) ((X t + (X t)⁻¹ * derivEntrywise X t) *ᵥ sixthRoot k) := fun k ↦ by
      rw [hσ1, hdd]; exact wd_det2_curv (hgb t).1 (hdet t) _
    simp only [stateCurvature]
    rw [← key]
    fin_cases j
    · exact h0
    · exact h2
    · exact h4
  -- Lemma 3.3.1 and Theorem 3.4.2, with the control variables `u = κ/(κ₀ + κ₁ + κ₂)`
  have hgW : ∀ t ∈ Icc 0 T, HasDerivWithinAtEntrywise g (derivEntrywise g t) (Icc 0 T) t :=
    fun t _ ↦ (hgb t).2.1.hasDerivWithinAtEntrywise
  have hpos := lemma3_3_1 T g (derivEntrywise g) hgW (fun t _ ↦ (hgb t).1) X (fun t ↦ rfl)
    (fun t _ ↦ hρ t) hκ
  set κ : ℝ → Fin 3 → ℝ := fun t ↦ stateCurvature (X t) (derivEntrywise X t) with hκ_def
  have hdyn := theorem3_4_2 T g (derivEntrywise g) hgW (fun t _ ↦ (hgb t).1) hg'L X
    (fun t ↦ rfl) (fun t _ ↦ hdet t) (fun t _ ↦ hρ t) hκ (fun t ↦ controlVariables (κ t))
    (fun t ↦ rfl)
  set good : ℝ → Prop := fun t ↦ (∀ j, 0 ≤ κ t j) ∧ 0 < κ t 0 + κ t 1 + κ t 2 with hgood_def
  set u : ℝ → Fin 3 → ℝ := fun t ↦ if good t then controlVariables (κ t) else fun _ ↦ 1 / 3
    with hu_def
  have hgood : ∀ᵐ t, t ∈ Ioo 0 T → good t := by
    filter_upwards [hκ, hpos] with t h1 h2 ht
    refine ⟨h1 ht, ?_⟩
    obtain ⟨j, hj⟩ := h2 ht
    have := h1 ht
    fin_cases j <;> simp at hj <;> linarith [this 0, this 1, this 2]
  have hus : ∀ t, u t ∈ controlSimplex := by
    intro t
    by_cases hgt : good t
    · rw [hu_def]; simp only [hgt, ite_true]
      obtain ⟨h1, h2⟩ := hgt
      refine ⟨fun i ↦ ⟨div_nonneg (h1 i) h2.le, (div_le_one h2).2 ?_⟩, ?_⟩
      · fin_cases i <;> simp <;> linarith [h1 0, h1 1, h1 2]
      · simp only [controlVariables]; field_simp
    · rw [hu_def]; simp only [hgt, ite_false]
      exact ⟨fun i ↦ ⟨by norm_num, by norm_num⟩, by norm_num⟩
  -- measurability of the control
  have hX'm : Measurable (derivEntrywise X) :=
    Measurable.of_eval_matrix _ fun i j ↦ measurable_deriv (fun s ↦ X s i j)
  have hinv : ∀ t, (X t)⁻¹ = (X t).adjugate := fun t ↦ by
    rw [Matrix.inv_def, hdet t, Ring.inverse_one, one_smul]
  have hκm : Measurable κ := by
    have hF : Continuous fun p : Mat2 × Mat2 ↦ fun j : Fin 3 ↦
        det2 (sixthRoot (2 * (j.val : ZMod 6)))
          ((p.1 + p.1.adjugate * p.2) *ᵥ sixthRoot (2 * (j.val : ZMod 6))) := by
      refine continuous_pi fun j ↦ ?_
      have hc : Continuous fun p : Mat2 × Mat2 ↦
          (p.1 + p.1.adjugate * p.2) *ᵥ sixthRoot (2 * (j.val : ZMod 6)) :=
        (continuous_fst.add (continuous_fst.matrix_adjugate.mul continuous_snd)).matrix_mulVec
          continuous_const
      unfold det2
      exact (continuous_const.mul ((continuous_apply 1).comp hc)).sub
        (continuous_const.mul ((continuous_apply 0).comp hc))
    have : κ = fun t ↦ (fun p : Mat2 × Mat2 ↦ fun j : Fin 3 ↦
        det2 (sixthRoot (2 * (j.val : ZMod 6)))
          ((p.1 + p.1.adjugate * p.2) *ᵥ sixthRoot (2 * (j.val : ZMod 6))))
          (X t, derivEntrywise X t) := by
      funext t j
      simp only [hκ_def, stateCurvature, hinv]
    rw [this]
    have : SecondCountableTopology Mat2 :=
      inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
    exact hF.measurable.comp (hXc.measurable.prodMk hX'm)
  have hum : Measurable u := by
    refine Measurable.ite ?_ ?_ measurable_const
    · have e : {t | good t} = (⋂ j, {t | 0 ≤ κ t j}) ∩ {t | 0 < κ t 0 + κ t 1 + κ t 2} := by
        ext t; simp [hgood_def]
      rw [e]
      have hκj : ∀ j, Measurable fun t ↦ κ t j := fun j ↦ (measurable_pi_apply j).comp hκm
      exact (MeasurableSet.iInter fun j ↦ measurableSet_le measurable_const (hκj j)).inter
        (measurableSet_lt measurable_const (((hκj 0).add (hκj 1)).add (hκj 2)))
    · have hκj : ∀ j, Measurable fun t ↦ κ t j := fun j ↦ (measurable_pi_apply j).comp hκm
      exact Measurable.of_eval fun j ↦ (by
        exact (hκj j).div (((hκj 0).add (hκj 1)).add (hκj 2)) :
          Measurable fun t ↦ κ t j / (κ t 0 + κ t 1 + κ t 2))
  -- the integral curves
  have hgI : IsIntegralCurve g (fun t ↦ g t * X t) T :=
    Matrix.eq_add_integral_of_hasDerivAtEntrywise_off_countable countable_empty hgc.continuousOn
      (fun t _ ↦ hgd t) fun i j ↦
        ((continuous_iff_entrywise.1 (hgc.mul hXc)) i j).intervalIntegrable _ _
  have hXI : IsIntegralCurve X
      (fun t ↦ controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) T := by
    refine wd_isIntegralCurve_of_lipschitz hT.le (fun i j ↦ ?_) ?_
    · obtain ⟨C, hC⟩ := hXL i j
      exact ⟨C, hC.mono (subset_univ _)⟩
    · filter_upwards [hdyn, hgood] with t h1 h2 ht
      have e : u t = controlVariables (κ t) := ite_eq_left_iff.2 fun h ↦ (h (h2 ht)).elim
      rw [e]
      convert h1 ht using 1
      simp only [controlP, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  -- the boundary conditions (§3.5)
  have hg0 : g 0 = 1 := wd_eq_of_mulVec (by rw [← hg, hc, Matrix.one_mulVec])
    (by rw [← hg, hc, Matrix.one_mulVec])
  have hgshift : ∀ t, g (t + T) = g t * R := fun t ↦ wd_eq_of_mulVec
    (by rw [← hg, hshift, hg, ← Matrix.mulVec_mulVec, oct_R_mulVec_sixthRoot])
    (by rw [← hg, hshift, hg, ← Matrix.mulVec_mulVec, oct_R_mulVec_sixthRoot])
  have hgT : g T = R := by have := hgshift 0; rwa [zero_add, hg0, Matrix.one_mul] at this
  have hg'T : derivEntrywise g T = derivEntrywise g 0 * R := by
    have h1 : HasDerivAtEntrywise (fun s ↦ g (s + T)) (derivEntrywise g (0 + T)) 0 :=
      fun i j ↦ HasDerivAt.comp_add_const 0 T ((hgb (0 + T)).2.1 i j)
    have h2 : HasDerivAtEntrywise (fun s ↦ g s * R) (derivEntrywise g 0 * R) 0 :=
      (hgb 0).2.1.mul_const R
    rw [show (fun s ↦ g (s + T)) = fun s ↦ g s * R from funext hgshift, zero_add] at h1
    exact h1.unique h2
  have hXT : X T = R⁻¹ * X 0 * R := by
    simp only [hX_def, hgT, hg0, inv_one, Matrix.one_mul, hg'T, Matrix.mul_assoc]
  exact ⟨u, ⟨hT, hum, fun t _ ↦ hus t, fun t _ ↦ ⟨(hgb t).1, htr t, hdet t, hρ t⟩, hgI, hXI⟩,
    hg0, hgT, hXT⟩

end SmoothedPolygons
