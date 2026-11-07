module

public import SmoothedPolygons.Ch3.StateDynamics

/-!
# Re-centering a balanced disk at a time `t₀` (proof of Theorem 5.0.2)

The proof of Theorem 5.0.2 applies Theorem 5.0.6, a statement about the multi-point `s_j*` at time
`0` of a balanced disk in circle representation, at every time `t₀` of the boundary trajectory
(TeX 4486–4489: "If any point of the trajectory `(g, X)` passes through a point `X = Φ(z)` …").
That step needs the re-centered disk, which the book does not state: for a balanced pair `(K, σ)`
with `σ_j(t) = g(t) s_j*`, the pair

  `K' = g(t₀)⁻¹ K`, `σ'_j(t) = g(t₀)⁻¹ σ_j(t + t₀) = g'(t) s_j*`, `g'(t) = g(t₀)⁻¹ g(t + t₀)`,

is again a balanced pair, in circle representation, with the same area (`det g(t₀) = 1`), and
`g'⁻¹ g'' = X(· + t₀)`: its `X` at time `0` is `X(t₀)` (`IsBalancedPair.recenter`).

## Proof

`det g = 1` (the multi-point condition gives `det(g s₀*, g s₁*) = det g · det(s₀*, s₁*)`, both
determinants being `√3/2`), so `g(t₀)` is invertible and area-preserving
(`MeasureTheory.Measure.addHaar_image_linearMap`). Each condition of `IsBalancedPair` is invariant
under a linear map of determinant one (`IsCCSDisk` through the homeomorphism `v ↦ g(t₀)⁻¹ v`,
`C¹` and regularity, Lipschitz derivatives, multi-points, the sign of `det(σ', σ'')` since
`(Aσ)' = Aσ'` and `(Aσ)'' = Aσ''` everywhere for invertible `A`, the star condition) and under a
time shift (the curvature condition holds almost everywhere because translation preserves Lebesgue
measure; injectivity on `[0, 6t_f)` follows from injectivity on one period and periodicity,
through `toIcoMod`; the image of a period is the range of the curve). The entries of `g` are
differentiable, from its columns `g e₀ = σ₀` and `g e₁ = (2σ₁ - σ₀)/√3`, so `derivEntrywise`
commutes with the constant left factor and the time shift.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix

/-- `det(Av, Aw) = det A · det(v, w)`. -/
private lemma cp_det2_mulVec (A : Mat2) (v w : Fin 2 → ℝ) :
    det2 (A *ᵥ v) (A *ᵥ w) = A.det * det2 v w := by
  simp only [det2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]; ring

private lemma cp_sixthRoot_zero : sixthRoot 0 = ![1, 0] := by
  simp [sixthRoot]

private lemma cp_sixthRoot_one : sixthRoot 1 = ![1 / 2, √3 / 2] := by
  have : (1 : ZMod 6).val = 1 := rfl
  simp only [sixthRoot, this, Nat.cast_one, mul_one, Real.cos_pi_div_three,
    Real.sin_pi_div_three]

/-- A matrix of determinant one maps multi-points to multi-points. -/
private lemma cp_isMultiPoint_mulVec {s : ZMod 6 → Fin 2 → ℝ} (hs : IsMultiPoint s) {A : Mat2}
    (hA : A.det = 1) : IsMultiPoint fun j ↦ A *ᵥ s j := by
  intro j
  obtain ⟨h1, h2, h3⟩ := hs j
  refine ⟨?_, ?_, ?_⟩
  · simp only [← Matrix.mulVec_add, h1, Matrix.mulVec_zero]
  · simp only [h2, Matrix.mulVec_neg]
  · rw [cp_det2_mulVec, hA, one_mul, h3]

/-- The curve `g` with `σ_j = g s_j*` of a family of multi-points has `det g = 1`:
`det(σ₀, σ₁) = det g · det(s₀*, s₁*)` and both determinants are `√3/2`. -/
private lemma cp_det_g {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {g : ℝ → Mat2}
    (hmp : ∀ t, IsMultiPoint fun j ↦ σ j t) (hg : ∀ j t, σ j t = g t *ᵥ sixthRoot j) (t : ℝ) :
    (g t).det = 1 := by
  have h := (hmp t 0).2.2
  simp only [zero_add] at h
  rw [hg 0 t, hg 1 t, cp_det2_mulVec, cp_sixthRoot_zero, cp_sixthRoot_one] at h
  simp only [det2, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have h3 : (0 : ℝ) < √3 := by positivity
  nlinarith

/-- The columns of `g`: `g e₀ = σ₀` and `g e₁ = (2σ₁ - σ₀)/√3`. -/
private lemma cp_g_entry {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {g : ℝ → Mat2}
    (hg : ∀ j t, σ j t = g t *ᵥ sixthRoot j) (t : ℝ) (i : Fin 2) :
    g t i 0 = σ 0 t i ∧ g t i 1 = (2 * σ 1 t i - σ 0 t i) / √3 := by
  have h0 := congrFun (hg 0 t) i
  have h1 := congrFun (hg 1 t) i
  rw [cp_sixthRoot_zero] at h0
  rw [cp_sixthRoot_one] at h1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h0 h1
  have h3 : (0 : ℝ) < √3 := by positivity
  refine ⟨by linarith, ?_⟩
  rw [eq_div_iff h3.ne']
  linarith

/-- The entries of `g` are differentiable when the curves `σ_j` are. -/
private lemma cp_g_differentiable {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {g : ℝ → Mat2}
    (hC : ∀ j, ContDiff ℝ 1 (σ j)) (hg : ∀ j t, σ j t = g t *ᵥ sixthRoot j) (k j : Fin 2) :
    Differentiable ℝ fun s ↦ g s k j := by
  have hd : ∀ (j : ZMod 6) (k : Fin 2), Differentiable ℝ fun s ↦ σ j s k := fun j k ↦
    differentiable_pi.1 ((hC j).differentiable one_ne_zero) k
  fin_cases j
  · simp only [Fin.zero_eta, show (fun s ↦ g s k 0) = fun s ↦ σ 0 s k from
      funext fun s ↦ (cp_g_entry hg s k).1]
    exact hd 0 k
  · simp only [Fin.mk_one, show (fun s ↦ g s k 1) = fun s ↦ (2 * σ 1 s k - σ 0 s k) / √3 from
      funext fun s ↦ (cp_g_entry hg s k).2]
    exact (((hd 1 k).const_mul 2).sub (hd 0 k)).div_const _

/-- `(A f)' = A f'` for an invertible matrix `A` (both sides vanish where `f` is not
differentiable). -/
private lemma cp_deriv_mulVec {A : Mat2} (hA : IsUnit A.det) (f : ℝ → Fin 2 → ℝ) (t : ℝ) :
    deriv (fun s ↦ A *ᵥ f s) t = A *ᵥ deriv f t := by
  by_cases hf : DifferentiableAt ℝ f t
  · exact ((hasDerivAtEntrywise_const A t).mulVec hf.hasDerivAt).deriv.trans (by simp)
  · rw [deriv_zero_of_not_differentiableAt hf, Matrix.mulVec_zero]
    refine deriv_zero_of_not_differentiableAt fun h ↦ hf ?_
    have h' := (hasDerivAtEntrywise_const A⁻¹ t).mulVec h.hasDerivAt
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec] at h'
    exact h'.differentiableAt

/-- A `P`-periodic function injective on `[0, P)` is injective on every window `[c, c + P)`,
read as `t ↦ f(t + c)` on `[0, P)`. -/
private lemma cp_injOn_shift {α : Type*} {f : ℝ → α} {P : ℝ} (hP : 0 < P)
    (hper : Function.Periodic f P) (hinj : InjOn f (Ico 0 P)) (c : ℝ) :
    InjOn (fun t ↦ f (t + c)) (Ico 0 P) := by
  intro a ha b hb hab
  have hred : ∀ x, f (toIcoMod hP 0 x) = f x := fun x ↦ by
    rw [← self_sub_toIcoDiv_zsmul]; exact hper.sub_zsmul_eq _
  have hmem : ∀ x, toIcoMod hP 0 x ∈ Ico 0 P := toIcoMod_mem_Ico' hP
  have h := hinj (hmem (a + c)) (hmem (b + c)) (by simp only [hred]; exact hab)
  obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod hP).1 h
  have hself : ∀ x ∈ Ico 0 P, toIcoMod hP c (x + c) = x + c := fun x hx ↦
    (toIcoMod_eq_self hP).2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h' : toIcoMod hP c (a + c) = toIcoMod hP c (b + c) :=
    (toIcoMod_eq_toIcoMod hP).2 ⟨n, hn⟩
  rw [hself a ha, hself b hb] at h'
  linarith

/-- A `P`-periodic function takes all its values on `[0, P)`. -/
private lemma cp_image_Ico {α : Type*} {f : ℝ → α} {P : ℝ} (hP : 0 < P)
    (hper : Function.Periodic f P) : f '' Ico 0 P = range f := by
  refine (image_subset_range _ _).antisymm ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico hP x 0
  exact ⟨y, by simpa using hy, hxy.symm⟩

/-- **Re-centering a balanced disk** (used without statement in the proof of Theorem 5.0.2,
TeX 4486–4489). Let `(K, σ)` be a balanced pair with `σ_j(t) = g(t) s_j*`, and `t₀ ∈ ℝ`. Then
`K' = g(t₀)⁻¹ K` with `σ'_j(t) = g(t₀)⁻¹ σ_j(t + t₀)` is a balanced pair in circle
representation, with `σ'_j(t) = g'(t) s_j*` for `g'(t) = g(t₀)⁻¹ g(t + t₀)`,
`g'(t)⁻¹ g''(t) = g(t + t₀)⁻¹ g'(t + t₀)`, and `area(K') = area(K)`. -/
theorem IsBalancedPair.recenter {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hKσ : IsBalancedPair K σ tf) {g : ℝ → Mat2} (hg : ∀ j t, σ j t = g t *ᵥ sixthRoot j)
    (t₀ : ℝ) :
    IsBalancedPair ((fun v ↦ (g t₀)⁻¹ *ᵥ v) '' K) (fun j t ↦ (g t₀)⁻¹ *ᵥ σ j (t + t₀)) tf ∧
      IsCircleRepresentation (fun j t ↦ (g t₀)⁻¹ *ᵥ σ j (t + t₀)) ∧
      (∀ j t, (g t₀)⁻¹ *ᵥ σ j (t + t₀) = ((g t₀)⁻¹ * g (t + t₀)) *ᵥ sixthRoot j) ∧
      (∀ t, ((g t₀)⁻¹ * g (t + t₀))⁻¹ * derivEntrywise (fun s ↦ (g t₀)⁻¹ * g (s + t₀)) t =
        (g (t + t₀))⁻¹ * derivEntrywise g (t + t₀)) ∧
      volume ((fun v ↦ (g t₀)⁻¹ *ᵥ v) '' K) = volume K := by
  obtain ⟨hK, hC, hL, hmp, hcurv, hstar, htf, hper, hinj, himg⟩ := hKσ
  have hdet : ∀ t, (g t).det = 1 := cp_det_g hmp hg
  set A := (g t₀)⁻¹ with hAdef
  have hgu : IsUnit (g t₀).det := by rw [hdet]; exact isUnit_one
  have hAdet : A.det = 1 := by rw [hAdef, Matrix.det_nonsing_inv, hdet, Ring.inverse_one]
  have hAu : IsUnit A.det := by rw [hAdet]; exact isUnit_one
  have hAg : A * g t₀ = 1 := Matrix.nonsing_inv_mul _ hgu
  -- `v ↦ A v` as a homeomorphism and as a continuous linear map
  let e : (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ) :=
    { toFun := fun v ↦ A *ᵥ v
      invFun := fun v ↦ A⁻¹ *ᵥ v
      left_inv := fun v ↦ by
        simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec]
      right_inv := fun v ↦ by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mulVec]
      continuous_toFun := continuous_const.matrix_mulVec continuous_id
      continuous_invFun := continuous_const.matrix_mulVec continuous_id }
  have he : ∀ v, e v = A *ᵥ v := fun _ ↦ rfl
  have heK : (fun v ↦ A *ᵥ v) '' K = e '' K := rfl
  let L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)
  have hLv : ∀ v, L v = A *ᵥ v := fun _ ↦ rfl
  set σ' : ZMod 6 → ℝ → Fin 2 → ℝ := fun j t ↦ A *ᵥ σ j (t + t₀) with hσ'
  have hσd : ∀ j, Differentiable ℝ (σ j) := fun j ↦ (hC j).1.differentiable one_ne_zero
  -- the derivatives of the re-centered curves
  have hd1 : ∀ j, deriv (σ' j) = fun t ↦ A *ᵥ deriv (σ j) (t + t₀) := fun j ↦ funext fun t ↦ by
    rw [hσ', cp_deriv_mulVec hAu (fun s ↦ σ j (s + t₀)) t, deriv_comp_add_const]
  have hd2 : ∀ j t, deriv (deriv (σ' j)) t = A *ᵥ deriv (deriv (σ j)) (t + t₀) := fun j t ↦ by
    rw [hd1, cp_deriv_mulVec hAu (fun s ↦ deriv (σ j) (s + t₀)) t, deriv_comp_add_const]
  have hP : (0 : ℝ) < 6 * tf := by positivity
  have hper' : ∀ j, Function.Periodic (σ' j) (6 * tf) := fun j t ↦ by
    simp only [hσ', show t + 6 * tf + t₀ = t + t₀ + 6 * tf by ring, hper]
  refine ⟨⟨?_, fun j ↦ ⟨?_, fun t ↦ ?_⟩, fun j ↦ ?_, fun t ↦ ?_, fun j ↦ ?_, fun j t ↦ ?_, htf,
    fun j t ↦ hper' j t, fun j ↦ ?_, fun j ↦ ?_⟩, fun j ↦ ?_, fun j t ↦ ?_, fun t ↦ ?_, ?_⟩
  · -- `A K` is a centrally symmetric convex disk
    obtain ⟨hconv, hcpt, hint, hsymm⟩ := hK
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hconv.linear_image (Matrix.mulVecLin A)
    · rw [heK]; exact hcpt.image e.continuous
    · rw [heK, ← e.image_interior]; exact hint.image _
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨-v, hsymm v hv, Matrix.mulVec_neg _ _⟩
  · -- `C¹`
    have : σ' j = fun t ↦ L (σ j (t + t₀)) := rfl
    rw [this]
    exact L.contDiff.comp ((hC j).1.comp (contDiff_id.add contDiff_const))
  · -- regular
    rw [hd1]
    intro h0
    apply (hC j).2 (t + t₀)
    have := congrArg (fun v ↦ A⁻¹ *ᵥ v) h0
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec,
      Matrix.mulVec_zero] using this
  · -- Lipschitz derivatives
    obtain ⟨C, hC'⟩ := hL j
    refine ⟨‖L‖₊ * (C * 1), ?_⟩
    rw [hd1]
    have hsh : LipschitzWith 1 fun t : ℝ ↦ t + t₀ :=
      LipschitzWith.of_dist_le_mul fun x y ↦ by simp [dist_add_right]
    exact L.lipschitzWith.comp (hC'.comp hsh)
  · -- multi-points
    exact cp_isMultiPoint_mulVec (hmp (t + t₀)) hAdet
  · -- curvature
    have h := (measurePreserving_add_right volume t₀).quasiMeasurePreserving.ae (hcurv j)
    filter_upwards [h] with t ht
    rw [hd2, hd1, cp_det2_mulVec, hAdet, one_mul]
    exact ht
  · -- star condition
    obtain ⟨α, β, hα, hβ, h⟩ := hstar j (t + t₀)
    refine ⟨α, β, hα, hβ, ?_⟩
    rw [hd1]
    simp only [hσ', h, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub]
  · -- simple on a period
    have hi := cp_injOn_shift hP (fun t ↦ hper j t) (hinj j) t₀
    intro a ha b hb hab
    refine hi ha hb ?_
    have := congrArg (fun v ↦ A⁻¹ *ᵥ v) hab
    simpa only [hσ', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec]
      using this
  · -- the image of a period is the boundary
    rw [cp_image_Ico hP (hper' j), heK, ← e.image_frontier, ← himg j,
      cp_image_Ico hP (fun t ↦ hper j t)]
    have : σ' j = e ∘ σ j ∘ fun t ↦ t + t₀ := rfl
    have hs : range (fun t : ℝ ↦ t + t₀) = univ :=
      Function.Surjective.range_eq fun t ↦ ⟨t - t₀, by ring⟩
    rw [this, range_comp, range_comp, hs, image_univ]
  · -- circle representation
    simp only [hσ', zero_add, hg j t₀, Matrix.mulVec_mulVec, hAg, Matrix.one_mulVec]
  · rw [hg j (t + t₀), Matrix.mulVec_mulVec]
  · -- `X` is unchanged by the re-centering
    have hgd : ∀ u, HasDerivAtEntrywise g (derivEntrywise g u) u := fun u k l ↦
      (cp_g_differentiable (fun j ↦ (hC j).1) hg k l u).hasDerivAt
    have hD := (HasDerivAtEntrywise.scomp (h := fun x ↦ x + t₀) (t := t) (hgd (t + t₀))
      ((hasDerivAt_id' t).add_const t₀)).const_mul A
    rw [hD.derivEntrywise, Matrix.mul_inv_rev, hAdef, Matrix.nonsing_inv_nonsing_inv _ hgu]
    simp only [one_smul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (g t₀), Matrix.mul_nonsing_inv _ hgu, Matrix.one_mul]
  · -- area
    have : (fun v ↦ A *ᵥ v) '' K = Matrix.toLin' A '' K := rfl
    rw [this, MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin', hAdet,
      abs_one, ENNReal.ofReal_one, one_mul]

end SmoothedPolygons
