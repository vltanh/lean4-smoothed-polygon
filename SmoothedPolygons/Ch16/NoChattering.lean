module

public import SmoothedPolygons.Ch16.ClusterPoint
public import SmoothedPolygons.Ch14.NoReturn

/-!
# Chapter 16: the hypothesis of Mahler's First from Theorems 16.4.1 and 14.4.1

The last step of the proof of Theorem 16.3.1 (Mahler's First conjecture) of Hales–Vajjha,
*Packings of Smoothed Polygons* (TeX 12817–12833): "The proof then reduces to the consideration of
a trajectory such that the infinite sequence of switching points has a subsequence tending to the
singular locus. Passing to the blow-up, which has a compact exceptional divisor, the sequence of
switching points has a subsequence tending to a limit on the exceptional divisor in finite time.
By Theorem 16.4.1 … the limit is `q_in` and the sequence approaches `q_in` along the stable curve
`W^s(q_in)`. By Theorem 14.4.1 and its time reversal, the stable curve `W^s(q_in)` did not come
from the exceptional divisor at an earlier time. Thus, the trajectory is not periodic. This is
contrary to the boundary conditions of the Reinhardt conjecture."

Layer 3 stated this step as the named hypothesis `NoChatteringIntoSingularLocus` of
`theorem16_3_1` (`SmoothedPolygons/Ch16/MahlerFirst.lean`). Here it is derived from Theorem 16.4.1
(`theorem16_4_1`, proved in this layer from the three named numerical facts of Layer 5 and N5) and
Theorem 14.4.1 (the named proposition `Theorem14_4_1`, Layer 7):

* `noChatteringIntoSingularLocus_of_clusterSetForwardInvariant`: from the numerical facts, N5 and
  Theorem 14.4.1;
* `noChatteringIntoSingularLocus_of_theorem14_4_1`: from the numerical facts and Theorem 14.4.1
  (N5 proved, `clusterSetForwardInvariant`);
* `theorem16_3_1_of_theorem14_4_1`: **Mahler's First conjecture conditional on Theorem 14.4.1 and
  the three named numerical facts of Theorem 16.1.1**.

## The argument (the steps of the docstring of `NoChatteringIntoSingularLocus`)

Let `(u, g, X, Λ₁, Λ_R, λ_cost)` be a Pontryagin extremal on `[0, T]`, edge extremal, whose lift
meets `𝒮_sing` at `t ∈ (0, T]` and chatters into it from the left; we derive a contradiction.
1. `λ_cost ≠ 0` at `𝒮_sing` (`IsExtremalOn.mem_singularLocus_iff`), so `λ_cost < 0`; scaling the
   costate by `-1/λ_cost > 0` (`IsExtremalOn.normalize`) gives `λ_cost = -1`.
2. The periodic extension (Remark 6.6.1, `remark6_6_1`) is a solution of the state–costate system on
   `[0, 2T]` with `X(s + T) = R⁻¹ X(s) R` etc. (`IsExtremalOn 0 (2T)`, normalized as in step 1);
   `𝒮_sing` is invariant under the rotation (`R⁻¹ J R = J`, `l6e_mem_singularLocus_rot`), so the
   extension meets `𝒮_sing` at `t + T` and avoids it on `(t + T - δ, t + T)` (the rotated copy of
   `(t - δ, t)`; `δ` is replaced by `min δ t`, so that the copy lies in `[T, 2T]`).
3. Let `e` be the last time in `[t, t + T - δ]` at which the extension meets `𝒮_sing` (the meeting
   times form a closed set containing `t`). On `(e, t + T)` the lift avoids `𝒮_sing`, and the
   control is bang-bang with finitely many switches on every compact `[α, β] ⊆ (e, t + T)`. The
   extension is **not** claimed to be edge extremal on `[0, 2T]` (an edge arc straddling `T` would
   need one edge costate across `T`, which `IsEdgeExtremalOn 0 T` does not provide); instead the
   finite bang-bang property is glued at `T`: if `α < T < β`, Theorem 8.3.2 (`theorem8_3_2`, with
   the edge extremality of Proposition 8.1.3 on `[0, T]`) on `[α, T]` for the original extremal and
   on `[0, β - T]` for the rotated copy (the controls are relabelled by
   `u'(s + T) = u'(s) ∘ (· - 1)`, which preserves finite bang-bang, `l6e_isFiniteBangBang_shift`),
   and the two finite switching sets together with `T` form a finite exceptional set on `[α, β]`
   (`l6e_isFiniteBangBang_glue`); if `β ≤ T` or `T ≤ α`, one of the two applies directly.
4. `exists_isChatteringArcInto` applied on `[e, t + T]` (its hypotheses only need the lift off
   `𝒮_sing` on `(e, t + T)`) gives, for any `e' ∈ (e, t + T)`, a chattering arc into `t + T` on
   `[e', t + T]`; Theorem 16.4.1, first part
   (`tendstoModVT_switchAng_of_clusterSetForwardInvariant`), says its switching points converge to
   `q_in` modulo `V_T`; the second part (the stable curve) is not used, so the assembly does not
   depend on Remark 14.3.4 or the stable manifold theorem.
5. Theorem 14.4.1, second statement (`Theorem14_4_1`), on `[e, t + T]` with `b = e'`: the lift
   avoids `𝒮_sing` at `e`, a contradiction ("Thus, the trajectory is not periodic").

Of the hypothesis `IsChatteringInto` only the avoidance of `𝒮_sing` on some `(t - δ, t)` is used:
the finite bang-bang structure on the excursion comes from Theorem 8.3.2 (step 3) and the
accumulation of the switching times from Lemma 8.3.4 (inside `exists_isChatteringArcInto`, "A
trajectory cannot reach the singular locus with finitely many switches").
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology MeasureTheory
open TriFuller

/-! ### Helpers: scaling the costate -/

/-- `F' = V` on `[0, T]` gives `(c F)' = c V`. -/
private lemma l6e_isIntegralCurve_smul {F V W : ℝ → Mat2} {T c : ℝ} (h : IsIntegralCurve F V T)
    (hW : ∀ t, W t = c • V t) : IsIntegralCurve (fun t ↦ c • F t) W T := by
  intro i j
  obtain ⟨hint, heq⟩ := h i j
  have hWij : (fun s ↦ W s i j) = fun s ↦ c * V s i j := funext fun s ↦ by rw [hW]; rfl
  refine ⟨by rw [hWij]; exact hint.const_mul c, fun t ht ↦ ?_⟩
  rw [hWij, intervalIntegral.integral_const_mul]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [heq t ht]
  ring

/-- **The state–costate system is homogeneous of degree one in `(Λ₁, Λ_R, λ_cost)`**: scaling the
costate of a solution with `λ_cost < 0` by `c = -1/λ_cost > 0` gives a solution with
`λ_cost = -1`; the Hamiltonian is multiplied by `c`. -/
private lemma l6e_isStateCostateSolution_normalize {T lam : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} (h : IsStateCostateSolution T u g X Λ₁ ΛR lam) (hlam : lam < 0) :
    IsStateCostateSolution T u g X (fun t ↦ (-lam)⁻¹ • Λ₁ t) (fun t ↦ (-lam)⁻¹ • ΛR t) (-1) := by
  obtain ⟨hst, -, hpt, hI1, hIR, hmax⟩ := h
  set c := (-lam)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.2 (by linarith)
  have hclam : c * (3 / 2 * lam) = 3 / 2 * -1 := by
    rw [hc, inv_neg, neg_mul, mul_left_comm, inv_mul_cancel₀ hlam.ne]
    ring
  have hJ : ∀ L : Mat2, c • L - (3 / 2 * -1 : ℝ) • J = c • (L - (3 / 2 * lam) • J) := by
    intro L
    rw [smul_sub, smul_smul, hclam]
  have hJ' : ∀ L : Mat2, -(c • L) + (3 / 2 * -1 : ℝ) • J = c • (-L + (3 / 2 * lam) • J) := by
    intro L
    rw [smul_add, smul_neg, smul_smul, hclam]
  have hH : ∀ (L R' X' : Mat2) (v : Fin 3 → ℝ),
      hamiltonian (-1) (c • L) (c • R') X' v = c * hamiltonian lam L R' X' v := by
    intro L R' X' v
    rw [hamiltonian, hamiltonian, hJ, traceForm_smul_left, traceForm_smul_left]
    ring
  refine ⟨hst, by norm_num, fun t ht ↦ ?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, -⟩ := hpt t ht
    exact ⟨by rw [Matrix.trace_smul, h1, smul_zero], by rw [Matrix.trace_smul, h2, smul_zero],
      by rw [traceForm_smul_left, h3, mul_zero], Or.inl (by norm_num)⟩
  · exact l6e_isIntegralCurve_smul hI1 fun t ↦ by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  · refine l6e_isIntegralCurve_smul hIR fun t ↦ ?_
    dsimp only
    rw [hJ', traceForm_smul_left]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    module
  · filter_upwards [hmax] with t ht htI
    obtain ⟨hH0, hM⟩ := ht htI
    refine ⟨by rw [hH, hH0, mul_zero], fun v hv ↦ ?_⟩
    rw [hH, hH]
    exact mul_le_mul_of_nonneg_left (hM v hv) hcpos.le

/-- **Normalization of the costate** (TeX 11484–11486: "We use the parameter values … `λ_cost = -1`.
Any trajectory that meets the singular locus must have these parameter values"; the Hamiltonian
and the costate equations are homogeneous of degree one in `(Λ₁, Λ_R, λ_cost)`): an extremal with
`λ_cost < 0`, with the costate scaled by `-1/λ_cost`, is an extremal with `λ_cost = -1`, and its
lift meets the singular locus at the same times. -/
theorem IsExtremalOn.normalize {a b lam : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) (hlam : lam < 0) :
    IsExtremalOn a b u g X (fun t ↦ (-lam)⁻¹ • Λ₁ t) (fun t ↦ (-lam)⁻¹ • ΛR t) (-1) ∧
      ∀ t, ((g t, (-lam)⁻¹ • Λ₁ t, X t, (-lam)⁻¹ • ΛR t) ∈ singularLocus ↔
        (g t, Λ₁ t, X t, ΛR t) ∈ singularLocus) := by
  refine ⟨l6e_isStateCostateSolution_normalize h hlam, fun t ↦ ?_⟩
  have hc : 0 < (-lam)⁻¹ := inv_pos.2 (by linarith)
  simp only [singularLocus, mem_ofPred_eq]
  constructor
  · rintro ⟨μ, hμ, hdet, h1, hX, hR⟩
    refine ⟨((-lam)⁻¹)⁻¹ * μ, mul_ne_zero (inv_ne_zero hc.ne') hμ, hdet, ?_, hX,
      (smul_eq_zero.1 hR).resolve_left hc.ne'⟩
    have e : Λ₁ t = ((-lam)⁻¹)⁻¹ • ((-lam)⁻¹ • Λ₁ t) := by
      rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    rw [e, h1, smul_smul]
    congr 1
    ring
  · rintro ⟨μ, hμ, hdet, h1, hX, hR⟩
    refine ⟨(-lam)⁻¹ * μ, mul_ne_zero hc.ne' hμ, hdet, ?_, hX, by rw [hR, smul_zero]⟩
    rw [h1, smul_smul]
    congr 1
    ring

/-! ### Helpers: finite bang-bang control on the periodic extension -/

/-- Finite bang-bang control on `[α, β]` depends only on the control on `(α, β)`. -/
private lemma l6e_isFiniteBangBang_congr {α β : ℝ} {v w : ℝ → Fin 3 → ℝ}
    (h : IsFiniteBangBang α β v) (hvw : ∀ s ∈ Ioo α β, w s = v s) : IsFiniteBangBang α β w := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun s hs hsS ↦ ?_⟩
  obtain ⟨i, ε, hε, hi⟩ := hS s hs hsS
  have h1 := min_le_left ε (min (s - α) (β - s))
  have h2 := (min_le_right ε (min (s - α) (β - s))).trans (min_le_left _ _)
  have h3 := (min_le_right ε (min (s - α) (β - s))).trans (min_le_right _ _)
  refine ⟨i, min ε (min (s - α) (β - s)),
    lt_min hε (lt_min (by linarith [hs.1]) (by linarith [hs.2])), ?_⟩
  filter_upwards [hi] with σ hσ hσI
  rw [hvw σ ⟨by linarith [hσI.1], by linarith [hσI.2]⟩]
  exact hσ ⟨by linarith [hσI.1], by linarith [hσI.2]⟩

/-- The rotated vertex: `(e_i)_{j-1} = (e_{i+1})_j`. -/
private lemma l6e_vertex_rot (i : Fin 3) : (fun j ↦ vertex i (j - 1)) = vertex (i + 1) := by
  funext j
  simp only [vertex, Pi.single_apply, sub_eq_iff_eq_add]

/-- **Finite bang-bang control under the rotation of the periodic extension**: if the control on
`[α, β]` is the control on `[α - T, β - T]` with its coordinates permuted cyclically
(`u'(s + T)_j = u'(s)_{j-1}`), finite bang-bang passes over (the exceptional set is translated;
a vertex goes to a vertex). -/
private lemma l6e_isFiniteBangBang_shift {α β T : ℝ} {v w : ℝ → Fin 3 → ℝ}
    (h : IsFiniteBangBang (α - T) (β - T) v)
    (hvw : ∀ s ∈ Ioo α β, w s = fun j ↦ v (s - T) (j - 1)) : IsFiniteBangBang α β w := by
  obtain ⟨S, hS⟩ := h
  classical
  refine ⟨S.image (· + T), fun s hs hsS ↦ ?_⟩
  have hs' : s - T ∈ Ioo (α - T) (β - T) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsS' : s - T ∉ S := fun h ↦ hsS (Finset.mem_image.2 ⟨_, h, by ring⟩)
  obtain ⟨i, ε, hε, hi⟩ := hS _ hs' hsS'
  have h1 := min_le_left ε (min (s - α) (β - s))
  have h2 := (min_le_right ε (min (s - α) (β - s))).trans (min_le_left _ _)
  have h3 := (min_le_right ε (min (s - α) (β - s))).trans (min_le_right _ _)
  refine ⟨i + 1, min ε (min (s - α) (β - s)),
    lt_min hε (lt_min (by linarith [hs.1]) (by linarith [hs.2])), ?_⟩
  have hmp := (measurePreserving_sub_right volume T).quasiMeasurePreserving
  filter_upwards [hmp.ae hi] with σ hσ hσI
  rw [hvw σ ⟨by linarith [hσI.1], by linarith [hσI.2]⟩,
    hσ ⟨by linarith [hσI.1], by linarith [hσI.2]⟩]
  exact l6e_vertex_rot i

/-- Finite bang-bang control on `[α, m]` and on `[m, β]` gives it on `[α, β]` (the exceptional
sets together with `m`). -/
private lemma l6e_isFiniteBangBang_glue {α m β : ℝ} {w : ℝ → Fin 3 → ℝ}
    (h₁ : IsFiniteBangBang α m w) (h₂ : IsFiniteBangBang m β w) : IsFiniteBangBang α β w := by
  obtain ⟨S₁, hS₁⟩ := h₁
  obtain ⟨S₂, hS₂⟩ := h₂
  classical
  refine ⟨S₁ ∪ S₂ ∪ {m}, fun s hs hsS ↦ ?_⟩
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hsS
  obtain ⟨⟨h1, h2⟩, h3⟩ := hsS
  rcases lt_or_gt_of_ne h3 with hlt | hgt
  · exact hS₁ s ⟨hs.1, hlt⟩ h1
  · exact hS₂ s ⟨hgt, hs.2⟩ h2

/-! ### Helpers: the singular locus under the rotation -/

private lemma l6e_det_R : R.det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [R, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

private lemma l6e_conj_inj {A B : Mat2} (h : R⁻¹ * A * R = R⁻¹ * B * R) : A = B := by
  have key : ∀ M : Mat2, R * (R⁻¹ * M * R) * R⁻¹ = M := fun M ↦ by
    rw [show R * (R⁻¹ * M * R) * R⁻¹ = (R * R⁻¹) * M * (R * R⁻¹) by
      simp only [Matrix.mul_assoc], mx_R_mul_R_inv, Matrix.one_mul, Matrix.mul_one]
  rw [← key A, h, key]

/-- `𝒮_sing` is invariant under the rotation of the periodic extension
(`(g, Λ₁, X, Λ_R) ↦ (gR, R⁻¹Λ₁R, R⁻¹XR, R⁻¹Λ_RR)`; `R⁻¹JR = J`, `det R = 1`). -/
private lemma l6e_mem_singularLocus_rot {G A B C : Mat2} :
    (G * R, R⁻¹ * A * R, R⁻¹ * B * R, R⁻¹ * C * R) ∈ singularLocus ↔
      (G, A, B, C) ∈ singularLocus := by
  have hJ : ∀ c : ℝ, R⁻¹ * (c • J) * R = c • J := fun c ↦ by
    rw [Matrix.mul_smul, Matrix.smul_mul, R_inv_mul_J_mul_R]
  have h0 : R⁻¹ * (0 : Mat2) * R = 0 := by simp
  simp only [singularLocus, mem_ofPred_eq, Matrix.det_mul, l6e_det_R, mul_one]
  constructor
  · rintro ⟨μ, hμ, hdet, h1, hX, hR⟩
    exact ⟨μ, hμ, hdet, l6e_conj_inj (h1.trans (hJ _).symm),
      l6e_conj_inj (hX.trans R_inv_mul_J_mul_R.symm), l6e_conj_inj (hR.trans h0.symm)⟩
  · rintro ⟨μ, hμ, hdet, h1, hX, hR⟩
    exact ⟨μ, hμ, hdet, by rw [h1, hJ], by rw [hX, R_inv_mul_J_mul_R], by rw [hR, h0]⟩

/-- **The hypothesis of Mahler's First from Theorems 16.4.1 and 14.4.1**, with N5 as a hypothesis
(the steps are in the module docstring). -/
theorem noChatteringIntoSingularLocus_of_clusterSetForwardInvariant (h₁ : DOutContracts)
    (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims) (hN5 : ClusterSetForwardInvariant)
    (hNR : Theorem14_4_1) : NoChatteringIntoSingularLocus := by
  intro T u g X Λ₁ ΛR lam hP hedge t ht hsing hchat
  obtain ⟨δ, hδ, -, hoffδ, -⟩ := hchat
  have hT : 0 < T := hP.1.1
  have h0T : IsExtremalOn 0 T u g X Λ₁ ΛR lam := hP.isExtremalOn le_rfl hT le_rfl
  have htI : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
  -- Step 1: `λ_cost < 0` at the singular locus
  have hlam : lam < 0 :=
    lt_of_le_of_ne hP.2.2.2.2.2.2.1 ((h0T.mem_singularLocus_iff htI).1 hsing).1
  -- Step 2: the periodic extension, a solution on `[0, 2T]`
  obtain ⟨u', g', X', Λ₁', ΛR', hu', hagree, hshift, -, -, -, hsol⟩ := remark6_6_1 hP
  have hext2 : IsExtremalOn 0 (2 * T) u' g' X' Λ₁' ΛR' lam := by
    have := hsol 2 (by norm_num)
    rw [show ((2 : ℕ) : ℝ) * T = 2 * T by norm_num] at this
    unfold IsExtremalOn
    simp only [zero_add, sub_zero]
    exact this
  obtain ⟨hextN, hsingN⟩ := hext2.normalize hlam
  -- the lift of the extension: equal to the original on `[0, T]`, rotated one period later
  have hagreeS : ∀ s ∈ Icc 0 T, ((g' s, Λ₁' s, X' s, ΛR' s) ∈ singularLocus ↔
      (g s, Λ₁ s, X s, ΛR s) ∈ singularLocus) := by
    intro s hs
    obtain ⟨hg, hX, h1, hR⟩ := hagree s hs
    rw [hg, hX, h1, hR]
  have hrot : ∀ s, 0 ≤ s → ((g' (s + T), Λ₁' (s + T), X' (s + T), ΛR' (s + T)) ∈ singularLocus ↔
      (g' s, Λ₁' s, X' s, ΛR' s) ∈ singularLocus) := by
    intro s hs
    obtain ⟨-, hg, hX, h1, hR⟩ := hshift s hs
    rw [hg, hX, h1, hR]
    exact l6e_mem_singularLocus_rot
  have hLt : (g' t, Λ₁' t, X' t, ΛR' t) ∈ singularLocus := (hagreeS t htI).2 hsing
  have hLtT : (g' (t + T), Λ₁' (t + T), X' (t + T), ΛR' (t + T)) ∈ singularLocus :=
    (hrot t ht.1.le).2 hLt
  -- the rotated copy of `(t - δ, t)` avoids `𝒮_sing` (with `δ' = min δ t`)
  have hδ'pos : 0 < min δ t := lt_min hδ ht.1
  have hδ't : min δ t ≤ t := min_le_right _ _
  have hδ'δ : min δ t ≤ δ := min_le_left _ _
  have hoffT : ∀ s ∈ Ioo (t + T - min δ t) (t + T),
      (g' s, Λ₁' s, X' s, ΛR' s) ∉ singularLocus := by
    intro s hs hsS
    have e : s - T + T = s := by ring
    have h1 := (hrot (s - T) (by linarith [hs.1])).1 (by rw [e]; exact hsS)
    exact hoffδ (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩
      ((hagreeS (s - T) ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩).1 h1)
  -- Step 3: `e`, the last meeting with `𝒮_sing` in `[t, t + T - δ']`
  have hsub : Icc t (t + T - min δ t) ⊆ Icc 0 (2 * T) :=
    Icc_subset_Icc ht.1.le (by linarith [ht.2])
  set Z : Set ℝ := Icc t (t + T - min δ t) ∩ (fun s ↦ (g' s, Λ₁' s, X' s, ΛR' s)) ⁻¹'
    {q : Mat2 × Mat2 × Mat2 × Mat2 | q.2.1 = (3 / 2 * lam) • J ∧ q.2.2.1 = J ∧ q.2.2.2 = 0}
    with hZ
  have hZc : IsClosed Z := by
    refine (hext2.continuousOn_lift.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc ?_
    exact (isClosed_eq (continuous_fst.comp continuous_snd) continuous_const).inter
      ((isClosed_eq (continuous_fst.comp (continuous_snd.comp continuous_snd))
        continuous_const).inter
      (isClosed_eq (continuous_snd.comp (continuous_snd.comp continuous_snd)) continuous_const))
  have hmemZ : ∀ s ∈ Icc t (t + T - min δ t),
      (s ∈ Z ↔ (g' s, Λ₁' s, X' s, ΛR' s) ∈ singularLocus) := by
    intro s hs
    rw [hext2.mem_singularLocus_iff (hsub hs)]
    exact ⟨fun h ↦ ⟨hlam.ne, h.2⟩, fun h ↦ ⟨hs, h.2⟩⟩
  have htT : t ≤ t + T - min δ t := by linarith [ht.2]
  have hbdd : BddAbove Z := ⟨t + T - min δ t, fun s hs ↦ hs.1.2⟩
  have heZ : sSup Z ∈ Z := hZc.csSup_mem ⟨t, (hmemZ t ⟨le_rfl, htT⟩).2 hLt⟩ hbdd
  set e := sSup Z with he
  have heI : e ∈ Icc t (t + T - min δ t) := heZ.1
  have hLe : (g' e, Λ₁' e, X' e, ΛR' e) ∈ singularLocus := (hmemZ e heI).1 heZ
  have het : e < t + T := by linarith [heI.2]
  have hfree : ∀ s ∈ Ioo e (t + T), (g' s, Λ₁' s, X' s, ΛR' s) ∉ singularLocus := by
    intro s hs hsS
    rcases le_or_gt s (t + T - min δ t) with hle | hgt
    · have hsI : s ∈ Icc t (t + T - min δ t) := ⟨heI.1.trans hs.1.le, hle⟩
      exact absurd (le_csSup hbdd ((hmemZ s hsI).2 hsS)) (not_le.2 hs.1)
    · exact hoffT s ⟨hgt, hs.2⟩ hsS
  -- finite bang-bang on compact subintervals of `(e, t + T)`, glued at `T`
  have hleft : ∀ α β, 0 < α → α < β → β ≤ T →
      (∀ s ∈ Icc α β, (g' s, Λ₁' s, X' s, ΛR' s) ∉ singularLocus) →
        IsFiniteBangBang α β u' := by
    intro α β hα hαβ hβ hS
    refine l6e_isFiniteBangBang_congr (theorem8_3_2 (hP.isExtremalOn hα.le hαβ hβ)
      (hedge.mono hα.le hβ) fun s hs ↦ ?_) fun s hs ↦ hu' s ⟨by linarith [hs.1], by
        linarith [hs.2]⟩
    rw [← hagreeS s ⟨by linarith [hs.1], by linarith [hs.2]⟩]
    exact hS s hs
  have hright : ∀ α β, T ≤ α → α < β → β < t + T →
      (∀ s ∈ Icc α β, (g' s, Λ₁' s, X' s, ΛR' s) ∉ singularLocus) →
        IsFiniteBangBang α β u' := by
    intro α β hα hαβ hβ hS
    refine l6e_isFiniteBangBang_shift (T := T) (v := u) (theorem8_3_2
      (hP.isExtremalOn (by linarith) (by linarith) (by linarith [ht.2]))
      (hedge.mono (by linarith) (by linarith [ht.2])) fun s hs ↦ ?_) fun s hs ↦ ?_
    · have hs0 : s ∈ Icc 0 T := ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩
      rw [← hagreeS s hs0, ← hrot s hs0.1]
      exact hS (s + T) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · have hs0 : 0 ≤ s - T := by linarith [hs.1]
      have e : s - T + T = s := by ring
      have h1 := (hshift (s - T) hs0).1
      rw [e] at h1
      rw [h1, hu' (s - T) ⟨hs0, by linarith [hs.2, ht.2]⟩]
  have hbb : ∀ α β, e < α → β < t + T → IsFiniteBangBang α β u' := by
    intro α β hα hβ
    rcases le_or_gt β α with hβα | hαβ
    · exact ⟨∅, fun s hs ↦ absurd (hs.1.trans hs.2) (not_lt.2 hβα)⟩
    have hS : ∀ s ∈ Icc α β, (g' s, Λ₁' s, X' s, ΛR' s) ∉ singularLocus := fun s hs ↦
      hfree s ⟨hα.trans_le hs.1, hs.2.trans_lt hβ⟩
    have hα0 : 0 < α := lt_of_lt_of_le ht.1 (heI.1.trans hα.le)
    rcases le_or_gt β T with hβT | hTβ
    · exact hleft α β hα0 hαβ hβT hS
    rcases le_or_gt T α with hTα | hαT
    · exact hright α β hTα hαβ hβ hS
    exact l6e_isFiniteBangBang_glue (hleft α T hα0 hαT le_rfl fun s hs ↦ hS s ⟨hs.1, by
      linarith [hs.2]⟩) (hright T β le_rfl hTβ hβ fun s hs ↦ hS s ⟨by linarith [hs.1], hs.2⟩)
  -- Step 4: a chattering arc into `t + T` from `e' ∈ (e, t + T)`; Theorem 16.4.1
  have hextNe := hextN.mono (by linarith [heI.1, ht.1]) het (by linarith [ht.2])
  have he' : (e + (t + T)) / 2 ∈ Ioo e (t + T) := ⟨by linarith, by linarith⟩
  obtain ⟨τ, hτ⟩ := exists_isChatteringArcInto hextNe ((hsingN (t + T)).2 hLtT)
    (fun s hs h ↦ hfree s hs ((hsingN s).1 h)) hbb _ he'
  have hconv := tendstoModVT_switchAng_of_clusterSetForwardInvariant h₁ h₂ h₃ hN5 hτ
  -- Step 5: Theorem 14.4.1 (second statement) on `[e, t + T]`: the lift avoids `𝒮_sing` at `e`
  exact hNR.2 e _ (t + T) u' g' X' _ _ τ hextNe ⟨he'.1.le, he'.2⟩ hbb hτ hconv e
    ⟨le_rfl, het⟩ ((hsingN e).2 hLe)

/-- **The hypothesis of Mahler's First from Theorem 14.4.1** and the three named numerical facts of
Theorem 16.1.1 (Theorem 16.4.1 is proved, `theorem16_4_1`). -/
theorem noChatteringIntoSingularLocus_of_theorem14_4_1 (h₁ : DOutContracts)
    (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims) (hNR : Theorem14_4_1) :
    NoChatteringIntoSingularLocus :=
  noChatteringIntoSingularLocus_of_clusterSetForwardInvariant h₁ h₂ h₃ clusterSetForwardInvariant
    hNR

/-- **Theorem 16.3.1** (`thm:mahler`, Mahler's First conjecture), **conditional on Theorem 14.4.1
and the three named numerical facts of Theorem 16.1.1** (`DOutContracts`, `CellTwoEntersDOut`,
`BoxSubclaims`): the global minimizer of the Reinhardt optimal control problem is a bang-bang
solution with finitely many switches, and the minimizer `K_min` is a finite-sided smoothed polygon
with rounded hyperbolic arcs at each corner of the sort described by Reinhardt and Mahler. -/
theorem theorem16_3_1_of_theorem14_4_1 (h₁ : DOutContracts) (h₂ : CellTwoEntersDOut)
    (h₃ : BoxSubclaims) (hNR : Theorem14_4_1) :
    (∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsReinhardtMinimizer T u g X →
      IsFiniteBangBang 0 T u) ∧
    ∀ K : Set (Fin 2 → ℝ), IsWorstDisk K → IsSmoothedPolygon K :=
  theorem16_3_1 (noChatteringIntoSingularLocus_of_theorem14_4_1 h₁ h₂ h₃ hNR)

end SmoothedPolygons
