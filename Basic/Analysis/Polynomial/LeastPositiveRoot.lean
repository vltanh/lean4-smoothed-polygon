module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Continuity of the least positive zero of a family of real functions

Let `f x : ℝ → ℝ` depend continuously on a parameter `x` (the map `(x, t) ↦ f x t` is jointly
continuous; for instance the evaluation of a family of real polynomials whose coefficients are
continuous in `x`). The least positive zero `inf {t > 0 | f x t = 0}` is continuous at `x₀` when it
is a sign change of `f x₀` before which `f x₀` is positive
(`tendsto_sInf_pos_zeros_of_signChange`): the intermediate value theorem gives zeros of `f x` just
after it, and compactness of `[0, T - ε]` keeps `f x` positive before it. A simple least positive
root of a real polynomial is such a sign change (`Polynomial.tendsto_sInf_pos_roots_of_simple`).

Tools:
* `tendsto_csInf_of_eventually`: `sInf (S x) → a` when eventually `S x` meets `(-∞, a + ε)` and
  misses `(-∞, a - ε]`;
* `eventually_forall_pos_of_isCompact`: positivity on a compact set persists under perturbation of
  the parameter (the tube lemma);
* `Polynomial.discr_eq_zero_of_isRoot_of_isRoot_derivative`: a double root forces the
  discriminant to vanish (Bézout for the resultant of `f` and `f'`).
-/

@[expose] public section

open Set Filter Topology Function

/-- `sInf (S i) → a` along `l` if, eventually, `S i` has an element below `a + ε` and all its
elements lie above `a - ε`. -/
theorem tendsto_csInf_of_eventually {ι : Type*} {l : Filter ι} {S : ι → Set ℝ} {a : ℝ}
    (hup : ∀ ε > 0, ∀ᶠ i in l, ∃ t ∈ S i, t < a + ε)
    (hlow : ∀ ε > 0, ∀ᶠ i in l, ∀ t ∈ S i, a - ε < t) :
    Tendsto (fun i ↦ sInf (S i)) l (𝓝 a) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hup (ε / 2) (half_pos hε), hlow (ε / 2) (half_pos hε)] with i ⟨t, ht, hlt⟩ hl
  have h1 : sInf (S i) ≤ t := csInf_le ⟨a - ε / 2, fun s hs ↦ (hl s hs).le⟩ ht
  have h2 : a - ε / 2 ≤ sInf (S i) := le_csInf ⟨t, ht⟩ fun s hs ↦ (hl s hs).le
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Positivity on a compact set persists** (the tube lemma): if `f x₀ > 0` on a compact set `K`
and `(x, y) ↦ f x y` is continuous at the points of `{x₀} × K`, then `f x > 0` on `K` for `x` near
`x₀`. -/
theorem eventually_forall_pos_of_isCompact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y → ℝ} {x₀ : X} {K : Set Y} (hK : IsCompact K)
    (hf : ∀ y ∈ K, ContinuousAt (uncurry f) (x₀, y)) (hpos : ∀ y ∈ K, 0 < f x₀ y) :
    ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, 0 < f x y :=
  hK.eventually_forall_of_forall_eventually fun y hy ↦
    (hf y hy).eventually (lt_mem_nhds (hpos y hy))

/-- **Continuity of the least positive zero at a sign change.** Let `(x, t) ↦ f x t` be continuous.
If `f x₀ > 0` on `[0, T)`, `T > 0`, and `f x₀` takes negative values arbitrarily close to `T` on
the right, then the least positive zero of `f x` tends to `T` as `x → x₀`. -/
theorem tendsto_sInf_pos_zeros_of_signChange {X : Type*} [TopologicalSpace X] {f : X → ℝ → ℝ}
    (hf : Continuous (uncurry f)) {x₀ : X} {T : ℝ} (hT : 0 < T)
    (hpos : ∀ t ∈ Ico 0 T, 0 < f x₀ t) (hneg : ∀ ε > 0, ∃ t ∈ Ioo T (T + ε), f x₀ t < 0) :
    Tendsto (fun x ↦ sInf {t | 0 < t ∧ f x t = 0}) (𝓝 x₀) (𝓝 T) := by
  apply tendsto_csInf_of_eventually
  · -- a zero of `f x` in `(0, s]`, where `f x₀ s < 0`, by the intermediate value theorem
    intro ε hε
    obtain ⟨s, hs, hfs⟩ := hneg ε hε
    have h0 : ∀ᶠ x in 𝓝 x₀, 0 < f x 0 :=
      (hf.uncurry_right 0).continuousAt.eventually (lt_mem_nhds (hpos 0 ⟨le_rfl, hT⟩))
    have h1 : ∀ᶠ x in 𝓝 x₀, f x s < 0 :=
      (hf.uncurry_right s).continuousAt.eventually (gt_mem_nhds hfs)
    filter_upwards [h0, h1] with x hx0 hxs
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' (by linarith [hs.1] : (0 : ℝ) ≤ s)
      (hf.uncurry_left x).continuousOn ⟨hxs.le, hx0.le⟩
    refine ⟨c, ⟨lt_of_le_of_ne hc.1 ?_, hfc⟩, by linarith [hc.2, hs.2]⟩
    rintro rfl
    exact hx0.ne' hfc
  · -- `f x > 0` on the compact `[0, T - ε]`
    intro ε hε
    have := eventually_forall_pos_of_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := T - ε))
      (fun y _ ↦ hf.continuousAt) (fun y hy ↦ hpos y ⟨hy.1, by linarith [hy.2]⟩)
    filter_upwards [this] with x hx t ⟨ht, hft⟩
    by_contra hle
    exact (hx t ⟨ht.le, not_lt.1 hle⟩).ne' hft

namespace Polynomial

/-- **A double root forces the discriminant to vanish**: if `f(r) = f'(r) = 0` for a nonzero
polynomial `f` over a domain, then `discr f = 0`. Proof: `resultant f f' = ± lc(f) · discr f`
(`resultant_deriv`) is a combination `f p + f' q` (`exists_mul_add_mul_eq_C_resultant`), which
vanishes at `r`. -/
theorem discr_eq_zero_of_isRoot_of_isRoot_derivative {R : Type*} [CommRing R] [IsDomain R]
    {f : R[X]} (hf : f ≠ 0) {r : R} (h : f.IsRoot r) (h' : f.derivative.IsRoot r) :
    f.discr = 0 := by
  have hdeg : 0 < f.degree := by
    by_contra hd
    have hc := eq_C_of_degree_le_zero (not_lt.1 hd)
    rw [hc, IsRoot, eval_C] at h
    exact hf (by rw [hc, h, map_zero])
  have hn : f.natDegree ≠ 0 := (natDegree_pos_iff_degree_pos.2 hdeg).ne'
  obtain ⟨p, q, -, -, e⟩ := exists_mul_add_mul_eq_C_resultant f f.derivative le_rfl
    (natDegree_derivative_le f) (Or.inl hn)
  have e' := congrArg (eval r) e
  rw [eval_add, eval_mul, eval_mul, h.eq_zero, h'.eq_zero, zero_mul, zero_mul, add_zero, eval_C,
    resultant_deriv hdeg] at e'
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hf
  rcases mul_eq_zero.1 e'.symm with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    · exact absurd h2 hlc
  · exact h1

/-- **A simple least positive root of a real polynomial depends continuously on the
polynomial.** Let `x ↦ P x` be a family of real polynomials with jointly continuous evaluation
`(x, t) ↦ (P x)(t)` (for instance, with coefficients continuous in `x`). If `(P x₀)(0) > 0` and the
least positive root `T` of `P x₀` is simple, then the least positive root of `P x` tends to `T` as
`x → x₀`. -/
theorem tendsto_sInf_pos_roots_of_simple {X : Type*} [TopologicalSpace X] {P : X → ℝ[X]}
    (hP : Continuous fun q : X × ℝ ↦ (P q.1).eval q.2) {x₀ : X} {T : ℝ} (hT : 0 < T)
    (h0 : 0 < (P x₀).eval 0) (hroot : (P x₀).IsRoot T)
    (hleast : ∀ t ∈ Ioo 0 T, (P x₀).eval t ≠ 0) (hsimple : (P x₀).derivative.eval T ≠ 0) :
    Tendsto (fun x ↦ sInf {t | 0 < t ∧ (P x).eval t = 0}) (𝓝 x₀) (𝓝 T) := by
  -- `P x₀ > 0` on `[0, T)`: it is positive at `0` and has no root in `(0, T)`
  have hpos : ∀ t ∈ Ico 0 T, 0 < (P x₀).eval t := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | ht0
    · exact h0
    by_contra hle
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' ht.1 (P x₀).continuousOn ⟨not_lt.1 hle, h0.le⟩
    rcases hc.1.eq_or_lt with rfl | hc0
    · exact h0.ne' hfc
    · exact hleast c ⟨hc0, hc.2.trans_lt ht.2⟩ hfc
  refine tendsto_sInf_pos_zeros_of_signChange (f := fun x t ↦ (P x).eval t) hP hT hpos ?_
  -- the simple root is a sign change: otherwise `T` would be a local minimum
  intro ε hε
  by_contra! hge
  have hmin : IsLocalMin (fun t ↦ (P x₀).eval t) T := by
    have hmem : Ioo 0 (T + ε) ∈ 𝓝 T := Ioo_mem_nhds hT (by linarith)
    filter_upwards [hmem] with t ht
    rcases lt_trichotomy t T with htT | htT | htT
    · rw [hroot.eq_zero]; exact (hpos t ⟨ht.1.le, htT⟩).le
    · rw [htT]
    · rw [hroot.eq_zero]; exact hge t ⟨htT, ht.2⟩
  exact hsimple (hmin.hasDerivAt_eq_zero ((P x₀).hasDerivAt T))

end Polynomial
