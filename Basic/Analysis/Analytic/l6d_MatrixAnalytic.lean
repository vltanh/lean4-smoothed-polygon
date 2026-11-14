module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Analytic functions: matrix exponentials, linear ODEs and one-sided orders

Helpers for the analytic extension of the Reinhardt–Poincaré map (Hales–Vajjha, *Packings of
Smoothed Polygons*, Lemma 14.3.1; `SmoothedPolygons/Ch14/AnalyticExtension.lean`), where the closed
form of the extremal flow with a constant control must be shown analytic in time and initial data.
Mathlib has the analyticity of `NormedSpace.exp` in a Banach algebra (`NormedSpace.exp_analytic`)
but no analytic parametric integrals; the integrals of the closed form are replaced by the solution
`exp (t • L) y₀` of a linear ODE (`l6d_eq_exp_smul_apply_of_hasDerivAt`).

* `l6d_analyticAt_matrix_exp_apply`: the entries of `exp (A y)` are analytic in `y` when the entries
  of `A y` are (no norm on matrices appears in the statement; the proof uses the operator norm);
* `l6d_analyticAt_clm_of_apply`: a map into `W →L[ℝ] F`, `W` finite-dimensional, is analytic when
  it is analytic applied to every vector;
* `l6d_eq_exp_smul_apply_of_hasDerivAt`: a solution of `y' = L y` is `t ↦ exp (t • L) (y 0)`;
* `l6d_isBigO_nhds_of_isBigO_nhdsGT`: a one-variable analytic function which is `O(r^k)` as
  `r → 0⁺` is `O(r^k)` as `r → 0`.
-/

@[expose] public section

open Filter Topology Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The entries of the exponential of a matrix-valued function with analytic entries are
analytic. -/
theorem l6d_analyticAt_matrix_exp_apply {n : Type*} [Fintype n] [DecidableEq n]
    {A : E → Matrix n n ℝ} {x : E} (hA : ∀ i j, AnalyticAt ℝ (fun y ↦ A y i j) x) (i j : n) :
    AnalyticAt ℝ (fun y ↦ NormedSpace.exp (A y) i j) x := by
  open scoped Matrix.Norms.Operator in
  have hc : @CompleteSpace (Matrix n n ℝ) PseudoMetricSpace.toUniformSpace := by
    exact inferInstanceAs (CompleteSpace (Matrix n n ℝ))
  have hA' : AnalyticAt ℝ A x := by
    let L : (n → n → ℝ) →L[ℝ] Matrix n n ℝ :=
      LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap
    have h : AnalyticAt ℝ (fun y ↦ (fun i j ↦ A y i j : n → n → ℝ)) x :=
      AnalyticAt.pi fun i ↦ AnalyticAt.pi fun j ↦ hA i j
    exact (L.analyticAt _).comp h
  have hexp := (NormedSpace.exp_analytic (𝕂 := ℝ) (A x)).comp hA'
  let ev : Matrix n n ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ i j)
  exact (ev.analyticAt _).comp hexp

/-- A map into the continuous linear maps on a finite-dimensional space is analytic if it is
analytic applied to every vector (write `f y = Σᵢ (b.coord i).smulRight (f y (b i))`). -/
theorem l6d_analyticAt_clm_of_apply {W F : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → W →L[ℝ] F} {x : E} (hf : ∀ w, AnalyticAt ℝ (fun y ↦ f y w) x) :
    AnalyticAt ℝ f x := by
  let b := Module.finBasis ℝ W
  let c : Fin (Module.finrank ℝ W) → StrongDual ℝ W := fun i ↦
    LinearMap.toContinuousLinearMap (b.coord i)
  have hsum : f = fun y ↦ ∑ i, ContinuousLinearMap.smulRightL ℝ W F (c i) (f y (b i)) := by
    funext y
    refine ContinuousLinearMap.ext fun w ↦ ?_
    simp only [c, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRightL_apply_apply]
    have h := congrArg (f y) (b.sum_repr w)
    rw [← h, map_sum]
    simp [map_smul]
  rw [hsum]
  exact Finset.analyticAt_fun_sum _ fun i _ ↦
    ((ContinuousLinearMap.smulRightL ℝ W F (c i)).analyticAt _).comp (hf (b i))

/-- **Linear ODEs**: a solution of `y' = L y` on `ℝ` (in a Banach space) is
`y t = exp (t • L) (y 0)`. -/
theorem l6d_eq_exp_smul_apply_of_hasDerivAt {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {L : W →L[ℝ] W} {y : ℝ → W} (hy : ∀ t, HasDerivAt y (L (y t)) t) (t : ℝ) :
    y t = NormedSpace.exp (t • L) (y 0) := by
  have hE : ∀ s : ℝ, HasDerivAt (fun u : ℝ ↦ NormedSpace.exp ((-u) • L))
      (-(L * NormedSpace.exp ((-s) • L))) s := by
    intro s
    have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) L (-s)).scomp s (hasDerivAt_neg s)
    simpa [Function.comp_def] using h
  have hz : ∀ s, HasDerivAt (fun u ↦ NormedSpace.exp ((-u) • L) (y u)) 0 s := by
    intro s
    have h := (hE s).clm_apply (hy s)
    convert h using 1
    have hc : Commute L (NormedSpace.exp ((-s) • L)) :=
      (Commute.refl L).smul_right (-s) |>.exp_right
    have h2 : NormedSpace.exp ((-s) • L) (L (y s)) = L (NormedSpace.exp ((-s) • L) (y s)) := by
      simpa using (congrArg (fun T : W →L[ℝ] W ↦ T (y s)) hc.eq).symm
    rw [h2]
    exact (neg_add_cancel (L (NormedSpace.exp ((-s) • L) (y s)))).symm
  have hconst : ∀ s, NormedSpace.exp ((-s) • L) (y s) = y 0 := by
    intro s
    have h := is_const_of_deriv_eq_zero (fun u ↦ (hz u).differentiableAt) (fun u ↦ (hz u).deriv)
      s 0
    simpa using h
  have hinv : NormedSpace.exp (t • L) * NormedSpace.exp ((-t) • L) = 1 := by
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
      ((Commute.refl L).smul_left t |>.smul_right (-t))
      ((NormedSpace.expSeries_radius_eq_top ℝ (W →L[ℝ] W)).symm ▸ edist_lt_top _ _)
      ((NormedSpace.expSeries_radius_eq_top ℝ (W →L[ℝ] W)).symm ▸ edist_lt_top _ _),
      ← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  calc y t = (NormedSpace.exp (t • L) * NormedSpace.exp ((-t) • L)) (y t) := by rw [hinv]; rfl
    _ = NormedSpace.exp (t • L) (y 0) := by
      rw [← hconst t]; rfl

/-- An analytic function of one real variable which is `O(r^k)` as `r → 0⁺` is `O(r^k)` as
`r → 0`: its order at `0` is at least `k` (if `f = r^m g` with `g 0 ≠ 0` and `m < k`, then
`g = O(r^{k-m})` on the right, so `g 0 = 0`). -/
theorem l6d_isBigO_nhds_of_isBigO_nhdsGT {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : AnalyticAt ℝ f 0) {k : ℕ}
    (hk : f =O[𝓝[>] 0] (fun r ↦ r ^ k)) : f =O[𝓝 0] (fun r ↦ r ^ k) := by
  by_cases h0 : ∀ᶠ z in 𝓝 (0 : ℝ), f z = 0
  · exact (isBigO_zero _ _).congr' (h0.mono fun z hz ↦ hz.symm) EventuallyEq.rfl
  obtain ⟨n, g, hg, hg0, hfg⟩ := hf.exists_eventuallyEq_pow_smul_ne_zero_iff.2 h0
  simp only [sub_zero] at hfg
  by_cases hnk : k ≤ n
  · have hb : (fun z : ℝ ↦ z ^ (n - k) • g z) =O[𝓝 0] (fun _ ↦ (1 : ℝ)) :=
      ((continuous_pow (n - k)).continuousAt.smul hg.continuousAt).isBigO_one ℝ
    have he : f =ᶠ[𝓝 0] fun z ↦ z ^ k • (z ^ (n - k) • g z) := hfg.mono fun z hz ↦ by
      simp only [hz, smul_smul, ← pow_add, Nat.add_sub_cancel' hnk]
    refine IsBigO.congr' ?_ he.symm EventuallyEq.rfl
    simpa using (isBigO_refl (fun z : ℝ ↦ z ^ k) (𝓝 0)).smul hb
  exfalso
  push Not at hnk
  obtain ⟨c, hc⟩ := hk.bound
  have hlim : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have hT : Tendsto (fun z : ℝ ↦ c * z ^ (k - n)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun z : ℝ ↦ c * z ^ (k - n)) (𝓝 0) (𝓝 (c * 0 ^ (k - n))) :=
        (continuous_const.mul (continuous_pow _)).tendsto 0
      rw [zero_pow (Nat.sub_ne_zero_of_lt hnk), mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hT
    filter_upwards [hc, nhdsWithin_le_nhds hfg, self_mem_nhdsWithin] with z hz hfz hz0
    have hz0' : (0 : ℝ) < z := hz0
    rw [hfz, norm_smul, norm_pow, Real.norm_of_nonneg hz0'.le, norm_pow,
      Real.norm_of_nonneg hz0'.le] at hz
    have hpow : z ^ k = z ^ n * z ^ (k - n) := by rw [← pow_add, Nat.add_sub_cancel' hnk.le]
    rw [hpow] at hz
    have hzn : 0 < z ^ n := pow_pos hz0' n
    nlinarith [norm_nonneg (g z)]
  exact hg0 (tendsto_nhds_unique (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlim)

end
