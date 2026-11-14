module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Dividing an analytic function by a power of a coordinate

If `f : ℝ × E → F` is analytic at `(0, y₀)` and, for every `y` near `y₀`, `r ↦ f (r, y)` is
`O(r^k)` at `0`, then `f (r, y) = r^k g(r, y)` near `(0, y₀)` with `g` analytic at `(0, y₀)`
(the "division of power series" of Hales–Vajjha, *Packings of Smoothed Polygons*, proof of
Lemma 14.3.1, TeX 11800–11806: "By Lemma 14.2.4, by division of power series, the function
`χ₂₁(…)/r₀³` extends to an analytic function"; and TeX 11846–11848 for `X_sw - J` and
`Λ₁sw + (3/2) J`).

Mathlib has the identity theorem in several variables
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) and the analytic implicit function
theorem (`ContDiffAt.implicitFunction` with `n = ω`), but no division by a coordinate.
Weierstrass preparation exists in Mathlib only for formal power series over a complete local
ring (`Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean`), not for convergent ones;
this lemma is the only division the Chapter 14 proofs need.

## Proof

By induction on `k`, dividing by `r` once at a time. If `f (r, y) = O(r^{k+1})` for `y` near
`y₀`, then `f (0, y) = 0` there, and `f = r • g₁` with `g₁` analytic (`l6a_exists_eq_smul`
below); then `g₁ (·, y) = O(r^k)` for `y` near `y₀` (`l6a_isBigO_of_eq_smul`: for `r ≠ 0` divide
by `r`, at `r = 0` use the continuity of `g₁`), and the induction hypothesis applies to `g₁`.

Division by `r` of a function vanishing on `{r = 0}` is a division of power series. Let `p` be
the power series of `f` at `(0, y₀)`, `π (r, y) = (0, y)` and `e₁ = (1, 0)`. For an
`(n + 1)`-linear map `P`, the `n`-linear map
`Q P (m) = Σ_i P (π m₀, …, π m_{i-1}, e₁, m_i, …, m_{n-1})` (`l6a_divTerm`, built with
`ContinuousMultilinearMap.curryMid` and `compContinuousLinearMap`) satisfies
`r • Q P (h, …, h) = P (h, …, h) - P (π h, …, π h)` for `h = (r, y)` (telescoping, since
`h - π h = r • e₁`; `l6a_smul_sum_divTerm`), and `‖Q P‖ ≤ (n + 1) ‖P‖`. So the series
`q n = Q (p (n + 1))` has a positive radius, and its sum `g` (analytic, `F` being complete)
satisfies `r • g (r, y) = f (r, y) - f (0, y) = f (r, y)` near `(0, y₀)`.

This replaces the plan of the layer-6 statements (expand in powers of `r` with analytic
coefficients `a_j (y)` and show `a_j = 0` for `j < k`), which needs the analyticity of the
coefficients and the convergence of the regrouped double series; the telescoping quotient
series needs neither.

Used by: the proof of `analyticAt_rescaledChi` (Step 3 of Lemma 14.3.1, `k = 3`, for `χ₂₁`) and
Step 7 of Lemma 14.3.1 (`k = 1, 2` for `X_sw - J`, `Λ₁sw + (3/2) J`), in
`SmoothedPolygons/Ch14/AnalyticExtension.lean`, which imports this file.
-/

@[expose] public section

open Filter Topology Asymptotics

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

/-! ### Division by the first coordinate of a function vanishing on the hyperplane -/

/-- The projection `(r, y) ↦ (0, y)` onto the hyperplane `{r = 0}`. -/
private noncomputable def l6a_proj : ℝ × E →L[ℝ] ℝ × E :=
  (ContinuousLinearMap.inr ℝ ℝ E).comp (ContinuousLinearMap.snd ℝ ℝ E)

private lemma l6a_proj_apply (h : ℝ × E) : l6a_proj h = ((0 : ℝ), h.2) := rfl

private lemma l6a_norm_proj_le : ‖(l6a_proj : ℝ × E →L[ℝ] ℝ × E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h ↦ by
    rw [l6a_proj_apply, one_mul, Prod.norm_mk, norm_zero]
    exact max_le ((norm_nonneg _).trans (norm_snd_le h)) (norm_snd_le h)

omit [CompleteSpace F] in
/-- The `i`-th term of the quotient by the first coordinate of an `(n + 1)`-linear map `P`: the
`n`-linear map `m ↦ P (π m₀, …, π m_{i-1}, e₁, m_i, …, m_{n-1})`, with `e₁ = (1, 0)` in the `i`-th
slot and the projection `π = l6a_proj` on the slots before it. -/
private noncomputable def l6a_divTerm {n : ℕ}
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) ↦ ℝ × E) F) (i : Fin (n + 1)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ ℝ × E) F :=
  (P.curryMid i ((1 : ℝ), (0 : E))).compContinuousLinearMap fun j ↦
    if j.castSucc < i then l6a_proj else ContinuousLinearMap.id ℝ (ℝ × E)

omit [CompleteSpace F] in
private lemma l6a_norm_divTerm_le {n : ℕ}
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) ↦ ℝ × E) F) (i : Fin (n + 1)) :
    ‖l6a_divTerm P i‖ ≤ ‖P‖ := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ‖P.curryMid i ((1 : ℝ), (0 : E))‖ ≤ ‖P‖ := by
    refine ((P.curryMid i).le_opNorm _).trans ?_
    simp
  have h2 : ∏ j : Fin n,
      ‖(if j.castSucc < i then l6a_proj else ContinuousLinearMap.id ℝ (ℝ × E))‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ ↦ norm_nonneg _) fun j _ ↦ by
      split_ifs
      · exact l6a_norm_proj_le
      · exact ContinuousLinearMap.norm_id_le
  calc _ ≤ ‖P‖ * 1 := mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
    _ = ‖P‖ := mul_one _

omit [CompleteSpace F] in
/-- **Telescoping.** `r • Σ_i (l6a_divTerm P i) (h, …, h) = P (h, …, h) - P (π h, …, π h)`
for `h = (r, y)`: the `i`-th term replaces the `i`-th copy of `h` by `π h`, since
`h - π h = r • e₁`. -/
private lemma l6a_smul_sum_divTerm {n : ℕ}
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) ↦ ℝ × E) F) (h : ℝ × E) :
    h.1 • ∑ i : Fin (n + 1), l6a_divTerm P i (fun _ ↦ h) =
      P (fun _ ↦ h) - P (fun _ ↦ l6a_proj h) := by
  classical
  -- `v k` has `π h` in the slots `< k` and `h` in the others.
  set v : ℕ → Fin (n + 1) → ℝ × E := fun k j ↦ if (j : ℕ) < k then l6a_proj h else h with hv
  have hterm : ∀ i : Fin (n + 1),
      h.1 • l6a_divTerm P i (fun _ ↦ h) = P (v i) - P (v (i + 1)) := by
    intro i
    have hins : (i.insertNth ((1 : ℝ), (0 : E)) fun j : Fin n ↦
        (if j.castSucc < i then l6a_proj else ContinuousLinearMap.id ℝ (ℝ × E)) h) =
        Function.update (v i) i ((1 : ℝ), (0 : E)) := by
      funext j
      rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
      · simp
      · rw [Fin.insertNth_apply_succAbove, Function.update_of_ne (Fin.succAbove_ne i j)]
        have hiff : ((i.succAbove j : ℕ) < (i : ℕ)) ↔ j.castSucc < i := by
          rw [← Fin.lt_def, Fin.succAbove_lt_iff_castSucc_lt]
        simp only [hv, hiff]
        split_ifs <;> rfl
    have h1 : h.1 • ((1 : ℝ), (0 : E)) = h - l6a_proj h := by
      ext <;> simp [l6a_proj_apply]
    have h2 : Function.update (v i) i h = v i := by
      rw [Function.update_eq_self_iff]
      simp [hv]
    have h3 : Function.update (v i) i (l6a_proj h) = v (i + 1) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hv]
      · rw [Function.update_of_ne hj]
        have hj' : (j : ℕ) ≠ i := fun h' ↦ hj (Fin.ext h')
        have hiff : (j : ℕ) < i ↔ (j : ℕ) < i + 1 := by omega
        simp only [hv, hiff]
    simp only [l6a_divTerm, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.curryMid_apply]
    rw [hins, ← ContinuousMultilinearMap.map_update_smul, h1,
      ContinuousMultilinearMap.map_update_sub, h2, h3]
  rw [Finset.smul_sum]
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ P (v k) - P (v (k + 1))), Finset.sum_range_sub']
  have hv0 : v 0 = fun _ ↦ h := by funext j; simp [hv]
  have hvn : v (n + 1) = fun _ ↦ l6a_proj h := by funext j; simp [hv, j.isLt]
  rw [hv0, hvn]

omit [CompleteSpace F] in
/-- The quotient series: `(l6a_divSeries p) n = Σ_i l6a_divTerm (p (n + 1)) i`. -/
private noncomputable def l6a_divSeries (p : FormalMultilinearSeries ℝ (ℝ × E) F) :
    FormalMultilinearSeries ℝ (ℝ × E) F :=
  fun n ↦ ∑ i : Fin (n + 1), l6a_divTerm (p (n + 1)) i

omit [CompleteSpace F] in
private lemma l6a_norm_divSeries_le (p : FormalMultilinearSeries ℝ (ℝ × E) F) (n : ℕ) :
    ‖l6a_divSeries p n‖ ≤ (n + 1) * ‖p (n + 1)‖ := by
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ ↦ l6a_norm_divTerm_le (p (n + 1)) i).trans ?_
  simp

omit [CompleteSpace F] in
/-- The quotient series has a positive radius of convergence (at least half of any radius of
`p`, since `n + 1 ≤ 2 ^ n`). -/
private lemma l6a_le_radius_divSeries (p : FormalMultilinearSeries ℝ (ℝ × E) F) {t : NNReal}
    (ht0 : 0 < t) (ht : (t : ENNReal) < p.radius) :
    ((t / 2 : NNReal) : ENNReal) ≤ (l6a_divSeries p).radius := by
  obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius ht
  have ht0' : (0 : ℝ) < t := ht0
  refine (l6a_divSeries p).le_radius_of_bound (C / t) fun n ↦ ?_
  have h1 := l6a_norm_divSeries_le p n
  have h2 : ((n : ℝ) + 1) ≤ 2 ^ n := by exact_mod_cast n.lt_two_pow_self
  have h3 := hC (n + 1)
  have h4 : 0 ≤ ‖p (n + 1)‖ * (t : ℝ) ^ (n + 1) := by positivity
  rw [le_div_iff₀ ht0', NNReal.coe_div, NNReal.coe_two, div_pow]
  calc ‖l6a_divSeries p n‖ * ((t : ℝ) ^ n / 2 ^ n) * t
      ≤ ((n + 1) * ‖p (n + 1)‖) * ((t : ℝ) ^ n / 2 ^ n) * t := by gcongr
    _ = ((n + 1) / 2 ^ n) * (‖p (n + 1)‖ * (t : ℝ) ^ (n + 1)) := by
        field_simp
        ring
    _ ≤ 1 * C := by
        gcongr
        · exact (div_le_one (by positivity)).2 h2
    _ = C := one_mul C

/-- **Division by the first coordinate.** If `f` is analytic at `(0, y₀)` and vanishes on the
hyperplane `{r = 0}` near `(0, y₀)`, then `f (r, y) = r • g (r, y)` near `(0, y₀)` with `g`
analytic at `(0, y₀)`: `g` is the sum of the quotient series `l6a_divSeries p` of the power
series `p` of `f`, termwise `r • (l6a_divSeries p) n (h, …, h) = p (n + 1) (h, …, h) -
p (n + 1) (π h, …, π h)` (`l6a_smul_sum_divTerm`), and `Σ_n p n (π h, …, π h) = f (0, y) = 0`. -/
private lemma l6a_exists_eq_smul {f : ℝ × E → F} {y₀ : E} (hf : AnalyticAt ℝ f ((0 : ℝ), y₀))
    (h0 : ∀ᶠ y in 𝓝 y₀, f ((0 : ℝ), y) = 0) :
    ∃ g : ℝ × E → F, AnalyticAt ℝ g ((0 : ℝ), y₀) ∧
      ∀ᶠ x in 𝓝 ((0 : ℝ), y₀), f x = x.1 • g x := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨t, ht0, htR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.radius_pos
  have ht0' : 0 < t := ENNReal.coe_pos.1 ht0
  have hqr := l6a_le_radius_divSeries p ht0' htR
  have hq0 : 0 < (l6a_divSeries p).radius :=
    lt_of_lt_of_le (ENNReal.coe_pos.2 (half_pos ht0')) hqr
  refine ⟨fun x ↦ (l6a_divSeries p).sum (x - ((0 : ℝ), y₀)), ?_, ?_⟩
  · have h := ((l6a_divSeries p).hasFPowerSeriesOnBall hq0).comp_sub ((0 : ℝ), y₀)
    rw [zero_add] at h
    exact h.analyticAt
  · have hρ : (0 : ENNReal) < min R ((t / 2 : NNReal) : ENNReal) :=
      lt_min hp.r_pos (ENNReal.coe_pos.2 (half_pos ht0'))
    have h0' : ∀ᶠ x in 𝓝 ((0 : ℝ), y₀), f ((0 : ℝ), x.2) = 0 :=
      (continuous_snd.tendsto' ((0 : ℝ), y₀) y₀ rfl).eventually h0
    filter_upwards [Metric.eball_mem_nhds _ hρ, h0'] with x hx hx0
    rw [Metric.mem_eball, lt_min_iff] at hx
    set h := x - ((0 : ℝ), y₀) with hh
    have hedist : edist h 0 = edist x ((0 : ℝ), y₀) := by
      rw [edist_zero_right, edist_eq_enorm_sub]
    have hπ : edist (l6a_proj h) 0 ≤ edist h 0 := by
      rw [edist_zero_right, edist_zero_right, enorm_le_iff_norm_le]
      calc ‖l6a_proj h‖ ≤ ‖(l6a_proj : ℝ × E →L[ℝ] ℝ × E)‖ * ‖h‖ := l6a_proj.le_opNorm h
        _ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right l6a_norm_proj_le (norm_nonneg h)
        _ = ‖h‖ := one_mul _
    have hhR : h ∈ Metric.eball (0 : ℝ × E) R := by
      rw [Metric.mem_eball, hedist]; exact hx.1
    have hhq : h ∈ Metric.eball (0 : ℝ × E) (l6a_divSeries p).radius := by
      rw [Metric.mem_eball, hedist]; exact hx.2.trans_le hqr
    have hπR : l6a_proj h ∈ Metric.eball (0 : ℝ × E) R := by
      rw [Metric.mem_eball]; exact hπ.trans_lt (Metric.mem_eball.1 hhR)
    have hs1 := hp.hasSum hhR
    have hs2 := hp.hasSum hπR
    have hs3 := ((l6a_divSeries p).hasSum hhq).const_smul h.1
    have hsum := (hasSum_nat_add_iff' 1).2 (hs1.sub hs2)
    have heq : (fun n ↦ h.1 • (l6a_divSeries p n) fun _ ↦ h) =
        fun n ↦ p (n + 1) (fun _ ↦ h) - p (n + 1) (fun _ ↦ l6a_proj h) := by
      funext n
      rw [← l6a_smul_sum_divTerm]
      simp [l6a_divSeries]
    rw [heq] at hs3
    have hx1 : ((0 : ℝ), y₀) + h = x := by rw [hh, add_sub_cancel]
    have hx2 : ((0 : ℝ), y₀) + l6a_proj h = ((0 : ℝ), x.2) := by
      ext <;> simp [l6a_proj_apply, hh]
    have hp0 : p 0 (fun _ ↦ h) = p 0 (fun _ ↦ l6a_proj h) :=
      congrArg (p 0) (funext fun i ↦ Fin.elim0 i)
    have h1 : h.1 = x.1 := by simp [hh]
    rw [hx1, hx2, hx0, Finset.sum_range_one, hp0, sub_self, sub_zero, sub_zero] at hsum
    rw [← h1]
    exact (hs3.unique hsum).symm

omit [CompleteSpace F] in
/-- If `φ (r) = r • ψ (r)` near `0`, with `ψ` continuous at `0`, and `φ = O(r ^ (k + 1))`, then
`ψ = O(r ^ k)` (at `r = 0` by continuity). -/
private lemma l6a_isBigO_of_eq_smul {φ ψ : ℝ → F} {k : ℕ} (hψ : ContinuousAt ψ 0)
    (hφψ : ∀ᶠ r in 𝓝 0, φ r = r • ψ r) (hφ : φ =O[𝓝 0] fun r ↦ r ^ (k + 1)) :
    ψ =O[𝓝 0] fun r ↦ r ^ k := by
  obtain ⟨c, hc⟩ := hφ.bound
  have hne : ∀ᶠ r in 𝓝 (0 : ℝ), r ≠ 0 → ‖ψ r‖ ≤ c * ‖r ^ k‖ := by
    filter_upwards [hc, hφψ] with r h1 h2 hr
    rw [h2, norm_smul, norm_pow, pow_succ'] at h1
    rw [norm_pow]
    have hr' : 0 < ‖r‖ := norm_pos_iff.2 hr
    have h3 : ‖r‖ * ‖ψ r‖ ≤ ‖r‖ * (c * ‖r‖ ^ k) := by linarith
    exact le_of_mul_le_mul_left h3 hr'
  have h0 : ‖ψ 0‖ ≤ c * ‖(0 : ℝ) ^ k‖ := by
    have hlim1 : Tendsto (fun r ↦ ‖ψ r‖) (𝓝[≠] 0) (𝓝 ‖ψ 0‖) :=
      hψ.norm.tendsto.mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto (fun r : ℝ ↦ c * ‖r ^ k‖) (𝓝[≠] 0) (𝓝 (c * ‖(0 : ℝ) ^ k‖)) :=
      ((by fun_prop : Continuous fun r : ℝ ↦ c * ‖r ^ k‖).tendsto 0).mono_left
        nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto hlim1 hlim2
      (eventually_nhdsWithin_iff.2 (hne.mono fun r h hr ↦ h hr))
  refine IsBigO.of_bound c (hne.mono fun r h ↦ ?_)
  by_cases hr : r = 0
  · subst hr
    exact h0
  · exact h hr

/-- **Division by a power of a coordinate.** If `f : ℝ × E → F` (`F` complete) is analytic at
`(0, y₀)` and, for all `y` near `y₀`, `f (r, y) = O(r^k)` as `r → 0`, then
`f (r, y) = r^k • g (r, y)` near `(0, y₀)` for some `g` analytic at `(0, y₀)`. Completeness of
`F` is needed: the coefficient series `Σ_{j ≥ k} a_j(y) r^{j-k}` must converge in `F` (without
it the statement fails: `f(r, y) = Σ_{j≥1} r^j γ_j(y)`, `γ_j(y) = Σ_m y^m e_{jm}/m!`, with values
in the span `F ⊆ ℓ²(ℕ × ℕ)` of the `e_{jm}` and the values of `f`, is analytic and `O(r)`, but
`g(0, y) = γ₁(y) ∉ F` for `y ≠ 0`). All the uses are `ℝ`- or `ℂ³`-valued. -/
theorem AnalyticAt.exists_eq_pow_smul_of_isBigO {f : ℝ × E → F} {y₀ : E}
    (hf : AnalyticAt ℝ f ((0 : ℝ), y₀)) {k : ℕ}
    (hk : ∀ᶠ y in 𝓝 y₀, (fun r : ℝ ↦ f (r, y)) =O[𝓝 0] (fun r ↦ r ^ k)) :
    ∃ g : ℝ × E → F, AnalyticAt ℝ g ((0 : ℝ), y₀) ∧
      ∀ᶠ p in 𝓝 ((0 : ℝ), y₀), f p = p.1 ^ k • g p := by
  induction k generalizing f with
  | zero => exact ⟨f, hf, Eventually.of_forall fun p ↦ by simp⟩
  | succ k ih =>
    -- `f` vanishes on the hyperplane, so `f = r • g₁` with `g₁` analytic.
    have h0 : ∀ᶠ y in 𝓝 y₀, f ((0 : ℝ), y) = 0 :=
      hk.mono fun y hy ↦ hy.eq_zero_imp.self_of_nhds (by simp)
    obtain ⟨g₁, hg₁, hfg⟩ := l6a_exists_eq_smul hf h0
    -- `g₁ (·, y) = O(r ^ k)` for `y` near `y₀`.
    have hfg' := hfg
    rw [nhds_prod_eq] at hfg'
    obtain ⟨pa, hpa, pb, hpb, hpab⟩ := Filter.eventually_prod_iff.1 hfg'
    have han : ∀ᶠ y in 𝓝 y₀, AnalyticAt ℝ g₁ ((0 : ℝ), y) :=
      (Continuous.tendsto' (by fun_prop : Continuous fun y : E ↦ ((0 : ℝ), y)) y₀ _ rfl).eventually
        hg₁.eventually_analyticAt
    have hk' : ∀ᶠ y in 𝓝 y₀, (fun r : ℝ ↦ g₁ (r, y)) =O[𝓝 0] (fun r ↦ r ^ k) := by
      filter_upwards [hk, hpb, han] with y hy hyb hya
      refine l6a_isBigO_of_eq_smul ?_ (hpa.mono fun r hr ↦ hpab hr hyb) hy
      exact hya.continuousAt.comp (f := fun r : ℝ ↦ (r, y)) (by fun_prop)
    -- Induction.
    obtain ⟨g, hg, hg₁g⟩ := ih hg₁ hk'
    refine ⟨g, hg, ?_⟩
    filter_upwards [hfg, hg₁g] with x h1 h2
    rw [h1, h2, smul_smul, pow_succ']
