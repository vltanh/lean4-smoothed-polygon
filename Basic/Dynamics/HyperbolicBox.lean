module

public import Basic.Dynamics.LinearizedStability
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# An isolating box at a fixed point with an invariant hyperplane and a transverse expansion

Let `F : ℝ × E → ℝ × E` fix `p₀ = (0, x₀)`, leave the hyperplane `{r = 0}` invariant near `p₀`,
expand in the transverse direction (`∂(F.1)/∂r (p₀) > 1`) and contract along the hyperplane (the
derivative of `x ↦ F(0, x).2` at `x₀` has all its complex eigenvalues of modulus `< 1`). Then a
sequence `pₙ` with `rₙ > 0`, `rₙ → 0`, which follows `F` near `p₀` (`p (n + 1) = F (p n)` whenever
`p n` is close to `p₀`), does not have `p₀` as a cluster point: each visit close to `p₀` with
small `r` is followed by a time at which `r` exceeds a fixed `δ > 0`, because `r` grows
geometrically while the hyperplane coordinate stays near `x₀`.

This is the "hyperbolic box" (isolating block) argument that replaces the `ε` versus
`ε/r_scale` argument of the proof of Theorem 16.4.1 in Hales–Vajjha, *Packings of Smoothed
Polygons* (TeX 13002–13026: "we claim that `q_out` is not a cluster point"); it uses the
derivative at the fixed point only (strict differentiability), not the stable manifold theorem.

## Proof

Write `F (r, x) = (r m(r, x), G(r, x))` near `p₀`. Strict differentiability at `p₀` and the
invariance `F.1(0, x) = 0` give `F.1(r, x) ≥ λ r` for `r ≥ 0` near `p₀`, with some `λ > 1`, and
`G(r, x) - x₀ = A(x - x₀) + r b + o(|r| + ‖x - x₀‖)` with `A` the hyperplane part of the
derivative and `b = (F'(1, 0)).2` (`l6a_eventually_estimates`). By
`ContinuousLinearMap.exists_norm_pow_lt_one`, `‖A ^ N‖ < 1` for some `N ≥ 1`, and
`V v = Σ_{j<N} ‖A^j v‖` is a Lyapunov function: `V (A v) ≤ V v - c ‖v‖` with `c > 0`
(`l6a_exists_lyapunov`). The decrease `c ‖x - x₀‖` absorbs the `o(‖x - x₀‖)` error, so near `p₀`,
for `r ≥ 0`: `r_{k+1} ≥ λ r_k` and `V (x_{k+1} - x₀) ≤ V (x_k - x₀) + C r_k`. Hence the
invariant `V (x_k - x₀) ≤ η/2 + K r_k`, `K (λ - 1) ≥ C`, propagates as long as `r_k < δ`, and it
keeps the orbit in a box `{0 < r < δ, V (x - x₀) ≤ η}` inside `W` (`K δ ≤ η/2`), where the orbit
follows `F`. Once `rₙ < δ` for all `n ≥ N₀`, a visit at a time `n ≥ N₀` to a small ball around
`p₀` (given by the cluster point) yields `λ^k rₙ ≤ r_{n+k} < δ` for every `k`: absurd.

This simplifies the plan of the layer-6 statements (an adapted norm `Σ_{j<N} θ^{-j} ‖A^j v‖` in
which `A` contracts, and the geometric series `Σ (κ'/λ)^j`): the linear invariant
`V ≤ η/2 + K r` replaces the summation, and no contraction rate is needed beyond `c > 0`.
-/

@[expose] public section

open Filter Topology Set

namespace Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A Lyapunov function for an operator with a contracting power. If `‖A ^ N‖ < 1` with `N ≥ 1`,
then `V v = Σ_{j<N} ‖A^j v‖` is subadditive, absolutely homogeneous, comparable to the norm
(`‖v‖ ≤ V v ≤ M ‖v‖`) and strictly decreasing along `A`: `V (A v) + c ‖v‖ ≤ V v` with
`c = 1 - ‖A ^ N‖ > 0`. (This is the adapted norm of the plan, with the weights `θ^{-j}` replaced
by `1`: only the decrease `V (A v) ≤ V v - c ‖v‖` is used.) -/
private lemma l6a_exists_lyapunov (A : E →L[ℝ] E) {N : ℕ} (hN0 : 0 < N) (hN : ‖A ^ N‖ < 1) :
    ∃ (V : E → ℝ) (M c : ℝ), 0 < c ∧ 0 ≤ M ∧ (∀ v, ‖v‖ ≤ V v) ∧ (∀ v, V v ≤ M * ‖v‖) ∧
      (∀ v w, V (v + w) ≤ V v + V w) ∧ (∀ (t : ℝ) v, V (t • v) = |t| * V v) ∧
      ∀ v, V (A v) + c * ‖v‖ ≤ V v := by
  refine ⟨fun v ↦ ∑ j ∈ Finset.range N, ‖(A ^ j) v‖, ∑ j ∈ Finset.range N, ‖A ^ j‖,
    1 - ‖A ^ N‖, by linarith, Finset.sum_nonneg fun j _ ↦ norm_nonneg _, fun v ↦ ?_, fun v ↦ ?_,
    fun v w ↦ ?_, fun t v ↦ ?_, fun v ↦ ?_⟩
  · simpa using Finset.single_le_sum (f := fun j ↦ ‖(A ^ j) v‖) (fun j _ ↦ norm_nonneg _)
      (Finset.mem_range.2 hN0)
  · rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ ↦ (A ^ j).le_opNorm v
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ ↦ by rw [map_add]; exact norm_add_le _ _
  · simp only [map_smul, norm_smul, Real.norm_eq_abs, Finset.mul_sum]
  · have h : ∀ j, (A ^ j) (A v) = (A ^ (j + 1)) v := fun j ↦ by
      rw [pow_succ]; rfl
    have hs := Finset.sum_range_succ' (fun j ↦ ‖(A ^ j) v‖) N
    rw [Finset.sum_range_succ] at hs
    simp only [pow_zero, one_apply_eq_self] at hs
    have hAN : ‖(A ^ N) v‖ ≤ ‖A ^ N‖ * ‖v‖ := (A ^ N).le_opNorm v
    simp only [h]
    linarith

omit [FiniteDimensional ℝ E] in
/-- The two first-order estimates at the fixed point: the strict derivative compares `F z` with
`F (0, z.2)` (the point of the hyperplane below `z`), and the derivative compares `F z` with
`F (0, x₀)`. -/
private lemma l6a_eventually_estimates {F : ℝ × E → ℝ × E} {F' : (ℝ × E) →L[ℝ] ℝ × E} {x₀ : E}
    (hF : HasStrictFDerivAt F F' ((0 : ℝ), x₀)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 ((0 : ℝ), x₀),
      ‖F z - F ((0 : ℝ), z.2) - z.1 • F' ((1 : ℝ), (0 : E))‖ ≤ ε * |z.1| ∧
      ‖F z - F ((0 : ℝ), x₀) - F' (z - ((0 : ℝ), x₀))‖ ≤ ε * ‖z - ((0 : ℝ), x₀)‖ := by
  have hs := (hasStrictFDerivAt_iff_isLittleO.1 hF).def hε
  have hT : Tendsto (fun z : ℝ × E ↦ (z, ((0 : ℝ), z.2))) (𝓝 ((0 : ℝ), x₀))
      (𝓝 (((0 : ℝ), x₀), ((0 : ℝ), x₀))) :=
    Continuous.tendsto' (by fun_prop) _ _ rfl
  refine ((hT.eventually hs).and (hF.hasFDerivAt.isLittleO.def hε)).mono
    fun z ⟨h1, h2⟩ ↦ ⟨?_, h2⟩
  have hz : z - ((0 : ℝ), z.2) = z.1 • ((1 : ℝ), (0 : E)) := by ext <;> simp
  dsimp only at h1
  rw [hz, map_smul, norm_smul] at h1
  simpa using h1

/-- **No cluster point at a fixed point with an invariant hyperplane and transverse expansion.**
Let `F : ℝ × E → ℝ × E` be strictly differentiable at `p₀ = (0, x₀)` with derivative `F'`, fix
`p₀`, leave `{r = 0}` invariant near `p₀`, expand transversally (`(F' (1, 0)).1 > 1`) and contract
along the hyperplane (every complex eigenvalue of `v ↦ (F' (0, v)).2` has modulus `< 1`). Then,
for **every** neighborhood `W` of `p₀`, no sequence `p` with `(p n).1 → 0` which, at every `n` with
`p n ∈ W`, has `(p n).1 > 0` and `p (n + 1) = F (p n)`, has `p₀` as a cluster point. (The box
argument uses only a small box inside `W`, so `W` may be any neighborhood: in applications it is
the neighborhood on which the sequence is known to follow `F`.)

Proof: the box argument of the module docstring, with the adapted norm replaced by the Lyapunov
function `V` of `l6a_exists_lyapunov` (`V (A v) ≤ V v - c ‖v‖`). On a ball `B(p₀, ρ) ⊆ W`,
`F.1 (r, x) ≥ λ r` (`λ > 1`) and `V (F.2 (r, x) - x₀) ≤ V (x - x₀) + C r` for `r ≥ 0`: the
decrease of `V` along `A` absorbs the error term of the derivative. Hence the invariant
`V (x - x₀) ≤ η/2 + K r`, `K (λ - 1) = C`, is preserved while `r < δ`, and keeps the orbit in
the box `{0 < r < δ, V (x - x₀) ≤ η} ⊆ B(p₀, ρ)`, on which `r` grows by the factor `λ`. A visit
to a small ball around `p₀` after the time from which `r < δ` therefore gives `λ^k r ≤ δ` for
all `k`, which is absurd. -/
theorem not_mapClusterPt_of_transverse_expansion {F : ℝ × E → ℝ × E}
    {F' : (ℝ × E) →L[ℝ] ℝ × E} {x₀ : E} (hF : HasStrictFDerivAt F F' ((0 : ℝ), x₀))
    (hfix : F ((0 : ℝ), x₀) = ((0 : ℝ), x₀))
    (hinv : ∀ᶠ x in 𝓝 x₀, (F ((0 : ℝ), x)).1 = 0) (hexp : 1 < (F' ((1 : ℝ), (0 : E))).1)
    (hcontr : ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly
      ((ContinuousLinearMap.snd ℝ ℝ E ∘L F' ∘L ContinuousLinearMap.inr ℝ ℝ E :
        E →L[ℝ] E) : E →ₗ[ℝ] E)) = 0 → ‖μ‖ < 1) :
    ∀ W ∈ 𝓝 ((0 : ℝ), x₀), ∀ p : ℕ → ℝ × E, Tendsto (fun n ↦ (p n).1) atTop (𝓝 0) →
      (∀ n, p n ∈ W → 0 < (p n).1 ∧ p (n + 1) = F (p n)) →
        ¬ MapClusterPt ((0 : ℝ), x₀) atTop p := by
  intro W hW p hp hfollow hcl
  -- The hyperplane part `A` of the derivative and its Lyapunov function `V`.
  obtain ⟨A, hAdef⟩ : ∃ A : E →L[ℝ] E,
      A = ContinuousLinearMap.snd ℝ ℝ E ∘L F' ∘L ContinuousLinearMap.inr ℝ ℝ E := ⟨_, rfl⟩
  rw [← hAdef] at hcontr
  have hAy : ∀ y, A y = (F' ((0 : ℝ), y)).2 := fun y ↦ by rw [hAdef]; rfl
  obtain ⟨N, hN0, hN⟩ := A.exists_norm_pow_lt_one hcontr
  obtain ⟨V, M, c, hc, hM, hVge, hVle, hVadd, hVsmul, hVA⟩ := l6a_exists_lyapunov A hN0 hN
  have hV0 : ∀ v, 0 ≤ V v := fun v ↦ (norm_nonneg v).trans (hVge v)
  -- The constants: the expansion rate `λ`, the error `ε`, the slope `K` of the invariant.
  obtain ⟨lam, hlam1, hlama⟩ : ∃ lam : ℝ, 1 < lam ∧ lam < (F' ((1 : ℝ), (0 : E))).1 :=
    ⟨(1 + (F' ((1 : ℝ), (0 : E))).1) / 2, by linarith, by linarith⟩
  obtain ⟨ε, hε0, hεa, hMε⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ (F' ((1 : ℝ), (0 : E))).1 - lam ∧
      M * ε ≤ c := by
    refine ⟨min ((F' ((1 : ℝ), (0 : E))).1 - lam) (c / (M + 1)),
      lt_min (by linarith) (by positivity), min_le_left _ _, ?_⟩
    calc M * min ((F' ((1 : ℝ), (0 : E))).1 - lam) (c / (M + 1))
        ≤ M * (c / (M + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hM
      _ ≤ c := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith
  obtain ⟨K, hK0, hKC⟩ : ∃ K : ℝ, 0 ≤ K ∧ K + (V (F' ((1 : ℝ), (0 : E))).2 + c) ≤ K * lam := by
    refine ⟨(V (F' ((1 : ℝ), (0 : E))).2 + c) / (lam - 1),
      div_nonneg (by linarith [hV0 (F' ((1 : ℝ), (0 : E))).2]) (by linarith), ?_⟩
    have h := div_mul_cancel₀ (V (F' ((1 : ℝ), (0 : E))).2 + c) (by linarith : lam - 1 ≠ 0)
    nlinarith
  -- A ball around `p₀` inside `W` on which the first-order estimates hold.
  have hev : ∀ᶠ z in 𝓝 ((0 : ℝ), x₀), z ∈ W ∧ (F ((0 : ℝ), z.2)).1 = 0 ∧
      ‖F z - F ((0 : ℝ), z.2) - z.1 • F' ((1 : ℝ), (0 : E))‖ ≤ ε * |z.1| ∧
      ‖F z - F ((0 : ℝ), x₀) - F' (z - ((0 : ℝ), x₀))‖ ≤ ε * ‖z - ((0 : ℝ), x₀)‖ := by
    have hinv' : ∀ᶠ z in 𝓝 ((0 : ℝ), x₀), (F ((0 : ℝ), z.2)).1 = 0 :=
      (continuous_snd.tendsto' ((0 : ℝ), x₀) x₀ rfl).eventually hinv
    have hW' : ∀ᶠ z in 𝓝 ((0 : ℝ), x₀), z ∈ W := hW
    exact hW'.and (hinv'.and (l6a_eventually_estimates hF hε0))
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  -- One step of `F` on the ball: `r` grows by `λ`, `V (x - x₀)` grows by at most `C r`.
  have hstep : ∀ z ∈ Metric.ball ((0 : ℝ), x₀) ρ, 0 ≤ z.1 →
      lam * z.1 ≤ (F z).1 ∧
        V ((F z).2 - x₀) ≤ V (z.2 - x₀) + (V (F' ((1 : ℝ), (0 : E))).2 + c) * z.1 := by
    intro z hz hz1
    obtain ⟨-, h0, h1, h2⟩ := hball z hz
    constructor
    · have h := (norm_fst_le _).trans h1
      simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul, h0, Real.norm_eq_abs,
        abs_of_nonneg hz1, sub_zero] at h
      have h' := (abs_le.1 h).1
      nlinarith
    · have hd : F' (z - ((0 : ℝ), x₀)) =
          z.1 • F' ((1 : ℝ), (0 : E)) + F' ((0 : ℝ), z.2 - x₀) := by
        rw [← map_smul, ← map_add]
        congr 1
        ext <;> simp
      have hw2 : (F z).2 - x₀ = A (z.2 - x₀) + (z.1 • (F' ((1 : ℝ), (0 : E))).2 +
          (F z - F ((0 : ℝ), x₀) - F' (z - ((0 : ℝ), x₀))).2) := by
        rw [hd, hAy, hfix]
        simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd]
        abel
      have hwn : ‖(F z - F ((0 : ℝ), x₀) - F' (z - ((0 : ℝ), x₀))).2‖ ≤
          ε * (z.1 + ‖z.2 - x₀‖) := by
        refine (norm_snd_le _).trans (h2.trans ?_)
        gcongr
        rw [Prod.norm_def]
        simp only [Prod.fst_sub, Prod.snd_sub, sub_zero, Real.norm_eq_abs, abs_of_nonneg hz1]
        exact max_le (by linarith [norm_nonneg (z.2 - x₀)]) (by linarith)
      have hA := hVA (z.2 - x₀)
      have hb := hVsmul z.1 (F' ((1 : ℝ), (0 : E))).2
      have hw := hVle (F z - F ((0 : ℝ), x₀) - F' (z - ((0 : ℝ), x₀))).2
      have hMw := mul_le_mul_of_nonneg_left hwn hM
      have h3 := mul_le_mul_of_nonneg_right hMε hz1
      have h4 := mul_le_mul_of_nonneg_right hMε (norm_nonneg (z.2 - x₀))
      rw [abs_of_nonneg hz1] at hb
      rw [hw2]
      refine (hVadd _ _).trans ?_
      have h5 := hVadd (z.1 • (F' ((1 : ℝ), (0 : E))).2)
        (F z - F ((0 : ℝ), x₀) - F' (z - ((0 : ℝ), x₀))).2
      nlinarith
  -- The box: radius `δ` in `r`, `η` in `V (x - x₀)`; the starting ball has radius `σ`.
  obtain ⟨η, hη, hηρ⟩ : ∃ η : ℝ, 0 < η ∧ η < ρ := ⟨ρ / 2, by positivity, by linarith⟩
  obtain ⟨δ, hδ, hδρ, hKδ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < ρ ∧ K * δ ≤ η / 2 := by
    refine ⟨η / (2 * (K + 1)), by positivity, ?_, ?_⟩
    · rw [div_lt_iff₀ (by positivity)]
      nlinarith
    · rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
  obtain ⟨σ, hσ, hσδ, hσM⟩ : ∃ σ : ℝ, 0 < σ ∧ σ ≤ δ ∧ M * σ ≤ η / 2 := by
    refine ⟨min δ (η / (2 * (M + 1))), lt_min hδ (by positivity), min_le_left _ _, ?_⟩
    calc M * min δ (η / (2 * (M + 1))) ≤ M * (η / (2 * (M + 1))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hM
      _ ≤ η / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hbox : ∀ z : ℝ × E, 0 ≤ z.1 → z.1 < δ → V (z.2 - x₀) ≤ η →
      z ∈ Metric.ball ((0 : ℝ), x₀) ρ := by
    intro z h0 h1 h2
    rw [Metric.mem_ball, dist_eq_norm, Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, sub_zero, Real.norm_eq_abs, abs_of_nonneg h0]
    exact max_lt (by linarith) (by linarith [hVge (z.2 - x₀)])
  -- From some time on `r < δ`; the cluster point gives a later visit to the starting ball.
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hp.eventually (gt_mem_nhds hδ))
  obtain ⟨n, hn, hnS⟩ := frequently_atTop.1
    (mapClusterPt_iff_frequently.1 hcl _ (Metric.ball_mem_nhds _ hσ)) N₀
  have hnρ : p n ∈ Metric.ball ((0 : ℝ), x₀) ρ :=
    Metric.ball_subset_ball (by linarith) hnS
  have hrn : 0 < (p n).1 := (hfollow n (hball _ hnρ).1).1
  have hVn : V ((p n).2 - x₀) ≤ η / 2 := by
    have h : ‖(p n).2 - x₀‖ < σ := by
      have := (norm_snd_le (p n - ((0 : ℝ), x₀))).trans_lt
        (by rw [← dist_eq_norm]; exact hnS)
      simpa using this
    calc V ((p n).2 - x₀) ≤ M * ‖(p n).2 - x₀‖ := hVle _
      _ ≤ M * σ := mul_le_mul_of_nonneg_left h.le hM
      _ ≤ η / 2 := hσM
  -- The invariant: `r` grows geometrically and `V (x - x₀) ≤ η/2 + K r`.
  have hinvt : ∀ k : ℕ, lam ^ k * (p n).1 ≤ (p (n + k)).1 ∧
      V ((p (n + k)).2 - x₀) ≤ η / 2 + K * (p (n + k)).1 := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, one_mul, add_zero, le_refl, true_and]
      nlinarith [mul_nonneg hK0 hrn.le]
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hr0 : 0 < (p (n + k)).1 := lt_of_lt_of_le (by positivity) ih1
      have hrδ : (p (n + k)).1 < δ := hN₀ (n + k) (by omega)
      have hKr := mul_le_mul_of_nonneg_left hrδ.le hK0
      have hz : p (n + k) ∈ Metric.ball ((0 : ℝ), x₀) ρ :=
        hbox _ hr0.le hrδ (by linarith)
      have hnext : p (n + k + 1) = F (p (n + k)) := (hfollow (n + k) (hball _ hz).1).2
      obtain ⟨hs1, hs2⟩ := hstep _ hz hr0.le
      rw [← add_assoc, hnext]
      have h6 := mul_le_mul_of_nonneg_left ih1 (by linarith : (0 : ℝ) ≤ lam)
      have h7 := mul_le_mul_of_nonneg_right hKC hr0.le
      have h8 := mul_le_mul_of_nonneg_left hs1 hK0
      refine ⟨?_, ?_⟩
      · rw [pow_succ]
        nlinarith
      · nlinarith
  -- `λ^k r ≤ r_{n+k} < δ` for every `k`: absurd.
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlam1).eventually_gt_atTop
    (δ / (p n).1)).exists
  have h1 := (hinvt k).1
  have h2 := hN₀ (n + k) (by omega)
  rw [div_lt_iff₀ hrn] at hk
  linarith

end Function
