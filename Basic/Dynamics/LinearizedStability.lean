module

public import Basic.Dynamics.Stability
public import StableManifold.Linear.Spectral
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Linearized stability for maps

A fixed point `x₀` of a map `f : E → E` of a finite-dimensional real normed space, at which `f`
is differentiable with a derivative whose (complex) eigenvalues all have modulus `< 1`, is
asymptotically stable. This is the discrete-time form of Lyapunov's first method (Perron), used
without proof in Hales–Vajjha, *Packings of Smoothed Polygons*, Lemma 13.5.5 (TeX 11443–11453:
"An explicit calculation of the eigenvalues of the Jacobian matrix … gives the result").

The eigenvalues are the complex roots of the characteristic polynomial `LinearMap.charpoly` of the
derivative: a real operator may have non-real eigenvalues, and `spectrum ℝ` would miss them, so
the hypothesis is stated with `Polynomial.aeval μ` for `μ : ℂ`.

Mathlib has Gelfand's formula (`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`, in
the form `spectrum.spectralRadius_eq_gelfandRadius`) for complex Banach algebras and the chain rule
for iterates (`HasFDerivAt.iterate`), but no stability theorem for maps.

* `ContinuousLinearMap.exists_norm_pow_lt_one` (from the stable manifold package,
  `StableManifold.Linear.Spectral`): if every complex root of the characteristic polynomial of `A`
  has modulus `< 1`, then `‖A ^ N‖ < 1` for some `N ≥ 1`.
* `Function.isAsymptoticallyStable_of_hasFDerivAt`: linearized stability.
-/

@[expose] public section

open Filter Topology

namespace Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A map differentiable at a fixed point `x₀` with `‖f'‖ < c` satisfies
`‖f x - x₀‖ ≤ c ‖x - x₀‖` near `x₀`. -/
private lemma l4a_exists_norm_sub_le {f : E → E} {f' : E →L[ℝ] E} {x₀ : E} (hfix : f x₀ = x₀)
    (hf : HasFDerivAt f f' x₀) {c : ℝ} (hc : ‖f'‖ < c) :
    ∃ δ > 0, ∀ x, ‖x - x₀‖ < δ → ‖f x - x₀‖ ≤ c * ‖x - x₀‖ := by
  obtain ⟨δ, hδ, hδh⟩ := Metric.eventually_nhds_iff.1 (hf.isLittleO.def (sub_pos.2 hc))
  refine ⟨δ, hδ, fun x hx ↦ ?_⟩
  have h1 := @hδh x (by rwa [dist_eq_norm])
  rw [hfix] at h1
  calc ‖f x - x₀‖ = ‖(f x - x₀ - f' (x - x₀)) + f' (x - x₀)‖ := by rw [sub_add_cancel]
    _ ≤ ‖f x - x₀ - f' (x - x₀)‖ + ‖f' (x - x₀)‖ := norm_add_le _ _
    _ ≤ (c - ‖f'‖) * ‖x - x₀‖ + ‖f'‖ * ‖x - x₀‖ := add_le_add h1 (f'.le_opNorm _)
    _ = c * ‖x - x₀‖ := by ring

/-- **Linearized stability for maps.** Let `x₀` be a fixed point of `f : E → E` (`E` a
finite-dimensional real normed space) at which `f` has the derivative `f'`, and suppose that every
complex eigenvalue of `f'` has modulus `< 1`. Then `x₀` is an asymptotically stable fixed point of
`f`.

Proof route: by `ContinuousLinearMap.exists_norm_pow_lt_one`, `‖f' ^ N‖ < 1` for some `N ≥ 1`.
By the chain rule for iterates at a fixed point (`HasFDerivAt.iterate`), `f^[N]` has the
derivative `f' ^ N` at `x₀`, so there are `θ < 1` and `δ > 0` with
`‖f^[N] x - x₀‖ ≤ θ ‖x - x₀‖` on the ball `B(x₀, δ)`; differentiability of `f` at `x₀` gives
`‖f x - x₀‖ ≤ C ‖x - x₀‖` near `x₀`, which controls the intermediate iterates `f^[j]`, `j < N`.
Hence orbits starting close to `x₀` stay close (Lyapunov stability) and tend to `x₀` geometrically
(attraction). Only differentiability at the single point `x₀` is used. -/
theorem isAsymptoticallyStable_of_hasFDerivAt {f : E → E} {f' : E →L[ℝ] E} {x₀ : E}
    (hfix : IsFixedPt f x₀) (hf : HasFDerivAt f f' x₀)
    (hspec : ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly (f' : E →ₗ[ℝ] E)) = 0 → ‖μ‖ < 1) :
    IsAsymptoticallyStable f x₀ := by
  obtain ⟨N, hN0, hN⟩ := f'.exists_norm_pow_lt_one hspec
  -- `f^[N]` contracts by `θ < 1` near `x₀`, and `f` expands by at most `C ≥ 1` near `x₀`.
  set θ := (‖f' ^ N‖ + 1) / 2 with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by linarith
  have hθk : ∀ k : ℕ, θ ^ k ≤ 1 := fun k ↦ pow_le_one₀ hθ0.le hθ1.le
  obtain ⟨δ₁, hδ₁, h₁⟩ :=
    l4a_exists_norm_sub_le (hfix.iterate N) (hf.iterate hfix N) (c := θ) (by linarith)
  set C := ‖f'‖ + 1 with hCdef
  have hC1 : 1 ≤ C := by have := norm_nonneg f'; linarith
  obtain ⟨δ₂, hδ₂, h₂⟩ := l4a_exists_norm_sub_le hfix hf (c := C) (by linarith)
  set K := C ^ N with hK
  have hK1 : 1 ≤ K := one_le_pow₀ hC1
  have hK0 : 0 < K := by linarith
  -- The intermediate iterates `f^[j]`, `j ≤ N`.
  have hshort : ∀ y : E, K * ‖y - x₀‖ < δ₂ → ∀ j ≤ N, ‖f^[j] y - x₀‖ ≤ C ^ j * ‖y - x₀‖ := by
    intro y hy j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hj' := ih (by omega)
      have hlt : ‖f^[j] y - x₀‖ < δ₂ :=
        calc ‖f^[j] y - x₀‖ ≤ C ^ j * ‖y - x₀‖ := hj'
          _ ≤ K * ‖y - x₀‖ :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1 (by omega)) (norm_nonneg _)
          _ < δ₂ := hy
      rw [iterate_succ_apply']
      calc ‖f (f^[j] y) - x₀‖ ≤ C * ‖f^[j] y - x₀‖ := h₂ _ hlt
        _ ≤ C * (C ^ j * ‖y - x₀‖) := mul_le_mul_of_nonneg_left hj' (by linarith)
        _ = C ^ (j + 1) * ‖y - x₀‖ := by ring
  set δ := min δ₁ δ₂ / K with hδdef
  have hδ : 0 < δ := by positivity
  have hKδ : K * δ = min δ₁ δ₂ := by rw [hδdef]; field_simp
  -- Blocks of `N` steps contract by `θ`.
  have hblock : ∀ x : E, ‖x - x₀‖ < δ → ∀ k : ℕ, ‖f^[N * k] x - x₀‖ ≤ θ ^ k * ‖x - x₀‖ := by
    intro x hx k
    induction k with
    | zero => simp
    | succ k ih =>
      have hlt : ‖f^[N * k] x - x₀‖ < δ₁ :=
        calc ‖f^[N * k] x - x₀‖ ≤ θ ^ k * ‖x - x₀‖ := ih
          _ ≤ ‖x - x₀‖ := mul_le_of_le_one_left (norm_nonneg _) (hθk k)
          _ < δ := hx
          _ ≤ K * δ := le_mul_of_one_le_left hδ.le hK1
          _ = min δ₁ δ₂ := hKδ
          _ ≤ δ₁ := min_le_left _ _
      rw [Nat.mul_succ, add_comm, iterate_add_apply]
      calc ‖f^[N] (f^[N * k] x) - x₀‖ ≤ θ * ‖f^[N * k] x - x₀‖ := h₁ _ hlt
        _ ≤ θ * (θ ^ k * ‖x - x₀‖) := mul_le_mul_of_nonneg_left ih hθ0.le
        _ = θ ^ (k + 1) * ‖x - x₀‖ := by ring
  -- All iterates: `‖fⁿ x - x₀‖ ≤ K θ^⌊n/N⌋ ‖x - x₀‖`.
  have hall : ∀ x : E, ‖x - x₀‖ < δ → ∀ n : ℕ,
      ‖f^[n] x - x₀‖ ≤ K * θ ^ (n / N) * ‖x - x₀‖ := by
    intro x hx n
    have hy := hblock x hx (n / N)
    have hyδ : K * ‖f^[N * (n / N)] x - x₀‖ < δ₂ :=
      calc K * ‖f^[N * (n / N)] x - x₀‖ ≤ K * ‖x - x₀‖ :=
            mul_le_mul_of_nonneg_left
              (hy.trans (mul_le_of_le_one_left (norm_nonneg _) (hθk _))) hK0.le
        _ < K * δ := mul_lt_mul_of_pos_left hx hK0
        _ = min δ₁ δ₂ := hKδ
        _ ≤ δ₂ := min_le_right _ _
    have hn : f^[n] x = f^[n % N] (f^[N * (n / N)] x) := by
      rw [← iterate_add_apply, Nat.mod_add_div]
    have hmod : n % N ≤ N := (Nat.mod_lt _ hN0).le
    rw [hn]
    calc ‖f^[n % N] (f^[N * (n / N)] x) - x₀‖
        ≤ C ^ (n % N) * ‖f^[N * (n / N)] x - x₀‖ := hshort _ hyδ _ hmod
      _ ≤ K * ‖f^[N * (n / N)] x - x₀‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1 hmod) (norm_nonneg _)
      _ ≤ K * (θ ^ (n / N) * ‖x - x₀‖) := mul_le_mul_of_nonneg_left hy hK0.le
      _ = K * θ ^ (n / N) * ‖x - x₀‖ := by ring
  refine ⟨hfix, fun U hU ↦ ?_, ⟨Metric.ball x₀ δ, Metric.ball_mem_nhds _ hδ, fun x hx ↦ ?_⟩⟩
  · -- Lyapunov stability.
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
    refine ⟨Metric.ball x₀ (min δ (ε / K)), Metric.ball_mem_nhds _ (by positivity),
      fun x hx n ↦ hεU ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
    have hx1 : ‖x - x₀‖ < δ := hx.trans_le (min_le_left _ _)
    have hx2 : K * ‖x - x₀‖ < ε := by
      have := hx.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀ hK0, mul_comm] at this
    calc ‖f^[n] x - x₀‖ ≤ K * θ ^ (n / N) * ‖x - x₀‖ := hall x hx1 n
      _ ≤ K * 1 * ‖x - x₀‖ := by gcongr; exact hθk _
      _ < ε := by rwa [mul_one]
  · -- Attraction.
    rw [Metric.mem_ball, dist_eq_norm] at hx
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ hall x hx n) ?_
    have h : Tendsto (fun n : ℕ ↦ θ ^ (n / N)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1).comp
        (Nat.tendsto_div_const_atTop hN0.ne')
    simpa using (h.const_mul K).mul_const ‖x - x₀‖

end Function
