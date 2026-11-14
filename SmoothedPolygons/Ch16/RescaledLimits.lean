module

public import SmoothedPolygons.Ch16.RescaledDynamics
public import SmoothedPolygons.Ch16.RelaxedFuller

/-!
# Chapter 16: limits of rescaled Reinhardt arcs are relaxed Fuller extremals (§16.4.2, part 2)

The compactness step of the proof of N5 (`clusterSetForwardInvariant`,
`SmoothedPolygons/Ch16/ReinhardtShadowing.lean`). Along a chattering arc into the singular locus,
after the `n`-th switching time `τ_n`, with the radius `ρ_n = φ(ẑ(q_n))` of the switching point:

* `switchRadius n = ρ_n`, `rescaledArc n s = scale ρ_n⁻¹ ẑ(q(τ_n + s ρ_n))` (so
  `rescaledArc n 0 = ξ_n`, the angular component of the switching point), and
  `rescaledControl n s = simplexToUT (u(τ_n + s ρ_n))`, the rescaled control in `U_T`;
* `rescaledArc_eq_integral`: the rescaled arc solves the rescaled Reinhardt equation
  `y' = rescaledField ρ_n v(s) y` in integral form (the extremal equations of Problem 6.7.1,
  `fullerCoords` being `ℝ`-linear, and the change of variables `t = τ_n + s ρ_n`), as long as the
  window `[τ_n, τ_n + S ρ_n]` stays before `b`;
* `exists_tendsto_rescaledArc`: along a subsequence with `ξ_{n_k} → ξ`, on a window `[0, S]` that
  stays before `b`, a further subsequence of the rescaled arcs converges uniformly to a trajectory
  `y` of the Fuller system with a relaxed control `w ∈ U_T` satisfying the maximum condition, with
  `y(0) = ξ`, and the integrated rescaled controls converge to `∫ w`.

## Proof of `exists_tendsto_rescaledArc` (plan)

1. Bounds: `|ξ_n| ≤ 1` on `Ξ`; by `tendstoUniformlyOn_rescaledField` on a compact ball the rescaled
   field is bounded for small `ρ` (and `ρ_n → 0`, `IsChatteringArcInto.switchPoints`), so the
   rescaled arcs stay in a fixed ball on `[0, S]` (a Grönwall-type bound from the integral
   equation) and are uniformly Lipschitz; the integrated controls `W_n(s) = ∫₀ˢ rescaledControl n`
   are 1-Lipschitz.
2. Arzelà–Ascoli (`BoundedContinuousFunction.arzela_ascoli` on `C([0, S])`) for the pairs
   `(rescaledArc n, W_n)`: a uniformly convergent subsequence, `→ (y, W)`, `W` Lipschitz with
   `W(s) - W(s') ∈ (s - s') U_T` (convex closed), so `w = W'` exists a.e. (Lebesgue's
   differentiation theorem for Lipschitz functions) with values in `U_T`, and `W = ∫ w`.
3. The limit equation: in the integral equation replace `rescaledField ρ v y` by
   `fullerField (simplexToUT v) y` (uniform error `→ 0`, `tendstoUniformlyOn_rescaledField`);
   `fullerField` is affine in the control, `∫ -i·simplexToUT v_n = -i W_n → -i W`, and the other
   components converge with `y_n → y`. So `(y, w)` is a trajectory with controls in `U_T`
   (`IsTrajectory UT`, Carathéodory form).
4. The maximum condition: for each vertex `v` and `[s₁, s₂] ⊆ [0, S]`,
   `∫_{s₁}^{s₂} (H(Z_v) - H(Z_{u})) ≤ 0` along the Reinhardt arc (the maximum condition of the
   extremal); divided by `ρ³` (`tendstoUniformlyOn_rescaledHam`) it tends to
   `24 ∫ (H_F(y, v) - H_F(y, w))` (`H_F` affine in the control; `∫ RR(w_n, y₃,n) → ∫ RR(w, y₃)` by
   integration by parts against the uniformly convergent `W_n`). Lebesgue's differentiation
   theorem turns the integral inequalities into the a.e. maximum condition.
Size: 700–1,000 lines.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology MeasureTheory
open TriFuller

/-- The radius `ρ_n = φ(ẑ(q_n))` of the `n`-th switching point in blow-up coordinates. -/
noncomputable def switchRadius (X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ) (n : ℕ) : ℝ :=
  weightedNorm (fullerCoords (phaseAt X Λ₁ ΛR (τ n)))

/-- The rescaled arc after the `n`-th switching time: `s ↦ scale ρ_n⁻¹ ẑ(q(τ_n + s ρ_n))`
(rescaled coordinates and rescaled time `s = t/ρ_n`, TeX 12908–12912). At `s = 0` it is the
angular component `ξ_n` of the switching point. -/
noncomputable def rescaledArc (X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ) (n : ℕ) (s : ℝ) : Fin 3 → ℂ :=
  scale (switchRadius X Λ₁ ΛR τ n)⁻¹
    (fullerCoords (phaseAt X Λ₁ ΛR (τ n + s * switchRadius X Λ₁ ΛR τ n)))

/-- The rescaled control after the `n`-th switching time, as a point of `U_T`. -/
noncomputable def rescaledControl (u : ℝ → Fin 3 → ℝ) (X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ) (n : ℕ)
    (s : ℝ) : ℂ :=
  simplexToUT (u (τ n + s * switchRadius X Λ₁ ΛR τ n))

/-- **The rescaled arc solves the rescaled Reinhardt equation**: along a chattering arc, if the
window `[τ_n, τ_n + S ρ_n]` stays before `b`, then for `s ∈ [0, S]`,
`rescaledArc n s = ξ_n + ∫₀ˢ rescaledField ρ_n (u(τ_n + σ ρ_n)) (rescaledArc n σ) dσ`, and
`rescaledArc n 0 = ξ_n`. -/
theorem rescaledArc_eq_integral {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n : ℕ) {S : ℝ}
    (hS : τ n + S * switchRadius X Λ₁ ΛR τ n ≤ b) :
    rescaledArc X Λ₁ ΛR τ n 0 = switchAng X Λ₁ ΛR τ n ∧
      ∀ s ∈ Icc 0 S, rescaledArc X Λ₁ ΛR τ n s = rescaledArc X Λ₁ ΛR τ n 0 +
        ∫ σ in (0 : ℝ)..s, rescaledField (switchRadius X Λ₁ ΛR τ n)
          (u (τ n + σ * switchRadius X Λ₁ ΛR τ n)) (rescaledArc X Λ₁ ΛR τ n σ) := by
  sorry

/-- **Limits of rescaled Reinhardt arcs are relaxed Fuller extremals** (the precise form of "By the
earlier asymptotic formulas … When `r = 0`, the Reinhardt switching function agrees with the Fuller
switching function", TeX 12912–12918, for whole arcs): along a chattering arc, let `n_k = φ k`
with `ξ_{n_k} → ξ`, and let `S > 0` be such that the windows `[τ_{n_k}, τ_{n_k} + S ρ_{n_k}]` stay
before `b` for large `k`. Then along a further subsequence the rescaled arcs converge uniformly on
`[0, S]` to a trajectory `y` of the Fuller system from `ξ` with a control `w` in `U_T` satisfying
the maximum condition, and the integrals of the rescaled controls converge to those of `w`. -/
theorem exists_tendsto_rescaledArc {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {ξ : Fin 3 → ℂ} (hξ : Tendsto (fun k ↦ switchAng X Λ₁ ΛR τ (φ k)) atTop (𝓝 ξ)) {S : ℝ}
    (hS : 0 < S) (hwin : ∀ᶠ k in atTop, τ (φ k) + S * switchRadius X Λ₁ ΛR τ (φ k) < b) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (y : ℝ → Fin 3 → ℂ) (w : ℝ → ℂ),
      IsTrajectory UT 0 S y w ∧ MaxCondition UT 0 S y w ∧ y 0 = ξ ∧
      TendstoUniformlyOn (fun k s ↦ rescaledArc X Λ₁ ΛR τ (φ (ψ k)) s) y atTop (Icc 0 S) ∧
      ∀ s ∈ Icc 0 S, Tendsto
        (fun k ↦ ∫ σ in (0 : ℝ)..s, rescaledControl u X Λ₁ ΛR τ (φ (ψ k)) σ) atTop
        (𝓝 (∫ σ in (0 : ℝ)..s, w σ)) := by
  sorry

end SmoothedPolygons
