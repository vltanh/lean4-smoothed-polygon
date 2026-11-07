module

public import SmoothedPolygons.Ch6.Hamiltonian

/-!
# Periodic extension of extremals (Remark 6.6.1)

The unlabelled Remark 6.6.1 of §6.6 (TeX 5216–5242):

* "The transversality conditions in the Reinhardt problem require the terminal time to satisfy
  `X(t_f) = R⁻¹X₀R`, where `R` is the usual rotation matrix. Thus, if we extend time, every
  optimal solution can be made into a periodic one. `X(3t_f) = X₀`. The same requirement also
  holds of `g`, `Λ₁` and `Λ_R`, except that the period for `g` is larger: `g(6t_f) = I₂`. Thus,
  every transversal trajectory determines a periodic solution (with discrete rotational
  symmetry) of the lifted trajectories in the cotangent bundle." (`remark6_6_1`)
* "The transversality condition for `Λ₁` is a consequence of the transversality condition for
  `g`. In fact, we know the general solution for `Λ₁` in terms of `g`. See Corollary 6.5.3."
  (`remark6_6_1_lambda1`)

The extension: for `t ∈ [kT, (k + 1)T)`, `s = t - kT`,
`g(t) = g(s)Rᵏ`, `X(t) = R⁻ᵏX(s)Rᵏ`, `Λᵢ(t) = R⁻ᵏΛᵢ(s)Rᵏ`, and the control is rotated, `u(t)`
being `u(s)` with its coordinates permuted cyclically `k` times, so that
`Z_{u(t)} = R⁻ᵏ Z_{u(s)} Rᵏ` (`R⁻¹Z_{e_m}R = Z_{e_{m+1}}`). Since `R³ = -I` and `R⁶ = I`,
conjugation by `R` has order 3 and right multiplication by `R` order 6. The state–costate
equations are invariant under this symmetry (`J` commutes with `R`, the trace form is
conjugation invariant, the star domain is invariant under the rotation, §4.6), and the pieces
join continuously by the transversality conditions (6.6.1).

`IsStateCostateSolution` is the state–costate system of Problem 6.7.1 with the conditions of the
maximum principle but without the boundary conditions: `IsPontryaginExtremal` is it together
with the transversality conditions (6.6.1) (`isPontryaginExtremal_iff`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory

/-- The state–costate system of Problem 6.7.1 on `[0, T]` with the conditions of the maximum
principle (§6.2: `λ_cost ≤ 0`, nontriviality, maximum condition and `H = 0` almost everywhere),
without boundary conditions: `IsPontryaginExtremal` without its transversality conditions. -/
def IsStateCostateSolution (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) : Prop :=
  IsStateTrajectory T u g X ∧ lam ≤ 0 ∧
    (∀ t ∈ Set.Icc 0 T, (Λ₁ t).trace = 0 ∧ (ΛR t).trace = 0 ∧ traceForm (ΛR t) (X t) = 0 ∧
      (lam ≠ 0 ∨ Λ₁ t ≠ 0 ∨ ΛR t ≠ 0)) ∧
    IsIntegralCurve Λ₁ (fun t ↦ Λ₁ t * X t - X t * Λ₁ t) T ∧
    IsIntegralCurve ΛR (fun t ↦
      (controlP (u t) (X t) * ΛR t - ΛR t * controlP (u t) (X t)) -
        traceForm (ΛR t) (controlP (u t) (X t)) •
          (controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) +
        ((-Λ₁ t + (3 / 2 * lam) • J) * X t - X t * (-Λ₁ t + (3 / 2 * lam) • J))) T ∧
    ∀ᵐ t, t ∈ Set.Ioo 0 T →
      hamiltonian lam (Λ₁ t) (ΛR t) (X t) (u t) = 0 ∧
        ∀ v ∈ controlSimplex,
          hamiltonian lam (Λ₁ t) (ΛR t) (X t) v ≤ hamiltonian lam (Λ₁ t) (ΛR t) (X t) (u t)

/-- A Pontryagin extremal is a solution of the state–costate system with the transversality
conditions (6.6.1). -/
theorem isPontryaginExtremal_iff {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} :
    IsPontryaginExtremal T u g X Λ₁ ΛR lam ↔ IsStateCostateSolution T u g X Λ₁ ΛR lam ∧
      g 0 = 1 ∧ g T = R ∧ X T = R⁻¹ * X 0 * R ∧ Λ₁ T = R⁻¹ * Λ₁ 0 * R ∧
      ΛR T = R⁻¹ * ΛR 0 * R := by
  unfold IsPontryaginExtremal IsStateCostateSolution
  tauto

/-- **Remark 6.6.1**, second item (`rem:lam1-transversality`, label of this formalization):
the transversality condition for `Λ₁` follows from the one for `g`: if `g' = gX` with
`g(0) = I₂`, `g(t_f) = R`, and `Λ₁' = [Λ₁, X]`, then `Λ₁(t_f) = R⁻¹Λ₁(0)R`, because
`Λ₁(t) = g(t)⁻¹Λ₁(0)g(t)` (Corollary 6.5.3, for Carathéodory solutions). -/
theorem remark6_6_1_lambda1 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) (hg0 : g 0 = 1) (hgT : g T = R)
    (hΛ : IsIntegralCurve Λ₁ (fun t ↦ Λ₁ t * X t - X t * Λ₁ t) T) :
    Λ₁ T = R⁻¹ * Λ₁ 0 * R := by
  sorry

/-- **Remark 6.6.1**, first item (`rem:periodic-extension`, label of this formalization): every
Pontryagin extremal on `[0, t_f]` (a "transversal trajectory") extends, with discrete rotational
symmetry, to a periodic solution of the state–costate system: there are `u', g', X', Λ₁', Λ_R'`
on `[0, ∞)`, equal to `u, g, X, Λ₁, Λ_R` on `[0, t_f]` (the control on `[0, t_f)`), such that

* `g'(t + t_f) = g'(t)R`, `X'(t + t_f) = R⁻¹X'(t)R`, `Λᵢ'(t + t_f) = R⁻¹Λᵢ'(t)R`, and the control
  is rotated, `u'(t + t_f)ⱼ = u'(t)_{j-1}` (so `Z_{u'(t + t_f)} = R⁻¹Z_{u'(t)}R`);
* `X'(3t_f) = X₀` and `g'(6t_f) = I₂`, and more generally `u', X', Λ₁', Λ_R'` are periodic with
  period `3t_f` and `g'` with period `6t_f`;
* for every `n ≥ 1`, the extension solves the state–costate system on `[0, n t_f]`
  (`IsStateCostateSolution`), with the same `λ_cost`. -/
theorem remark6_6_1 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) :
    ∃ (u' : ℝ → Fin 3 → ℝ) (g' X' Λ₁' ΛR' : ℝ → Mat2),
      (∀ t ∈ Ico 0 T, u' t = u t) ∧
      (∀ t ∈ Icc 0 T, g' t = g t ∧ X' t = X t ∧ Λ₁' t = Λ₁ t ∧ ΛR' t = ΛR t) ∧
      (∀ t, 0 ≤ t → (u' (t + T) = fun j ↦ u' t (j - 1)) ∧ g' (t + T) = g' t * R ∧
        X' (t + T) = R⁻¹ * X' t * R ∧ Λ₁' (t + T) = R⁻¹ * Λ₁' t * R ∧
        ΛR' (t + T) = R⁻¹ * ΛR' t * R) ∧
      X' (3 * T) = X 0 ∧ g' (6 * T) = 1 ∧
      (∀ t, 0 ≤ t → u' (t + 3 * T) = u' t ∧ g' (t + 6 * T) = g' t ∧ X' (t + 3 * T) = X' t ∧
        Λ₁' (t + 3 * T) = Λ₁' t ∧ ΛR' (t + 3 * T) = ΛR' t) ∧
      ∀ n : ℕ, 0 < n → IsStateCostateSolution (n * T) u' g' X' Λ₁' ΛR' lam := by
  sorry

end SmoothedPolygons
