module

public import SmoothedPolygons.Ch6.IwasawaChart
public import SmoothedPolygons.Ch3.ControlProblem
public import SmoothedPolygons.Ch4.StarDomain
public import OptimalControl.Pontryagin.Defs

/-!
# The Reinhardt problem in the global chart `ℝ³ × 𝔥*`

The state space to which the maximum principle is applied is `SL₂(ℝ) × 𝔥*`, covered by the
chart `(p, z) ↦ (π(p), Φ(z))`, `π` the Iwasawa chart (`SmoothedPolygons/Ch6/IwasawaChart.lean`)
and `Φ` the map of the upper half-plane onto the adjoint orbit of `J` (Lemma 4.2.1); `X = Φ(z)`
satisfies the star conditions exactly for `z ∈ 𝔥*` (Theorem 4.4.1). So the *lifted problem* lives
on the open set `liftedDomain = ℝ³ × 𝔥* ⊆ ℝ³ × ℝ²`, with

* the dynamics `liftedField`: `p' = iwasawaField p Φ(z)` (the lift of `g' = gX`) and
  `z' = (f₁(z; u), f₂(z; u))` (Problem 4.5.1, Lemma 4.5.2; the denominator does not vanish on
  `𝔥* × U_T` by Lemma 3.3.4);
* the control set `U_T` (`controlSimplex`), compact;
* the cost `liftedCost = -(3/2)⟨J, Φ(z)⟩ = (3/2)(1 + x² + y²)/y` (equation `eqn:cost`);
* the boundary condition `liftedEndpoints p₁`: `p(0) = 0`, `p(T) = p₁` and `z(T) = R⁻¹ · z(0)`
  (Möbius action, `mobius`), the zero set of the `C¹` submersion `liftedBoundary p₁`
  (`k = 8` equations). Here `p₁` is the end point of the lift of the minimizer's `g`, a lift of
  `R`; then `π(p(0)) = I`, `π(p(T)) = R` and `X(T) = R⁻¹X(0)R` (`Φ` is equivariant), which are
  the boundary conditions of Problem 3.6.2.

A Reinhardt trajectory lifts to an admissible pair of the lifted problem
(`IsStateTrajectory.exists_lift`), admissible pairs of the lifted problem project to Reinhardt
trajectories (`isStateTrajectory_of_isAdmissibleIn`), and the costs agree (`cost_liftedCost`).
Hence a global minimizer of the Reinhardt problem (`IsReinhardtMinimizer`) lifts to a (strong
local) minimizer of the lifted problem (`IsReinhardtMinimizer.exists_lift`).

Why this state space (inventory §3.4, `notes/plan_ch5_8_16/inventory.md`): on
`SL₂(ℝ) × 𝔰𝔩₂(ℝ)` (the book's choice) the maximum principle returns the spurious multiplier
`(λ_cost, Λ₁, Λ₂) = (0, 0, cX)` for every trajectory (E21), and on `Mat₂ × 𝔥*` the end condition
`g(T) = R` violates the constraint qualification (`det g` is a first integral). On `ℝ³ × 𝔥*`
the nontriviality of the costate is the nontriviality of the reduced costate `(λ_cost, Λ₁, Λ_R)`,
which is the condition of `IsPontryaginExtremal`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Pontryagin ControlSystem

/-- The state space `ℝ³ × ℝ²` of the lifted problem: Iwasawa coordinates `p = (s, r, θ)` of `g`
and the point `z = (x, y)` of the upper half-plane with `X = Φ(x + iy)`. -/
abbrev LiftedState : Type := (ℝ × ℝ × ℝ) × (ℝ × ℝ)

/-- The open set `ℝ³ × 𝔥*` on which the lifted problem is posed. -/
def liftedDomain : Set LiftedState := univ ×ˢ starDomain

/-- The dynamics of the lifted problem: `p' = iwasawaField p Φ(z)`, `z' = (f₁(z; u), f₂(z; u))`. -/
noncomputable def liftedField (q : LiftedState) (u : Fin 3 → ℝ) : LiftedState :=
  (iwasawaField q.1 (Φ q.2.1 q.2.2), (halfPlaneF₁ q.2.1 q.2.2 u, halfPlaneF₂ q.2.1 q.2.2 u))

/-- The cost integrand `-(3/2)⟨J, Φ(z)⟩` of the lifted problem (equation `eqn:cost`). -/
noncomputable def liftedCost (q : LiftedState) (_u : Fin 3 → ℝ) : ℝ :=
  -(3 / 2) * traceForm J (Φ q.2.1 q.2.2)

/-- The Möbius action `z ↦ (az + b)/(cz + d)` of `A = [[a, b], [c, d]]` on the upper half-plane,
in real coordinates `z = x + iy`: with `D = (cx + d)² + c²y²`,
`((ax + b)(cx + d) + acy²)/D + i (ad - bc) y/D`. -/
noncomputable def mobius (A : Mat2) (z : ℝ × ℝ) : ℝ × ℝ :=
  (((A 0 0 * z.1 + A 0 1) * (A 1 0 * z.1 + A 1 1) + A 0 0 * A 1 0 * z.2 ^ 2) /
      ((A 1 0 * z.1 + A 1 1) ^ 2 + A 1 0 ^ 2 * z.2 ^ 2),
    (A 0 0 * A 1 1 - A 0 1 * A 1 0) * z.2 / ((A 1 0 * z.1 + A 1 1) ^ 2 + A 1 0 ^ 2 * z.2 ^ 2))

/-- The boundary map of the lifted problem: `(p(0), p(T) - p₁, z(T) - R⁻¹ · z(0))`. -/
noncomputable def liftedBoundary (p₁ : ℝ × ℝ × ℝ) (w : LiftedState × LiftedState) :
    (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × (ℝ × ℝ) :=
  (w.1.1, w.2.1 - p₁, w.2.2 - mobius R⁻¹ w.1.2)

/-- The boundary condition of the lifted problem: `p(0) = 0`, `p(T) = p₁`, `z(T) = R⁻¹ · z(0)`. -/
def liftedEndpoints (p₁ : ℝ × ℝ × ℝ) : Set (LiftedState × LiftedState) :=
  {w | liftedBoundary p₁ w = 0}

/-- The control simplex `U_T` is compact. -/
theorem isCompact_controlSimplex : IsCompact controlSimplex := by
  have hsub : controlSimplex ⊆ Set.pi univ (fun _ : Fin 3 ↦ Icc (0 : ℝ) 1) :=
    fun u hu i _ ↦ hu.1 i
  refine (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset ?_ hsub
  have e : controlSimplex = (⋂ i, {u : Fin 3 → ℝ | 0 ≤ u i ∧ u i ≤ 1}) ∩
      {u | u 0 + u 1 + u 2 = 1} := by
    ext u; simp [controlSimplex]
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun i ↦ ?_) (isClosed_eq (by fun_prop) continuous_const)
  exact (isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_apply i) continuous_const)

/-- `ℝ³ × 𝔥*` is open. -/
theorem isOpen_liftedDomain : IsOpen liftedDomain := by
  refine isOpen_univ.prod ?_
  have e : starDomain = {p : ℝ × ℝ | 0 < p.2} ∩ {p | -(1 / √3) < p.1} ∩ {p | p.1 < 1 / √3} ∩
      {p | 1 / 3 < p.1 ^ 2 + p.2 ^ 2} := by
    ext p; simp [starDomain, and_assoc]
  rw [e]
  exact (((isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_const continuous_fst)).inter
    (isOpen_lt continuous_fst continuous_const)).inter (isOpen_lt continuous_const (by fun_prop))

/-- The lifted dynamics satisfies the regularity hypotheses of the maximum principle on
`ℝ³ × 𝔥*` (smooth in the state, the denominator `⟨Z_u, X⟩` being negative on `𝔥* × U_T` by
Lemma 3.3.4). -/
theorem isC1On_liftedField : IsC1On liftedField liftedDomain controlSimplex := by
  sorry

/-- The cost integrand is smooth on `ℝ³ × 𝔥*`. -/
theorem isC1On_liftedCost : IsC1On liftedCost liftedDomain controlSimplex := by
  sorry

/-- Equivariance of `Φ` (Remark 4.2.2, `ΦH_smul`) in real coordinates: for `det A = 1` and
`y > 0`, the Möbius map of `A` keeps the upper half-plane and `Φ(A · z) = A Φ(z) A⁻¹`. -/
theorem Φ_mobius {A : Mat2} (hA : A.det = 1) {z : ℝ × ℝ} (hz : 0 < z.2) :
    0 < (mobius A z).2 ∧ Φ (mobius A z).1 (mobius A z).2 = A * Φ z.1 z.2 * A⁻¹ := by
  sorry

/-- The boundary map is `C¹` near every pair of states in the upper half-plane. -/
theorem contDiffAt_liftedBoundary (p₁ : ℝ × ℝ × ℝ) {w : LiftedState × LiftedState}
    (hw : 0 < w.1.2.2) : ContDiffAt ℝ 1 (liftedBoundary p₁) w := by
  sorry

/-- The boundary map is a submersion (the constraint qualification of the maximum principle). -/
theorem surjective_fderiv_liftedBoundary (p₁ : ℝ × ℝ × ℝ) {w : LiftedState × LiftedState}
    (hw : 0 < w.1.2.2) : Function.Surjective (fderiv ℝ (liftedBoundary p₁) w) := by
  sorry

/-- The cost of a pair of the lifted problem is the Reinhardt cost of its projection. -/
theorem cost_liftedCost (T : ℝ) (u : ℝ → Fin 3 → ℝ) (q : ℝ → LiftedState) :
    cost liftedCost T u q = reinhardtCost T (fun t ↦ Φ (q t).2.1 (q t).2.2) := by
  simp [cost, liftedCost, reinhardtCost, intervalIntegral.integral_const_mul]

/-- A Reinhardt state trajectory with `g(0) = I` lifts to an admissible pair of the lifted
problem, with `p(0) = 0` (Lemma 4.2.1, Theorem 4.4.1, Lemma 4.5.2, path lifting through `π`). -/
theorem IsStateTrajectory.exists_lift {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) (hg0 : g 0 = 1) :
    ∃ q : ℝ → LiftedState, (q 0).1 = 0 ∧
      (∀ t ∈ Icc 0 T, iwasawa (q t).1 = g t ∧ Φ (q t).2.1 (q t).2.2 = X t) ∧
      IsAdmissibleIn liftedField liftedDomain controlSimplex (q 0) T u q := by
  sorry

/-- An admissible pair of the lifted problem projects to a Reinhardt state trajectory
(Theorem 4.4.1, `eqn:tangent-map-f1f2` from the proof of Lemma 4.5.2, `isIntegralCurve_iwasawa`). -/
theorem isStateTrajectory_of_isAdmissibleIn {T : ℝ} (hT : 0 < T) {u : ℝ → Fin 3 → ℝ}
    {q : ℝ → LiftedState} (h : IsAdmissibleIn liftedField liftedDomain controlSimplex (q 0) T u q) :
    IsStateTrajectory T u (fun t ↦ iwasawa (q t).1) (fun t ↦ Φ (q t).2.1 (q t).2.2) := by
  sorry

/-- **A Reinhardt minimizer lifts to a strong local minimizer of the lifted problem**: its lift
`q` (with `p(0) = 0`) minimizes the cost among the admissible pairs of the lifted problem with
the boundary condition `liftedEndpoints (q T).1`, since these project to admissible trajectories
of Problem 3.6.2 with the same cost; in particular it is a strong local minimizer. -/
theorem IsReinhardtMinimizer.exists_lift {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtMinimizer T u g X) :
    ∃ q : ℝ → LiftedState, (q 0).1 = 0 ∧
      (∀ t ∈ Icc 0 T, iwasawa (q t).1 = g t ∧ Φ (q t).2.1 (q t).2.2 = X t) ∧
      IsStrongLocalMinimizer liftedField liftedCost liftedDomain controlSimplex
        (liftedEndpoints (q T).1) T u q := by
  sorry

end SmoothedPolygons
