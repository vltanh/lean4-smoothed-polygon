module

public import SmoothedPolygons.Ch5.Theorem502
public import SmoothedPolygons.Ch6.AdmissibleDisk
public import SmoothedPolygons.Ch6.MatrixExtremal
public import SmoothedPolygons.Ch6.Hamiltonian
public import SmoothedPolygons.Ch4.TerminalTime
public import OptimalControl.ODE.StateConstraint

/-!
# Existence of an optimal control (§6.1)

§6.1 (`sec:existence-opt-control`, TeX 4520–4600) argues that the Reinhardt control problem
(Problem 3.6.2) has an optimal control, by Filippov's theorem (Theorem 6.1.1,
`External.filippov`). With the lift of every global minimizer to a Pontryagin extremal (§6.2,
`exists_isPontryaginExtremal_of_isReinhardtMinimizer`), this gives a global minimizer that is a
Pontryagin extremal (`exists_isReinhardtMinimizer_isPontryaginExtremal`), the premise of
Proposition 8.1.3 ("We have seen that the global minimizer must be extremal", TeX 6791).

## The book's argument (TeX 4553–4600)

* the control set `U_T` is compact; the velocity sets are convex (Lemma 6.1.2, `lemma6_1_2`);
* "Recall that Reinhardt has proved the existence of an optimal solution to the Reinhardt problem.
  We claim that the velocity sets can be assumed to be compactly supported": by Theorem 5.0.2,
  "we may assume that `z` lies in the compact set `𝔥**`", so `Φ(z)` and the field
  `[Z_u, Φ(z)]/⟨Z_u, Φ(z)⟩` are bounded; `t_f ≤ π/3` by Lemma 4.3.1 and Gronwall's inequality
  (App. A.1) bound `g`;
* the fields are multiplied by a smooth cut-off `ψ` with `ψ = 1` on `𝔥**`, and Filippov's theorem is
  applied to the cut-off system.

## Gaps, and their repair along the book's lines (inventory, Part I §3.5)

1. *Theorem 5.0.2 is about balanced disks; §6.1 applies it to admissible trajectories.* That needs
   the converse of Problem 3.6.2 (E15), which is false for trajectories of higher winding number
   (`exists_isReinhardtAdmissible_not_isWindingOne`). Repair: higher winding costs at least `7π/2`
   (`isWindingOne_of_reinhardtCost_lt`, `SmoothedPolygons/Ch6/Winding.lean`), more than the
   smoothed octagon, and the converse holds for winding number one
   (`exists_isBalancedPair_of_isReinhardtAdmissible`). Together with Theorem 5.0.2:
   `IsReinhardtAdmissible.forall_mem_truncatedStarDomain`.
2. *The cut-off.* A minimizer of the cut-off problem need not be a Reinhardt trajectory (`ψ`
   changes the dynamics outside `𝔥**`). Repair: impose the closed state constraint `z ∈ 𝔥**`, as
   the book's "we may assume that `z` lies in the compact set `𝔥**`" says, and use Filippov's
   theorem with a state constraint (`ControlSystem.exists_optimal_constrained`,
   `OptimalControl/ODE/StateConstraint.lean`; same proof as Theorem 6.1.1).
3. *Boundary conditions.* `X(0)` is free and the endpoints are coupled (`g(0) = I`, `g(t_f) = R`,
   `X(t_f) = R⁻¹X(0)R`), while Theorem 6.1.1 fixes the initial point. Repair: the same theorem with
   a compact set of initial points and a closed endpoint relation.
4. *Time bound.* Lemma 4.3.1 assumes a minimizer. Repair: the cost density `-(3/2)⟨J, X⟩` is at
   least `3` on star states (`three_mul_le_reinhardtCost`), so every competitor cheaper than the
   smoothed octagon (`< π`) has `t_f < π/3`.
5. *Reinhardt's existence theorem* (TeX 4569–4572) concerns `K_min`, not the control problem; the
   argument does not use it (see `SmoothedPolygons/Ch6/WorstDisk.lean` for the identification).

## Proof (to be written) of `exists_isReinhardtMinimizer`

On the matrix system of Layer 1 (`MatrixState`, `matrixField`, `matrixCost`, `controlSimplex`;
`SmoothedPolygons/Ch6/MatrixSystem.lean`), with `C` from `exists_bound_of_forall_mem_truncated`:

* state constraint `S = {q | stateX q ∈ Φ(𝔥**), det (stateG q) = 1, |(stateG q)ᵢⱼ| ≤ C}`,
  closed and bounded (`isCompact_truncatedStarDomain`, `Φ` continuous on `y > 0`), inside
  `matrixDomain`, on which `matrixField` is continuous (`isC1On_matrixField`), hence bounded on
  `S × U_T`; initial set `K₀ = {q | stateG q = 1, stateX q ∈ Φ(𝔥**)}` (compact); endpoint relation
  `N = {(q₀, q₁) | stateG q₀ = 1, stateG q₁ = R, stateX q₁ = R⁻¹ (stateX q₀) R}` (closed); window
  `[0, π/3]`;
* convexity of the extended velocity sets: `convex_image_matrixField` (Lemma 6.1.2 transported by
  the tangent map of `Φ`, Lemma 4.5.2; the cost does not depend on `u`);
* the class is nonempty: the smoothed octagon's trajectory (`smoothedPolygonDisk_spec`) lies in
  `𝔥**` by Theorem 5.0.2 applied to its own disk (otherwise its cost would exceed itself), has
  `t_f < π/3` (`three_mul_le_reinhardtCost`, cost `< π`), and `|g| ≤ C`;
* `ControlSystem.exists_optimal_constrained` gives a minimizer `(τ, u, q)` of the constrained
  problem; `τ > 0` since `stateG q(0) = I ≠ R`; it projects to a Reinhardt-admissible trajectory
  (`isStateTrajectory_of_isAdmissibleIn_matrix`, `cost_matrixCost`);
* global minimality: a competitor of cost `≥` the octagon's costs at least the constrained minimum
  (the octagon is in the class); a cheaper one has winding number one, lies in `𝔥**` with
  `t_f < π/3` (`IsReinhardtAdmissible.forall_mem_truncatedStarDomain`) and `|g| ≤ C`, so it is in
  the class (`IsStateTrajectory.isAdmissibleIn_matrix`).

Departure from the book (besides the repairs): the book applies Filippov's theorem to the
half-plane system `(g, z)` (Problem 4.5.1), the formalization to the matrix system `(g, X)` of
Layer 1, whose admissible pairs are already translated to Reinhardt trajectories; the convexity is
Lemma 6.1.2 carried over by `Φ`.

Sizes: `three_mul_le_reinhardtCost` 50–100 lines; `exists_bound_of_forall_mem_truncated` 100–200
(Gronwall: `ControlSystem.le_mul_exp_of_le_add_integral`); `convex_image_matrixField` 100–200;
`IsReinhardtAdmissible.forall_mem_truncatedStarDomain` 100–200; `exists_isReinhardtMinimizer`
300–600; the rest 50–100.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix

/-- **The time bound** (repair of the use of Lemma 4.3.1 in §6.1, TeX 4583): the cost density
`-(3/2)⟨J, X⟩ = (3/2)(x² + y² + 1)/y` is at least `3` on star states, so the cost of every state
trajectory on `[0, T]` is at least `3T`. -/
theorem three_mul_le_reinhardtCost {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) : 3 * T ≤ reinhardtCost T X := by
  sorry

/-- **Gronwall's bound on `g`** (§6.1, TeX 4583–4586, citing App. A.1): there is a constant `C`
bounding the entries of `g` along every state trajectory with `g(0) = I`, `T ≤ π/3` and
`X(t) ∈ Φ(𝔥**)`. -/
theorem exists_bound_of_forall_mem_truncated :
    ∃ C : ℝ, ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsStateTrajectory T u g X →
      g 0 = 1 → T ≤ Real.pi / 3 → (∀ t ∈ Icc 0 T, ∃ z ∈ truncatedStarDomain, X t = Φ z.1 z.2) →
      ∀ t ∈ Icc 0 T, ∀ i j, |g t i j| ≤ C := by
  sorry

/-- **Convex velocity sets of the matrix system** (Lemma 6.1.2 in the matrix coordinates): at a
state with `X = Φ(z)`, `z ∈ 𝔥*`, the velocity set of `(g, X)' = (gX, [P, X])` extended by the cost
`-(3/2)⟨J, X⟩` is convex. It is the image of the half-plane velocity set `f(z, U_T)` of
Lemma 6.1.2 under the linear map `v ↦ (gX, TΦ_z v, -(3/2)⟨J, X⟩)` (Lemma 4.5.2: `TΦ(f(z, u))` is
`[P, X]`). -/
theorem convex_image_matrixField {q : MatrixState}
    (hq : ∃ z ∈ starDomain, stateX q = Φ z.1 z.2) :
    Convex ℝ ((fun u ↦ (matrixField q u, matrixCost q u)) '' controlSimplex) := by
  sorry

/-- **Every competitor at most as costly as the smoothed octagon lies in `𝔥**`** (§6.1, TeX 4579:
"By Theorem 5.0.2, we may assume that `z` lies in the compact set `𝔥**`"). An admissible trajectory
of the Reinhardt control problem with cost at most the area of the smoothed octagon has
`t_f < π/3`, and `X(t) = Φ(z)` with `z ∈ 𝔥**` for all `t ∈ [0, t_f]`. (Proof: winding number one
by `isWindingOne_of_reinhardtCost_lt`, the balanced disk of
`exists_isBalancedPair_of_isReinhardtAdmissible`, and Theorem 5.0.2, `theorem5_0_2`.) -/
theorem IsReinhardtAdmissible.forall_mem_truncatedStarDomain {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsReinhardtAdmissible T u g X)
    (hc : reinhardtCost T X ≤ volume.real (smoothedPolygonDisk 1)) :
    T < Real.pi / 3 ∧ ∀ t ∈ Icc 0 T, ∃ z ∈ truncatedStarDomain, X t = Φ z.1 z.2 := by
  sorry

/-- **Existence of an optimal control** (§6.1, `sec:existence-opt-control`, TeX 4520–4600): the
Reinhardt control problem (Problem 3.6.2) has a global minimizer. -/
theorem exists_isReinhardtMinimizer :
    ∃ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsReinhardtMinimizer T u g X := by
  sorry

/-- A global minimizer of the Reinhardt control problem costs at most the smoothed octagon, has
terminal time `t_f < π/3`, and its trajectory lies in `𝔥**` (§6.1 with Theorem 5.0.2). -/
theorem IsReinhardtMinimizer.forall_mem_truncatedStarDomain {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsReinhardtMinimizer T u g X) :
    reinhardtCost T X ≤ volume.real (smoothedPolygonDisk 1) ∧ T < Real.pi / 3 ∧
      ∀ t ∈ Icc 0 T, ∃ z ∈ truncatedStarDomain, X t = Φ z.1 z.2 := by
  sorry

/-- **A global minimizer exists, and it is a Pontryagin extremal** (§6.1 and §6.2): the
Reinhardt control problem has a global minimizer (`exists_isReinhardtMinimizer`), and every global
minimizer lifts to a Pontryagin extremal
(`exists_isPontryaginExtremal_of_isReinhardtMinimizer`). This is the premise of Proposition 8.1.3
(TeX 6791). -/
theorem exists_isReinhardtMinimizer_isPontryaginExtremal :
    ∃ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ),
      IsReinhardtMinimizer T u g X ∧ IsPontryaginExtremal T u g X Λ₁ ΛR lam := by
  sorry

end SmoothedPolygons
