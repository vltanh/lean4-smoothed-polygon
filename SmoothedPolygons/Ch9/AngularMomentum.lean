module

public import SmoothedPolygons.Ch9.ControlSets
public import SmoothedPolygons.Ch6.MatrixExtremal
public import SmoothedPolygons.Ch8.Defs
public import External.NoetherSussmann

/-!
# §9.1: the circular control problem and the conservation of angular momentum

Hales–Vajjha, *Packings of Smoothed Polygons*, §9.1 "Conserved Quantity for the Circular Control
Set" (TeX 7792–7999), and the introduction's restatement (theorem*, TeX 940–953: "In the control
problem with the circular disk control set, each Pontryagin extremal satisfies a conservation law
(which we call the angular momentum)").

* **Problem 9.1.5** (TeX 7882–7885): the circular control problem is Problem 6.7.1 with the
  control set `U_T` replaced by its circumscribing disk `U_C`. Here Problem 6.7.1 is posed for any
  control set `U` (`IsStarStateFor`, `IsStateTrajectoryFor`, `IsPontryaginExtremalFor`); for
  `U = U_T` it is the project's `IsPontryaginExtremal`
  (`isPontryaginExtremalFor_controlSimplex_iff`), and the circular problem is `U = controlDiskC`.
* **The angular momentum** `𝒜 = ⟨J, Λ₁ + Λ_R⟩` (TeX 7887–7889, `angularMomentum`).
* **Theorem 9.1.6** (`thm:angular-momentum`, TeX 7894–7966): `𝒜` is conserved along every
  Pontryagin extremal of the circular control problem (`theorem9_1_6`), from the generic
  `angularMomentum_conserved` for a compact control set closed under rotations.
* **Remark 9.1.7** (TeX 7968–7986): the same holds for every disk `U_r` (`remark9_1_7`); acting on
  `g` by `g ↦ g exp(-Jθ)` instead of conjugation gives the conserved quantity `-𝒜` directly
  (`momentum_rightRotationField`, `remark9_1_7_rightAction`).

The Noether–Sussmann theorem and Definitions 9.1.1–9.1.3 are in
`External/NoetherSussmann.lean` (Sussmann's statement, used here) and
`SmoothedPolygons/Ch9/NoetherAsPrinted.lean` (the book's, which is false as printed).

## The book's proof and its formal steps

The book (TeX 7902–7966) lets `SO₂(ℝ)` act on `T*(T SL₂(ℝ))` by
`(g, X, Λ₁, Λ₂) ↦ (e^{θJ} g e^{-θJ}, Ad_{e^{θJ}} X, Ad_{e^{θJ}} Λ₁, Ad_{e^{θJ}} Λ₂)`; these are
symmetries "by the proof of Theorem 9.0.3" and since `Ad_{e^{θJ}} Z_u ∈ U_C`. The infinitesimal
action is `τ(J)(g, X) = (Jg - gJ, [J, X])`, and the momentum map is
`𝐉^τ = ⟨Λ₁, Ad_{g⁻¹} J - J⟩ + ⟨Λ₂, [J, X]⟩ = ⟨Λ₁, Ad_{g⁻¹} J⟩ - ⟨J, Λ₁ + Λ_R⟩`; by Corollary 6.5.3
`Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)`, so the first term is constant, and the Noether–Sussmann theorem makes
`𝐉^τ` constant. Formally:

1. The state space (as in Chapter 6, `SmoothedPolygons/Ch6/MatrixSystem.lean`): the open set
   `matrixDomainFor U = GL₂⁺(ℝ) × {X | ⟨Z_u, X⟩ < 0 for u ∈ U}` of `Mat₂(ℝ) × 𝔰𝔩₂(ℝ)`, the
   dynamics `matrixField` and the cost `matrixCost` of Chapter 6, with controls in `U`
   (`isOpen_matrixDomainFor`, `contDiffOn_matrixField_matrixDomainFor`,
   `IsStateTrajectoryFor.isAdmissibleIn_matrix`).
2. The symmetries: the rotations act by `rotateState (exp(θJ))`, with generator `rotationField`;
   they preserve the dynamics and the cost (`matrixField_rotateState`, `matrixCost_rotateState`:
   the proof of Theorem 9.0.3) and permute the controls of a rotation-closed `U`, so
   `rotationField` is an infinitesimal symmetry in Sussmann's sense, cost included
   (`isInfinitesimalSymmetry_rotationField`).
3. Noether–Sussmann (`External.noether_sussmann_one_parameter`; `𝔰𝔬₂(ℝ) = ℝJ` is one-dimensional,
   so the momentum map is the momentum of `τ(J) = rotationField`): `⟨p, Y(q)⟩` is constant along
   every covector curve with the adjoint equation and the maximum condition
   (`momentum_rotationField_eq`).
4. The momentum map computed (TeX 7945–7956; `momentum_rotationField`).
5. The lift (`IsPontryaginExtremalFor.exists_covector`; see the departure below): every extremal
   `(g, X, Λ₁, Λ_R)` comes from such a covector curve `p`, with `Λ₁ = covectorΛ₁ q p` and
   `Λ_R = covectorΛR q p`.
6. Corollary 6.5.3 for the first term, and the conclusion (`angularMomentum_conserved`).

## Readings

* **`U_C`** is the disk `U_1` (`controlDiskC`; the printed formula is `U_T`,
  `SmoothedPolygons/Ch9/ControlSets.lean`).
* **The state space of the circular problem.** Problem 9.1.5 does not say where the dynamics are
  defined. `P = Z_u/⟨Z_u, X⟩` must be defined for every `u ∈ U_C` (the Hamiltonian is maximized
  over all of `U_C`, and the regularity of §6.2 that the Noether–Sussmann theorem assumes needs
  it), so the state space of `X` is the set of star states for `U_C` (`IsStarStateFor`):
  `det X = 1` and `⟨Z_u, X⟩ < 0` for all `u ∈ U_C`, a set smaller than the star domain of
  Problem 3.6.2 (`IsStarStateFor.isStarState`). In the upper half-plane it is the hyperbolic disk
  `√3(1 + |z|²) < 4 Im z` about `i`, of radius `arccosh(2/√3)` (`isStarStateFor_controlDiskC_Φ`).
  The sign `< 0` is that of Lemma 3.3.4 on `U_T ⊆ U_C`: since `U_C` is connected, `⟨Z_u, X⟩ ≠ 0`
  on `U_C` allows only this sign or `⟨Z_u, X⟩ > 0` on all of `U_C`, which no star state of
  Problem 3.6.2 satisfies.
* **"Along the optimal trajectory"** (TeX 7896) is read as "along every Pontryagin extremal", as
  the proof gives and the introduction states (TeX 948–952). Optimality is not used, and the
  existence of an optimal control for `U_C` is not established in the book (Filippov's theorem
  needs convex velocity sets, TeX 4564–4566); the stronger form is stated.
* **The extremals of the circular problem** are those of Problem 6.7.1, the reduced costate
  `(Λ₁, Λ_R)` with the conditions of the maximum principle and the transversality conditions,
  with `U_T` replaced by `U_C` throughout (the maximum condition over `U_C`, the controls in
  `U_C`, the star states for `U_C`): `IsPontryaginExtremalFor controlDiskC`.
* **`SL₂(ℝ)`** is replaced by the open set `GL₂⁺(ℝ)` of `Mat₂(ℝ)`, as in Chapter 6 (the reading D1
  of `External/Pontryagin.lean`; the Noether–Sussmann theorem is formalized on open subsets of a
  finite-dimensional space, S1 of the OptimalControl package); `det g = 1` along the extremals.
* **The Lie algebra** `𝔰𝔬₂(ℝ) = ℝJ` is one-dimensional, so the book's momentum map
  `𝐉^τ(q, p)(aJ) = a ⟨p, τ(J)(q)⟩` is constant if and only if the momentum of the one field
  `τ(J) = rotationField` is; the one-parameter form of the theorem is applied.
* **The Noether–Sussmann theorem** is applied in Sussmann's form, whose symmetries preserve the
  cost (`External.noether_sussmann_one_parameter`), not in the printed form, which is false
  (`noetherSussmann_false_as_printed`). The rotations preserve the cost `-(3/2)⟨J, X⟩`
  (`matrixCost_rotateState`), as the book's appeal to "the proof of Theorem 9.0.3" (TeX 7921)
  checks for the whole Hamiltonian.
* **Remark 9.1.7**, third item: "whenever `r² > ⅓`". The conservation holds for every `r`
  (`remark9_1_7` has no hypothesis on `r`); for `r² < ⅓` the disk is empty and there are no
  extremals, for `r² = ⅓` it is the centroid.

## Departure from the paper

**The lift of the reduced costate** (`IsPontryaginExtremalFor.exists_covector`). The book's proof
works with the full costate `(Λ₁, Λ₂)` of `T*(T SL₂(ℝ))`, the covector to which the
Noether–Sussmann theorem applies. The extremals of Problem 6.7.1, as formalized
(`IsPontryaginExtremal`, and here `IsPontryaginExtremalFor`), carry only the reduced costate
`(Λ₁, Λ_R)`, `Λ_R = [Λ₂, X]`, which determines `Λ₂` up to a multiple of `X`. The lift reconstructs
a covector curve: `Λ₂ = [X, Λ_R]/4 + c X` (since `[[X, Λ_R], X] = 4Λ_R` for `Λ_R ⊥ X`,
`det X = 1`), with `c` the integral of an explicit function, chosen so that `Λ₂` satisfies the
`X`-part of Hamilton's equations (its component along `X`; the rest follows from the `Λ_R`
equation); the `g`-part is `p = Λ₁ g⁻¹`. The book does not need this step, since its extremals
are lifted trajectories in the cotangent bundle; the conserved quantity does not depend on `c`
(`[X, X] = 0`).

## Shorter routes (documented, not taken)

* **Remark 9.1.7, second item**: the action `g ↦ g e^{-θJ}`, `X ↦ Ad_{e^{θJ}} X` has momentum
  `-𝒜` exactly (`momentum_rightRotationField`), with no term `⟨Λ₁, Ad_{g⁻¹}J⟩`, so Corollary 6.5.3
  is not needed (`remark9_1_7_rightAction`).
* **Without Noether or the lift**: by the costate equations, `𝒜' = ⟨J, [P, Λ_R] - ⟨Λ_R, P⟩[P, X]⟩`
  almost everywhere (`⟨J, [J, X]⟩ = 0`, and the `[Λ₁, X]` terms cancel), and this is
  `-d/dθ H(Λ₁, Λ_R, X; Ad_{e^{θJ}} Z_u)` at `θ = 0`, which vanishes at a maximizer `u` of `H` over
  a rotation-closed `U` (Theorem 9.0.3: the rotated controls stay in `U`). An absolutely continuous
  function with zero derivative almost everywhere is constant. This is Noether's argument
  specialized to the matrix form, about 100–150 lines, and needs neither the lift (step 5,
  350–500 lines) nor the infinitesimal-symmetry machinery (step 2).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Matrix Pontryagin ControlSystem

/-! ### Problem 9.1.5: the circular control problem -/

/-- **The star states for the control set `U`**: `X ∈ 𝔰𝔩₂(ℝ)` with `det X = 1` and
`⟨Z_u, X⟩ < 0` for every `u ∈ U`, so that `P = Z_u/⟨Z_u, X⟩` is defined for every control. For
`U = U_T` these are the star states of Problem 3.6.2 (`isStarStateFor_controlSimplex_iff`, by
Lemma 3.3.4); for `U = U_C` they form the state space of the circular problem (module docstring,
"Readings"). -/
def IsStarStateFor (U : Set (Fin 3 → ℝ)) (X : Mat2) : Prop :=
  X.trace = 0 ∧ X.det = 1 ∧ ∀ u ∈ U, traceForm (controlMatrix u) X < 0

/-- For `U = U_T`, the star states for `U` are the star states (Lemma 3.3.4).

Proof plan (5–10 lines): unfold; `lemma3_3_4 X hX` turns `0 < ρ₀ X ∧ 0 < ρ₁ X ∧ 0 < ρ₂ X` into
the condition on `U_T`. -/
theorem isStarStateFor_controlSimplex_iff (X : Mat2) :
    IsStarStateFor controlSimplex X ↔ IsStarState X := by
  sorry

/-- For a control set containing `U_T` (such as `U_C`), the star states for `U` are star states:
the state space of the circular problem lies in that of Problem 3.6.2.

Proof plan (5–10 lines): restrict the condition to `U_T` and apply
`isStarStateFor_controlSimplex_iff`. -/
theorem IsStarStateFor.isStarState {U : Set (Fin 3 → ℝ)} (hU : controlSimplex ⊆ U) {X : Mat2}
    (hX : IsStarStateFor U X) : IsStarState X := by
  sorry

/-- **The state space of the circular problem in the upper half-plane**: `Φ(x + iy)` is a star
state for `U_C` exactly when `√3(1 + x² + y²) < 4y`, i.e. `cosh d(z, i) < 2/√3` for the hyperbolic
distance `d`. In particular `J = Φ(i)` is one, and `Φ(2i)` (a star state of Problem 3.6.2) is not.

Proof plan (40–60 lines): on the plane `Σuᵢ = 1`, write `u₀ = ⅓ + s₀`, `u₁ - u₂ = √3 s₁`; then
`U_C` is the disk `s₀² + s₁² ≤ (⅔)²` (`Σuᵢ² = ⅓ + (3/2)(s₀² + s₁²)`), and for
`X = [[a, b], [c, -a]]`, `⟨Z_u, X⟩ = (b - c)/3 + 2a s₁ + (b + c) s₀`. Its maximum over the disk
is `(b - c)/3 + (⅔)√(4a² + (b + c)²)` (Cauchy–Schwarz, attained). For `X = Φ(x + iy)`:
`b - c = -(1 + x² + y²)/y` and `4a² + (b + c)² = ((1 + x² + y²)² - 4y²)/y²`, so the maximum is
negative iff `2√((1 + |z|²)² - 4y²) < 1 + |z|²` iff `3(1 + |z|²)² < 16y²`. `det Φ = 1` and
`tr Φ = 0` by `ring`/`field_simp`. -/
theorem isStarStateFor_controlDiskC_Φ {x y : ℝ} (hy : 0 < y) :
    IsStarStateFor controlDiskC (Φ x y) ↔ √3 * (1 + x ^ 2 + y ^ 2) < 4 * y := by
  sorry

/-- **A state trajectory of the problem with control set `U`** on `[0, T]` (Problem 3.6.2, and
Problem 9.1.5 for `U = U_C`): `IsStateTrajectory` with `U_T` replaced by `U`, in the controls and
in the star states: a measurable control `u` with values in `U`, `g` in `SL₂(ℝ)`, `X` among the
star states for `U`, `g' = gX` and `X' = [P, X]` with `P = Z_u/⟨Z_u, X⟩`. -/
def IsStateTrajectoryFor (U : Set (Fin 3 → ℝ)) (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2) :
    Prop :=
  0 < T ∧ Measurable u ∧ (∀ t ∈ Set.Icc 0 T, u t ∈ U) ∧
    (∀ t ∈ Set.Icc 0 T, (g t).det = 1 ∧ IsStarStateFor U (X t)) ∧
    IsIntegralCurve g (fun t ↦ g t * X t) T ∧
    IsIntegralCurve X (fun t ↦ controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) T

/-- **A Pontryagin extremal of the problem with control set `U`** on `[0, T]`: Problem 6.7.1 with
`U_T` replaced by `U` (`IsPontryaginExtremal` with `U` in the state trajectory and in the maximum
condition). **Problem 9.1.5** (TeX 7882–7885, the circular control problem) is
`U = controlDiskC`: "We start with problem 6.7.1 and enlarge the control set `U_T` to its
circumscribing disk `U_C`." The conditions: the state trajectory (`IsStateTrajectoryFor U`); the
transversality conditions `g(0) = I`, `g(T) = R`, `X(T) = R⁻¹X(0)R`, `Λ₁(T) = R⁻¹Λ₁(0)R`,
`Λ_R(T) = R⁻¹Λ_R(0)R`; `λ_cost ≤ 0`; `Λ₁, Λ_R ∈ 𝔰𝔩₂(ℝ)`, `Λ_R ⊥ X` and
`(λ_cost, Λ₁, Λ_R) ≠ 0` at every time; the costate equations `Λ₁' = [Λ₁, X]` and
`Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩[P, X] + [-Λ₁ + (3/2)λ_cost J, X]`; for almost every time, `H = 0` and
the control maximizes `H` over `U`. -/
def IsPontryaginExtremalFor (U : Set (Fin 3 → ℝ)) (T : ℝ) (u : ℝ → Fin 3 → ℝ)
    (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) : Prop :=
  IsStateTrajectoryFor U T u g X ∧
    g 0 = 1 ∧ g T = R ∧ X T = R⁻¹ * X 0 * R ∧ Λ₁ T = R⁻¹ * Λ₁ 0 * R ∧ ΛR T = R⁻¹ * ΛR 0 * R ∧
    lam ≤ 0 ∧
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
        ∀ v ∈ U, hamiltonian lam (Λ₁ t) (ΛR t) (X t) v ≤ hamiltonian lam (Λ₁ t) (ΛR t) (X t) (u t)

/-- For `U = U_T`, the extremals for `U` are the Pontryagin extremals of Problem 6.7.1: the
definition of Problem 9.1.5 changes only the control set.

Proof plan (15–25 lines): unfold both definitions; the conditions coincide term by term except
the star states, which agree by `isStarStateFor_controlSimplex_iff`. -/
theorem isPontryaginExtremalFor_controlSimplex_iff {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} :
    IsPontryaginExtremalFor controlSimplex T u g X Λ₁ ΛR lam ↔
      IsPontryaginExtremal T u g X Λ₁ ΛR lam := by
  sorry

/-- **The angular momentum** `𝒜 = ⟨J, Λ₁ + Λ_R⟩` (TeX 7887–7889). -/
noncomputable def angularMomentum (Λ₁ ΛR : Mat2) : ℝ := traceForm J (Λ₁ + ΛR)

/-! ### The matrix system with control set `U` -/

/-- The open set of the matrix system for the control set `U`: `det g > 0` and `X` in the open
cone `⟨Z_u, X⟩ < 0` for all `u ∈ U` (Chapter 6's `matrixDomain` for `U = U_T`,
`matrixDomainFor_controlSimplex`). The star states for `U` are its points with `det X = 1`. -/
def matrixDomainFor (U : Set (Fin 3 → ℝ)) : Set MatrixState :=
  {q | 0 < (stateG q).det ∧ ∀ u ∈ U, traceForm (controlMatrix u) (stateX q) < 0}

/-- For `U = U_T`, the open set is Chapter 6's `GL₂⁺(ℝ) × C`.

Proof plan (8–12 lines): `ext q`; `lemma3_3_4 (stateX q) (trace_slMatrix _)`. -/
theorem matrixDomainFor_controlSimplex : matrixDomainFor controlSimplex = matrixDomain := by
  sorry

/-- For a compact control set the domain is open.

Proof plan (25–40 lines): `det ∘ stateG` is continuous. For the cone: if `U = ∅` it is everything;
otherwise `M(X) = max_{u ∈ U} ⟨Z_u, X⟩` is continuous (`IsCompact.continuous_sSup`-type lemma, or
directly: `(u, X) ↦ ⟨Z_u, X⟩` is continuous and `U` compact, so by the tube lemma
`IsCompact.eventually_forall_of_forall_eventually` the strict inequality `< 0` at `X₀` for all
`u ∈ U` persists on a neighbourhood of `X₀`), composed with the continuous `stateX`. -/
theorem isOpen_matrixDomainFor {U : Set (Fin 3 → ℝ)} (hU : IsCompact U) :
    IsOpen (matrixDomainFor U) := by
  sorry

/-- The dynamics `f(·, u)`, `u ∈ U`, are of class `C¹` on the domain: `⟨Z_u, X⟩ ≠ 0` there.

Proof plan (30–50 lines): as `isC1On_matrixField` (`SmoothedPolygons/Ch6/MatrixSystem.lean`), for
the single control `u`: on the open set `{q | ⟨Z_u, stateX q⟩ ≠ 0}`, which contains the domain,
the entries of `matrixField q u` are rational functions of the coordinates with nonvanishing
denominators (`fun_prop (disch := assumption)`); `ContDiffAt.contDiffWithinAt` pointwise. -/
theorem contDiffOn_matrixField_matrixDomainFor {U : Set (Fin 3 → ℝ)} {u : Fin 3 → ℝ}
    (hu : u ∈ U) : ContDiffOn ℝ 1 (matrixField · u) (matrixDomainFor U) := by
  sorry

/-- The cost `-(3/2)⟨J, X⟩` is smooth (linear in the state).

Proof plan (3–5 lines): as `isC1On_matrixCost`: unfold, `fun_prop`. -/
theorem contDiff_matrixCost (u : Fin 3 → ℝ) : ContDiff ℝ 1 (matrixCost · u) := by
  sorry

/-- A state trajectory for `U` is an admissible pair of the matrix system in `matrixDomainFor U`
with controls in `U`.

Proof plan (60–80 lines): the proof of `IsStateTrajectory.isAdmissibleIn_matrix`
(`SmoothedPolygons/Ch6/MatrixMinimizer.lean`) with `U` for `U_T`: the entrywise integral equations
of `g` and `X` are the integral equation of `q = (g, X)` (`slCoords` picks entries); `det g = 1 > 0`
and the star condition for `U` put `q(t)` in the domain. (The private helpers it uses,
`mxb_eq_add_integral_of_coords` and `continuousOn_Icc_of_eq_add_integral`, are restated or made
public.) -/
theorem IsStateTrajectoryFor.isAdmissibleIn_matrix {U : Set (Fin 3 → ℝ)} {T : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (h : IsStateTrajectoryFor U T u g X) :
    IsAdmissibleIn matrixField (matrixDomainFor U) U (toMatrixState (g 0) (X 0)) T u
      (fun t ↦ toMatrixState (g t) (X t)) := by
  sorry

/-! ### The rotation symmetry -/

/-- The action of a rotation `A` on the state space: `(g, X) ↦ (A g A⁻¹, A X A⁻¹)` (TeX 7911–7917:
"the action on `g` is by inner automorphisms and the rest are given by the adjoint action"). It is
a linear map of `MatrixState`. -/
noncomputable def rotateState (A : Mat2) (q : MatrixState) : MatrixState :=
  toMatrixState (A * stateG q * A⁻¹) (A * stateX q * A⁻¹)

/-- **The dynamics are equivariant under rotations** (the proof of Theorem 9.0.3, TeX 7758–7778:
`X ↦ Ad_A X`, and the transformed quantities satisfy the same equations): if
`Z_{u'} = A Z_u A⁻¹`, then `f(Ad_A q, u') = Ad_A f(q, u)`, i.e.
`(AgA⁻¹)(AXA⁻¹) = A(gX)A⁻¹` and `[P', AXA⁻¹] = A[P, X]A⁻¹` with `P' = A P A⁻¹`.

Proof plan (25–40 lines): `A` is invertible (`det A = 1`); `stateG (rotateState A q) = AgA⁻¹` and
`stateX (rotateState A q) = AXA⁻¹` (`stateX_toMatrixState`, `AXA⁻¹` traceless); `controlP u'
(AXA⁻¹) = A (controlP u X) A⁻¹` since `⟨AZA⁻¹, AXA⁻¹⟩ = ⟨Z, X⟩` (`Matrix.trace_mul_cycle`);
then `Prod.ext` with `Matrix.mul_assoc`, `Matrix.nonsing_inv_mul`. -/
theorem matrixField_rotateState {A : Mat2} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    {u u' : Fin 3 → ℝ} (hu : controlMatrix u' = A * controlMatrix u * A⁻¹) (q : MatrixState) :
    matrixField (rotateState A q) u' = rotateState A (matrixField q u) := by
  sorry

/-- **The cost is invariant under rotations**: `⟨J, AXA⁻¹⟩ = ⟨A⁻¹JA, X⟩ = ⟨J, X⟩` for
`A ∈ SO₂(ℝ)` (Sussmann's condition (ii); the book's Definition 9.1.1 omits it, but its proof of
Theorem 9.1.6 checks the whole Hamiltonian, TeX 7921).

Proof plan (10–15 lines): `A = [[a, -c], [c, a]]` commutes with `J`
(`Matrix.of_mem_specialOrthogonalGroup_fin_two_iff`), and the trace form is invariant under
conjugation. -/
theorem matrixCost_rotateState {A : Mat2} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (q : MatrixState) (u u' : Fin 3 → ℝ) : matrixCost (rotateState A q) u' = matrixCost q u := by
  sorry

/-- **The infinitesimal rotation** `τ(J)(g, X) = (Jg - gJ, [J, X])` (TeX 7931–7943: the derivative
at `θ = 0` of `(e^{θJ} g e^{-θJ}, Ad_{e^{θJ}} X)`). -/
noncomputable def rotationField (q : MatrixState) : MatrixState :=
  toMatrixState (J * stateG q - stateG q * J) (J * stateX q - stateX q * J)

/-- **The rotations are symmetries** (TeX 7918–7925: "These are symmetries by the proof of
Theorem 9.0.3 and also since the rotation action on the control matrix `Z_u` is
`Z_u ↦ Ad_{exp(Jθ)} Z_u ∈ U_C`"): for a compact control set closed under rotations,
`rotationField` is an infinitesimal symmetry of the matrix system in Sussmann's sense (every
`e^{θY}` is a `C¹` diffeomorphism of the domain permuting the controls, with the cost invariant).

Proof plan (150–250 lines): `Pontryagin.isInfinitesimalSymmetry_of_flow` (open domain:
`isOpen_matrixDomainFor`) with the explicit flow `Φ θ = rotateState (expJ θ)`:
* `expJ θ ∈ SO₂(ℝ)`, `(expJ θ)⁻¹ = expJ (-θ)` (`cos² + sin² = 1`), `expJ` commutes with `J`;
* `Φ θ` maps the domain into itself: `det (A g A⁻¹) = det g`, and for `u ∈ U`,
  `⟨Z_u, AXA⁻¹⟩ = ⟨A⁻¹Z_uA, X⟩ = ⟨Z_{u''}, X⟩ < 0` with `u'' ∈ U` given by `hU` for `A⁻¹`;
* `Φ 0 = id` (`rotateState 1 q = q`: `slCoords (slMatrix x) = x`), `Φ (-θ) ∘ Φ θ = id`;
* `∂_θ Φ(θ, q) = rotationField (Φ(θ, q))` (entrywise: `(expJ θ)' = J expJ θ = expJ θ J`);
* `Φ θ` is linear, hence `C¹`, and `fderiv (Φ θ) q = Φ θ` (as a continuous linear map);
* `PermutesFamily`: for `u ∈ U`, `u₁ ∈ U` with `Z_{u₁} = Ad_{expJ θ} Z_u` and `u₂ ∈ U` with
  `Z_{u₂} = Ad_{expJ (-θ)} Z_u` (`hU`); `matrixField_rotateState` and `matrixCost_rotateState`
  give (i) and (ii). -/
theorem isInfinitesimalSymmetry_rotationField {U : Set (Fin 3 → ℝ)} (hU : IsRotationClosed U)
    (hUc : IsCompact U) :
    IsInfinitesimalSymmetry matrixField matrixCost (matrixDomainFor U) U rotationField := by
  sorry

/-- **The momentum map of the rotations** (TeX 7945–7956):
`𝐉^τ(g, X, Λ₁, Λ₂)(J) = ⟨Λ₁, Ad_{g⁻¹}J - J⟩ + ⟨Λ₂, [J, X]⟩ = ⟨Λ₁, Ad_{g⁻¹}J⟩ - ⟨J, Λ₁ + Λ_R⟩`,
for the costates `Λ₁ = covectorΛ₁ q π` (the left-trivialized `g`-part, made traceless) and
`Λ_R = covectorΛR q π` of a covector `π` at `q` with `det g ≠ 0`.

Proof plan (30–50 lines): `π(rotationField q) = π(Jg - gJ, 0) + π(0, slCoords [J, X])`
(linearity); the first term is `tr(p(Jg - gJ))` (`trace_covectorG_mul`), the second
`⟨Λ₂, [J, X]⟩` (`traceForm_covectorΛ₂`, `slMatrix_slCoords` for the traceless `[J, X]`). With
`Λ₁ = pg - (tr(pg)/2) I`: `⟨Λ₁, g⁻¹Jg⟩ = tr(pJg)` (`tr(g⁻¹Jg) = tr J = 0`), `⟨J, Λ₁⟩ = tr(pgJ)`;
and `⟨Λ₂, [J, X]⟩ = -⟨J, [Λ₂, X]⟩ = -⟨J, Λ_R⟩` (`Matrix.trace_mul_cycle`). -/
theorem momentum_rotationField {q : MatrixState} (hq : (stateG q).det ≠ 0)
    (π : StrongDual ℝ MatrixState) :
    momentum rotationField q π =
      traceForm (covectorΛ₁ q π) ((stateG q)⁻¹ * J * stateG q) -
        angularMomentum (covectorΛ₁ q π) (covectorΛR q π) := by
  sorry

/-- **Noether–Sussmann for the rotations**: for a compact control set closed under rotations,
along every admissible pair `(ũ, q)` of the matrix system with a covector curve `p` satisfying the
adjoint equation and the maximum condition (any multiplier `ν`), the momentum `⟨p, τ(J)(q)⟩` is
constant (TeX 7963–7965: "by the Noether–Sussmann theorem").

Proof: `External.noether_sussmann_one_parameter` with `isOpen_matrixDomainFor`,
`contDiffOn_matrixField_matrixDomainFor`, `contDiff_matrixCost` and
`isInfinitesimalSymmetry_rotationField`. -/
theorem momentum_rotationField_eq {U : Set (Fin 3 → ℝ)} (hU : IsRotationClosed U)
    (hUc : IsCompact U) {T ν : ℝ} {ũ : ℝ → Fin 3 → ℝ} {q : ℝ → MatrixState}
    {p : ℝ → StrongDual ℝ MatrixState}
    (href : IsAdmissibleIn matrixField (matrixDomainFor U) U (q 0) T ũ q)
    (hadj : IsAdjoint matrixField matrixCost ν ũ q T p)
    (hmax : IsMaximal matrixField matrixCost ν U ũ q T p) :
    ∀ t ∈ Icc 0 T, momentum rotationField (q t) (p t) = momentum rotationField (q 0) (p 0) :=
  External.noether_sussmann_one_parameter (isOpen_matrixDomainFor hUc)
    (fun _ hu ↦ contDiffOn_matrixField_matrixDomainFor hu)
    (fun u _ ↦ (contDiff_matrixCost u).contDiffOn) (isInfinitesimalSymmetry_rotationField hU hUc)
    href hadj hmax

/-! ### The lift of the reduced costate -/

/-- **The lift of an extremal to the cotangent bundle** (departure from the paper; module
docstring). Every extremal `(g, X, Λ₁, Λ_R)` of Problem 6.7.1 with a compact control set `U` comes
from a covector curve `p` on the matrix system satisfying the adjoint equation and the maximum
condition of the maximum principle (with the same multiplier `λ_cost`), with
`Λ₁ = covectorΛ₁ q p` and `Λ_R = covectorΛR q p` for `q = (g, X)`.

Proof plan (350–500 lines):
1. `Λ₂ := [X, Λ_R]/4 + c X` with `c(t) = ∫₀ᵗ κ`, where
   `κ = (⟨X, D₀⟩ + ⟨[X, [P, X]], Λ_R⟩/4)/2`, `D₀ = Λ₁ - (3/2)λ J + [Λ₂⁰, P] - ⟨[Λ₂⁰, P], X⟩ P` the
   functional derivative `δH/δX` of `fullHamiltonian` at `Λ₂⁰ = [X, Λ_R]/4`; `κ` is bounded and
   measurable on `[0, T]` (`U` compact and `X([0, T])` compact in the open cone, so `⟨Z_u, X⟩` is
   bounded away from `0`; `u` measurable).
2. `p(t)` is the covector `(W, x) ↦ tr(Λ₁ g⁻¹ W) + ⟨Λ₂, slMatrix x⟩` (a continuous linear map
   built from `Matrix.trace` and `slMatrix`); then `covectorG p = Λ₁ g⁻¹`, `covectorΛ₂ p = Λ₂`,
   `covectorΛ₁ q p = Λ₁` (`Λ₁` traceless), and `covectorΛR q p = [Λ₂, X] = Λ_R`, since
   `[[X, Λ_R], X] = 4Λ_R` for `Λ_R ⊥ X` traceless and `det X = 1` (`X² = -I`; `ext`, `ring`).
3. The maximum condition: `controlHamiltonian_matrix_eq_hamiltonian` and step 2 turn it into the
   maximum condition of the extremal (the null sets `{0, T}` aside).
4. The adjoint equation: at almost every `t` (where `g`, `X`, `Λ₁`, `Λ_R`, `c` have the integrands
   as derivatives, Lebesgue's differentiation theorem as in `isIntegralCurve_covectorΛ_of_adjoint`),
   * `g`-part: `(Λ₁ g⁻¹)' = [Λ₁, X] g⁻¹ - Λ₁ g⁻¹ (gX) g⁻¹ = -X Λ₁ g⁻¹`, which is
     `-covectorG(p ∘ ∂f + λ ∂φ)` by `covectorG_comp_fderiv_matrixField` (restated for
     `matrixDomainFor U`: its proof uses only `⟨Z_u, X⟩ ≠ 0`);
   * `X`-part: `D := Λ₂' + δH/δX(Λ₁, Λ₂, X; u)` vanishes: `⟨D, X⟩ = 0` by the choice of `c`
     (`⟨X, X'⟩ = 0`, `⟨X, [X, P]⟩ = 0`, `δH/δX` affine in `Λ₂` with `δH/δX(Λ₂⁰ + cX) =
     δH/δX(Λ₂⁰) + c[X, P]`), and `[D, X] = 0` by the `Λ_R` equation and the identity
     `Λ_R' = [Λ₂', X] + [Λ₂, X']` of the proof of Proposition 6.5.1 (TeX 5071–5085: the `Λ_R`
     right-hand side is `[-δH/δX, X] + [Λ₂, [P, X]]`, an algebraic identity); a traceless `D`
     with `⟨D, X⟩ = 0` and `[D, X] = 0` is `0` when `det X = 1`. With
     `hasFunctionalDerivative_fullHamiltonian` (restated for `matrixDomainFor U`) this is the
     `X`-part of the adjoint equation.
   Then `p` is absolutely continuous (its entries are polynomial in the absolutely continuous
   `g⁻¹ = adj g`, `X`, `Λ₁`, `Λ_R`, `c`), so `p(t) = p(T) + ∫ₜᵀ (p ∘ ∂f + λ ∂φ)`
   (`AbsolutelyContinuousOnInterval.eq_add_integral_of_ae_hasDerivAt`, entrywise through the
   coordinates of `StrongDual ℝ MatrixState`), the integrand being bounded and measurable. -/
theorem IsPontryaginExtremalFor.exists_covector {U : Set (Fin 3 → ℝ)} (hUc : IsCompact U)
    {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremalFor U T u g X Λ₁ ΛR lam) :
    ∃ p : ℝ → StrongDual ℝ MatrixState,
      IsAdjoint matrixField matrixCost lam u (fun t ↦ toMatrixState (g t) (X t)) T p ∧
      IsMaximal matrixField matrixCost lam U u (fun t ↦ toMatrixState (g t) (X t)) T p ∧
      ∀ t ∈ Icc 0 T, covectorΛ₁ (toMatrixState (g t) (X t)) (p t) = Λ₁ t ∧
        covectorΛR (toMatrixState (g t) (X t)) (p t) = ΛR t := by
  sorry

/-! ### Theorem 9.1.6 -/

/-- **Conservation of angular momentum for a rotation-invariant control set** (Theorem 9.1.6 and
Remark 9.1.7 in one statement): for a compact control set `U` closed under rotations, the angular
momentum `𝒜 = ⟨J, Λ₁ + Λ_R⟩` is constant along every Pontryagin extremal of Problem 6.7.1 with
control set `U`.

Proof plan (60–90 lines; the book's proof, TeX 7902–7966, with the lift):
1. `h.exists_covector hUc`: a covector curve `p` with the adjoint equation, the maximum condition,
   `covectorΛ₁ (q t) (p t) = Λ₁ t` and `covectorΛR (q t) (p t) = Λ_R t`, `q t = (g t, X t)`.
2. `h.1.isAdmissibleIn_matrix`: `(u, q)` is admissible in `matrixDomainFor U`.
3. `momentum_rotationField_eq hU hUc` (Noether–Sussmann): `⟨p(t), τ(J)(q(t))⟩` is constant.
4. `momentum_rotationField` (`det g(t) = 1`; `stateG (q t) = g t`, `stateX (q t) = X t`):
   `⟨Λ₁(t), g(t)⁻¹ J g(t)⟩ - 𝒜(t) = ⟨Λ₁(0), g(0)⁻¹ J g(0)⟩ - 𝒜(0)`.
5. Corollary 6.5.3 (`corollary6_5_3`, after FTC-1 for the continuous integrands as in
   `IsStateTrajectory.eq_conj_of_isIntegralCurve`, whose proof uses only `det g = 1` and the two
   integral curves): `Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)`, since `g(0) = I`; hence
   `⟨Λ₁(t), g(t)⁻¹ J g(t)⟩ = tr(g⁻¹ Λ₁(0) J g) = ⟨Λ₁(0), J⟩`, the same at `t = 0`.
6. Subtract: `𝒜(t) = 𝒜(0)`. -/
theorem angularMomentum_conserved {U : Set (Fin 3 → ℝ)} (hU : IsRotationClosed U)
    (hUc : IsCompact U) {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremalFor U T u g X Λ₁ ΛR lam) :
    ∀ t ∈ Icc 0 T, angularMomentum (Λ₁ t) (ΛR t) = angularMomentum (Λ₁ 0) (ΛR 0) := by
  sorry

/-- **Theorem 9.1.6** (`thm:angular-momentum`, TeX 7894–7966; the introduction's theorem*,
TeX 948–952). The angular momentum `𝒜 = ⟨J, Λ₁ + Λ_R⟩` is conserved along every Pontryagin
extremal of the circular control problem (Problem 9.1.5: control set `U_C`).

The book says "along the optimal trajectory"; its proof, and the introduction, give it for every
Pontryagin extremal, which is stated here (module docstring, "Readings").

Proof (the book's, module docstring): `angularMomentum_conserved` for `U_C = U_1`, closed under
rotations (`isRotationClosed_controlDisk`) and compact (`isCompact_controlDisk`). -/
theorem theorem9_1_6 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremalFor controlDiskC T u g X Λ₁ ΛR lam) :
    ∀ t ∈ Icc 0 T, angularMomentum (Λ₁ t) (ΛR t) = angularMomentum (Λ₁ 0) (ΛR 0) :=
  angularMomentum_conserved (isRotationClosed_controlDisk 1) (isCompact_controlDisk 1) h

/-! ### Remark 9.1.7 -/

/-- **Remark 9.1.7**, third item (TeX 7979–7984): "We also obtain the same conserved quantity for
a control set `U_r` which is a disk of any radius `r` whenever `r² > ⅓`." The hypothesis
`r² > ⅓` is not needed (module docstring).

Proof: `angularMomentum_conserved` for `U_r` (`isRotationClosed_controlDisk`,
`isCompact_controlDisk`), the same argument as Theorem 9.1.6. -/
theorem remark9_1_7 (r : ℝ) {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremalFor (controlDisk r) T u g X Λ₁ ΛR lam) :
    ∀ t ∈ Icc 0 T, angularMomentum (Λ₁ t) (ΛR t) = angularMomentum (Λ₁ 0) (ΛR 0) :=
  angularMomentum_conserved (isRotationClosed_controlDisk r) (isCompact_controlDisk r) h

/-- The infinitesimal generator `(g, X) ↦ (-gJ, [J, X])` of the action
`(g, X) ↦ (g e^{-θJ}, Ad_{e^{θJ}} X)` of Remark 9.1.7, second item (TeX 7975–7978: "we could also
modify the action to be `g ↦ g exp(-Jθ)`"). -/
noncomputable def rightRotationField (q : MatrixState) : MatrixState :=
  toMatrixState (-(stateG q * J)) (J * stateX q - stateX q * J)

/-- **Remark 9.1.7**, second item: the momentum of the modified action is `-𝒜`, without the
"spurious constant" `⟨Λ₁, Ad_{g⁻¹}J⟩` (TeX 7975–7978).

Proof plan (15–25 lines): as `momentum_rotationField`: `π(-gJ, 0) = -tr(pgJ) = -⟨Λ₁, J⟩` (`J`
traceless) and `π(0, slCoords [J, X]) = ⟨Λ₂, [J, X]⟩ = -⟨J, Λ_R⟩`. -/
theorem momentum_rightRotationField (q : MatrixState) (π : StrongDual ℝ MatrixState) :
    momentum rightRotationField q π = -angularMomentum (covectorΛ₁ q π) (covectorΛR q π) := by
  sorry

/-- **Remark 9.1.7**, second item: the modified action is by symmetries (`g ↦ g e^{-θJ}` preserves
`det g`, and `(g A⁻¹)(A X A⁻¹) = (gX)A⁻¹`), so `rightRotationField` is an infinitesimal symmetry.

Proof plan (100–150 lines, sharing the lemmas of `isInfinitesimalSymmetry_rotationField`):
`Pontryagin.isInfinitesimalSymmetry_of_flow` with `Φ θ (g, X) = (g expJ(-θ), Ad_{expJ θ} X)`;
the equivariance `f(Φ θ q, u₁) = Φ θ (f(q, u))` for `Z_{u₁} = Ad_{expJ θ} Z_u` (as
`matrixField_rotateState`, with `g ↦ g A⁻¹` on the first factor) and `matrixCost_rotateState`
for the cost. -/
theorem isInfinitesimalSymmetry_rightRotationField {U : Set (Fin 3 → ℝ)}
    (hU : IsRotationClosed U) (hUc : IsCompact U) :
    IsInfinitesimalSymmetry matrixField matrixCost (matrixDomainFor U) U rightRotationField := by
  sorry

/-- **Remark 9.1.7**, second item: with the modified action, the Noether–Sussmann theorem gives the
conservation of `𝒜` directly, along every covector curve with the adjoint equation and the maximum
condition of the matrix system with a compact control set closed under rotations (no appeal to
Corollary 6.5.3). This is the covector form of Theorem 9.1.6 (the shorter route of the module
docstring).

Proof: `External.noether_sussmann_one_parameter` with
`isInfinitesimalSymmetry_rightRotationField`, and `momentum_rightRotationField`. -/
theorem remark9_1_7_rightAction {U : Set (Fin 3 → ℝ)} (hU : IsRotationClosed U)
    (hUc : IsCompact U) {T ν : ℝ} {ũ : ℝ → Fin 3 → ℝ} {q : ℝ → MatrixState}
    {p : ℝ → StrongDual ℝ MatrixState}
    (href : IsAdmissibleIn matrixField (matrixDomainFor U) U (q 0) T ũ q)
    (hadj : IsAdjoint matrixField matrixCost ν ũ q T p)
    (hmax : IsMaximal matrixField matrixCost ν U ũ q T p) :
    ∀ t ∈ Icc 0 T, angularMomentum (covectorΛ₁ (q t) (p t)) (covectorΛR (q t) (p t)) =
      angularMomentum (covectorΛ₁ (q 0) (p 0)) (covectorΛR (q 0) (p 0)) := by
  intro t ht
  have h := External.noether_sussmann_one_parameter (isOpen_matrixDomainFor hUc)
    (fun _ hu ↦ contDiffOn_matrixField_matrixDomainFor hu)
    (fun u _ ↦ (contDiff_matrixCost u).contDiffOn)
    (isInfinitesimalSymmetry_rightRotationField hU hUc) href hadj hmax t ht
  rwa [momentum_rightRotationField, momentum_rightRotationField, neg_inj] at h

end SmoothedPolygons
