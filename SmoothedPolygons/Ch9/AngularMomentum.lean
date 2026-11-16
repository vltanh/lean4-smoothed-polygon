module

public import SmoothedPolygons.Ch9.ControlSets
public import SmoothedPolygons.Ch6.MatrixExtremal
public import SmoothedPolygons.Ch8.Defs
public import External.NoetherSussmann

/-!
# §9.1: the circular control problem and the conservation of angular momentum

Hales–Vajjha, *Packings of Smoothed Polygons*, §9.1 "Conserved Quantity for the Circular Control
Set" (TeX 7792–7999), and the introduction's restatement (theorem*, TeX 948–952: "In the control
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
  `angularMomentum_conserved` for a compact control set closed under rotations, which assumes only
  the state–costate equations and the maximum condition (no boundary conditions).
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
5. The lift (`IsStateTrajectoryFor.exists_covector`; see the departure below): every solution
   `(g, X, Λ₁, Λ_R)` of the state–costate equations with the maximum condition comes from such a
   covector curve `p`, with `Λ₁ = covectorΛ₁ q p` and `Λ_R = covectorΛR q p`.
6. Corollary 6.5.3 for the first term, and the conclusion (`angularMomentum_conserved`). The
   corollary is applied to `ĝ = g(0)⁻¹ g` (`ĝ' = ĝ X`, `ĝ(0) = I`), which gives
   `g Λ₁ g⁻¹ = g(0) Λ₁(0) g(0)⁻¹` without assuming `g(0) = I`.

## Readings

* **`U_C`** is the disk `U_1` (`controlDiskC`; the printed formula is `U_T`,
  `SmoothedPolygons/Ch9/ControlSets.lean`).
* **The state space of the circular problem.** Problem 9.1.5 does not say where the dynamics are
  defined. The introduction's footnote (TeX 912–919) says that the relaxed problem "is defined on
  a smaller domain" than Problem 3.6.2, but the book never specifies that domain.
  `P = Z_u/⟨Z_u, X⟩` must be defined for every `u ∈ U_C` (the Hamiltonian is maximized over all
  of `U_C`, and the regularity of §6.2 that the Noether–Sussmann theorem assumes needs it), so the
  state space of `X` is the set of star states for `U_C` (`IsStarStateFor`): `det X = 1` and
  `⟨Z_u, X⟩ < 0` for all `u ∈ U_C`, a set smaller than the star domain of Problem 3.6.2
  (`IsStarStateFor.isStarState`). In the upper half-plane it is the hyperbolic disk
  `√3(1 + |z|²) < 4 Im z` about `i`, of radius `arccosh(2/√3)` (`isStarStateFor_controlDiskC_Φ`).
  The sign `< 0` is that of Lemma 3.3.4 on `U_T ⊆ U_C`: since `U_C` is connected, `⟨Z_u, X⟩ ≠ 0`
  on `U_C` allows only this sign or `⟨Z_u, X⟩ > 0` on all of `U_C`, which no star state of
  Problem 3.6.2 satisfies.
* **Chapter 10's competing convention** (TeX 8531–8547) imposes the star condition only at the
  optimal control, `⟨X, Z*⟩ < 0`, on "a region slightly larger than the star domain". It is not
  taken here: the Noether–Sussmann theorem needs every `f(·, u)`, `u ∈ U_C`, to be `C¹` on an open
  domain, and where `⟨X, Z_u⟩` changes sign on `U_C` the term `-⟨Λ_R, Z_u⟩/⟨X, Z_u⟩` of the
  Hamiltonian is unbounded near the zeros of the denominator, so the maximum of `H` over `U_C` is
  in general `+∞`.
* **"Along the optimal trajectory"** (TeX 7896) is read as "along every Pontryagin extremal", as
  the proof gives and the introduction states (TeX 948–952). Optimality is not used, and the
  existence of an optimal control for `U_C` is not established in the book: the introduction's
  footnote (TeX 912–919) says that the compactification of Chapter 5 is not extended to the
  relaxed problem. (Convexity is not the obstacle: `u ↦ Z_u/⟨Z_u, X⟩` is a perspective map, so it
  keeps the disk convex, and the velocity sets of the circular problem are convex.) The stronger
  form is stated; it is stronger than the book's given the maximum principle for `U_C`, which
  makes optimal trajectories extremals and is not formalized for `U_C`.
* **The extremals of the circular problem** are those of Problem 6.7.1, the reduced costate
  `(Λ₁, Λ_R)` with the conditions of the maximum principle and the transversality conditions,
  with `U_T` replaced by `U_C` throughout (the maximum condition over `U_C`, the controls in
  `U_C`, the star states for `U_C`): `IsPontryaginExtremalFor controlDiskC`.
* **Local solutions.** The conservation law (`angularMomentum_conserved`) assumes only what its
  proof uses: the state trajectory, the two costate equations, `Λ₁, Λ_R ∈ 𝔰𝔩₂(ℝ)`, `Λ_R ⊥ X` and
  the maximum condition; not the transversality conditions, `g(0) = I`, `H = 0`, `λ_cost ≤ 0` or
  nontriviality. §9.3 (TeX 8136–8295: the derivative of `𝒜`, TeX 8183–8196, and the constraint on
  the optimal control, TeX 8285–8295) and Chapter 10 (TeX 8684–8689, 8945–8946) apply the
  conservation along such local solutions of the state–costate equations with `U = U_r`.
  Theorem 9.1.6 and Remark 9.1.7 are its corollaries for the extremals of Problem 9.1.5
  (`theorem9_1_6`, `remark9_1_7`).
* **`SL₂(ℝ)`** is replaced by the open set `GL₂⁺(ℝ)` of `Mat₂(ℝ)`, as in Chapter 6 (the reading D1
  of `External/Pontryagin.lean`; the Noether–Sussmann theorem is formalized on open subsets of a
  finite-dimensional space, S1 of the OptimalControl package); `det g = 1` along the extremals.
* **The Lie algebra** `𝔰𝔬₂(ℝ) = ℝJ` is one-dimensional, so the book's momentum map
  `𝐉^τ(q, p)(aJ) = a ⟨p, τ(J)(q)⟩` is constant if and only if the momentum of the one field
  `τ(J) = rotationField` is; the one-parameter form of the theorem is applied.
* **The Noether–Sussmann theorem** is applied in Sussmann's form, whose symmetries preserve the
  cost (`External.noether_sussmann_one_parameter`), not in the printed form, which is false
  (`noetherSussmann_false_as_printed`). The rotations preserve the cost `-(3/2)⟨J, X⟩`
  (`matrixCost_rotateState`), as the book's appeal to "the proof of Theorem 9.0.3"
  (TeX 7921–7922) checks for the whole Hamiltonian.
* **Remark 9.1.7**, third item: "whenever `r² > ⅓`". The conservation holds for every `r`
  (`remark9_1_7` has no hypothesis on `r`); for `r² < ⅓` the disk is empty and there are no
  extremals, for `r² = ⅓` it is the centroid.

## Departure from the paper

**The lift of the reduced costate** (`IsStateTrajectoryFor.exists_covector`). The book's proof
works with the full costate `(Λ₁, Λ₂)` of `T*(T SL₂(ℝ))`, the covector to which the
Noether–Sussmann theorem applies. The extremals of Problem 6.7.1, as formalized
(`IsPontryaginExtremal`, and here `IsPontryaginExtremalFor`), carry only the reduced costate
`(Λ₁, Λ_R)`, `Λ_R = [Λ₂, X]`, which determines `Λ₂` up to a multiple of `X`. The lift reconstructs
a covector curve: `Λ₂ = [X, Λ_R]/4 + c X` (since `[[X, Λ_R], X] = 4Λ_R` for `Λ_R ⊥ X`,
`det X = 1`), with `c = ∫ κ`, `κ = (⟨Λ₁ - (3/2)λ_cost J, X⟩ + ⟨X', [Λ_R, X]⟩/4)/2`, chosen so that
`Λ₂` satisfies the `X`-part of Hamilton's equations (its component along `X`; the rest follows
from the `Λ_R` equation); the `g`-part is `p = Λ₁ g⁻¹`. The book does not need this step, since
its extremals are lifted trajectories in the cotangent bundle; the conserved quantity does not
depend on `c` (`[X, X] = 0`).

## Shorter routes (documented, not taken)

* **Remark 9.1.7, second item**: the action `g ↦ g e^{-θJ}`, `X ↦ Ad_{e^{θJ}} X` has momentum
  `-𝒜` exactly (`momentum_rightRotationField`), with no term `⟨Λ₁, Ad_{g⁻¹}J⟩`, so Corollary 6.5.3
  is not needed (`remark9_1_7_rightAction`).
* **Without Noether or the lift**: by the costate equations, `𝒜' = ⟨J, [P, Λ_R] - ⟨Λ_R, P⟩[P, X]⟩`
  almost everywhere (`⟨J, [J, X]⟩ = 0`, and the `[Λ₁, X]` terms cancel), and this is
  `-d/dθ H(Λ₁, Λ_R, X; Ad_{e^{θJ}} Z_u)` at `θ = 0`, which vanishes at a maximizer `u` of `H` over
  a rotation-closed `U` (Theorem 9.0.3: the rotated controls stay in `U`). An absolutely continuous
  function with zero derivative almost everywhere is constant. This is Noether's argument
  specialized to the matrix form, about 100–150 lines, and needs neither the lift (step 5, about
  700 lines with its helpers) nor the infinitesimal-symmetry machinery (step 2, about 200).
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

Proof: `lemma3_3_4` turns `0 < ρ₀ X ∧ 0 < ρ₁ X ∧ 0 < ρ₂ X` into the condition on `U_T`. -/
theorem isStarStateFor_controlSimplex_iff (X : Mat2) :
    IsStarStateFor controlSimplex X ↔ IsStarState X := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, h1, (lemma3_3_4 X h0).2 h2⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, h1, (lemma3_3_4 X h0).1 h2⟩

/-- For a control set containing `U_T` (such as `U_C`), the star states for `U` are star states:
the state space of the circular problem lies in that of Problem 3.6.2.

Proof: restrict the condition to `U_T` and apply `isStarStateFor_controlSimplex_iff`. -/
theorem IsStarStateFor.isStarState {U : Set (Fin 3 → ℝ)} (hU : controlSimplex ⊆ U) {X : Mat2}
    (hX : IsStarStateFor U X) : IsStarState X :=
  (isStarStateFor_controlSimplex_iff X).1 ⟨hX.1, hX.2.1, fun u hu ↦ hX.2.2 u (hU hu)⟩

/-- **The state space of the circular problem in the upper half-plane**: `Φ(x + iy)` is a star
state for `U_C` exactly when `√3(1 + x² + y²) < 4y`, i.e. `cosh d(z, i) < 2/√3` for the hyperbolic
distance `d`. In particular `J = Φ(i)` is one, and `Φ(2i)` (a star state of Problem 3.6.2) is not.

Proof: on the plane `Σuᵢ = 1`, write `s₀ = u₀ - ⅓`, `s₁ = (u₁ - u₂)/√3`; then `U_C` is the disk
`s₀² + s₁² ≤ (⅔)²` (`Σuᵢ² = ⅓ + (3/2)(s₀² + s₁²)`), and with `r = x² + y²`,
`y ⟨Z_u, Φ⟩ = 2x s₁ + (1 - r) s₀ - (1 + r)/3`. Its maximum over the disk is
`(⅔)√(4x² + (1 - r)²) - (1 + r)/3` (Cauchy–Schwarz, attained), and
`4x² + (1 - r)² = (1 + r)² - 4y²`, so the maximum is negative iff `3(1 + r)² < 16y²`. `det Φ = 1`
and `tr Φ = 0` by `ring`/`field_simp`. -/
theorem isStarStateFor_controlDiskC_Φ {x y : ℝ} (hy : 0 < y) :
    IsStarStateFor controlDiskC (Φ x y) ↔ √3 * (1 + x ^ 2 + y ^ 2) < 4 * y := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  set r := x ^ 2 + y ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  -- `y ⟨Z_u, Φ(x + iy)⟩ = 2x s₁ + (1 - r) s₀ - (1 + r)/3`, `s₀ = u₀ - ⅓`, `s₁ = (u₁ - u₂)/√3`
  have key : ∀ u : Fin 3 → ℝ, u 0 + u 1 + u 2 = 1 → y * traceForm (controlMatrix u) (Φ x y) =
      2 * x * ((u 1 - u 2) / √3) + (1 - r) * (u 0 - 1 / 3) - (1 + r) / 3 := by
    intro u hu
    have hu2 : u 2 = 1 - u 0 - u 1 := by linarith
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, controlMatrix,
      Φ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, hr, hu2]
    field_simp
    ring
  -- `Σuᵢ² = ⅓ + (3/2)(s₀² + s₁²)`
  have hsq : ∀ u : Fin 3 → ℝ, u 0 + u 1 + u 2 = 1 → u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 =
      1 / 3 + 3 / 2 * ((u 0 - 1 / 3) ^ 2 + ((u 1 - u 2) / √3) ^ 2) := by
    intro u hu
    rw [div_pow, h3, show u 2 = 1 - u 0 - u 1 by linarith]
    ring
  have htr : (Φ x y).trace = 0 := by simp [Φ, Matrix.trace_fin_two]; ring
  have hdet : (Φ x y).det = 1 := by
    simp only [Φ, Matrix.det_fin_two_of]; field_simp; ring
  -- `4x² + (1 - r)² = (1 + r)² - 4y²`
  have hN2 : 4 * x ^ 2 + (1 - r) ^ 2 = (1 + r) ^ 2 - 4 * y ^ 2 := by rw [hr]; ring
  -- the condition squared: `3(1 + r)² < 16y²`
  have hiff : √3 * (1 + r) < 4 * y ↔ 3 * (1 + r) ^ 2 < 16 * y ^ 2 := by
    rw [← pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero, mul_pow, mul_pow, h3]
    norm_num
  have hcond : √3 * (1 + x ^ 2 + y ^ 2) = √3 * (1 + r) := by rw [hr, add_assoc]
  rw [hcond, hiff]
  constructor
  · rintro ⟨-, -, h⟩
    set N := √(4 * x ^ 2 + (1 - r) ^ 2) with hNdef
    have hNsq : N ^ 2 = 4 * x ^ 2 + (1 - r) ^ 2 := Real.sq_sqrt (by positivity)
    rcases (show (0 : ℝ) ≤ N from Real.sqrt_nonneg _).eq_or_lt with hN | hN
    · -- `x = 0`, `r = 1`, `y = 1`
      rw [← hN] at hNsq
      nlinarith
    -- the control maximizing `⟨Z_u, Φ⟩` on `U_C`
    set s₀ := 2 * (1 - r) / (3 * N) with hs₀
    set s₁ := 4 * x / (3 * N) with hs₁
    set u : Fin 3 → ℝ := ![1 / 3 + s₀, (2 / 3 - s₀ + √3 * s₁) / 2, (2 / 3 - s₀ - √3 * s₁) / 2]
    have hsum : u 0 + u 1 + u 2 = 1 := by simp [u]; ring
    have hs : (u 1 - u 2) / √3 = s₁ := by simp [u]; field_simp; ring
    have hss : s₀ ^ 2 + s₁ ^ 2 = 4 / 9 := by
      rw [hs₀, hs₁, div_pow, div_pow, ← add_div, div_eq_iff (by positivity)]
      linear_combination (-4 : ℝ) * hNsq
    have hu : u ∈ controlDiskC := by
      refine ⟨hsum, ?_⟩
      rw [hsq u hsum, hs]
      simp only [u, Matrix.cons_val_zero, add_sub_cancel_left, hss]
      norm_num
    have hk := key u hsum
    rw [hs] at hk
    simp only [u, Matrix.cons_val_zero, add_sub_cancel_left] at hk
    have hL : 2 * x * s₁ + (1 - r) * s₀ = 2 * N / 3 := by
      rw [hs₀, hs₁]
      field_simp
      nlinarith [hNsq]
    have hneg : y * traceForm (controlMatrix u) (Φ x y) < 0 := mul_neg_of_pos_of_neg hy (h u hu)
    have h2N : 2 * N < 1 + r := by linarith
    nlinarith
  · intro h
    refine ⟨htr, hdet, fun u hu ↦ ?_⟩
    obtain ⟨hsum, hle⟩ := hu
    have hu2 := hsq u hsum
    have hk := key u hsum
    set s₀ := u 0 - 1 / 3
    set s₁ := (u 1 - u 2) / √3
    have hss : s₀ ^ 2 + s₁ ^ 2 ≤ 4 / 9 := by rw [one_pow] at hle; linarith
    -- Cauchy–Schwarz: `(2x s₁ + (1 - r) s₀)² ≤ (4x² + (1 - r)²)(s₀² + s₁²) < ((1 + r)/3)²`
    have hCS : (2 * x * s₁ + (1 - r) * s₀) ^ 2 ≤ (4 * x ^ 2 + (1 - r) ^ 2) * (s₀ ^ 2 + s₁ ^ 2) := by
      nlinarith [sq_nonneg (2 * x * s₀ - (1 - r) * s₁)]
    have hlt : (2 * x * s₁ + (1 - r) * s₀) ^ 2 < ((1 + r) / 3) ^ 2 := by
      have h0 : 0 ≤ 4 * x ^ 2 + (1 - r) ^ 2 := by positivity
      calc _ ≤ (4 * x ^ 2 + (1 - r) ^ 2) * (s₀ ^ 2 + s₁ ^ 2) := hCS
        _ ≤ (4 * x ^ 2 + (1 - r) ^ 2) * (4 / 9) := mul_le_mul_of_nonneg_left hss h0
        _ < ((1 + r) / 3) ^ 2 := by rw [hN2]; nlinarith
    have hL : 2 * x * s₁ + (1 - r) * s₀ < (1 + r) / 3 :=
      abs_lt_of_sq_lt_sq' hlt (by positivity) |>.2
    have : y * traceForm (controlMatrix u) (Φ x y) < 0 := by rw [hk]; linarith
    exact neg_of_mul_neg_right this hy.le

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

/-- For `U = U_T`, the state trajectories for `U` are the state trajectories of Problem 3.6.2.

Proof: the definitions differ only in the star states (`isStarStateFor_controlSimplex_iff`). -/
theorem isStateTrajectoryFor_controlSimplex_iff {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} :
    IsStateTrajectoryFor controlSimplex T u g X ↔ IsStateTrajectory T u g X := by
  simp only [IsStateTrajectoryFor, IsStateTrajectory, isStarStateFor_controlSimplex_iff]

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

Proof: the conditions coincide term by term except the state trajectory, which agrees by
`isStateTrajectoryFor_controlSimplex_iff`. -/
theorem isPontryaginExtremalFor_controlSimplex_iff {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} :
    IsPontryaginExtremalFor controlSimplex T u g X Λ₁ ΛR lam ↔
      IsPontryaginExtremal T u g X Λ₁ ΛR lam := by
  simp only [IsPontryaginExtremalFor, IsPontryaginExtremal,
    isStateTrajectoryFor_controlSimplex_iff]

/-- **The angular momentum** `𝒜 = ⟨J, Λ₁ + Λ_R⟩` (TeX 7887–7889). -/
noncomputable def angularMomentum (Λ₁ ΛR : Mat2) : ℝ := traceForm J (Λ₁ + ΛR)

/-! ### The matrix system with control set `U` -/

/-- The open set of the matrix system for the control set `U`: `det g > 0` and `X` in the open
cone `⟨Z_u, X⟩ < 0` for all `u ∈ U` (Chapter 6's `matrixDomain` for `U = U_T`,
`matrixDomainFor_controlSimplex`). The star states for `U` are its points with `det X = 1`. -/
def matrixDomainFor (U : Set (Fin 3 → ℝ)) : Set MatrixState :=
  {q | 0 < (stateG q).det ∧ ∀ u ∈ U, traceForm (controlMatrix u) (stateX q) < 0}

/-- For `U = U_T`, the open set is Chapter 6's `GL₂⁺(ℝ) × C`.

Proof: Lemma 3.3.4 (`lemma3_3_4`) for the traceless `stateX q`. -/
theorem matrixDomainFor_controlSimplex : matrixDomainFor controlSimplex = matrixDomain := by
  ext q
  simp only [matrixDomainFor, matrixDomain, Set.mem_ofPred_eq,
    lemma3_3_4 (stateX q) (trace_slMatrix _)]

/-- For a compact control set the domain is open.

Proof: `det ∘ stateG` is continuous; for the cone, `(q, u) ↦ ⟨Z_u, stateX q⟩` is continuous, so
by the tube lemma (`IsCompact.eventually_forall_of_forall_eventually`) the strict inequality
`< 0` at `q₀` for all `u ∈ U` persists on a neighbourhood of `q₀`. -/
theorem isOpen_matrixDomainFor {U : Set (Fin 3 → ℝ)} (hU : IsCompact U) :
    IsOpen (matrixDomainFor U) := by
  have hc : Continuous fun q : MatrixState ↦ (stateG q).det := by
    simp only [stateG, Matrix.det_fin_two, Matrix.of_apply]; fun_prop
  have hF : Continuous fun p : MatrixState × (Fin 3 → ℝ) ↦
      traceForm (controlMatrix p.2) (stateX p.1) := by
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      controlMatrix, stateX, slMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    fun_prop
  change IsOpen ({q | 0 < (stateG q).det} ∩
    {q | ∀ u ∈ U, traceForm (controlMatrix u) (stateX q) < 0})
  refine (isOpen_lt continuous_const hc).inter (isOpen_iff_mem_nhds.2 fun q hq ↦ ?_)
  exact hU.eventually_forall_of_forall_eventually fun v hv ↦
    hF.continuousAt.eventually_lt continuousAt_const (hq v hv)

/-- The dynamics `f(·, u)` are smooth near every state with `⟨Z_u, X⟩ ≠ 0` (the computation of
`isC1On_matrixField`, `SmoothedPolygons/Ch6/MatrixSystem.lean`, for one control): the entries of
`matrixField q u` are rational functions of the coordinates with nonvanishing denominators. -/
theorem contDiffAt_matrixField {q : MatrixState} {u : Fin 3 → ℝ}
    (hD : traceForm (controlMatrix u) (stateX q) ≠ 0) : ContDiffAt ℝ 1 (matrixField · u) q := by
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    controlMatrix, stateX, slMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at hD
  refine ContDiffAt.prodMk ?_ ?_
  · refine contDiffAt_pi.2 fun i ↦ contDiffAt_pi.2 fun j ↦ ?_
    fin_cases i <;> fin_cases j <;>
      simp only [stateG, stateX, slMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
      fun_prop
  · refine contDiffAt_pi.2 fun k ↦ ?_
    fin_cases k <;>
      simp only [slCoords, controlP, traceForm, Matrix.trace_fin_two, Matrix.sub_apply,
        Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two, controlMatrix,
        stateX, slMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
        Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons] <;>
      fun_prop (disch := assumption)

/-- The dynamics `f(·, u)`, `u ∈ U`, are of class `C¹` on the domain: `⟨Z_u, X⟩ ≠ 0` there.

Proof: `contDiffAt_matrixField` at every point. -/
theorem contDiffOn_matrixField_matrixDomainFor {U : Set (Fin 3 → ℝ)} {u : Fin 3 → ℝ}
    (hu : u ∈ U) : ContDiffOn ℝ 1 (matrixField · u) (matrixDomainFor U) :=
  fun _ hq ↦ (contDiffAt_matrixField (hq.2 u hu).ne).contDiffWithinAt

/-- The cost `-(3/2)⟨J, X⟩` is smooth (linear in the state).

Proof: as `isC1On_matrixCost`: unfold, `fun_prop`. -/
theorem contDiff_matrixCost (u : Fin 3 → ℝ) : ContDiff ℝ 1 (matrixCost · u) := by
  simp only [matrixCost, traceForm, J, stateX, slMatrix, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  fun_prop

/-- A curve in `MatrixState` is in integral form if its coordinates are (as the private
`mxb_eq_add_integral_of_coords` of `SmoothedPolygons/Ch6/MatrixMinimizer.lean`). -/
private lemma am_eq_add_integral_of_coords {T : ℝ} (hT : 0 ≤ T) {x v : ℝ → MatrixState}
    (hg : ∀ i j, IntervalIntegrable (fun s ↦ (v s).1 i j) volume 0 T ∧
      ∀ t ∈ Icc 0 T, (x t).1 i j = (x 0).1 i j + ∫ s in (0 : ℝ)..t, (v s).1 i j)
    (hX : ∀ k, IntervalIntegrable (fun s ↦ (v s).2 k) volume 0 T ∧
      ∀ t ∈ Icc 0 T, (x t).2 k = (x 0).2 k + ∫ s in (0 : ℝ)..t, (v s).2 k) :
    IntervalIntegrable v volume 0 T ∧ ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, v s := by
  have hv : IntervalIntegrable v volume 0 T :=
    ⟨(Integrable.of_eval fun i ↦ Integrable.of_eval fun j ↦ (hg i j).1.1).prodMk
        (Integrable.of_eval fun k ↦ (hX k).1.1),
      (Integrable.of_eval fun i ↦ Integrable.of_eval fun j ↦ (hg i j).1.2).prodMk
        (Integrable.of_eval fun k ↦ (hX k).1.2)⟩
  refine ⟨hv, fun t ht ↦ ?_⟩
  have hvt : IntervalIntegrable v volume 0 t := hv.mono_set (by
    rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
  refine Prod.ext (funext fun i ↦ funext fun j ↦ ?_) (funext fun k ↦ ?_)
  · have e := (((ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))).comp
      (ContinuousLinearMap.fst ℝ (Fin 2 → Fin 2 → ℝ) (Fin 3 → ℝ))).intervalIntegral_comp_comm hvt
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.proj_apply] at e
    rw [(hg i j).2 t ht, e]
    rfl
  · have e := ((ContinuousLinearMap.proj k : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.snd ℝ (Fin 2 → Fin 2 → ℝ) (Fin 3 → ℝ))).intervalIntegral_comp_comm hvt
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.proj_apply] at e
    rw [(hX k).2 t ht, e]
    rfl

/-- A state trajectory for `U` is an admissible pair of the matrix system in `matrixDomainFor U`
with controls in `U`.

Proof: the proof of `IsStateTrajectory.isAdmissibleIn_matrix`
(`SmoothedPolygons/Ch6/MatrixMinimizer.lean`) with `U` for `U_T`: the entrywise integral equations
of `g` and `X` are the integral equation of `q = (g, X)` (`slCoords` picks entries); `det g = 1 > 0`
and the star condition for `U` put `q(t)` in the domain. -/
theorem IsStateTrajectoryFor.isAdmissibleIn_matrix {U : Set (Fin 3 → ℝ)} {T : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (h : IsStateTrajectoryFor U T u g X) :
    IsAdmissibleIn matrixField (matrixDomainFor U) U (toMatrixState (g 0) (X 0)) T u
      (fun t ↦ toMatrixState (g t) (X t)) := by
  obtain ⟨hT, hmeas, hU, hstate, hgI, hXI⟩ := h
  have hXq : ∀ t ∈ Icc 0 T, stateX (toMatrixState (g t) (X t)) = X t := fun t ht ↦
    stateX_toMatrixState _ (hstate t ht).2.1
  -- the matrix field along the pair: `(gX, slCoords [P, X])`
  have hv : ∀ s ∈ Icc 0 T, matrixField (toMatrixState (g s) (X s)) (u s) =
      (fun i j ↦ (g s * X s) i j,
        slCoords (controlP (u s) (X s) * X s - X s * controlP (u s) (X s))) := by
    intro s hs
    simp only [matrixField, hXq s hs, stateG_toMatrixState]
  -- the coordinates of `slCoords M` are entries of `M`
  have hsl : ∀ k : Fin 3, ∃ a b : Fin 2, ∀ M : Mat2, slCoords M k = M a b := by
    intro k
    fin_cases k
    exacts [⟨0, 0, fun _ ↦ rfl⟩, ⟨0, 1, fun _ ↦ rfl⟩, ⟨1, 0, fun _ ↦ rfl⟩]
  have hint := am_eq_add_integral_of_coords (x := fun t ↦ toMatrixState (g t) (X t))
    (v := fun s ↦ matrixField (toMatrixState (g s) (X s)) (u s)) hT.le ?_ ?_
  · refine ⟨⟨hmeas, hU, continuousOn_Icc_of_eq_add_integral hT.le hint.1 hint.2, hint.1,
      hint.2⟩, fun t ht ↦ ⟨?_, fun v hv ↦ ?_⟩⟩
    · rw [stateG_toMatrixState, (hstate t ht).1]; exact one_pos
    · rw [hXq t ht]; exact (hstate t ht).2.2.2 v hv
  · intro i j
    refine ⟨(intervalIntegrable_congr fun s hs ↦ ?_).2 (hgI i j).1, fun t ht ↦ ?_⟩
    · rw [uIoc_of_le hT.le] at hs
      simp only [hv s (Ioc_subset_Icc_self hs)]
    · change g t i j = g 0 i j + _
      rw [(hgI i j).2 t ht]
      congr 1
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      rw [uIcc_of_le ht.1] at hs
      simp only [hv s ⟨hs.1, hs.2.trans ht.2⟩]
  · intro k
    obtain ⟨a, b, hab⟩ := hsl k
    refine ⟨(intervalIntegrable_congr fun s hs ↦ ?_).2 (hXI a b).1, fun t ht ↦ ?_⟩
    · rw [uIoc_of_le hT.le] at hs
      simp only [hv s (Ioc_subset_Icc_self hs), hab]
    · change slCoords (X t) k = slCoords (X 0) k + _
      rw [hab, hab, (hXI a b).2 t ht]
      congr 1
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      rw [uIcc_of_le ht.1] at hs
      simp only [hv s ⟨hs.1, hs.2.trans ht.2⟩, hab]

/-! ### The rotation symmetry -/

/-- The action of a rotation `A` on the state space: `(g, X) ↦ (A g A⁻¹, A X A⁻¹)` (TeX 7918–7919:
"the action on `g` is by inner automorphisms and the rest are given by the adjoint action"). It is
a linear map of `MatrixState`. -/
noncomputable def rotateState (A : Mat2) (q : MatrixState) : MatrixState :=
  toMatrixState (A * stateG q * A⁻¹) (A * stateX q * A⁻¹)

/-- A matrix of `SO₂(ℝ)` is a unit. -/
private lemma am_isUnit_det {A : Mat2} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    IsUnit A.det := by
  rw [(Matrix.mem_specialOrthogonalGroup_iff.1 hA).2]; exact isUnit_one

/-- A matrix of `SO₂(ℝ)` commutes with `J`. -/
private lemma am_commute_J {A : Mat2} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    A * J = J * A := by
  rw [Matrix.eta_fin_two A, Matrix.of_mem_specialOrthogonalGroup_fin_two_iff] at hA
  obtain ⟨h1, h2, -⟩ := hA
  rw [Matrix.eta_fin_two A]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, h1, h2]

/-- Conjugation preserves the trace. -/
private lemma am_trace_conj {A : Mat2} (hA : IsUnit A.det) (M : Mat2) :
    (A * M * A⁻¹).trace = M.trace := by
  rw [Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]

/-- Conjugation preserves the trace form. -/
private lemma am_traceForm_conj {A : Mat2} (hA : IsUnit A.det) (M N : Mat2) :
    traceForm (A * M * A⁻¹) (A * N * A⁻¹) = traceForm M N := by
  rw [traceForm, traceForm, show A * M * A⁻¹ * (A * N * A⁻¹) = A * (M * N) * A⁻¹ by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹ A, Matrix.nonsing_inv_mul _ hA,
      Matrix.one_mul], am_trace_conj hA]

/-- **Equivariance of the dynamics** under `(g, X) ↦ (B g A⁻¹, A X A⁻¹)` with
`Z_{u'} = A Z_u A⁻¹`: `B g A⁻¹ A X A⁻¹ = B (g X) A⁻¹` and `P' = A P A⁻¹`. -/
private lemma am_matrixField_conj {A B : Mat2} (hA : IsUnit A.det) {u u' : Fin 3 → ℝ}
    (hu : controlMatrix u' = A * controlMatrix u * A⁻¹) (q : MatrixState) :
    matrixField (toMatrixState (B * stateG q * A⁻¹) (A * stateX q * A⁻¹)) u' =
      toMatrixState (B * stateG (matrixField q u) * A⁻¹)
        (A * stateX (matrixField q u) * A⁻¹) := by
  have hXt : (A * stateX q * A⁻¹).trace = 0 := by rw [am_trace_conj hA]; exact trace_slMatrix _
  have hP : controlP u' (A * stateX q * A⁻¹) = A * controlP u (stateX q) * A⁻¹ := by
    rw [controlP, controlP, hu, am_traceForm_conj hA, Matrix.mul_smul, Matrix.smul_mul]
  have hc : stateX (matrixField q u) =
      controlP u (stateX q) * stateX q - stateX q * controlP u (stateX q) :=
    slMatrix_slCoords (by rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self])
  have hg : stateG (matrixField q u) = stateG q * stateX q := by
    ext i j; rfl
  have hAA : ∀ M N : Mat2, A * M * A⁻¹ * (A * N * A⁻¹) = A * (M * N) * A⁻¹ := fun M N ↦ by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹ A, Matrix.nonsing_inv_mul _ hA,
      Matrix.one_mul]
  have hBA : B * stateG q * A⁻¹ * (A * stateX q * A⁻¹) = B * (stateG q * stateX q) * A⁻¹ := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹ A, Matrix.nonsing_inv_mul _ hA,
      Matrix.one_mul]
  refine Prod.ext ?_ ?_
  · funext i j
    change (stateG (toMatrixState (B * stateG q * A⁻¹) (A * stateX q * A⁻¹)) *
      stateX (toMatrixState (B * stateG q * A⁻¹) (A * stateX q * A⁻¹))) i j =
      (B * stateG (matrixField q u) * A⁻¹) i j
    rw [stateG_toMatrixState, stateX_toMatrixState _ hXt, hg, hBA]
  · change slCoords (controlP u' (stateX (toMatrixState (B * stateG q * A⁻¹)
      (A * stateX q * A⁻¹))) * stateX (toMatrixState (B * stateG q * A⁻¹) (A * stateX q * A⁻¹)) -
      stateX (toMatrixState (B * stateG q * A⁻¹) (A * stateX q * A⁻¹)) *
      controlP u' (stateX (toMatrixState (B * stateG q * A⁻¹) (A * stateX q * A⁻¹)))) =
      slCoords (A * stateX (matrixField q u) * A⁻¹)
    rw [stateX_toMatrixState _ hXt, hP, hc, hAA, hAA, ← Matrix.sub_mul, ← Matrix.mul_sub]

/-- **The cost is invariant** under `(g, X) ↦ (B g A⁻¹, A X A⁻¹)`, `A ∈ SO₂(ℝ)`. -/
private lemma am_matrixCost_conj {A B : Mat2} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (q : MatrixState) (u u' : Fin 3 → ℝ) :
    matrixCost (toMatrixState (B * stateG q * A⁻¹) (A * stateX q * A⁻¹)) u' = matrixCost q u := by
  have hA' := am_isUnit_det hA
  have hXt : (A * stateX q * A⁻¹).trace = 0 := by rw [am_trace_conj hA']; exact trace_slMatrix _
  have hJ : A * J * A⁻¹ = J := by
    rw [am_commute_J hA, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA', Matrix.mul_one]
  rw [matrixCost, matrixCost, stateX_toMatrixState _ hXt]
  conv_lhs => rw [← hJ]
  rw [am_traceForm_conj hA']

/-- **The dynamics are equivariant under rotations** (the proof of Theorem 9.0.3, TeX 7758–7778:
`X ↦ Ad_A X`, and the transformed quantities satisfy the same equations): if
`Z_{u'} = A Z_u A⁻¹`, then `f(Ad_A q, u') = Ad_A f(q, u)`, i.e.
`(AgA⁻¹)(AXA⁻¹) = A(gX)A⁻¹` and `[P', AXA⁻¹] = A[P, X]A⁻¹` with `P' = A P A⁻¹`.

Proof: `am_matrixField_conj` with `B = A`: `⟨AZA⁻¹, AXA⁻¹⟩ = ⟨Z, X⟩`, so `P' = A P A⁻¹`. -/
theorem matrixField_rotateState {A : Mat2} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    {u u' : Fin 3 → ℝ} (hu : controlMatrix u' = A * controlMatrix u * A⁻¹) (q : MatrixState) :
    matrixField (rotateState A q) u' = rotateState A (matrixField q u) :=
  am_matrixField_conj (am_isUnit_det hA) hu q

/-- **The cost is invariant under rotations**: `⟨J, AXA⁻¹⟩ = ⟨A⁻¹JA, X⟩ = ⟨J, X⟩` for
`A ∈ SO₂(ℝ)` (Sussmann's condition (ii); the book's Definition 9.1.1 omits it, but its proof of
Theorem 9.1.6 checks the whole Hamiltonian, TeX 7921–7922).

Proof: `am_matrixCost_conj`: `A` commutes with `J`, and the trace form is invariant under
conjugation. -/
theorem matrixCost_rotateState {A : Mat2} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (q : MatrixState) (u u' : Fin 3 → ℝ) : matrixCost (rotateState A q) u' = matrixCost q u :=
  am_matrixCost_conj hA q u u'

/-- **The infinitesimal rotation** `τ(J)(g, X) = (Jg - gJ, [J, X])` (TeX 7931–7943: the derivative
at `θ = 0` of `(e^{θJ} g e^{-θJ}, Ad_{e^{θJ}} X)`). -/
noncomputable def rotationField (q : MatrixState) : MatrixState :=
  toMatrixState (J * stateG q - stateG q * J) (J * stateX q - stateX q * J)

/-! ### The rotations `exp(θJ)` and their flow on the state space -/

/-- `exp(0 J) = I`. -/
private lemma am_expJ_zero : expJ 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [expJ]

/-- `exp(-θJ) exp(θJ) = I`. -/
private lemma am_expJ_neg_mul (θ : ℝ) : expJ (-θ) * expJ θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [expJ, Real.cos_neg, Real.sin_neg, neg_neg, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two, mul_neg, neg_mul, ne_eq,
      zero_ne_one, one_ne_zero, not_false_eq_true, Matrix.one_apply_eq, Matrix.one_apply_ne] <;>
    first | linear_combination Real.cos_sq_add_sin_sq θ | ring

/-- `exp(θJ)⁻¹ = exp(-θJ)`. -/
private lemma am_inv_expJ (θ : ℝ) : (expJ θ)⁻¹ = expJ (-θ) :=
  Matrix.inv_eq_left_inv (am_expJ_neg_mul θ)

/-- `exp(θJ) ∈ SO₂(ℝ)`. -/
private lemma am_expJ_mem (θ : ℝ) : expJ θ ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [expJ, Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
  exact ⟨rfl, rfl, by rw [neg_sq]; exact Real.cos_sq_add_sin_sq θ⟩

/-- `(exp(θJ))' = J exp(θJ)`. -/
private lemma am_hasDerivAt_expJ (θ : ℝ) : HasDerivAtEntrywise expJ (J * expJ θ) θ := by
  rw [hasDerivAtEntrywise_fin_two_iff]
  simp only [expJ, J, Matrix.mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, Fin.isValue]
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert Real.hasDerivAt_cos θ using 1; ring
  · convert (Real.hasDerivAt_sin θ).neg using 1; ring
  · convert Real.hasDerivAt_sin θ using 1; ring
  · convert Real.hasDerivAt_cos θ using 1; ring

/-- `(exp(θJ)⁻¹)' = -(exp(θJ)⁻¹ J)`. -/
private lemma am_hasDerivAt_inv_expJ (θ : ℝ) :
    HasDerivAtEntrywise (fun r ↦ (expJ r)⁻¹) (-((expJ θ)⁻¹ * J)) θ := by
  have h := (am_hasDerivAt_expJ (-θ)).scomp (hasDerivAt_neg θ)
  simp only [am_inv_expJ]
  refine h.congr_deriv ?_
  rw [am_commute_J (am_expJ_mem (-θ))]
  simp

/-! ### The linear maps `(g, X) ↦ (A g B, C X D)` -/

/-- The linear map `(g, X) ↦ (A g B, C X D)` of the state space. -/
private noncomputable def am_sandwich (A B C D : Mat2) : MatrixState →L[ℝ] MatrixState :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q ↦ toMatrixState (A * stateG q * B) (C * stateX q * D)
      map_add' := fun q q' ↦ by
        refine Prod.ext (funext fun i ↦ funext fun j ↦ ?_) (funext fun k ↦ ?_)
        · simp only [toMatrixState, stateG, Prod.fst_add, Matrix.mul_apply, Fin.sum_univ_two,
            Matrix.of_apply, Pi.add_apply]
          ring
        · fin_cases k <;>
          simp only [toMatrixState, stateX, slMatrix, slCoords, Prod.snd_add, Matrix.mul_apply,
            Fin.sum_univ_two, Matrix.of_apply, Pi.add_apply, Matrix.cons_val', Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue,
            Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
            Matrix.head_cons] <;>
          ring
      map_smul' := fun c q ↦ by
        refine Prod.ext (funext fun i ↦ funext fun j ↦ ?_) (funext fun k ↦ ?_)
        · simp only [toMatrixState, stateG, Prod.smul_fst, Matrix.mul_apply, Fin.sum_univ_two,
            Matrix.of_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          ring
        · fin_cases k <;>
          simp only [toMatrixState, stateX, slMatrix, slCoords, Prod.smul_snd, Matrix.mul_apply,
            Fin.sum_univ_two, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
            Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
            Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
            Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] <;>
          ring }

/-- `am_sandwich A B C D q = (A g B, C X D)`. -/
private lemma am_sandwich_apply (A B C D : Mat2) (q : MatrixState) :
    am_sandwich A B C D q = toMatrixState (A * stateG q * B) (C * stateX q * D) := rfl

/-- A state is determined by its `g` and its `X`. -/
private lemma am_toMatrixState_self (q : MatrixState) : toMatrixState (stateG q) (stateX q) = q :=
  Prod.ext rfl (slCoords_slMatrix q.2)

/-- A curve `t ↦ (M t, N t)` of states with entrywise derivatives `(M', N')`. -/
private lemma am_hasDerivAt_toMatrixState {M N : ℝ → Mat2} {M' N' : Mat2} {t : ℝ}
    (hM : HasDerivAtEntrywise M M' t) (hN : HasDerivAtEntrywise N N' t) :
    HasDerivAt (fun r ↦ toMatrixState (M r) (N r)) (toMatrixState M' N') t := by
  refine HasDerivAt.prodMk (hasDerivAt_pi.2 fun i ↦ hasDerivAt_pi.2 fun j ↦ hM i j)
    (hasDerivAt_pi.2 fun k ↦ ?_)
  fin_cases k
  exacts [hN 0 0, hN 0 1, hN 1 0]

/-- A map `q ↦ (M q, N q)` with smooth entries is smooth. -/
private lemma am_contDiff_toMatrixState {M N : MatrixState → Mat2}
    (hM : ∀ i j, ContDiff ℝ 1 fun q ↦ M q i j) (hN : ∀ i j, ContDiff ℝ 1 fun q ↦ N q i j) :
    ContDiff ℝ 1 fun q ↦ toMatrixState (M q) (N q) := by
  refine ContDiff.prodMk (contDiff_pi.2 fun i ↦ contDiff_pi.2 fun j ↦ hM i j)
    (contDiff_pi.2 fun k ↦ ?_)
  fin_cases k
  exacts [hN 0 0, hN 0 1, hN 1 0]

/-- **The flows of the rotations are symmetries** (the common part of
`isInfinitesimalSymmetry_rotationField` and `isInfinitesimalSymmetry_rightRotationField`): for a
compact control set closed under rotations, a curve `ℓ` in `GL₂⁺(ℝ)` with `ℓ(0) = I`,
`ℓ(-θ) ℓ(θ) = I` and `ℓ' = L ℓ`, the flow `(g, X) ↦ (ℓ(θ) g e^{-θJ}, e^{θJ} X e^{-θJ})` of the
field `(g, X) ↦ (L g - g J, [J, X])` consists of symmetries of the matrix system (the dynamics are
equivariant and the cost invariant, `am_matrixField_conj`, `am_matrixCost_conj`). -/
private theorem am_isInfinitesimalSymmetry {U : Set (Fin 3 → ℝ)} (hU : IsRotationClosed U)
    (hUc : IsCompact U) (ℓ : ℝ → Mat2) (L : Mat2) (hℓ0 : ℓ 0 = 1)
    (hℓinv : ∀ θ, ℓ (-θ) * ℓ θ = 1) (hℓdet : ∀ θ, 0 < (ℓ θ).det)
    (hℓd : ∀ θ, HasDerivAtEntrywise ℓ (L * ℓ θ) θ) :
    IsInfinitesimalSymmetry matrixField matrixCost (matrixDomainFor U) U
      (fun q ↦ toMatrixState (L * stateG q - stateG q * J) (J * stateX q - stateX q * J)) := by
  have hE : ∀ θ, IsUnit (expJ θ).det := fun θ ↦ am_isUnit_det (am_expJ_mem θ)
  -- the flow
  set Φ : ℝ → MatrixState → MatrixState :=
    fun θ ↦ am_sandwich (ℓ θ) (expJ θ)⁻¹ (expJ θ) (expJ θ)⁻¹ with hΦ
  have hΦa : ∀ θ q, Φ θ q = toMatrixState (ℓ θ * stateG q * (expJ θ)⁻¹)
      (expJ θ * stateX q * (expJ θ)⁻¹) := fun _ _ ↦ rfl
  have hXt : ∀ θ q, (expJ θ * stateX q * (expJ θ)⁻¹).trace = 0 := fun θ q ↦ by
    rw [am_trace_conj (hE θ)]; exact trace_slMatrix _
  have hΦG : ∀ θ q, stateG (Φ θ q) = ℓ θ * stateG q * (expJ θ)⁻¹ := fun _ _ ↦ rfl
  have hΦX : ∀ θ q, stateX (Φ θ q) = expJ θ * stateX q * (expJ θ)⁻¹ := fun θ q ↦
    stateX_toMatrixState _ (hXt θ q)
  refine isInfinitesimalSymmetry_of_flow (isOpen_matrixDomainFor hUc) ?_ Φ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the field is smooth (linear)
    refine (am_contDiff_toMatrixState (fun i j ↦ ?_) (fun i j ↦ ?_)).contDiffOn <;>
    fin_cases i <;> fin_cases j <;>
      simp only [stateG, stateX, slMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.sub_apply, J, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
      fun_prop
  · -- the flow preserves the domain
    intro θ q hq
    refine ⟨?_, fun v hv ↦ ?_⟩
    · rw [hΦG, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
        (Matrix.mem_specialOrthogonalGroup_iff.1 (am_expJ_mem θ)).2, Ring.inverse_one, mul_one]
      exact mul_pos (hℓdet θ) hq.1
    · obtain ⟨v', hv', hZ⟩ := hU _ (am_expJ_mem (-θ)) v hv
      have e : traceForm (controlMatrix v) (expJ θ * stateX q * (expJ θ)⁻¹) =
          traceForm (controlMatrix v') (stateX q) := by
        rw [hZ, am_inv_expJ (-θ), neg_neg, ← am_inv_expJ θ, traceForm, traceForm,
          show controlMatrix v * (expJ θ * stateX q * (expJ θ)⁻¹) =
            controlMatrix v * expJ θ * stateX q * (expJ θ)⁻¹ by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      rw [hΦX, e]
      exact hq.2 v' hv'
  · -- `Φ₀ = id`
    intro q _
    rw [hΦa, hℓ0, am_expJ_zero, inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one, am_toMatrixState_self]
  · -- `∂_θ Φ_θ(q) = Y(Φ_θ(q))`
    intro q _ θ
    have hinv := am_hasDerivAt_inv_expJ θ
    have h := am_hasDerivAt_toMatrixState (((hℓd θ).mul_const (stateG q)).mul hinv)
      (((am_hasDerivAt_expJ θ).mul_const (stateX q)).mul hinv)
    convert h using 1
    · funext r; exact hΦa r q
    · rw [hΦG, hΦX]
      congr 1 <;> noncomm_ring
  · -- `Φ_{-θ} ∘ Φ_θ = id`
    intro θ q _
    have h1 : ℓ (-θ) * (ℓ θ * stateG q * (expJ θ)⁻¹) * (expJ (-θ))⁻¹ = stateG q := by
      rw [am_inv_expJ (-θ), neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hℓinv,
        Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hE θ), Matrix.mul_one]
    have h2 : expJ (-θ) * (expJ θ * stateX q * (expJ θ)⁻¹) * (expJ (-θ))⁻¹ = stateX q := by
      rw [am_inv_expJ (-θ), neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, am_expJ_neg_mul,
        Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hE θ), Matrix.mul_one]
    rw [hΦa, hΦG, hΦX, h1, h2, am_toMatrixState_self]
  · -- `Φ_θ` is smooth (linear)
    intro θ
    exact (am_sandwich _ _ _ _).contDiff.contDiffOn
  · -- `Φ_θ` permutes the dynamics and preserves the cost
    intro θ
    have hfd : ∀ x v, fderiv ℝ (Φ θ) x v = Φ θ v :=
      fun x v ↦ by rw [hΦ, (am_sandwich _ _ _ _).fderiv]
    refine ⟨fun u hu ↦ ?_, fun u hu ↦ ?_⟩
    · obtain ⟨u₁, hu₁, hZ⟩ := hU _ (am_expJ_mem θ) u hu
      refine ⟨u₁, hu₁, fun x _ ↦ ⟨?_, ?_⟩⟩
      · rw [hfd, hΦa, hΦa]
        exact (am_matrixField_conj (hE θ) hZ x).symm
      · rw [hΦa]
        exact am_matrixCost_conj (am_expJ_mem θ) x u u₁
    · obtain ⟨u₂, hu₂, hZ⟩ := hU _ (am_expJ_mem (-θ)) u hu
      have hZ' : controlMatrix u = expJ θ * controlMatrix u₂ * (expJ θ)⁻¹ := by
        rw [hZ, am_inv_expJ (-θ), neg_neg, ← am_inv_expJ θ, ← Matrix.mul_assoc,
          ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hE θ), Matrix.one_mul, Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ (hE θ), Matrix.mul_one]
      refine ⟨u₂, hu₂, fun x _ ↦ ⟨?_, ?_⟩⟩
      · rw [hfd, hΦa, hΦa]
        exact (am_matrixField_conj (hE θ) hZ' x).symm
      · rw [hΦa]
        exact am_matrixCost_conj (am_expJ_mem θ) x u₂ u

/-- **The rotations are symmetries** (TeX 7918–7925: "These are symmetries by the proof of
Theorem 9.0.3 and also since the rotation action on the control matrix `Z_u` is
`Z_u ↦ Ad_{exp(Jθ)} Z_u ∈ U_C`"): for a compact control set closed under rotations,
`rotationField` is an infinitesimal symmetry of the matrix system in Sussmann's sense (every
`e^{θY}` is a `C¹` diffeomorphism of the domain permuting the controls, with the cost invariant).

Proof: `am_isInfinitesimalSymmetry` with `ℓ = exp(·J)`, `L = J`: the flow is
`rotateState (exp(θJ))`, the dynamics are equivariant and the cost invariant (the proof of
Theorem 9.0.3, `am_matrixField_conj`, `am_matrixCost_conj`), and `U` permutes under the rotations
(`IsRotationClosed`). -/
theorem isInfinitesimalSymmetry_rotationField {U : Set (Fin 3 → ℝ)} (hU : IsRotationClosed U)
    (hUc : IsCompact U) :
    IsInfinitesimalSymmetry matrixField matrixCost (matrixDomainFor U) U rotationField :=
  am_isInfinitesimalSymmetry hU hUc expJ J am_expJ_zero am_expJ_neg_mul
    (fun θ ↦ by rw [(Matrix.mem_specialOrthogonalGroup_iff.1 (am_expJ_mem θ)).2]; exact one_pos)
    am_hasDerivAt_expJ

/-- A covector evaluated on `(W, x)`: `tr(p W) + ⟨Λ₂, X(x)⟩`. -/
private lemma am_apply_eq (π : StrongDual ℝ MatrixState) (W : Fin 2 → Fin 2 → ℝ)
    (x : Fin 3 → ℝ) :
    π (W, x) = (covectorG π * Matrix.of W).trace + traceForm (covectorΛ₂ π) (slMatrix x) := by
  rw [trace_covectorG_mul, traceForm_covectorΛ₂, ← map_add]
  congr 1
  refine Prod.ext ?_ ?_ <;> simp

/-- **The momentum map of the rotations** (TeX 7945–7956):
`𝐉^τ(g, X, Λ₁, Λ₂)(J) = ⟨Λ₁, Ad_{g⁻¹}J - J⟩ + ⟨Λ₂, [J, X]⟩ = ⟨Λ₁, Ad_{g⁻¹}J⟩ - ⟨J, Λ₁ + Λ_R⟩`,
for the costates `Λ₁ = covectorΛ₁ q π` (the left-trivialized `g`-part, made traceless) and
`Λ_R = covectorΛR q π` of a covector `π` at `q` with `det g ≠ 0`.

Proof: `π(rotationField q) = tr(p(Jg - gJ)) + ⟨Λ₂, [J, X]⟩` (`am_apply_eq`); with
`Λ₁ = pg - (tr(pg)/2) I`: `⟨Λ₁, g⁻¹Jg⟩ = tr(pJg)` (`tr(g⁻¹Jg) = tr J = 0`), `⟨J, Λ₁⟩ = tr(pgJ)`;
and `⟨Λ₂, [J, X]⟩ = -⟨J, [Λ₂, X]⟩ = -⟨J, Λ_R⟩` (entrywise). -/
theorem momentum_rotationField {q : MatrixState} (hq : (stateG q).det ≠ 0)
    (π : StrongDual ℝ MatrixState) :
    momentum rotationField q π =
      traceForm (covectorΛ₁ q π) ((stateG q)⁻¹ * J * stateG q) -
        angularMomentum (covectorΛ₁ q π) (covectorΛR q π) := by
  have hc : (J * stateX q - stateX q * J).trace = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  have hJ : J.trace = 0 := by simp [J, Matrix.trace_fin_two]
  rw [momentum, rotationField, toMatrixState, am_apply_eq, slMatrix_slCoords hc]
  simp only [angularMomentum, covectorΛ₁, covectorΛR]
  generalize stateG q = g at hq ⊢
  generalize stateX q = X
  generalize covectorG π = p
  generalize covectorΛ₂ π = L
  have hg : IsUnit g.det := isUnit_iff_ne_zero.2 hq
  -- `⟨Λ₁, g⁻¹ J g⟩ = tr(p J g)`, since `tr(g⁻¹ J g) = tr J = 0`
  have h1 : traceForm (p * g - ((p * g).trace / 2) • (1 : Mat2)) (g⁻¹ * J * g) =
      (p * J * g).trace := by
    rw [traceForm, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul,
      Matrix.one_mul, Matrix.trace_mul_cycle g⁻¹ J g, Matrix.mul_nonsing_inv _ hg,
      Matrix.one_mul, hJ, smul_zero, sub_zero,
      show p * g * (g⁻¹ * J * g) = p * (g * g⁻¹) * J * g by simp only [Matrix.mul_assoc],
      Matrix.mul_nonsing_inv _ hg, Matrix.mul_one]
  have hW : Matrix.of (fun i j ↦ (J * g - g * J) i j) = J * g - g * J := rfl
  rw [hW, h1]
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, J,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, smul_eq_mul,
    ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, Fin.isValue]
  ring

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

/-! ### The lift of the reduced costate

The departure of the module docstring: algebraic identities, Hamilton's equations where
`⟨Z_u, X⟩ ≠ 0`, the covector `p`, and the calculus of absolutely continuous curves, then
`IsStateTrajectoryFor.exists_covector`. -/

/-- For traceless `X` with `det X = 1` and traceless `Y ⊥ X`: `[[X, Y], X] = 4Y`. -/
private lemma am_bracket_bracket {X Y : Mat2} (hX : X.trace = 0) (hdet : X.det = 1)
    (hY : Y.trace = 0) (hYX : traceForm Y X = 0) :
    (X * Y - Y * X) * X - X * (X * Y - Y * X) = (4 : ℝ) • Y := by
  rw [Matrix.trace_fin_two] at hX hY
  rw [Matrix.det_fin_two] at hdet
  have hX11 : X 1 1 = -X 0 0 := by linarith
  have hY11 : Y 1 1 = -Y 0 0 := by linarith
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hX11,
    hY11] at hYX
  rw [hX11] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul, hX11, hY11, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination 2 * X 0 0 * hYX + 4 * Y 0 0 * hdet
  · linear_combination 2 * X 0 1 * hYX + 4 * Y 0 1 * hdet
  · linear_combination 2 * X 1 0 * hYX + 4 * Y 1 0 * hdet
  · linear_combination -(2 * X 0 0 * hYX + 4 * Y 0 0 * hdet)

/-- A traceless `E` commuting with and orthogonal to a traceless `X` with `det X ≠ 0` is `0`. -/
private lemma am_eq_zero_of_commute {E X : Mat2} (hE : E.trace = 0) (hX : X.trace = 0)
    (hdet : X.det ≠ 0) (hc : E * X - X * E = 0) (ho : traceForm E X = 0) : E = 0 := by
  rw [Matrix.trace_fin_two] at hX hE
  rw [Matrix.det_fin_two] at hdet
  have hX11 : X 1 1 = -X 0 0 := by linarith
  have hE11 : E 1 1 = -E 0 0 := by linarith
  have h00 := congrFun (congrFun hc 0) 0
  have h01 := congrFun (congrFun hc 0) 1
  have h10 := congrFun (congrFun hc 1) 0
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply, hX11,
    hE11] at h00 h01 h10
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hX11,
    hE11] at ho
  rw [hX11] at hdet
  have hd : X 0 0 ^ 2 + X 0 1 * X 1 0 ≠ 0 := fun h ↦ hdet (by linear_combination -h)
  have he : E 0 0 = 0 := by
    have : E 0 0 * (X 0 0 ^ 2 + X 0 1 * X 1 0) = 0 := by
      linear_combination X 0 0 / 2 * ho - X 0 0 / 2 * h00 - X 0 1 / 2 * h10
    exact (mul_eq_zero.1 this).resolve_right hd
  have hf : E 0 1 = 0 := by
    have : E 0 1 * (X 0 0 ^ 2 + X 0 1 * X 1 0) = 0 := by
      linear_combination -(X 0 0 / 2) * h01 + X 0 1 / 2 * ho + X 0 1 / 2 * h00
    exact (mul_eq_zero.1 this).resolve_right hd
  have hg : E 1 0 = 0 := by
    have : E 1 0 * (X 0 0 ^ 2 + X 0 1 * X 1 0) = 0 := by
      linear_combination X 0 0 / 2 * h10 + X 1 0 / 2 * ho - X 1 0 / 2 * h00
    exact (mul_eq_zero.1 this).resolve_right hd
  ext i j
  fin_cases i <;> fin_cases j <;> simp [he, hf, hg, hE11]

/-- The `Λ_R` equation in terms of `Λ₂` (the algebraic identity of the proof of
Proposition 6.5.1, TeX 5071–5085): with `Λ_R = [Λ₂, X]`, `P = Z_u/⟨Z_u, X⟩` and
`D = δH/δX = Λ₁ - (3/2)λJ + [Λ₂, P] - ⟨[Λ₂, P], X⟩P`, the right-hand side of `eqn:lamR` is
`[-D, X] + [Λ₂, [P, X]]`. -/
private lemma am_costateRHS_eq (lam : ℝ) (Λ₁ Λ₂ X : Mat2) (u : Fin 3 → ℝ) :
    costateRHS lam Λ₁ (Λ₂ * X - X * Λ₂) X u =
      (-(Λ₁ - (3 / 2 * lam) • J + (Λ₂ * controlP u X - controlP u X * Λ₂) -
          traceForm (Λ₂ * controlP u X - controlP u X * Λ₂) X • controlP u X)) * X -
        X * (-(Λ₁ - (3 / 2 * lam) • J + (Λ₂ * controlP u X - controlP u X * Λ₂) -
          traceForm (Λ₂ * controlP u X - controlP u X * Λ₂) X • controlP u X)) +
      (Λ₂ * (controlP u X * X - X * controlP u X) -
        (controlP u X * X - X * controlP u X) * Λ₂) := by
  set P := controlP u X
  have hκ : traceForm (Λ₂ * P - P * Λ₂) X = -traceForm (Λ₂ * X - X * Λ₂) P := by
    simp only [traceForm, Matrix.sub_mul, Matrix.trace_sub]
    rw [Matrix.trace_mul_cycle Λ₂ X P, Matrix.trace_mul_cycle X Λ₂ P,
      Matrix.trace_mul_cycle P X Λ₂]
    ring
  unfold costateRHS
  rw [hκ]
  generalize traceForm (Λ₂ * X - X * Λ₂) P = κ
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc, smul_sub, Matrix.mul_add, Matrix.add_mul, neg_smul,
    neg_sub]
  abel

/-- `⟨P, X⟩ = 1` where `⟨Z_u, X⟩ ≠ 0`. -/
private lemma am_traceForm_controlP {u : Fin 3 → ℝ} {X : Mat2}
    (hden : traceForm (controlMatrix u) X ≠ 0) : traceForm (controlP u X) X = 1 := by
  rw [controlP, traceForm, Matrix.smul_mul, Matrix.trace_smul, ← traceForm, smul_eq_mul,
    inv_mul_cancel₀ hden]

/-- `⟨X, X⟩ = -2 det X` for traceless `X`. -/
private lemma am_traceForm_self {X : Mat2} (hX : X.trace = 0) :
    traceForm X X = -2 * X.det := by
  rw [Matrix.trace_fin_two] at hX
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.det_fin_two]
  rw [show X 1 1 = -X 0 0 by linarith]
  ring

/-- The control matrices are traceless. -/
private lemma am_trace_controlMatrix (u : Fin 3 → ℝ) : (controlMatrix u).trace = 0 := by
  simp [controlMatrix, Matrix.trace_fin_two]; ring

/-- **The `X`-part of the lift** (pointwise algebra): at a time of differentiability, with
`Λ₂ = [X, Λ_R]/4 + cX` and `c' = κ` for the `κ` below, the derivative `Λ₂'` (computed by the
product rule from `X' = [P, X]` and `Λ_R'`) is `-δH/δX`, provided the derivative of `[Λ₂, X]` is
the right-hand side of `eqn:lamR` (`hcomm`): `E = Λ₂' + δH/δX` is traceless, commutes with `X`
(`hcomm`, `am_costateRHS_eq` and `[Λ₂, X] = Λ_R`) and is orthogonal to `X` (the choice of `κ`,
`⟨P, X⟩ = 1`, `⟨X, X⟩ = -2`), so `E = 0` (`am_eq_zero_of_commute`). -/
private lemma am_lift_X {lam c κ : ℝ} {u : Fin 3 → ℝ} {X ΛR Λ₁ X' ΛR' Λ₂' : Mat2}
    (hX : X.trace = 0) (hdet : X.det = 1) (hR : ΛR.trace = 0) (hRX : traceForm ΛR X = 0)
    (hΛ₁ : Λ₁.trace = 0) (hden : traceForm (controlMatrix u) X ≠ 0)
    (hX' : X' = controlP u X * X - X * controlP u X)
    (hκ : κ = (traceForm (Λ₁ - (3 / 2 * lam) • J) X + traceForm X' (ΛR * X - X * ΛR) / 4) / 2)
    (hΛ₂' : Λ₂' = (1 / 4 : ℝ) • ((X' * ΛR + X * ΛR') - (ΛR' * X + ΛR * X')) + (c • X' + κ • X))
    (hcomm : (Λ₂' * X + ((1 / 4 : ℝ) • (X * ΛR - ΛR * X) + c • X) * X') -
      (X' * ((1 / 4 : ℝ) • (X * ΛR - ΛR * X) + c • X) + X * Λ₂') =
        costateRHS lam Λ₁ ΛR X u) :
    Λ₂' = -(Λ₁ - (3 / 2 * lam) • J +
      (((1 / 4 : ℝ) • (X * ΛR - ΛR * X) + c • X) * controlP u X -
        controlP u X * ((1 / 4 : ℝ) • (X * ΛR - ΛR * X) + c • X)) -
      traceForm (((1 / 4 : ℝ) • (X * ΛR - ΛR * X) + c • X) * controlP u X -
        controlP u X * ((1 / 4 : ℝ) • (X * ΛR - ΛR * X) + c • X)) X • controlP u X) := by
  set P := controlP u X with hP
  set Λ₂ := (1 / 4 : ℝ) • (X * ΛR - ΛR * X) + c • X with hΛ₂
  set D := Λ₁ - (3 / 2 * lam) • J + (Λ₂ * P - P * Λ₂) - traceForm (Λ₂ * P - P * Λ₂) X • P
    with hD
  have hcommtr : ∀ A B : Mat2, (A * B - B * A).trace = 0 := fun A B ↦ by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  have hJ : J.trace = 0 := by simp [J, Matrix.trace_fin_two]
  have hPtr : P.trace = 0 := by
    rw [hP, controlP, Matrix.trace_smul, am_trace_controlMatrix, smul_zero]
  -- `[Λ₂, X] = Λ_R`
  have hLR : Λ₂ * X - X * Λ₂ = ΛR := by
    have h4 := am_bracket_bracket hX hdet hR hRX
    rw [hΛ₂]
    have e : ((1 / 4 : ℝ) • (X * ΛR - ΛR * X) + c • X) * X -
        X * ((1 / 4 : ℝ) • (X * ΛR - ΛR * X) + c • X) =
        (1 / 4 : ℝ) • ((X * ΛR - ΛR * X) * X - X * (X * ΛR - ΛR * X)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
        Matrix.mul_smul, smul_sub]
      abel
    rw [e, h4, smul_smul]
    norm_num
  -- `E = Λ₂' + D` commutes with `X`
  have hc : (Λ₂' + D) * X - X * (Λ₂' + D) = 0 := by
    have h1 := am_costateRHS_eq lam Λ₁ Λ₂ X u
    rw [hLR, ← hcomm, hX'] at h1
    rw [← hP, ← hD] at h1
    have e : (Λ₂' + D) * X - X * (Λ₂' + D) =
        ((Λ₂' * X + Λ₂ * (P * X - X * P)) - ((P * X - X * P) * Λ₂ + X * Λ₂')) -
          ((-D) * X - X * (-D) + (Λ₂ * (P * X - X * P) - (P * X - X * P) * Λ₂)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg]
      abel
    rw [e, h1, sub_self]
  -- and is orthogonal to `X`
  have ho : traceForm (Λ₂' + D) X = 0 := by
    have e1 : traceForm Λ₂' X = traceForm X' (ΛR * X - X * ΛR) / 4 + c * traceForm X' X +
        κ * traceForm X X := by
      rw [hΛ₂']
      simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have e2 : traceForm X' X = 0 := by
      rw [hX', traceForm, Matrix.trace_mul_comm, ← traceForm, traceForm_commutator_self]
    have e3 : traceForm D X = traceForm (Λ₁ - (3 / 2 * lam) • J) X := by
      rw [hD]
      simp only [traceForm, Matrix.sub_mul, Matrix.add_mul, Matrix.trace_sub, Matrix.trace_add,
        Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      have hPX : (P * X).trace = 1 := am_traceForm_controlP hden
      rw [hPX]
      ring
    rw [traceForm, Matrix.add_mul, Matrix.trace_add, ← traceForm, ← traceForm, e1, e2, e3,
      am_traceForm_self hX, hdet, hκ]
    ring
  -- and is traceless
  have htr : (Λ₂' + D).trace = 0 := by
    have hX'tr : X'.trace = 0 := by rw [hX']; exact hcommtr _ _
    have hΛ₂'tr : Λ₂'.trace = 0 := by
      rw [hΛ₂']
      simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, hX'tr, hX]
      rw [Matrix.trace_mul_comm X' ΛR, Matrix.trace_mul_comm X ΛR']
      ring
    have hDtr : D.trace = 0 := by
      rw [hD, Matrix.trace_sub, Matrix.trace_add, hcommtr, Matrix.trace_sub, Matrix.trace_smul,
        Matrix.trace_smul, hΛ₁, hJ, hPtr]
      simp
    rw [Matrix.trace_add, hΛ₂'tr, hDtr, add_zero]
  have hE := am_eq_zero_of_commute htr hX (by rw [hdet]; exact one_ne_zero) hc ho
  exact eq_neg_of_add_eq_zero_left hE

/-! ### Lift helpers: Hamilton's equations where `⟨Z_u, X⟩ ≠ 0` -/

/-- An affine function of `s` has derivative its slope. -/
private lemma am_hasDerivAt_affine (a b : ℝ) : HasDerivAt (fun s : ℝ ↦ a + s * b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a

/-- The quotient rule for two affine functions of `s`, at `s = 0`. -/
private lemma am_hasDerivAt_affine_div (a b c d : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ (a + s * b) / (c + s * d)) ((b * c - a * d) / c ^ 2) 0 := by
  simpa using (am_hasDerivAt_affine a b).fun_div (am_hasDerivAt_affine c d) (by simpa using hc)

/-- `slMatrix` is linear. -/
private lemma am_slMatrix_add_smul (x y : Fin 3 → ℝ) (s : ℝ) :
    slMatrix (x + s • y) = slMatrix x + s • slMatrix y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [slMatrix]; ring

/-- The covector `π ∘ ∂f/∂q + λ_cost ∂φ/∂q` is the derivative at `q` of the Hamiltonian of the
maximum principle along the line `s ↦ q + s v`, where `⟨Z_u, X⟩ ≠ 0`. -/
private lemma am_hasDerivAt_controlHamiltonian_line {ν : ℝ} {q : MatrixState}
    {u : Fin 3 → ℝ} (hq : traceForm (controlMatrix u) (stateX q) ≠ 0)
    (π : StrongDual ℝ MatrixState) (v : MatrixState) :
    HasDerivAt (fun s : ℝ ↦ controlHamiltonian matrixField matrixCost ν (q + s • v) π u)
      ((π.comp (fderiv ℝ (matrixField · u) q) + ν • fderiv ℝ (matrixCost · u) q) v) 0 := by
  have hF : HasFDerivAt (fun q' ↦ π (matrixField q' u) + ν * matrixCost q' u)
      (π.comp (fderiv ℝ (matrixField · u) q) + ν • fderiv ℝ (matrixCost · u) q) q :=
    (π.hasFDerivAt.comp q
      ((contDiffAt_matrixField hq).differentiableAt one_ne_zero).hasFDerivAt).fun_add
      (((contDiff_matrixCost u).contDiffAt.differentiableAt one_ne_zero).hasFDerivAt.const_mul ν)
  have hl : HasDerivAt (fun s : ℝ ↦ q + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  exact hF.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

/-- In a direction `(W, 0)` of the group variable, `∂H/∂q (W, 0) = tr(p W X)`. -/
private lemma am_apply_g (ν : ℝ) {q : MatrixState} {u : Fin 3 → ℝ}
    (hq : traceForm (controlMatrix u) (stateX q) ≠ 0) (π : StrongDual ℝ MatrixState)
    (W : Fin 2 → Fin 2 → ℝ) :
    (π.comp (fderiv ℝ (matrixField · u) q) + ν • fderiv ℝ (matrixCost · u) q) (W, 0) =
      (covectorG π * (Matrix.of W * stateX q)).trace := by
  have hX : ∀ s : ℝ, stateX (q + s • ((W, 0) : MatrixState)) = stateX q := fun s ↦ by
    simp [stateX]
  have hf : ∀ s : ℝ, matrixField (q + s • ((W, 0) : MatrixState)) u =
      matrixField q u + s • ((fun i j ↦ (Matrix.of W * stateX q) i j, 0) : MatrixState) := by
    intro s
    refine Prod.ext ?_ ?_
    · funext i j
      simp only [matrixField, hX, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, stateG]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp only [matrixField, hX, Prod.snd_add, Prod.smul_snd, smul_zero, add_zero]
  have e : (fun s : ℝ ↦ controlHamiltonian matrixField matrixCost ν
      (q + s • ((W, 0) : MatrixState)) π u) = fun s ↦
        controlHamiltonian matrixField matrixCost ν q π u +
          s * (covectorG π * (Matrix.of W * stateX q)).trace := by
    funext s
    simp only [controlHamiltonian, hf, map_add, map_smul, smul_eq_mul, matrixCost, hX,
      trace_covectorG_mul]
    ring
  have h := am_hasDerivAt_controlHamiltonian_line (ν := ν) hq π (W, 0)
  rw [e] at h
  exact h.unique (am_hasDerivAt_affine _ _)

/-- **Hamilton's equations, `g`-part**, where `⟨Z_u, X⟩ ≠ 0`: `covectorG_comp_fderiv_matrixField`
of Chapter 6 (stated there on `GL₂⁺(ℝ) × C` with `u ∈ U_T`), whose proof uses only
`⟨Z_u, X⟩ ≠ 0`. -/
theorem covectorG_comp_fderiv_matrixField_of_ne (ν : ℝ) {q : MatrixState} {u : Fin 3 → ℝ}
    (hq : traceForm (controlMatrix u) (stateX q) ≠ 0) (π : StrongDual ℝ MatrixState) :
    covectorG (π.comp (fderiv ℝ (matrixField · u) q) + ν • fderiv ℝ (matrixCost · u) q) =
      stateX q * covectorG π := by
  ext i j
  rw [covectorG, Matrix.of_apply, am_apply_g ν hq π]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Hamilton's equations, `X`-part**, where `⟨Z_u, X⟩ ≠ 0`:
`hasFunctionalDerivative_fullHamiltonian` of Chapter 6 (stated there on `GL₂⁺(ℝ) × C` with
`u ∈ U_T`), whose proof uses only `⟨Z_u, X⟩ ≠ 0`. -/
theorem hasFunctionalDerivative_fullHamiltonian_of_ne (ν : ℝ) {q : MatrixState}
    {u : Fin 3 → ℝ} (hq : traceForm (controlMatrix u) (stateX q) ≠ 0)
    (π : StrongDual ℝ MatrixState) :
    HasFunctionalDerivative (fun Y ↦ fullHamiltonian ν (covectorΛ₁ q π) (covectorΛ₂ π) Y u)
      (stateX q)
      (covectorΛ₂ (π.comp (fderiv ℝ (matrixField · u) q) + ν • fderiv ℝ (matrixCost · u) q)) := by
  refine ⟨trace_covectorΛ₂ _, fun W hW ↦ ?_⟩
  have e : (fun s : ℝ ↦ controlHamiltonian matrixField matrixCost ν
      (q + s • ((0, slCoords W) : MatrixState)) π u) = fun s ↦
        fullHamiltonian ν (covectorΛ₁ q π) (covectorΛ₂ π) (stateX q + s • W) u := by
    funext s
    rw [controlHamiltonian_matrix_eq_fullHamiltonian]
    have hg : stateG (q + s • ((0, slCoords W) : MatrixState)) = stateG q := by simp [stateG]
    have hX : stateX (q + s • ((0, slCoords W) : MatrixState)) = stateX q + s • W := by
      simp only [stateX, Prod.snd_add, Prod.smul_snd, am_slMatrix_add_smul, slMatrix_slCoords hW]
    simp only [covectorΛ₁, hg, hX]
  have h := am_hasDerivAt_controlHamiltonian_line (ν := ν) hq π (0, slCoords W)
  rw [e] at h
  convert h using 1
  rw [traceForm, Matrix.trace_mul_comm, ← traceForm, ← traceForm_covectorΛ₂,
    slMatrix_slCoords hW]

/-- The trace form is nondegenerate on `𝔰𝔩₂(ℝ)` (as the private `eq_of_traceForm_eq` of
`SmoothedPolygons/Ch6/Hamiltonian.lean`). -/
private lemma am_eq_of_traceForm_eq {D D' : Mat2} (hD : D.trace = 0) (hD' : D'.trace = 0)
    (h : ∀ W : Mat2, W.trace = 0 → traceForm W D = traceForm W D') : D = D' := by
  have h1 := h !![0, 1; 0, 0] (by simp [Matrix.trace_fin_two])
  have h2 := h !![0, 0; 1, 0] (by simp [Matrix.trace_fin_two])
  have h3 := h !![1, 0; 0, -1] (by simp [Matrix.trace_fin_two])
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h1 h2 h3
  rw [Matrix.trace_fin_two] at hD hD'
  ext i j
  fin_cases i <;> fin_cases j <;> simp at h1 h2 h3 ⊢ <;> linarith

/-- Functional derivatives are unique. -/
private lemma am_hasFunctionalDerivative_unique {F : Mat2 → ℝ} {X D D' : Mat2}
    (h : HasFunctionalDerivative F X D) (h' : HasFunctionalDerivative F X D') : D = D' :=
  am_eq_of_traceForm_eq h.1 h'.1 fun W hW ↦ (h.2 W hW).unique (h'.2 W hW)

/-- **The functional derivative `δH/δX`** (the computation in the proof of Proposition 6.5.1):
`δH/δX(Λ₁, Λ₂, X; Z_u) = Λ₁ - (3/2)λJ + [Λ₂, P] - ⟨[Λ₂, P], X⟩P`. -/
private lemma am_hasFunctionalDerivative_X (lam : ℝ) {Λ₁ Λ₂ X : Mat2} {u : Fin 3 → ℝ}
    (hΛ₁ : Λ₁.trace = 0) (hden : traceForm (controlMatrix u) X ≠ 0) :
    HasFunctionalDerivative (fun Y ↦ fullHamiltonian lam Λ₁ Λ₂ Y u) X
      (Λ₁ - (3 / 2 * lam) • J + (Λ₂ * controlP u X - controlP u X * Λ₂) -
        traceForm (Λ₂ * controlP u X - controlP u X * Λ₂) X • controlP u X) := by
  set Z := controlMatrix u with hZdef
  set P := controlP u X with hPdef
  set M := Λ₁ - (3 / 2 * lam) • J with hMdef
  have hZtr : Z.trace = 0 := am_trace_controlMatrix u
  have hJtr : J.trace = 0 := by simp [J, Matrix.trace_fin_two]
  have hPZ : P = (traceForm Z X)⁻¹ • Z := rfl
  have hPtr : P.trace = 0 := by rw [hPZ, Matrix.trace_smul, hZtr, smul_zero]
  have hden' : traceForm X Z ≠ 0 := by rw [traceForm, Matrix.trace_mul_comm]; exact hden
  refine ⟨?_, fun W _ ↦ ?_⟩
  · have hc : (Λ₂ * P - P * Λ₂).trace = 0 := by
      rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
    rw [Matrix.trace_sub, Matrix.trace_add, hc, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_smul, hPtr, hJtr, hΛ₁]
    simp
  have e : (fun s : ℝ ↦ fullHamiltonian lam Λ₁ Λ₂ (X + s • W) u) = fun s ↦
      (traceForm M X + s * traceForm M W) +
        (traceForm Λ₂ (Z * X - X * Z) + s * traceForm Λ₂ (Z * W - W * Z)) /
          (traceForm X Z + s * traceForm W Z) := by
    funext s
    simp [fullHamiltonian, traceForm, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add,
      Matrix.trace_smul, Matrix.mul_sub, Matrix.trace_sub, hMdef, hZdef]
    ring
  rw [e]
  convert (am_hasDerivAt_affine _ _).add (am_hasDerivAt_affine_div _ _ _ _ hden') using 1
  rw [hPZ, show traceForm Z X = traceForm X Z from Matrix.trace_mul_comm Z X]
  have hden'' := hden'
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hden'' ⊢
  field_simp
  ring

/-! ### Lift helpers: the covector and calculus -/

/-- The covector `(W, x) ↦ tr(A W) + ⟨Λ, X(x)⟩` on the state space (`p = A` the `g`-part,
`Λ₂ = Λ` the `X`-part). -/
private noncomputable def am_covector (A Λ : Mat2) : StrongDual ℝ MatrixState :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w ↦ (A * Matrix.of w.1).trace + traceForm Λ (slMatrix w.2)
      map_add' := fun w w' ↦ by
        simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.of_apply, slMatrix, Prod.fst_add, Prod.snd_add, Pi.add_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one, Fin.isValue]
        ring
      map_smul' := fun c w ↦ by
        simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.of_apply, slMatrix, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue]
        ring }

/-- `am_covector A Λ (W, x) = tr(A W) + ⟨Λ, X(x)⟩`. -/
private lemma am_covector_apply (A Λ : Mat2) (w : MatrixState) :
    am_covector A Λ w = (A * Matrix.of w.1).trace + traceForm Λ (slMatrix w.2) := rfl

/-- The `g`-part of `am_covector A Λ` is `A`. -/
private lemma am_covectorG_covector (A Λ : Mat2) : covectorG (am_covector A Λ) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [covectorG, am_covector_apply, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, traceForm, slMatrix, Pi.single_apply]

/-- The `X`-part of `am_covector A Λ` is `Λ`, for traceless `Λ`. -/
private lemma am_covectorΛ₂_covector (A : Mat2) {Λ : Mat2} (hΛ : Λ.trace = 0) :
    covectorΛ₂ (am_covector A Λ) = Λ := by
  rw [Matrix.trace_fin_two] at hΛ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [covectorΛ₂, am_covector_apply, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, traceForm, slMatrix] <;> linarith

/-- A covector evaluated at `v`: `tr(p v₁) + ⟨Λ₂, X(v₂)⟩`. -/
private lemma am_apply_eq' (π : StrongDual ℝ MatrixState) (v : MatrixState) :
    π v = (covectorG π * Matrix.of v.1).trace + traceForm (covectorΛ₂ π) (slMatrix v.2) := by
  rw [trace_covectorG_mul, traceForm_covectorΛ₂, ← map_add]
  congr 1
  refine Prod.ext ?_ ?_ <;> simp

/-- A curve of covectors whose values at every vector are interval integrable is interval
integrable (the dual of a finite-dimensional space; `π = Σᵢ π(bᵢ) bᵢ*` for a basis `b`). -/
private lemma am_intervalIntegrable_of_apply {F : ℝ → StrongDual ℝ MatrixState} {a b : ℝ}
    (h : ∀ v, IntervalIntegrable (fun r ↦ F r v) volume a b) :
    IntervalIntegrable F volume a b := by
  set B := Module.finBasis ℝ MatrixState
  have e : F = fun r ↦ ∑ i, F r (B i) • LinearMap.toContinuousLinearMap (B.coord i) := by
    funext r
    refine ContinuousLinearMap.ext fun v ↦ ?_
    conv_lhs => rw [← B.sum_repr v]
    rw [map_sum]
    simp [map_smul, mul_comm]
  rw [e]
  have hs := IntervalIntegrable.sum (μ := volume) (a := a) (b := b) Finset.univ
    (f := fun i r ↦ F r (B i) • LinearMap.toContinuousLinearMap (B.coord i))
    fun i _ ↦ ⟨(h (B i)).1.smul_const _, (h (B i)).2.smul_const _⟩
  convert hs using 1
  funext r
  simp

/-- Entrywise absolute continuity of a matrix curve on `[a, b]`. -/
private def am_AC (f : ℝ → Mat2) (a b : ℝ) : Prop :=
  ∀ i j, AbsolutelyContinuousOnInterval (fun s ↦ f s i j) a b

/-- Products of entrywise absolutely continuous curves. -/
private lemma am_AC.mul {f g : ℝ → Mat2} {a b : ℝ} (hf : am_AC f a b) (hg : am_AC g a b) :
    am_AC (fun s ↦ f s * g s) a b := fun i j ↦ by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hf i 0).mul (hg 0 j)).add ((hf i 1).mul (hg 1 j))

/-- Sums of entrywise absolutely continuous curves. -/
private lemma am_AC.add {f g : ℝ → Mat2} {a b : ℝ} (hf : am_AC f a b) (hg : am_AC g a b) :
    am_AC (fun s ↦ f s + g s) a b := fun i j ↦ (hf i j).add (hg i j)

/-- Differences of entrywise absolutely continuous curves. -/
private lemma am_AC.sub {f g : ℝ → Mat2} {a b : ℝ} (hf : am_AC f a b) (hg : am_AC g a b) :
    am_AC (fun s ↦ f s - g s) a b := fun i j ↦ (hf i j).sub (hg i j)

/-- An absolutely continuous scalar times an entrywise absolutely continuous curve. -/
private lemma am_AC.smul {c : ℝ → ℝ} {f : ℝ → Mat2} {a b : ℝ}
    (hc : AbsolutelyContinuousOnInterval c a b) (hf : am_AC f a b) :
    am_AC (fun s ↦ c s • f s) a b := fun i j ↦ hc.mul (hf i j)

/-- A constant times an entrywise absolutely continuous curve. -/
private lemma am_AC.const_smul (c : ℝ) {f : ℝ → Mat2} {a b : ℝ} (hf : am_AC f a b) :
    am_AC (fun s ↦ c • f s) a b := fun i j ↦ (hf i j).const_mul c

/-- Constant curves are absolutely continuous. -/
private lemma am_AC_const (M : Mat2) (a b : ℝ) : am_AC (fun _ ↦ M) a b := fun i j ↦
  (LipschitzWith.const (M i j)).lipschitzOnWith.absolutelyContinuousOnInterval

/-- The adjugate of an entrywise absolutely continuous `2 × 2` curve (`adj` is linear). -/
private lemma am_AC.adjugate {f : ℝ → Mat2} {a b : ℝ} (hf : am_AC f a b) :
    am_AC (fun s ↦ (f s).adjugate) a b := fun i j ↦ by
  simp only [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  exacts [hf 1 1, (hf 0 1).neg, (hf 1 0).neg, hf 0 0]

/-- The trace of an entrywise absolutely continuous curve. -/
private lemma am_AC.trace {f : ℝ → Mat2} {a b : ℝ} (hf : am_AC f a b) :
    AbsolutelyContinuousOnInterval (fun s ↦ (f s).trace) a b := by
  simp only [Matrix.trace_fin_two]
  exact (hf 0 0).add (hf 1 1)

/-- A Carathéodory solution is entrywise absolutely continuous. -/
private lemma am_AC_of_isIntegralCurve {f v : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (h : IsIntegralCurve f v T) : am_AC f 0 T := fun i j ↦
  absolutelyContinuousOnInterval_of_eq_add_integral hT (h i j).1 (h i j).2

/-- A Carathéodory solution has the integrand as derivative at almost every time (Lebesgue's
differentiation theorem). -/
private lemma am_ae_hasDerivAtEntrywise {f v : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (h : IsIntegralCurve f v T) : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAtEntrywise f (v t) t := by
  have h' : ∀ i j, ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt (fun s ↦ f s i j) (v t i j) t :=
    fun i j ↦ ae_hasDerivAt_of_eq_add_integral (h i j).1 ⟨le_rfl, hT⟩ (h i j).2
  filter_upwards [ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ h' i j] with t ht htI i j
    using ht i j htI

/-- The adjugate of a `2 × 2` matrix curve is differentiable, with derivative the adjugate of the
derivative (`adj` is linear on `2 × 2` matrices). -/
private lemma am_hasDerivAtEntrywise_adjugate {f : ℝ → Mat2} {f' : Mat2} {t : ℝ}
    (hf : HasDerivAtEntrywise f f' t) :
    HasDerivAtEntrywise (fun s ↦ (f s).adjugate) f'.adjugate t := by
  rw [hasDerivAtEntrywise_fin_two_iff]
  simp only [Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue]
  exact ⟨hf 1 1, (hf 0 1).neg, (hf 1 0).neg, hf 0 0⟩

/-- `adj X = -X` for traceless `2 × 2` `X`. -/
private lemma am_adjugate_of_trace {X : Mat2} (hX : X.trace = 0) : X.adjugate = -X := by
  rw [Matrix.trace_fin_two] at hX
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- The trace form of two curves continuous on `s` is continuous on `s`. -/
private lemma am_continuousOn_traceForm {f g : ℝ → Mat2} {s : Set ℝ} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun t ↦ traceForm (f t) (g t)) s := by
  have hf' := Matrix.continuousOn_iff_entrywise.1 hf
  have hg' := Matrix.continuousOn_iff_entrywise.1 hg
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  exact (((hf' 0 0).mul (hg' 0 0)).add ((hf' 0 1).mul (hg' 1 0))).add
    (((hf' 1 0).mul (hg' 0 1)).add ((hf' 1 1).mul (hg' 1 1)))

/-- **The lift to the cotangent bundle** (departure from the paper; module docstring). Every
solution `(g, X, Λ₁, Λ_R)` of the state–costate equations of Problem 6.7.1 with control set `U`
(a state trajectory for `U`, `Λ₁, Λ_R ∈ 𝔰𝔩₂(ℝ)`, `Λ_R ⊥ X`, the costate equations) with the
maximum condition over `U` comes from a covector curve `p` on the matrix system satisfying the
adjoint equation and the maximum condition of the maximum principle (with the same multiplier
`λ_cost`), with `Λ₁ = covectorΛ₁ q p` and `Λ_R = covectorΛR q p` for `q = (g, X)`. No boundary
condition is assumed, and `U` need not be compact.

Proof:
1. `Λ₂ := [X, Λ_R]/4 + c X` with `c(t) = ∫₀ᵗ κ`,
   `κ = (⟨Λ₁ - (3/2)λJ, X⟩ + ⟨X', [Λ_R, X]⟩/4)/2`; `κ` is integrable since the entries of
   `X' = [P, X]` are and the other factors are continuous on `[0, T]`.
2. `p(t) := (W, x) ↦ tr(A W) + ⟨Λ₂, slMatrix x⟩` with `A = Λ₁ adj g` (`= Λ₁ g⁻¹`, `det g = 1`)
   (`am_covector`); then `covectorΛ₁ q p = Λ₁` (`A g = Λ₁`, `Λ₁` traceless) and
   `covectorΛR q p = [Λ₂, X] = Λ_R` (`[[X, Λ_R], X] = 4Λ_R`, `am_bracket_bracket`).
3. The maximum condition: `controlHamiltonian_matrix_eq_hamiltonian` and step 2 turn it into the
   maximum condition of the extremal (the null sets `{0, T}` aside).
4. The adjoint equation, coordinate by coordinate: for every vector `v`, `t ↦ p(t)(v)` is
   absolutely continuous (polynomial in the entries of `g`, `X`, `Λ₁`, `Λ_R` and `c`), and at
   almost every `t` (Lebesgue's differentiation theorem) its derivative is
   `tr(A' W) + ⟨Λ₂', slMatrix x⟩ = -F(t)(v)`, `F` the integrand of `IsAdjoint`:
   * `g`-part: `(Λ₁ adj g)' = [Λ₁, X] adj g + Λ₁ adj(gX) = -X Λ₁ adj g`, and the `g`-part of `F`
     is `X p` (`covectorG_comp_fderiv_matrixField_of_ne`);
   * `X`-part: `Λ₂' = -δH/δX` (`am_lift_X`: `[Λ₂, X] = Λ_R` near `t`, so the derivative of
     `[Λ₂, X]` is the right-hand side of `eqn:lamR`), and the `X`-part of `F` is `δH/δX`
     (`hasFunctionalDerivative_fullHamiltonian_of_ne`, `am_hasFunctionalDerivative_X`).
   The fundamental theorem of calculus for absolutely continuous functions gives the integral
   form of each coordinate and the integrability of `t ↦ F(t)(v)`, hence of `F`
   (`am_intervalIntegrable_of_apply`), and `p(t) = p(T) + ∫ₜᵀ F`. -/
theorem IsStateTrajectoryFor.exists_covector {U : Set (Fin 3 → ℝ)} {T : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (hst : IsStateTrajectoryFor U T u g X)
    (htr : ∀ t ∈ Icc 0 T, (Λ₁ t).trace = 0 ∧ (ΛR t).trace = 0 ∧ traceForm (ΛR t) (X t) = 0)
    (hΛ₁ : IsIntegralCurve Λ₁ (fun t ↦ Λ₁ t * X t - X t * Λ₁ t) T)
    (hΛR : IsIntegralCurve ΛR (fun t ↦ costateRHS lam (Λ₁ t) (ΛR t) (X t) (u t)) T)
    (hmax : ∀ᵐ t, t ∈ Ioo 0 T → ∀ v ∈ U,
      hamiltonian lam (Λ₁ t) (ΛR t) (X t) v ≤ hamiltonian lam (Λ₁ t) (ΛR t) (X t) (u t)) :
    ∃ p : ℝ → StrongDual ℝ MatrixState,
      IsAdjoint matrixField matrixCost lam u (fun t ↦ toMatrixState (g t) (X t)) T p ∧
      IsMaximal matrixField matrixCost lam U u (fun t ↦ toMatrixState (g t) (X t)) T p ∧
      ∀ t ∈ Icc 0 T, covectorΛ₁ (toMatrixState (g t) (X t)) (p t) = Λ₁ t ∧
        covectorΛR (toMatrixState (g t) (X t)) (p t) = ΛR t := by
  obtain ⟨hT, -, hU, hstate, hgI, hXI⟩ := hst
  have hT0 : (0 : ℝ) ≤ T := hT.le
  set q : ℝ → MatrixState := fun t ↦ toMatrixState (g t) (X t) with hq
  -- the velocity `X' = [P, X]`, and `κ = (⟨Λ₁ - (3/2)λJ, X⟩ + ⟨X', [Λ_R, X]⟩/4)/2`
  set V : ℝ → Mat2 := fun t ↦ controlP (u t) (X t) * X t - X t * controlP (u t) (X t) with hV
  set κ : ℝ → ℝ := fun t ↦ (traceForm (Λ₁ t - (3 / 2 * lam) • J) (X t) +
      traceForm (V t) (ΛR t * X t - X t * ΛR t) / 4) / 2 with hκdef
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  have hΛ₁c : ContinuousOn Λ₁ (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hΛ₁
  have hΛRc : ContinuousOn ΛR (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hΛR
  -- `κ` is integrable: the entries of `X'` are integrable, the other factors continuous
  have hκ : IntervalIntegrable κ volume 0 T := by
    have hK : ContinuousOn (fun t ↦ ΛR t * X t - X t * ΛR t) (uIcc 0 T) := by
      rw [uIcc_of_le hT0]; exact (hΛRc.mul hXc).sub (hXc.mul hΛRc)
    have hM : ContinuousOn (fun t ↦ traceForm (Λ₁ t - (3 / 2 * lam) • J) (X t)) (uIcc 0 T) := by
      rw [uIcc_of_le hT0]; exact am_continuousOn_traceForm (hΛ₁c.sub continuousOn_const) hXc
    have hKe := Matrix.continuousOn_iff_entrywise.1 hK
    have hVK : IntervalIntegrable (fun t ↦ traceForm (V t) (ΛR t * X t - X t * ΛR t))
        volume 0 T := by
      simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      exact (((hXI 0 0).1.mul_continuousOn (hKe 0 0)).add
        ((hXI 0 1).1.mul_continuousOn (hKe 1 0))).add
        (((hXI 1 0).1.mul_continuousOn (hKe 0 1)).add ((hXI 1 1).1.mul_continuousOn (hKe 1 1)))
    exact ((hM.intervalIntegrable).add (hVK.div_const 4)).div_const 2
  -- the lift: `Λ₂ = [X, Λ_R]/4 + cX` with `c = ∫ κ`, and the `g`-part `p = Λ₁ g⁻¹ = Λ₁ adj g`
  set c : ℝ → ℝ := fun t ↦ ∫ s in (0 : ℝ)..t, κ s with hcdef
  set Λ₂ : ℝ → Mat2 := fun t ↦ (1 / 4 : ℝ) • (X t * ΛR t - ΛR t * X t) + c t • X t with hΛ₂def
  set A : ℝ → Mat2 := fun t ↦ Λ₁ t * (g t).adjugate with hAdef
  set p : ℝ → StrongDual ℝ MatrixState := fun t ↦ am_covector (A t) (Λ₂ t) with hpdef
  -- pointwise facts on `[0, T]`
  have hXtr : ∀ t ∈ Icc 0 T, (X t).trace = 0 := fun t ht ↦ (hstate t ht).2.1
  have hXdet : ∀ t ∈ Icc 0 T, (X t).det = 1 := fun t ht ↦ (hstate t ht).2.2.1
  have hden : ∀ t ∈ Icc 0 T, traceForm (controlMatrix (u t)) (X t) ≠ 0 := fun t ht ↦
    ((hstate t ht).2.2.2 _ (hU t ht)).ne
  have hXq : ∀ t ∈ Icc 0 T, stateX (q t) = X t := fun t ht ↦
    stateX_toMatrixState _ (hXtr t ht)
  have hden' : ∀ t ∈ Icc 0 T, traceForm (controlMatrix (u t)) (stateX (q t)) ≠ 0 := fun t ht ↦ by
    rw [hXq t ht]; exact hden t ht
  have hΛ₂tr : ∀ t ∈ Icc 0 T, (Λ₂ t).trace = 0 := fun t ht ↦ by
    simp only [hΛ₂def, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub,
      Matrix.trace_mul_comm (X t) (ΛR t), sub_self, hXtr t ht, smul_zero, add_zero]
  -- `[Λ₂, X] = Λ_R` (`[[X, Λ_R], X] = 4Λ_R`)
  have hLR : ∀ t ∈ Icc 0 T, Λ₂ t * X t - X t * Λ₂ t = ΛR t := fun t ht ↦ by
    have h4 := am_bracket_bracket (hXtr t ht) (hXdet t ht) (htr t ht).2.1 (htr t ht).2.2
    have e : Λ₂ t * X t - X t * Λ₂ t =
        (1 / 4 : ℝ) • ((X t * ΛR t - ΛR t * X t) * X t - X t * (X t * ΛR t - ΛR t * X t)) := by
      simp only [hΛ₂def, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.smul_mul, Matrix.mul_smul, smul_sub]
      abel
    rw [e, h4, smul_smul]
    norm_num
  have hid1 : ∀ t ∈ Icc 0 T, covectorΛ₁ (q t) (p t) = Λ₁ t := fun t ht ↦ by
    have hAg : A t * g t = Λ₁ t := by
      rw [hAdef, Matrix.mul_assoc, Matrix.adjugate_mul, (hstate t ht).1, one_smul,
        Matrix.mul_one]
    rw [covectorΛ₁, am_covectorG_covector, stateG_toMatrixState, hAg, (htr t ht).1, zero_div,
      zero_smul, sub_zero]
  have hid2 : ∀ t ∈ Icc 0 T, covectorΛR (q t) (p t) = ΛR t := fun t ht ↦ by
    rw [covectorΛR, am_covectorΛ₂_covector _ (hΛ₂tr t ht), hXq t ht, hLR t ht]
  -- the integrand of the adjoint equation, and its `g`- and `X`-parts (Hamilton's equations)
  set F : ℝ → StrongDual ℝ MatrixState := fun r ↦ (p r).comp (linearization matrixField u q r) +
    lam • fderiv ℝ (matrixCost · (u r)) (q r) with hFdef
  have hFG : ∀ t ∈ Icc 0 T, covectorG (F t) = X t * A t := fun t ht ↦ by
    rw [show F t = (p t).comp (fderiv ℝ (matrixField · (u t)) (q t)) +
      lam • fderiv ℝ (matrixCost · (u t)) (q t) from rfl,
      covectorG_comp_fderiv_matrixField_of_ne lam (hden' t ht), am_covectorG_covector, hXq t ht]
  have hFΛ₂ : ∀ t ∈ Icc 0 T, covectorΛ₂ (F t) = Λ₁ t - (3 / 2 * lam) • J +
      (Λ₂ t * controlP (u t) (X t) - controlP (u t) (X t) * Λ₂ t) -
      traceForm (Λ₂ t * controlP (u t) (X t) - controlP (u t) (X t) * Λ₂ t) (X t) •
        controlP (u t) (X t) := fun t ht ↦ by
    have h1 := hasFunctionalDerivative_fullHamiltonian_of_ne lam (hden' t ht) (p t)
    rw [hid1 t ht, am_covectorΛ₂_covector _ (hΛ₂tr t ht), hXq t ht] at h1
    exact am_hasFunctionalDerivative_unique h1
      (am_hasFunctionalDerivative_X lam (htr t ht).1 (hden t ht))
  -- almost everywhere, `t ↦ p(t)(v)` has derivative `-F(t)(v)`
  have hcd : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt c (κ t) t :=
    ae_hasDerivAt_of_eq_add_integral hκ ⟨le_rfl, hT0⟩ (x₀ := 0) fun t _ ↦ by simp [hcdef]
  have hderiv : ∀ v : MatrixState, ∀ᵐ t, t ∈ Ioo 0 T →
      HasDerivAt (fun s ↦ p s v) (-(F t v)) t := by
    intro v
    filter_upwards [am_ae_hasDerivAtEntrywise hT0 hgI, am_ae_hasDerivAtEntrywise hT0 hXI,
      am_ae_hasDerivAtEntrywise hT0 hΛ₁, am_ae_hasDerivAtEntrywise hT0 hΛR, hcd]
      with t hg' hX' hΛ₁' hΛR' hc' htI
    have ht := Ioo_subset_Icc_self htI
    -- `(Λ₁ adj g)' = [Λ₁, X] adj g + Λ₁ adj(gX) = -X Λ₁ adj g`
    have hA' : HasDerivAtEntrywise A (-(X t * A t)) t := by
      refine ((hΛ₁' htI).mul (am_hasDerivAtEntrywise_adjugate (hg' htI))).congr_deriv ?_
      rw [Matrix.adjugate_mul_distrib, am_adjugate_of_trace (hXtr t ht)]
      simp only [hAdef]
      noncomm_ring
    -- `Λ₂'` by the product rule
    have hΛ₂d : HasDerivAtEntrywise Λ₂ ((1 / 4 : ℝ) • ((V t * ΛR t + X t *
        costateRHS lam (Λ₁ t) (ΛR t) (X t) (u t)) -
        (costateRHS lam (Λ₁ t) (ΛR t) (X t) (u t) * X t + ΛR t * V t)) +
        (c t • V t + κ t • X t)) t :=
      ((((hX' htI).mul (hΛR' htI)).sub ((hΛR' htI).mul (hX' htI))).const_smul
        (1 / 4 : ℝ)).add (HasDerivAtEntrywise.smul (hc' htI) (hX' htI))
    -- the derivative of `[Λ₂, X] = Λ_R` is the right-hand side of `eqn:lamR`
    have hcomm := ((hΛ₂d.mul (hX' htI)).sub ((hX' htI).mul hΛ₂d)).unique
      ((hΛR' htI).congr_of_eventuallyEq
        (eventually_of_mem (Icc_mem_nhds htI.1 htI.2) fun s hs ↦ hLR s hs))
    have hΛ₂' := am_lift_X (hXtr t ht) (hXdet t ht) (htr t ht).2.1 (htr t ht).2.2 (htr t ht).1
      (hden t ht) rfl rfl rfl hcomm
    have e : (fun s ↦ p s v) =
        fun s ↦ (A s * Matrix.of v.1).trace + (Λ₂ s * slMatrix v.2).trace := rfl
    rw [e]
    convert ((hA'.mul_const (Matrix.of v.1)).trace).add
      ((hΛ₂d.mul_const (slMatrix v.2)).trace) using 1
    rw [am_apply_eq' (F t) v, hFG t ht, hFΛ₂ t ht, hΛ₂']
    simp only [traceForm, Matrix.neg_mul, Matrix.trace_neg]
    ring
  -- `t ↦ p(t)(v)` is absolutely continuous (polynomial in the entries of `g`, `X`, `Λ₁`, `Λ_R`,
  -- `c`)
  have hac : ∀ v : MatrixState, AbsolutelyContinuousOnInterval (fun s ↦ p s v) 0 T := by
    intro v
    have hcAC : AbsolutelyContinuousOnInterval c 0 T :=
      absolutelyContinuousOnInterval_of_eq_add_integral hT0 hκ fun t _ ↦ by simp [hcdef]
    have hgA := am_AC_of_isIntegralCurve hT0 hgI
    have hXA := am_AC_of_isIntegralCurve hT0 hXI
    have hΛ₁A := am_AC_of_isIntegralCurve hT0 hΛ₁
    have hΛRA := am_AC_of_isIntegralCurve hT0 hΛR
    have hAA : am_AC A 0 T := hΛ₁A.mul hgA.adjugate
    have hΛ₂A : am_AC Λ₂ 0 T :=
      (((hXA.mul hΛRA).sub (hΛRA.mul hXA)).const_smul _).add (am_AC.smul hcAC hXA)
    exact ((hAA.mul (am_AC_const _ 0 T)).trace).add ((hΛ₂A.mul (am_AC_const _ 0 T)).trace)
  -- the fundamental theorem of calculus, coordinate by coordinate
  have hFTC : ∀ v : MatrixState, IntervalIntegrable (fun t ↦ -(F t v)) volume 0 T ∧
      ∀ t ∈ Icc 0 T, p t v = p 0 v + ∫ s in (0 : ℝ)..t, -(F s v) :=
    fun v ↦ (hac v).eq_add_integral_of_ae_hasDerivAt hT0 (hderiv v)
  have hFint : IntervalIntegrable F volume 0 T :=
    am_intervalIntegrable_of_apply fun v ↦ by
      simpa only [Pi.neg_def, neg_neg] using (hFTC v).1.neg
  refine ⟨p, ⟨hFint, fun t ht ↦ ContinuousLinearMap.ext fun v ↦ ?_⟩, ?_,
    fun t ht ↦ ⟨hid1 t ht, hid2 t ht⟩⟩
  · have hsub : IntervalIntegrable F volume t T := hFint.mono_set (by
      rw [uIcc_of_le hT0, uIcc_of_le ht.2]; exact Icc_subset_Icc_left ht.1)
    have hi : IntervalIntegrable (fun s ↦ -(F s v)) volume 0 t := (hFTC v).1.mono_set (by
      rw [uIcc_of_le hT0, uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
    have e := intervalIntegral.integral_interval_sub_left (hFTC v).1 hi
    have h1 := (hFTC v).2 t ht
    have h2 := (hFTC v).2 T ⟨hT0, le_rfl⟩
    simp only [intervalIntegral.integral_neg] at e h1 h2
    rw [add_apply, ContinuousLinearMap.intervalIntegral_apply hsub, h1, h2]
    linarith
  · -- the maximum condition (`controlHamiltonian_matrix_eq_hamiltonian`)
    rw [IsMaximal, ae_restrict_iff' measurableSet_Icc]
    have hne0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
    have hneT : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [hmax, hne0, hneT] with t hmt h0 hTt htI v hv
    have htIoo : t ∈ Ioo 0 T :=
      ⟨lt_of_le_of_ne htI.1 (Ne.symm h0), lt_of_le_of_ne htI.2 hTt⟩
    rw [controlHamiltonian_matrix_eq_hamiltonian, controlHamiltonian_matrix_eq_hamiltonian,
      hid1 t htI, hid2 t htI, hXq t htI]
    exact hmt htIoo v hv

/-! ### Theorem 9.1.6 -/

/-- **Corollary 6.5.3 along a state trajectory for `U`**, with `g(0)` arbitrary: applied to the
normalized `ĝ = g(0)⁻¹ g` (`ĝ' = ĝ X`, `ĝ(0) = I`, `det ĝ = 1`), it gives
`Λ₁(t) = ĝ(t)⁻¹ Λ₁(0) ĝ(t)`. -/
private lemma am_eq_conj {U : Set (Fin 3 → ℝ)} {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ : ℝ → Mat2}
    (h : IsStateTrajectoryFor U T u g X)
    (hΛ : IsIntegralCurve Λ₁ (fun t ↦ Λ₁ t * X t - X t * Λ₁ t) T) :
    ∀ t ∈ Icc 0 T, Λ₁ t = ((g 0)⁻¹ * g t)⁻¹ * Λ₁ 0 * ((g 0)⁻¹ * g t) := by
  obtain ⟨hT, -, -, hst, hgI, hXI⟩ := h
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  have hgc : ContinuousOn g (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hgI
  have hΛc : ContinuousOn Λ₁ (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hΛ
  have hg0 : IsUnit (g 0).det := by rw [(hst 0 ⟨le_rfl, hT.le⟩).1]; exact isUnit_one
  have hG : ∀ t ∈ Icc 0 T, Matrix.HasDerivWithinAtEntrywise (fun s ↦ (g 0)⁻¹ * g s)
      ((g 0)⁻¹ * g t * X t) (Icc 0 T) t := fun t ht ↦ by
    rw [Matrix.mul_assoc]
    exact (Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hgI ht
      ((hgc.mul hXc) t ht)).const_mul _
  have hΛ' : ∀ t ∈ Icc 0 T,
      Matrix.HasDerivWithinAtEntrywise Λ₁ (Λ₁ t * X t - X t * Λ₁ t) (Icc 0 T) t :=
    fun t ht ↦ Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hΛ ht
      (((hΛc.mul hXc).sub (hXc.mul hΛc)) t ht)
  have hdet : ∀ t ∈ Icc 0 T, ((g 0)⁻¹ * g t).det = 1 := fun t ht ↦ by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, (hst 0 ⟨le_rfl, hT.le⟩).1, (hst t ht).1,
      Ring.inverse_one, one_mul]
  exact fun t ht ↦ (corollary6_5_3 T (fun s ↦ (g 0)⁻¹ * g s) X Λ₁ hG
    (Matrix.nonsing_inv_mul _ hg0) hdet hΛ' t ht).1

/-- **Conservation of angular momentum for a rotation-invariant control set** (Theorem 9.1.6 and
Remark 9.1.7 in one statement): for a compact control set `U` closed under rotations, the angular
momentum `𝒜 = ⟨J, Λ₁ + Λ_R⟩` is constant along every solution of the state–costate equations of
Problem 6.7.1 with control set `U` (a state trajectory for `U`, `Λ₁, Λ_R ∈ 𝔰𝔩₂(ℝ)`, `Λ_R ⊥ X`,
`Λ₁' = [Λ₁, X]`, `eqn:lamR`) with the maximum condition over `U`. The transversality conditions,
`g(0) = I`, `H = 0`, `λ_cost ≤ 0` and nontriviality are not assumed: §9.3 (TeX 8136–8295) and
Chapter 10 (TeX 8684–8689, 8945–8946) apply the conservation along such local solutions with
`U = U_r`.

Proof (the book's proof, TeX 7902–7966, with the lift):
1. `IsStateTrajectoryFor.exists_covector`: a covector curve `p` with the adjoint equation, the
   maximum condition, `covectorΛ₁ (q t) (p t) = Λ₁ t` and `covectorΛR (q t) (p t) = Λ_R t`,
   `q t = (g t, X t)`.
2. `IsStateTrajectoryFor.isAdmissibleIn_matrix`: `(u, q)` is admissible in `matrixDomainFor U`.
3. `momentum_rotationField_eq` (Noether–Sussmann): `⟨p(t), τ(J)(q(t))⟩` is constant.
4. `momentum_rotationField` (`det g(t) = 1`):
   `⟨Λ₁(t), g(t)⁻¹ J g(t)⟩ - 𝒜(t) = ⟨Λ₁(0), g(0)⁻¹ J g(0)⟩ - 𝒜(0)`.
5. Corollary 6.5.3 (`corollary6_5_3` for `ĝ = g(0)⁻¹ g`, `am_eq_conj`):
   `Λ₁(t) = ĝ(t)⁻¹ Λ₁(0) ĝ(t)`, so `⟨Λ₁(t), g(t)⁻¹ J g(t)⟩ = tr(g(0) Λ₁(0) g(0)⁻¹ J)`, the same
   at `t = 0`.
6. Subtract: `𝒜(t) = 𝒜(0)`. -/
theorem angularMomentum_conserved {U : Set (Fin 3 → ℝ)} (hU : IsRotationClosed U)
    (hUc : IsCompact U) {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (hst : IsStateTrajectoryFor U T u g X)
    (htr : ∀ t ∈ Icc 0 T, (Λ₁ t).trace = 0 ∧ (ΛR t).trace = 0 ∧ traceForm (ΛR t) (X t) = 0)
    (hΛ₁ : IsIntegralCurve Λ₁ (fun t ↦ Λ₁ t * X t - X t * Λ₁ t) T)
    (hΛR : IsIntegralCurve ΛR (fun t ↦ costateRHS lam (Λ₁ t) (ΛR t) (X t) (u t)) T)
    (hmax : ∀ᵐ t, t ∈ Ioo 0 T → ∀ v ∈ U,
      hamiltonian lam (Λ₁ t) (ΛR t) (X t) v ≤ hamiltonian lam (Λ₁ t) (ΛR t) (X t) (u t)) :
    ∀ t ∈ Icc 0 T, angularMomentum (Λ₁ t) (ΛR t) = angularMomentum (Λ₁ 0) (ΛR 0) := by
  -- the lift to a covector curve with the adjoint equation and the maximum condition
  obtain ⟨p, hadj, hmaxp, hid⟩ := IsStateTrajectoryFor.exists_covector hst htr hΛ₁ hΛR hmax
  -- Noether–Sussmann for the rotations: `⟨p, τ(J)(q)⟩` is constant
  have hN := momentum_rotationField_eq hU hUc hst.isAdmissibleIn_matrix hadj hmaxp
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hst.1.le⟩
  have hdet : ∀ t ∈ Icc 0 T, (g t).det = 1 := fun t ht ↦ (hst.2.2.2.1 t ht).1
  intro t ht
  have h := hN t ht
  -- the momentum map (TeX 7945–7956): `⟨Λ₁, g⁻¹Jg⟩ - 𝒜`
  rw [momentum_rotationField (by rw [stateG_toMatrixState, hdet t ht]; exact one_ne_zero),
    momentum_rotationField (by rw [stateG_toMatrixState, hdet 0 h0]; exact one_ne_zero),
    (hid t ht).1, (hid t ht).2, (hid 0 h0).1, (hid 0 h0).2, stateG_toMatrixState,
    stateG_toMatrixState] at h
  -- Corollary 6.5.3: `⟨Λ₁(t), g(t)⁻¹ J g(t)⟩ = ⟨g(0)Λ₁(0)g(0)⁻¹, J⟩` is constant
  have hg : ∀ s ∈ Icc 0 T, IsUnit (g s).det := fun s hs ↦ by rw [hdet s hs]; exact isUnit_one
  have hk : ∀ s ∈ Icc 0 T, traceForm (Λ₁ s) ((g s)⁻¹ * J * g s) =
      (g 0 * Λ₁ 0 * (g 0)⁻¹ * J).trace := fun s hs ↦ by
    rw [am_eq_conj hst hΛ₁ s hs, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hg 0 h0),
      traceForm]
    rw [show (g s)⁻¹ * g 0 * Λ₁ 0 * ((g 0)⁻¹ * g s) * ((g s)⁻¹ * J * g s) =
        (g s)⁻¹ * (g 0 * Λ₁ 0 * (g 0)⁻¹ * J) * g s by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (g s) (g s)⁻¹, Matrix.mul_nonsing_inv _ (hg s hs), Matrix.one_mul],
      Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ (hg s hs), Matrix.one_mul]
  rw [hk t ht, hk 0 h0] at h
  linarith

/-- `angularMomentum_conserved` along a Pontryagin extremal for `U`. -/
private theorem am_angularMomentum_of_extremal {U : Set (Fin 3 → ℝ)} (hU : IsRotationClosed U)
    (hUc : IsCompact U) {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremalFor U T u g X Λ₁ ΛR lam) :
    ∀ t ∈ Icc 0 T, angularMomentum (Λ₁ t) (ΛR t) = angularMomentum (Λ₁ 0) (ΛR 0) := by
  obtain ⟨hst, -, -, -, -, -, -, hΛ, hΛ₁, hΛR, hmax⟩ := h
  exact angularMomentum_conserved hU hUc hst
    (fun t ht ↦ ⟨(hΛ t ht).1, (hΛ t ht).2.1, (hΛ t ht).2.2.1⟩) hΛ₁ hΛR
    (by filter_upwards [hmax] with t ht htI using (ht htI).2)

/-- **Theorem 9.1.6** (`thm:angular-momentum`, TeX 7894–7966; the introduction's theorem*,
TeX 948–952). The angular momentum `𝒜 = ⟨J, Λ₁ + Λ_R⟩` is conserved along every Pontryagin
extremal of the circular control problem (Problem 9.1.5: control set `U_C`).

The book says "along the optimal trajectory"; its proof, and the introduction, give it for every
Pontryagin extremal, which is stated here (module docstring, "Readings").

Proof (the book's, module docstring): `angularMomentum_conserved` for `U_C = U_1`, closed under
rotations (`isRotationClosed_controlDisk`) and compact (`isCompact_controlDisk`), applied to the
state–costate equations and the maximum condition of the extremal. -/
theorem theorem9_1_6 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremalFor controlDiskC T u g X Λ₁ ΛR lam) :
    ∀ t ∈ Icc 0 T, angularMomentum (Λ₁ t) (ΛR t) = angularMomentum (Λ₁ 0) (ΛR 0) :=
  am_angularMomentum_of_extremal (isRotationClosed_controlDisk 1) (isCompact_controlDisk 1) h

/-! ### Remark 9.1.7 -/

/-- **Remark 9.1.7** (`rem:angular-momentum-disks`, label of this formalization; unlabelled),
third item (TeX 7979–7984): "We also obtain the same conserved quantity for a control set `U_r`
which is a disk of any radius `r` whenever `r² > ⅓`." The hypothesis `r² > ⅓` is not needed
(module docstring).

Proof: `angularMomentum_conserved` for `U_r` (`isRotationClosed_controlDisk`,
`isCompact_controlDisk`), the same argument as Theorem 9.1.6. -/
theorem remark9_1_7 (r : ℝ) {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremalFor (controlDisk r) T u g X Λ₁ ΛR lam) :
    ∀ t ∈ Icc 0 T, angularMomentum (Λ₁ t) (ΛR t) = angularMomentum (Λ₁ 0) (ΛR 0) :=
  am_angularMomentum_of_extremal (isRotationClosed_controlDisk r) (isCompact_controlDisk r) h

/-- The infinitesimal generator `(g, X) ↦ (-gJ, [J, X])` of the action
`(g, X) ↦ (g e^{-θJ}, Ad_{e^{θJ}} X)` of Remark 9.1.7, second item (TeX 7975–7978: "we could also
modify the action to be `g ↦ g exp(-Jθ)`"). -/
noncomputable def rightRotationField (q : MatrixState) : MatrixState :=
  toMatrixState (-(stateG q * J)) (J * stateX q - stateX q * J)

/-- **Remark 9.1.7**, second item: the momentum of the modified action is `-𝒜`, without the
"spurious constant" `⟨Λ₁, Ad_{g⁻¹}J⟩` (TeX 7975–7978).

Proof: as `momentum_rotationField`: `π(-gJ, 0) = -tr(pgJ) = -⟨J, Λ₁⟩` (`J` traceless) and
`π(0, slCoords [J, X]) = ⟨Λ₂, [J, X]⟩ = -⟨J, Λ_R⟩` (entrywise). -/
theorem momentum_rightRotationField (q : MatrixState) (π : StrongDual ℝ MatrixState) :
    momentum rightRotationField q π = -angularMomentum (covectorΛ₁ q π) (covectorΛR q π) := by
  have hc : (J * stateX q - stateX q * J).trace = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  rw [momentum, rightRotationField, toMatrixState, am_apply_eq, slMatrix_slCoords hc]
  have hW : Matrix.of (fun i j ↦ (-(stateG q * J)) i j) = -(stateG q * J) := rfl
  rw [hW]
  simp only [angularMomentum, covectorΛ₁, covectorΛR]
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, J,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, smul_eq_mul,
    ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, Fin.isValue]
  ring

/-- **Remark 9.1.7**, second item: the modified action is by symmetries (`g ↦ g e^{-θJ}` preserves
`det g`, and `(g A⁻¹)(A X A⁻¹) = (gX)A⁻¹`), so `rightRotationField` is an infinitesimal symmetry.

Proof: `am_isInfinitesimalSymmetry` (shared with `isInfinitesimalSymmetry_rotationField`) with
`ℓ = 1`, `L = 0`: the flow `(g, X) ↦ (g e^{-θJ}, Ad_{e^{θJ}} X)`. -/
theorem isInfinitesimalSymmetry_rightRotationField {U : Set (Fin 3 → ℝ)}
    (hU : IsRotationClosed U) (hUc : IsCompact U) :
    IsInfinitesimalSymmetry matrixField matrixCost (matrixDomainFor U) U rightRotationField := by
  have e : rightRotationField = fun q ↦
      toMatrixState (0 * stateG q - stateG q * J) (J * stateX q - stateX q * J) := by
    funext q
    rw [rightRotationField, Matrix.zero_mul, zero_sub]
  rw [e]
  exact am_isInfinitesimalSymmetry hU hUc (fun _ ↦ 1) 0 rfl (fun _ ↦ Matrix.one_mul 1)
    (fun _ ↦ by rw [Matrix.det_one]; exact one_pos)
    (fun θ ↦ (hasDerivAtEntrywise_const (1 : Mat2) θ).congr_deriv (Matrix.zero_mul _).symm)

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
