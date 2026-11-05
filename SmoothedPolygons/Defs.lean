module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Shared definitions

The definitions that the statements of `Challenge.lean` use. The block between the two marker
comments is copied word for word into `Challenge.lean` by `scripts/sync_challenge_defs.py`, so that
the Challenge and the library elaborate the same constants (Palomar's Comparator requires this).
This module imports exactly what `Challenge.lean` imports.

The definitions follow Hales–Vajjha, *Packings of Smoothed Polygons* (arXiv:2405.04331v1):

* the trace form `⟨X, Y⟩ = tr(XY)` on `𝔰𝔩₂(ℝ)` (§3.3), the matrices `J` and `R = exp(Jπ/3)`
  (Definition 3.1.5), the control matrix `Z_u` (equation `eqn:Z0`), the map `Φ` of the upper
  half-plane onto the adjoint orbit of `J` (Lemma 4.2.1), and the star inequalities `ρᵢ(X) > 0`
  (Corollary 3.1.6);
* the Reinhardt control problem (Problem 3.6.2): state trajectories `(g, X)` with
  `g' = gX`, `X' = [Z_u, X]/⟨Z_u, X⟩` and the cost `-(3/2) ∫ ⟨J, X⟩`;
* the state–costate equations and the Hamiltonian (Problem 6.7.1), and Pontryagin extremals: the
  lifted trajectories that satisfy the conditions of the Pontryagin maximum principle listed in
  §6.2 and §6.6 (maximality of the Hamiltonian, vanishing Hamiltonian, nontriviality,
  `λ_cost ≤ 0` constant, transversality);
* bang-bang controls (Definition 7.3.2), and the data of the smoothed `(6k+2)`-gon (§7.5): the
  angle `θ_k`, the height `y₀`, the switching time `t_sw`, the terminal time `t_f = (3k+1) t_sw`
  and the control sequence `e₃, e₁, e₂, e₃, …`.

Conventions: points of `ℝ²` are `Fin 2 → ℝ`; the controls `u = (u₀, u₁, u₂)` are `Fin 3 → ℝ`, so
the vertices `e₁, e₂, e₃` of the simplex `U_T` are `Pi.single 0 1`, `Pi.single 1 1`,
`Pi.single 2 1`. Solutions of differential equations are taken in Carathéodory's sense (the
solution is the indefinite integral of an integrable right-hand side), as usual for measurable
controls. The Lie bracket `[A, B]` is written `A * B - B * A`.
-/

@[expose] public section

-- BEGIN SHARED DEFINITIONS

namespace SmoothedPolygons

open MeasureTheory

/-- The control simplex `U_T = {(u₀, u₁, u₂) | 0 ≤ uᵢ ≤ 1, u₀ + u₁ + u₂ = 1}` (Definition 3.3.3). -/
def controlSimplex : Set (Fin 3 → ℝ) :=
  {u | (∀ i, 0 ≤ u i ∧ u i ≤ 1) ∧ u 0 + u 1 + u 2 = 1}

/-- The real `2 × 2` matrices. -/
abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℝ

/-- The trace form `⟨X, Y⟩ = tr(XY)` (§3.3). -/
def traceForm (X Y : Mat2) : ℝ := (X * Y).trace

/-- The infinitesimal generator `J` of the rotation group (Definition 3.1.5). -/
def J : Mat2 := !![0, -1; 1, 0]

/-- The rotation `R = exp(Jπ/3)` by the angle `π/3` (Definition 3.1.5), written out. -/
noncomputable def R : Mat2 := !![1 / 2, -(√3 / 2); √3 / 2, 1 / 2]

/-- The control matrix `Z_u` of a control `u = (u₀, u₁, u₂)` (equation `eqn:Z0`). -/
noncomputable def controlMatrix (u : Fin 3 → ℝ) : Mat2 :=
  !![(u 1 - u 2) / √3, (u 0 - 2 * u 1 - 2 * u 2) / 3; u 0, (u 2 - u 1) / √3]

/-- The matrix `Φ(x + iy)` of the adjoint orbit of `J` attached to a point `x + iy` of the upper
half-plane (Lemma 4.2.1). -/
noncomputable def Φ (x y : ℝ) : Mat2 := !![x / y, -(x ^ 2 + y ^ 2) / y; 1 / y, -x / y]

/-- The star function `ρ₀(X) = (c + √3 a)/√3` of `X = [[a, b], [c, -a]]` (Corollary 3.1.6). -/
noncomputable def ρ₀ (X : Mat2) : ℝ := (X 1 0 + √3 * X 0 0) / √3

/-- The star function `ρ₁(X) = (c - √3 a)/√3` of `X = [[a, b], [c, -a]]` (Corollary 3.1.6). -/
noncomputable def ρ₁ (X : Mat2) : ℝ := (X 1 0 - √3 * X 0 0) / √3

/-- The star function `ρ₂(X) = -(3b + c)/(2√3)` of `X = [[a, b], [c, -a]]` (Corollary 3.1.6). -/
noncomputable def ρ₂ (X : Mat2) : ℝ := -(3 * X 0 1 + X 1 0) / (2 * √3)

/-- The state space of the Lie-algebra variable: `X ∈ 𝔰𝔩₂(ℝ)` with `det X = 1` satisfying the star
inequalities `ρᵢ(X) > 0` (Corollary 3.1.6, §3.5, Theorem 4.4.1). -/
def IsStarState (X : Mat2) : Prop :=
  X.trace = 0 ∧ X.det = 1 ∧ 0 < ρ₀ X ∧ 0 < ρ₁ X ∧ 0 < ρ₂ X

/-- The matrix `P = Z_u / ⟨Z_u, X⟩` (Theorem 3.4.2, Problem 6.7.1). -/
noncomputable def controlP (u : Fin 3 → ℝ) (X : Mat2) : Mat2 :=
  (traceForm (controlMatrix u) X)⁻¹ • controlMatrix u

/-- The control-dependent Hamiltonian
`H(Λ₁, Λ_R, X; Z_u) = ⟨Λ₁ - (3/2) λ_cost J, X⟩ - ⟨Λ_R, Z_u⟩ / ⟨X, Z_u⟩`
(equation `eqn:full-hamiltonian`). -/
noncomputable def hamiltonian (lam : ℝ) (Λ₁ ΛR X : Mat2) (u : Fin 3 → ℝ) : ℝ :=
  traceForm (Λ₁ - (3 / 2 * lam) • J) X -
    traceForm ΛR (controlMatrix u) / traceForm X (controlMatrix u)

/-- `f` solves `f' = v` on `[0, T]` in Carathéodory's sense: each entry of `v` is integrable on
`[0, T]` and each entry of `f` is the indefinite integral of the corresponding entry of `v`. -/
def IsIntegralCurve (f v : ℝ → Mat2) (T : ℝ) : Prop :=
  ∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume 0 T ∧
    ∀ t ∈ Set.Icc 0 T, f t i j = f 0 i j + ∫ s in (0 : ℝ)..t, v s i j

/-- A state trajectory of the Reinhardt control problem on `[0, T]` (Problem 3.6.2, with state
space `SL₂(ℝ) × 𝔥*` by Theorem 4.4.1): a measurable control `u` with values in the simplex `U_T`,
`g` with values in `SL₂(ℝ)`, `X` with values in the star states, `g' = gX` and
`X' = [P, X]` with `P = Z_u / ⟨Z_u, X⟩`. No boundary condition is imposed. -/
def IsStateTrajectory (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2) : Prop :=
  0 < T ∧ Measurable u ∧ (∀ t ∈ Set.Icc 0 T, u t ∈ controlSimplex) ∧
    (∀ t ∈ Set.Icc 0 T, (g t).det = 1 ∧ IsStarState (X t)) ∧
    IsIntegralCurve g (fun t ↦ g t * X t) T ∧
    IsIntegralCurve X (fun t ↦ controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) T

/-- A Pontryagin extremal of the Reinhardt control problem on `[0, T]` (§6.2, Problem 6.7.1,
§6.6): a state trajectory `(g, X)` with control `u`, lifted by costate variables `Λ₁, Λ_R` and a
constant multiplier `λ_cost ≤ 0`, such that

* `Λ₁, Λ_R ∈ 𝔰𝔩₂(ℝ)`, `Λ_R ⊥ X` (because `Λ_R = [Λ₂, X]`), and `(λ_cost, Λ₁, Λ_R) ≠ 0` at every
  time;
* the costate equations `Λ₁' = [Λ₁, X]` and
  `Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩ [P, X] + [-Λ₁ + (3/2) λ_cost J, X]` hold;
* for almost every time the control maximizes the Hamiltonian over `U_T`, and the Hamiltonian
  vanishes;
* the transversality conditions `g(0) = I`, `g(T) = R`, `X(T) = R⁻¹X(0)R`,
  `Λ₁(T) = R⁻¹Λ₁(0)R` and `Λ_R(T) = R⁻¹Λ_R(0)R` hold. -/
def IsPontryaginExtremal (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) : Prop :=
  IsStateTrajectory T u g X ∧
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
        ∀ v ∈ controlSimplex,
          hamiltonian lam (Λ₁ t) (ΛR t) (X t) v ≤ hamiltonian lam (Λ₁ t) (ΛR t) (X t) (u t)

/-- A control is bang-bang on `[0, T]` if its values are extreme points of the control simplex
`U_T` (Definition 7.3.2). -/
def IsBangBang (T : ℝ) (u : ℝ → Fin 3 → ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 T, u t ∈ Set.extremePoints ℝ (controlSimplex)

/-- The cost `-(3/2) ∫₀ᵀ ⟨J, X⟩ dt` of a trajectory (equation `eqn:cost`); for the trajectory of a
balanced disk in circle representation it is the area of the disk. -/
noncomputable def reinhardtCost (T : ℝ) (X : ℝ → Mat2) : ℝ :=
  -(3 / 2) * ∫ t in (0 : ℝ)..T, traceForm J (X t)

/-- The angle `θ_k = πk/(3k+1)` of the smoothed `(6k+2)`-gon (Lemma 7.5.5). -/
noncomputable def θ (k : ℕ) : ℝ := Real.pi * k / (3 * k + 1)

/-- The height `y₀` of the initial point `z₀ = i y₀` of the smoothed `(6k+2)`-gon: the positive
solution of `4/(3y₀² + 1) = 2 cos θ_k` (Lemma 7.5.5). -/
noncomputable def y₀ (k : ℕ) : ℝ := √((2 / Real.cos (θ k) - 1) / 3)

/-- The switching time `t_sw = ln(4/(3y₀² + 1)) / (√3 y₀)` of the smoothed `(6k+2)`-gon
(equation `eqn:t1`). -/
noncomputable def tsw (k : ℕ) : ℝ := Real.log (4 / (3 * y₀ k ^ 2 + 1)) / (√3 * y₀ k)

/-- The terminal time `t_f = (3k+1) t_sw` of the smoothed `(6k+2)`-gon (Lemma 7.5.5). -/
noncomputable def tf (k : ℕ) : ℝ := (3 * k + 1) * tsw k

/-- The control of the smoothed `(6k+2)`-gon (equation `eqn:3k+1`): on the `i`-th switching interval
`[i t_sw, (i+1) t_sw)` it is the vertex `R⁻ⁱ · e₃` of `U_T`, so the controls are
`e₃, e₁, e₂, e₃, e₁, …`, that is, `Pi.single ((2 + i) mod 3) 1`. -/
noncomputable def polygonControl (k : ℕ) (t : ℝ) : Fin 3 → ℝ :=
  Pi.single (⟨(2 + ⌊t / tsw k⌋₊) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) 1

end SmoothedPolygons

-- END SHARED DEFINITIONS

end
