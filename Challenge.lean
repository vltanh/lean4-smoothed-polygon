module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Challenge: smoothed polygons in the Reinhardt optimal control problem

Statements of record for the formalization of Thomas Hales and Koundinya Vajjha, *Packings of
Smoothed Polygons*, arXiv:2405.04331v1 (2024), Chapter 7: the smoothed `(6k+2)`-gons are Pontryagin
extremals of the Reinhardt optimal control problem with bang-bang control (Theorem 7.5.6), and the
smoothed octagon has Reinhardt's density `(8 - √32 - ln 2)/(√8 - 1)` (the example before
Theorem 7.5.6). The book's main theorem (Mahler's First conjecture, Theorem 16.3.1) is not part of
this formalization.

## The control problem

The Reinhardt problem asks for the centrally symmetric convex disk in the plane whose densest
packing is least dense. The book reformulates it (Chapters 2–4) as an optimal control problem.
A state trajectory on `[0, t_f]` is a pair of curves `g` in `SL₂(ℝ)` and `X` in `𝔰𝔩₂(ℝ)` with

* `g' = gX`, and `X' = [Z_u, X]/⟨Z_u, X⟩`, where `⟨A, B⟩ = tr(AB)` and `Z_u` is the control matrix
  of a measurable control `u(t)` in the simplex `U_T = {u ∈ ℝ³ | uᵢ ≥ 0, u₀ + u₁ + u₂ = 1}`;
* `det X = 1` and the star inequalities `ρᵢ(X) > 0` for all `t` (the state space).

Its cost `-(3/2) ∫₀^{t_f} ⟨J, X⟩ dt` is the area of the corresponding disk, `J = [[0, -1], [1, 0]]`.
The boundary conditions are `g(0) = I₂`, `g(t_f) = R` (the rotation by `π/3`) and
`X(t_f) = R⁻¹X(0)R`.

Differential equations are solved in Carathéodory's sense (`IsIntegralCurve`): each entry of the
solution is the indefinite integral of the corresponding entry of the right-hand side, which is
integrable. The Lie bracket `[A, B]` is written `A * B - B * A`.

## Pontryagin extremals

A Pontryagin extremal (`IsPontryaginExtremal`) lifts a state trajectory by costates `Λ₁, Λ_R` in
`𝔰𝔩₂(ℝ)` and a multiplier `λ_cost ≤ 0`, as the maximum principle requires (§6.2–§6.7 of the book):
`Λ_R ⊥ X`; `(λ_cost, Λ₁, Λ_R) ≠ 0`; the costate equations `Λ₁' = [Λ₁, X]` and
`Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩[P, X] + [-Λ₁ + (3/2)λ_cost J, X]` with `P = Z_u/⟨Z_u, X⟩`; for almost
every `t` the control maximizes the Hamiltonian `H = ⟨Λ₁ - (3/2)λ_cost J, X⟩ - ⟨Λ_R, Z_u⟩/⟨X, Z_u⟩`
over `U_T` and `H = 0`; and the transversality conditions (`g(0) = I₂`, `g(t_f) = R`, and `X`, `Λ₁`,
`Λ_R` at `t_f` are `R⁻¹(·)(0)R`). A control is bang-bang if it takes values in the vertices of
`U_T`.

## The smoothed `(6k+2)`-gon

For `k ≥ 1` let `θ_k = πk/(3k+1)`, let `y₀ > 0` solve `4/(3y₀² + 1) = 2 cos θ_k`, let
`t_sw = ln(4/(3y₀² + 1))/(√3 y₀)` and `t_f = (3k+1) t_sw`. The control `polygonControl k` takes the
vertex values `e₃, e₁, e₂, e₃, e₁, …` of `U_T` on the `3k+1` consecutive intervals of length `t_sw`
(the vertices `e₁, e₂, e₃` are `Pi.single 0 1`, `Pi.single 1 1`, `Pi.single 2 1`). The smoothed
`(6k+2)`-gon is the state trajectory with this control, `g(0) = I₂` and `X(0) = Φ(i y₀)`, where
`Φ(x + iy) = [[x/y, -(x² + y²)/y], [1/y, -x/y]]`.

`smoothed_polygon_extremal` states that this trajectory exists and that every state trajectory
with this control and these initial values (there is exactly one) is bang-bang and lifts to a
Pontryagin extremal. `smoothed_octagon_density` identifies `y₀` and `t_sw` for the octagon
(`k = 1`) with the book's values and states that the cost (the area of the smoothed octagon in the
book's normalization, in which its critical hexagon has area `√12`) is
`√12 (8 - √32 - ln 2)/(√8 - 1) ≈ 3.126 < π`, so that the density, the area divided by `√12`, is
Reinhardt's value `(8 - √32 - ln 2)/(√8 - 1) ≈ 0.902414`.

## Corrections of the printed text

Problem 3.6.2 prints the terminal condition `X(t_f) = R X(0) R⁻¹`; its derivation, the
half-plane form and the transversality conditions of the book all give `R⁻¹ X(0) R`, used here.
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

namespace SmoothedPolygonsChallenge

open SmoothedPolygons

/-- **Theorem 7.5.6** (Hales–Vajjha). For each positive integer `k`, the smoothed `(6k+2)`-gon is a
Pontryagin extremal of the Reinhardt control problem given by a bang-bang control. -/
theorem smoothed_polygon_extremal (k : ℕ) (hk : 1 ≤ k) :
    (∃ g X : ℝ → Mat2, IsStateTrajectory (tf k) (polygonControl k) g X ∧ g 0 = 1 ∧
      X 0 = Φ 0 (y₀ k)) ∧
    ∀ g X : ℝ → Mat2, IsStateTrajectory (tf k) (polygonControl k) g X → g 0 = 1 →
      X 0 = Φ 0 (y₀ k) →
      IsBangBang (tf k) (polygonControl k) ∧
        ∃ (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ),
          IsPontryaginExtremal (tf k) (polygonControl k) g X Λ₁ ΛR lam := by
  sorry

/-- **The smoothed octagon** (the example before Theorem 7.5.6). For `k = 1`,
`y₀ = √((√8 - 1)/3)` and `t_sw = ln 2/(2√(√8 - 1))`, and the trajectory of the smoothed octagon has
cost (area) `√12 (8 - √32 - ln 2)/(√8 - 1) < π`, hence density
`(8 - √32 - ln 2)/(√8 - 1)`. -/
theorem smoothed_octagon_density :
    y₀ 1 = √((√8 - 1) / 3) ∧ tsw 1 = Real.log 2 / (2 * √(√8 - 1)) ∧
      ∀ g X : ℝ → Mat2, IsStateTrajectory (tf 1) (polygonControl 1) g X → g 0 = 1 →
        X 0 = Φ 0 (y₀ 1) →
        reinhardtCost (tf 1) X = √12 * (8 - √32 - Real.log 2) / (√8 - 1) ∧
          reinhardtCost (tf 1) X < Real.pi ∧
          reinhardtCost (tf 1) X / √12 = (8 - √32 - Real.log 2) / (√8 - 1) := by
  sorry

end SmoothedPolygonsChallenge

end
