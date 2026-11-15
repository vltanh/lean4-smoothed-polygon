module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Challenge: smoothed polygons in the Reinhardt optimal control problem

Statements of record for the formalization of Thomas Hales and Koundinya Vajjha, *Packings of
Smoothed Polygons*, arXiv:2405.04331v1 (2024): the book's main theorem, Mahler's First conjecture
(Theorem 16.3.1: the global minimizer of the Reinhardt optimal control problem is bang-bang with
finitely many switches, and the worst disk `K_min` is a smoothed polygon of the sort described by
Reinhardt and Mahler), and, from Chapter 7, that the smoothed `(6k+2)`-gons are Pontryagin
extremals of the Reinhardt optimal control problem with bang-bang control (Theorem 7.5.6) and that
the smoothed octagon has Reinhardt's density `(8 - √32 - ln 2)/(√8 - 1)` (the example before
Theorem 7.5.6).

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
`Λ_R` at `t_f` are `R⁻¹(·)(0)R`). The nontriviality condition is imposed on the reduced costate
`(λ_cost, Λ₁, Λ_R)`, with `Λ_R = [Λ₂, X]`: imposed on the full costate `(Λ₁, Λ₂)` of §6.2 of the
book, it would let every state trajectory lift (`λ_cost = 0`, `Λ₁ = 0`, `Λ₂ = X`, so `Λ_R = 0`).
A control is bang-bang if it takes values in the vertices of
`U_T`.

## The smoothed `(6k+2)`-gon

For `k ≥ 1` let `θ_k = πk/(3k+1)`, let `y₀ > 0` solve `4/(3y₀² + 1) = 2 cos θ_k`, let
`t_sw = ln(4/(3y₀² + 1))/(√3 y₀)` and `t_f = (3k+1) t_sw`. The control `polygonControl k` takes the
vertex values `e₃, e₁, e₂, e₃, e₁, …` of `U_T` on the `3k+1` consecutive intervals of length `t_sw`
(the vertices `e₁, e₂, e₃` are `Pi.single 0 1`, `Pi.single 1 1`, `Pi.single 2 1`). The smoothed
`(6k+2)`-gon is the state trajectory with this control, `g(0) = I₂` and `X(0) = Φ(i y₀)`, where
`Φ(x + iy) = [[x/y, -(x² + y²)/y], [1/y, -x/y]]`.

`smoothed_polygon_extremal` states that this trajectory exists and that every state trajectory
with this control and these initial values (there is exactly one on `[0, t_f]`) is bang-bang and
lifts to a Pontryagin extremal. `smoothed_octagon_density` identifies `y₀` and `t_sw` for the
octagon (`k = 1`) with the book's values and states that the cost (the area of the smoothed
octagon in the book's normalization, in which its critical hexagon has area `√12`) is
`√12 (8 - √32 - ln 2)/(√8 - 1) ≈ 3.126 < π`, so that the density, the area divided by `√12`, is
Reinhardt's value `(8 - √32 - ln 2)/(√8 - 1) ≈ 0.902414`.

## Mahler's First conjecture

**Global minimizers** (`IsReinhardtAdmissible`, `IsReinhardtMinimizer`; Problem 3.6.2,
TeX 3203–3237). An admissible trajectory is a state trajectory on `[0, T]`, for some terminal time
`T > 0` (the terminal time is free), with the boundary conditions `g(0) = I₂`, `g(T) = R` and
`X(T) = R⁻¹X(0)R`. A global minimizer is an admissible trajectory whose cost
`-(3/2) ∫₀ᵀ ⟨J, X⟩ dt` (`reinhardtCost`) is at most the cost of every admissible trajectory, with
any terminal time.

**Bang-bang with finitely many switches** (`IsFiniteBangBang a b u`; Definition 7.3.2,
TeX 5844–5848, with the finitely many switches of Theorem 16.3.1): there is a finite set `S` of
times such that every `t ∈ (a, b)` outside `S` has a neighbourhood on which `u` is almost
everywhere equal to one vertex `e_{i+1}` of `U_T` (`vertex i = Pi.single i 1`). A measurable
control matters only up to equality almost everywhere, so this is "equal almost everywhere to a
piecewise constant function with values in the vertices and finitely many switches".

**The worst disks** (`minimaxDensity`, `IsWorstDisk`; §2.1, TeX 1244–1267). The minimax density
is `δ_min = inf δ(K)` over the centrally symmetric convex disks `K`, with `δ(K)` the greatest
packing density (`greatestPackingDensity`, Definition 2.1.1); a worst disk `K_min` is a centrally
symmetric convex disk with `δ(K_min) = δ_min`.

**Smoothed polygons** (`IsSupportLine`, `IsHyperbolicArc`, `IsSmoothedPolygonBoundary`,
`IsSmoothedPolygon`; Theorem 16.3.1 and its gloss, TeX 12789–12804). A support line of `K`
(Definition 2.2.3, TeX 1422–1425) is a line `{x | a · x = c}`, `a ≠ 0`, that meets `K` and has
`K` on one side. A hyperbolic arc (the conclusion of Lemma 3.1.8, TeX 2554) is a continuous
injective curve on `[α, β]`, `α < β`, on a hyperbola `det(d₁, x - p₁) · det(d₂, x - p₂) = c`,
`c ≠ 0`, whose asymptotes are the non-parallel lines `p₁ + ℝ d₁` and `p₂ + ℝ d₂`. The book's gloss
of "a finite-sided smoothed polygon with rounded hyperbolic arcs at each corner of the sort
described by Reinhardt and Mahler" is "the minimizer `K_min` has no corners and the boundary
alternates between straight edge segments and hyperbolic arcs, whose asymptotes are lines
extending the straight edge segments of the boundary". `IsSmoothedPolygon K` reads it as: `K` is
a centrally symmetric convex disk with a unique support line at every boundary point (no
corners), and its boundary is the union of finitely many segments `[a_k, b_k]` (`a_k ≠ b_k`) and
finitely many hyperbolic arcs, each of which begins and ends on a segment ("alternates") and has
as asymptotes the lines of two of the segments.

`mahler_first_conjecture` states both sentences of Theorem 16.3.1: the control of every global
minimizer is bang-bang with finitely many switches on `(0, T)`, and every worst disk is a smoothed
polygon. "The global minimizer" and "the minimizer `K_min`" presuppose uniqueness, which the book
does not prove; the statement is for every global minimizer and every `K_min` (both exist).

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
  time (the nontriviality condition of §6.2, for the reduced costate `(Λ₁, Λ_R)` of
  Problem 6.7.1; it excludes the spurious lift `λ_cost = 0`, `Λ₁ = 0`, `Λ₂ = X`);
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
`U_T` (Definition 7.3.2; the clause "with discontinuous switching" of the definition describes the
switching and is not a condition). -/
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

/-! ### Multi-points and balanced disks (Definitions 2.4.1, 2.4.7) -/

/-- The determinant `det(v, w) = v₁w₂ - v₂w₁` of the `2 × 2` matrix with columns `v, w`. -/
def det2 (v w : Fin 2 → ℝ) : ℝ := v 0 * w 1 - v 1 * w 0

/-- A multi-point (Definition 2.4.1): `s : ℤ/6ℤ → ℝ²` with `s₀ + s₂ + s₄ = 0`,
`s_{j+3} = -s_j` and `det(s_j, s_{j+1}) = √3/2` for all `j` (equations `eqn:multi`,
`eqn:sqrt12`); the first condition is imposed for every shift `j`, as in equation
`eqn:multi-point-properties`. -/
def IsMultiPoint (s : ZMod 6 → Fin 2 → ℝ) : Prop :=
  ∀ j : ZMod 6, s j + s (j + 2) + s (j + 4) = 0 ∧ s (j + 3) = -s j ∧
    det2 (s j) (s (j + 1)) = √3 / 2

/-- The sixth roots of unity `s_j* = exp(2πij/6)`, as points of `ℝ²`. -/
noncomputable def sixthRoot (j : ZMod 6) : Fin 2 → ℝ :=
  ![Real.cos (Real.pi * j.val / 3), Real.sin (Real.pi * j.val / 3)]

/-- A centrally symmetric convex disk centered at the origin (§1.1, §2.1): a compact convex set
with nonempty interior, invariant under `x ↦ -x`. -/
def IsCCSDisk (K : Set (Fin 2 → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧ ∀ x ∈ K, -x ∈ K

/-- A balanced pair `(K, σ)` (Definition 2.4.7): `K` is a centrally symmetric convex disk and
`σ` is a multi-curve of six regular `C¹` curves `σ_j : ℝ → ℝ²` such that

1. each `σ_j` is `C¹` and regular;
2. each derivative `σ_j'` is Lipschitz;
3. `j ↦ σ_j(t)` is a multi-point for every `t`;
4. the curvature constraint `det(σ_j'(t), σ_j''(t)) ≥ 0` holds for almost every `t`;
5. (star condition) `σ_j'(t)` points into the open cone with apex `σ_j(t)` and rays through
   `σ_{j+1}(t)` and `σ_j(t) + σ_{j+1}(t)`, that is, `σ_j' = α (σ_{j+1} - σ_j) + β σ_{j+1}` with
   `α, β > 0`;
6. the curves are periodic with the common period `6 t_f`, and each `σ_j` restricted to one
   period is a simple closed curve whose image is the boundary of `K`.

The counterclockwise orientation required by item 1 of the definition follows from items 3 and 5
(`det(σ_j, σ_j') > 0`). -/
def IsBalancedPair (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ) : Prop :=
  IsCCSDisk K ∧
    (∀ j, ContDiff ℝ 1 (σ j) ∧ ∀ t, deriv (σ j) t ≠ 0) ∧
    (∀ j, ∃ C, LipschitzWith C (deriv (σ j))) ∧
    (∀ t, IsMultiPoint fun j ↦ σ j t) ∧
    (∀ j, ∀ᵐ t, 0 ≤ det2 (deriv (σ j) t) (deriv (deriv (σ j)) t)) ∧
    (∀ j t, ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      deriv (σ j) t = α • (σ (j + 1) t - σ j t) + β • σ (j + 1) t) ∧
    0 < tf ∧ (∀ j t, σ j (t + 6 * tf) = σ j t) ∧
    (∀ j, Set.InjOn (σ j) (Set.Ico 0 (6 * tf))) ∧
    (∀ j, σ j '' Set.Ico 0 (6 * tf) = frontier K)

/-- A balanced pair is in circle representation (§2.4) if `σ_j(0) = s_j*` for all `j`. -/
def IsCircleRepresentation (σ : ZMod 6 → ℝ → Fin 2 → ℝ) : Prop :=
  ∀ j, σ j 0 = sixthRoot j

/-! ### Convex disks and packing densities (Definition 2.1.1) -/

/-- A convex disk (§1.1, §2.1): a compact convex set with nonempty interior. -/
def IsConvexDisk (K : Set (Fin 2 → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- The Euclidean disk `B_r = {x | x₀² + x₁² ≤ r²}` of radius `r` centered at the origin
(Definition 2.1.1). -/
def euclidDisk (r : ℝ) : Set (Fin 2 → ℝ) := {x | x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2}

/-- `K'` is a congruent copy of `K` (§2.1): its image `{A x + b | x ∈ K}` under a Euclidean
isometry, with `A` an orthogonal matrix. -/
def IsCongruentCopy (K K' : Set (Fin 2 → ℝ)) : Prop :=
  ∃ A ∈ Matrix.orthogonalGroup (Fin 2) ℝ, ∃ b : Fin 2 → ℝ, K' = (fun x ↦ Matrix.mulVec A x + b) '' K

/-- A packing (§2.1): a family of convex disks, any two distinct members of which do not overlap,
that is, have disjoint interiors. -/
def IsPacking (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  (∀ K' ∈ P, IsConvexDisk K') ∧ P.Pairwise fun A B ↦ Disjoint (interior A) (interior B)

/-- A packing with congruent copies of `K` (Definition 2.1.1). -/
def IsPackingOfCopies (K : Set (Fin 2 → ℝ)) (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  IsPacking P ∧ ∀ K' ∈ P, IsCongruentCopy K K'

/-- The ratio `(1/area(B_r)) Σ_{K' ∈ P} area(K' ∩ B_r)` of Definition 2.1.1, in `[0, ∞]`. -/
noncomputable def packingRatio (P : Set (Set (Fin 2 → ℝ))) (r : ℝ) : ENNReal :=
  (∑' K' : P, volume ((K' : Set (Fin 2 → ℝ)) ∩ euclidDisk r)) / volume (euclidDisk r)

/-- The upper density `limsup_{r → ∞} (1/area(B_r)) Σ_{K' ∈ P} area(K' ∩ B_r)` of a packing
(Definition 2.1.1). -/
noncomputable def upperDensity (P : Set (Set (Fin 2 → ℝ))) : ENNReal :=
  Filter.limsup (packingRatio P) Filter.atTop

/-- The lower density `liminf_{r → ∞} (1/area(B_r)) Σ_{K' ∈ P} area(K' ∩ B_r)` of a packing
(Definition 2.1.1). -/
noncomputable def lowerDensity (P : Set (Set (Fin 2 → ℝ))) : ENNReal :=
  Filter.liminf (packingRatio P) Filter.atTop

/-- The density of `P` exists (Definition 2.1.1): the upper and lower densities exist (are
finite) and coincide. -/
def HasDensity (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  upperDensity P ≠ ⊤ ∧ upperDensity P = lowerDensity P

/-- The density `δ(K, P)` of a packing (Definition 2.1.1): the common value of the upper and
lower densities, when the density exists (`HasDensity`). -/
noncomputable def packingDensity (P : Set (Set (Fin 2 → ℝ))) : ℝ :=
  (upperDensity P).toReal

/-- **Definition 2.1.1** (greatest packing density).
`δ(K) = sup {δ(K, P) | δ(K, P) exists, and P is a packing with congruent copies of K}`. -/
noncomputable def greatestPackingDensity (K : Set (Fin 2 → ℝ)) : ℝ :=
  sSup {d | ∃ P, IsPackingOfCopies K P ∧ HasDensity P ∧ packingDensity P = d}

/-! ### Mahler's First conjecture (Theorem 16.3.1)

The objects of the statement of Theorem 16.3.1: global minimizers of the Reinhardt control problem
(Problem 3.6.2), bang-bang controls with finitely many switches, the worst disks `K_min` (§2.1),
support lines (Definition 2.2.3) and smoothed polygons (Theorem 16.3.1). -/

/-- The vertex `e_{i+1}` of the control simplex `U_T`: `vertex 0 = e₁ = (1, 0, 0)`,
`vertex 1 = e₂ = (0, 1, 0)`, `vertex 2 = e₃ = (0, 0, 1)`. -/
noncomputable def vertex (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1

/-- **Problem 3.6.2** (`pbm:reinhardt-optimal-control`). An admissible trajectory of the
Reinhardt control problem: a state trajectory on `[0, t_f]` (`g' = gX`, `X' = [Z_u, X]/⟨Z_u, X⟩`,
control in `U_T`, `X(t)` satisfying the star conditions with `det X = 1`) with the initial
condition `g(0) = I₂` and the terminal conditions `g(t_f) = R` and `X(t_f) = R⁻¹X(0)R`.

The problem prints the terminal condition as `X(t_f) = R X₀ R⁻¹`; the derivation that precedes it
(§3.5), the half-plane form (Problem 4.5.1) and the transversality conditions (§6.6) all give
`X(t_f) = R⁻¹ X₀ R`, which differs because `Ad_R` has order 3. This is a misprint, corrected
here. -/
def IsReinhardtAdmissible (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2) : Prop :=
  IsStateTrajectory T u g X ∧ g 0 = 1 ∧ g T = R ∧ X T = R⁻¹ * X 0 * R

/-- A global minimizer of the Reinhardt control problem (Problem 3.6.2): an admissible trajectory
whose cost `-(3/2) ∫ ⟨J, X⟩` is at most the cost of every admissible trajectory. -/
def IsReinhardtMinimizer (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2) : Prop :=
  IsReinhardtAdmissible T u g X ∧
    ∀ (T' : ℝ) (u' : ℝ → Fin 3 → ℝ) (g' X' : ℝ → Mat2), IsReinhardtAdmissible T' u' g' X' →
      reinhardtCost T X ≤ reinhardtCost T' X'

/-- The control `u` is **bang-bang with finitely many switches on `[a, b]`** (Definition 7.3.2;
Theorems 8.1.4, 8.3.2, 16.3.1: "equal a.e. to a piecewise constant function … with finitely many
switches"): off a finite set `S` of times, `u` is almost everywhere constant near each time of
`(a, b)`, equal to a vertex of `U_T`. (On each interval between consecutive points of `S ∪ {a, b}`
it is then almost everywhere equal to one vertex.) -/
def IsFiniteBangBang (a b : ℝ) (u : ℝ → Fin 3 → ℝ) : Prop :=
  ∃ S : Finset ℝ, ∀ t ∈ Set.Ioo a b, t ∉ S → ∃ i : Fin 3, ∃ ε > 0,
    ∀ᵐ τ, τ ∈ Set.Ioo (t - ε) (t + ε) → u τ = vertex i

/-- The minimax density `δ_min = inf_{K ∈ 𝔎_ccs} δ(K)` (§2.1): the least greatest packing density
among all centrally symmetric convex disks. -/
noncomputable def minimaxDensity : ℝ :=
  sInf {d | ∃ K, IsCCSDisk K ∧ greatestPackingDensity K = d}

/-- `K` is a worst disk `K_min` (§2.1): a centrally symmetric convex disk with
`δ(K_min) = δ_min`, the worst greatest packing density. -/
def IsWorstDisk (K : Set (Fin 2 → ℝ)) : Prop :=
  IsCCSDisk K ∧ greatestPackingDensity K = minimaxDensity

/-- **Definition 2.2.3** (support line; `def:support`). For a convex disk `K`, a support line is a
line containing at least one point of `K` that does not separate any two points of `K`. The line
is `{x | a · x = c}` with `a ≠ 0`; it separates `x` and `y` when they lie strictly on opposite
sides, `(a · x - c)(a · y - c) < 0`. -/
def IsSupportLine (K ℓ : Set (Fin 2 → ℝ)) : Prop :=
  (∃ a : Fin 2 → ℝ, a ≠ 0 ∧ ∃ c : ℝ, ℓ = {x | a ⬝ᵥ x = c} ∧
    ∀ x ∈ K, ∀ y ∈ K, 0 ≤ (a ⬝ᵥ x - c) * (a ⬝ᵥ y - c)) ∧ (ℓ ∩ K).Nonempty

/-- `γ` traces on `[α, β]` (`α < β`, continuous and injective there) an arc of the hyperbola
`det(d₁, x - p₁) · det(d₂, x - p₂) = c`, `c ≠ 0`, whose asymptotes are the non-parallel lines
`p₁ + ℝ d₁` and `p₂ + ℝ d₂`: the form of the conclusion of Lemma 3.1.8 (`lemma3_1_8`). -/
def IsHyperbolicArc (γ : ℝ → Fin 2 → ℝ) (α β : ℝ) (p₁ d₁ p₂ d₂ : Fin 2 → ℝ) : Prop :=
  α < β ∧ ContinuousOn γ (Set.Icc α β) ∧ Set.InjOn γ (Set.Icc α β) ∧ d₁ ≠ 0 ∧ d₂ ≠ 0 ∧
    det2 d₁ d₂ ≠ 0 ∧ ∃ c : ℝ, c ≠ 0 ∧ ∀ t ∈ Set.Icc α β, det2 d₁ (γ t - p₁) * det2 d₂ (γ t - p₂) = c

/-- **The boundary of a smoothed polygon** (Remark 8.3.3; Theorem 16.3.1 and its gloss, TeX
12789–12804): the boundary of `K` is the union of finitely many straight edges `[a_k, b_k]`
(`a_k ≠ b_k`) and finitely many hyperbolic arcs `γ_l([α_l, β_l])`; each hyperbolic arc has as
asymptotes the lines extending two of the edges ("hyperbolic arcs, whose asymptotes are lines
extending the straight edge segments of the boundary") and begins and ends on edges (the boundary
alternates between edges and hyperbolic arcs: each hyperbolic arc rounds a corner between two
edges). -/
def IsSmoothedPolygonBoundary (K : Set (Fin 2 → ℝ)) : Prop :=
  ∃ (m n : ℕ) (a b : Fin m → Fin 2 → ℝ) (γ : Fin n → ℝ → Fin 2 → ℝ) (α β : Fin n → ℝ),
    (∀ k, a k ≠ b k) ∧
    (∀ l, ∃ k₁ k₂, IsHyperbolicArc (γ l) (α l) (β l) (a k₁) (b k₁ - a k₁) (a k₂) (b k₂ - a k₂)) ∧
    (∀ l, γ l (α l) ∈ ⋃ k, segment ℝ (a k) (b k)) ∧
    (∀ l, γ l (β l) ∈ ⋃ k, segment ℝ (a k) (b k)) ∧
    frontier K = (⋃ k, segment ℝ (a k) (b k)) ∪ ⋃ l, γ l '' Set.Icc (α l) (β l)

/-- **A finite-sided smoothed polygon with rounded hyperbolic arcs at each corner, of the sort
described by Reinhardt and Mahler** (Theorem 16.3.1, TeX 12792–12804: "the minimizer `K_min` has
no corners and the boundary alternates between straight edge segments and hyperbolic arcs, whose
asymptotes are lines extending the straight edge segments of the boundary"): a centrally
symmetric convex disk with a unique support line at every boundary point (no corners,
Lemma 2.2.5's form) whose boundary is that of a smoothed polygon (`IsSmoothedPolygonBoundary`). -/
def IsSmoothedPolygon (K : Set (Fin 2 → ℝ)) : Prop :=
  IsCCSDisk K ∧ (∀ x ∈ frontier K, ∃! ℓ, IsSupportLine K ℓ ∧ x ∈ ℓ) ∧
    IsSmoothedPolygonBoundary K

end SmoothedPolygons

-- END SHARED DEFINITIONS

namespace SmoothedPolygonsChallenge

open SmoothedPolygons

/-- **Theorem 16.3.1** (Mahler's First conjecture; Hales–Vajjha). The global minimizer of the
Reinhardt optimal control problem is a bang-bang solution with finitely many switches. In
particular, the minimizer `K_min` of the Reinhardt problem is a finite-sided smoothed polygon with
rounded hyperbolic arcs at each corner of the sort described by Reinhardt and Mahler. -/
theorem mahler_first_conjecture :
    (∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsReinhardtMinimizer T u g X →
      IsFiniteBangBang 0 T u) ∧
    ∀ K : Set (Fin 2 → ℝ), IsWorstDisk K → IsSmoothedPolygon K := by
  sorry

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

/-- **The smoothed octagon** (the example before Theorem 7.5.6, with the area formula `eqn:cost`
of §3.2). For `k = 1`, `y₀ = √((√8 - 1)/3)` and `t_sw = ln 2/(2√(√8 - 1))`; every trajectory of
the smoothed octagon has cost `√12 (8 - √32 - ln 2)/(√8 - 1) < π`, so cost/√12 is
`(8 - √32 - ln 2)/(√8 - 1)`; and the trajectory defines a balanced disk `K` in circle
representation (`σ_j(t) = g(t) s_j*`, `σ_j(t + t_f) = σ_{j+1}(t)`) whose area is that cost and whose
greatest packing density (Definition 2.1.1) is `(8 - √32 - ln 2)/(√8 - 1)`. -/
theorem smoothed_octagon_density :
    y₀ 1 = √((√8 - 1) / 3) ∧ tsw 1 = Real.log 2 / (2 * √(√8 - 1)) ∧
      (∀ g X : ℝ → Mat2, IsStateTrajectory (tf 1) (polygonControl 1) g X → g 0 = 1 →
        X 0 = Φ 0 (y₀ 1) →
        reinhardtCost (tf 1) X = √12 * (8 - √32 - Real.log 2) / (√8 - 1) ∧
          reinhardtCost (tf 1) X < Real.pi ∧
          reinhardtCost (tf 1) X / √12 = (8 - √32 - Real.log 2) / (√8 - 1)) ∧
    ∃ (g X : ℝ → Mat2) (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ),
      IsStateTrajectory (tf 1) (polygonControl 1) g X ∧ g 0 = 1 ∧ X 0 = Φ 0 (y₀ 1) ∧
      (∀ j t, σ j t = Matrix.mulVec (g t) (sixthRoot j)) ∧ (∀ j t, σ j (t + tf 1) = σ (j + 1) t) ∧
      IsBalancedPair K σ (tf 1) ∧ IsCircleRepresentation σ ∧
      MeasureTheory.volume K = ENNReal.ofReal (√12 * (8 - √32 - Real.log 2) / (√8 - 1)) ∧
      greatestPackingDensity K = (8 - √32 - Real.log 2) / (√8 - 1) := by
  sorry

end SmoothedPolygonsChallenge

end
