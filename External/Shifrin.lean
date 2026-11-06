module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Convex plane curves have curvature of one sign

Cited in the proof of Lemma 2.4.6 of Hales–Vajjha, *Packings of Smoothed Polygons*, from
T. Shifrin, *Differential Geometry: A First Course in Curves and Surfaces*, University of Georgia,
2015, Proposition 3.8: a simple closed regular plane curve is convex if and only if its
orientation can be chosen so that its signed curvature is everywhere nonnegative.

Definitions, in the terms of the source. Curves are smooth (`C^∞`). A closed curve is a periodic
map `α : ℝ → ℝ²` (period `T > 0`); it is simple if it is injective on `[0, T)`, and regular if
`α' ≠ 0` everywhere. The signed curvature is `κ = det(α', α'')/|α'|³`. A plane curve is convex if
it lies on one side of each of its tangent lines. Reversing the orientation (`t ↦ α(-t)`) changes
the sign of `κ`, so "the orientation can be chosen with `κ ≥ 0`" means `κ ≥ 0` everywhere or
`κ ≤ 0` everywhere.

The book applies the proposition to curves that are only `C¹` with Lipschitz derivative, whose
curvature exists almost everywhere; the source's hypothesis of smoothness is kept here.
-/

@[expose] public section

namespace External

open Set
open scoped ContDiff

namespace Shifrin

/-- The determinant `det(u, v) = u₀v₁ - u₁v₀` of two vectors of the plane. -/
def cross (u v : Fin 2 → ℝ) : ℝ := u 0 * v 1 - u 1 * v 0

/-- A simple closed regular smooth plane curve with period `T`. -/
def IsSimpleClosedRegularCurve (α : ℝ → Fin 2 → ℝ) (T : ℝ) : Prop :=
  ContDiff ℝ ∞ α ∧ 0 < T ∧ (∀ t, α (t + T) = α t) ∧ InjOn α (Ico 0 T) ∧ ∀ t, deriv α t ≠ 0

/-- The signed curvature `κ(t) = det(α'(t), α''(t))/|α'(t)|³` of a plane curve. -/
noncomputable def signedCurvature (α : ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  cross (deriv α t) (deriv (deriv α) t) / √(deriv α t 0 ^ 2 + deriv α t 1 ^ 2) ^ 3

/-- A plane curve is convex if it lies on one side of each of its tangent lines: for each `t`,
the points `α(s)` all lie in one closed half-plane bounded by the tangent line at `α(t)`. -/
def IsConvexCurve (α : ℝ → Fin 2 → ℝ) : Prop :=
  ∀ t, (∀ s, 0 ≤ cross (deriv α t) (α s - α t)) ∨ (∀ s, cross (deriv α t) (α s - α t) ≤ 0)

end Shifrin

open Shifrin in
/-- **Shifrin, Proposition 3.8.** A simple closed regular plane curve is convex if and only if its
orientation can be chosen so that its signed curvature is everywhere nonnegative, that is, iff its
signed curvature is everywhere `≥ 0` or everywhere `≤ 0`. -/
theorem shifrin_proposition_3_8 {α : ℝ → Fin 2 → ℝ} {T : ℝ}
    (hα : IsSimpleClosedRegularCurve α T) :
    IsConvexCurve α ↔ (∀ t, 0 ≤ signedCurvature α t) ∨ ∀ t, signedCurvature α t ≤ 0 := by
  sorry

end External
