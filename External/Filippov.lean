module

public import OptimalControl.ODE.ControlSystem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Compactness.Compact

/-!
# Filippov's theorem (compactness of attainable sets, existence of optimal controls)

Cited as Theorem 6.1.1 of Hales–Vajjha, *Packings of Smoothed Polygons* (§6.1, TeX 4538–4546),
without a reference (§6.1 cites nothing). The book's control-theory reference, cited for the
maximum principle (TeX 737, 4674), is the bibliography entry `zelikin2004control`, which is
A. A. Agrachev and Yu. L. Sachkov, *Control Theory from the Geometric Viewpoint*, Encyclopaedia of
Mathematical Sciences 87, Springer, 2004 (the entry also lists M. I. Zelikin, and Sachkov twice);
Hales's earlier paper (arXiv:1703.01352, §"Filippov's lemma") cites the same
result as Theorem 10.1 of that book. The book states:

*On a smooth manifold `M`, let `q' = f(q, u)` be an optimal control system with an associated cost
objective `∫₀ᵗ φ(q, u) dt → min`. Here `u ∈ U ⊂ ℝᵐ`, a compact set (the control set). Assume that
the velocity set `f(q, U) = {f(q, u) | u ∈ U}` is convex for each `q ∈ M` and that the support of
`f` is a compact subset of `M × U`. Then the attainable sets are compact and an optimal control
exists.*

The authors' own comment in the TeX (after the theorem) reads: "This is not the Filippov lemma I was
expecting. The Filippov lemma I expected was one asserting the existence of lifted trajectories in
the cotangent bundle satisfying PMP. Also, the conclusion below 'optimal control exists' does not
match the theorem statement", answered by "Reworded conclusion. See sentence before theorem
statement" (the sentence: the compactness of attainable sets implies the existence of an optimal
control, which is a measurable function).

## Reading

* **Setting.** The state space is `ℝⁿ` (`Fin n → ℝ`) instead of a smooth manifold `M`. For `f`
  smooth in `q` and of compact support, the manifold statement follows from this one: embed `M` in
  some `ℝᴺ` (Whitney) and extend `f` to a compactly supported field on `ℝᴺ`, tangent to `M` on `M`;
  the velocity sets are linear images of the original ones, hence convex, and trajectories starting
  on `M` stay on `M`. Measurable controls on manifolds would need machinery Mathlib lacks.
* **Control system** (Agrachev–Sachkov's standing assumptions): `f : ℝⁿ × ℝᵐ → ℝⁿ` continuous,
  smooth in `q` for each control value, with `∂f/∂q` continuous jointly in `(q, u)`. Admissible
  controls are measurable `u : [0, T] → U` (bounded, since `U` is compact); the trajectory is a
  solution in Carathéodory's sense (`q(t) = q₀ + ∫₀ᵗ f(q(s), u(s)) ds`, as in the project's
  `IsIntegralCurve`). The smoothness assumptions give existence and uniqueness of trajectories for
  a given control; the proof of the theorem does not use them.
* **Compact support.** "The support of `f` is a compact subset of `M × U`" is, `U` being compact,
  the source's "there is a compact `K` with `f(q, u) = 0` for `q ∉ K`, `u ∈ U`".
* **Attainable sets.** `A_{q₀}(T)`, the endpoints at time `T` of the admissible trajectories from
  `q₀`, and `A_{q₀}^{≤T} = ⋃_{τ ∈ [0, T]} A_{q₀}(τ)` (Agrachev–Sachkov's `A_{q₀}(t)` and
  `A_{q₀}^t`); the theorem asserts that both are compact (Agrachev–Sachkov, Theorem 10.1).
* **Optimal control.** With only `f(q, U)` convex, "an optimal control exists" is false for costs
  that depend on the control: on `ℝ`, `q' = u ψ(q)` with `U = [-1, 1]` and a bump `ψ = 1` on
  `[-1, 1]`, minimizing `∫₀¹ (q² + 1 - u²) dt` from `q(0) = 0` to `q(1) = 0` has infimum `0`
  (chattering `u = ±1`) and no minimizer (cost `0` forces `q = 0`, hence `u = 0` a.e., of cost `1`).
  We state the existence of an optimal control in the source's form, for the problem
  `q(0) = q₀`, `q(t_f) = q₁`, `∫₀^{t_f} φ(q, u) dt → min` with `φ` continuous, under the convexity
  of the extended velocity sets `{(f(q, u), φ(q, u)) | u ∈ U}`; when `φ` does not depend on `u` (as
  for the Reinhardt problem, whose cost `-(3/2)⟨J, X⟩` is a function of the state), this is the
  book's convexity hypothesis. Both the fixed terminal time `t_f = T` and the free terminal time
  `t_f ∈ [0, T]` are covered (the book applies the theorem with free terminal time `t_f ≤ π/3`); the
  latter follows from the compactness of the extended attainable set `A^{≤T}`.

## Proof

The general theory is in `OptimalControl.ODE.ControlSystem` of the OptimalControl package (for a
control system on a finite-dimensional space): Filippov's compactness theorem
(`ControlSystem.isCompact_reachableSet`, `ControlSystem.isCompact_reachableSetLE`) and the existence
of optimal controls through the system extended by the cost coordinate
(`ControlSystem.exists_optimal_fixedTime`, `ControlSystem.exists_optimal_freeTime`). The compact
support of `f` bounds the velocities. The proof is the standard one: a sequence of
trajectories with endpoints converging has a limit trajectory, which is Lipschitz, has its velocity
in the convex set `f(q, U)` almost everywhere, and is driven by a measurable control obtained by a
measurable selection (Filippov's lemma, `MeasureTheory.exists_measurable_forall_mem_ae_eq_zero` in
`OptimalControl.MeasureTheory.MeasurableSelection`). The limit is extracted by Tychonoff's theorem
(pointwise convergence along a filter finer than `atTop`) rather than Arzelà–Ascoli; since the
trajectories are equi-Lipschitz, pointwise convergence is all the argument needs.

The application in §6.1 (an optimal control exists for the Reinhardt problem, TeX 4553–4600) uses
the compactification of the state space (Theorem 5.0.2 of Chapter 5, `th:compactification`), which
is outside the scope of this formalization; it is not stated.
-/

@[expose] public section

namespace External

namespace Filippov

open MeasureTheory

open scoped ContDiff

variable {n m : ℕ}

/-- An admissible pair on `[0, T]` from `q₀` for the control system `q' = f(q, u)`, `u ∈ U`: a
measurable control `u` with values in `U` on `[0, T]` and a continuous trajectory `q` with
`t ↦ f(q(t), u(t))` integrable and `q(t) = q₀ + ∫₀ᵗ f(q(s), u(s)) ds` on `[0, T]`. -/
def IsAdmissiblePair (f : (Fin n → ℝ) → (Fin m → ℝ) → Fin n → ℝ) (U : Set (Fin m → ℝ))
    (q₀ : Fin n → ℝ) (T : ℝ) (u : ℝ → Fin m → ℝ) (q : ℝ → Fin n → ℝ) : Prop :=
  Measurable u ∧ (∀ t ∈ Set.Icc 0 T, u t ∈ U) ∧ ContinuousOn q (Set.Icc 0 T) ∧
    IntervalIntegrable (fun s ↦ f (q s) (u s)) volume 0 T ∧
    ∀ t ∈ Set.Icc 0 T, q t = q₀ + ∫ s in (0 : ℝ)..t, f (q s) (u s)

/-- The attainable set `A_{q₀}(T)`: the endpoints `q(T)` of the admissible trajectories on
`[0, T]` from `q₀`. -/
def attainableSet (f : (Fin n → ℝ) → (Fin m → ℝ) → Fin n → ℝ) (U : Set (Fin m → ℝ))
    (q₀ : Fin n → ℝ) (T : ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ u q, IsAdmissiblePair f U q₀ T u q ∧ q T = x}

/-- The attainable set `A_{q₀}^{≤T} = ⋃_{τ ∈ [0, T]} A_{q₀}(τ)` for times at most `T`. -/
def attainableSetLE (f : (Fin n → ℝ) → (Fin m → ℝ) → Fin n → ℝ) (U : Set (Fin m → ℝ))
    (q₀ : Fin n → ℝ) (T : ℝ) : Set (Fin n → ℝ) :=
  ⋃ τ ∈ Set.Icc 0 T, attainableSet f U q₀ τ

/-- The cost `∫₀ᵀ φ(q(t), u(t)) dt` of a pair `(u, q)` on `[0, T]`. -/
noncomputable def cost (φ : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (T : ℝ) (u : ℝ → Fin m → ℝ)
    (q : ℝ → Fin n → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, φ (q t) (u t)

end Filippov

open Filippov

open scoped ContDiff

variable {n m : ℕ}

set_option linter.unusedVariables false in
/-- **Filippov's theorem** (Theorem 6.1.1 of the book; Agrachev–Sachkov, *Control Theory from the
Geometric Viewpoint*, Theorem 10.1, and its consequence for problems with integral cost), on `ℝⁿ`.
Let `q' = f(q, u)` be a control system on `ℝⁿ` with `f` continuous and smooth in `q` (with
`∂f/∂q` continuous in `(q, u)`), with a compact control set `U ⊆ ℝᵐ`; assume that the velocity
sets `f(q, U)` are convex and that `f` has compact support (`f(q, u) = 0` for `q` outside a compact
set and `u ∈ U`). Then

1. the attainable sets `A_{q₀}(T)` and `A_{q₀}^{≤T}` are compact, for all `q₀` and `T ≥ 0`;
2. an optimal control exists: for a continuous cost `φ(q, u)` whose extended velocity sets
   `{(f(q, u), φ(q, u)) | u ∈ U}` are convex,
   * (fixed terminal time) for every `q₁ ∈ A_{q₀}(T)`, some admissible pair from `q₀` to `q₁` at
     time `T` has the least cost `∫₀ᵀ φ(q, u) dt` among all such pairs;
   * (free terminal time) for every `q₁ ∈ A_{q₀}^{≤T}`, some admissible pair from `q₀` to `q₁` at
     a time `τ ∈ [0, T]` has the least cost `∫₀^τ φ(q, u) dt` among all admissible pairs from `q₀`
     to `q₁` at times `τ' ∈ [0, T]`.

The smoothness assumptions on `f` are Agrachev–Sachkov's standing assumptions; the proof does not
use them. See the module docstring for the reading (state space `ℝⁿ`; the extended convexity in
part 2, without which part 2 is false, and which is the book's hypothesis when `φ` does not depend
on `u`).
-/
theorem filippov (f : (Fin n → ℝ) → (Fin m → ℝ) → Fin n → ℝ) (U : Set (Fin m → ℝ))
    (hU : IsCompact U) (hf : Continuous fun p : (Fin n → ℝ) × (Fin m → ℝ) ↦ f p.1 p.2)
    (hfq : ∀ u ∈ U, ContDiff ℝ ∞ fun q ↦ f q u)
    (hfq' : Continuous fun p : (Fin n → ℝ) × (Fin m → ℝ) ↦ fderiv ℝ (fun q ↦ f q p.2) p.1)
    (hsupp : ∃ K : Set (Fin n → ℝ), IsCompact K ∧ ∀ q ∉ K, ∀ u ∈ U, f q u = 0)
    (hconv : ∀ q, Convex ℝ (f q '' U)) :
    (∀ (q₀ : Fin n → ℝ) (T : ℝ), 0 ≤ T →
      IsCompact (attainableSet f U q₀ T) ∧ IsCompact (attainableSetLE f U q₀ T)) ∧
    ∀ φ : (Fin n → ℝ) → (Fin m → ℝ) → ℝ,
      (Continuous fun p : (Fin n → ℝ) × (Fin m → ℝ) ↦ φ p.1 p.2) →
      (∀ q, Convex ℝ ((fun u ↦ (f q u, φ q u)) '' U)) →
      ∀ (q₀ q₁ : Fin n → ℝ) (T : ℝ), 0 ≤ T →
        (q₁ ∈ attainableSet f U q₀ T →
          ∃ u q, IsAdmissiblePair f U q₀ T u q ∧ q T = q₁ ∧
            ∀ u' q', IsAdmissiblePair f U q₀ T u' q' → q' T = q₁ →
              cost φ T u q ≤ cost φ T u' q') ∧
        (q₁ ∈ attainableSetLE f U q₀ T →
          ∃ τ ∈ Set.Icc 0 T, ∃ u q, IsAdmissiblePair f U q₀ τ u q ∧ q τ = q₁ ∧
            ∀ τ' ∈ Set.Icc 0 T, ∀ u' q', IsAdmissiblePair f U q₀ τ' u' q' → q' τ' = q₁ →
              cost φ τ u q ≤ cost φ τ' u' q') := by
  -- the smoothness of `f` in `q` (`hfq`, `hfq'`: existence and uniqueness of trajectories) is
  -- not needed
  -- the velocities are bounded, `f` being continuous with compact support
  obtain ⟨K, hK, hfK⟩ := hsupp
  obtain ⟨C, hC⟩ := (hK.prod hU).exists_bound_of_continuousOn hf.continuousOn
  have hM : ∀ q, ∀ u ∈ U, ‖f q u‖ ≤ max C 0 := by
    intro q u hu
    by_cases hq : q ∈ K
    · exact (hC (q, u) ⟨hq, hu⟩).trans (le_max_left _ _)
    · rw [hfK q hq u hu, norm_zero]
      exact le_max_right _ _
  refine ⟨fun q₀ T hT ↦ ⟨?_, ?_⟩, fun φ hφ hconvφ q₀ q₁ T hT ↦ ⟨fun h₁ ↦ ?_, fun h₁ ↦ ?_⟩⟩
  · exact ControlSystem.isCompact_reachableSet hf hU hconv hT (le_max_right _ _)
      fun u q h s hs ↦ hM _ _ (h.2.1 s hs)
  · exact ControlSystem.isCompact_reachableSetLE hf hU hconv (le_max_right _ _)
      fun τ _ u q h s hs ↦ hM _ _ (h.2.1 s hs)
  · exact ControlSystem.exists_optimal_fixedTime hf hU hφ hconvφ hM hT h₁
  · exact ControlSystem.exists_optimal_freeTime hf hU hφ hconvφ hM h₁

end External
