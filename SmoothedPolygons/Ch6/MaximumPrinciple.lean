module

public import SmoothedPolygons.Ch6.LiftedSystem
public import SmoothedPolygons.Ch6.HalfPlane
public import External.Pontryagin

/-!
# The maximum principle for the Reinhardt problem (§6.2, §6.6)

The book applies the Pontryagin maximum principle, cited from `zelikin2004control`
(Agrachev–Sachkov), to the Reinhardt control problem (§6.2, TeX 4662–4830), computes the costate
equations in Lie-algebra form (§§6.4–6.5, 6.8), derives the transversality conditions (6.6.1)
(§6.6, TeX 5157–5215), and collects the result as Problem 6.7.1; Proposition 8.1.3 then says (TeX
6791) "We have seen that the global minimizer must be extremal". That statement is
`exists_isPontryaginExtremal_of_isReinhardtMinimizer`: every global minimizer of Problem 3.6.2
(`IsReinhardtMinimizer`) lifts to a Pontryagin extremal (`IsPontryaginExtremal`).

## Route

1. The minimizer lifts to a minimizer of the lifted problem on `ℝ³ × 𝔥*`
   (`IsReinhardtMinimizer.exists_lift`, `SmoothedPolygons/Ch6/LiftedSystem.lean`).
2. The maximum principle (`External.pontryagin_maximum_principle`: free terminal time, integral
   cost, the boundary map `liftedBoundary` a submersion) gives `ν ≤ 0` and a costate
   `p(t) ∈ (ℝ³ × ℝ²)*`.
3. Translation (`isPontryaginExtremal_of_costate`): the `ℝ³`-part of `p` is the left-trivialized
   costate `Λ₁` (Proposition 3.6.1: `⟨Λ₁, Y⟩ = p(Dπ⁻¹(gY), 0)`, i.e. `p(iwasawaField q Y, 0)`), the
   `ℝ²`-part is the half-plane costate `ν = T*Φ(-Λ_R)` (`cotangentNu`, Lemma 6.8.1), which
   determines `Λ_R ∈ X^⊥`; `(p ↦ (Λ₁, Λ_R))` is a linear isomorphism, so `(ν, p) ≠ 0` is
   `(λ_cost, Λ₁, Λ_R) ≠ 0`; the adjoint equation becomes `Λ₁' = [Λ₁, X]` (Proposition 6.4.1,
   Proposition 6.5.1) and the `Λ_R` equation (Theorem 6.8.3, Corollary 6.5.4); the Hamiltonian
   `⟨p, f⟩ + ν φ` is `hamiltonian ν Λ₁ Λ_R X u` (Theorem 6.8.2); transversality for the
   `z`-coupling gives `Λ_R(T) = R⁻¹Λ_R(0)R`, and `Λ₁(T) = R⁻¹Λ₁(0)R` follows from `g(T) = R`
   (Corollary 6.5.3, as Remark 6.6.1 says).

## Departures from the book's route

The book applies the PMP on `SL₂(ℝ) × 𝔰𝔩₂(ℝ)`, where it yields the spurious multiplier
`(0, 0, cX)` (E21; inventory §3.4); the state space here is `SL₂(ℝ) × 𝔥*` in the global chart
`ℝ³ × 𝔥*` (Iwasawa coordinates of the universal cover), on which the nontriviality condition is
the reduced one of `IsPontryaginExtremal`. The book's "smooth manifold" and "closed control set"
are read through the chart and the compact `U_T`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Pontryagin ControlSystem

/-- **Translation of the costate.** Let `(u, g, X)` be admissible for the Reinhardt problem, `q`
its lift to `ℝ³ × 𝔥*` (`π(q(t).1) = g(t)`, `Φ(q(t).2) = X(t)`, `q(0).1 = 0`), and `(ν, p)` a
multiplier and costate satisfying the conclusions of the maximum principle for the lifted
problem (`External.pontryagin_maximum_principle` with the boundary map
`liftedBoundary (q T).1`). Then the left-trivialized costate `Λ₁` and the reduced costate `Λ_R`
read off from `p` make `(u, g, X, Λ₁, Λ_R, ν)` a Pontryagin extremal.

Proof: see the module docstring (Propositions 3.6.1, 6.4.1, 6.5.1, Corollaries 6.5.3, 6.5.4,
Lemma 6.8.1, Theorems 6.8.2, 6.8.3); the a.e. derivatives are turned into integral equations by
the fundamental theorem of calculus for Lipschitz curves. -/
theorem isPontryaginExtremal_of_costate {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) {q : ℝ → LiftedState} (hq0 : (q 0).1 = 0)
    (hq : ∀ t ∈ Icc 0 T, iwasawa (q t).1 = g t ∧ Φ (q t).2.1 (q t).2.2 = X t)
    (hadm : IsAdmissibleIn liftedField liftedDomain controlSimplex (q 0) T u q) {ν : ℝ}
    {p : ℝ → StrongDual ℝ LiftedState} (hν : ν ≤ 0) (hlip : ∃ K, LipschitzOnWith K p (Icc 0 T))
    (hN : ∀ t ∈ Icc 0 T, (ν, p t) ≠ 0) (hA : IsAdjoint liftedField liftedCost ν u q T p)
    (hM : IsMaximal liftedField liftedCost ν controlSimplex u q T p)
    (hZ : ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
      controlHamiltonian liftedField liftedCost ν (q t) (p t) (u t) = 0)
    (hT : ∀ v w : LiftedState, fderiv ℝ (liftedBoundary (q T).1) (q 0, q T) (v, w) = 0 →
      -p 0 v + p T w = 0) :
    ∃ Λ₁ ΛR : ℝ → Mat2, IsPontryaginExtremal T u g X Λ₁ ΛR ν := by
  sorry

/-- **The global minimizer is a Pontryagin extremal** (`sec:PMP`, label of this formalization:
§6.2 and §6.6 of the book, TeX 4662–4830 and 5157–5215, summarized in Problem 6.7.1 and used in
the proof of Proposition 8.1.3, TeX 6791: "We have seen that the global minimizer must be
extremal"). Every global minimizer `(u, g, X)` of the Reinhardt control problem (Problem 3.6.2)
lifts to a Pontryagin extremal: there are costates `Λ₁, Λ_R` and a multiplier `λ_cost ≤ 0` with
the state–costate equations of Problem 6.7.1, the maximum condition and `H = 0` almost
everywhere, the nontriviality `(λ_cost, Λ₁, Λ_R) ≠ 0` at every time, and the transversality
conditions (6.6.1).

The book applies the maximum principle on `SL₂(ℝ) × 𝔰𝔩₂(ℝ)`; the proof applies it on
`SL₂(ℝ) × 𝔥*` in the chart `ℝ³ × 𝔥*` (see the module docstring and inventory §3.4, E21).

Proof: `IsReinhardtMinimizer.exists_lift`, `External.pontryagin_maximum_principle` (with
`isC1On_liftedField`, `isC1On_liftedCost`, `isCompact_controlSimplex`,
`contDiffAt_liftedBoundary`, `surjective_fderiv_liftedBoundary`), and
`isPontryaginExtremal_of_costate`. -/
theorem exists_isPontryaginExtremal_of_isReinhardtMinimizer {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsReinhardtMinimizer T u g X) :
    ∃ (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ), IsPontryaginExtremal T u g X Λ₁ ΛR lam := by
  obtain ⟨q, hq0, hq, hmin⟩ := h.exists_lift
  have hadm := hmin.2.1
  have hy : 0 < (q 0).2.2 := (hadm.2 0 ⟨le_rfl, hmin.1.le⟩).2.1
  obtain ⟨ν, p, hν, hlip, hN, hA, hM, hZ, hT⟩ :=
    External.pontryagin_maximum_principle isOpen_liftedDomain isCompact_controlSimplex
      isC1On_liftedField isC1On_liftedCost hmin (contDiffAt_liftedBoundary (q T).1 hy)
      (surjective_fderiv_liftedBoundary (q T).1 hy) hmin.2.2.1
      (Eventually.of_forall fun _ hz ↦ hz)
  obtain ⟨Λ₁, ΛR, hext⟩ :=
    isPontryaginExtremal_of_costate h.1 hq0 hq hadm hν hlip hN hA hM hZ hT
  exact ⟨Λ₁, ΛR, ν, hext⟩

end SmoothedPolygons
