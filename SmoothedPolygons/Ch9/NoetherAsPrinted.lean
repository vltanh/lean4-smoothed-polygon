module

public import External.NoetherSussmann

/-!
# §9.1: the book's definitions of symmetries, and the Noether–Sussmann theorem as printed

Definitions 9.1.1–9.1.3 and the Noether–Sussmann theorem (Theorem 9.1.4) of Hales–Vajjha,
*Packings of Smoothed Polygons*, §9.1 (TeX 7812–7880), quoted from Sussmann (bibliography entry
`sussman`; `External/NoetherSussmann.lean`).

* **Definition 9.1.1** (`def:symmetry`, TeX 7822–7830), as printed: a symmetry of
  `𝒬 = (M, U, f, φ)` is a diffeomorphism `ψ : V₁ → V₂` between open subsets of `M` such that for
  every `u ∈ U` there are `u₁, u₂ ∈ U` with `dψ(q)(f_u(q)) = f_{u₁}(ψ(q))` and
  `dψ(q)(f_{u₂}(q)) = f_u(ψ(q))` for all `q ∈ V₁` (`IsSymmetryAsPrinted`). Sussmann's
  condition (ii), `φ_{u₁} ∘ ψ = φ_u` and `φ_u ∘ ψ = φ_{u₂}`, is missing.
* **Definition 9.1.2** (`def:infinitesimal-symmetry`, TeX 7836–7843), as printed: an infinitesimal
  group of symmetries is a smooth action `τ : 𝔤 → Γ^∞(TM)` every `exp(tτ(X))` of which is a
  symmetry in the sense of Definition 9.1.1 (`IsInfinitesimalGroupOfSymmetriesAsPrinted`).
* **Definition 9.1.3** (`def:momentum-map`, TeX 7850–7860): `𝐉^τ(q, p)(X) = ⟨p, τ(X)(q)⟩`. This is
  Sussmann's momentum map, `Pontryagin.momentumMap` of the OptimalControl package; no new
  definition.
* **Theorem 9.1.4** (Noether–Sussmann, TeX 7871–7880), as printed, is **false**
  (`noetherSussmann_false_as_printed`). Sussmann's theorem, with (ii), is
  `External.noether_sussmann`; Theorem 9.1.6 is proved from it, not from the printed statement.

## Readings

The objects are read in the coordinates of the OptimalControl package (its readings S1–S8, module
docstring of `OptimalControl.Pontryagin.Noether`): `M` is an open subset `Ω` of a
finite-dimensional real normed space `E`, "diffeomorphism" and "smooth" are read as `C¹` (S2), the
flow `exp(tY)` is `Pontryagin.flowMap Y Ω t` on its domain `Pontryagin.flowDomain Y Ω t` (S3), and
the "smooth action" `τ` is a linear map with `τ⁅X, X'⁆ = [τ X, τ X']` (S8). The two definitions
below differ from the package's `Pontryagin.IsSymmetry` and
`Pontryagin.IsInfinitesimalGroupOfSymmetries` only in the missing condition (ii). "Let `G` be a
Lie group with Lie algebra `𝔤`" (TeX 7823) plays no role in the definitions and is dropped: `𝔤` is
any real Lie algebra. The counterexample's flows are translations of `ℝ`, smooth in every sense, so
the falsity does not depend on the reading of "smooth".
-/

@[expose] public section

open MeasureTheory Set

namespace SmoothedPolygons

open Pontryagin ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Definition 9.1.1 as printed** (`def:symmetry`, TeX 7822–7830): a symmetry of the optimal
control system `(Ω, U, f, φ)` is a diffeomorphism `ψ : V₁ → V₂` between open subsets of `Ω` (read
as `C¹`: `ψ` maps `V₁` bijectively onto `V₂`, is `C¹` on `V₁`, and its inverse is `C¹` on `V₂`)
such that for every `u ∈ U` there exist `u₁, u₂ ∈ U` for which `dψ(q)(f_u(q)) = f_{u₁}(ψ(q))` and
`dψ(q)(f_{u₂}(q)) = f_u(ψ(q))` for all `q ∈ V₁`. The cost `φ` does not enter: Sussmann's
condition (ii) (`Pontryagin.PermutesFamily`) is not in the book. -/
structure IsSymmetryAsPrinted (f : E → V → E) (Ω : Set E) (U : Set V) (ψ : E → E)
    (V₁ V₂ : Set E) : Prop where
  isOpen_left : IsOpen V₁
  isOpen_right : IsOpen V₂
  left_subset : V₁ ⊆ Ω
  right_subset : V₂ ⊆ Ω
  bijOn : BijOn ψ V₁ V₂
  contDiffOn : ContDiffOn ℝ 1 ψ V₁
  contDiffOn_invFunOn : ContDiffOn ℝ 1 (Function.invFunOn ψ V₁) V₂
  permutes : ∀ u ∈ U, ∃ u₁ ∈ U, ∃ u₂ ∈ U, ∀ q ∈ V₁,
    fderiv ℝ ψ q (f q u) = f (ψ q) u₁ ∧ fderiv ℝ ψ q (f q u₂) = f (ψ q) u

/-- **Definition 9.1.2 as printed** (`def:infinitesimal-symmetry`, TeX 7836–7843): an
infinitesimal group of symmetries of `(Ω, U, f, φ)` is a smooth action `τ : 𝔤 → Γ^∞(TM)` of the
Lie algebra `𝔤` (read as in the package: linear, `τ⁅X, X'⁆ = [τ X, τ X']` on `Ω`, each `τ(X)` of
class `C¹` on `Ω`) such that every diffeomorphism `exp(tτ(X))` is a symmetry in the sense of
Definition 9.1.1 as printed (`IsSymmetryAsPrinted`). -/
structure IsInfinitesimalGroupOfSymmetriesAsPrinted {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (f : E → V → E) (Ω : Set E) (U : Set V) (τ : L →ₗ[ℝ] E → E) : Prop where
  map_lie : ∀ X X' : L, ∀ x ∈ Ω, τ ⁅X, X'⁆ x = VectorField.lieBracket ℝ (τ X) (τ X') x
  contDiffOn : ∀ X : L, ContDiffOn ℝ 1 (τ X) Ω
  isSymmetry : ∀ (X : L) (t : ℝ), IsSymmetryAsPrinted f Ω U (flowMap (τ X) Ω t)
    (flowDomain (τ X) Ω t) (flowDomain (τ X) Ω (-t))

/-- **The Noether–Sussmann theorem as printed is false** (Theorem 9.1.4, TeX 7871–7880, with
Definitions 9.1.1–9.1.3 as printed). The printed statement: for an optimal control system
`𝒬 = (M, U, f, φ)` with the regularity of §6.2 (here: `Ω` open, `U` compact, `f` and `φ` of class
`C¹` in the sense of `ControlSystem.IsC1On`) and a cost `φ` independent of the control
(TeX 7816–7818), an infinitesimal group of symmetries `τ` (Definition 9.1.2 as printed) and a
lifted controlled trajectory `p` satisfying the Pontryagin maximum principle (here all the
conclusions of `External.pontryagin_maximum_principle` for a problem with fixed endpoints, for which
transversality is empty: `ν ≤ 0`, `p` Lipschitz, `(ν, p(t)) ≠ 0`, the adjoint equation, the maximum
condition, `H = 0` almost everywhere), the momentum map `𝐉^τ` is constant along `p`. It fails
already on `M = ℝ`.

Counterexample: `U = [-1, 1]`, `f(x, u) = u`, `φ(x, u) = x`, the Lie algebra `ℝ` acting by
`τ(a) = a ∂ₓ` (flows `x ↦ x + at`, which satisfy Definition 9.1.1 as printed with `u₁ = u₂ = u`,
since `f` does not depend on `x`; they do not preserve the cost, against Sussmann's (ii)). On
`[0, 2]`, `q(t) = |1 - t|` with `ũ(t) = -1` for `t < 1` and `1` for `t ≥ 1`, `ν = -1` and
`p(t) = (t - 1) dx`: `ṗ = -ν ∂ₓφ = 1`, the maximum of `H = p u + ν x` over `u ∈ [-1, 1]` is
attained at `u = sign(t - 1)`, and `H = |t - 1| - |1 - t| = 0`. The momentum
`𝐉^τ(q(t), p(t))(1) = p(t)(1) = t - 1` is not constant. (The pair is optimal for the cost
`∫₀² x dt` with `x(0) = x(2) = 1`: `x(t) ≥ |1 - t|` for every admissible `x`. In Sussmann's
convention, `c = 1`, `ζ(t) = 1 - t`.)

Proof plan (120–200 lines): specialize to `L = ℝ` with `LieRing.ofAssociativeRing` and
`LieAlgebra.ofAssociativeAlgebra` (`⁅a, b⁆ = 0`), `Ω = univ`, `τ = LinearMap.smulRight
LinearMap.id (fun _ ↦ 1)`.
1. Regularity: `U = Icc (-1) 1` compact; `f`, `φ` affine, `IsC1On` by `fun_prop`-level facts.
2. `IsInfinitesimalGroupOfSymmetriesAsPrinted`: `map_lie` (both sides `0`: `⁅a, b⁆ = 0`, and the
   bracket of constant fields is `0`); `τ a` constant, hence `C¹`; its flow on `univ` is
   `x ↦ x + a t` (`Pontryagin.flowMap_eq_of_isIntegralCurveIn` with the curve `r ↦ x + a r`,
   `flowDomain = univ`); the translation is a `C^∞` bijection with inverse the translation by
   `-a t`, and `fderiv` of a translation is the identity, so `u₁ = u₂ = u` work.
3. The trajectory: `ũ` measurable (piecewise constant), `q(t) = 1 + ∫₀ᵗ ũ` on `[0, 2]`
   (`intervalIntegral.integral_comp`-level computation on `[0, 1]` and `[1, 2]`), values in `univ`.
4. The costate: `p(t) = (t - 1) • ContinuousLinearMap.id ℝ ℝ` is Lipschitz; the adjoint integrand
   is `p(r) ∘ 0 + (-1) • id = -id` (`fderiv` of `f(·, u)` is `0`, of `φ(·, u)` is `id`), so
   `p(t) = p(2) + ∫ₜ² (-id) = (1 - (2 - t)) • id` holds; `(ν, p(t)) ≠ 0` since `ν = -1`.
5. Maximum condition and `H = 0` at every `t ≠ 1`: `H(u) = (t - 1) u - |1 - t|`, maximal at
   `u = ũ(t)` with value `0`.
6. At `t = 2`: `𝐉^τ(q(2), p(2))(1) = 1 ≠ -1 = 𝐉^τ(q(0), p(0))(1)`. -/
theorem noetherSussmann_false_as_printed :
    ¬ ∀ (L : Type) [LieRing L] [LieAlgebra ℝ L] (Ω U : Set ℝ) (f φ : ℝ → ℝ → ℝ)
      (τ : L →ₗ[ℝ] ℝ → ℝ), IsOpen Ω → IsCompact U → IsC1On f Ω U → IsC1On φ Ω U →
      (∀ x u v, φ x u = φ x v) → IsInfinitesimalGroupOfSymmetriesAsPrinted f Ω U τ →
      ∀ (T ν : ℝ) (ũ q : ℝ → ℝ) (p : ℝ → StrongDual ℝ ℝ),
        IsAdmissibleIn f Ω U (q 0) T ũ q → ν ≤ 0 → (∃ K, LipschitzOnWith K p (Icc 0 T)) →
        (∀ t ∈ Icc 0 T, (ν, p t) ≠ 0) → IsAdjoint f φ ν ũ q T p → IsMaximal f φ ν U ũ q T p →
        (∀ᵐ t ∂(volume.restrict (Icc 0 T)), controlHamiltonian f φ ν (q t) (p t) (ũ t) = 0) →
        ∀ t ∈ Icc 0 T, momentumMap τ (q t) (p t) = momentumMap τ (q 0) (p 0) := by
  sorry

end SmoothedPolygons
