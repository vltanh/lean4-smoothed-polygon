module

public import OptimalControl.Pontryagin.Noether

/-!
# Sussmann's Noether theorem for optimal control

Cited in Hales–Vajjha, *Packings of Smoothed Polygons*, §9.1 (TeX 7812–7880), as the
"Noether–Sussmann theorem", from the bibliography entry `sussman`: H. J. Sussmann, *Symmetries and
integrals of motion in optimal control*, in *Geometry in Nonlinear Control and Differential
Inclusions*, Banach Center Publications 32, Institute of Mathematics, Polish Academy of Sciences,
Warszawa, 1995, pp. 379–393 (the book's entry gives 1996), Theorem 4.1 (p. 389). The book applies it
in the proof of Theorem 9.1.6 (`thm:angular-momentum`), to the rotations of the circular control
problem.

## Sussmann's statement and the book's quotation

Sussmann (p. 389): an optimal control system `P = (M, U, f, f⁰)`; a **symmetry** of `P` is a
diffeomorphism `σ : V₁ → V₂` between open subsets of `M` such that for every `u ∈ U` there exist
`u₁, u₂ ∈ U` for which

* (i) `dσ(x)(f_u(x)) = f_{u₁}(σ(x))` and `dσ(x)(f_{u₂}(x)) = f_u(σ(x))` for all `x ∈ V₁`, and
* (ii) `f⁰_{u₁} ∘ σ = f⁰_u` and `f⁰_u ∘ σ = f⁰_{u₂}`;

an infinitesimal group of symmetries is a smooth action `τ` of a Lie algebra `L` on `M` every
`e^{tτ(X)}` of which is a symmetry; the momentum map is `μ^τ(x, z)(X) = ⟨z, τ(X)(x)⟩`. Theorem 4.1:
for `P` of class `C¹`, `μ^τ` is constant along every biextremal.

**The book misquotes the definition of a symmetry.** Its Definition 9.1.1 (`def:symmetry`,
TeX 7822–7830) keeps (i) and drops (ii), the invariance of the cost; the running text before it
(TeX 7816–7818) assumes only that the cost does not depend on the control. With that definition the
Noether–Sussmann theorem as printed (TeX 7871–7880) is false: on `M = ℝ` with `U = [-1, 1]`,
`f_u(x) = u` and the cost `φ(x) = x`, the translations `x ↦ x + s` (the flow of `τ = ∂ₓ`) satisfy
(i) with `u₁ = u₂ = u`; the optimal trajectory `x(t) = |1 - t|` of `∫₀² x dt → min`,
`x(0) = x(2) = 1`, lifts to an extremal with costate `ζ(t) = 1 - t` (`c = 1`, `H ≡ 0`), along
which `μ^τ = ζ` is not constant (`SmoothedPolygons.noetherSussmann_false_as_printed`,
`SmoothedPolygons/Ch9/NoetherAsPrinted.lean`). The book's application is not affected: the proof of
Theorem 9.1.6 checks that the rotations preserve the whole Hamiltonian, cost included ("by the proof
of Theorem 9.0.3", TeX 7921), and the cost `-(3/2)⟨J, X⟩` of the circular problem is invariant
under them. The results here are Sussmann's, with condition (ii).

## Forms

The OptimalControl package (`OptimalControl.Pontryagin.Noether`) proves Theorem 4.1 in coordinates
(`M` an open subset `Ω` of a finite-dimensional real normed space; the readings S1–S8 of its module
docstring, among them `C¹` in place of `C^∞`, S2). Three forms are recorded here:

* `External.sussmann_theorem4_1`: Theorem 4.1 as Sussmann states it, for biextremals in his
  minimization convention;
* `External.noether_sussmann`: the form the book quotes (TeX 7871–7880, with (ii) restored): along
  every lifted trajectory satisfying the adjoint equation and the maximum condition of the maximum
  principle in the convention of `External.pontryagin_maximum_principle` (maximization, any
  multiplier `ν`), the momentum map is constant;
* `External.noether_sussmann_one_parameter`: the same for one infinitesimal symmetry `Y`, the
  momentum `⟨p, Y(q)⟩` being constant. This is Theorem 4.1 for the one-dimensional Lie algebra
  spanned by `Y` (Sussmann's "that is, all the scalar Hamiltonian functions
  `(x, z) ↦ ⟨z, τ(X)(x)⟩`, `X ∈ L`, are constant along `Ξ`"); for the rotations of §9.1, whose Lie
  algebra `𝔰𝔬₂(ℝ) = ℝJ` is one-dimensional, `μ^τ(q, p)(aJ) = a ⟨p, Y(q)⟩` with `Y = τ(J)`, and the
  two forms say the same.

## Proof

In the OptimalControl package (branch `noether`): `Pontryagin.sussmann_theorem4_1`,
`Pontryagin.noether_momentumMap` and `Pontryagin.noether`, proved there by Sussmann's argument
(the cotangent lift of the symmetries, the maximum at `s = 0`, the vanishing Poisson bracket, and
absolute continuity of the momentum).
-/

@[expose] public section

open MeasureTheory Set

namespace External

open Pontryagin

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace V] {f : E → V → E} {φ : E → V → ℝ} {Ω : Set E} {U : Set V}

/-- **Sussmann, Theorem 4.1** (p. 389), as stated there: let `(Ω, U, f, φ)` be an optimal control
system of class `C¹`, `L` a Lie algebra and `τ` an infinitesimal group of symmetries (Sussmann's
definition, with the invariance (ii) of the cost), and let `Ξ = (q, ζ)` be a biextremal
(Sussmann's (EAV1)–(EAV3), minimization convention, `c ≥ 0`). Then the momentum map `μ^τ` is
constant along `Ξ`.

Proof: `Pontryagin.sussmann_theorem4_1` of the OptimalControl package, which has the same
statement. -/
theorem sussmann_theorem4_1 {L : Type*} [LieRing L] [LieAlgebra ℝ L] (hΩ : IsOpen Ω)
    (hf : ∀ u ∈ U, ContDiffOn ℝ 1 (f · u) Ω) (hφ : ∀ u ∈ U, ContDiffOn ℝ 1 (φ · u) Ω)
    {τ : L →ₗ[ℝ] E → E} (hτ : IsInfinitesimalGroupOfSymmetries f φ Ω U τ) {T c : ℝ}
    {ũ : ℝ → V} {q : ℝ → E} {ζ : ℝ → StrongDual ℝ E} (hΞ : IsBiextremal f φ Ω U T ũ q c ζ) :
    ∀ t ∈ Icc 0 T, momentumMap τ (q t) (ζ t) = momentumMap τ (q 0) (ζ 0) :=
  Pontryagin.sussmann_theorem4_1 hΩ hf hφ hτ hΞ

/-- **The Noether–Sussmann theorem in the form quoted by the book** (§9.1, TeX 7871–7880), with
Sussmann's cost invariance (ii) in the definition of a symmetry: let `(Ω, U, f, φ)` be an optimal
control system of class `C¹` and `τ` an infinitesimal group of symmetries of it, and let `(q, p)` be
a lifted controlled trajectory satisfying the adjoint equation and the maximum condition of the
maximum principle (`IsAdjoint`, `IsMaximal`, in the convention of
`External.pontryagin_maximum_principle`, for some multiplier `ν`). Then the momentum map
`μ^τ(q(t), p(t))` is constant on `[0, T]`. (The other conclusions of the maximum principle,
`ν ≤ 0`, nontriviality, `H = 0` and transversality, are not needed.)

Proof: `Pontryagin.noether_momentumMap` of the OptimalControl package, which has the same
statement. -/
theorem noether_sussmann {L : Type*} [LieRing L] [LieAlgebra ℝ L] (hΩ : IsOpen Ω)
    (hf : ∀ u ∈ U, ContDiffOn ℝ 1 (f · u) Ω) (hφ : ∀ u ∈ U, ContDiffOn ℝ 1 (φ · u) Ω)
    {τ : L →ₗ[ℝ] E → E} (hτ : IsInfinitesimalGroupOfSymmetries f φ Ω U τ) {T ν : ℝ}
    {ũ : ℝ → V} {q : ℝ → E} {p : ℝ → StrongDual ℝ E} (href : IsAdmissibleIn f Ω U (q 0) T ũ q)
    (hadj : IsAdjoint f φ ν ũ q T p) (hmax : IsMaximal f φ ν U ũ q T p) :
    ∀ t ∈ Icc 0 T, momentumMap τ (q t) (p t) = momentumMap τ (q 0) (p 0) :=
  Pontryagin.noether_momentumMap hΩ hf hφ hτ href hadj hmax

/-- **The Noether–Sussmann theorem for one infinitesimal symmetry**: under the hypotheses of
`noether_sussmann`, with one infinitesimal symmetry `Y` (every `e^{sY}` a symmetry, with the
invariance (ii) of the cost) in place of the group `τ`, the momentum `⟨p(t), Y(q(t))⟩` is constant
on `[0, T]`. This is Theorem 4.1 for the one-dimensional Lie algebra spanned by `Y`.

Proof: `Pontryagin.noether` of the OptimalControl package, which has the same statement. -/
theorem noether_sussmann_one_parameter (hΩ : IsOpen Ω) (hf : ∀ u ∈ U, ContDiffOn ℝ 1 (f · u) Ω)
    (hφ : ∀ u ∈ U, ContDiffOn ℝ 1 (φ · u) Ω) {Y : E → E}
    (hY : IsInfinitesimalSymmetry f φ Ω U Y) {T ν : ℝ} {ũ : ℝ → V} {q : ℝ → E}
    {p : ℝ → StrongDual ℝ E} (href : IsAdmissibleIn f Ω U (q 0) T ũ q)
    (hadj : IsAdjoint f φ ν ũ q T p) (hmax : IsMaximal f φ ν U ũ q T p) :
    ∀ t ∈ Icc 0 T, momentum Y (q t) (p t) = momentum Y (q 0) (p 0) :=
  Pontryagin.noether hΩ hf hφ hY href hadj hmax

end External
