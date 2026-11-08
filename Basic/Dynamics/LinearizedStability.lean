module

public import Basic.Dynamics.Stability
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Linearized stability for maps

A fixed point `x₀` of a map `f : E → E` of a finite-dimensional real normed space, at which `f`
is differentiable with a derivative whose (complex) eigenvalues all have modulus `< 1`, is
asymptotically stable. This is the discrete-time form of Lyapunov's first method (Perron), used
without proof in Hales–Vajjha, *Packings of Smoothed Polygons*, Lemma 13.5.5 (TeX 11443–11453:
"An explicit calculation of the eigenvalues of the Jacobian matrix … gives the result").

The eigenvalues are the complex roots of the characteristic polynomial `LinearMap.charpoly` of the
derivative: a real operator may have non-real eigenvalues, and `spectrum ℝ` would miss them, so
the hypothesis is stated with `Polynomial.aeval μ` for `μ : ℂ`.

Mathlib has Gelfand's formula (`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`) for
complex Banach algebras and the chain rule for iterates (`HasFDerivAt.iterate`), but no stability
theorem for maps.

* `ContinuousLinearMap.exists_norm_pow_lt_one`: if every complex root of the characteristic
  polynomial of `A` has modulus `< 1`, then `‖A ^ N‖ < 1` for some `N ≥ 1`.
* `Function.isAsymptoticallyStable_of_hasFDerivAt`: linearized stability.
-/

@[expose] public section

open Filter Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- If every complex eigenvalue of a linear operator `A` of a finite-dimensional real normed space
(every root in `ℂ` of its characteristic polynomial) has modulus `< 1`, then some power `A ^ N`,
`N ≥ 1`, has operator norm `< 1`.

Proof route: complexify (for instance, choose a basis, so that `A` is a real matrix `M`, and view
`M` as a complex matrix with an operator norm); the spectrum of the complex matrix is the set of
roots of `M.charpoly` (`Matrix.mem_spectrum_iff_isRoot_charpoly`), so its spectral radius is `< 1`;
by Gelfand's formula `‖Mⁿ‖^(1/n)` tends to the spectral radius, so `‖Mⁿ‖ → 0`; since the norms
of a finite-dimensional space are equivalent, `‖Aⁿ‖ → 0`. -/
theorem exists_norm_pow_lt_one (A : E →L[ℝ] E)
    (hA : ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly (A : E →ₗ[ℝ] E)) = 0 → ‖μ‖ < 1) :
    ∃ N : ℕ, 0 < N ∧ ‖A ^ N‖ < 1 := by
  sorry

end ContinuousLinearMap

namespace Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Linearized stability for maps.** Let `x₀` be a fixed point of `f : E → E` (`E` a
finite-dimensional real normed space) at which `f` has the derivative `f'`, and suppose that every
complex eigenvalue of `f'` has modulus `< 1`. Then `x₀` is an asymptotically stable fixed point of
`f`.

Proof route: by `ContinuousLinearMap.exists_norm_pow_lt_one`, `‖f' ^ N‖ < 1` for some `N ≥ 1`.
By the chain rule for iterates at a fixed point (`HasFDerivAt.iterate`), `f^[N]` has the
derivative `f' ^ N` at `x₀`, so there are `θ < 1` and `δ > 0` with
`‖f^[N] x - x₀‖ ≤ θ ‖x - x₀‖` on the ball `B(x₀, δ)`; differentiability of `f` at `x₀` gives
`‖f x - x₀‖ ≤ C ‖x - x₀‖` near `x₀`, which controls the intermediate iterates `f^[j]`, `j < N`.
Hence orbits starting close to `x₀` stay close (Lyapunov stability) and tend to `x₀` geometrically
(attraction). Only differentiability at the single point `x₀` is used. -/
theorem isAsymptoticallyStable_of_hasFDerivAt {f : E → E} {f' : E →L[ℝ] E} {x₀ : E}
    (hfix : IsFixedPt f x₀) (hf : HasFDerivAt f f' x₀)
    (hspec : ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly (f' : E →ₗ[ℝ] E)) = 0 → ‖μ‖ < 1) :
    IsAsymptoticallyStable f x₀ := by
  sorry

end Function
