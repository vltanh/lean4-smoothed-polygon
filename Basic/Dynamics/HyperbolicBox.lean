module

public import Basic.Dynamics.LinearizedStability
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# An isolating box at a fixed point with an invariant hyperplane and a transverse expansion

Let `F : ℝ × E → ℝ × E` fix `p₀ = (0, x₀)`, leave the hyperplane `{r = 0}` invariant near `p₀`,
expand in the transverse direction (`∂(F.1)/∂r (p₀) > 1`) and contract along the hyperplane (the
derivative of `x ↦ F(0, x).2` at `x₀` has all its complex eigenvalues of modulus `< 1`). Then a
sequence `pₙ` with `rₙ > 0`, `rₙ → 0`, which follows `F` near `p₀` (`p (n + 1) = F (p n)` whenever
`p n` is close to `p₀`), does not have `p₀` as a cluster point: each visit close to `p₀` with
small `r` is followed by a time at which `r` exceeds a fixed `δ > 0`, because `r` grows
geometrically while the hyperplane coordinate stays near `x₀`.

This is the "hyperbolic box" (isolating block) argument that replaces the `ε` versus
`ε/r_scale` argument of the proof of Theorem 16.4.1 in Hales–Vajjha, *Packings of Smoothed
Polygons* (TeX 13002–13026: "we claim that `q_out` is not a cluster point"); it uses the
derivative at the fixed point only (strict differentiability), not the stable manifold theorem.

## Proof (plan)

Write `F (r, x) = (r m(r, x), G(r, x))` near `p₀`. Strict differentiability at `p₀` and the
invariance `F.1(0, x) = 0` give `F.1(r, x) ≥ λ r` for `0 < r ≤ δ`, `‖x - x₀‖ ≤ η`, with some
`λ > 1`, and `G(r, x) - x₀ = A(x - x₀) + r b + o(|r| + ‖x - x₀‖)` with `A` the hyperplane part of
the derivative and `b = (F'(1, 0)).2`. By `ContinuousLinearMap.exists_norm_pow_lt_one` there is an
adapted norm `‖·‖_*` on `E` (`‖v‖_* = Σ_{j<N} θ^{-j} ‖A^j v‖`) in which `A` is a contraction
`‖A v‖_* ≤ κ ‖v‖_*`, `κ < 1`. On the box `B = {0 < r ≤ δ, ‖x - x₀‖_* ≤ η}` the iterates satisfy
`r_{k+1} ≥ λ r_k` and `‖x_{k+1} - x₀‖_* ≤ κ' ‖x_k - x₀‖_* + C r_k`; starting from
`‖x - x₀‖_* ≤ η/2` and `r ≤ (1 - κ')(λ - κ') η / (2Cλ)`, the second coordinate stays in the box
while `r ≤ δ` (sum the geometric series `Σ (κ'/λ)^j`). Since `r` grows geometrically, some later
term has `r > δ'`, for a fixed `δ'`. A cluster point at `p₀` gives infinitely many visits to the
smaller box, hence infinitely many terms with `r > δ'`, against `rₙ → 0`; the box is chosen
inside the given `W`, where the sequence follows `F`. Size: 300–500 lines.
-/

@[expose] public section

open Filter Topology Set

namespace Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **No cluster point at a fixed point with an invariant hyperplane and transverse expansion.**
Let `F : ℝ × E → ℝ × E` be strictly differentiable at `p₀ = (0, x₀)` with derivative `F'`, fix
`p₀`, leave `{r = 0}` invariant near `p₀`, expand transversally (`(F' (1, 0)).1 > 1`) and contract
along the hyperplane (every complex eigenvalue of `v ↦ (F' (0, v)).2` has modulus `< 1`). Then there
for **every** neighborhood `W` of `p₀`, no sequence `p` with `(p n).1 → 0` which, at every `n` with
`p n ∈ W`, has `(p n).1 > 0` and `p (n + 1) = F (p n)`, has `p₀` as a cluster point. (The box
argument uses only a small box inside `W`, so `W` may be any neighborhood: in applications it is
the neighborhood on which the sequence is known to follow `F`.) -/
theorem not_mapClusterPt_of_transverse_expansion {F : ℝ × E → ℝ × E}
    {F' : (ℝ × E) →L[ℝ] ℝ × E} {x₀ : E} (hF : HasStrictFDerivAt F F' ((0 : ℝ), x₀))
    (hfix : F ((0 : ℝ), x₀) = ((0 : ℝ), x₀))
    (hinv : ∀ᶠ x in 𝓝 x₀, (F ((0 : ℝ), x)).1 = 0) (hexp : 1 < (F' ((1 : ℝ), (0 : E))).1)
    (hcontr : ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly
      ((ContinuousLinearMap.snd ℝ ℝ E ∘L F' ∘L ContinuousLinearMap.inr ℝ ℝ E :
        E →L[ℝ] E) : E →ₗ[ℝ] E)) = 0 → ‖μ‖ < 1) :
    ∀ W ∈ 𝓝 ((0 : ℝ), x₀), ∀ p : ℕ → ℝ × E, Tendsto (fun n ↦ (p n).1) atTop (𝓝 0) →
      (∀ n, p n ∈ W → 0 < (p n).1 ∧ p (n + 1) = F (p n)) →
        ¬ MapClusterPt ((0 : ℝ), x₀) atTop p := by
  sorry

end Function
