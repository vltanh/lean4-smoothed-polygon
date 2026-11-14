module

public import Basic.Dynamics.StableManifold
public import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# Stable and unstable manifolds (Appendix A.3)

Appendix A.3 of Hales–Vajjha, *Packings of Smoothed Polygons* (`sec:stable-manifold`,
TeX 13176–13211) recalls from Irwin (*Smooth Dynamical Systems*, World Scientific 2001,
Chapter 6) the local and global stable sets of a fixed point of a diffeomorphism, hyperbolic fixed
points and their stable and unstable summands, and Theorem A.3.1 (Irwin): at a hyperbolic fixed
point of a `C^r` diffeomorphism (`r ≥ 1`), the local stable set of `f|_U`, for some open
neighborhood `U` of `p`, is a `C^r` embedded submanifold tangent at `p` to the stable summand, and
the global stable set is a `C^r` immersed submanifold; "There are corresponding statements for
local and global unstable manifolds".

The definitions are `Function.localStableSet`, `Function.globalStableSet`,
`Function.localUnstableSet`, `ContinuousLinearMap.IsHyperbolic`,
`ContinuousLinearMap.stableSubspace` and `ContinuousLinearMap.unstableSubspace`
(`Basic/Dynamics/StableManifold.lean`).

"Unstable for `f` means stable for `f⁻¹`" (TeX 13207–13208) is
`Function.localStableSet_symm_eq_localUnstableSet`, for an open partial homeomorphism and a set
inside its source and target.

`theoremA_3_1` is the theorem for a diffeomorphism between open subsets of a finite-dimensional real
normed space (the manifolds of Chapter 14 are such open sets: the chart `ℝ⁴ = ℝ × ℝ³` near the
fixed points), with the submanifolds written as graphs over the summands, and with the unstable
statement. The global (immersed) part is not stated: no proof of the book uses it (Theorem 14.3.3
uses the local unstable manifold; §14.4 "extends the local unstable manifold to the global unstable
manifold" by iterating, TeX 11922–11932, which needs no theorem).

Proof: `Function.exists_localStableSet_localUnstableSet_eq_graph`, with `n = r`, `W = e.source`;
`Df(p)` is invertible because `e.symm ∘ e = id` near `p` and both are differentiable (chain rule).
-/

@[expose] public section

namespace SmoothedPolygons

open Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem A.3.1** (Irwin; TeX 13198–13211), local part, for a `C^r` diffeomorphism `e` between
open subsets of a finite-dimensional real normed space with a hyperbolic fixed point `p`
(`1 ≤ r ≤ ∞`): for some open neighborhood `U` of `p`, the local stable set of `e|_U` at `p` is a
`C^r` embedded submanifold tangent at `p` to the stable summand of `De(p)` (the graph of a `C^r`
map `h_s` from the stable summand to the unstable one, with `h_s(0) = 0`, `Dh_s(0) = 0`), and the
local unstable set is a `C^r` embedded submanifold tangent at `p` to the unstable summand. -/
theorem theoremA_3_1 (e : OpenPartialHomeomorph E E) {p : E} (hp : p ∈ e.source)
    (hfix : e p = p) {r : ℕ∞} (hr : 1 ≤ r) (he : ContDiffOn ℝ r e e.source)
    (he' : ContDiffOn ℝ r e.symm e.target) (hyp : (fderiv ℝ e p).IsHyperbolic) :
    ∃ U ∈ 𝓝 p, IsOpen U ∧ U ⊆ e.source ∧
      (∃ Vs ∈ 𝓝 (0 : (fderiv ℝ e p).stableSubspace),
        ∃ hs : (fderiv ℝ e p).stableSubspace → (fderiv ℝ e p).unstableSubspace,
          ContDiffOn ℝ r hs Vs ∧ hs 0 = 0 ∧ fderiv ℝ hs 0 = 0 ∧
          Function.localStableSet e p U = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs) ∧
      (∃ Vu ∈ 𝓝 (0 : (fderiv ℝ e p).unstableSubspace),
        ∃ hu : (fderiv ℝ e p).unstableSubspace → (fderiv ℝ e p).stableSubspace,
          ContDiffOn ℝ r hu Vu ∧ hu 0 = 0 ∧ fderiv ℝ hu 0 = 0 ∧
          Function.localUnstableSet e p U = (fun y ↦ p + ↑y + ↑(hu y)) '' Vu) := by
  sorry

end SmoothedPolygons
