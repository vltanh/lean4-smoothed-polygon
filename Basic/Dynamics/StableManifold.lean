module

public import Basic.Dynamics.LinearizedStability
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# Stable and unstable manifolds of a hyperbolic fixed point of a map

The local stable and unstable sets of a fixed point `p` of a map `f`, the stable and unstable
subspaces of a hyperbolic linear map, and the stable manifold theorem for a `Cⁿ` map of a
finite-dimensional real normed space near a hyperbolic fixed point (`1 ≤ n ≤ ∞`), in graph form:
the local stable set is the graph of a `Cⁿ` map from the stable subspace to the unstable one,
tangent to the stable subspace at `p`, and the local unstable set is the graph of a `Cⁿ` map from
the unstable subspace to the stable one (Irwin, *Smooth Dynamical Systems*, Chapter 6; Hirsch,
Pugh and Shub, *Invariant Manifolds*). This is the form used by Hales–Vajjha, *Packings of
Smoothed Polygons*, Appendix A.3 (Theorem A.3.1, TeX 13176–13211) and Chapter 14
(Theorem 14.3.3, Remark 14.3.4).

* `Function.localStableSet f p U`: the points whose forward orbit stays in `U` and tends to `p`
  (the local stable set of `f|_U`);
* `Function.localUnstableSet f p U`: the points having a backward orbit (`f (y (n + 1)) = y n`) in
  `U` that tends to `p` (the local stable set of `f⁻¹|_U` when `f` is invertible; the definition
  does not need an inverse);
* `ContinuousLinearMap.IsHyperbolic A`: no complex eigenvalue of `A` has modulus `1`;
* `ContinuousLinearMap.stableSubspace A`: the vectors `v` with `Aⁿ v → 0`;
  `ContinuousLinearMap.unstableSubspace A`: the vectors with a backward orbit tending to `0`;
* `ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace`: for a hyperbolic `A` the two
  subspaces are complementary (they are the sums of the generalized eigenspaces of the eigenvalues
  of modulus `< 1`, resp. `> 1`);
* `Function.eventually_iterate_mem_localStableSet`, `Function.eventually_mem_localUnstableSet`:
  an orbit tending to `p` eventually lies in the local stable set of every neighborhood, and a
  backward orbit tending to `p` eventually lies in the local unstable set;
* `Function.localStableSet_symm_eq_localUnstableSet`: unstable for `e` is stable for `e⁻¹`;
* `Function.exists_localStableSet_localUnstableSet_eq_graph`: **the stable manifold theorem**.

Mathlib has no stable manifold theorem (checked: no `stableManifold`, `localStableSet` or
hyperbolic fixed point in `Mathlib/Dynamics`).

## Proofs (plan)

The submodule structures and the two `eventually` lemmas are immediate from the definitions.

`isCompl_stableSubspace_unstableSubspace`: factor the characteristic polynomial over `ℝ` as
`χ = χ_s χ_u`, the factors collecting the roots of modulus `< 1` and `> 1` (coprime); then
`E = ker χ_s(A) ⊕ ker χ_u(A)` (kernel decomposition for coprime factors,
`Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime`, `LinearMap.charpoly` and Cayley–Hamilton,
`LinearMap.aeval_self_charpoly`). On `ker χ_s(A)` the spectral radius is `< 1`, so `Aⁿ → 0` there
(Gelfand's formula, as in `ContinuousLinearMap.exists_norm_pow_lt_one`); on `ker χ_u(A)`, `A` is
invertible with inverse of spectral radius `< 1`. A vector with a nonzero `ker χ_u(A)`-component
has `‖Aⁿ v‖ → ∞`, and one with a nonzero `ker χ_s(A)`-component has no backward orbit tending to
`0`. Size: 300–500 lines.

The stable manifold theorem (Perron's method, Irwin's Chapter 6): (1) with a bump function
(`ContDiffBump`), replace `f` near `p` by `p + A(x - p) + φ(x - p)` with `φ` globally
`ε`-Lipschitz and `Cⁿ`, equal to `f` near `p`; (2) in an adapted norm (`‖A|_{E_s}‖ < 1`,
`‖(A|_{E_u})⁻¹‖ < 1`, from `exists_norm_pow_lt_one` and averaging), the points whose forward
orbit is bounded form the graph of a Lipschitz map `h : E_s → E_u` (fixed point of a contraction
on bounded sequences, the Lyapunov–Perron operator); (3) `h` is `C¹` with `Dh(0) = 0` (fiber
contraction theorem), and `Cⁿ` by induction on the order (Irwin's `C^r` section theorem);
(4) near `p` the bounded forward orbits are those tending to `p`, and the modified map agrees
with `f` on a neighborhood `U`; (5) the unstable set is the stable set of the local inverse
(inverse function theorem, `HasStrictFDerivAt.localInverse`), or directly the bounded backward
orbits. Size: 3,000–5,000 lines for `Cⁿ`; a Lipschitz (`C⁰`) graph with `Dh(0) = 0` is
1,200–2,000 lines and suffices for every use in the book other than the words "`C^∞` curve" of
Theorem 14.3.3.
-/

@[expose] public section

open Filter Topology Set

namespace Function

variable {X : Type*} [TopologicalSpace X]

/-- The **local stable set** of `f|_U` at `p` (TeX 13184–13187): the points `x` whose forward
orbit `fⁿ(x)` stays in `U` and tends to `p`. (The book writes "the set of all `q ∈ U` such that
`lim fⁿ(q) = p`"; for the iterates of `f|_U` to be defined the orbit must stay in `U`.) -/
def localStableSet (f : X → X) (p : X) (U : Set X) : Set X :=
  {x | (∀ n : ℕ, f^[n] x ∈ U) ∧ Tendsto (fun n : ℕ ↦ f^[n] x) atTop (𝓝 p)}

/-- The **global stable set** of `f` at `p` (TeX 13182–13184): the points whose forward orbit
tends to `p`. -/
def globalStableSet (f : X → X) (p : X) : Set X :=
  {x | Tendsto (fun n : ℕ ↦ f^[n] x) atTop (𝓝 p)}

/-- The **local unstable set** of `f|_U` at `p` ("Unstable for `f` means stable for `f⁻¹`",
TeX 13207–13208): the points `x` having a backward orbit `y` (`y 0 = x`, `f (y (n + 1)) = y n`) in
`U` that tends to `p`. For an `f` invertible on `U` it is the local stable set of `f⁻¹|_U`. -/
def localUnstableSet (f : X → X) (p : X) (U : Set X) : Set X :=
  {x | ∃ y : ℕ → X, y 0 = x ∧ (∀ n, y n ∈ U ∧ f (y (n + 1)) = y n) ∧ Tendsto y atTop (𝓝 p)}

/-- A point of the local stable set lies in `U`. -/
theorem mem_of_mem_localStableSet {f : X → X} {p : X} {U : Set X} {x : X}
    (h : x ∈ localStableSet f p U) : x ∈ U := by
  simpa using h.1 0

/-- A point of the local unstable set lies in `U`. -/
theorem mem_of_mem_localUnstableSet {f : X → X} {p : X} {U : Set X} {x : X}
    (h : x ∈ localUnstableSet f p U) : x ∈ U := by
  obtain ⟨y, rfl, hy, -⟩ := h
  exact (hy 0).1

/-- **An orbit tending to `p` eventually lies in the local stable set** of any neighborhood `U`
of `p` ("by the definition of the stable manifold", TeX 13002–13005): the tail of the orbit
stays in `U`.

Proof: `fⁿ(x) ∈ U` for `n ≥ N`; then `f^[k] (f^[n] x) = f^[k + n] x ∈ U` and tends to `p`. -/
theorem eventually_iterate_mem_localStableSet {f : X → X} {p : X} {U : Set X} (hU : U ∈ 𝓝 p)
    {x : X} (hx : Tendsto (fun n : ℕ ↦ f^[n] x) atTop (𝓝 p)) :
    ∀ᶠ n in atTop, f^[n] x ∈ localStableSet f p U := by
  sorry

/-- **A backward orbit tending to `p` eventually lies in the local unstable set** of any
neighborhood `U` of `p`: if `f (y (n + 1)) = y n` for all `n` and `y n → p`, then `y n` lies in
`localUnstableSet f p U` for all large `n` (with the backward orbit `k ↦ y (n + k)`). -/
theorem eventually_mem_localUnstableSet {f : X → X} {p : X} {U : Set X} (hU : U ∈ 𝓝 p)
    {y : ℕ → X} (hy : ∀ n, f (y (n + 1)) = y n) (ht : Tendsto y atTop (𝓝 p)) :
    ∀ᶠ n in atTop, y n ∈ localUnstableSet f p U := by
  sorry

/-- **Unstable for `f` means stable for `f⁻¹`** (TeX 13207–13208): for an open partial
homeomorphism `e` and a set `U` inside both its source and its target, the local stable set of
`e⁻¹|_U` is the local unstable set of `e|_U` (a forward `e⁻¹`-orbit in `U` is a backward
`e`-orbit, and conversely), and symmetrically.

Proof: if `y n = e.symm^[n] x ∈ U ⊆ e.target`, then `e (y (n + 1)) = e (e.symm (y n)) = y n`;
conversely, if `e (y (n + 1)) = y n` with `y (n + 1) ∈ U ⊆ e.source`, then
`e.symm (y n) = y (n + 1)`, so `y n = e.symm^[n] x` by induction. -/
theorem localStableSet_symm_eq_localUnstableSet (e : OpenPartialHomeomorph X X) {p : X}
    {U : Set X} (hU : U ⊆ e.source ∩ e.target) :
    localStableSet e.symm p U = localUnstableSet e p U ∧
      localUnstableSet e.symm p U = localStableSet e p U := by
  sorry

end Function

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A linear map is **hyperbolic** (TeX 13189–13191) if it has no eigenvalue of absolute value
`1`: no complex root of its characteristic polynomial has modulus `1`. (A real operator may have
non-real eigenvalues, so the eigenvalues are the complex roots of `LinearMap.charpoly`.) -/
def IsHyperbolic (A : E →L[ℝ] E) : Prop :=
  ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly (A : E →ₗ[ℝ] E)) = 0 → ‖μ‖ ≠ 1

/-- The **stable subspace** of `A`: the vectors `v` with `Aⁿ v → 0`. For a hyperbolic `A` it is
the stable summand of TeX 13191–13195 (the sum of the generalized eigenspaces of the eigenvalues
of modulus `< 1`). -/
def stableSubspace (A : E →L[ℝ] E) : Submodule ℝ E where
  carrier := {v | Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0)}
  add_mem' {v w} hv hw := by
    simp only [mem_ofPred_eq, map_add] at hv hw ⊢
    simpa using hv.add hw
  zero_mem' := by simp
  smul_mem' c v hv := by
    simp only [mem_ofPred_eq, map_smul] at hv ⊢
    simpa using hv.const_smul c

/-- The **unstable subspace** of `A`: the vectors `v` having a backward orbit tending to `0`
(`w 0 = v`, `A (w (n + 1)) = w n`, `w n → 0`). For a hyperbolic `A` it is the unstable summand of
TeX 13191–13195 (the sum of the generalized eigenspaces of the eigenvalues of modulus `> 1`). -/
def unstableSubspace (A : E →L[ℝ] E) : Submodule ℝ E where
  carrier := {v | ∃ w : ℕ → E, w 0 = v ∧ (∀ n, A (w (n + 1)) = w n) ∧
    Tendsto w atTop (𝓝 0)}
  add_mem' {v₁ v₂} h₁ h₂ := by
    obtain ⟨w₁, h01, hA1, ht1⟩ := h₁
    obtain ⟨w₂, h02, hA2, ht2⟩ := h₂
    refine ⟨fun n ↦ w₁ n + w₂ n, by simp [h01, h02], fun n ↦ by simp [hA1, hA2], ?_⟩
    simpa using ht1.add ht2
  zero_mem' := ⟨fun _ ↦ 0, rfl, fun _ ↦ by simp, tendsto_const_nhds⟩
  smul_mem' c v h := by
    obtain ⟨w, h0, hA, ht⟩ := h
    refine ⟨fun n ↦ c • w n, by simp [h0], fun n ↦ by simp [hA], ?_⟩
    simpa using ht.const_smul c

/-- **The hyperbolic splitting** (TeX 13191–13195): for a hyperbolic linear map the stable and
unstable subspaces are complementary, `E = E_s ⊕ E_u`. -/
theorem isCompl_stableSubspace_unstableSubspace {A : E →L[ℝ] E} (hA : A.IsHyperbolic) :
    IsCompl (stableSubspace A) (unstableSubspace A) := by
  sorry

end ContinuousLinearMap

namespace Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The stable manifold theorem** for maps, in graph form (Irwin, *Smooth Dynamical Systems*,
Chapter 6; the form of Theorem A.3.1, TeX 13198–13211, used by Theorem 14.3.3 and Remark 14.3.4).
Let `f` be `Cⁿ` (`1 ≤ n ≤ ∞`) on a neighborhood `W` of a fixed point `p`, with invertible and
hyperbolic derivative `A = Df(p)` (`f` is a local diffeomorphism at `p`), and let `E_s`, `E_u` be
the stable and unstable subspaces of `A`. Then there are an open neighborhood `U` of `p` and `Cⁿ`
maps `h_s : E_s → E_u`, `h_u : E_u → E_s`, vanishing with their derivatives at `0`, such that

* the local stable set of `f|_U` is the graph `{p + x + h_s(x)}` of `h_s` over a neighborhood
  `V_s` of `0` in `E_s` (a `Cⁿ` embedded submanifold tangent at `p` to `E_s`), and
* the local unstable set of `f|_U` is the graph `{p + y + h_u(y)}` of `h_u` over a neighborhood
  `V_u` of `0` in `E_u` (a `Cⁿ` embedded submanifold tangent at `p` to `E_u`).

The book's statement also asserts that the global stable set is an immersed submanifold; no proof
of the book uses that part, which is not stated here. -/
theorem exists_localStableSet_localUnstableSet_eq_graph {f : E → E} {p : E} {W : Set E}
    {n : ℕ∞} (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) (hfix : f p = p)
    (hinv : (fderiv ℝ f p).IsInvertible) (hyp : (fderiv ℝ f p).IsHyperbolic) :
    ∃ U ∈ 𝓝 p, IsOpen U ∧
      (∃ Vs ∈ 𝓝 (0 : (fderiv ℝ f p).stableSubspace),
        ∃ hs : (fderiv ℝ f p).stableSubspace → (fderiv ℝ f p).unstableSubspace,
          ContDiffOn ℝ n hs Vs ∧ hs 0 = 0 ∧ fderiv ℝ hs 0 = 0 ∧
          localStableSet f p U = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs) ∧
      (∃ Vu ∈ 𝓝 (0 : (fderiv ℝ f p).unstableSubspace),
        ∃ hu : (fderiv ℝ f p).unstableSubspace → (fderiv ℝ f p).stableSubspace,
          ContDiffOn ℝ n hu Vu ∧ hu 0 = 0 ∧ fderiv ℝ hu 0 = 0 ∧
          localUnstableSet f p U = (fun y ↦ p + ↑y + ↑(hu y)) '' Vu) := by
  sorry

end Function
