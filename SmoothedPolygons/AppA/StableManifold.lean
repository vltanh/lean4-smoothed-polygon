module

public import StableManifold
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Stable and unstable manifolds (Appendix A.3)

Appendix A.3 of Hales–Vajjha, *Packings of Smoothed Polygons* (`sec:stable-manifold`,
TeX 13176–13211) recalls from Irwin (*Smooth Dynamical Systems*, Academic Press 1980,
reprinted World Scientific 2001, Chapter 6) the local and global stable sets of a fixed point of
a diffeomorphism, hyperbolic fixed points and their stable and unstable summands, and Theorem
A.3.1 (Irwin): at a hyperbolic fixed point of a `C^r` diffeomorphism (`r ≥ 1`), the local stable set of `f|_U`, for some open
neighborhood `U` of `p`, is a `C^r` embedded submanifold tangent at `p` to the stable summand, and
the global stable set is a `C^r` immersed submanifold; "There are corresponding statements for
local and global unstable manifolds".

The definitions are `Function.localStableSet`, `Function.localUnstableSet`,
`ContinuousLinearMap.IsHyperbolic`, `ContinuousLinearMap.stableSubspace` and
`ContinuousLinearMap.unstableSubspace` (`StableManifold/Defs.lean` of the StableManifold package)
and `Function.globalStableSet` (`StableManifold/LocalSets.lean`). The stable and unstable summands
are defined by the dynamics of `A = Df(p)`: the vectors `v` with `Aⁿ v → 0`, and those with a
backward orbit tending to `0`. The book defines them by the characteristic polynomial (the sums of
the generalized eigenspaces of the eigenvalues of modulus `< 1` and `> 1`, TeX 13191–13197); at a
hyperbolic fixed point the two definitions agree, and they give complementary summands
(`ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace`).

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
The one-neighbourhood form of the general theorem gives some open neighbourhood `U` of `p`, not
necessarily inside `e.source`; so it is applied to the map that is `e` on the source and
sends every other point to a fixed point `q ∉ e.source` (when `e.source ≠ univ`). An orbit of that
map leaving the source becomes constant `q ≠ p`, and a backward orbit through a point of the source
stays in it, so the local sets of `e` on `U ∩ e.source` are those of the modified map on `U`
(intersected with the source, a graph over a smaller neighborhood of `0` in the unstable summand).
The package's stronger form, for every small neighbourhood
(`Function.exists_nhds_localStableSet_localUnstableSet_eq_graph`), would make this cut-off
unnecessary (REPORT.md, Section 11).
-/

@[expose] public section

namespace SmoothedPolygons

open Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Restricting the local sets to the source

The stable manifold theorem (`Function.exists_localStableSet_localUnstableSet_eq_graph`) gives
some open neighborhood `U` of the fixed point, not necessarily inside `e.source`. To get one inside
the source, apply it to the map `f'` that is `e` on the source and sends every other point to a
fixed point `q` outside the source: an orbit of `f'` that leaves the source is eventually `q`, so it
does not tend to `p`, and a backward orbit of `f'` through a point of the source stays in the
source. Hence the local sets of `e` on `U ∩ e.source` are those of `f'` on `U` (intersected with the
source). -/

open Classical in
/-- The map that is `f` on `S` and `q` elsewhere. -/
private noncomputable def l6j_cut {X : Type*} (f : X → X) (S : Set X) (q : X) : X → X :=
  fun x ↦ if x ∈ S then f x else q

private lemma l6j_cut_of_mem {X : Type*} {f : X → X} {S : Set X} {q x : X} (hx : x ∈ S) :
    l6j_cut f S q x = f x := by
  simp [l6j_cut, hx]

private lemma l6j_cut_of_not_mem {X : Type*} {f : X → X} {S : Set X} {q x : X} (hx : x ∉ S) :
    l6j_cut f S q x = q := by
  simp [l6j_cut, hx]

/-- Along an orbit that stays in `S` (for either map) the two maps have the same iterates. -/
private lemma l6j_iterate_cut {X : Type*} {f : X → X} {S : Set X} {q x : X}
    (h : (∀ n, (l6j_cut f S q)^[n] x ∈ S) ∨ ∀ n, f^[n] x ∈ S) (n : ℕ) :
    (l6j_cut f S q)^[n] x = f^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, l6j_cut_of_mem]
    rcases h with h | h
    · exact ih ▸ h n
    · exact h n

private lemma l6j_localStableSet_cut {X : Type*} [TopologicalSpace X] [T2Space X] {f : X → X}
    {S : Set X} {p q : X} (hp : p ∈ S) (hq : q ∉ S) (U : Set X) :
    Function.localStableSet (l6j_cut f S q) p U = Function.localStableSet f p (U ∩ S) := by
  ext x
  constructor
  · rintro ⟨hU, ht⟩
    have hS : ∀ n, (l6j_cut f S q)^[n] x ∈ S := by
      by_contra hn
      push Not at hn
      obtain ⟨n, hn⟩ := hn
      have hq' : ∀ m, (l6j_cut f S q)^[m + (n + 1)] x = q := by
        intro m
        induction m with
        | zero =>
          rw [zero_add, Function.iterate_succ_apply', l6j_cut_of_not_mem hn]
        | succ m ih =>
          rw [show m + 1 + (n + 1) = (m + (n + 1)) + 1 by ring, Function.iterate_succ_apply', ih,
            l6j_cut_of_not_mem hq]
      have ht' : Tendsto (fun m ↦ (l6j_cut f S q)^[m + (n + 1)] x) atTop (𝓝 p) :=
        ht.comp (tendsto_add_atTop_nat (n + 1))
      simp only [hq'] at ht'
      exact hq ((tendsto_nhds_unique tendsto_const_nhds ht') ▸ hp)
    have he := l6j_iterate_cut (Or.inl hS)
    refine ⟨fun n ↦ ⟨he n ▸ hU n, he n ▸ hS n⟩, ?_⟩
    simpa only [he] using ht
  · rintro ⟨hU, ht⟩
    have he := l6j_iterate_cut (q := q) (Or.inr fun n ↦ (hU n).2)
    exact ⟨fun n ↦ (he n).symm ▸ (hU n).1, by simpa only [he] using ht⟩

private lemma l6j_localUnstableSet_cut {X : Type*} [TopologicalSpace X] {f : X → X}
    {S : Set X} {p q : X} (hq : q ∉ S) (U : Set X) :
    Function.localUnstableSet f p (U ∩ S) = Function.localUnstableSet (l6j_cut f S q) p U ∩ S := by
  ext x
  constructor
  · rintro ⟨y, rfl, hy, ht⟩
    exact ⟨⟨y, rfl, fun n ↦ ⟨(hy n).1.1, by rw [l6j_cut_of_mem (hy (n + 1)).1.2, (hy n).2]⟩, ht⟩,
      (hy 0).1.2⟩
  · rintro ⟨⟨y, rfl, hy, ht⟩, hx⟩
    have hS : ∀ n, y n ∈ S := by
      intro n
      induction n with
      | zero => exact hx
      | succ n ih =>
        by_contra h
        rw [← (hy n).2, l6j_cut_of_not_mem h] at ih
        exact hq ih
    refine ⟨y, rfl, fun n ↦ ⟨⟨(hy n).1, hS n⟩, ?_⟩, ht⟩
    rw [← l6j_cut_of_mem (f := f) (q := q) (hS (n + 1)), (hy n).2]

omit [FiniteDimensional ℝ E] in
/-- The derivative of an open partial homeomorphism that is `C¹` with a `C¹` inverse is invertible
at a fixed point. -/
private lemma l6j_isInvertible_fderiv (e : OpenPartialHomeomorph E E) {p : E} (hp : p ∈ e.source)
    (hfix : e p = p) {r : ℕ∞} (hr : 1 ≤ r) (he : ContDiffOn ℝ r e e.source)
    (he' : ContDiffOn ℝ r e.symm e.target) : (fderiv ℝ e p).IsInvertible := by
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    have : (0 : ℕ∞) < r := zero_lt_one.trans_le hr
    exact_mod_cast this.ne'
  have hpt : p ∈ e.target := hfix ▸ e.map_source hp
  have hsp : e.symm p = p := by simpa [hfix] using e.left_inv hp
  have hd : HasFDerivAt e (fderiv ℝ e p) p :=
    ((he.contDiffAt (e.open_source.mem_nhds hp)).differentiableAt hr0).hasFDerivAt
  have hd' : HasFDerivAt e.symm (fderiv ℝ e.symm p) p :=
    ((he'.contDiffAt (e.open_target.mem_nhds hpt)).differentiableAt hr0).hasFDerivAt
  have h1 : (fderiv ℝ e.symm p).comp (fderiv ℝ e p) = ContinuousLinearMap.id ℝ E := by
    have hc : HasFDerivAt (e.symm ∘ e) ((fderiv ℝ e.symm p).comp (fderiv ℝ e p)) p := by
      refine HasFDerivAt.comp p ?_ hd
      rw [hfix]
      exact hd'
    exact hc.unique ((hasFDerivAt_id p).congr_of_eventuallyEq (e.eventually_left_inverse hp))
  have h2 : (fderiv ℝ e p).comp (fderiv ℝ e.symm p) = ContinuousLinearMap.id ℝ E := by
    have hc : HasFDerivAt (e ∘ e.symm) ((fderiv ℝ e p).comp (fderiv ℝ e.symm p)) p := by
      refine HasFDerivAt.comp p ?_ hd'
      rw [hsp]
      exact hd
    exact hc.unique ((hasFDerivAt_id p).congr_of_eventuallyEq (e.eventually_right_inverse hpt))
  refine ⟨ContinuousLinearEquiv.equivOfInverse (fderiv ℝ e p) (fderiv ℝ e.symm p)
    (fun v ↦ ?_) (fun v ↦ ?_), rfl⟩
  · simpa using congrArg (fun L : E →L[ℝ] E ↦ L v) h1
  · simpa using congrArg (fun L : E →L[ℝ] E ↦ L v) h2

/-- **Theorem A.3.1** (`thm:stable-manifold`, Irwin; TeX 13198–13211), local part, for a `C^r`
diffeomorphism `e` between open subsets of a finite-dimensional real normed space with a hyperbolic
fixed point `p` (`1 ≤ r ≤ ∞`): for some open neighborhood `U` of `p`, the local stable set of `e|_U`
at `p` is a `C^r` embedded submanifold tangent at `p` to the stable summand of `De(p)` (the graph of
a `C^r` map `h_s` from the stable summand to the unstable one, with `h_s(0) = 0`, `Dh_s(0) = 0`),
and the local unstable set is a `C^r` embedded submanifold tangent at `p` to the unstable summand.
-/
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
  have hinv := l6j_isInvertible_fderiv e hp hfix hr he he'
  by_cases hS : e.source = univ
  · obtain ⟨U, hU, hUo, hst, hun⟩ := Function.exists_localStableSet_localUnstableSet_eq_graph hr
      (e.open_source.mem_nhds hp) he hfix hinv hyp
    exact ⟨U, hU, hUo, hS ▸ subset_univ U, hst, hun⟩
  obtain ⟨q, hq⟩ : ∃ q, q ∉ e.source := by
    by_contra h
    push Not at h
    exact hS (eq_univ_of_forall h)
  set f := l6j_cut e e.source q with hfdef
  have hfe : f =ᶠ[𝓝 p] e :=
    Filter.eventually_of_mem (e.open_source.mem_nhds hp) fun x hx ↦ l6j_cut_of_mem hx
  have hfd : fderiv ℝ f p = fderiv ℝ e p := hfe.fderiv_eq
  have hf : ContDiffOn ℝ r f e.source := he.congr fun x hx ↦ l6j_cut_of_mem hx
  have hfix' : f p = p := by rw [hfdef, l6j_cut_of_mem hp, hfix]
  obtain ⟨U, hU, hUo, hst, hun⟩ := Function.exists_localStableSet_localUnstableSet_eq_graph hr
    (e.open_source.mem_nhds hp) hf hfix' (hfd ▸ hinv) (hfd ▸ hyp)
  rw [hfd] at hst hun
  refine ⟨U ∩ e.source, inter_mem hU (e.open_source.mem_nhds hp), hUo.inter e.open_source,
    inter_subset_right, ?_, ?_⟩
  · obtain ⟨Vs, hVs, hs, hsC, hs0, hsd, hsU⟩ := hst
    refine ⟨Vs, hVs, hs, hsC, hs0, hsd, ?_⟩
    rw [← l6j_localStableSet_cut hp hq, ← hsU]
  · obtain ⟨Vu, hVu, hu, huC, hu0, hud, huU⟩ := hun
    set g : (fderiv ℝ e p).unstableSubspace → E := fun y ↦ p + ↑y + ↑(hu y) with hg
    have hgc : ContinuousAt g 0 := by
      have : ContinuousAt hu 0 := huC.continuousOn.continuousAt hVu
      exact (continuous_const.add continuous_subtype_val).continuousAt.add
        (continuous_subtype_val.continuousAt.comp this)
    have hg0 : g 0 = p := by simp [hg, hu0]
    have hgs : e.source ∈ 𝓝 (g 0) := by rw [hg0]; exact e.open_source.mem_nhds hp
    refine ⟨Vu ∩ g ⁻¹' e.source, inter_mem hVu (hgc.preimage_mem_nhds hgs), hu,
      huC.mono inter_subset_left, hu0, hud, ?_⟩
    rw [l6j_localUnstableSet_cut hq, image_inter_preimage, ← huU]

end SmoothedPolygons
