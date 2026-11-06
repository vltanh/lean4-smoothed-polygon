module

public import SmoothedPolygons.Ch2.MultiCurve

/-!
# Hyperbolic arcs (Lemma 3.1.8)

If two curves `σ_{i-1}` and `σ_{i+1}` of a multi-curve parametrizing the boundary of a centrally
symmetric convex disk move along straight lines during a time interval, then the third curve `σ_i`
moves along a hyperbolic arc whose asymptotes are these two lines (Reinhardt's observation that
the pencil of lines cutting a constant area from a parallelogram envelopes a hyperbola).

The lemma belongs to §3.1 (`SmoothedPolygons.Ch3.StateDynamics`); it is kept in its own module
because it uses only the vocabulary of Chapter 2 (`IsCCSDisk`, `IsMultiCurve`, `det2`) and adding
it to `StateDynamics` would rebuild the modules of Chapters 3–7 that import it.

Conventions. The line through `p` with direction `d ≠ 0` is `{x | det(d, x - p) = 0}`. For two
lines `L₁ = {det(d₁, x - p₁) = 0}` and `L₂ = {det(d₂, x - p₂) = 0}` that are not parallel
(`det(d₁, d₂) ≠ 0`), the level sets `{x | det(d₁, x - p₁) · det(d₂, x - p₂) = c}` with `c ≠ 0` are
exactly the hyperbolas with asymptotes `L₁` and `L₂`, as in Remark 2.2.4 (`hexHyperbolaFun`).
-/

@[expose] public section

namespace SmoothedPolygons

/-- **Lemma 3.1.8** (`lem:hyp-arc`). Suppose that `K ∈ 𝔎_ccs` and that the boundary of `K` is
parametrized by a `C¹` multi-curve `σ`. If two curves `σ_{i-1}` and `σ_{i+1}` move along straight
lines during some time interval, then the third curve `σ_i` moves along a hyperbolic arc, whose
asymptotes are the lines determined by `σ_{i-1}` and `σ_{i+1}`.

Reading. "The boundary is parametrized by a `C¹` multi-curve" is read, as in §2.4 (TeX 1944–1947:
"we can parameterize the boundary by a regular `C¹` curve"), as: `σ` is a `C¹` multi-curve on
`[0, t_f]` (Definition 2.4.1), every `σ_j(t)` lies on the boundary of `K`, the arcs
`σ_j([0, t_f])` cover the boundary, and the curves are regular (`σ_j' ≠ 0`). The time interval is
`[a, b] ⊆ [0, t_f]` with `a < b`; `σ_{i-1}` moves along the line `L₁` through `p₁` with direction
`d₁ ≠ 0`, and `σ_{i+1}` along the line `L₂` through `p₂` with direction `d₂ ≠ 0` (regular curves
are not constant, so these are the lines determined by `σ_{i-1}` and `σ_{i+1}`).
The conclusion: the lines are not parallel, and `σ_i([a, b])` lies on one hyperbola
`det(d₁, x - p₁) · det(d₂, x - p₂) = c`, `c ≠ 0`, with asymptotes `L₁` and `L₂`.

Without regularity the statement is false: for the square `[-λ, λ]²`, `λ² = √3/2`, the boundary
has a `C¹` multi-curve in which `σ₂ = (-λ, 0)` is constant while `σ₁` and `σ₃ = -σ₀` slide along
the parallel edge lines `y = λ` and `y = -λ`; no hyperbola has parallel asymptotes. -/
theorem lemma3_1_8 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    {tf : ℝ} (hσ : IsMultiCurve 1 σ tf) (hbd : ∀ j, ∀ t ∈ Set.Icc 0 tf, σ j t ∈ frontier K)
    (hcover : (⋃ j, σ j '' Set.Icc 0 tf) = frontier K)
    (hreg : ∀ j, ∀ t ∈ Set.Icc 0 tf, derivWithin (σ j) (Set.Icc 0 tf) t ≠ 0)
    (i : ZMod 6) {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ tf)
    {p₁ d₁ p₂ d₂ : Fin 2 → ℝ} (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (h₁ : ∀ t ∈ Set.Icc a b, det2 d₁ (σ (i - 1) t - p₁) = 0)
    (h₂ : ∀ t ∈ Set.Icc a b, det2 d₂ (σ (i + 1) t - p₂) = 0) :
    det2 d₁ d₂ ≠ 0 ∧ ∃ c : ℝ, c ≠ 0 ∧ ∀ t ∈ Set.Icc a b,
      det2 d₁ (σ i t - p₁) * det2 d₂ (σ i t - p₂) = c := by
  sorry

end SmoothedPolygons
