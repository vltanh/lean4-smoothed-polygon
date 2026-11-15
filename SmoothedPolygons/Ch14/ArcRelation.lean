module

public import SmoothedPolygons.Ch14.ArcNormalForm

/-!
# Chapter 14, N4: the parameters of a section point and the quadric relation (2.1)

`notes/n4/proof.md` §2.1: a section point is determined by its arc parameters `(ε, Y, f₀, q, p)`:
`X₀` by `(ε, Y)` (Proposition 1.1), `Λ̂₀ = Λ₁(0) + (3/2) J` linearly by `(f₀, q, p)` ((1.5),
Theorem 1.3; `X₀, V_e, V_f` are a basis of `𝔰𝔩₂(ℝ)`), `Λ_R` by the linear conditions of the
section (`frame_section_costateR`). The remaining constraint `det Λ₁ = 9/4`, i.e.
`⟨Λ̂, Λ̂⟩ = 3⟨Λ̂, J⟩`, is the quadric relation `R = 0` (`ArcParams.rel`, (2.1)). So the section is
parametrized by `(ε, Y, f₀, p)` and a choice of one of the two roots `q` of `R = 0`. Part of the
reduction of N4 to (INV) (`ArcRegionInvariant`).

**Departure from the paper.** The book computes the unstable curve numerically (Figure 14.2,
TeX 11951–11991); the formalization proves N4 from (INV) by the exact structure of the arcs (see
`SmoothedPolygons/Ch14/ArcParams.lean`).

**Status of (2.1) in the research notes.** The research found `R` by computer algebra (sympy
`solve` and `factor`, `notes/n4/relation.py`), not by hand; it is a polynomial identity. Here it
is split into two identities a proof agent can check with `field_simp` and `ring` /
`linear_combination` (both re-checked with sympy in `notes/n4f/rel_identity.py`, where they
simplify to `0`):

* (inversion, `frame_reducedCostate`) with `κ = 1 + ε²`, the frame components of `Λ̂₀` are
  `l_h = √3 (Y²ε²p - κ(2ε² + 1) f₀ + κ q)/(2Y)`, `l_e = 2√3 ε² (q - κ f₀)`,
  `l_f = -√3 (Y²ε²p - κ² f₀)/(2Y²)`.
  Check: substitute into `f₀ = -(√3/(3ε³Y')) ⟨Λ̂₀, X₀⟩`, `q = -(√3/(6ε)) ⟨Λ̂₀, V_e⟩`,
  `p = (2/(√3ε)) ⟨Λ̂₀, V_f⟩` with `⟨M, N⟩ = 2m_h n_h + m_e n_f + m_f n_e`,
  `X₀ = (-ε, -2εY, εY'/2)`, `V_e = (x_e, -x_e²/ε, ε)`, `V_f = (x_f, ε, -x_f²/ε)`,
  `Y' = (1 + ε²)/(ε²Y)`; each reduces to an identity of rational functions. Since the map
  `Λ̂ ↦ (⟨Λ̂, X₀⟩, ⟨Λ̂, V_e⟩, ⟨Λ̂, V_f⟩)` is injective on `𝔰𝔩₂(ℝ)` (`X₀, V_e, V_f` is a basis: its
  Gram determinant for the trace form is nonzero), this determines `Λ̂₀`.
* (the relation, `arcParams_rel_identity`)
  `R = (4Y²/3)(l_h² + l_e l_f + √3 l_h - (√3/2) l_e + 2√3 l_f)`, and the bracket is
  `9/4 - det Λ₁`: for traceless `Λ₁ = Λ̂ - (3/2)J`, `det Λ₁ = -⟨Λ₁, Λ₁⟩/2 =
  9/4 - (⟨Λ̂, Λ̂⟩ - 3⟨Λ̂, J⟩)/2`, `⟨Λ̂, Λ̂⟩ = 2l_h² + 2l_e l_f`, `⟨Λ̂, J⟩ = (-2l_h + l_e - 4l_f)/√3`
  ((1.2)). Substituting the `l`'s, `R - (4Y²/3)(…)` is `0` modulo `√3² = 3` (see the next item;
  `field_simp; ring` alone does not close it).
* (the cofactor, the review `notes/briefs/n4_review_report.md`, Documentation 4; computed with
  sympy, `polys.div` by `s² - 3`) write `s = √3`, `h3 : s ^ 2 = 3`, `Λ̂₀ = ofFrame l_h l_e l_f`,
  `X₀ = ofFrame (-ε) (-2εY) (εY'/2)`, `Y' = (1 + ε²)/(ε² Y)`. Then (`traceForm_ofFrame`)
  `f₀(1.5) = -s (-2l_h + Y' l_e/2 - 2Y l_f)/(3ε² Y')`, `q = -(s/6)(-4Y l_h + l_e - 4Y² l_f)`,
  `p = (2/s)(Y' l_h - Y'² l_e/4 + l_f)`,
  `9/4 - det Λ₁ = l_h² + l_e l_f + s l_h - (s/2) l_e + 2s l_f` (`det_ofFrame`, using `s² = 3`
  once), and, with `β(l) := l_h² + l_e l_f + s l_h - (s/2) l_e + 2s l_f`,
  `36 ε⁴ s² (R(ε, Y, f₀, q, p) - (4Y²/3) β(l)) = (s² - 3) K`,
  `K = s² A₁² - 3 B₁ (B₁ + 4ε² s (Y - 2))`, `A₁ = 4Y²ε⁴ l_f + 4Yε⁴ l_h + (1 - ε⁴) l_e`,
  `B₁ = 4Y²ε⁴ l_f + 4Y(ε⁴ + ε²) l_h - (1 + ε²)² l_e`
  (an identity of rational functions in `ε, Y, s, l`: after clearing denominators,
  `linear_combination K * h3` up to the normalization `field_simp` chooses).
  **Simpler, without a cofactor**: put `λ = l/√3` (the frame of `Λ̂₀/√3`). Then `√3` cancels
  (each pairing uses `√3 · √3 = 3` once, `Real.mul_self_sqrt`):
  `f₀(1.5) = (4Y²ε² λ_f + 4Yε² λ_h - (1 + ε²) λ_e)/(2ε²(1 + ε²))`, `q = (4Y² λ_f + 4Y λ_h - λ_e)/2`,
  `p = (4Y²ε⁴ λ_f + 4Y(ε⁴ + ε²) λ_h - (1 + ε²)² λ_e)/(2Y²ε⁴)`,
  `9/4 - det Λ₁ = 3(λ_h² + λ_e λ_f + λ_h - λ_e/2 + 2λ_f)`, and the identity
  `R(ε, Y, f₀, q, p) = 4Y²(λ_h² + λ_e λ_f + λ_h - λ_e/2 + 2λ_f)` is `field_simp; ring` in
  `(ε, Y, λ)`. (Both checked with sympy: `notes/n4s2/cofactor.py`.)

## Statements

* `frame_reducedCostate`: the frame of `Λ̂₀` on a section point, in the parameters.
* `arcParams_rel_identity`: `R(ε, Y, f₀(1.5), q, p) = (4Y²/3)(9/4 - det Λ₁)` for every phase point
  with `X₀` a star state and `Λ₁` traceless, `f₀(1.5) = -(√3/(3ε³Y')) ⟨Λ̂₀, X₀⟩`.
* **(2.1)** (`arcParams_rel`): `R(arcParams q) = 0` on section points.
* `arcParams_injOn`: a section point is determined by its parameters.

## Proofs (the route)

1. `frame_reducedCostate`: on a section point, `f₀ = f₀(1.5)` (`arcF0_eq_reducedHam`); compute the
   three pairings of `ofFrame l_h l_e l_f` (`traceForm_ofFrame`, `frame_state`) and compare with
   `Λ̂₀` by injectivity of the pairings (or solve the `3 × 3` linear system directly).
2. `arcParams_rel_identity`: `Λ̂₀ = ofFrame (frameH Λ̂₀) (frameE Λ̂₀) (frameF Λ̂₀)`
   (`ofFrame_frame`); express `f₀(1.5)`, `q`, `p` through the components and verify the polynomial
   identity above.
3. `arcParams_rel`: step 2 with `det Λ₁ = 9/4` and `f₀ = f₀(1.5)` (`arcF0_eq_reducedHam`).
4. `arcParams_injOn`: `ε`, `Y` and (1.3) give `ρ₀, ρ₁, ρ₂`, hence `X₀` (traceless, `ρ`'s determine
   `a, b, c`); step 1 gives `Λ̂₀` and `Λ₁ = Λ̂₀ - (3/2) J`; `frame_section_costateR` gives
   `Λ_R` (traceless).

Checked numerically (`notes/n4f/check1.py`: `R = 0` at a chart point near `W^u`, the identity at a
generic traceless point, the frame of `Λ̂₀`; `notes/n4f/check2.py`: `R = 0` at Poincaré images).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

variable {q : iso_PhasePt}

/-- **The frame of `Λ̂₀ = Λ₁(0) + (3/2) J` on a section point**, in the parameters (proof.md §2.1;
`notes/n4/relation.py`): with `κ = 1 + ε²`,
`l_h = √3 (Y²ε²p - κ(2ε² + 1) f₀ + κ q)/(2Y)`, `l_e = 2√3 ε² (q - κ f₀)`,
`l_f = -√3 (Y²ε²p - κ² f₀)/(2Y²)`. -/
theorem frame_reducedCostate (hq : IsArcSectionPt q) :
    frameH (q.2.1 + (3 / 2 : ℝ) • J) =
        √3 * (arcY q ^ 2 * arcEps q ^ 2 * arcP q -
          (1 + arcEps q ^ 2) * (2 * arcEps q ^ 2 + 1) * arcF0 q +
          (1 + arcEps q ^ 2) * arcQ q) / (2 * arcY q) ∧
      frameE (q.2.1 + (3 / 2 : ℝ) • J) =
        2 * √3 * arcEps q ^ 2 * (arcQ q - (1 + arcEps q ^ 2) * arcF0 q) ∧
      frameF (q.2.1 + (3 / 2 : ℝ) • J) =
        -(√3 * (arcY q ^ 2 * arcEps q ^ 2 * arcP q - (1 + arcEps q ^ 2) ^ 2 * arcF0 q)) /
          (2 * arcY q ^ 2) := by
  sorry

/-- **The quadric relation as an identity** (proof.md (2.1), `notes/n4/relation.py`): for a phase
point with `X₀` a star state and `Λ₁` traceless, with `f₀` given by (1.5),
`R(ε, Y, f₀, q, p) = (4Y²/3)(9/4 - det Λ₁)`. The identity needs `√3² = 3`: see the module
docstring for the `linear_combination` cofactor `K` (with `h3 : √3 ^ 2 = 3`) and for the
substitution `λ = (frame of Λ̂₀)/√3`, after which it is `field_simp; ring`. -/
theorem arcParams_rel_identity (hX : IsStarState q.1) (hL : q.2.1.trace = 0) :
    (⟨arcEps q, arcY q, -(√3 / (3 * arcEps q ^ 3 * arcY' q)) * reducedHam q.2.1 q.1, 0,
        arcQ q, arcP q⟩ : ArcParams).rel =
      4 * arcY q ^ 2 / 3 * (9 / 4 - q.2.1.det) := by
  sorry

/-- **(2.1)**: the parameters of a section point satisfy the quadric relation `R = 0`. -/
theorem arcParams_rel (hq : IsArcSectionPt q) : (arcParams q).rel = 0 := by
  sorry

/-- **A section point is determined by its parameters** (proof.md §2.1): `arcParams` is injective
on section points. -/
theorem arcParams_injOn : Set.InjOn arcParams {q | IsArcSectionPt q} := by
  sorry

end SmoothedPolygons
