module

public import SmoothedPolygons.Ch14.ArcNormalForm

/-!
# Chapter 14, N4: the parameters of a section point and the quadric relation (3.1)

Part of the formalization's proof of N4 (`UnstableCurveLeavesStarDomain`, Figure 14.2) without
computer assistance. **Departure from the paper**, by the user's decision: the book reads N4 off a
computed figure (Figure 14.2, TeX 11951–11991; REPORT.md E88); the formalization proves it from
the exact structure of the Reinhardt flow along an `e₂`-arc and an invariant region (see
`SmoothedPolygons/Ch14/ArcParams.lean`, and `SmoothedPolygons/Ch14/ArcRegionInvariant.lean` for
the numbering of the steps).

This file is §3: a section point is determined by its arc parameters `(ε, Y, f₀, q, p)`:
`X₀` by `(ε, Y)` (Proposition 2.1), `Λ̂₀ = Λ₁(0) + (3/2) J` linearly by `(f₀, q, p)` ((2.4),
Theorem 2.3; `X₀, V_e, V_f` are a basis of `𝔰𝔩₂(ℝ)`), `Λ_R` by the linear conditions of the
section (`frame_section_costateR`). The remaining constraint `det Λ₁ = 9/4`, i.e.
`⟨Λ̂, Λ̂⟩ = 3⟨Λ̂, J⟩`, is the quadric relation `R = 0` (`ArcParams.rel`, (3.1)). So the section is
parametrized by `(ε, Y, f₀, p)` and a choice of one of the two roots `q` of `R = 0`.

**How (3.1) is proved.** `R` was found by computer algebra (sympy `solve` and `factor`), not by
hand; it is a polynomial identity. Here it is split into two identities that `field_simp` and
`ring` / `linear_combination` check (both also checked with sympy, where they simplify to `0`):

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
  ((2.2)). Substituting the `l`'s, `R - (4Y²/3)(…)` is `0` modulo `√3² = 3` (see the next item;
  `field_simp; ring` alone does not close it).
* (the cofactor, found in review; computed with sympy, `polys.div` by `s² - 3`) write `s = √3`,
  `h3 : s ^ 2 = 3`, `Λ̂₀ = ofFrame l_h l_e l_f`, `X₀ = ofFrame (-ε) (-2εY) (εY'/2)`,
  `Y' = (1 + ε²)/(ε² Y)`. Then (`traceForm_ofFrame`)
  `f₀(2.4) = -s (-2l_h + Y' l_e/2 - 2Y l_f)/(3ε² Y')`, `q = -(s/6)(-4Y l_h + l_e - 4Y² l_f)`,
  `p = (2/s)(Y' l_h - Y'² l_e/4 + l_f)`,
  `9/4 - det Λ₁ = l_h² + l_e l_f + s l_h - (s/2) l_e + 2s l_f` (`det_ofFrame`, using `s² = 3`
  once), and, with `β(l) := l_h² + l_e l_f + s l_h - (s/2) l_e + 2s l_f`,
  `36 ε⁴ s² (R(ε, Y, f₀, q, p) - (4Y²/3) β(l)) = (s² - 3) K`,
  `K = s² A₁² - 3 B₁ (B₁ + 4ε² s (Y - 2))`, `A₁ = 4Y²ε⁴ l_f + 4Yε⁴ l_h + (1 - ε⁴) l_e`,
  `B₁ = 4Y²ε⁴ l_f + 4Y(ε⁴ + ε²) l_h - (1 + ε²)² l_e`
  (an identity of rational functions in `ε, Y, s, l`: after clearing denominators,
  `linear_combination K * h3` up to the normalization `field_simp` chooses).
  The Lean proof of `arcParams_rel_identity` uses this cofactor. With
  `Λ₁ = ofFrame (l_h + (3/2)/s) (l_e + 6/s) (l_f - (3/2)/s)` (`det_ofFrame`),
  `9/4 - det Λ₁ - β(l) = (s² - 3) K₂`, `K₂ = 9/(4s²) - l_h/s + l_e/(2s) - 2l_f/s`, so
  `R - (4Y²/3)(9/4 - det Λ₁) = (s² - 3) (K/(36ε⁴s²) - (4Y²/3) K₂)`: one
  `linear_combination (norm := skip)` of `h3` with this cofactor, then `field_simp; ring` (an
  identity of rational functions, true without `s² = 3`).
  **Simpler, without a cofactor**: put `λ = l/√3` (the frame of `Λ̂₀/√3`). Then `√3` cancels
  (each pairing uses `√3 · √3 = 3` once, `Real.mul_self_sqrt`):
  `f₀(2.4) = (4Y²ε² λ_f + 4Yε² λ_h - (1 + ε²) λ_e)/(2ε²(1 + ε²))`, `q = (4Y² λ_f + 4Y λ_h - λ_e)/2`,
  `p = (4Y²ε⁴ λ_f + 4Y(ε⁴ + ε²) λ_h - (1 + ε²)² λ_e)/(2Y²ε⁴)`,
  `9/4 - det Λ₁ = 3(λ_h² + λ_e λ_f + λ_h - λ_e/2 + 2λ_f)`, and the identity
  `R(ε, Y, f₀, q, p) = 4Y²(λ_h² + λ_e λ_f + λ_h - λ_e/2 + 2λ_f)` is `field_simp; ring` in
  `(ε, Y, λ)`. (Both checked with sympy.)

## Statements

* `frame_reducedCostate`: the frame of `Λ̂₀` on a section point, in the parameters.
* `arcParams_rel_identity`: `R(ε, Y, f₀(2.4), q, p) = (4Y²/3)(9/4 - det Λ₁)` for every phase point
  with `X₀` a star state and `Λ₁` traceless, `f₀(2.4) = -(√3/(3ε³Y')) ⟨Λ̂₀, X₀⟩`.
* **(3.1)** (`arcParams_rel`): `R(arcParams q) = 0` on section points.
* `arcParams_injOn`: a section point is determined by its parameters.

## Proofs (the route)

1. `frame_reducedCostate`: on a section point, `f₀ = f₀(2.4)` (`arcF0_eq_reducedHam`); compute the
   three pairings of `ofFrame l_h l_e l_f` (`traceForm_ofFrame`, `frame_state`) and compare with
   `Λ̂₀` by injectivity of the pairings (or solve the `3 × 3` linear system directly). In Lean:
   write `Λ̂₀ = ofFrame l_h l_e l_f`; substituting the three pairings into the right-hand sides,
   each component is one `linear_combination` of `h3 : √3 ^ 2 = 3`, with the cofactors
   `(4Y²ε⁴ l_f + 4Yε⁴ l_h - (1 + ε²)² l_e)/(12Yε²)`, `-l_e/3` and
   `-(1 + ε²)(4Y²ε² l_f + 4Yε² l_h - (1 + ε²) l_e)/(12Y²ε²)` (no injectivity argument needed).
2. `arcParams_rel_identity`: `Λ̂₀ = ofFrame (frameH Λ̂₀) (frameE Λ̂₀) (frameF Λ̂₀)`
   (`ofFrame_frame`); express `f₀(2.4)`, `q`, `p` through the components and verify the polynomial
   identity above.
3. `arcParams_rel`: step 2 with `det Λ₁ = 9/4` and `f₀ = f₀(2.4)` (`arcF0_eq_reducedHam`).
4. `arcParams_injOn`: `ε`, `Y` and (2.1) give `ρ₀, ρ₁, ρ₂`, hence `X₀` (traceless, `ρ`'s determine
   `a, b, c`; in Lean through the frame, `X₀ = ofFrame (-ε) (-2εY) (εY'/2)`, `frame_state`);
   step 1 gives `Λ̂₀` and `Λ₁ = Λ̂₀ - (3/2) J`; `frame_section_costateR` gives `Λ_R` (traceless).

Also checked numerically, while the statements were written: `R = 0` at a chart point near `W^u`
and at its Poincaré images, the identity at a generic traceless point, the frame of `Λ̂₀`. The
proofs do not depend on these checks.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

variable {q : iso_PhasePt}

/-! ### Helpers: `Λ̂₀` and `Λ₁` in the frame -/

private lemma ofFrame_sub_smul_ofFrame (a b c a' b' c' r : ℝ) :
    ofFrame a b c - r • ofFrame a' b' c' = ofFrame (a - r * a') (b - r * b') (c - r * c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofFrame] <;> ring

private lemma arcVe_eq_ofFrame_arcEps (q : iso_PhasePt) :
    arcVe q.1 = ofFrame (frameE q.1) (-frameE q.1 ^ 2 / arcEps q) (arcEps q) := rfl

private lemma arcVf_eq_ofFrame_arcEps (q : iso_PhasePt) :
    arcVf q.1 = ofFrame (frameF q.1) (arcEps q) (-frameF q.1 ^ 2 / arcEps q) := rfl

/-- `Λ̂₀ = Λ₁(0) + (3/2) J` is traceless when `Λ₁(0)` is. -/
private lemma trace_add_three_halves_smul_J_eq_zero (hL : q.2.1.trace = 0) :
    (q.2.1 + (3 / 2 : ℝ) • J).trace = 0 := by
  simp [Matrix.trace_add, hL, J, Matrix.trace_fin_two]

/-- `Y' = (1 + ε²)/(ε² Y)` ((2.1)). -/
private lemma arcY'_eq_one_add_sq_div (hX : IsStarState q.1) :
    arcY' q = (1 + arcEps q ^ 2) / (arcEps q ^ 2 * arcY q) := by
  rw [← arcParams_Y' hX]
  rfl

/-- **The frame of `Λ̂₀ = Λ₁(0) + (3/2) J` on a section point**, in the parameters (§3): with
`κ = 1 + ε²`,
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
  have hX := hq.2
  have he := arcEps_pos hX
  have hY := one_lt_arcY hX
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : √3 ≠ 0 := by positivity
  obtain ⟨-, hxe, hxf, -⟩ := frame_state hX
  obtain ⟨lh, le, lf, hΛ⟩ : ∃ a b c, q.2.1 + (3 / 2 : ℝ) • J = ofFrame a b c :=
    ⟨_, _, _, (ofFrame_frame (trace_add_three_halves_smul_J_eq_zero hq.1.1.2.1)).symm⟩
  rw [arcF0_eq_reducedHam hq]
  unfold arcQ arcP reducedHam
  rw [hΛ, arcVe_eq_ofFrame_arcEps, arcVf_eq_ofFrame_arcEps, hxe, hxf, state_eq_ofFrame hX]
  simp only [traceForm_ofFrame, frameH_ofFrame, frameE_ofFrame, frameF_ofFrame]
  rw [arcY'_eq_one_add_sq_div hX]
  set e := arcEps q
  set Y := arcY q
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (norm := skip)
      ((4 * Y ^ 2 * e ^ 4 * lf + 4 * Y * e ^ 4 * lh - e ^ 4 * le - 2 * e ^ 2 * le - le) /
        (12 * Y * e ^ 2)) * hs
    field_simp
    ring
  · linear_combination (norm := skip) (-le / 3) * hs
    field_simp
    ring
  · linear_combination (norm := skip)
      (-(e ^ 2 + 1) * (4 * Y ^ 2 * e ^ 2 * lf + 4 * Y * e ^ 2 * lh - e ^ 2 * le - le) /
        (12 * Y ^ 2 * e ^ 2)) * hs
    field_simp
    ring

/-- **The quadric relation as an identity** ((3.1)): for a phase
point with `X₀` a star state and `Λ₁` traceless, with `f₀` given by (2.4),
`R(ε, Y, f₀, q, p) = (4Y²/3)(9/4 - det Λ₁)`. The identity needs `√3² = 3`: see the module
docstring for the `linear_combination` cofactor `K` (with `h3 : √3 ^ 2 = 3`) and for the
substitution `λ = (frame of Λ̂₀)/√3`, after which it is `field_simp; ring`. The proof is one
`linear_combination` of `h3` with the cofactor `K/(36ε⁴s²) - (4Y²/3) K₂` of the module docstring
(`s = √3`, `Λ̂₀ = ofFrame l_h l_e l_f`). -/
theorem arcParams_rel_identity (hX : IsStarState q.1) (hL : q.2.1.trace = 0) :
    (⟨arcEps q, arcY q, -(√3 / (3 * arcEps q ^ 3 * arcY' q)) * reducedHam q.2.1 q.1, 0,
        arcQ q, arcP q⟩ : ArcParams).rel =
      4 * arcY q ^ 2 / 3 * (9 / 4 - q.2.1.det) := by
  have he := arcEps_pos hX
  have hY := one_lt_arcY hX
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : √3 ≠ 0 := by positivity
  obtain ⟨-, hxe, hxf, -⟩ := frame_state hX
  obtain ⟨lh, le, lf, hΛ⟩ : ∃ a b c, q.2.1 + (3 / 2 : ℝ) • J = ofFrame a b c :=
    ⟨_, _, _, (ofFrame_frame (trace_add_three_halves_smul_J_eq_zero hL)).symm⟩
  -- `Λ₁ = Λ̂₀ - (3/2) J` in the frame
  have hdet : q.2.1.det = -((lh - 3 / 2 * -(1 / √3)) ^ 2 +
      (le - 3 / 2 * -(4 / √3)) * (lf - 3 / 2 * (1 / √3))) := by
    rw [eq_sub_of_add_eq hΛ, frame_controlMatrix.2.2.2, ofFrame_sub_smul_ofFrame, det_ofFrame]
  rw [hdet]
  simp only [ArcParams.rel]
  unfold arcQ arcP reducedHam
  rw [hΛ, arcVe_eq_ofFrame_arcEps, arcVf_eq_ofFrame_arcEps, hxe, hxf, state_eq_ofFrame hX]
  simp only [traceForm_ofFrame]
  rw [arcY'_eq_one_add_sq_div hX]
  set e := arcEps q
  set Y := arcY q
  -- the cofactor `K/(36ε⁴s²) - (4Y²/3) K₂` of `s² - 3` (module docstring)
  linear_combination (norm := skip)
    ((√3 ^ 2 * (4 * Y ^ 2 * e ^ 4 * lf + 4 * Y * e ^ 4 * lh + (1 - e ^ 4) * le) ^ 2 -
        3 * (4 * Y ^ 2 * e ^ 4 * lf + 4 * Y * (e ^ 4 + e ^ 2) * lh - (1 + e ^ 2) ^ 2 * le) *
          (4 * Y ^ 2 * e ^ 4 * lf + 4 * Y * (e ^ 4 + e ^ 2) * lh - (1 + e ^ 2) ^ 2 * le +
            4 * e ^ 2 * √3 * (Y - 2))) / (36 * e ^ 4 * √3 ^ 2) -
      4 * Y ^ 2 / 3 * (9 / (4 * √3 ^ 2) - lh / √3 + le / (2 * √3) - 2 * lf / √3)) * hs
  field_simp
  ring

/-- **(3.1)**: the parameters of a section point satisfy the quadric relation `R = 0`. -/
theorem arcParams_rel (hq : IsArcSectionPt q) : (arcParams q).rel = 0 := by
  have h := arcParams_rel_identity hq.2 hq.1.1.2.1
  rw [hq.1.2, sub_self, mul_zero] at h
  rw [← h]
  simp only [ArcParams.rel, arcParams, arcF0_eq_reducedHam hq]

/-- **A section point is determined by its parameters** (§3): `arcParams` is injective
on section points. -/
theorem arcParams_injOn : Set.InjOn arcParams {q | IsArcSectionPt q} := by
  intro q hq q' hq' h
  have hε : arcEps q = arcEps q' := congrArg ArcParams.eps h
  have hY : arcY q = arcY q' := congrArg ArcParams.Y h
  have hf : arcF0 q = arcF0 q' := congrArg ArcParams.f0 h
  have hqq : arcQ q = arcQ q' := congrArg ArcParams.q h
  have hp : arcP q = arcP q' := congrArg ArcParams.p h
  have hY' : arcY' q = arcY' q' := by
    rw [← arcParams_Y' hq.2, ← arcParams_Y' hq'.2, h]
  -- `X₀` by `(ε, Y)` (Proposition 2.1, (2.1))
  have hX : q.1 = q'.1 := by
    rw [state_eq_ofFrame hq.2, state_eq_ofFrame hq'.2, hε, hY, hY']
  -- `Λ̂₀` by `(ε, Y, f₀, q, p)` (`frame_reducedCostate`)
  have hL : q.2.1 = q'.2.1 := by
    have e1 := frame_reducedCostate hq
    have e2 := frame_reducedCostate hq'
    have hΛ : q.2.1 + (3 / 2 : ℝ) • J = q'.2.1 + (3 / 2 : ℝ) • J := by
      rw [← ofFrame_frame (trace_add_three_halves_smul_J_eq_zero hq.1.1.2.1),
        ← ofFrame_frame (trace_add_three_halves_smul_J_eq_zero hq'.1.1.2.1), e1.1, e1.2.1, e1.2.2,
        e2.1, e2.2.1, e2.2.2, hε, hY, hf, hqq, hp]
    exact add_right_cancel hΛ
  -- `Λ_R` by the linear conditions of the section (`frame_section_costateR`)
  have hR : q.2.2 = q'.2.2 := by
    have e1 := frame_section_costateR hq
    have e2 := frame_section_costateR hq'
    rw [← ofFrame_frame hq.1.1.2.2.1, ← ofFrame_frame hq'.1.1.2.2.1, e1.1, e1.2.1, e1.2.2,
      e2.1, e2.2.1, e2.2.2, hε, hX, hL]
  exact Prod.ext hX (Prod.ext hL hR)

end SmoothedPolygons
