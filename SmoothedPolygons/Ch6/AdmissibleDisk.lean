module

public import SmoothedPolygons.Ch6.Winding
public import SmoothedPolygons.Ch7.SmoothedPolygonDisk

/-!
# The disk bounded by an admissible trajectory of winding number one (E15)

Problem 3.6.2 opens with "The convex disks in `𝔎_bal` in circle representation arise via the
following optimal control problem" (TeX 3205). Its converse, that an admissible trajectory bounds a
balanced disk whose area is the cost, is used without proof at TeX 4579 (§6.1: "By
Theorem 5.0.2, we may assume that `z` lies in the compact set `𝔥**`", Theorem 5.0.2 being a
statement about balanced disks); REPORT.md, E15. It is false as stated: an admissible trajectory
may wind `1 + 6m` times around the origin
(`exists_isReinhardtAdmissible_not_isWindingOne`, `SmoothedPolygons/Ch6/Winding.lean`). For
winding number one (`IsWindingOne`) it holds: `exists_isBalancedPair_of_isReinhardtAdmissible`.

This is the form of the converse that §6.1 needs: by `isWindingOne_of_reinhardtCost_lt`, every
admissible trajectory of cost less than `7π/2`, in particular every one at most as costly as the
smoothed octagon, has winding number one.

## Proof (to be written): the argument of `smoothedPolygonDisk_isBalancedPair`, generalized

`SmoothedPolygons/Ch7/SmoothedPolygonDisk.lean` proves the statement for the smoothed
`(6k+2)`-gons. In general:

1. *Periodic extension.* `G(t + nT) = G(t) Rⁿ`, `X̃(t + nT) = R⁻ⁿ X(t) Rⁿ` (`n ∈ ℤ`,
   `t ∈ [0, T)`), consistent at the junctions by `g(T) = R`, `X(T) = R⁻¹X(0)R`; period `6T`
   (`R⁶ = I`, `oct_R_pow_six`). `X` is continuous (an integral curve), so `G` is `C¹` with
   `G' = G X̃` everywhere, also at the junctions. `X̃` takes star values.
2. `σ_j(t) = G(t) s_j*`. Multi-points: `det G = 1` (`oct_isMultiPoint_mulVec`). Star condition from
   the star inequalities (`oct_star_mulVec`, the converse of Corollary 3.1.6). Regularity:
   `σ_j' = G X̃ s_j* ≠ 0`. Lipschitz derivatives: `X̃' = [P, X̃]` is bounded, since
   `⟨Z_u, X⟩ < 0` is bounded away from `0` on the compact image of `[0, T] × U_T`
   (`lemma3_3_4`). Curvature `det(σ_j', σ_j'') ≥ 0` almost everywhere: `X' = [P, X]` almost
   everywhere with `u(t) ∈ U_T`, and the curvatures are `-2u_j/⟨Z_u, X⟩ ≥ 0`
   (`oct_stateCurvature_eq`, `oct_det2_curv`, Definition 3.3.2 read backwards). The shift
   `σ_j(t + T) = σ_{j+1}(t)` from `R s_j* = s_{j+1}*` (`oct_R_mulVec_sixthRoot`).
3. *Simplicity from winding number one.* The angle of `σ₀` increases strictly
   (`det(σ₀, σ₀') = X̃₁₀ > 0`) and, by `IsWindingOne` and the shift relation, by exactly `2π` over
   the period `6T` (the angle of `σ₀(t + T) = σ₁(t)` exceeds that of `σ₀(t)` by the angle between
   consecutive points of a multi-point, which is in `(0, π)`, continuous, and `π/3` at `t = 0`);
   a curve turning counterclockwise about the origin by exactly `2π` over a period is simple on the
   period (`oct_injOn_of_phase`, with `oct_phase`).
4. *The disk.* `K` is the region swept from the origin by `σ₀` over a period
   (`PlaneCurve.radialHull`); `PlaneCurve.IsStarCurve` (`Basic/Analysis/Convex/StarCurve.lean`,
   `StarCurveConvex.lean`) gives convexity (`convex_radialHull`, from the curvature condition),
   compactness, `0` in the interior and `∂K = σ₀([0, 6T))`, as in
   `smoothedPolygonDisk_isBalancedPair`; central symmetry from `σ₀(t + 3T) = -σ₀(t)`.
5. *Area.* `area(K) = cost` by the area formula `eqn_cost`
   (`SmoothedPolygons/Ch3/AreaFormula.lean`).

Size: 600–1,000 lines.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix

/-- **The converse of Problem 3.6.2 for winding number one**
(`pbm:reinhardt-optimal-control:converse`, label of this formalization; E15, used without proof at
TeX 4579). An admissible trajectory `(g, X)` of the Reinhardt control problem on `[0, T]` whose
curve `g s₀*` winds once (`IsWindingOne`) extends to `G` on `ℝ` (`G(t + T) = G(t) R`) such that
`σ_j(t) = G(t) s_j*` is the multi-curve of a balanced pair `(K, σ)` in circle representation with
`σ_j(t + T) = σ_{j+1}(t)`, `G = g` and `G⁻¹G' = X` on `[0, T]`, `G⁻¹G'` a star state everywhere, and
`area(K)` equal to the cost of the trajectory. The hypothesis `IsWindingOne` cannot be dropped
(`exists_isReinhardtAdmissible_not_isWindingOne`). -/
theorem exists_isBalancedPair_of_isReinhardtAdmissible {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsReinhardtAdmissible T u g X) (hw : IsWindingOne T g) :
    ∃ (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (G : ℝ → Mat2),
      (∀ t ∈ Icc 0 T, G t = g t) ∧
      (∀ t ∈ Icc 0 T, (G t)⁻¹ * derivEntrywise G t = X t) ∧
      (∀ t, IsStarState ((G t)⁻¹ * derivEntrywise G t)) ∧
      (∀ j t, σ j t = G t *ᵥ sixthRoot j) ∧ (∀ j t, σ j (t + T) = σ (j + 1) t) ∧
      IsBalancedPair K σ T ∧ IsCircleRepresentation σ ∧
      volume K = ENNReal.ofReal (reinhardtCost T X) := by
  sorry

end SmoothedPolygons
