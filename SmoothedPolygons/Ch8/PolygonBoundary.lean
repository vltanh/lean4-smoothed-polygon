module

public import SmoothedPolygons.Ch8.FiniteBangBang
public import SmoothedPolygons.Ch3.HyperbolicArc
public import SmoothedPolygons.Ch3.ControlProblem
public import SmoothedPolygons.Ch2.Reinhardt

/-!
# Finite bang-bang trajectories bound smoothed polygons (Remark 8.3.3)

Remark 8.3.3 (unlabelled, TeX 7610–7616; label of this formalization `rem:smoothed-polygon`):
"a trajectory `(g, X)` that is extremal and edge-extremal that does not meet the singular locus
`𝒮_sing` defines a balanced disk `K(g, X) ∈ 𝔎_bal` whose boundary is a smoothed polygon,
consisting of finitely many straight edges and hyperbolic arcs." The remark has no proof. Its
content is Theorem 8.3.2 together with the discussion of §7.2 (TeX 5612–5622, recorded as
Lemma 7.2.1): on an interval of constant control at a vertex `e_{i+1}`, two of the state-dependent
curvatures vanish, so `σ_{2m}` (`m ≠ i`) and their opposites move along straight lines, and by
Lemma 3.1.8 the third pair moves along hyperbolic arcs whose asymptotes are those lines. The same
sentence is the first line of the proof of Theorem 16.3.1: "A bang-bang trajectory with finitely
many switches is a polygon with rounded corners of the sort described by Reinhardt".

Definitions: `IsHyperbolicArc` (the conclusion of Lemma 3.1.8), `IsSmoothedPolygonBoundary` (the
boundary is the union of finitely many straight edges and hyperbolic arcs, each hyperbolic arc
joining two edges and having as asymptotes lines that extend edges of the boundary), and
`IsSmoothedPolygon` (the gloss of Theorem 16.3.1, TeX 12800–12804: in addition, a centrally
symmetric convex disk with no corners).

Reading of "defines a balanced disk `K(g, X)`": the disk attached to `(g, X)` (index entry
"`K(g, X)`, attached to data `(g, X)`") is taken as given, a balanced pair `(K, σ)` with
`σ_j = g s_j*` on `[0, t_f]` and `σ_j(t + t_f) = σ_{j+1}(t)`. Such a disk exists when the
trajectory has winding number one (`exists_isBalancedPair_of_isReinhardtAdmissible`), in
particular for every trajectory cheaper than the octagon (`isWindingOne_of_reinhardtCost_lt`) and
so for the global minimizer; the book does not show that it exists for every extremal (admissible
trajectories without winding number one exist, `exists_isReinhardtAdmissible_not_isWindingOne`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- `γ` traces on `[α, β]` (`α < β`, continuous and injective there) an arc of the hyperbola
`det(d₁, x - p₁) · det(d₂, x - p₂) = c`, `c ≠ 0`, whose asymptotes are the non-parallel lines
`p₁ + ℝ d₁` and `p₂ + ℝ d₂`: the form of the conclusion of Lemma 3.1.8 (`lemma3_1_8`). -/
def IsHyperbolicArc (γ : ℝ → Fin 2 → ℝ) (α β : ℝ) (p₁ d₁ p₂ d₂ : Fin 2 → ℝ) : Prop :=
  α < β ∧ ContinuousOn γ (Icc α β) ∧ InjOn γ (Icc α β) ∧ d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ det2 d₁ d₂ ≠ 0 ∧
    ∃ c : ℝ, c ≠ 0 ∧ ∀ t ∈ Icc α β, det2 d₁ (γ t - p₁) * det2 d₂ (γ t - p₂) = c

/-- **The boundary of a smoothed polygon** (Remark 8.3.3; Theorem 16.3.1 and its gloss, TeX
12789–12804): the boundary of `K` is the union of finitely many straight edges `[a_k, b_k]`
(`a_k ≠ b_k`) and finitely many hyperbolic arcs `γ_l([α_l, β_l])`; each hyperbolic arc has as
asymptotes the lines extending two of the edges ("hyperbolic arcs, whose asymptotes are lines
extending the straight edge segments of the boundary") and begins and ends on edges (the boundary
alternates between edges and hyperbolic arcs: each hyperbolic arc rounds a corner between two
edges). -/
def IsSmoothedPolygonBoundary (K : Set (Fin 2 → ℝ)) : Prop :=
  ∃ (m n : ℕ) (a b : Fin m → Fin 2 → ℝ) (γ : Fin n → ℝ → Fin 2 → ℝ) (α β : Fin n → ℝ),
    (∀ k, a k ≠ b k) ∧
    (∀ l, ∃ k₁ k₂, IsHyperbolicArc (γ l) (α l) (β l) (a k₁) (b k₁ - a k₁) (a k₂) (b k₂ - a k₂)) ∧
    (∀ l, γ l (α l) ∈ ⋃ k, segment ℝ (a k) (b k)) ∧
    (∀ l, γ l (β l) ∈ ⋃ k, segment ℝ (a k) (b k)) ∧
    frontier K = (⋃ k, segment ℝ (a k) (b k)) ∪ ⋃ l, γ l '' Icc (α l) (β l)

/-- **A finite-sided smoothed polygon with rounded hyperbolic arcs at each corner, of the sort
described by Reinhardt and Mahler** (Theorem 16.3.1, TeX 12792–12804: "the minimizer `K_min` has
no corners and the boundary alternates between straight edge segments and hyperbolic arcs, whose
asymptotes are lines extending the straight edge segments of the boundary"): a centrally
symmetric convex disk with a unique support line at every boundary point (no corners,
Lemma 2.2.5's form) whose boundary is that of a smoothed polygon (`IsSmoothedPolygonBoundary`). -/
def IsSmoothedPolygon (K : Set (Fin 2 → ℝ)) : Prop :=
  IsCCSDisk K ∧ (∀ x ∈ frontier K, ∃! ℓ, IsSupportLine K ℓ ∧ x ∈ ℓ) ∧
    IsSmoothedPolygonBoundary K

/-- **Constant control at a vertex: two of the curves move along straight lines** (§7.2, TeX
5612–5622: "two of the state-dependent curvatures `κ_j, κ_{j+1}` are zero. Thus the corresponding
trajectories `σ_i(t) = g(t) s_i*`, `i = 2j, 2j + 2`, move along straight lines"; the discussion that
Lemma 7.2.1 records, whose half-plane part is `lemma7_2_1`). If the control of a state trajectory
is the vertex `e_{i+1}` almost everywhere on `[c, d]`, then for every `m ≠ i` the curve
`σ_{2m} = g s_{2m}*` moves along a straight line on `[c, d]`.

Proof: along the trajectory the state-dependent curvature `κ_m = det(s_{2m}*, (X + X⁻¹X') s_{2m}*)`
(`stateCurvature`) is a positive multiple of `u_m` (`X' = [P, X]` and `controlMatrix_spec`;
explicitly `κ_m = 6 y u_m / D` with `D = -3y⟨X, Z_u⟩ > 0`, checked with sympy), so it vanishes
a.e. on `[c, d]`; `det(σ', σ'') = det g · det X · κ_m = κ_m` with `σ' = gXs`, `σ'' = g(X² + X')s`
(a.e.); a `C¹` curve with nonvanishing velocity (`det(s, Xs) > 0`, star condition) and
`det(σ', σ'') = 0` a.e. has a velocity of constant direction, hence lies on a line. Expected size:
150–300 lines. -/
theorem l3st_straight_of_vertexControl {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ T)
    {i : Fin 3} (hu : ∀ᵐ t, t ∈ Ioo c d → u t = vertex i) {m : Fin 3} (hm : m ≠ i) :
    ∃ p v : Fin 2 → ℝ, v ≠ 0 ∧
      ∀ t ∈ Icc c d, det2 v (g t *ᵥ sixthRoot (2 * (m.val : ZMod 6)) - p) = 0 := by
  sorry

/-- **A bang-bang trajectory with finitely many switches bounds a smoothed polygon** (the content
of Remark 8.3.3 and the first sentence of the proof of Theorem 16.3.1, TeX 12808–12810). Let
`(g, X)` be an admissible trajectory of Problem 3.6.2 whose control is bang-bang with finitely many
switches on `[0, t_f]`, and `(K, σ)` the balanced pair attached to it (`σ_j = g s_j*` on
`[0, t_f]`, `σ_j(t + t_f) = σ_{j+1}(t)`). Then the boundary of `K` is that of a smoothed polygon.

Proof:
1. `∂K = ⋃_j σ_j([0, t_f])` (`IsBalancedPair`: `σ₀([0, 6t_f)) = ∂K`, and the shift).
2. On each switching interval `[τ_k, τ_{k+1}]` with control `e_{i+1}`, `σ_{2m}` and
   `σ_{2m+3} = -σ_{2m}` (`m ≠ i`) move along lines (`l3st_straight_of_vertexControl`), so their
   arcs are straight edges (a regular curve on a line is monotone along it); `σ_{2i}` and
   `σ_{2i+3}` move along hyperbolic arcs whose asymptotes are the lines of their two neighbours
   `σ_{2i ± 1}` (Lemma 3.1.8, `lemma3_1_8`, with `IsMultiCurve 1` from the balanced pair).
3. A curve `σ_j` is hyperbolic under exactly one vertex control, so at an interior switching time
   a hyperbolic arc is followed and preceded by an edge of the same curve. At `t_f` (and `0`) the
   arc of `σ_j` on `[τ_{N-1}, t_f]` continues as the arc of `σ_{j+1}` on `[0, τ₁]`; if both are
   hyperbolic they lie on the same hyperbola (the neighbouring straight arcs continue along the
   same lines, the curves being `C¹`, and the constant `c` is continuous) and are merged.
Expected size: 300–600 lines. -/
theorem l3st_isSmoothedPolygonBoundary_of_isFiniteBangBang {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsReinhardtAdmissible T u g X) (hbb : IsFiniteBangBang 0 T u)
    {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} (hKσ : IsBalancedPair K σ T)
    (hσ : ∀ j, ∀ t ∈ Icc 0 T, σ j t = g t *ᵥ sixthRoot j)
    (hshift : ∀ j t, σ j (t + T) = σ (j + 1) t) :
    IsSmoothedPolygonBoundary K := by
  sorry

/-- **Remark 8.3.3** (`rem:smoothed-polygon`, label of this formalization; unlabelled, TeX
7610–7616). A trajectory `(g, X)` that is a Pontryagin extremal and edge extremal and does not meet
the singular locus `𝒮_sing` defines a balanced disk `K(g, X)` whose boundary is a smoothed polygon,
consisting of finitely many straight edges and hyperbolic arcs. The disk `K(g, X)` is a hypothesis
(the balanced pair with `σ_j = g s_j*`; see the module docstring for its existence).

Proof: Theorem 8.3.2 (`theorem8_3_2`, on `[0, t_f]`, with
`l3st_isExtremalOn_of_isPontryaginExtremal`) makes the control bang-bang with finitely many
switches; then `l3st_isSmoothedPolygonBoundary_of_isFiniteBangBang` (the discussion of §7.2 with
Lemma 3.1.8). Expected size: 20–40 lines. -/
theorem remark8_3_3 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) (hedge : IsEdgeExtremalOn 0 T u X)
    (hS : ∀ t ∈ Icc 0 T, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus) {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} (hKσ : IsBalancedPair K σ T)
    (hσ : ∀ j, ∀ t ∈ Icc 0 T, σ j t = g t *ᵥ sixthRoot j)
    (hshift : ∀ j t, σ j (t + T) = σ (j + 1) t) :
    IsSmoothedPolygonBoundary K := by
  sorry

/-- Being the boundary of a smoothed polygon is invariant under invertible linear maps: lines go to
lines, segments to segments, and `det(A⁻¹d, A⁻¹(x - p)) = det(A⁻¹) det(d, x - p)`, so hyperbolic
arcs with asymptotes go to hyperbolic arcs with the image asymptotes (constant `c det(A⁻¹)²`); the
frontier of the image is the image of the frontier (a linear homeomorphism). Expected size:
80–150 lines. -/
theorem l3st_isSmoothedPolygonBoundary_of_image {K : Set (Fin 2 → ℝ)} {A : Mat2} (hA : A.det ≠ 0)
    (h : IsSmoothedPolygonBoundary ((fun v ↦ A *ᵥ v) '' K)) : IsSmoothedPolygonBoundary K := by
  sorry

end SmoothedPolygons
