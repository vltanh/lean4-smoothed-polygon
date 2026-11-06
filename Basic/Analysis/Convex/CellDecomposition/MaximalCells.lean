module

public import Basic.Analysis.Convex.CellDecomposition.Defs

/-!
# (A) A maximal family of cells

Part of the proof of the cell lemma (`Basic.Analysis.Convex.CellDecomposition`).
-/

@[expose] public section

open MeasureTheory Set

namespace PlaneConvex

/-! ### (A) A maximal family of cells -/

/-- **(A) A maximal family of cells exists.** Let `Q = halfPlanesInter b d` be bounded and
`K i ⊆ Q` (`i < n`) non-overlapping compact convex sets with nonempty interiors. Then there are
convex polygons `C i` with `K i ⊆ C i ⊆ Q`, non-overlapping, of maximal total area among all
non-overlapping families of convex sets `K i ⊆ C' i ⊆ Q` (`IsMaximalCells`).

Argument. (1) *Separation.* For `i ≠ j`, `interior (K i)` and `interior (K j)` are disjoint open
convex sets, so a line separates them (`geometric_hahn_banach_open_open`), and since
`K i = closure (interior (K i))` (`Convex.closure_interior_eq_closure_of_nonempty_interior`) it
separates `K i` and `K j`: there are `u ≠ 0` and `t` with `⟨u, x⟩ ≤ t` on `K i` and `≥ t` on `K j`.
More generally any two convex sets with nonempty disjoint interiors are separated by a line.
(2) *Parametrization.* For each ordered pair `i ≠ j` take `(u_ij, t_ij)` with
`u_ji = -u_ij`, `t_ji = -t_ij`, `|u_ij| = 1`, `sup_{K i} ⟨u_ij, ·⟩ ≤ t_ij ≤ inf_{K j} ⟨u_ij, ·⟩`;
this is a compact set `Λ` of parameters (`t_ij` is bounded since `Q` is). The cells
`P_i(λ) = Q ∩ ⋂_{j ≠ i} {⟨u_ij, x⟩ ≤ t_ij}` are convex polygons (bounded, `⊇ K i`), contain
`K i`, and are non-overlapping (`P_i ⊆ {⟨u_ij, ·⟩ ≤ t_ij}`, `P_j ⊆ {⟨u_ij, ·⟩ ≥ t_ij}`).
(3) *Continuity.* `λ ↦ ∑ |P_i(λ)|` is continuous on `Λ`: the indicator of `P_i(λ)` converges
pointwise to that of `P_i(λ₀)` off the finitely many lines `⟨u_ij, x⟩ = t_ij` of `λ₀` (a null set),
and is dominated by the indicator of `Q` (dominated convergence,
`tendsto_lintegral_of_dominated_convergence`). So the maximum is attained
(`IsCompact.exists_isMaxOn`) at some `λ₀`; put `C i = P_i(λ₀)`.
(4) *Maximality among all convex families.* If `C' i` are convex, non-overlapping, with
`K i ⊆ C' i ⊆ Q`, then each `C' i` has nonempty interior, so `C' i` and `C' j` are separated by a
line as in (1); normalizing gives `λ ∈ Λ` with `C' i ⊆ P_i(λ)`, hence
`∑ |C' i| ≤ ∑ |P_i(λ)| ≤ ∑ |C i|`.

Estimated size: 500–800 lines. -/
theorem exists_isMaximalCells {m n : ℕ} (b : Fin m → Fin 2 → ℝ) (d : Fin m → ℝ)
    (hQ : Bornology.IsBounded (halfPlanesInter b d)) (K : Fin n → Set (Fin 2 → ℝ))
    (hK : ∀ i, Convex ℝ (K i) ∧ IsCompact (K i) ∧ (interior (K i)).Nonempty)
    (hKQ : ∀ i, K i ⊆ halfPlanesInter b d) (hdisj : NonOverlapping K) :
    ∃ C : Fin n → Set (Fin 2 → ℝ), (∀ i, IsConvexPolygon (C i)) ∧ (∀ i, K i ⊆ C i) ∧
      (∀ i, C i ⊆ halfPlanesInter b d) ∧ NonOverlapping C ∧
      IsMaximalCells (halfPlanesInter b d) K C := by
  sorry

end PlaneConvex
