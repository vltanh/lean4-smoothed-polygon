module

public import SmoothedPolygons.Ch13.Jacobian
public import Basic.Dynamics.LinearizedStability

/-!
# Chapter 13: Lemma 13.5.5 (stability of `q_out`, instability of `q_in`)

Lemma 13.5.5 of Hales–Vajjha, *Packings of Smoothed Polygons* (`lem:eigenvalues`,
TeX 11433–11453): on `Ξ_{𝒲,0}/V_T`, `q_out` is an asymptotically stable fixed point of `F_ang`
and `q_in` is unstable. Chapter 16 relies on it (Theorem 16.1.1, TeX 12596–12598). Chapter 14
(Theorem 14.3.3, TeX 11911–11917) needs more than this lemma: the linearization of `F` at `q_out`
on the exceptional divisor (three eigenvalues of modulus `< 1`; the bound `0.1` is quoted at
TeX 11961), transferred to its own coordinates. It relies on the Jacobian lemmas of
`SmoothedPolygons/Ch13/Jacobian.lean` (`l4st_hasFDerivAt_chartMap`,
`l4st_charpoly_jacobianOut_roots`) with the normalization map `chartOf`
(`l4f_chartOf_chartCart`, `l4f_chartMap_eventuallyEq_chartOf`, `l4f_contDiffAt_chartOf`), not on
`lemma13_5_5`.

The book's proof, and its formalization:
1. "It suffices to show that `q_out` is asymptotically stable. … An open neighborhood of `q_out`
   in `Ξ_{𝒲,0}/V_T` is diffeomorphic to an open subset of `ℝ³`. An explicit calculation of the
   eigenvalues of the Jacobian matrix in terms of local coordinates centered at `q_out` gives the
   result": the chart and the certified Jacobian (`SmoothedPolygons/Ch13/Jacobian.lean`:
   `l4st_exists_chart`, `l4st_chartMap_xOut`, `l4st_hasFDerivAt_chartMap`,
   `l4st_charpoly_jacobianOut`, `l4st_charpoly_jacobianOut_roots`), linearized stability for maps
   (`Function.isAsymptoticallyStable_of_hasFDerivAt`, `Basic/Dynamics/LinearizedStability.lean`;
   the eigenvalues of `Matrix.toLin' M` are the roots of `M.charpoly`, `LinearMap.charpoly_toLin'`)
   and the transfer through the chart (`Function.IsAsymptoticallyStable.of_conj`).
2. "The second assertion follows from the first, because `q_in` is obtained by time reversal from
   `q_out`": `τ ∘ F_ang` is an involution near `q_out` and near `q_in`
   (`l4st_tauZero_poincareAngZero_involutive`, from `F(τ F(z)) = τ(z)` at genuine switching points,
   `l4st_poincare_tau_poincare`, Lemmas 13.2.3 and 13.2.5; not spelled out in the book, inventory
   gap 12), `τ(q_out) = q_in` (`l4st_tauQuot_qOut`), and an asymptotically stable fixed point is
   carried by such a time reversal to an unstable one
   (`Function.IsAsymptoticallyStable.isUnstable_of_involutive`; `Ξ_{𝒲,0}/V_T` is compact
   Hausdorff, `l4st_topology_XiWQuot`, and `F_ang` is continuous near `q_out`,
   `l4st_contDiffAt_chartMap`).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology

namespace TriFuller

/-- **Time reversal near the fixed points** (the formal content of "`q_in` is obtained by time
reversal from `q_out`", TeX 11441–11442): `τ ∘ F_ang` is an involution of `Ξ_{𝒲,0}/V_T` near
`q_out` and near `q_in`.

Proof route: near `q_out` (and near `q_in = τ q_out`) every point is a genuine switching point:
its first control is `ζ` and its most recent control is `ζ²`, the conjugate of the first control
`ζ` of its image by `τ` (Lemma 13.2.5), both by open lexicographic conditions (on the wall `𝒲₀`
the ties are broken by the sign of `Im z₂`). There `F(τ F(z)) = τ(z)`
(`l4st_poincare_tau_poincare`), which passes to the angular map on the quotient
(`l4st_ang_poincare_ang`, `τ (v ξ) = v̄ τ ξ`, `τ` commutes with the rescaling).

The same argument gives the identity on all of the big open cells of Chapter 15
(Definition `def:big:open`, TeX 12104–12110: the points with a representative `z₃ ∈ ℝ_{<0}`,
`Im z₂ ≠ 0`, where the first control is `ζ` and the most recent `ζ²` if `Im z₂ > 0`, and
conversely if `Im z₂ < 0`); it is stated here in the neighborhood form that Lemma 13.5.5 uses, and
the cell form belongs with the cells of Chapter 15. -/
theorem l4st_tauZero_poincareAngZero_involutive :
    (∀ᶠ x in 𝓝 qOut0, tauZero (poincareAngZero (tauZero (poincareAngZero x))) = x) ∧
      ∀ᶠ x in 𝓝 qIn0, tauZero (poincareAngZero (tauZero (poincareAngZero x))) = x := by
  sorry

end TriFuller

open TriFuller

/-- **Lemma 13.5.5** (`lem:eigenvalues`, TeX 11433–11453). Restrict `F_ang` to the subset
`Ξ_{𝒲,0}/V_T` of `Ξ_𝒲/V_T` on which the Hamiltonian vanishes. On that subset, the fixed point
`q_out` is an asymptotically stable equilibrium, and the fixed point `q_in` is unstable.

Proof: the book's, in the module docstring. The book's numerical eigenvalue computation
("Numerically, the three eigenvalues have absolute value less than `0.1`. The calculations were
made in Mathematica.") is replaced by the exact Jacobian in `ℚ(√3, r_scale)` and a certified bound
on the roots of its characteristic polynomial (`l4st_charpoly_jacobianOut_roots`). -/
theorem lemma13_5_5 :
    Function.IsAsymptoticallyStable poincareAngZero qOut0 ∧
      Function.IsUnstable poincareAngZero qIn0 := by
  sorry

end SmoothedPolygons
