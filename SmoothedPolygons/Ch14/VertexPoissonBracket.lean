module

public import SmoothedPolygons.Ch14.AnalyticExtension
import SmoothedPolygons.Ch7.Isolated.VertexFlow
import SmoothedPolygons.Ch7.Isolated.Return

/-!
# Chapter 14, N4: the Poisson brackets of the vertex Hamiltonians (Lemma 2.3)

`notes/n4/proof.md` Lemma 2.3: for the vertex vector fields `V_u` (`iso_extremalField (vertex u)`,
`λ_cost = -1`) and the vertex Hamiltonians `H_u` (`phaseHam · (vertex u)`), `L_{V_u} H_u = 0` and
`L_{V_u} H_v + L_{V_v} H_u = 0`: the Hamiltonian structure of the maximum principle. Used for
`SwitchEntersE2` in Proposition 3.4 (1) (`SmoothedPolygons/Ch14/ArcConditions.lean`: the slope of
`H(e₃) - H(e₂)` along the `e₃`-flow is minus the slope of `χ₂₃` along the `e₂`-flow). proof.md
also uses it for the slope of `p_new` in Theorem 2.1 (`phaseHamSlope_chi21`: the slope of `χ₂₁`
is the same along the `e₁`- and the `e₂`-flow), but that is no longer needed: `p_new` follows
from the closed form (1.4) of `Λ₁(t)` (`arcP_adRinv_vertexFlow`,
`SmoothedPolygons/Ch14/ArcPoincareMap.lean`, route there, "Simpler route for steps 5–6"). So only
`phaseHamSlope_e3` (with `hasDerivAt_phaseHam_vertexFlow`) is on the critical path of N4. Part
of the reduction of N4 to (INV) (`ArcRegionInvariant`).

**Departure from the paper.** The book computes the unstable curve numerically (Figure 14.2,
TeX 11951–11991); the formalization proves N4 from (INV) by the exact structure of the arcs (see
`SmoothedPolygons/Ch14/ArcParams.lean`).

**Status in the research notes.** The research checked Lemma 2.3 only with sympy `simplify` on
generic traceless matrices (`notes/n4/pb.py`). It has a short proof by hand, found while writing
these statements (and checked numerically on arbitrary, not traceless, matrices,
`notes/n4f/check_pb.py`): with `P_u = Z_u/⟨X, Z_u⟩` (`controlP`), `Λ̂ = Λ₁ + (3/2) J`,
`[A, B] = AB - BA`,

  `L_{V_u} H_v = ⟨Λ̂, [P_u - P_v, X]⟩ + ⟨Λ_R, [P_u, P_v]⟩`
  `  - (⟨Λ_R, P_u⟩ + ⟨Λ_R, P_v⟩)⟨X, [P_u, P_v]⟩`

(`phaseHamSlope_eq`), which is visibly antisymmetric in `(u, v)` and vanishes for `u = v`. No
trace condition is needed, only `⟨X, Z_u⟩ ≠ 0` and `⟨X, Z_v⟩ ≠ 0`.

## Statements

* `phaseHamSlope u v q`: `L_{V_u} H_v` at `q`, the directional derivative of `q ↦ H_v(q)` along
  `V_u(q)`, written out (`H_v = ⟨Λ̂, X⟩ - ⟨Λ_R, Z_v⟩/⟨X, Z_v⟩`).
* `hasDerivAt_phaseHam_vertexFlow`: along the `e_u`-flow, `d/dt H_v = L_{V_u} H_v`.
* `phaseHamSlope_eq`: the closed form above.
* **Lemma 2.3**: `phaseHamSlope_self`, `phaseHamSlope_add_swap`; the two consequences
  `phaseHamSlope_chi21` (the slope of `χ₂₁ = H₂ - H₁` along `V₂` equals its slope along `V₁`) and
  `phaseHamSlope_e3` (`L_{V₃}(H₃ - H₂) = -L_{V₂}(H₂ - H₃)`).
* Lemma 2.3, last sentence (`⟨X, Λ_R⟩` and `det Λ₁` are constant along every vertex flow): these
  are `traceForm_vertexFlow` and the determinant lemma before it in
  `SmoothedPolygons/Ch14/VertexFlowAnalytic.lean`; they are not restated.

## Proofs (the route)

1. `hasDerivAt_phaseHam_vertexFlow`: `iso_vertexFlow_solution` gives the derivative of the flow,
   which is `iso_extremalField (vertex u)` at the current point; then the product and quotient
   rules entrywise (as in `irt_chi_hasDerivAt`, `SmoothedPolygons/Ch7/Isolated/Return.lean`, and
   `hamiltonian_vertexFlow`, `SmoothedPolygons/Ch14/VertexFlowAnalytic.lean`). The product rule
   for the trace form there, `l6d_traceForm_hasDerivAt` (VertexFlowAnalytic.lean:347), is
   **private**: reprove it here as a private helper (about three lines: from
   `HasDerivAtEntrywise A A' t` and `HasDerivAtEntrywise B B' t`, `h := hA.mul hB`, then
   `(h 0 0).add (h 1 1)` and `simp [traceForm, Matrix.trace_fin_two]`, `ring`, giving
   `HasDerivAt (fun s ↦ traceForm (A s) (B s)) (traceForm A' (B t) + traceForm (A t) B') t`).
2. `phaseHamSlope_eq`: with `X' = [P_u, X]`, `Λ₁' = [Λ₁, X]`,
   `Λ_R' = [P_u, Λ_R] - ⟨Λ_R, P_u⟩[P_u, X] - [Λ̂, X]` (`costateRHS (-1)`): `⟨Λ₁', X⟩ = 0`; the
   quotient rule gives `d(⟨Λ_R, Z_v⟩/⟨X, Z_v⟩) = ⟨Λ_R', P_v⟩ - ⟨Λ_R, P_v⟩⟨X', P_v⟩`; and the
   invariance `⟨[A, B], C⟩ = ⟨A, [B, C]⟩` of the trace form gives
   `⟨[P_u, Λ_R], P_v⟩ = -⟨Λ_R, [P_u, P_v]⟩`, `⟨[Λ̂, X], P_v⟩ = -⟨Λ̂, [P_v, X]⟩`,
   `⟨[P_u, X], P_v⟩ = -⟨X, [P_u, P_v]⟩`. Entrywise: `field_simp` (the denominators `⟨X, Z_u⟩`,
   `⟨X, Z_v⟩`), `ring`. The identity holds for **arbitrary** `2 × 2` matrices `Z_u`, `Z_v` in place
   of the control matrices (the review, `notes/n4rev/t12_pb_generic.py`, sympy): so the proof can
   generalize `controlMatrix (vertex u)`, `controlMatrix (vertex v)` to variables `Z`, `W` (with
   `⟨X, Z⟩ ≠ 0`, `⟨X, W⟩ ≠ 0`) and needs no `√3` arithmetic.
3. Lemma 2.3 from step 2: swapping `u, v` changes the sign of each of the three terms.

Checked numerically against the literal flow (`notes/n4f/check2.py` at section points,
`notes/n4f/check_pb.py` at arbitrary points).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- **`L_{V_u} H_v`**: the derivative of `H_v = ⟨Λ₁ + (3/2) J, X⟩ - ⟨Λ_R, Z_v⟩/⟨X, Z_v⟩`
(`phaseHam · (vertex v)`) along the vector field `V_u = iso_extremalField (vertex u)` of the
`e_u`-flow, at `q`. -/
noncomputable def phaseHamSlope (u v : Fin 3) (q : iso_PhasePt) : ℝ :=
  traceForm (iso_extremalField (vertex u) q).2.1 q.1 +
      traceForm (q.2.1 + (3 / 2 : ℝ) • J) (iso_extremalField (vertex u) q).1 -
    (traceForm (iso_extremalField (vertex u) q).2.2 (controlMatrix (vertex v)) *
          traceForm q.1 (controlMatrix (vertex v)) -
        traceForm q.2.2 (controlMatrix (vertex v)) *
          traceForm (iso_extremalField (vertex u) q).1 (controlMatrix (vertex v))) /
      traceForm q.1 (controlMatrix (vertex v)) ^ 2

/-- Along the `e_u`-flow, `d/dt H_v = L_{V_u} H_v` wherever `⟨X, Z_v⟩ ≠ 0`. -/
theorem hasDerivAt_phaseHam_vertexFlow (u v : Fin 3) (q : iso_PhasePt) (t : ℝ)
    (hv : traceForm (iso_vertexFlow u q t).1 (controlMatrix (vertex v)) ≠ 0) :
    HasDerivAt (fun s ↦ phaseHam (iso_vertexFlow u q s) (vertex v))
      (phaseHamSlope u v (iso_vertexFlow u q t)) t := by
  sorry

/-- **The Poisson bracket in closed form**: with `P_w = controlP (vertex w) X`,
`L_{V_u} H_v = ⟨Λ̂, [P_u - P_v, X]⟩ + ⟨Λ_R, [P_u, P_v]⟩ -
(⟨Λ_R, P_u⟩ + ⟨Λ_R, P_v⟩)⟨X, [P_u, P_v]⟩`. -/
theorem phaseHamSlope_eq (u v : Fin 3) (q : iso_PhasePt)
    (hv : traceForm q.1 (controlMatrix (vertex v)) ≠ 0) :
    phaseHamSlope u v q =
      traceForm (q.2.1 + (3 / 2 : ℝ) • J)
          ((controlP (vertex u) q.1 - controlP (vertex v) q.1) * q.1 -
            q.1 * (controlP (vertex u) q.1 - controlP (vertex v) q.1)) +
        traceForm q.2.2 (controlP (vertex u) q.1 * controlP (vertex v) q.1 -
          controlP (vertex v) q.1 * controlP (vertex u) q.1) -
        (traceForm q.2.2 (controlP (vertex u) q.1) + traceForm q.2.2 (controlP (vertex v) q.1)) *
          traceForm q.1 (controlP (vertex u) q.1 * controlP (vertex v) q.1 -
            controlP (vertex v) q.1 * controlP (vertex u) q.1) := by
  sorry

/-- **Lemma 2.3**: `L_{V_u} H_u = 0` (`H_u` is conserved along its own flow). -/
theorem phaseHamSlope_self (u : Fin 3) (q : iso_PhasePt)
    (hu : traceForm q.1 (controlMatrix (vertex u)) ≠ 0) : phaseHamSlope u u q = 0 := by
  sorry

/-- **Lemma 2.3**: `L_{V_u} H_v + L_{V_v} H_u = 0` (`{H_v, H_u} = -{H_u, H_v}`). -/
theorem phaseHamSlope_add_swap (u v : Fin 3) (q : iso_PhasePt)
    (hu : traceForm q.1 (controlMatrix (vertex u)) ≠ 0)
    (hv : traceForm q.1 (controlMatrix (vertex v)) ≠ 0) :
    phaseHamSlope u v q + phaseHamSlope v u q = 0 := by
  sorry

/-- **Lemma 2.3, consequence** (Theorem 2.1, `p_new`): the slope of `χ₂₁ = H(e₂) - H(e₁)` is the
same along the `e₂`-field and along the `e₁`-field. -/
theorem phaseHamSlope_chi21 (q : iso_PhasePt)
    (h0 : traceForm q.1 (controlMatrix (vertex 0)) ≠ 0)
    (h1 : traceForm q.1 (controlMatrix (vertex 1)) ≠ 0) :
    phaseHamSlope 1 1 q - phaseHamSlope 1 0 q = phaseHamSlope 0 1 q - phaseHamSlope 0 0 q := by
  sorry

/-- **Lemma 2.3, consequence** (Proposition 3.4 (1)): the slope of `H(e₃) - H(e₂)` along the
`e₃`-field is minus the slope of `χ₂₃ = H(e₂) - H(e₃)` along the `e₂`-field. -/
theorem phaseHamSlope_e3 (q : iso_PhasePt)
    (h1 : traceForm q.1 (controlMatrix (vertex 1)) ≠ 0)
    (h2 : traceForm q.1 (controlMatrix (vertex 2)) ≠ 0) :
    phaseHamSlope 2 2 q - phaseHamSlope 2 1 q = -(phaseHamSlope 1 1 q - phaseHamSlope 1 2 q) := by
  sorry

end SmoothedPolygons
