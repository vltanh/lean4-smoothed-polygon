module

public import SmoothedPolygons.Ch14.AnalyticExtension
import SmoothedPolygons.Ch7.Isolated.VertexFlow
import SmoothedPolygons.Ch7.Isolated.Return

/-!
# Chapter 14, N4: the Poisson brackets of the vertex Hamiltonians (Lemma 2.3)

Part of the formalization's proof of N4 (`UnstableCurveLeavesStarDomain`, Figure 14.2) without
computer assistance. **Departure from the paper**, by the user's decision: the book reads N4 off a
computed figure (Figure 14.2, TeX 11951–11991; REPORT.md E88); the formalization proves it from
the exact structure of the Reinhardt flow along an `e₂`-arc and an invariant region (see
`SmoothedPolygons/Ch14/ArcParams.lean`, and `SmoothedPolygons/Ch14/ArcRegionInvariant.lean` for
the numbering of the steps).

Lemma 2.3: for the vertex vector fields `V_u` (`iso_extremalField (vertex u)`, `λ_cost = -1`) and
the vertex Hamiltonians `H_u` (`phaseHam · (vertex u)`), `L_{V_u} H_u = 0` and
`L_{V_u} H_v + L_{V_v} H_u = 0`: the Hamiltonian structure of the maximum principle. Used for
`SwitchEntersE2` in Proposition 3.4 (1) (`SmoothedPolygons/Ch14/ArcConditions.lean`: the slope of
`H(e₃) - H(e₂)` along the `e₃`-flow is minus the slope of `χ₂₃` along the `e₂`-flow). It would also
give the slope of `p_new` in Theorem 2.1 (`phaseHamSlope_chi21`: the slope of `χ₂₁` is the same
along the `e₁`- and the `e₂`-flow), but that is not needed: `p_new` follows from the closed form
INV (1.4) of `Λ₁(t)` (`arcP_adRinv_vertexFlow`, `SmoothedPolygons/Ch14/ArcPoincareMap.lean`, route
there, "Simpler route for steps 5–6"). So only `phaseHamSlope_e3` (with
`hasDerivAt_phaseHam_vertexFlow`) is on the path to N4.

**A proof by hand.** Lemma 2.3 was first checked only symbolically (sympy `simplify` on generic
traceless matrices). It has a short proof by hand (also checked numerically on arbitrary, not
traceless, matrices): with `P_u = Z_u/⟨X, Z_u⟩` (`controlP`), `Λ̂ = Λ₁ + (3/2) J`,
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
   for the trace form, private in VertexFlowAnalytic.lean, is proved again here
   (`hasDerivAt_traceForm`: from `HasDerivAtEntrywise A A' t` and
   `HasDerivAtEntrywise B B' t`, `h := hA.mul hB`, then `(h 0 0).add (h 1 1)`, giving
   `HasDerivAt (fun s ↦ traceForm (A s) (B s)) (traceForm A' (B t) + traceForm (A t) B') t`).
2. `phaseHamSlope_eq`: with `X' = [P_u, X]`, `Λ₁' = [Λ₁, X]`,
   `Λ_R' = [P_u, Λ_R] - ⟨Λ_R, P_u⟩[P_u, X] - [Λ̂, X]` (`costateRHS (-1)`): `⟨Λ₁', X⟩ = 0`; the
   quotient rule gives `d(⟨Λ_R, Z_v⟩/⟨X, Z_v⟩) = ⟨Λ_R', P_v⟩ - ⟨Λ_R, P_v⟩⟨X', P_v⟩`; and the
   invariance `⟨[A, B], C⟩ = ⟨A, [B, C]⟩` of the trace form gives
   `⟨[P_u, Λ_R], P_v⟩ = -⟨Λ_R, [P_u, P_v]⟩`, `⟨[Λ̂, X], P_v⟩ = -⟨Λ̂, [P_v, X]⟩`,
   `⟨[P_u, X], P_v⟩ = -⟨X, [P_u, P_v]⟩`. Entrywise: `field_simp` (the denominators `⟨X, Z_u⟩`,
   `⟨X, Z_v⟩`), `ring`. The identity holds for **arbitrary** `2 × 2` matrices in place of the
   control matrices, so no `√3` arithmetic is needed: the proof generalizes `P_u` to an arbitrary
   matrix `P` (so `⟨X, Z_u⟩ ≠ 0` is not needed) and writes `Z_v = c Q` with `c = ⟨X, Z_v⟩`;
   after cancelling `c`, the identity is polynomial in `X, Λ₁, Λ_R, P, Q`
   (`phaseHamSlope_poly_identity`), checked entrywise by `ring`.
3. Lemma 2.3 from step 2: swapping `u, v` changes the sign of each of the three terms.

Also checked numerically, while the statements were written, against the literal flow at section
points and at arbitrary points; the proofs do not depend on these checks.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- The product rule for the trace form along entrywise-differentiable curves of matrices. -/
private lemma hasDerivAt_traceForm {A B : ℝ → Mat2} {A' B' : Mat2} {t : ℝ}
    (hA : Matrix.HasDerivAtEntrywise A A' t) (hB : Matrix.HasDerivAtEntrywise B B' t) :
    HasDerivAt (fun s ↦ traceForm (A s) (B s)) (traceForm A' (B t) + traceForm (A t) B') t := by
  have h := hA.mul hB
  have h2 := (h 0 0).add (h 1 1)
  simp only [Matrix.add_apply] at h2
  convert h2 using 1
  · funext s; simp [traceForm, Matrix.trace_fin_two]
  · simp [traceForm, Matrix.trace_fin_two]; ring

/-- The product rule for `s ↦ ⟨A(s), B⟩` with `B` constant. -/
private lemma hasDerivAt_traceForm_const {A : ℝ → Mat2} {A' : Mat2} {t : ℝ} (B : Mat2)
    (hA : Matrix.HasDerivAtEntrywise A A' t) :
    HasDerivAt (fun s ↦ traceForm (A s) B) (traceForm A' B) t := by
  have h := hasDerivAt_traceForm hA (Matrix.hasDerivAtEntrywise_const B t)
  simpa [traceForm] using h

/-- `⟨A, c • B⟩ = c ⟨A, B⟩`. -/
private lemma traceForm_smul_right (A B : Mat2) (c : ℝ) :
    traceForm A (c • B) = c * traceForm A B := by
  simp [traceForm, Matrix.trace_smul]

/-- The closed form of the Poisson bracket as a polynomial identity in arbitrary matrices `X`,
`Λ₁`, `Λ_R`, `P` (for `P_u`) and `Q` (for `P_v`), `Λ̂ = Λ₁ + (3/2) J`: with
`Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩[P, X] - [Λ̂, X]`,
`⟨[Λ₁, X], X⟩ + ⟨Λ̂, [P, X]⟩ - (⟨Λ_R', Q⟩ - ⟨Λ_R, Q⟩⟨[P, X], Q⟩)` equals
`⟨Λ̂, [P - Q, X]⟩ + ⟨Λ_R, [P, Q]⟩ - (⟨Λ_R, P⟩ + ⟨Λ_R, Q⟩)⟨X, [P, Q]⟩` (the invariance
`⟨[A, B], C⟩ = ⟨A, [B, C]⟩` of the trace form; checked entrywise). -/
private lemma phaseHamSlope_poly_identity (X L₁ LR P Q : Mat2) :
    traceForm (L₁ * X - X * L₁) X + traceForm (L₁ + (3 / 2 : ℝ) • J) (P * X - X * P) -
        (traceForm ((P * LR - LR * P) - traceForm LR P • (P * X - X * P) +
            ((-L₁ + (3 / 2 * -1 : ℝ) • J) * X - X * (-L₁ + (3 / 2 * -1 : ℝ) • J))) Q -
          traceForm LR Q * traceForm (P * X - X * P) Q) =
      traceForm (L₁ + (3 / 2 : ℝ) • J) ((P - Q) * X - X * (P - Q)) +
        traceForm LR (P * Q - Q * P) -
        (traceForm LR P + traceForm LR Q) * traceForm X (P * Q - Q * P) := by
  simp only [traceForm, J, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

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
  obtain ⟨h1, h2, h3, -⟩ := iso_vertexFlow_solution u q t
  have hA := hasDerivAt_traceForm (h2.add_const ((3 / 2 : ℝ) • J)) h1
  have hN := hasDerivAt_traceForm_const (controlMatrix (vertex v)) h3
  have hD := hasDerivAt_traceForm_const (controlMatrix (vertex v)) h1
  convert hA.sub (hN.div hD hv) using 1
  · funext s
    simp only [phaseHam, hamiltonian, Pi.sub_apply, Pi.div_apply]
    rw [show (3 / 2 * -1 : ℝ) = -(3 / 2) by norm_num, neg_smul, sub_neg_eq_add]
  · rfl

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
  have hQ : controlP (vertex v) q.1 =
      (traceForm q.1 (controlMatrix (vertex v)))⁻¹ • controlMatrix (vertex v) := by
    rw [controlP, traceForm, Matrix.trace_mul_comm, ← traceForm]
  rw [hQ]
  unfold phaseHamSlope iso_extremalField costateRHS
  dsimp only
  generalize controlP (vertex u) q.1 = P
  generalize controlMatrix (vertex v) = Z at hv ⊢
  generalize hc : traceForm q.1 Z = c at hv ⊢
  obtain ⟨Q, rfl⟩ : ∃ Q, Z = c • Q := ⟨c⁻¹ • Z, by rw [smul_smul, mul_inv_cancel₀ hv, one_smul]⟩
  rw [smul_smul, inv_mul_cancel₀ hv, one_smul, ← phaseHamSlope_poly_identity]
  simp only [traceForm_smul_right]
  field_simp

/-- **Lemma 2.3**: `L_{V_u} H_u = 0` (`H_u` is conserved along its own flow). -/
theorem phaseHamSlope_self (u : Fin 3) (q : iso_PhasePt)
    (hu : traceForm q.1 (controlMatrix (vertex u)) ≠ 0) : phaseHamSlope u u q = 0 := by
  rw [phaseHamSlope_eq u u q hu]
  simp [traceForm]

/-- **Lemma 2.3**: `L_{V_u} H_v + L_{V_v} H_u = 0` (`{H_v, H_u} = -{H_u, H_v}`). -/
theorem phaseHamSlope_add_swap (u v : Fin 3) (q : iso_PhasePt)
    (hu : traceForm q.1 (controlMatrix (vertex u)) ≠ 0)
    (hv : traceForm q.1 (controlMatrix (vertex v)) ≠ 0) :
    phaseHamSlope u v q + phaseHamSlope v u q = 0 := by
  rw [phaseHamSlope_eq u v q hv, phaseHamSlope_eq v u q hu]
  generalize controlP (vertex u) q.1 = P
  generalize controlP (vertex v) q.1 = Q
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **Lemma 2.3, consequence** (Theorem 2.1, `p_new`): the slope of `χ₂₁ = H(e₂) - H(e₁)` is the
same along the `e₂`-field and along the `e₁`-field. -/
theorem phaseHamSlope_chi21 (q : iso_PhasePt)
    (h0 : traceForm q.1 (controlMatrix (vertex 0)) ≠ 0)
    (h1 : traceForm q.1 (controlMatrix (vertex 1)) ≠ 0) :
    phaseHamSlope 1 1 q - phaseHamSlope 1 0 q = phaseHamSlope 0 1 q - phaseHamSlope 0 0 q := by
  rw [phaseHamSlope_self 1 q h1, phaseHamSlope_self 0 q h0]
  linarith [phaseHamSlope_add_swap 0 1 q h0 h1]

/-- **Lemma 2.3, consequence** (Proposition 3.4 (1)): the slope of `H(e₃) - H(e₂)` along the
`e₃`-field is minus the slope of `χ₂₃ = H(e₂) - H(e₃)` along the `e₂`-field. -/
theorem phaseHamSlope_e3 (q : iso_PhasePt)
    (h1 : traceForm q.1 (controlMatrix (vertex 1)) ≠ 0)
    (h2 : traceForm q.1 (controlMatrix (vertex 2)) ≠ 0) :
    phaseHamSlope 2 2 q - phaseHamSlope 2 1 q = -(phaseHamSlope 1 1 q - phaseHamSlope 1 2 q) := by
  rw [phaseHamSlope_self 2 q h2, phaseHamSlope_self 1 q h1]
  linarith [phaseHamSlope_add_swap 1 2 q h1 h2]

end SmoothedPolygons
