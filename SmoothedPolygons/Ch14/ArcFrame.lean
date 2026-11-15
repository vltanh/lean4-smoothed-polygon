module

public import SmoothedPolygons.Ch14.AnalyticExtension
public import SmoothedPolygons.Ch14.ArcParams
import SmoothedPolygons.Ch7.Isolated.VertexFlow

/-!
# Chapter 14, N4: the eigenframe of an `e₂`-arc and the state along it (Proposition 1.1)

Part of the formalization's proof of N4 (`UnstableCurveLeavesStarDomain`, Figure 14.2) without
computer assistance. **Departure from the paper**, by the user's decision: the book reads N4 off a
computed figure (Figure 14.2, TeX 11951–11991; REPORT.md E88); the formalization proves it from
the exact structure of the Reinhardt flow along an `e₂`-arc and an invariant region (see
`SmoothedPolygons/Ch14/ArcParams.lean`, and `SmoothedPolygons/Ch14/ArcRegionInvariant.lean` for
the numbering of the steps). This file is its first part, §1.1–§1.2: the frame in which
`P = Z_{e₂}/⟨Z_{e₂}, X₀⟩` is diagonal, the star functions in it, and the state `X(t)` of the
`e₂`-flow (`iso_vfX 1`) in closed form.

## Vocabulary

* The frame (§1.1): `S = [[1, 1], [0, √3]]` (`arcFrameS`), `H = diag(1, -1)`, `E = e₁₂`,
  `F = e₂₁`; a traceless matrix is `S (h H + e E + f F) S⁻¹ = ofFrame h e f`, with components
  `frameH`, `frameE`, `frameF`. In the frame `⟨M, N⟩ = 2 m_h n_h + m_e n_f + m_f n_e`,
  `[H, E] = 2E`, `[H, F] = -2F`, `[E, F] = H`, and (1.2):
  `Z_{e₁} = (F - H)/√3`, `Z_{e₂} = H/√3`, `Z_{e₃} = -(H + 4E)/√3`, `J = (-H - 4E + F)/√3`.
* (1.1): for traceless `X`, `⟨X, Z_{e₁}⟩ = -(2/√3) ρ₂`, `⟨X, Z_{e₂}⟩ = -(2/√3) ρ₁`,
  `⟨X, Z_{e₃}⟩ = -(2/√3) ρ₀`, `Z_{e₁} + Z_{e₂} + Z_{e₃} = J`, `ρ₀ρ₁ + ρ₁ρ₂ + ρ₂ρ₀ = det X`.
* The cleared switching numerators `N_ij = ⟨Λ_R, Z_j⟩⟨X, Z_i⟩ - ⟨Λ_R, Z_i⟩⟨X, Z_j⟩ =
  χ_ij ⟨X, Z_i⟩⟨X, Z_j⟩` (`switchingNum`); in the star domain the factor is positive, so `N_ij`
  and `χ_ij` (`switchingFn`) have the same sign (`switchingFn_pos_iff` and its companions). Unlike
  `χ₂₁`, `N₂₁` has no pole where the arc leaves the star domain.
* A section point (`IsArcSectionPt`): `q ∈ N_{9/4}` (Chapter 7's section `χ₂₃ = 0`, `H(e₃) = 0`,
  `⟨X, Λ_R⟩ = 0`, `det X = 1`, traceless, with `det Λ₁ = 9/4`, the normalization of Chapters
  11–16) and `X` a star state. The image of `lieChart` near the fixed point, and of `reinPoincare`
  on it (`arcParams_reinPoincare`), consists of section points.
* The arc parameters of the state: `ε = ρ₁(X₀)` (`arcEps`), `Y = 1 + ρ₂/ε` (`arcY`),
  `Y' = 1 + ρ₀/ε` (`arcY'`), the exit time `T = ε log Y` (`arcExitTime`).

## Statements

* §1.1: `ofFrame_eq_conj`, `ofFrame_frame`, `frameH_ofFrame` …, `trace_ofFrame`,
  `det_ofFrame`, `traceForm_ofFrame`, `ofFrame_mul_sub`, the linear algebra `ofFrame_add`,
  `ofFrame_sub`, `smul_ofFrame`, `ofFrame_zero`, the star functions `ρ_ofFrame`,
  `frame_controlMatrix` (1.2), `traceForm_controlMatrix_vertex` and `controlMatrix_vertex_add`
  (1.1), `ρ_mul_add`.
* (1.3) and the frame of `X₀`: `arcEps_pos`, `one_lt_arcY`, `one_lt_arcY'`,
  `arcEps_sq_mul_arcY_mul_arcY'` (`ε² Y Y' = 1 + ε²`), `frame_state` (`X₀ = -ε H + x_e E + x_f F`,
  `x_e = -2εY`, `x_f = εY'/2`, `x_e x_f = -(1 + ε²)`; `state_eq_ofFrame`), `X00_eq_arcRadius`
  (`r = X₁₁ = ε(Y' - 2)/2`).
* **Proposition 1.1** (1): `iso_vfP_one_eq` (`P = -ω H`, `ω = 1/(2ε)`), `iso_vfP_one_mul_self`
  (`P² = ω² I`), `det_iso_vfP_one` (`det P = -1/(4ε²) = det(X₀ + P)`), `exp_smul_iso_vfP_one`
  (`e^{tP} = cosh(ωt) I + ω⁻¹ sinh(ωt) P`), `exp_conj_ofFrame` (`Ad e^{tP}` fixes `H` and scales
  `E`, `F` by `u = e^{-t/ε}`, `u⁻¹`).
  (2): `iso_vfX_one_eq`, `ρ_iso_vfX_one` (`ρ₁(t) = ε`, `ρ₂(t) = ε(Y e^{-t/ε} - 1)`,
  `ρ₀(t) = ε(Y' e^{t/ε} - 1)`).
  (3): `arcExitTime_pos`, `isStarState_iso_vfX_one_iff` (for `t ≥ 0`, `X(t) ∈ 𝔥*` iff `t < T`),
  `ρ₂_iso_vfX_one_arcExitTime` (`ρ₂(T) = 0`), `hasDerivAt_ρ₂_iso_vfX_one` (`ρ₂'(T) = -1`).
  (4): `iso_vfX_one_Φ` (in the upper half-plane, `z(t) - 1/√3 = e^{-t/ε}(z(0) - 1/√3)`: the state
  runs along a Euclidean ray into the cusp `1/√3` of the ideal triangle `𝔥*`).

## Proofs (the route, §1.1–§1.2)

1. The frame identities: `ofFrame h e f = [[h + f, (e - 2h - f)/√3], [√3 f, -(h + f)]]` is
   `S [[h, e], [f, -h]] S⁻¹` (`Matrix.inv_def`, `det S = √3`); the components invert it on
   traceless matrices. `traceForm_ofFrame`, `ofFrame_mul_sub`, `det_ofFrame`, (1.2), (1.1),
   `ρ_mul_add`: entrywise (`Matrix.trace_fin_two`, `Matrix.det_fin_two`, `Matrix.mul_apply`,
   `Fin.sum_univ_two`), `field_simp`, `ring`, `Real.sq_sqrt`.
2. (1.3): `ε² (1 + ρ₂/ε)(1 + ρ₀/ε) = (ε + ρ₂)(ε + ρ₀) = ε² + (ρ₀ρ₁ + ρ₁ρ₂ + ρ₂ρ₀) = ε² + 1`.
   `frame_state`: compare (1.2) with (1.1): `x_h = -ε`, `x_e = -2(ρ₂ + ε)`, `x_f = (ρ₀ + ε)/2`;
   `det X₀ = 1` reads `x_e x_f = -(1 + ε²)` (`det_ofFrame`).
3. Proposition 1.1 (1): `iso_vfP 1 q = controlP (vertex 1) q.1 = ⟨Z_{e₂}, X₀⟩⁻¹ Z_{e₂}` with
   `⟨Z_{e₂}, X₀⟩ = -(2/√3) ε` and `Z_{e₂} = ofFrame (1/√3) 0 0`. `P² = ω² I` from the frame; `det`
   from `det_ofFrame`; `det(X₀ + P) = det P` (Lemma 7.1.3, `lemma7_1_3`) is read off the frame:
   `X₀ + P = -(ε + ω) H + x_e E + x_f F`, so `det(X₀ + P) = -((ε + ω)² + x_e x_f) =
   -(2εω + ω² - 1) = -ω²` (`2εω = 1`, `x_e x_f = -(1 + ε²)`). The exponential: `lemmaA_6_4` with
   `det P = -ω² < 0`. Conjugation: `e^{tP} = S diag(e^{-ωt}, e^{ωt}) S⁻¹`, so `Ad e^{tP}` acts by
   `H ↦ H`, `E ↦ u E`, `F ↦ u⁻¹ F`, `u = e^{-2ωt} = e^{-t/ε}` (expand `exp_smul_iso_vfP_one` and
   `Real.cosh_eq`, `Real.sinh_eq` entrywise).
4. (2): `iso_vfX 1 q t = e^{tP} X₀ e^{-tP}` (`constControlX`) and steps 2–3; the `ρ`'s from the
   components (`ρ₁ = -x_h`, `ρ₂ = -x_e/2 - ρ₁`, `ρ₀ = 2 x_f - ρ₁`).
5. (3): `ρ₁(t) = ε > 0`, `ρ₀(t) ≥ ρ₀(0) > 0` for `t ≥ 0` (`Y' e^{t/ε} ≥ Y' > 1`); `X(t)` is
   traceless, and `det X(t) = -(ε² - ε² Y Y') = 1` by `det_ofFrame` and (1.3) (the factors `u`,
   `u⁻¹` cancel); `ρ₂(t) > 0 ⟺ e^{-t/ε} > 1/Y ⟺ t < ε log Y`
   (`Y > 1`). `ρ₂(T) = ε(Y/Y - 1) = 0`; `ρ₂'(t) = -Y e^{-t/ε} = -1` at `t = T`.
6. (4): with `X₀ = Φ(x, y)` (`y > 0`), `iso_vfX_one_eq` and the entries of `Φ`: both sides are
   `[[x'/y', -(x'² + y'²)/y'], [1/y', -x'/y']]` for `x' = 1/√3 + u(x - 1/√3)`, `y' = u y`;
   `ε = ρ₁(Φ(x, y)) = (1 - √3 x)/(√3 y)`; entrywise `field_simp`, `ring`. (Geometrically:
   the Möbius action of `e^{tZ_{e₂}}` fixes `1/√3` and `∞`.)

All of this was also checked numerically, while the statements were written, against a literal
model of the Lean definitions; the proofs do not depend on these checks.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-! ### The frame (§1.1) -/

/-- The frame matrix `S = [[1, 1], [0, √3]]` (§1.1): `S⁻¹ Z_{e₂} S = H/√3`. -/
noncomputable def arcFrameS : Mat2 := !![1, 1; 0, √3]

/-- The traceless matrix with frame components `(h, e, f)`: `S (h H + e E + f F) S⁻¹`
(`ofFrame_eq_conj`), `H = diag(1, -1)`, `E = e₁₂`, `F = e₂₁`. -/
noncomputable def ofFrame (h e f : ℝ) : Mat2 :=
  !![h + f, (e - 2 * h - f) / √3; √3 * f, -(h + f)]

/-- The `H`-component of a traceless matrix in the frame. -/
noncomputable def frameH (M : Mat2) : ℝ := M 0 0 - M 1 0 / √3

/-- The `E`-component of a traceless matrix in the frame. -/
noncomputable def frameE (M : Mat2) : ℝ := √3 * M 0 1 + 2 * M 0 0 - M 1 0 / √3

/-- The `F`-component of a traceless matrix in the frame. -/
noncomputable def frameF (M : Mat2) : ℝ := M 1 0 / √3

/-- **A section point** (§1.1): a point of Chapter 7's Poincaré section `N_{9/4}`
(`X, Λ₁, Λ_R` traceless, `det X = 1`, `⟨X, Λ_R⟩ = 0`, `H(e₃) = 0`, `χ₂₃ = 0`, `det Λ₁ = 9/4`) whose
state is a star state. On it `H(e₂) = H(e₃) = 0`. -/
def IsArcSectionPt (q : iso_PhasePt) : Prop := q ∈ iso_sectionN (9 / 4) ∧ IsStarState q.1

/-- **The cleared switching numerator** `N_ij = ⟨Λ_R, Z_j⟩⟨X, Z_i⟩ - ⟨Λ_R, Z_i⟩⟨X, Z_j⟩`
(§1.1), `Z_k = Z_{e_k}`; it is `χ_ij ⟨X, Z_i⟩⟨X, Z_j⟩` (`switchingNum_eq`). -/
noncomputable def switchingNum (i j : Fin 3) (q : iso_PhasePt) : ℝ :=
  traceForm q.2.2 (controlMatrix (vertex j)) * traceForm q.1 (controlMatrix (vertex i)) -
    traceForm q.2.2 (controlMatrix (vertex i)) * traceForm q.1 (controlMatrix (vertex j))

/-- `ε = ρ₁(X₀)`, the constant value of `ρ₁` along the `e₂`-arc from `q`. -/
noncomputable def arcEps (q : iso_PhasePt) : ℝ := ρ₁ q.1

/-- `Y = 1 + ρ₂(X₀)/ε` ((1.3)). -/
noncomputable def arcY (q : iso_PhasePt) : ℝ := 1 + ρ₂ q.1 / ρ₁ q.1

/-- `Y' = 1 + ρ₀(X₀)/ε` ((1.3)). -/
noncomputable def arcY' (q : iso_PhasePt) : ℝ := 1 + ρ₀ q.1 / ρ₁ q.1

/-- **The exit time** `T = ε log Y` of the `e₂`-arc from `q` (Proposition 1.1 (3)). -/
noncomputable def arcExitTime (q : iso_PhasePt) : ℝ := ρ₁ q.1 * Real.log (arcY q)

/-! ### Frame identities, (1.1) and (1.2) -/

private lemma n4b_sqrt3_pos : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
private lemma n4b_sqrt3_ne : (√3 : ℝ) ≠ 0 := n4b_sqrt3_pos.ne'
private lemma n4b_sqrt3_sq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- `ofFrame h e f = S [[h, e], [f, -h]] S⁻¹`. -/
theorem ofFrame_eq_conj (h e f : ℝ) :
    ofFrame h e f = arcFrameS * !![h, e; f, -h] * arcFrameS⁻¹ := by
  have hS : arcFrameS * !![1, -(1 / √3); 0, 1 / √3] = 1 := by
    have := n4b_sqrt3_ne
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [arcFrameS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [Matrix.inv_eq_right_inv hS]
  have := n4b_sqrt3_ne
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [arcFrameS, ofFrame, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp; ring

@[simp] theorem frameH_ofFrame (h e f : ℝ) : frameH (ofFrame h e f) = h := by
  have := n4b_sqrt3_ne
  simp [frameH, ofFrame]

@[simp] theorem frameE_ofFrame (h e f : ℝ) : frameE (ofFrame h e f) = e := by
  have := n4b_sqrt3_ne
  simp [frameE, ofFrame]; field_simp; ring

@[simp] theorem frameF_ofFrame (h e f : ℝ) : frameF (ofFrame h e f) = f := by
  have := n4b_sqrt3_ne
  simp [frameF, ofFrame]

/-- A traceless matrix is `ofFrame` of its components. -/
theorem ofFrame_frame {M : Mat2} (hM : M.trace = 0) :
    ofFrame (frameH M) (frameE M) (frameF M) = M := by
  have := n4b_sqrt3_ne
  rw [Matrix.trace_fin_two] at hM
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [frameH, frameE, frameF, ofFrame] <;> field_simp
  · ring
  · linarith

theorem trace_ofFrame (h e f : ℝ) : (ofFrame h e f).trace = 0 := by
  simp [ofFrame, Matrix.trace_fin_two]

/-- `det(h H + e E + f F) = -(h² + e f)`. -/
theorem det_ofFrame (h e f : ℝ) : (ofFrame h e f).det = -(h ^ 2 + e * f) := by
  have := n4b_sqrt3_ne
  simp [ofFrame, Matrix.det_fin_two]; field_simp; ring

/-- The trace form in the frame: `⟨M, N⟩ = 2 m_h n_h + m_e n_f + m_f n_e`. -/
theorem traceForm_ofFrame (h e f h' e' f' : ℝ) :
    traceForm (ofFrame h e f) (ofFrame h' e' f') = 2 * h * h' + e * f' + f * e' := by
  have := n4b_sqrt3_ne
  simp [traceForm, ofFrame, Matrix.trace_fin_two]
  field_simp; ring

/-- The bracket in the frame: `[aH + bE + cF, a'H + b'E + c'F] =
(bc' - cb') H + 2(ab' - ba') E + 2(ca' - ac') F`. -/
theorem ofFrame_mul_sub (h e f h' e' f' : ℝ) :
    ofFrame h e f * ofFrame h' e' f' - ofFrame h' e' f' * ofFrame h e f =
      ofFrame (e * f' - f * e') (2 * (h * e' - e * h')) (2 * (f * h' - h * f')) := by
  have := n4b_sqrt3_ne
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ofFrame] <;> field_simp <;> ring

theorem ofFrame_add (h e f h' e' f' : ℝ) :
    ofFrame h e f + ofFrame h' e' f' = ofFrame (h + h') (e + e') (f + f') := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ofFrame] <;> ring

theorem ofFrame_sub (h e f h' e' f' : ℝ) :
    ofFrame h e f - ofFrame h' e' f' = ofFrame (h - h') (e - e') (f - f') := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ofFrame] <;> ring

theorem smul_ofFrame (c h e f : ℝ) :
    c • ofFrame h e f = ofFrame (c * h) (c * e) (c * f) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ofFrame] <;> ring

theorem ofFrame_zero : ofFrame 0 0 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ofFrame]

/-- The star functions in the frame: `ρ₁ = -h`, `ρ₂ = h - e/2`, `ρ₀ = h + 2f`. -/
theorem ρ_ofFrame (h e f : ℝ) :
    ρ₁ (ofFrame h e f) = -h ∧ ρ₂ (ofFrame h e f) = h - e / 2 ∧
      ρ₀ (ofFrame h e f) = h + 2 * f := by
  have := n4b_sqrt3_ne
  have h3 := n4b_sqrt3_sq
  refine ⟨?_, ?_, ?_⟩ <;> simp only [ρ₀, ρ₁, ρ₂, ofFrame, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
    field_simp
  · ring
  · linear_combination (e - 2 * h - f) * h3
  · ring

/-- **(1.2)**: `Z_{e₁} = (F - H)/√3`, `Z_{e₂} = H/√3`, `Z_{e₃} = -(H + 4E)/√3`,
`J = (-H - 4E + F)/√3` in the frame. -/
theorem frame_controlMatrix :
    controlMatrix (vertex 0) = ofFrame (-(1 / √3)) 0 (1 / √3) ∧
      controlMatrix (vertex 1) = ofFrame (1 / √3) 0 0 ∧
      controlMatrix (vertex 2) = ofFrame (-(1 / √3)) (-(4 / √3)) 0 ∧
      J = ofFrame (-(1 / √3)) (-(4 / √3)) (1 / √3) := by
  have := n4b_sqrt3_ne
  have h3 := n4b_sqrt3_sq
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [controlMatrix, vertex, ofFrame, J] <;> field_simp <;> norm_num [h3]

/-- **(1.1)**: for traceless `X`, `⟨X, Z_{e₁}⟩ = -(2/√3) ρ₂`, `⟨X, Z_{e₂}⟩ = -(2/√3) ρ₁`,
`⟨X, Z_{e₃}⟩ = -(2/√3) ρ₀`. -/
theorem traceForm_controlMatrix_vertex {X : Mat2} (hX : X.trace = 0) :
    traceForm X (controlMatrix (vertex 0)) = -(2 / √3) * ρ₂ X ∧
      traceForm X (controlMatrix (vertex 1)) = -(2 / √3) * ρ₁ X ∧
      traceForm X (controlMatrix (vertex 2)) = -(2 / √3) * ρ₀ X := by
  have := n4b_sqrt3_ne
  have h3 := n4b_sqrt3_sq
  rw [Matrix.trace_fin_two] at hX
  have h11 : X 1 1 = -X 0 0 := by linarith
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [traceForm, controlMatrix, vertex, ρ₀, ρ₁, ρ₂, Matrix.trace_fin_two, Matrix.mul_apply,
      h11] <;> field_simp <;> ring_nf <;> simp [h3] <;> ring

/-- **(1.1)**: `Z_{e₁} + Z_{e₂} + Z_{e₃} = J`. -/
theorem controlMatrix_vertex_add :
    controlMatrix (vertex 0) + controlMatrix (vertex 1) + controlMatrix (vertex 2) = J := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [controlMatrix, vertex, J] <;> ring

/-- **(1.1)**: `ρ₀ρ₁ + ρ₁ρ₂ + ρ₂ρ₀ = det X` for traceless `X` (`= 1` on the states). -/
theorem ρ_mul_add {X : Mat2} (hX : X.trace = 0) :
    ρ₀ X * ρ₁ X + ρ₁ X * ρ₂ X + ρ₂ X * ρ₀ X = X.det := by
  have := n4b_sqrt3_ne
  have h3 := n4b_sqrt3_sq
  rw [Matrix.trace_fin_two] at hX
  have h11 : X 1 1 = -X 0 0 := by linarith
  simp only [ρ₀, ρ₁, ρ₂, Matrix.det_fin_two, h11]
  field_simp
  ring_nf
  simp [h3]
  ring

/-! ### The cleared switching numerators -/

/-- `N_ij = χ_ij ⟨X, Z_i⟩⟨X, Z_j⟩` where both pairings are nonzero. -/
theorem switchingNum_eq (i j : Fin 3) (q : iso_PhasePt)
    (hi : traceForm q.1 (controlMatrix (vertex i)) ≠ 0)
    (hj : traceForm q.1 (controlMatrix (vertex j)) ≠ 0) :
    switchingNum i j q = switchingFn i j q.2.2 q.1 *
      (traceForm q.1 (controlMatrix (vertex i)) * traceForm q.1 (controlMatrix (vertex j))) := by
  have hc : ∀ k, traceForm (controlMatrix (vertex k)) q.1 =
      traceForm q.1 (controlMatrix (vertex k)) := fun k ↦ Matrix.trace_mul_comm _ _
  simp only [switchingNum, switchingFn, controlP, traceForm, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at hi hj hc ⊢
  rw [hc i, hc j]
  field_simp

/-- In the star domain every pairing `⟨X, Z_{e_k}⟩` is negative (by (1.1)). -/
private lemma n4b_traceForm_vertex_neg {X : Mat2} (hX : IsStarState X) (k : Fin 3) :
    traceForm X (controlMatrix (vertex k)) < 0 := by
  obtain ⟨h0, h1, h2⟩ := traceForm_controlMatrix_vertex hX.1
  have hs : 0 < 2 / √3 := div_pos two_pos n4b_sqrt3_pos
  obtain ⟨-, -, hρ₀, hρ₁, hρ₂⟩ := hX
  fin_cases k
  · simp only [Fin.zero_eta, h0]; nlinarith
  · simp only [Fin.mk_one, h1]; nlinarith
  · simp only [Fin.reduceFinMk, h2]; nlinarith

private lemma n4b_switchingNum_eq_mul (i j : Fin 3) {q : iso_PhasePt} (hX : IsStarState q.1) :
    switchingNum i j q = switchingFn i j q.2.2 q.1 *
      (traceForm q.1 (controlMatrix (vertex i)) * traceForm q.1 (controlMatrix (vertex j))) ∧
    0 < traceForm q.1 (controlMatrix (vertex i)) * traceForm q.1 (controlMatrix (vertex j)) :=
  ⟨switchingNum_eq i j q (n4b_traceForm_vertex_neg hX i).ne (n4b_traceForm_vertex_neg hX j).ne,
    mul_pos_of_neg_of_neg (n4b_traceForm_vertex_neg hX i) (n4b_traceForm_vertex_neg hX j)⟩

/-- In the star domain `χ_ij > 0` iff `N_ij > 0` (the factor `⟨X, Z_i⟩⟨X, Z_j⟩` is positive by
(1.1)). -/
theorem switchingFn_pos_iff (i j : Fin 3) {q : iso_PhasePt} (hX : IsStarState q.1) :
    0 < switchingFn i j q.2.2 q.1 ↔ 0 < switchingNum i j q := by
  obtain ⟨he, hp⟩ := n4b_switchingNum_eq_mul i j hX
  rw [he, mul_pos_iff_of_pos_right hp]

/-- In the star domain `χ_ij < 0` iff `N_ij < 0`. -/
theorem switchingFn_neg_iff (i j : Fin 3) {q : iso_PhasePt} (hX : IsStarState q.1) :
    switchingFn i j q.2.2 q.1 < 0 ↔ switchingNum i j q < 0 := by
  obtain ⟨he, hp⟩ := n4b_switchingNum_eq_mul i j hX
  rw [he]
  exact ⟨fun h ↦ mul_neg_of_neg_of_pos h hp, fun h ↦ by
    by_contra h'
    exact (mul_nonneg (not_lt.1 h') hp.le).not_gt h⟩

/-- In the star domain `χ_ij = 0` iff `N_ij = 0`. -/
theorem switchingFn_eq_zero_iff (i j : Fin 3) {q : iso_PhasePt} (hX : IsStarState q.1) :
    switchingFn i j q.2.2 q.1 = 0 ↔ switchingNum i j q = 0 := by
  obtain ⟨he, hp⟩ := n4b_switchingNum_eq_mul i j hX
  rw [he, mul_eq_zero, or_iff_left hp.ne']

/-! ### (1.3) and the frame of the initial state -/

variable {q : iso_PhasePt}

theorem arcEps_pos (hX : IsStarState q.1) : 0 < arcEps q := hX.2.2.2.1

theorem one_lt_arcY (hX : IsStarState q.1) : 1 < arcY q := by
  unfold arcY
  have := div_pos hX.2.2.2.2 hX.2.2.2.1
  linarith

theorem one_lt_arcY' (hX : IsStarState q.1) : 1 < arcY' q := by
  unfold arcY'
  have := div_pos hX.2.2.1 hX.2.2.2.1
  linarith

/-- `ε Y = ε + ρ₂` and `ε Y' = ε + ρ₀`. -/
private lemma n4b_arcEps_mul (hε : ρ₁ q.1 ≠ 0) :
    arcEps q * arcY q = arcEps q + ρ₂ q.1 ∧ arcEps q * arcY' q = arcEps q + ρ₀ q.1 := by
  unfold arcEps arcY arcY'
  constructor <;> field_simp

/-- **(1.3)**: `ε² Y Y' = 1 + ε²`. -/
theorem arcEps_sq_mul_arcY_mul_arcY' (hX : IsStarState q.1) :
    arcEps q ^ 2 * arcY q * arcY' q = 1 + arcEps q ^ 2 := by
  obtain ⟨h1, h2⟩ := n4b_arcEps_mul hX.2.2.2.1.ne'
  have hd := ρ_mul_add hX.1
  rw [hX.2.1] at hd
  have : arcEps q ^ 2 * arcY q * arcY' q = (arcEps q * arcY q) * (arcEps q * arcY' q) := by ring
  rw [this, h1, h2]
  unfold arcEps
  linear_combination hd

/-- **The initial state in the frame** (Proposition 1.1 (1)): `X₀ = -ε H + x_e E + x_f F` with
`x_e = -2εY`, `x_f = εY'/2`, and `x_e x_f = -(1 + ε²)` (`det X₀ = 1`). -/
theorem frame_state (hX : IsStarState q.1) :
    frameH q.1 = -arcEps q ∧ frameE q.1 = -2 * arcEps q * arcY q ∧
      frameF q.1 = arcEps q * arcY' q / 2 ∧ frameE q.1 * frameF q.1 = -(1 + arcEps q ^ 2) := by
  obtain ⟨h1, h2⟩ := n4b_arcEps_mul hX.2.2.2.1.ne'
  have := n4b_sqrt3_ne
  have h3 := n4b_sqrt3_sq
  have hH : frameH q.1 = -arcEps q := by
    simp only [frameH, arcEps, ρ₁]; field_simp; ring
  have hE : frameE q.1 = -2 * arcEps q * arcY q := by
    rw [mul_assoc, h1]; simp only [frameE, arcEps, ρ₁, ρ₂]; field_simp; ring_nf; simp [h3]; ring
  have hF : frameF q.1 = arcEps q * arcY' q / 2 := by
    rw [h2]; simp only [frameF, arcEps, ρ₁, ρ₀]; field_simp; ring
  refine ⟨hH, hE, hF, ?_⟩
  have hd := det_ofFrame (frameH q.1) (frameE q.1) (frameF q.1)
  rw [ofFrame_frame hX.1, hX.2.1, hH] at hd
  linear_combination hd

/-- **The chart radius** `r = X₁₁ = (ρ₀ - ρ₁)/2 = ε (Y' - 2)/2` (Theorem 2.1), for every matrix
`X₀` with `ρ₁(X₀) ≠ 0` (`ρ₀ - ρ₁ = 2 X₁₁` needs no trace condition). -/
theorem X00_eq_arcRadius (hε : ρ₁ q.1 ≠ 0) :
    q.1 0 0 = arcEps q * (arcY' q - 2) / 2 := by
  have h2 := (n4b_arcEps_mul hε).2
  have := n4b_sqrt3_ne
  rw [mul_sub, h2]
  simp only [arcEps, ρ₁, ρ₀]
  field_simp
  ring

/-! ### Proposition 1.1: the state along the `e₂`-arc -/

/-- **The initial state in the frame**: `X₀ = ofFrame (-ε) (-2εY) (εY'/2)` (`frame_state`). -/
theorem state_eq_ofFrame (hX : IsStarState q.1) :
    q.1 = ofFrame (-arcEps q) (-2 * arcEps q * arcY q) (arcEps q * arcY' q / 2) := by
  obtain ⟨hH, hE, hF, -⟩ := frame_state hX
  rw [← hH, ← hE, ← hF, ofFrame_frame hX.1]

/-- **Proposition 1.1 (1)**: `P = Z_{e₂}/⟨Z_{e₂}, X₀⟩ = -ω H`, `ω = 1/(2ε)`. -/
theorem iso_vfP_one_eq (hX : IsStarState q.1) :
    iso_vfP 1 q = ofFrame (-(1 / (2 * arcEps q))) 0 0 := by
  have hε := (arcEps_pos hX).ne'
  have := n4b_sqrt3_ne
  have hc : traceForm (controlMatrix (vertex 1)) q.1 = -(2 / √3) * arcEps q := by
    rw [traceForm, Matrix.trace_mul_comm, ← traceForm]
    exact (traceForm_controlMatrix_vertex hX.1).2.1
  rw [iso_vfP, controlP, hc, (frame_controlMatrix).2.1, smul_ofFrame]
  congr 1
  · field_simp
  all_goals simp

/-- **Proposition 1.1 (1)**: `P² = ω² I`. -/
theorem iso_vfP_one_mul_self (hX : IsStarState q.1) :
    iso_vfP 1 q * iso_vfP 1 q = (1 / (2 * arcEps q)) ^ 2 • (1 : Mat2) := by
  have := n4b_sqrt3_ne
  rw [iso_vfP_one_eq hX]
  ext i j; fin_cases i <;> fin_cases j <;> simp [ofFrame, Matrix.mul_apply] <;> ring

/-- **Proposition 1.1 (1)**: `det P = -1/(4ρ₁²)` and `det(X₀ + P) = det P`. -/
theorem det_iso_vfP_one (hX : IsStarState q.1) :
    (iso_vfP 1 q).det = -1 / (4 * arcEps q ^ 2) ∧
      (q.1 + iso_vfP 1 q).det = (iso_vfP 1 q).det := by
  have hε := (arcEps_pos hX).ne'
  have hef := (frame_state hX).2.2.2
  obtain ⟨hH, hE, hF, -⟩ := frame_state hX
  have hdP : (iso_vfP 1 q).det = -1 / (4 * arcEps q ^ 2) := by
    rw [iso_vfP_one_eq hX, det_ofFrame]; field_simp; ring
  refine ⟨hdP, ?_⟩
  rw [hdP, iso_vfP_one_eq hX, ← ofFrame_frame hX.1, ofFrame_add, det_ofFrame, add_zero,
    add_zero, hH, hef]
  field_simp
  ring

/-- **Proposition 1.1 (1)**: `e^{tP} = cosh(ωt) I + ω⁻¹ sinh(ωt) P`, `ω = 1/(2ε)`. -/
theorem exp_smul_iso_vfP_one (hX : IsStarState q.1) (t : ℝ) :
    NormedSpace.exp (t • iso_vfP 1 q) =
      Real.cosh (t / (2 * arcEps q)) • (1 : Mat2) +
        (2 * arcEps q * Real.sinh (t / (2 * arcEps q))) • iso_vfP 1 q := by
  have hε := arcEps_pos hX
  have htr : (iso_vfP 1 q).trace = 0 := by rw [iso_vfP_one_eq hX]; exact trace_ofFrame _ _ _
  have hd := (det_iso_vfP_one hX).1
  have hneg : (iso_vfP 1 q).det < 0 := by
    rw [hd]; exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hsq : √(-(iso_vfP 1 q).det) = 1 / (2 * arcEps q) := by
    rw [hd, show -(-1 / (4 * arcEps q ^ 2)) = (1 / (2 * arcEps q)) ^ 2 by field_simp; ring,
      Real.sqrt_sq (by positivity)]
  rw [((lemmaA_6_4 _ htr).2 t).1 hneg, hsq, mul_one_div]
  congr 2
  field_simp

/-- `e^{tP} = [[e^{-ωt}, (e^{ωt} - e^{-ωt})/√3], [0, e^{ωt}]]`, `ω = 1/(2ε)`. -/
private lemma n4b_exp_smul_eq (hX : IsStarState q.1) (t : ℝ) :
    NormedSpace.exp (t • iso_vfP 1 q) =
      !![Real.exp (-(t / (2 * arcEps q))),
        (Real.exp (t / (2 * arcEps q)) - Real.exp (-(t / (2 * arcEps q)))) / √3;
        0, Real.exp (t / (2 * arcEps q))] := by
  have hε := (arcEps_pos hX).ne'
  have := n4b_sqrt3_ne
  rw [exp_smul_iso_vfP_one hX, iso_vfP_one_eq hX, Real.cosh_eq, Real.sinh_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [ofFrame] <;> field_simp <;> ring

/-- **Proposition 1.1 (1)**: `Ad e^{tP}` in the frame fixes `H` and multiplies `E`, `F` by
`u = e^{-t/ε}` and `u⁻¹`. -/
theorem exp_conj_ofFrame (hX : IsStarState q.1) (t h e f : ℝ) :
    NormedSpace.exp (t • iso_vfP 1 q) * ofFrame h e f * NormedSpace.exp (-t • iso_vfP 1 q) =
      ofFrame h (Real.exp (-t / arcEps q) * e) (Real.exp (t / arcEps q) * f) := by
  have hε := (arcEps_pos hX).ne'
  have := n4b_sqrt3_ne
  rw [n4b_exp_smul_eq hX, n4b_exp_smul_eq hX, neg_div, neg_neg]
  have e1 : Real.exp (t / arcEps q) = Real.exp (t / (2 * arcEps q)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; field_simp; ring
  have e2 : Real.exp (-t / arcEps q) = (Real.exp (t / (2 * arcEps q)) ^ 2)⁻¹ := by
    rw [neg_div, Real.exp_neg, e1]
  rw [e1, e2, Real.exp_neg]
  have hE := Real.exp_pos (t / (2 * arcEps q))
  generalize Real.exp (t / (2 * arcEps q)) = E at hE ⊢
  have hE' := hE.ne'
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ofFrame, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring_nf

/-- **Proposition 1.1 (2)**: `X(t) = -ε H + x_e u E + x_f u⁻¹ F`, `u = e^{-t/ε}`. -/
theorem iso_vfX_one_eq (hX : IsStarState q.1) (t : ℝ) :
    iso_vfX 1 q t = ofFrame (-arcEps q) (-2 * arcEps q * arcY q * Real.exp (-t / arcEps q))
      (arcEps q * arcY' q / 2 * Real.exp (t / arcEps q)) := by
  rw [iso_vfX, constControlX, state_eq_ofFrame hX, exp_conj_ofFrame hX]
  congr 1 <;> ring

/-- **Proposition 1.1 (2)**: `ρ₁(t) = ε`, `ρ₂(t) = ε(Y e^{-t/ε} - 1)`, `ρ₀(t) = ε(Y' e^{t/ε} - 1)`
along the `e₂`-arc. -/
theorem ρ_iso_vfX_one (hX : IsStarState q.1) (t : ℝ) :
    ρ₁ (iso_vfX 1 q t) = arcEps q ∧
      ρ₂ (iso_vfX 1 q t) = arcEps q * (arcY q * Real.exp (-t / arcEps q) - 1) ∧
      ρ₀ (iso_vfX 1 q t) = arcEps q * (arcY' q * Real.exp (t / arcEps q) - 1) := by
  obtain ⟨h1, h2, h0⟩ := ρ_ofFrame (-arcEps q)
    (-2 * arcEps q * arcY q * Real.exp (-t / arcEps q))
    (arcEps q * arcY' q / 2 * Real.exp (t / arcEps q))
  rw [iso_vfX_one_eq hX, h1, h2, h0]
  refine ⟨neg_neg _, ?_, ?_⟩ <;> ring

/-- The exit time is positive. -/
theorem arcExitTime_pos (hX : IsStarState q.1) : 0 < arcExitTime q :=
  mul_pos hX.2.2.2.1 (Real.log_pos (one_lt_arcY hX))

/-- **Proposition 1.1 (3)**: for `t ≥ 0`, `X(t)` is a star state iff `t < T = ε log Y`: the arc
leaves `𝔥*` exactly at `T`, through `ρ₂ = 0` (`ρ₁` is constant and `ρ₀` increases). -/
theorem isStarState_iso_vfX_one_iff (hX : IsStarState q.1) {t : ℝ} (ht : 0 ≤ t) :
    IsStarState (iso_vfX 1 q t) ↔ t < arcExitTime q := by
  have hε := arcEps_pos hX
  have hY := one_lt_arcY hX
  have hY' := one_lt_arcY' hX
  obtain ⟨h1, h2, h0⟩ := ρ_iso_vfX_one hX t
  have htr : (iso_vfX 1 q t).trace = 0 := by rw [iso_vfX_one_eq hX]; exact trace_ofFrame _ _ _
  have hdet : (iso_vfX 1 q t).det = 1 := by
    have hYY := arcEps_sq_mul_arcY_mul_arcY' hX
    have hu : Real.exp (-t / arcEps q) * Real.exp (t / arcEps q) = 1 := by
      rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
    rw [iso_vfX_one_eq hX, det_ofFrame]
    linear_combination hYY + arcEps q ^ 2 * arcY q * arcY' q * hu
  have hρ₀ : 0 < ρ₀ (iso_vfX 1 q t) := by
    rw [h0]
    have : 1 ≤ Real.exp (t / arcEps q) := Real.one_le_exp (div_nonneg ht hε.le)
    have : 1 < arcY' q * Real.exp (t / arcEps q) := by nlinarith
    exact mul_pos hε (by linarith)
  have hρ₂ : 0 < ρ₂ (iso_vfX 1 q t) ↔ t < arcExitTime q := by
    rw [h2, mul_pos_iff_of_pos_left hε, sub_pos]
    have hY0 : 0 < arcY q := by linarith
    rw [show arcY q * Real.exp (-t / arcEps q) = Real.exp (Real.log (arcY q) - t / arcEps q) by
      rw [Real.exp_sub, Real.exp_log hY0, neg_div, Real.exp_neg, ← div_eq_mul_inv],
      Real.one_lt_exp_iff, sub_pos, div_lt_iff₀ hε, arcExitTime]
    exact ⟨fun h ↦ by unfold arcEps at h; linarith, fun h ↦ by unfold arcEps; linarith⟩
  rw [← hρ₂]
  exact ⟨fun h ↦ h.2.2.2.2, fun h ↦ ⟨htr, hdet, hρ₀, h1 ▸ hε, h⟩⟩

/-- **Proposition 1.1 (3)**: `ρ₂(X(T)) = 0`. -/
theorem ρ₂_iso_vfX_one_arcExitTime (hX : IsStarState q.1) :
    ρ₂ (iso_vfX 1 q (arcExitTime q)) = 0 := by
  have hε : ρ₁ q.1 ≠ 0 := (arcEps_pos hX).ne'
  have hY0 : 0 < arcY q := by linarith [one_lt_arcY hX]
  rw [(ρ_iso_vfX_one hX _).2.1, arcExitTime,
    show -(ρ₁ q.1 * Real.log (arcY q)) / arcEps q = -Real.log (arcY q) by
      unfold arcEps; field_simp,
    Real.exp_neg, Real.exp_log hY0, mul_inv_cancel₀ hY0.ne', sub_self, mul_zero]

/-- **Proposition 1.1 (3)**: `ρ₂'(T) = -1` (the transversal exit, the "`-1.000`" of the numerical
check). -/
theorem hasDerivAt_ρ₂_iso_vfX_one (hX : IsStarState q.1) :
    HasDerivAt (fun t ↦ ρ₂ (iso_vfX 1 q t)) (-1) (arcExitTime q) := by
  have hε : ρ₁ q.1 ≠ 0 := (arcEps_pos hX).ne'
  have hY0 : 0 < arcY q := by linarith [one_lt_arcY hX]
  have hf : (fun t ↦ ρ₂ (iso_vfX 1 q t)) =
      fun t ↦ arcEps q * (arcY q * Real.exp (-t / arcEps q) - 1) :=
    funext fun t ↦ (ρ_iso_vfX_one hX t).2.1
  rw [hf]
  have hd := ((((hasDerivAt_neg (arcExitTime q)).div_const (arcEps q)).exp.const_mul
    (arcY q)).sub_const 1).const_mul (arcEps q)
  convert hd using 1
  rw [arcExitTime, show -(ρ₁ q.1 * Real.log (arcY q)) / arcEps q = -Real.log (arcY q) by
      unfold arcEps; field_simp, Real.exp_neg, Real.exp_log hY0]
  unfold arcEps
  field_simp

/-- **Proposition 1.1 (4)**: in the upper half-plane (`X₀ = Φ(z)`, `z = x + iy`),
`z(t) - 1/√3 = e^{-t/ε} (z(0) - 1/√3)`: the state runs along a Euclidean ray into the cusp `1/√3`
of the ideal triangle `𝔥*`, at the angle fixed by `ρ₁ = ε`. -/
theorem iso_vfX_one_Φ (hX : IsStarState q.1) {x y : ℝ} (hy : 0 < y) (hq : q.1 = Φ x y) (t : ℝ) :
    iso_vfX 1 q t = Φ (1 / √3 + Real.exp (-t / arcEps q) * (x - 1 / √3))
      (Real.exp (-t / arcEps q) * y) := by
  have hε := (arcEps_pos hX).ne'
  obtain ⟨h1, h2⟩ := n4b_arcEps_mul hε
  have := n4b_sqrt3_ne
  have h3 := n4b_sqrt3_sq
  have hy' := hy.ne'
  rw [iso_vfX_one_eq hX, mul_assoc (-2 : ℝ), h1, h2,
    show Real.exp (t / arcEps q) = (Real.exp (-t / arcEps q))⁻¹ by
      rw [neg_div, Real.exp_neg, inv_inv]]
  have hu := Real.exp_pos (-t / arcEps q)
  generalize Real.exp (-t / arcEps q) = u at hu ⊢
  have hu' := hu.ne'
  unfold arcEps
  rw [hq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ofFrame, Φ, ρ₀, ρ₁, ρ₂] <;> field_simp
  · ring
  · linear_combination 2 * u ^ 2 * (x ^ 2 + y ^ 2) * h3
  · ring
  · ring

end SmoothedPolygons
