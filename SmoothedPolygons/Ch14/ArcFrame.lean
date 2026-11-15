module

public import SmoothedPolygons.Ch14.AnalyticExtension
public import SmoothedPolygons.Ch14.ArcParams
import SmoothedPolygons.Ch7.Isolated.VertexFlow

/-!
# Chapter 14, N4: the eigenframe of an `e₂`-arc and the state along it (Proposition 1.1)

`notes/n4/proof.md` §1.1–§1.2: the frame in which `P = Z_{e₂}/⟨Z_{e₂}, X₀⟩` is diagonal, the star
functions in it, and the state `X(t)` of the `e₂`-flow (`iso_vfX 1`) in closed form. Part of the
reduction of N4 (`UnstableCurveLeavesStarDomain`) to the single-step statement (INV)
(`ArcRegionInvariant`, `SmoothedPolygons/Ch14/ArcRegionInvariant.lean`).

**Departure from the paper.** The book computes the unstable curve numerically (Figure 14.2,
TeX 11951–11991); the formalization proves N4 from (INV) by the exact structure of the arcs, of
which this file is the first part (see `SmoothedPolygons/Ch14/ArcParams.lean`).

## Vocabulary

* The frame (proof.md §1.1): `S = [[1, 1], [0, √3]]` (`arcFrameS`), `H = diag(1, -1)`, `E = e₁₂`,
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
  `det_ofFrame`, `traceForm_ofFrame`, `ofFrame_mul_sub`, `frame_controlMatrix` (1.2),
  `traceForm_controlMatrix_vertex` and `controlMatrix_vertex_add` (1.1), `ρ_mul_add`.
* (1.3) and the frame of `X₀`: `arcEps_pos`, `one_lt_arcY`, `one_lt_arcY'`,
  `arcEps_sq_mul_arcY_mul_arcY'` (`ε² Y Y' = 1 + ε²`), `frame_state` (`X₀ = -ε H + x_e E + x_f F`,
  `x_e = -2εY`, `x_f = εY'/2`, `x_e x_f = -(1 + ε²)`), `X00_eq_arcRadius` (`r = X₁₁ = ε(Y' - 2)/2`).
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

## Proofs (the route, proof.md §1.1–§1.2)

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
   from `det_ofFrame`; `det(X₀ + P) = det P` is Lemma 7.1.3 (`lemma7_1_3`), or directly:
   `det A = -⟨A, A⟩/2` for traceless `A` and `⟨X₀, P⟩ = 1`. The exponential: `lemmaA_6_4` with
   `det P = -ω² < 0`. Conjugation: `e^{tP} = S diag(e^{-ωt}, e^{ωt}) S⁻¹`, so `Ad e^{tP}` acts by
   `H ↦ H`, `E ↦ u E`, `F ↦ u⁻¹ F`, `u = e^{-2ωt} = e^{-t/ε}` (expand `exp_smul_iso_vfP_one` and
   `Real.cosh_eq`, `Real.sinh_eq` entrywise).
4. (2): `iso_vfX 1 q t = e^{tP} X₀ e^{-tP}` (`constControlX`) and steps 2–3; the `ρ`'s from the
   components (`ρ₁ = -x_h`, `ρ₂ = -x_e/2 - ρ₁`, `ρ₀ = 2 x_f - ρ₁`).
5. (3): `ρ₁(t) = ε > 0`, `ρ₀(t) ≥ ρ₀(0) > 0` for `t ≥ 0` (`Y' e^{t/ε} ≥ Y' > 1`); trace and
   determinant are preserved by conjugation; `ρ₂(t) > 0 ⟺ e^{-t/ε} > 1/Y ⟺ t < ε log Y`
   (`Y > 1`). `ρ₂(T) = ε(Y/Y - 1) = 0`; `ρ₂'(t) = -Y e^{-t/ε} = -1` at `t = T`.
6. (4): with `X₀ = Φ(x, y)` (`y > 0`), `iso_vfX_one_eq` and the entries of `Φ`: both sides are
   `[[x'/y', -(x'² + y'²)/y'], [1/y', -x'/y']]` for `x' = 1/√3 + u(x - 1/√3)`, `y' = u y`;
   `ε = ρ₁(Φ(x, y)) = (1 - √3 x)/(√3 y)`; entrywise `field_simp`, `ring`. (Geometrically:
   the Möbius action of `e^{tZ_{e₂}}` fixes `1/√3` and `∞`.)

Checked numerically against a literal model of the Lean definitions (`notes/n4f/check1.py`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-! ### The frame (proof.md §1.1) -/

/-- The frame matrix `S = [[1, 1], [0, √3]]` (proof.md §1.1): `S⁻¹ Z_{e₂} S = H/√3`. -/
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

/-- **A section point** (proof.md §1.1): a point of Chapter 7's Poincaré section `N_{9/4}`
(`X, Λ₁, Λ_R` traceless, `det X = 1`, `⟨X, Λ_R⟩ = 0`, `H(e₃) = 0`, `χ₂₃ = 0`, `det Λ₁ = 9/4`) whose
state is a star state. On it `H(e₂) = H(e₃) = 0`. -/
def IsArcSectionPt (q : iso_PhasePt) : Prop := q ∈ iso_sectionN (9 / 4) ∧ IsStarState q.1

/-- **The cleared switching numerator** `N_ij = ⟨Λ_R, Z_j⟩⟨X, Z_i⟩ - ⟨Λ_R, Z_i⟩⟨X, Z_j⟩`
(proof.md §1.1), `Z_k = Z_{e_k}`; it is `χ_ij ⟨X, Z_i⟩⟨X, Z_j⟩` (`switchingNum_eq`). -/
noncomputable def switchingNum (i j : Fin 3) (q : iso_PhasePt) : ℝ :=
  traceForm q.2.2 (controlMatrix (vertex j)) * traceForm q.1 (controlMatrix (vertex i)) -
    traceForm q.2.2 (controlMatrix (vertex i)) * traceForm q.1 (controlMatrix (vertex j))

/-- `ε = ρ₁(X₀)`, the constant value of `ρ₁` along the `e₂`-arc from `q`. -/
noncomputable def arcEps (q : iso_PhasePt) : ℝ := ρ₁ q.1

/-- `Y = 1 + ρ₂(X₀)/ε` (proof.md (1.3)). -/
noncomputable def arcY (q : iso_PhasePt) : ℝ := 1 + ρ₂ q.1 / ρ₁ q.1

/-- `Y' = 1 + ρ₀(X₀)/ε` (proof.md (1.3)). -/
noncomputable def arcY' (q : iso_PhasePt) : ℝ := 1 + ρ₀ q.1 / ρ₁ q.1

/-- **The exit time** `T = ε log Y` of the `e₂`-arc from `q` (Proposition 1.1 (3)). -/
noncomputable def arcExitTime (q : iso_PhasePt) : ℝ := ρ₁ q.1 * Real.log (arcY q)

/-! ### Frame identities, (1.1) and (1.2) -/

/-- `ofFrame h e f = S [[h, e], [f, -h]] S⁻¹`. -/
theorem ofFrame_eq_conj (h e f : ℝ) :
    ofFrame h e f = arcFrameS * !![h, e; f, -h] * arcFrameS⁻¹ := by
  sorry

@[simp] theorem frameH_ofFrame (h e f : ℝ) : frameH (ofFrame h e f) = h := by
  sorry

@[simp] theorem frameE_ofFrame (h e f : ℝ) : frameE (ofFrame h e f) = e := by
  sorry

@[simp] theorem frameF_ofFrame (h e f : ℝ) : frameF (ofFrame h e f) = f := by
  sorry

/-- A traceless matrix is `ofFrame` of its components. -/
theorem ofFrame_frame {M : Mat2} (hM : M.trace = 0) :
    ofFrame (frameH M) (frameE M) (frameF M) = M := by
  sorry

theorem trace_ofFrame (h e f : ℝ) : (ofFrame h e f).trace = 0 := by
  sorry

/-- `det(h H + e E + f F) = -(h² + e f)`. -/
theorem det_ofFrame (h e f : ℝ) : (ofFrame h e f).det = -(h ^ 2 + e * f) := by
  sorry

/-- The trace form in the frame: `⟨M, N⟩ = 2 m_h n_h + m_e n_f + m_f n_e`. -/
theorem traceForm_ofFrame (h e f h' e' f' : ℝ) :
    traceForm (ofFrame h e f) (ofFrame h' e' f') = 2 * h * h' + e * f' + f * e' := by
  sorry

/-- The bracket in the frame: `[aH + bE + cF, a'H + b'E + c'F] =
(bc' - cb') H + 2(ab' - ba') E + 2(ca' - ac') F`. -/
theorem ofFrame_mul_sub (h e f h' e' f' : ℝ) :
    ofFrame h e f * ofFrame h' e' f' - ofFrame h' e' f' * ofFrame h e f =
      ofFrame (e * f' - f * e') (2 * (h * e' - e * h')) (2 * (f * h' - h * f')) := by
  sorry

/-- **(1.2)**: `Z_{e₁} = (F - H)/√3`, `Z_{e₂} = H/√3`, `Z_{e₃} = -(H + 4E)/√3`,
`J = (-H - 4E + F)/√3` in the frame. -/
theorem frame_controlMatrix :
    controlMatrix (vertex 0) = ofFrame (-(1 / √3)) 0 (1 / √3) ∧
      controlMatrix (vertex 1) = ofFrame (1 / √3) 0 0 ∧
      controlMatrix (vertex 2) = ofFrame (-(1 / √3)) (-(4 / √3)) 0 ∧
      J = ofFrame (-(1 / √3)) (-(4 / √3)) (1 / √3) := by
  sorry

/-- **(1.1)**: for traceless `X`, `⟨X, Z_{e₁}⟩ = -(2/√3) ρ₂`, `⟨X, Z_{e₂}⟩ = -(2/√3) ρ₁`,
`⟨X, Z_{e₃}⟩ = -(2/√3) ρ₀`. -/
theorem traceForm_controlMatrix_vertex {X : Mat2} (hX : X.trace = 0) :
    traceForm X (controlMatrix (vertex 0)) = -(2 / √3) * ρ₂ X ∧
      traceForm X (controlMatrix (vertex 1)) = -(2 / √3) * ρ₁ X ∧
      traceForm X (controlMatrix (vertex 2)) = -(2 / √3) * ρ₀ X := by
  sorry

/-- **(1.1)**: `Z_{e₁} + Z_{e₂} + Z_{e₃} = J`. -/
theorem controlMatrix_vertex_add :
    controlMatrix (vertex 0) + controlMatrix (vertex 1) + controlMatrix (vertex 2) = J := by
  sorry

/-- **(1.1)**: `ρ₀ρ₁ + ρ₁ρ₂ + ρ₂ρ₀ = det X` for traceless `X` (`= 1` on the states). -/
theorem ρ_mul_add {X : Mat2} (hX : X.trace = 0) :
    ρ₀ X * ρ₁ X + ρ₁ X * ρ₂ X + ρ₂ X * ρ₀ X = X.det := by
  sorry

/-! ### The cleared switching numerators -/

/-- `N_ij = χ_ij ⟨X, Z_i⟩⟨X, Z_j⟩` where both pairings are nonzero. -/
theorem switchingNum_eq (i j : Fin 3) (q : iso_PhasePt)
    (hi : traceForm q.1 (controlMatrix (vertex i)) ≠ 0)
    (hj : traceForm q.1 (controlMatrix (vertex j)) ≠ 0) :
    switchingNum i j q = switchingFn i j q.2.2 q.1 *
      (traceForm q.1 (controlMatrix (vertex i)) * traceForm q.1 (controlMatrix (vertex j))) := by
  sorry

/-- In the star domain `χ_ij > 0` iff `N_ij > 0` (the factor `⟨X, Z_i⟩⟨X, Z_j⟩` is positive by
(1.1)). -/
theorem switchingFn_pos_iff (i j : Fin 3) {q : iso_PhasePt} (hX : IsStarState q.1) :
    0 < switchingFn i j q.2.2 q.1 ↔ 0 < switchingNum i j q := by
  sorry

/-- In the star domain `χ_ij < 0` iff `N_ij < 0`. -/
theorem switchingFn_neg_iff (i j : Fin 3) {q : iso_PhasePt} (hX : IsStarState q.1) :
    switchingFn i j q.2.2 q.1 < 0 ↔ switchingNum i j q < 0 := by
  sorry

/-- In the star domain `χ_ij = 0` iff `N_ij = 0`. -/
theorem switchingFn_eq_zero_iff (i j : Fin 3) {q : iso_PhasePt} (hX : IsStarState q.1) :
    switchingFn i j q.2.2 q.1 = 0 ↔ switchingNum i j q = 0 := by
  sorry

/-! ### (1.3) and the frame of the initial state -/

variable {q : iso_PhasePt}

theorem arcEps_pos (hX : IsStarState q.1) : 0 < arcEps q := by
  sorry

theorem one_lt_arcY (hX : IsStarState q.1) : 1 < arcY q := by
  sorry

theorem one_lt_arcY' (hX : IsStarState q.1) : 1 < arcY' q := by
  sorry

/-- **(1.3)**: `ε² Y Y' = 1 + ε²`. -/
theorem arcEps_sq_mul_arcY_mul_arcY' (hX : IsStarState q.1) :
    arcEps q ^ 2 * arcY q * arcY' q = 1 + arcEps q ^ 2 := by
  sorry

/-- **The initial state in the frame** (Proposition 1.1 (1)): `X₀ = -ε H + x_e E + x_f F` with
`x_e = -2εY`, `x_f = εY'/2`, and `x_e x_f = -(1 + ε²)` (`det X₀ = 1`). -/
theorem frame_state (hX : IsStarState q.1) :
    frameH q.1 = -arcEps q ∧ frameE q.1 = -2 * arcEps q * arcY q ∧
      frameF q.1 = arcEps q * arcY' q / 2 ∧ frameE q.1 * frameF q.1 = -(1 + arcEps q ^ 2) := by
  sorry

/-- **The chart radius** `r = X₁₁ = (ρ₀ - ρ₁)/2 = ε (Y' - 2)/2` (proof.md Theorem 2.1). -/
theorem X00_eq_arcRadius (hX : q.1.trace = 0) (hε : ρ₁ q.1 ≠ 0) :
    q.1 0 0 = arcEps q * (arcY' q - 2) / 2 := by
  sorry

/-! ### Proposition 1.1: the state along the `e₂`-arc -/

/-- **Proposition 1.1 (1)**: `P = Z_{e₂}/⟨Z_{e₂}, X₀⟩ = -ω H`, `ω = 1/(2ε)`. -/
theorem iso_vfP_one_eq (hX : IsStarState q.1) :
    iso_vfP 1 q = ofFrame (-(1 / (2 * arcEps q))) 0 0 := by
  sorry

/-- **Proposition 1.1 (1)**: `P² = ω² I`. -/
theorem iso_vfP_one_mul_self (hX : IsStarState q.1) :
    iso_vfP 1 q * iso_vfP 1 q = (1 / (2 * arcEps q)) ^ 2 • (1 : Mat2) := by
  sorry

/-- **Proposition 1.1 (1)**: `det P = -1/(4ρ₁²)` and `det(X₀ + P) = det P`. -/
theorem det_iso_vfP_one (hX : IsStarState q.1) :
    (iso_vfP 1 q).det = -1 / (4 * arcEps q ^ 2) ∧
      (q.1 + iso_vfP 1 q).det = (iso_vfP 1 q).det := by
  sorry

/-- **Proposition 1.1 (1)**: `e^{tP} = cosh(ωt) I + ω⁻¹ sinh(ωt) P`, `ω = 1/(2ε)`. -/
theorem exp_smul_iso_vfP_one (hX : IsStarState q.1) (t : ℝ) :
    NormedSpace.exp (t • iso_vfP 1 q) =
      Real.cosh (t / (2 * arcEps q)) • (1 : Mat2) +
        (2 * arcEps q * Real.sinh (t / (2 * arcEps q))) • iso_vfP 1 q := by
  sorry

/-- **Proposition 1.1 (1)**: `Ad e^{tP}` in the frame fixes `H` and multiplies `E`, `F` by
`u = e^{-t/ε}` and `u⁻¹`. -/
theorem exp_conj_ofFrame (hX : IsStarState q.1) (t h e f : ℝ) :
    NormedSpace.exp (t • iso_vfP 1 q) * ofFrame h e f * NormedSpace.exp (-t • iso_vfP 1 q) =
      ofFrame h (Real.exp (-t / arcEps q) * e) (Real.exp (t / arcEps q) * f) := by
  sorry

/-- **Proposition 1.1 (2)**: `X(t) = -ε H + x_e u E + x_f u⁻¹ F`, `u = e^{-t/ε}`. -/
theorem iso_vfX_one_eq (hX : IsStarState q.1) (t : ℝ) :
    iso_vfX 1 q t = ofFrame (-arcEps q) (-2 * arcEps q * arcY q * Real.exp (-t / arcEps q))
      (arcEps q * arcY' q / 2 * Real.exp (t / arcEps q)) := by
  sorry

/-- **Proposition 1.1 (2)**: `ρ₁(t) = ε`, `ρ₂(t) = ε(Y e^{-t/ε} - 1)`, `ρ₀(t) = ε(Y' e^{t/ε} - 1)`
along the `e₂`-arc. -/
theorem ρ_iso_vfX_one (hX : IsStarState q.1) (t : ℝ) :
    ρ₁ (iso_vfX 1 q t) = arcEps q ∧
      ρ₂ (iso_vfX 1 q t) = arcEps q * (arcY q * Real.exp (-t / arcEps q) - 1) ∧
      ρ₀ (iso_vfX 1 q t) = arcEps q * (arcY' q * Real.exp (t / arcEps q) - 1) := by
  sorry

/-- The exit time is positive. -/
theorem arcExitTime_pos (hX : IsStarState q.1) : 0 < arcExitTime q := by
  sorry

/-- **Proposition 1.1 (3)**: for `t ≥ 0`, `X(t)` is a star state iff `t < T = ε log Y`: the arc
leaves `𝔥*` exactly at `T`, through `ρ₂ = 0` (`ρ₁` is constant and `ρ₀` increases). -/
theorem isStarState_iso_vfX_one_iff (hX : IsStarState q.1) {t : ℝ} (ht : 0 ≤ t) :
    IsStarState (iso_vfX 1 q t) ↔ t < arcExitTime q := by
  sorry

/-- **Proposition 1.1 (3)**: `ρ₂(X(T)) = 0`. -/
theorem ρ₂_iso_vfX_one_arcExitTime (hX : IsStarState q.1) :
    ρ₂ (iso_vfX 1 q (arcExitTime q)) = 0 := by
  sorry

/-- **Proposition 1.1 (3)**: `ρ₂'(T) = -1` (the transversal exit, the "`-1.000`" of the numerical
check). -/
theorem hasDerivAt_ρ₂_iso_vfX_one (hX : IsStarState q.1) :
    HasDerivAt (fun t ↦ ρ₂ (iso_vfX 1 q t)) (-1) (arcExitTime q) := by
  sorry

/-- **Proposition 1.1 (4)**: in the upper half-plane (`X₀ = Φ(z)`, `z = x + iy`),
`z(t) - 1/√3 = e^{-t/ε} (z(0) - 1/√3)`: the state runs along a Euclidean ray into the cusp `1/√3`
of the ideal triangle `𝔥*`, at the angle fixed by `ρ₁ = ε`. -/
theorem iso_vfX_one_Φ (hX : IsStarState q.1) {x y : ℝ} (hy : 0 < y) (hq : q.1 = Φ x y) (t : ℝ) :
    iso_vfX 1 q t = Φ (1 / √3 + Real.exp (-t / arcEps q) * (x - 1 / √3))
      (Real.exp (-t / arcEps q) * y) := by
  sorry

end SmoothedPolygons
