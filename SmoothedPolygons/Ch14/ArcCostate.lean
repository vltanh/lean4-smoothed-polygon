module

public import SmoothedPolygons.Ch14.ArcFrame
import SmoothedPolygons.Ch7.Isolated.VertexFlow

/-!
# Chapter 14, N4: the costate along an `e₂`-arc (Lemma 1.2 and the quadratures)

Part of the formalization's proof of N4 (`UnstableCurveLeavesStarDomain`, Figure 14.2) without
computer assistance. **Departure from the paper**, by the user's decision: the book reads N4 off a
computed figure (Figure 14.2, TeX 11951–11991; REPORT.md E88); the formalization proves it from
the exact structure of the Reinhardt flow along an `e₂`-arc and an invariant region (see
`SmoothedPolygons/Ch14/ArcParams.lean`, and `SmoothedPolygons/Ch14/ArcRegionInvariant.lean` for
the numbering of the steps).

This file is §1.3, first half: the nilpotent eigenvectors `V_e`, `V_f` of `ad(X₀ + P)`
(Lemma 1.2), the closed form of `M(t)` and `c(t)` (`iso_vfM`, `iso_vfC`), and the two scalar
functions `φ_e`, `φ_f` whose derivatives are pairings of `M(t)` with `V_e`, `V_f`. The normal form
of the cleared switching numerators (Theorem 1.3, `SmoothedPolygons/Ch14/ArcNormalForm.lean`)
integrates these. It also holds INV (1.4), the costate in a moving eigenbasis
(`iso_vfΛ₁_one_eq`).

## Notation

`q = (X₀, Λ₁(0), Λ_R(0))` with `X₀` a star state, `ε = ρ₁(X₀)`, `ω = 1/(2ε)`, `u = e^{-t/ε}`,
`P = iso_vfP 1 q = -ω H` (`iso_vfP_one_eq`), `A = X₀ + P`, `X₀ = -ε H + x_e E + x_f F`
(`frame_state`: `x_e = -2εY`, `x_f = εY'/2`, `x_e x_f = -(1 + ε²)`). The closed form of Chapter 7:
`M(t) = e^{-tP}(Λ₁(t) + (3/2) J) e^{tP}` (`iso_vfM`), `c(t) = ⟨Λ_R(t), P⟩` (`iso_vfC`,
`ivf_vfC_eq`), `Λ̃(t) = e^{-tP} Λ_R(t) e^{tP} = Λ_R(0) - (∫₀ᵗ c)[P, X₀] - ∫₀ᵗ [M, X₀]`
(`arcLamTilde`, from `iso_vfΛR`).

## Statements

* **Lemma 1.2** (`arcVe`, `arcVf`, `trace_arcVe`, `det_arcVe`, …, `commutator_arcVe`,
  `commutator_arcVf`, `exp_conj_arcVe`, `exp_conj_arcVf`): the nilpotent matrices
  `V_e = x_e H - 2ω x_e² E + ε F`, `V_f = x_f H + ε E - 2ω x_f² F` satisfy `[A, V_e] = -2ω V_e`,
  `[A, V_f] = 2ω V_f`, hence `e^{tA} V_e e^{-tA} = u V_e`, `e^{tA} V_f e^{-tA} = u⁻¹ V_f`.
* `iso_vfM_eq` (any vertex): `M(t) = e^{-tA} Λ₁(0) e^{tA} + (3/2) e^{-tP} J e^{tP}`.
* `iso_vfC_eq_sub` (any vertex): `c(t) = ⟨M(t), X₀⟩ - H_m(q)`; on `H(e₂) = 0`, `c = ⟨M, X₀⟩`.
* `switchingNum_iso_vertexFlow_one`: with `φ_e = Λ̃_e - x_e c`, `φ_f = Λ̃_f - x_f c` (frame
  components; `arcPhiE`, `arcPhiF`), `N₂₁(t) = -(2ε/3) u φ_e(t)` and `N₂₃(t) = (8ε/3) u⁻¹ φ_f(t)`.
* `hasDerivAt_arcPhiE`, `hasDerivAt_arcPhiF` (on `H(e₂) = 0`): `φ_e' = -2⟨M, V_e⟩`,
  `φ_f' = 2⟨M, V_f⟩`.
* `traceForm_iso_vfM_arcVe`, `traceForm_iso_vfM_arcVf`:
  `⟨M(t), V_e⟩ = u ⟨Λ₁(0), V_e⟩ - (√3/2)(2x_e + x_e² u/ε + 4ε/u)` and
  `⟨M(t), V_f⟩ = u⁻¹ ⟨Λ₁(0), V_f⟩ + (√3/2)(-2x_f + ε u + 4x_f²/(ε u))`.
* `iso_vfΛ₁_one_eq` (INV (1.4), the first step of INV Theorem 1): the costate has
  constant coefficients in the moving eigenbasis,
  `Λ₁(t) = α (X(t) + P) + β u⁻² V_e(X(t)) + γ u² V_f(X(t))`, `α = 2ε² ⟨Λ₁(0), X₀ + P⟩`,
  `β = ε² ⟨Λ₁(0), V_f⟩`, `γ = ε² ⟨Λ₁(0), V_e⟩`. On a section point the coefficients are explicit
  in the parameters (`iso_vfΛ₁_one_eq_arcParams`, `SmoothedPolygons/Ch14/ArcPoincareMap.lean`);
  this gives the parameters of the image without the quadratures and without Lemma 2.3.

## Proofs (the route, §1.3)

1. Lemma 1.2: `A = -(ε + ω) H + x_e E + x_f F` (`iso_vfP_one_eq`, `frame_state`); by
   `ofFrame_mul_sub` the `H`, `E`, `F` coefficients of `[A, V_e]` are
   `ε x_e + 2ω x_e² x_f = -2ω x_e`,
   `2x_e²(2ω(ε + ω) - 1) = 4ω² x_e²`, `2(x_e x_f + ε(ε + ω)) = -1 = -2ωε`, using
   `x_e x_f = -(1 + ε²)` and `2ωε = 1`; the same for `V_f`. `det = -(h² + e f) = 0`
   (`det_ofFrame`). The conjugation (`exp_conj_eq_of_commutator_eq_smul`): if `[A, V] = μ V`, then
   `t ↦ e^{-tμ} e^{tA} V e^{-tA}` has entrywise derivative `0`, so it is constant
   (`is_const_of_deriv_eq_zero`) and `e^{tA} V e^{-tA} = e^{tμ} V`; with `μ = ∓2ω = ∓1/ε` this
   gives `u V_e` and `u⁻¹ V_f`.
2. `iso_vfM_eq`: `Λ₁(s) = g⁻¹ Λ₁(0) g` with `g = e^{sA} e^{-sP}` (`iso_vfΛ₁`, `iso_vfG`,
   `constControlG`), so `e^{-sP} Λ₁(s) e^{sP} = e^{-sA} Λ₁(0) e^{sA}`
   (`NormedSpace.exp` of `s • B` and `-s • B` are inverse: `Matrix.exp_neg_smul_mul_exp_smul`).
3. `iso_vfC_eq_sub`: `H_m(flow t) = H_m(q)` (`hamiltonian_vertexFlow`); by
   `hamiltonian_eq_traceForm_sub`, `H_m(flow t) = ⟨Λ̂(t), X(t)⟩ - ⟨Λ_R(t), P⟩` with
   `controlP (vertex m) X(t) = P` (`ivf_controlP_vfX`); `⟨Λ̂(t), X(t)⟩ = ⟨M(t), X₀⟩` (conjugation
   invariance of the trace form); `⟨Λ_R(t), P⟩ = c(t)` (`ivf_vfC_eq`).
4. `switchingNum_iso_vertexFlow_one`: `⟨X(t), Z_{e₂}⟩ = ⟨X₀, Z_{e₂}⟩ = -2ε/√3`, and
   `⟨Λ_R, Z_{e₂}⟩ = c ⟨X, Z_{e₂}⟩`, so `N₂₁ = ⟨X, Z_{e₂}⟩ (⟨Λ_R, Z_{e₁}⟩ - c ⟨X, Z_{e₁}⟩)`. By
   `exp_conj_ofFrame` and (1.2), `e^{-tP} Z_{e₁} e^{tP} = (u F - H)/√3`, and
   `c = ⟨Λ̃, P⟩ = -2ω Λ̃_h`; with `X(t) = -εH + x_e u E + x_f u⁻¹ F` this gives
   `⟨Λ_R, Z_{e₁}⟩ - c⟨X, Z_{e₁}⟩ = (1/√3)(u Λ̃_e - 2Λ̃_h + 2ω Λ̃_h(x_e u + 2ε)) = (u/√3) φ_e`.
   Likewise `e^{-tP} Z_{e₃} e^{tP} = -(H + 4u⁻¹ E)/√3` and
   `⟨Λ_R, Z_{e₃}⟩ - c⟨X, Z_{e₃}⟩ = -(4u⁻¹/√3) φ_f`. This needs `Λ_R(0)` traceless (so that `Λ̃` is
   `ofFrame` of its components, `ofFrame_frame`); the frame components of a matrix with nonzero
   trace are not the pairings used here (checked numerically at a generic point).
5. `hasDerivAt_arcPhiE`: `arcLamTilde q t = Λ_R(0) - (∫₀ᵗ c)[P, X₀] - ∫₀ᵗ [M, X₀]` (the
   exponentials in `iso_vfΛR` cancel), so by the fundamental theorem of calculus
   (`intervalIntegral.integral_hasDerivAt_right`, continuity: `ivf_vfC_continuous`,
   `ivf_vfM_continuous`) `Λ̃' = -c [P, X₀] - [M, X₀]` and `c' = -⟨M, [X₀, P]⟩`. In the frame
   `[P, X₀] = -2ω x_e E + 2ω x_f F`, `[M, X₀]_e = 2 m_h x_e + 2ε m_e`,
   `c' = 2ω(x_f m_e - x_e m_f)`, and, by step 3 with `H(e₂) = 0`,
   `c = ⟨M, X₀⟩ = -2ε m_h + x_f m_e + x_e m_f`. Substituting and using `x_e x_f = -(1 + ε²)`,
   `2ωε = 1`, everything collapses to `φ_e' = -4x_e m_h - 2ε m_e + 4ω x_e² m_f = -2⟨M, V_e⟩`;
   the same computation gives `φ_f' = 2⟨M, V_f⟩`. (Without `H(e₂) = 0` there is an extra term
   `-2ω x_e H(e₂)`: the four-term form of Theorem 1.3 survives but not its universal coefficients.)
6. `traceForm_iso_vfM_arcVe`: step 2 and step 1: `⟨e^{-tA} Λ₁(0) e^{tA}, V_e⟩ =
   ⟨Λ₁(0), e^{tA} V_e e^{-tA}⟩ = u ⟨Λ₁(0), V_e⟩`; `e^{tP} V_e e^{-tP} = x_e H - 2ω x_e² u E +
   ε u⁻¹ F` (`exp_conj_ofFrame`), and `⟨J, a H + b E + c F⟩ = (-2a + b - 4c)/√3` ((1.2),
   `traceForm_ofFrame`). The same for `V_f` (`e^{tP} V_f e^{-tP} = x_f H + ε u E - 2ω x_f² u⁻¹ F`).
7. `iso_vfΛ₁_one_eq` (INV Theorem 1 (i)): see its docstring.

All of these were also checked numerically, while the statements were written, against a literal
model of the Lean definitions (matrix exponentials, the quadratures of `iso_vfC` and `iso_vfΛR`
by numerical integration); the proofs do not depend on these checks.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- **`V_e`** (Lemma 1.2): `x_e H - 2ω x_e² E + ε F` in the frame of `X₀`, `ω = 1/(2ε)`,
`x_e = frameE X₀`, `ε = ρ₁(X₀)`. -/
noncomputable def arcVe (X : Mat2) : Mat2 := ofFrame (frameE X) (-(frameE X) ^ 2 / ρ₁ X) (ρ₁ X)

/-- **`V_f`** (Lemma 1.2): `x_f H + ε E - 2ω x_f² F` in the frame of `X₀`, `x_f = frameF X₀`. -/
noncomputable def arcVf (X : Mat2) : Mat2 := ofFrame (frameF X) (ρ₁ X) (-(frameF X) ^ 2 / ρ₁ X)

/-- `Λ̃(t) = e^{-tP} Λ_R(t) e^{tP}`, `P = iso_vfP 1 q`: the costate `Λ_R` of the `e₂`-flow in the
frame rotating with `e^{tP}`. -/
noncomputable def arcLamTilde (q : iso_PhasePt) (t : ℝ) : Mat2 :=
  NormedSpace.exp (-t • iso_vfP 1 q) * iso_vfΛR 1 q t * NormedSpace.exp (t • iso_vfP 1 q)

/-- `φ_e(t) = Λ̃_e(t) - x_e c(t)` (proof of Theorem 1.3): `N₂₁(t) = -(2ε/3) u φ_e(t)`. -/
noncomputable def arcPhiE (q : iso_PhasePt) (t : ℝ) : ℝ :=
  frameE (arcLamTilde q t) - frameE q.1 * iso_vfC 1 q t

/-- `φ_f(t) = Λ̃_f(t) - x_f c(t)` (proof of Theorem 1.3): `N₂₃(t) = (8ε/3) u⁻¹ φ_f(t)`. -/
noncomputable def arcPhiF (q : iso_PhasePt) (t : ℝ) : ℝ :=
  frameF (arcLamTilde q t) - frameF q.1 * iso_vfC 1 q t

variable {q : iso_PhasePt}

/-! ### Frame and trace-form helpers -/

private lemma traceForm_add_left (A B C : Mat2) :
    traceForm (A + B) C = traceForm A C + traceForm B C := by
  simp only [traceForm, Matrix.add_mul, Matrix.trace_add]

private lemma traceForm_smul_right (c : ℝ) (A C : Mat2) :
    traceForm A (c • C) = c * traceForm A C := by
  simp only [traceForm, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- `⟨E L F, Z⟩ = ⟨L, F Z E⟩`. -/
private lemma traceForm_conj_left (E L F Z : Mat2) :
    traceForm (E * L * F) Z = traceForm L (F * Z * E) := by
  unfold traceForm
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm E]
  simp only [Matrix.mul_assoc]

/-- `⟨A, E X F⟩ = ⟨F A E, X⟩`. -/
private lemma traceForm_conj_right (A E X F : Mat2) :
    traceForm A (E * X * F) = traceForm (F * A * E) X := by
  unfold traceForm
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm F]
  simp only [Matrix.mul_assoc]

/-- `F (E X F) E = X` when `F E = 1`. -/
private lemma conj_cancel_of_mul_eq_one {E F : Mat2} (h : F * E = 1) (X : Mat2) :
    F * (E * X * F) * E = X := by
  calc F * (E * X * F) * E = (F * E) * X * (F * E) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [h, Matrix.one_mul, Matrix.mul_one]

/-- Every matrix is `ofFrame a b c + d • 1`. -/
private lemma exists_eq_ofFrame_add_smul_one (M : Mat2) :
    ∃ a b c d : ℝ, M = ofFrame a b c + d • (1 : Mat2) := by
  refine ⟨frameH (M - (M.trace / 2) • (1 : Mat2)), frameE (M - (M.trace / 2) • (1 : Mat2)),
    frameF (M - (M.trace / 2) • (1 : Mat2)), M.trace / 2, ?_⟩
  rw [ofFrame_frame, sub_add_cancel]
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  simp

private lemma commutator_add_smul_one_left (N X : Mat2) (d : ℝ) :
    (N + d • (1 : Mat2)) * X - X * (N + d • (1 : Mat2)) = N * X - X * N := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]
  abel

private lemma traceForm_add_smul_one (N Y : Mat2) (d : ℝ) :
    traceForm (N + d • (1 : Mat2)) Y = traceForm N Y + d * Y.trace := by
  simp only [traceForm, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, smul_eq_mul]

/-- `(3/2) ⟨J, h H + e E + f F⟩ = (√3/2)(-2h + e - 4f)` ((1.2)). -/
private lemma three_halves_mul_traceForm_J_ofFrame (h e f : ℝ) :
    (3 / 2 : ℝ) * traceForm J (ofFrame h e f) = √3 / 2 * (-2 * h + e - 4 * f) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h0 : √3 ≠ 0 := by positivity
  simp [traceForm, J, ofFrame, Matrix.trace_fin_two]
  field_simp
  linear_combination (f - e + 2 * h) * h3

/-- The entrywise derivative passes to `frameE`. -/
private lemma hasDerivAt_frameE {f : ℝ → Mat2} {f' : Mat2} {t : ℝ}
    (h : Matrix.HasDerivAtEntrywise f f' t) :
    HasDerivAt (fun s ↦ frameE (f s)) (frameE f') t := by
  unfold frameE
  exact (((h 0 1).const_mul √3).add ((h 0 0).const_mul 2)).sub ((h 1 0).div_const √3)

/-- The entrywise derivative passes to `frameF`. -/
private lemma hasDerivAt_frameF {f : ℝ → Mat2} {f' : Mat2} {t : ℝ}
    (h : Matrix.HasDerivAtEntrywise f f' t) :
    HasDerivAt (fun s ↦ frameF (f s)) (frameF f') t := by
  unfold frameF
  exact (h 1 0).div_const √3

/-- If `[A, V] = μ V`, then `e^{tA} V e^{-tA} = e^{tμ} V`: `t ↦ e^{-tμ} e^{tA} V e^{-tA}` has
derivative `0`. -/
private lemma exp_conj_eq_of_commutator_eq_smul {A V : Mat2} {μ : ℝ} (h : A * V - V * A = μ • V)
    (t : ℝ) :
    NormedSpace.exp (t • A) * V * NormedSpace.exp (-t • A) = Real.exp (t * μ) • V := by
  set g : ℝ → Mat2 := fun s ↦ Real.exp (-(s * μ)) •
    (NormedSpace.exp (s • A) * V * NormedSpace.exp (-s • A)) with hg
  have hd : ∀ s, Matrix.HasDerivAtEntrywise g 0 s := by
    intro s
    have h1 := ((Matrix.hasDerivAtEntrywise_exp_smul_const A s).mul_const V).mul
      (Matrix.hasDerivAtEntrywise_exp_neg_smul_const' A s)
    have hc : HasDerivAt (fun s ↦ Real.exp (-(s * μ))) (Real.exp (-(s * μ)) * (-μ)) s := by
      simpa using ((hasDerivAt_id s).mul_const μ).neg.exp
    refine (h1.smul hc).congr_deriv ?_
    have hf' : NormedSpace.exp (s • A) * A * V * NormedSpace.exp (-s • A) +
        NormedSpace.exp (s • A) * V * -(A * NormedSpace.exp (-s • A)) =
        μ • (NormedSpace.exp (s • A) * V * NormedSpace.exp (-s • A)) := by
      rw [show NormedSpace.exp (s • A) * A * V * NormedSpace.exp (-s • A) +
          NormedSpace.exp (s • A) * V * -(A * NormedSpace.exp (-s • A)) =
          NormedSpace.exp (s • A) * (A * V - V * A) * NormedSpace.exp (-s • A) by noncomm_ring, h,
        Matrix.mul_smul, Matrix.smul_mul]
    rw [hf', smul_smul, ← add_smul, show Real.exp (-(s * μ)) * μ +
      Real.exp (-(s * μ)) * -μ = 0 by ring, zero_smul]
  have hconst : g t = g 0 := by
    ext i j
    exact is_const_of_deriv_eq_zero (fun s ↦ (hd s i j).differentiableAt)
      (fun s ↦ (hd s i j).deriv) t 0
  have h0 : g 0 = V := by simp [hg]
  have hgt : NormedSpace.exp (t • A) * V * NormedSpace.exp (-t • A) = Real.exp (t * μ) • g t := by
    rw [hg, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  rw [hgt, hconst, h0]

/-- `X₀ = -ε H + x_e E + x_f F`. -/
private lemma state_eq_ofFrame_frame (hX : IsStarState q.1) :
    q.1 = ofFrame (-arcEps q) (frameE q.1) (frameF q.1) := by
  have h := ofFrame_frame hX.1
  rw [(frame_state hX).1] at h
  exact h.symm

/-- `A = X₀ + P = -(ε + ω) H + x_e E + x_f F`. -/
private lemma state_add_iso_vfP_one_eq_ofFrame (hX : IsStarState q.1) :
    q.1 + iso_vfP 1 q = ofFrame (-arcEps q - 1 / (2 * arcEps q)) (frameE q.1) (frameF q.1) := by
  rw [iso_vfP_one_eq hX]
  conv_lhs => rw [state_eq_ofFrame_frame hX]
  rw [ofFrame_add]
  congr 1 <;> ring

private lemma arcVe_eq_ofFrame (X : Mat2) :
    arcVe X = ofFrame (frameE X) (-(frameE X) ^ 2 / ρ₁ X) (ρ₁ X) := rfl

private lemma arcVf_eq_ofFrame (X : Mat2) :
    arcVf X = ofFrame (frameF X) (ρ₁ X) (-(frameF X) ^ 2 / ρ₁ X) := rfl

private lemma arcVe_eq_ofFrame_arcEps (q : iso_PhasePt) :
    arcVe q.1 = ofFrame (frameE q.1) (-(frameE q.1) ^ 2 / arcEps q) (arcEps q) := rfl

private lemma arcVf_eq_ofFrame_arcEps (q : iso_PhasePt) :
    arcVf q.1 = ofFrame (frameF q.1) (arcEps q) (-(frameF q.1) ^ 2 / arcEps q) := rfl

/-- `Ad e^{-tP}` in the frame (`exp_conj_ofFrame` at `-t`). -/
private lemma exp_neg_conj_ofFrame (hX : IsStarState q.1) (t h e f : ℝ) :
    NormedSpace.exp (-t • iso_vfP 1 q) * ofFrame h e f * NormedSpace.exp (t • iso_vfP 1 q) =
      ofFrame h (Real.exp (t / arcEps q) * e) (Real.exp (-t / arcEps q) * f) := by
  have := exp_conj_ofFrame hX (-t) h e f
  simp only [neg_neg] at this
  exact this

/-! ### Lemma 1.2 -/

/-- `V_e` is nilpotent: traceless with determinant `0`. -/
theorem trace_arcVe (X : Mat2) : (arcVe X).trace = 0 := trace_ofFrame _ _ _

/-- `V_e` is nilpotent: traceless with determinant `0`. -/
theorem det_arcVe {X : Mat2} (hε : ρ₁ X ≠ 0) : (arcVe X).det = 0 := by
  rw [arcVe_eq_ofFrame, det_ofFrame]
  field_simp
  ring

/-- `V_f` is nilpotent: traceless with determinant `0`. -/
theorem trace_arcVf (X : Mat2) : (arcVf X).trace = 0 := trace_ofFrame _ _ _

/-- `V_f` is nilpotent: traceless with determinant `0`. -/
theorem det_arcVf {X : Mat2} (hε : ρ₁ X ≠ 0) : (arcVf X).det = 0 := by
  rw [arcVf_eq_ofFrame, det_ofFrame]
  field_simp
  ring

private lemma commutator_arcVe_ofFrame {ε xe xf : ℝ} (hε : ε ≠ 0) (hd : xe * xf = -(1 + ε ^ 2)) :
    ofFrame (-ε - 1 / (2 * ε)) xe xf * ofFrame xe (-xe ^ 2 / ε) ε -
        ofFrame xe (-xe ^ 2 / ε) ε * ofFrame (-ε - 1 / (2 * ε)) xe xf =
      -(1 / ε) • ofFrame xe (-xe ^ 2 / ε) ε := by
  have hxe : xe ≠ 0 := by rintro rfl; nlinarith
  obtain rfl : xf = -(1 + ε ^ 2) / xe := by field_simp; linarith
  rw [ofFrame_mul_sub, smul_ofFrame]
  congr 1 <;> field_simp <;> ring

private lemma commutator_arcVf_ofFrame {ε xe xf : ℝ} (hε : ε ≠ 0) (hd : xe * xf = -(1 + ε ^ 2)) :
    ofFrame (-ε - 1 / (2 * ε)) xe xf * ofFrame xf ε (-xf ^ 2 / ε) -
        ofFrame xf ε (-xf ^ 2 / ε) * ofFrame (-ε - 1 / (2 * ε)) xe xf =
      (1 / ε) • ofFrame xf ε (-xf ^ 2 / ε) := by
  have hxe : xe ≠ 0 := by rintro rfl; nlinarith
  obtain rfl : xf = -(1 + ε ^ 2) / xe := by field_simp; linarith
  rw [ofFrame_mul_sub, smul_ofFrame]
  congr 1 <;> field_simp <;> ring

/-- **Lemma 1.2**: `[X₀ + P, V_e] = -2ω V_e = -(1/ε) V_e`. -/
theorem commutator_arcVe (hX : IsStarState q.1) :
    (q.1 + iso_vfP 1 q) * arcVe q.1 - arcVe q.1 * (q.1 + iso_vfP 1 q) =
      -(1 / arcEps q) • arcVe q.1 := by
  rw [state_add_iso_vfP_one_eq_ofFrame hX]
  exact commutator_arcVe_ofFrame (arcEps_pos hX).ne' (frame_state hX).2.2.2

/-- **Lemma 1.2**: `[X₀ + P, V_f] = 2ω V_f = (1/ε) V_f`. -/
theorem commutator_arcVf (hX : IsStarState q.1) :
    (q.1 + iso_vfP 1 q) * arcVf q.1 - arcVf q.1 * (q.1 + iso_vfP 1 q) =
      (1 / arcEps q) • arcVf q.1 := by
  rw [state_add_iso_vfP_one_eq_ofFrame hX]
  exact commutator_arcVf_ofFrame (arcEps_pos hX).ne' (frame_state hX).2.2.2

/-- **Lemma 1.2**: `e^{tA} V_e e^{-tA} = u V_e`, `A = X₀ + P`, `u = e^{-t/ε}`. -/
theorem exp_conj_arcVe (hX : IsStarState q.1) (t : ℝ) :
    NormedSpace.exp (t • (q.1 + iso_vfP 1 q)) * arcVe q.1 *
        NormedSpace.exp (-t • (q.1 + iso_vfP 1 q)) =
      Real.exp (-t / arcEps q) • arcVe q.1 := by
  rw [exp_conj_eq_of_commutator_eq_smul (commutator_arcVe hX) t]
  congr 2
  ring

/-- **Lemma 1.2**: `e^{tA} V_f e^{-tA} = u⁻¹ V_f`. -/
theorem exp_conj_arcVf (hX : IsStarState q.1) (t : ℝ) :
    NormedSpace.exp (t • (q.1 + iso_vfP 1 q)) * arcVf q.1 *
        NormedSpace.exp (-t • (q.1 + iso_vfP 1 q)) =
      Real.exp (t / arcEps q) • arcVf q.1 := by
  rw [exp_conj_eq_of_commutator_eq_smul (commutator_arcVf hX) t]
  congr 2
  ring

/-! ### `M(t)` and `c(t)` -/

/-- `g(t)⁻¹ = e^{tP} e^{-tA}` for `g(t) = e^{tA} e^{-tP}`. -/
private lemma iso_vfG_inv_eq (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    (iso_vfG m q t)⁻¹ = NormedSpace.exp (t • iso_vfP m q) *
      NormedSpace.exp (-t • (q.1 + iso_vfP m q)) := by
  apply Matrix.inv_eq_left_inv
  unfold iso_vfG constControlG
  calc NormedSpace.exp (t • iso_vfP m q) * NormedSpace.exp (-t • (q.1 + iso_vfP m q)) *
        (NormedSpace.exp (t • (q.1 + iso_vfP m q)) * NormedSpace.exp (-t • iso_vfP m q)) =
      NormedSpace.exp (t • iso_vfP m q) * (NormedSpace.exp (-t • (q.1 + iso_vfP m q)) *
        NormedSpace.exp (t • (q.1 + iso_vfP m q))) * NormedSpace.exp (-t • iso_vfP m q) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [Matrix.exp_neg_smul_mul_exp_smul, Matrix.mul_one, Matrix.exp_smul_mul_exp_neg_smul]

/-- `Λ₁(t) = e^{tP} (e^{-tA} Λ₁(0) e^{tA}) e^{-tP}`. -/
private lemma iso_vfΛ₁_eq_conj (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    iso_vfΛ₁ m q t = NormedSpace.exp (t • iso_vfP m q) *
      (NormedSpace.exp (-t • (q.1 + iso_vfP m q)) * q.2.1 *
        NormedSpace.exp (t • (q.1 + iso_vfP m q))) * NormedSpace.exp (-t • iso_vfP m q) := by
  rw [iso_vfΛ₁, iso_vfG_inv_eq]
  unfold iso_vfG constControlG
  simp only [Matrix.mul_assoc]

/-- `M(t) = e^{-tA} Λ₁(0) e^{tA} + (3/2) e^{-tP} J e^{tP}`, `A = X₀ + P` (§1.3), for every vertex
control. -/
theorem iso_vfM_eq (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    iso_vfM m q t =
      NormedSpace.exp (-t • (q.1 + iso_vfP m q)) * q.2.1 *
          NormedSpace.exp (t • (q.1 + iso_vfP m q)) +
        (3 / 2 : ℝ) •
          (NormedSpace.exp (-t • iso_vfP m q) * J * NormedSpace.exp (t • iso_vfP m q)) := by
  rw [iso_vfM, iso_vfΛ₁_eq_conj, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    conj_cancel_of_mul_eq_one (Matrix.exp_neg_smul_mul_exp_smul _ t)]

/-- `c(t) = ⟨M(t), X₀⟩ - H(e_m)(q)` along the `e_m`-flow (conservation of `H(e_m)`); on
`H(e₂) = 0` this is the identity `c = ⟨M, X₀⟩` of §1.3. -/
theorem iso_vfC_eq_sub (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    iso_vfC m q t = traceForm (iso_vfM m q t) q.1 - phaseHam q (vertex m) := by
  have h := hamiltonian_vertexFlow m q t
  rw [hamiltonian_eq_traceForm_sub] at h
  change traceForm (iso_vfΛ₁ m q t + (3 / 2 : ℝ) • J) (iso_vfX m q t) -
    traceForm (iso_vfΛR m q t) (controlP (vertex m) (iso_vfX m q t)) = phaseHam q (vertex m) at h
  rw [ivf_controlP_vfX, ← ivf_vfC_eq, iso_vfX, constControlX, traceForm_conj_right] at h
  rw [iso_vfM]
  linarith

/-! ### The cleared numerators through `φ_e`, `φ_f` -/

/-- `Λ̃(t) = Λ_R(0) - (∫₀ᵗ c)[P, X₀] - ∫₀ᵗ [M, X₀]` (the exponentials of `iso_vfΛR` cancel). -/
private lemma arcLamTilde_eq_sub_integral (q : iso_PhasePt) (t : ℝ) :
    arcLamTilde q t = q.2.2 - (∫ σ in (0 : ℝ)..t, iso_vfC 1 q σ) •
        (iso_vfP 1 q * q.1 - q.1 * iso_vfP 1 q) -
      Matrix.of fun i j ↦ ∫ s in (0 : ℝ)..t, (iso_vfM 1 q s * q.1 - q.1 * iso_vfM 1 q s) i j := by
  rw [arcLamTilde, iso_vfΛR, conj_cancel_of_mul_eq_one (Matrix.exp_neg_smul_mul_exp_smul _ t)]

/-- `e^{-tB} B e^{tB} = B`. -/
private lemma exp_neg_smul_conj_self (B : Mat2) (t : ℝ) :
    NormedSpace.exp (-t • B) * B * NormedSpace.exp (t • B) = B := by
  rw [← (Matrix.commute_exp_smul B (-t)).eq, Matrix.mul_assoc, Matrix.exp_neg_smul_mul_exp_smul,
    Matrix.mul_one]

/-- `Λ_R(t) = e^{tP} Λ̃(t) e^{-tP}`. -/
private lemma iso_vfΛR_one_eq_conj_arcLamTilde (q : iso_PhasePt) (t : ℝ) :
    iso_vfΛR 1 q t = NormedSpace.exp (t • iso_vfP 1 q) * arcLamTilde q t *
      NormedSpace.exp (-t • iso_vfP 1 q) := by
  rw [arcLamTilde, conj_cancel_of_mul_eq_one (Matrix.exp_smul_mul_exp_neg_smul _ t)]

/-- `tr Λ̃(t) = tr Λ_R(0)`. -/
private lemma trace_arcLamTilde (q : iso_PhasePt) (t : ℝ) :
    (arcLamTilde q t).trace = q.2.2.trace := by
  have hM := ivf_vfM_continuous 1 q
  have hN : Continuous fun s ↦ iso_vfM 1 q s * q.1 - q.1 * iso_vfM 1 q s :=
    (hM.matrix_mul continuous_const).sub (continuous_const.matrix_mul hM)
  have hi : ∀ i j, IntervalIntegrable (fun s ↦ (iso_vfM 1 q s * q.1 - q.1 * iso_vfM 1 q s) i j)
      MeasureTheory.volume 0 t := fun i j ↦ (hN.matrix_elem i j).intervalIntegrable _ _
  have hz : ∀ s, (iso_vfM 1 q s * q.1 - q.1 * iso_vfM 1 q s) 0 0 +
      (iso_vfM 1 q s * q.1 - q.1 * iso_vfM 1 q s) 1 1 = 0 := fun s ↦ by
    rw [← Matrix.trace_fin_two, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  rw [arcLamTilde_eq_sub_integral, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, smul_zero, sub_zero,
    Matrix.trace_fin_two (Matrix.of _)]
  simp only [Matrix.of_apply]
  rw [← intervalIntegral.integral_add (hi 0 0) (hi 1 1)]
  simp only [hz, intervalIntegral.integral_zero, sub_zero]

/-- **The cleared numerators through `φ_e`, `φ_f`** (proof of Theorem 1.3):
`N₂₁(t) = -(2ε/3) e^{-t/ε} φ_e(t)` and `N₂₃(t) = (8ε/3) e^{t/ε} φ_f(t)` along the `e₂`-flow. -/
theorem switchingNum_iso_vertexFlow_one (hX : IsStarState q.1) (hR : q.2.2.trace = 0) (t : ℝ) :
    switchingNum 1 0 (iso_vertexFlow 1 q t) =
        -(2 * arcEps q / 3) * Real.exp (-t / arcEps q) * arcPhiE q t ∧
      switchingNum 1 2 (iso_vertexFlow 1 q t) =
        8 * arcEps q / 3 * Real.exp (t / arcEps q) * arcPhiF q t := by
  have hε : arcEps q ≠ 0 := (arcEps_pos hX).ne'
  have hL := ofFrame_frame ((trace_arcLamTilde q t).trans hR)
  have hpL : ∀ h e f, traceForm (arcLamTilde q t) (ofFrame h e f) =
      2 * frameH (arcLamTilde q t) * h + frameE (arcLamTilde q t) * f +
        frameF (arcLamTilde q t) * e := fun h e f ↦ by
    conv_lhs => rw [← hL]
    exact traceForm_ofFrame _ _ _ _ _ _
  have hpX : ∀ h e f, traceForm q.1 (ofFrame h e f) =
      2 * (-arcEps q) * h + frameE q.1 * f + frameF q.1 * e := fun h e f ↦ by
    conv_lhs => rw [state_eq_ofFrame_frame hX]
    exact traceForm_ofFrame _ _ _ _ _ _
  have hc : arcEps q * iso_vfC 1 q t = -frameH (arcLamTilde q t) := by
    rw [ivf_vfC_eq, iso_vfΛR_one_eq_conj_arcLamTilde, traceForm_conj_left, exp_neg_smul_conj_self,
      iso_vfP_one_eq hX, hpL]
    field_simp
    ring
  have hs : (1 / √3 : ℝ) ^ 2 = 1 / 3 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), one_pow]
  obtain ⟨hZ0, hZ1, hZ2, -⟩ := frame_controlMatrix
  simp only [switchingNum, iso_vertexFlow, iso_vfΛR_one_eq_conj_arcLamTilde, iso_vfX, constControlX,
    traceForm_conj_left, hZ0, hZ1, hZ2, exp_neg_conj_ofFrame hX, hpL, hpX, arcPhiE, arcPhiF]
  constructor
  · linear_combination (-2 * Real.exp (-t / arcEps q) * (arcEps q * frameE (arcLamTilde q t) +
      frameE q.1 * frameH (arcLamTilde q t))) * hs +
      (-(2 / 3) * Real.exp (-t / arcEps q) * frameE q.1) * hc
  · linear_combination (8 * Real.exp (t / arcEps q) * (arcEps q * frameF (arcLamTilde q t) +
      frameF q.1 * frameH (arcLamTilde q t))) * hs +
      (8 / 3 * Real.exp (t / arcEps q) * frameF q.1) * hc

/-- The algebra behind `φ_e' = -2⟨M, V_e⟩`: with `X₀ = -εH + x_e E + x_f F`, `P = -H/(2ε)` and
`c = ⟨M, X₀⟩`, `(-c[P, X₀] - [M, X₀])_e + x_e ⟨M, [X₀, P]⟩ = -2⟨M, V_e⟩` for every `M`. -/
private lemma arcPhiE_deriv_identity (M X : Mat2) {ε xe xf : ℝ} (hε : ε ≠ 0)
    (hX : X = ofFrame (-ε) xe xf) :
    frameE ((0 - traceForm M X • (ofFrame (-(1 / (2 * ε))) 0 0 * X -
          X * ofFrame (-(1 / (2 * ε))) 0 0)) - (M * X - X * M)) -
        xe * -traceForm M (X * ofFrame (-(1 / (2 * ε))) 0 0 - ofFrame (-(1 / (2 * ε))) 0 0 * X) =
      -2 * traceForm M (ofFrame xe (-xe ^ 2 / ε) ε) := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_ofFrame_add_smul_one M
  subst hX
  rw [commutator_add_smul_one_left]
  simp only [ofFrame_mul_sub, traceForm_add_smul_one, traceForm_ofFrame, trace_ofFrame,
    mul_zero, add_zero]
  rw [← ofFrame_zero, smul_ofFrame, ofFrame_sub, ofFrame_sub, frameE_ofFrame]
  field_simp
  ring

/-- The algebra behind `φ_f' = 2⟨M, V_f⟩`. -/
private lemma arcPhiF_deriv_identity (M X : Mat2) {ε xe xf : ℝ} (hε : ε ≠ 0)
    (hX : X = ofFrame (-ε) xe xf) :
    frameF ((0 - traceForm M X • (ofFrame (-(1 / (2 * ε))) 0 0 * X -
          X * ofFrame (-(1 / (2 * ε))) 0 0)) - (M * X - X * M)) -
        xf * -traceForm M (X * ofFrame (-(1 / (2 * ε))) 0 0 - ofFrame (-(1 / (2 * ε))) 0 0 * X) =
      2 * traceForm M (ofFrame xf ε (-xf ^ 2 / ε)) := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_ofFrame_add_smul_one M
  subst hX
  rw [commutator_add_smul_one_left]
  simp only [ofFrame_mul_sub, traceForm_add_smul_one, traceForm_ofFrame, trace_ofFrame,
    mul_zero, add_zero]
  rw [← ofFrame_zero, smul_ofFrame, ofFrame_sub, ofFrame_sub, frameF_ofFrame]
  field_simp
  ring

/-- **The derivatives of `φ_e`, `φ_f`** (proof of Theorem 1.3), on `H(e₂) = 0`:
`φ_e' = -2⟨M, V_e⟩` and `φ_f' = 2⟨M, V_f⟩`. -/
theorem hasDerivAt_arcPhi (hX : IsStarState q.1) (hH : phaseHam q (vertex 1) = 0) (t : ℝ) :
    HasDerivAt (arcPhiE q) (-2 * traceForm (iso_vfM 1 q t) (arcVe q.1)) t ∧
      HasDerivAt (arcPhiF q) (2 * traceForm (iso_vfM 1 q t) (arcVf q.1)) t := by
  have hε : arcEps q ≠ 0 := (arcEps_pos hX).ne'
  have hM := ivf_vfM_continuous 1 q
  have hC := ivf_vfC_continuous 1 q
  have hN : Continuous fun s ↦ iso_vfM 1 q s * q.1 - q.1 * iso_vfM 1 q s :=
    (hM.matrix_mul continuous_const).sub (continuous_const.matrix_mul hM)
  -- `Λ̃' = -c [P, X₀] - [M, X₀]`
  have hI1 : HasDerivAt (fun t ↦ ∫ σ in (0 : ℝ)..t, iso_vfC 1 q σ) (iso_vfC 1 q t) t :=
    (hC.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hI2 : Matrix.HasDerivAtEntrywise (fun t ↦ Matrix.of fun i j ↦
      ∫ s in (0 : ℝ)..t, (iso_vfM 1 q s * q.1 - q.1 * iso_vfM 1 q s) i j)
      (iso_vfM 1 q t * q.1 - q.1 * iso_vfM 1 q t) t := fun i j ↦ by
    simpa only [Matrix.of_apply] using
      ((hN.matrix_elem i j).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hL := ((Matrix.hasDerivAtEntrywise_const q.2.2 t).sub
    (Matrix.hasDerivAtEntrywise_smul_const hI1 (iso_vfP 1 q * q.1 - q.1 * iso_vfP 1 q))).sub hI2
  rw [show (fun t ↦ q.2.2 - (∫ σ in (0 : ℝ)..t, iso_vfC 1 q σ) •
      (iso_vfP 1 q * q.1 - q.1 * iso_vfP 1 q) - Matrix.of fun i j ↦
        ∫ s in (0 : ℝ)..t, (iso_vfM 1 q s * q.1 - q.1 * iso_vfM 1 q s) i j) = arcLamTilde q from
    funext fun t ↦ (arcLamTilde_eq_sub_integral q t).symm] at hL
  -- `c' = -⟨M, [X₀, P]⟩`
  have hg : Continuous fun s ↦
      traceForm (iso_vfM 1 q s) (q.1 * iso_vfP 1 q - iso_vfP 1 q * q.1) :=
    (hM.matrix_mul continuous_const).matrix_trace
  have hc' : HasDerivAt (iso_vfC 1 q)
      (-traceForm (iso_vfM 1 q t) (q.1 * iso_vfP 1 q - iso_vfP 1 q * q.1)) t :=
    (hg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_sub _
  have hcM : iso_vfC 1 q t = traceForm (iso_vfM 1 q t) q.1 := by
    rw [iso_vfC_eq_sub, hH, sub_zero]
  have hq1 := state_eq_ofFrame_frame hX
  refine ⟨((hasDerivAt_frameE hL).sub (hc'.const_mul (frameE q.1))).congr_deriv ?_,
    ((hasDerivAt_frameF hL).sub (hc'.const_mul (frameF q.1))).congr_deriv ?_⟩
  · rw [hcM, iso_vfP_one_eq hX]
    exact arcPhiE_deriv_identity _ _ hε hq1
  · rw [hcM, iso_vfP_one_eq hX]
    exact arcPhiF_deriv_identity _ _ hε hq1

/-- **`⟨M(t), V_e⟩` in closed form** (proof of Theorem 1.3):
`u ⟨Λ₁(0), V_e⟩ - (√3/2)(2x_e + x_e² u/ε + 4ε/u)`, `u = e^{-t/ε}`. -/
theorem traceForm_iso_vfM_arcVe (hX : IsStarState q.1) (t : ℝ) :
    traceForm (iso_vfM 1 q t) (arcVe q.1) =
      Real.exp (-t / arcEps q) * traceForm q.2.1 (arcVe q.1) -
        √3 / 2 * (2 * frameE q.1 + frameE q.1 ^ 2 / arcEps q * Real.exp (-t / arcEps q) +
          4 * arcEps q * Real.exp (t / arcEps q)) := by
  rw [iso_vfM_eq, traceForm_add_left, ivf_traceForm_smul_left, traceForm_conj_left,
    traceForm_conj_left, exp_conj_arcVe hX, traceForm_smul_right, arcVe_eq_ofFrame_arcEps q,
    exp_conj_ofFrame hX, three_halves_mul_traceForm_J_ofFrame]
  ring

/-- **`⟨M(t), V_f⟩` in closed form** (proof of Theorem 1.3):
`u⁻¹ ⟨Λ₁(0), V_f⟩ + (√3/2)(-2x_f + ε u + 4x_f²/(ε u))`. -/
theorem traceForm_iso_vfM_arcVf (hX : IsStarState q.1) (t : ℝ) :
    traceForm (iso_vfM 1 q t) (arcVf q.1) =
      Real.exp (t / arcEps q) * traceForm q.2.1 (arcVf q.1) +
        √3 / 2 * (-2 * frameF q.1 + arcEps q * Real.exp (-t / arcEps q) +
          4 * frameF q.1 ^ 2 / arcEps q * Real.exp (t / arcEps q)) := by
  rw [iso_vfM_eq, traceForm_add_left, ivf_traceForm_smul_left, traceForm_conj_left,
    traceForm_conj_left, exp_conj_arcVf hX, traceForm_smul_right, arcVf_eq_ofFrame_arcEps q,
    exp_conj_ofFrame hX, three_halves_mul_traceForm_J_ofFrame]
  ring

/-! ### The costate in the moving eigenbasis (INV (1.4)) -/

/-- A traceless matrix in the basis `A = X₀ + P`, `V_e`, `V_f` (dual to itself up to the pairings
`⟨A, A⟩ = 1/(2ε²)`, `⟨V_e, V_f⟩ = 1/ε²`, the others `0`). -/
private lemma ofFrame_eq_eigenbasis_sum (lh le lf : ℝ) {ε xe xf : ℝ} (hε : ε ≠ 0)
    (hd : xe * xf = -(1 + ε ^ 2)) :
    ofFrame lh le lf =
      (2 * ε ^ 2 * traceForm (ofFrame lh le lf) (ofFrame (-ε - 1 / (2 * ε)) xe xf)) •
          ofFrame (-ε - 1 / (2 * ε)) xe xf +
        (ε ^ 2 * traceForm (ofFrame lh le lf) (ofFrame xf ε (-xf ^ 2 / ε))) •
          ofFrame xe (-xe ^ 2 / ε) ε +
        (ε ^ 2 * traceForm (ofFrame lh le lf) (ofFrame xe (-xe ^ 2 / ε) ε)) •
          ofFrame xf ε (-xf ^ 2 / ε) := by
  have hxe : xe ≠ 0 := by rintro rfl; nlinarith
  obtain rfl : xf = -(1 + ε ^ 2) / xe := by field_simp; linarith
  simp only [traceForm_ofFrame, smul_ofFrame, ofFrame_add]
  congr 1 <;> field_simp <;> ring

/-- `e^{tB} B e^{-tB} = B`. -/
private lemma exp_smul_conj_self (B : Mat2) (t : ℝ) :
    NormedSpace.exp (t • B) * B * NormedSpace.exp (-t • B) = B := by
  rw [← (Matrix.commute_exp_smul B t).eq, Matrix.mul_assoc, Matrix.exp_smul_mul_exp_neg_smul,
    Matrix.mul_one]

/-- **INV (1.4): the costate along the `e₂`-arc in the moving eigenbasis** (INV Theorem 1 (i)).
For `X₀` a star state and `Λ₁(0)` traceless, with `u = e^{-t/ε}`, `A = X₀ + P`,
`Λ₁(t) = α (X(t) + P) + β u⁻² V_e(X(t)) + γ u² V_f(X(t))`, where `α = 2ε² ⟨Λ₁(0), A⟩`,
`β = ε² ⟨Λ₁(0), V_f⟩` and `γ = ε² ⟨Λ₁(0), V_e⟩`. No quadrature and no logarithm: the costate is
an algebraic function of `u`. On a section point `α, β, γ` are explicit in the parameters
(`iso_vfΛ₁_one_eq_arcParams`, `SmoothedPolygons/Ch14/ArcPoincareMap.lean`).

Route (INV §1, proof of INV Theorem 1 (i)):
1. *The basis.* In the frame `A = ofFrame (-ε - ω) x_e x_f` (`frame_state`, `iso_vfP_one_eq`,
   `ω = 1/(2ε)`), `V_e = ofFrame x_e (-x_e²/ε) ε`, `V_f = ofFrame x_f ε (-x_f²/ε)`; with
   `x_e x_f = -(1 + ε²)` and `traceForm_ofFrame`: `⟨A, A⟩ = 1/(2ε²)`, `⟨V_e, V_f⟩ = 1/ε²`, and
   `⟨A, V_e⟩ = ⟨A, V_f⟩ = ⟨V_e, V_e⟩ = ⟨V_f, V_f⟩ = 0`. So for traceless `Λ₁(0)`
   (`ofFrame_frame`), `Λ₁(0) = α A + β V_e + γ V_f` (compare the three frame components:
   `field_simp`, `ring`, with `x_e = -2εY`, `x_f = εY'/2`, `ε² Y Y' = 1 + ε²`).
2. *The flow.* `Λ₁(t) = g⁻¹ Λ₁(0) g`, `g = e^{tA} e^{-tP}` (`iso_vfΛ₁`, `iso_vfG`, `constControlG`),
   so `Λ₁(t) = e^{tP} (e^{-tA} Λ₁(0) e^{tA}) e^{-tP}` (as in `iso_vfM_eq`:
   `e^{sB} e^{-sB} = 1`).
3. `e^{-tA} A e^{tA} = A`; `e^{-tA} V_e e^{tA} = u⁻¹ V_e`, `e^{-tA} V_f e^{tA} = u V_f`
   (`exp_conj_arcVe`, `exp_conj_arcVf` at `-t`).
4. `Ad e^{tP}` in the frame (`exp_conj_ofFrame`): `A ↦ ofFrame (-ε - ω) (u x_e) (u⁻¹ x_f) =
   X(t) + P` (`iso_vfX_one_eq`); `V_e ↦ ofFrame x_e (-u x_e²/ε) (u⁻¹ ε) = u⁻¹ arcVe (X(t))` and
   `V_f ↦ ofFrame x_f (u ε) (-u⁻¹ x_f²/ε) = u arcVf (X(t))` (the frame of `X(t)` is
   `(-ε, u x_e, u⁻¹ x_f)` and `ρ₁(X(t)) = ε`, `ρ_iso_vfX_one`).
5. Collect: `u⁻² = e^{2t/ε}`, `u² = e^{-2t/ε}`.
Also checked exactly with sympy against the literal definitions (matrix exponentials
`cosh(ωt) I + ω⁻¹ sinh(ωt) M` for `M² = ω² I`), symbolically and at exact points. -/
theorem iso_vfΛ₁_one_eq (hX : IsStarState q.1) (hL : q.2.1.trace = 0) (t : ℝ) :
    iso_vfΛ₁ 1 q t =
      (2 * arcEps q ^ 2 * traceForm q.2.1 (q.1 + iso_vfP 1 q)) • (iso_vfX 1 q t + iso_vfP 1 q) +
        (arcEps q ^ 2 * traceForm q.2.1 (arcVf q.1) * Real.exp (2 * t / arcEps q)) •
          arcVe (iso_vfX 1 q t) +
        (arcEps q ^ 2 * traceForm q.2.1 (arcVe q.1) * Real.exp (-2 * t / arcEps q)) •
          arcVf (iso_vfX 1 q t) := by
  have hε : arcEps q ≠ 0 := (arcEps_pos hX).ne'
  obtain ⟨-, hxe, hxf, hd⟩ := frame_state hX
  -- step 1: `Λ₁(0) = α A + β V_e + γ V_f`
  have hdec := ofFrame_eq_eigenbasis_sum (frameH q.2.1) (frameE q.2.1) (frameF q.2.1) hε hd
  rw [ofFrame_frame hL, ← state_add_iso_vfP_one_eq_ofFrame hX, ← arcVe_eq_ofFrame_arcEps q,
    ← arcVf_eq_ofFrame_arcEps q] at hdec
  set α := 2 * arcEps q ^ 2 * traceForm q.2.1 (q.1 + iso_vfP 1 q)
  set β := arcEps q ^ 2 * traceForm q.2.1 (arcVf q.1)
  set γ := arcEps q ^ 2 * traceForm q.2.1 (arcVe q.1)
  -- step 3: conjugation by `e^{-tA}`
  have hVe : NormedSpace.exp (-t • (q.1 + iso_vfP 1 q)) * arcVe q.1 *
      NormedSpace.exp (t • (q.1 + iso_vfP 1 q)) = Real.exp (t / arcEps q) • arcVe q.1 := by
    have := exp_conj_arcVe hX (-t)
    simp only [neg_neg] at this
    exact this
  have hVf : NormedSpace.exp (-t • (q.1 + iso_vfP 1 q)) * arcVf q.1 *
      NormedSpace.exp (t • (q.1 + iso_vfP 1 q)) = Real.exp (-t / arcEps q) • arcVf q.1 := by
    have := exp_conj_arcVf hX (-t)
    simp only [neg_neg] at this
    exact this
  have h3 : NormedSpace.exp (-t • (q.1 + iso_vfP 1 q)) *
      (α • (q.1 + iso_vfP 1 q) + β • arcVe q.1 + γ • arcVf q.1) *
      NormedSpace.exp (t • (q.1 + iso_vfP 1 q)) = α • (q.1 + iso_vfP 1 q) +
        (β * Real.exp (t / arcEps q)) • arcVe q.1 + (γ * Real.exp (-t / arcEps q)) • arcVf q.1 := by
    generalize q.1 + iso_vfP 1 q = A at hVe hVf ⊢
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      exp_neg_smul_conj_self A t, hVe, hVf, smul_smul]
  -- steps 2 and 4: `Λ₁(t) = e^{tP} (⋯) e^{-tP}` in the frame
  rw [iso_vfΛ₁_eq_conj, hdec, h3, state_add_iso_vfP_one_eq_ofFrame hX, arcVe_eq_ofFrame_arcEps q,
    arcVf_eq_ofFrame_arcEps q]
  simp only [smul_ofFrame, ofFrame_add]
  rw [exp_conj_ofFrame hX, arcVe_eq_ofFrame, arcVf_eq_ofFrame, (ρ_iso_vfX_one hX t).1,
    iso_vfX_one_eq hX t, frameE_ofFrame, frameF_ofFrame, iso_vfP_one_eq hX]
  simp only [smul_ofFrame, ofFrame_add]
  -- step 5: compare the frame components
  have hv : Real.exp (t / arcEps q) ≠ 0 := (Real.exp_pos _).ne'
  have hu : Real.exp (-t / arcEps q) = (Real.exp (t / arcEps q))⁻¹ := by
    rw [neg_div, Real.exp_neg]
  have h2 : Real.exp (2 * t / arcEps q) = Real.exp (t / arcEps q) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hm2 : Real.exp (-2 * t / arcEps q) = (Real.exp (t / arcEps q) ^ 2)⁻¹ := by
    rw [sq, ← Real.exp_add, ← Real.exp_neg]
    ring_nf
  rw [hxe, hxf, hu, h2, hm2]
  congr 1 <;> field_simp <;> ring


end SmoothedPolygons
