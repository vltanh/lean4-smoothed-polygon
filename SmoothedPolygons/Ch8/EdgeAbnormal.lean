module

public import SmoothedPolygons.Ch8.EdgeProblem

/-!
# Abnormal extremals with arbitrary edge control (Remark 8.1.6)

Remark 8.1.6 (`rem:edge-abnormal`, TeX 7035–7070): along every Reinhardt trajectory with control in
the edge `{u₀ = 0}`, an explicit abnormal costate (`λ_cost = 0`) makes every edge control a
maximizer of the Hamiltonian, so the Reinhardt problem has "unnecessarily many extremals"
(TeX 6645–6653); the edge control problem removes them (Theorem 8.1.4), which is why Chapter 8
assumes edge extremality. With the signs as printed the edge is the face of *minimizers* (E51),
and the signs of both costates are reversed here.

These abnormal extremals also show that the restatement of Theorem 8.3.2 in Chapter 1 (TeX
851–856), which drops the hypothesis "edge extremal", is false for extremal lifted trajectories on
an interval, the sense of Theorem 8.3.2 (E57): they never meet the singular locus (`Λ_R ≠ 0`),
and their control is any measurable edge control (e.g. the midpoint of the edge, which is not
bang-bang). Whether it also fails for extremals with the boundary conditions of Problem 3.6.2 is
not settled here (the costate of the remark is tied to one edge and need not satisfy the
transversality conditions).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix
open scoped Interval

/-- The costate `Λ₁ = -[[-x, x²], [-1, x]]` of Remark 8.1.6, with the sign reversed (E51), as
a function of `X = Φ(x + iy)` (`x = X₀₀/X₁₀`). -/
noncomputable def abnormalEdgeΛ₁ (X : Mat2) : Mat2 :=
  -!![-(X 0 0 / X 1 0), (X 0 0 / X 1 0) ^ 2; -1, X 0 0 / X 1 0]

/-- The costate `Λ_R = -[[x, y² - x²], [1, -x]]` of Remark 8.1.6, with the sign reversed
(E51), as a function of `X = Φ(x + iy)` (`x = X₀₀/X₁₀`, `y = 1/X₁₀`). -/
noncomputable def abnormalEdgeΛR (X : Mat2) : Mat2 :=
  -!![X 0 0 / X 1 0, (1 / X 1 0) ^ 2 - (X 0 0 / X 1 0) ^ 2; 1, -(X 0 0 / X 1 0)]

/-! ### Carathéodory solutions and almost-everywhere derivatives -/

/-- The entries of `t ↦ [[a, b], [c, d]](t)` are absolutely continuous when `a, b, c, d` are. -/
private lemma l3c_ac_fin_two {a b c d : ℝ → ℝ} {T : ℝ} (ha : AbsolutelyContinuousOnInterval a 0 T)
    (hb : AbsolutelyContinuousOnInterval b 0 T) (hc : AbsolutelyContinuousOnInterval c 0 T)
    (hd : AbsolutelyContinuousOnInterval d 0 T) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t ↦ (!![a t, b t; c t, d t] : Mat2) i j) 0 T := by
  fin_cases i <;> fin_cases j <;> simpa

/-- A curve of matrices whose entries are absolutely continuous on `[0, T]`, with entrywise
derivative `V` almost everywhere, is an integral curve of `V`. -/
private lemma l3c_isIntegralCurve_of_ae {F V : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (hac : ∀ i j, AbsolutelyContinuousOnInterval (fun t ↦ F t i j) 0 T)
    (hd : ∀ᵐ s, s ∈ Ioo 0 T → HasDerivAtEntrywise F (V s) s) : IsIntegralCurve F V T :=
  fun i j ↦ (hac i j).eq_add_integral_of_ae_hasDerivAt hT
    (by filter_upwards [hd] with s hs hsI using hs hsI i j)

/-! ### Pointwise identities ("It can be checked", MCA:4647835) -/

/-- A star state is `Φ(x, y)` with `x = X₀₀/X₁₀` and `y = 1/X₁₀ > 0` (Lemma 4.2.1). -/
private lemma l3c_isStarState_eq_Φ {X : Mat2} (hX : IsStarState X) :
    0 < X 1 0 ∧ X = Φ (X 0 0 / X 1 0) (1 / X 1 0) := by
  obtain ⟨htr, hdet, h0, h1, -⟩ := hX
  have h3 : 0 < √3 := by positivity
  have hc : 0 < X 1 0 := by
    unfold ρ₀ at h0
    unfold ρ₁ at h1
    have a := (div_pos_iff_of_pos_right h3).1 h0
    have b := (div_pos_iff_of_pos_right h3).1 h1
    linarith
  refine ⟨hc, ?_⟩
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have h11 : X 1 1 = -X 0 0 := by linarith
  have h01 : X 0 1 * X 1 0 = -(1 + X 0 0 ^ 2) := by rw [h11] at hdet; nlinarith
  have hc' := hc.ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Φ, h11]
  · field_simp
  · field_simp
    linear_combination h01
  · field_simp

/-- `[Λ₁, Φ(x, y)] = [[y, -2xy], [0, -y]]` for `Λ₁ = [[x, -x²], [1, -x]]`: the right-hand side
of `Λ₁' = [Λ₁, X]` is the derivative of `Λ₁` along `x' = y`. -/
private lemma l3c_bracket₁ (x y : ℝ) (hy : y ≠ 0) :
    !![x, -(x * x); 1, -x] * Φ x y - Φ x y * !![x, -(x * x); 1, -x] =
      !![y, -(y * x + x * y); 0, -y] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Φ] <;>
    field_simp <;> ring

/-- The right-hand side of the costate equation of `Λ_R` (§6.5, `λ_cost = 0`) along the edge
`{u₀ = 0}`, with `Z_u = [[p, -2/3], [0, -p]]`, `Λ_R = [[-x, x² - y²], [-1, x]]`,
`Λ₁ = [[x, -x²], [1, -x]]` and `X = Φ(x, y)`: it is the derivative of `Λ_R` along `x' = y`,
`y' = f₂ = 3y²p/(-1 + 3xp)`. -/
private lemma l3c_bracketR (x y p : ℝ) (hy : y ≠ 0) (hD : -1 + 3 * x * p ≠ 0) :
    ((traceForm !![p, -2 / 3; 0, -p] (Φ x y))⁻¹ • !![p, -2 / 3; 0, -p] *
        !![-x, x * x - y * y; -1, x] -
      !![-x, x * x - y * y; -1, x] *
        (traceForm !![p, -2 / 3; 0, -p] (Φ x y))⁻¹ • !![p, -2 / 3; 0, -p]) -
      traceForm !![-x, x * x - y * y; -1, x]
          ((traceForm !![p, -2 / 3; 0, -p] (Φ x y))⁻¹ • !![p, -2 / 3; 0, -p]) •
        ((traceForm !![p, -2 / 3; 0, -p] (Φ x y))⁻¹ • !![p, -2 / 3; 0, -p] * Φ x y -
          Φ x y * (traceForm !![p, -2 / 3; 0, -p] (Φ x y))⁻¹ • !![p, -2 / 3; 0, -p]) +
      ((-!![x, -(x * x); 1, -x] + (3 / 2 * 0 : ℝ) • J) * Φ x y -
        Φ x y * (-!![x, -(x * x); 1, -x] + (3 / 2 * 0 : ℝ) • J)) =
      !![-y, (y * x + x * y) - (3 * y ^ 2 * p / (-1 + 3 * x * p) * y +
        y * (3 * y ^ 2 * p / (-1 + 3 * x * p))); 0, y] := by
  have htf : traceForm !![p, -2 / 3; 0, -p] (Φ x y) = 2 * (-1 + 3 * x * p) / (3 * y) := by
    simp [traceForm, Φ, Matrix.trace_fin_two]
    field_simp
    ring
  rw [htf]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Φ, J, traceForm, Matrix.trace_fin_two] <;>
    field_simp <;> ring

/-- The Hamiltonian of the abnormal costates: for `X = Φ(x, y)` and `Z = [[α, β], [γ, -α]]`,
`H = ⟨Λ₁, X⟩ - ⟨Λ_R, Z⟩/⟨X, Z⟩ = 2y²γ/⟨X, Z⟩` (`λ_cost = 0`). -/
private lemma l3c_ham (x y α β γ : ℝ) (hy : y ≠ 0)
    (hZ : traceForm (Φ x y) !![α, β; γ, -α] ≠ 0) :
    traceForm (!![x, -(x * x); 1, -x] - (3 / 2 * 0 : ℝ) • J) (Φ x y) -
        traceForm !![-x, x * x - y * y; -1, x] !![α, β; γ, -α] /
          traceForm (Φ x y) !![α, β; γ, -α] =
      2 * y ^ 2 * γ / traceForm (Φ x y) !![α, β; γ, -α] := by
  rw [eq_div_iff hZ, sub_mul, div_mul_cancel₀ _ hZ]
  simp [traceForm, Φ, J, Matrix.trace_fin_two]
  field_simp
  ring

/-- On the edge `{u₀ = 0}` of `U_T`, `Z_u = [[p, -2/3], [0, -p]]` with `p = (u₁ - u₂)/√3`. -/
private lemma l3c_controlMatrix_edge {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) (hu0 : u 0 = 0) :
    controlMatrix u = !![(u 1 - u 2) / √3, -2 / 3; 0, -((u 1 - u 2) / √3)] := by
  have hs := hu.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [controlMatrix, hu0]
  · linarith
  · ring

/-- `Z_u = [[α, β], [γ, -α]]` with `γ = u₀`. -/
private lemma l3c_controlMatrix_eq (u : Fin 3 → ℝ) :
    controlMatrix u = !![(u 1 - u 2) / √3, (u 0 - 2 * u 1 - 2 * u 2) / 3; u 0,
      -((u 1 - u 2) / √3)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [controlMatrix]
  ring

/-- `f₂(x, y, u_e) = 3y²p/(-1 + 3xp)` with `u_e = d/2`, `p = d/√3`. -/
private lemma l3c_edgeF₂_eq (x y d : ℝ) :
    edgeF₂ x y (d / 2) = 3 * y ^ 2 * (d / √3) / (-1 + 3 * x * (d / √3)) := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  have e1 : 2 * √3 * y ^ 2 * (d / 2) = 3 * y ^ 2 * (d / √3) := by
    field_simp
    linear_combination (y ^ 2 * d) * h3
  have e2 : -1 + 2 * √3 * x * (d / 2) = -1 + 3 * x * (d / √3) := by
    field_simp
    linear_combination (x * d) * h3
  rw [edgeF₂, e1, e2]

/-- `⟨Z, Φ(x, y)⟩ = 2(-1 + 3xp)/(3y)` for `Z = [[p, -2/3], [0, -p]]` (the edge `{u₀ = 0}`). -/
private lemma l3c_traceForm_edge (x y p : ℝ) (hy : y ≠ 0) :
    traceForm !![p, -2 / 3; 0, -p] (Φ x y) = 2 * (-1 + 3 * x * p) / (3 * y) := by
  simp [traceForm, Φ, Matrix.trace_fin_two]
  field_simp
  ring

/-- The components of a vector-valued Carathéodory solution `q = q(0) + ∫₀ᵗ F` in `ℝ³`. -/
private lemma l3c_comp_eq {F q : ℝ → Fin 3 → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hint : IntervalIntegrable F volume 0 T)
    (heq : ∀ t ∈ Icc 0 T, q t = q 0 + ∫ s in (0 : ℝ)..t, F s) (i : Fin 3) :
    IntervalIntegrable (fun s ↦ F s i) volume 0 T ∧
      ∀ t ∈ Icc 0 T, q t i = q 0 i + ∫ s in (0 : ℝ)..t, F s i := by
  refine ⟨⟨Integrable.eval hint.1 i, Integrable.eval hint.2 i⟩, fun t ht ↦ ?_⟩
  have hsub : IntervalIntegrable F volume 0 t := hint.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc_right ht.2)
  have e := ContinuousLinearMap.intervalIntegral_comp_comm
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) i) hsub
  simp only [ContinuousLinearMap.proj_apply] at e
  rw [heq t ht, Pi.add_apply, ← e]

/-- **Remark 8.1.6** (`rem:edge-abnormal`; abnormal extremals with arbitrary edge control). Let
`(g, X)` be a state trajectory of the Reinhardt problem on `[0, T]` whose control lies in the
edge `{u₀ = 0}` almost everywhere, with any measurable edge control `u_e ∈ [-½, ½]` (so `g` is
given by (8.1.1) and `X = Φ(z)` with `z` given by (8.1.3)). With `λ_cost = 0`,
`Λ_R = -[[x, y² - x²], [1, -x]]` and `Λ₁ = -[[-x, x²], [-1, x]]` solve the costate equations of
§6.5, `Λ_R ⊥ X`, the Hamiltonian vanishes identically on the edge, and every control of the edge
maximizes it: the set of maximizers over `U_T` is the edge `{u₀ = 0}` at every time. So
`(Λ₁, Λ_R, 0)` lifts the trajectory to an abnormal extremal (`IsStateCostateSolution`, no boundary
conditions) whatever the edge control.

Statement correction (E51): the book prints `Λ_R = [[x, y² - x²], [1, -x]]`,
`Λ₁ = [[-x, x²], [-1, x]]`. With these signs the costate equations hold and `H ≡ 0` on the edge,
but `H(u) = 6 u₀ y³/D` with `D = -3y⟨X, Z_u⟩ > 0` on the star domain (Lemma 3.3.4), so the edge
is the set of *minimizers* of `H` over `U_T` and the claim "any measurable control maximizes the
Hamiltonian" fails. Both costates are reversed here (the costate equations are linear and
`λ_cost = 0`), which makes `H(u) = -6 u₀ y³/D ≤ 0`, with equality exactly on the edge (checked
with sympy).

Proof (the book: "It can be checked", MCA:4647835): with `x' = y`, `y' = f₂` (`eqn_xy_edge`,
`j = 0`, `edgeFrame 0 = id`; `X = Φ(x, y)` with `x = X₀₀/X₁₀`, `y = 1/X₁₀`,
`l3c_isStarState_eq_Φ`), the entries of `Λ₁ = [[x, -x²], [1, -x]]` and
`Λ_R = [[-x, x² - y²], [-1, x]]` are polynomials in the absolutely continuous `x, y`, with
derivatives `[[y, -2xy], [0, -y]]` and `[[-y, 2xy - 2yf₂], [0, y]]` almost everywhere. On the edge
`Z_u = [[p, -2/3], [0, -p]]` with `p = (u₁ - u₂)/√3` and `f₂ = 3y²p/(-1 + 3xp)`; the identities
`[Λ₁, X] = Λ₁'` (`l3c_bracket₁`) and `[P, Λ_R] - ⟨Λ_R, P⟩[P, X] + [-Λ₁, X] = Λ_R'`
(`l3c_bracketR`) are checked by `field_simp; ring`, and the integral form follows from the
fundamental theorem of calculus for absolutely continuous functions
(`l3c_isIntegralCurve_of_ae`). `⟨Λ_R, X⟩ = 0` and `H(v) = 2y²v₀/⟨X, Z_v⟩` (`l3c_ham`) are
identities too; `⟨X, Z_v⟩ < 0` on `U_T` (Lemma 3.3.4) gives `H ≤ 0` with equality exactly on the
edge. `Λ_R ≠ 0` (its `(1, 0)` entry is `-1`) gives nontriviality. -/
theorem remark8_1_6 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (h : IsStateTrajectory T u g X)
    (hu : ∀ᵐ t, t ∈ Ioo 0 T → u t 0 = 0) :
    IsStateCostateSolution T u g X (fun t ↦ abnormalEdgeΛ₁ (X t)) (fun t ↦ abnormalEdgeΛR (X t))
        0 ∧
      ∀ t ∈ Icc 0 T,
        (∀ v ∈ controlEdge 0, hamiltonian 0 (abnormalEdgeΛ₁ (X t)) (abnormalEdgeΛR (X t)) (X t) v =
          0) ∧
        hamiltonianArgmax 0 (abnormalEdgeΛ₁ (X t)) (abnormalEdgeΛR (X t)) (X t) =
          controlEdge 0 := by
  have hT : 0 < T := h.1
  have hU : ∀ t ∈ Icc 0 T, u t ∈ controlSimplex := h.2.2.1
  have hst : ∀ t ∈ Icc 0 T, IsStarState (X t) := fun t ht ↦ (h.2.2.2.1 t ht).2
  -- the point `z = x + iy` of the star domain with `Φ(z) = X`: `x = X₀₀/X₁₀`, `y = 1/X₁₀`
  set xf : ℝ → ℝ := fun t ↦ X t 0 0 / X t 1 0 with hxf
  set yf : ℝ → ℝ := fun t ↦ 1 / X t 1 0 with hyf
  have hXΦ : ∀ t ∈ Icc 0 T, 0 < yf t ∧ X t = Φ (xf t) (yf t) := fun t ht ↦
    ⟨one_div_pos.2 (l3c_isStarState_eq_Φ (hst t ht)).1, (l3c_isStarState_eq_Φ (hst t ht)).2⟩
  -- `(x, y)` solves the edge state equations (8.1.3): `x' = y`, `y' = f₂(x, y, u_e)`
  obtain ⟨⟨⟨-, -, -, hint, heq⟩, -⟩, -, -⟩ := eqn_xy_edge h (j := 0) le_rfl hT le_rfl hu
  simp only [sub_zero, zero_add] at hint heq
  have hq0 : ∀ s, edgeState 0 X 0 s 0 = xf s := fun s ↦ by simp [edgeState, edgeFrame, xf]
  have hq1 : ∀ s, edgeState 0 X 0 s 1 = yf s := fun s ↦ by simp [edgeState, edgeFrame, yf]
  have hF : ∀ s, edgeField (edgeState 0 X 0 s) (edgeParam 0 (u s)) =
      ![yf s, edgeF₂ (xf s) (yf s) ((u s 1 - u s 2) / 2), 1 / yf s] := fun s ↦ by
    simp [edgeField, hq0, hq1, edgeParam]
  obtain ⟨hyi, hxe⟩ := l3c_comp_eq hT.le hint heq 0
  obtain ⟨hfi, hye⟩ := l3c_comp_eq hT.le hint heq 1
  simp only [hF, hq0, hq1, Matrix.cons_val_zero, Matrix.cons_val_one] at hyi hxe hfi hye
  have hxac := absolutelyContinuousOnInterval_of_eq_add_integral hT.le hyi hxe
  have hxd := ae_hasDerivAt_of_eq_add_integral hyi ⟨le_rfl, hT.le⟩ hxe
  have hyac := absolutelyContinuousOnInterval_of_eq_add_integral hT.le hfi hye
  have hyd := ae_hasDerivAt_of_eq_add_integral hfi ⟨le_rfl, hT.le⟩ hye
  have hconst : ∀ c : ℝ, AbsolutelyContinuousOnInterval (fun _ ↦ c) 0 T := fun c ↦
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  -- the explicit costates in the coordinates `x, y` (sign reversed, E51)
  have hΛ₁t : ∀ t, abnormalEdgeΛ₁ (X t) = !![xf t, -(xf t * xf t); 1, -xf t] := fun t ↦ by
    ext i j; fin_cases i <;> fin_cases j <;> simp [abnormalEdgeΛ₁, xf, sq]
  have hΛRt : ∀ t, abnormalEdgeΛR (X t) =
      !![-xf t, xf t * xf t - yf t * yf t; -1, xf t] := fun t ↦ by
    ext i j; fin_cases i <;> fin_cases j <;> simp [abnormalEdgeΛR, xf, yf, sq]
  simp only [hΛ₁t, hΛRt]
  -- the Hamiltonian: `H(v) = 2y²v₀/⟨X, Z_v⟩ ≤ 0` on `U_T`, with equality exactly on the edge
  have hH : ∀ t ∈ Icc 0 T, ∀ v ∈ controlSimplex,
      hamiltonian 0 !![xf t, -(xf t * xf t); 1, -xf t]
          !![-xf t, xf t * xf t - yf t * yf t; -1, xf t] (X t) v ≤ 0 ∧
        (hamiltonian 0 !![xf t, -(xf t * xf t); 1, -xf t]
          !![-xf t, xf t * xf t - yf t * yf t; -1, xf t] (X t) v = 0 ↔ v 0 = 0) := by
    intro t ht v hv
    obtain ⟨hy, hX⟩ := hXΦ t ht
    have hneg : traceForm (X t) (controlMatrix v) < 0 := by
      rw [traceForm, Matrix.trace_mul_comm]
      exact (lemma3_3_4 (X t) (hst t ht).1).1
        ⟨(hst t ht).2.2.1, (hst t ht).2.2.2.1, (hst t ht).2.2.2.2⟩ v hv
    rw [l3c_controlMatrix_eq v, hX] at hneg
    have hval : hamiltonian 0 !![xf t, -(xf t * xf t); 1, -xf t]
        !![-xf t, xf t * xf t - yf t * yf t; -1, xf t] (X t) v =
        2 * yf t ^ 2 * v 0 / traceForm (Φ (xf t) (yf t))
          !![(v 1 - v 2) / √3, (v 0 - 2 * v 1 - 2 * v 2) / 3; v 0, -((v 1 - v 2) / √3)] := by
      rw [hamiltonian, l3c_controlMatrix_eq v, hX]
      exact l3c_ham _ _ _ _ _ hy.ne' hneg.ne
    rw [hval]
    refine ⟨div_nonpos_of_nonneg_of_nonpos (by have := (hv.1 0).1; positivity) hneg.le, ?_⟩
    rw [div_eq_zero_iff]
    constructor
    · rintro (h0 | h0)
      · have : 2 * yf t ^ 2 ≠ 0 := by positivity
        exact (mul_eq_zero.1 h0).resolve_left this
      · exact absurd h0 hneg.ne
    · intro h0
      left
      rw [h0, mul_zero]
  refine ⟨?_, fun t ht ↦ ⟨fun v hv ↦ (hH t ht v hv.1).2.2 hv.2, ?_⟩⟩
  swap
  · -- the maximizers of the Hamiltonian over `U_T` form the edge `{u₀ = 0}`
    ext v
    constructor
    · rintro ⟨hv, hmax⟩
      refine ⟨hv, (hH t ht v hv).2.1 (le_antisymm (hH t ht v hv).1 ?_)⟩
      have hw : (![0, 1, 0] : Fin 3 → ℝ) ∈ controlSimplex :=
        ⟨fun i ↦ by fin_cases i <;> norm_num, by norm_num⟩
      exact ((hH t ht _ hw).2.2 (by simp)).symm.le.trans (hmax _ hw)
    · rintro ⟨hv, hv0⟩
      exact ⟨hv, fun w hw ↦ (hH t ht w hw).1.trans ((hH t ht v hv).2.2 hv0).ge⟩
  unfold IsStateCostateSolution
  refine ⟨h, le_rfl, ?_, ?_, ?_, ?_⟩
  · -- `Λ₁, Λ_R ∈ 𝔰𝔩₂`, `Λ_R ⊥ X`, and `Λ_R ≠ 0`
    intro t ht
    obtain ⟨hy, hX⟩ := hXΦ t ht
    refine ⟨by simp [Matrix.trace_fin_two], by simp [Matrix.trace_fin_two], ?_,
      Or.inr (Or.inr fun h0 ↦ by simpa using congrFun (congrFun h0 1) 0)⟩
    rw [hX]
    simp [traceForm, Φ, Matrix.trace_fin_two]
    field_simp
    ring
  · -- `Λ₁' = [Λ₁, X]`
    refine l3c_isIntegralCurve_of_ae hT.le
      (l3c_ac_fin_two hxac (hxac.fun_mul hxac).fun_neg (hconst 1) hxac.fun_neg) ?_
    filter_upwards [hxd] with s hxs hsI
    obtain ⟨hy, hX⟩ := hXΦ s (Ioo_subset_Icc_self hsI)
    have hxs' := hxs hsI
    rw [hX, l3c_bracket₁ _ _ hy.ne']
    exact hasDerivAtEntrywise_fin_two_iff.2 ⟨by simpa using hxs',
      by simpa using (hxs'.fun_mul hxs').fun_neg, by simpa using hasDerivAt_const s (1 : ℝ),
      by simpa using hxs'.fun_neg⟩
  · -- `Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩[P, X] + [-Λ₁, X]`
    refine l3c_isIntegralCurve_of_ae hT.le
      (l3c_ac_fin_two hxac.fun_neg ((hxac.fun_mul hxac).fun_sub (hyac.fun_mul hyac)) (hconst (-1))
        hxac) ?_
    filter_upwards [hxd, hyd, hu] with s hxs hys hus hsI
    obtain ⟨hy, hX⟩ := hXΦ s (Ioo_subset_Icc_self hsI)
    have hUs := hU s (Ioo_subset_Icc_self hsI)
    have hxs' := hxs hsI
    have hys' := hys hsI
    rw [l3c_edgeF₂_eq] at hys'
    -- the denominator `-1 + 3xp` of `f₂` is negative (Lemma 3.3.4)
    have hneg : traceForm (controlMatrix (u s)) (X s) < 0 :=
      (lemma3_3_4 (X s) (hst s (Ioo_subset_Icc_self hsI)).1).1
        ⟨(hst s (Ioo_subset_Icc_self hsI)).2.2.1, (hst s (Ioo_subset_Icc_self hsI)).2.2.2.1,
          (hst s (Ioo_subset_Icc_self hsI)).2.2.2.2⟩ (u s) hUs
    rw [l3c_controlMatrix_edge hUs (hus hsI), hX, l3c_traceForm_edge _ _ _ hy.ne'] at hneg
    have hD : -1 + 3 * xf s * ((u s 1 - u s 2) / √3) < 0 := by
      have h3y : 0 < 3 * yf s := by positivity
      have := mul_neg_of_neg_of_pos hneg h3y
      rw [div_mul_cancel₀ _ h3y.ne'] at this
      linarith
    rw [controlP, l3c_controlMatrix_edge hUs (hus hsI), hX,
      l3c_bracketR _ _ _ hy.ne' hD.ne]
    exact hasDerivAtEntrywise_fin_two_iff.2 ⟨by simpa using hxs'.fun_neg,
      by simpa using (hxs'.fun_mul hxs').fun_sub (hys'.fun_mul hys'),
      by simpa using hasDerivAt_const s (-1 : ℝ), by simpa using hxs'⟩
  · -- almost everywhere the control lies in the edge, where `H = 0` is maximal
    filter_upwards [hu] with t hut htI
    have ht := Ioo_subset_Icc_self htI
    exact ⟨(hH t ht (u t) (hU t ht)).2.2 (hut htI), fun v hv ↦
      (hH t ht v hv).1.trans ((hH t ht (u t) (hU t ht)).2.2 (hut htI)).ge⟩

end SmoothedPolygons
