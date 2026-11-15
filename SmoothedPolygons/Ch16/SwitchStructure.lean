module

public import SmoothedPolygons.Ch14.FixedPointManifolds
public import SmoothedPolygons.Ch7.Isolated.Return

/-!
# Theorem 16.4.1, helper: the switching structure at the chart points near `q_out` and `q_in`

The proof of `IsChatteringArcInto.eventually_follows_out` (and `…_in`) in
`SmoothedPolygons/Ch16/ClusterPoint.lean` needs, besides the structure of the flow with the control
`e₂` (`eventually_isSwitch_reinSwitchTime`, `remark14_3_4`), the switching structure **at** a
chart point `q = lieChart p` (or `lieChartIn p`), `p` near `(0, x̃_out)`, `r > 0`: which control an
extremal through `q` uses right after `q`. This is the book's claim "the first control of
`(X(r, x̃), Λ₁(r, x̃), Λ_R(r, x̃))` is `u = e₂` for all sufficiently small `r > 0`, provided …
`ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁ < 0` and `ℓ̃₂₁ < 0`" (TeX 11706–11718), stated without proof, at the switching
points that "give the value of the Reinhardt–Poincaré map" (TeX 11835–11836). Two facts decide it.

* `H(e₁) < H(e₂) = H(e₃) = 0` at `q` (so `e₁` is not a maximizer at `q`): on the section
  (`Λ_R = h K(X)`, `lieΛR_eq_reducedHam_smul`) one has exactly `H(e₁) = 6h/(3 + 3a² - c²)` for
  `X = [[a, b], [c, -a]]`, `det X = 1` (`l6h_ham0_eq`), and on the chart `h = r³ G(r, x̃)` with
  `G(0, x̃) = 2(ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁)` (`l6h_reducedHam_lieChart`), negative at `x̃_out`
  (`l6h_xTildeOut_signs`; it is `12 z₃(x̃_out) < 0`, the wall `𝒲₀`).
* The slope of `χ₃₂ = H(e₃) - H(e₂)` at `q` along the vector field of `e₂` and of `e₃` is
  negative: on the section it is exactly `4√3 (c h + (Λ₁)₂₁ + 3/2)/(c² - 3a²)` for both controls
  (`l6h_dsw_eq`; the equality of the two slopes is `iso_edge_slope` of Chapter 7), which is
  `4√3 r² (c r G + ℓ̃₂₁)/(c² - 3r²)` on the chart, with limit sign that of `ℓ̃₂₁ < 0` at `x̃_out`.
  So along the `e₃`-flow from `q`, `H(e₃) < H(e₂)` right after `q`: an extremal cannot leave `q`
  with the control `e₃`. (In the Fuller limit this is `χ_{ζ→ζ²}'(0) = 24 RR(ζ - ζ², z₂) > 0`.)

The mirrored chart `lieChartIn = reinTau ∘ lieChart` is reduced to the chart by the time reversal
(`iso_vertexFlow_reinTau`, `switchingFn_reinTau`): the `e₃`-flow from `τ q` is the reversed
`e₂`-flow from `q`, so the second fact at `τ q` is the slope of `χ₃₂` along the `e₂`-field at `q`.

The result is `eventually_switchStructure`. Everything is exact algebra on `2 × 2` matrices (the
identities were also checked with sympy) and continuity at `r = 0`.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology
open TriFuller

/-! ### The control matrices and `P = Z/⟨Z, X⟩` on traceless `X` -/

private lemma l6h_cm0 : controlMatrix (vertex 0) = !![0, 1 / 3; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [controlMatrix, vertex]

private lemma l6h_cm1 : controlMatrix (vertex 1) = !![√3 / 3, -2 / 3; 0, -(√3 / 3)] := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs : (√3 : ℝ) ≠ 0 := by positivity
  ext i j; fin_cases i <;> fin_cases j <;> simp [controlMatrix, vertex] <;> field_simp <;>
    linarith

private lemma l6h_cm2 : controlMatrix (vertex 2) = !![-(√3 / 3), -2 / 3; 0, √3 / 3] := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs : (√3 : ℝ) ≠ 0 := by positivity
  ext i j; fin_cases i <;> fin_cases j <;> simp [controlMatrix, vertex] <;> field_simp <;>
    linarith

private lemma l6h_cP1 (a b c : ℝ) (h1 : √3 * a - c ≠ 0) :
    controlP (vertex 1) !![a, b; c, -a] =
      !![√3 / (2 * (√3 * a - c)), -1 / (√3 * a - c); 0, -(√3 / (2 * (√3 * a - c)))] := by
  rw [controlP, l6h_cm1]
  have : traceForm !![√3 / 3, -2 / 3; 0, -(√3 / 3)] !![a, b; c, -a] = 2 / 3 * (√3 * a - c) := by
    simp [traceForm, Matrix.trace_fin_two]; ring
  rw [this]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp

private lemma l6h_cP2 (a b c : ℝ) (h2 : √3 * a + c ≠ 0) :
    controlP (vertex 2) !![a, b; c, -a] =
      !![√3 / (2 * (√3 * a + c)), 1 / (√3 * a + c); 0, -(√3 / (2 * (√3 * a + c)))] := by
  rw [controlP, l6h_cm2]
  have : traceForm !![-(√3 / 3), -2 / 3; 0, √3 / 3] !![a, b; c, -a] =
      -(2 / 3 * (√3 * a + c)) := by
    simp [traceForm, Matrix.trace_fin_two]; ring
  rw [this]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp

/-! ### The section in closed form: `H(e₁)` and the slope of `χ₃₂` -/

/-- **`H(e₁)` on the section**: for `X = [[a, b], [c, -a]]` with `det X = 1`, `c ≠ 0`,
`⟨X, Z_{e₁}⟩ ≠ 0` and `Λ_R = h K(X)`, `h = ⟨Λ₁ + (3/2) J, X⟩`: `H(e₁) = 6h/(3 + 3a² - c²)`. -/
private theorem l6h_ham0_eq (a b c l w n : ℝ) (hdet : a ^ 2 + b * c + 1 = 0) (hc : c ≠ 0)
    (h0 : 3 + 3 * a ^ 2 - c ^ 2 ≠ 0) :
    hamiltonian (-1) !![l, w; n, -l]
        (reducedHam !![l, w; n, -l] !![a, b; c, -a] • lieΛRShape !![a, b; c, -a])
        !![a, b; c, -a] (vertex 0) =
      6 * reducedHam !![l, w; n, -l] !![a, b; c, -a] / (3 + 3 * a ^ 2 - c ^ 2) := by
  have hb : b = -(1 + a ^ 2) / c := by field_simp; linarith
  have hK : lieΛRShape !![a, b; c, -a] = !![a, -2 * a ^ 2 / c - b; c, -a] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [lieΛRShape]
  have hh : traceForm (!![l, w; n, -l] - (3 / 2 * -1 : ℝ) • J) !![a, b; c, -a] =
      reducedHam !![l, w; n, -l] !![a, b; c, -a] := by
    rw [reducedHam]; congr 1; rw [show (3 / 2 * -1 : ℝ) = -(3 / 2) by norm_num, neg_smul,
      sub_neg_eq_add]
  rw [hamiltonian, hh, hK, l6h_cm0]
  generalize reducedHam !![l, w; n, -l] !![a, b; c, -a] = h
  have e1 : traceForm (h • !![a, -2 * a ^ 2 / c - b; c, -a]) !![0, 1 / 3; 1, 0] =
      h * (-2 * a ^ 2 / c - b + c / 3) := by
    simp [traceForm, Matrix.trace_fin_two]; ring
  have e2 : traceForm !![a, b; c, -a] !![0, 1 / 3; 1, 0] = b + c / 3 := by
    simp [traceForm, Matrix.trace_fin_two]; ring
  have hcD : c * (b + c / 3) = -(3 + 3 * a ^ 2 - c ^ 2) / 3 := by linear_combination hdet
  have hD : b + c / 3 ≠ 0 := by
    intro h; apply h0
    have : c * (b + c / 3) = 0 := by rw [h, mul_zero]
    rw [hcD] at this; linarith
  have hX : -2 * a ^ 2 / c - b + c / 3 = (b + c / 3) + 2 / c := by
    field_simp; linear_combination (-6) * hdet
  rw [e1, e2, hX]
  generalize b + c / 3 = B at hcD hD ⊢
  rw [show h - h * (B + 2 / c) / B = -(2 * h) / (c * B) by field_simp; ring, hcD]
  field_simp
  ring

set_option linter.flexible false in
/-- **The slope of `χ₃₂` on the section**, along the vector field of the control `e₂` or `e₃`:
for `X = [[a, b], [c, -a]]` with `det X = 1`, `c ≠ 0`, `√3 a ∓ c ≠ 0`, `Λ₁ = [[l, w], [n, -l]]`
and `Λ_R = h K(X)`, the derivative of `χ₃₂ = ⟨Λ_R, P₂ - P₃⟩` along the field is
`4√3 (c h + n + 3/2)/(c² - 3a²)`. -/
private theorem l6h_dsw_eq (m : Fin 3) (hm : m = 1 ∨ m = 2) (a b c l w n : ℝ)
    (hdet : a ^ 2 + b * c + 1 = 0) (hc : c ≠ 0) (h1 : √3 * a - c ≠ 0) (h2 : √3 * a + c ≠ 0) :
    irt_dsw 2 1 (reducedHam !![l, w; n, -l] !![a, b; c, -a] • lieΛRShape !![a, b; c, -a])
      !![a, b; c, -a]
      (iso_extremalField (vertex m) (!![a, b; c, -a], !![l, w; n, -l],
        reducedHam !![l, w; n, -l] !![a, b; c, -a] • lieΛRShape !![a, b; c, -a])).2.2
      (iso_extremalField (vertex m) (!![a, b; c, -a], !![l, w; n, -l],
        reducedHam !![l, w; n, -l] !![a, b; c, -a] • lieΛRShape !![a, b; c, -a])).1 =
      4 * √3 * (c * reducedHam !![l, w; n, -l] !![a, b; c, -a] + n + 3 / 2) /
        (c ^ 2 - 3 * a ^ 2) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq : c ^ 2 - 3 * a ^ 2 ≠ 0 := by
    have : c ^ 2 - 3 * a ^ 2 = -((√3 * a - c) * (√3 * a + c)) := by ring_nf; rw [h3]
    rw [this, neg_ne_zero]; exact mul_ne_zero h1 h2
  have hb : b = -(1 + a ^ 2) / c := by field_simp; linarith
  have hK : lieΛRShape !![a, b; c, -a] = !![a, -2 * a ^ 2 / c - b; c, -a] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [lieΛRShape]
  have hh : reducedHam !![l, w; n, -l] !![a, b; c, -a] =
      2 * l * a + (w - 3 / 2) * c + (n + 3 / 2) * b := by
    simp [reducedHam, traceForm, J, Matrix.trace_fin_two]; ring
  rw [eq_div_iff hq]
  rcases hm with rfl | rfl <;>
  · simp only [irt_dsw, iso_extremalField, costateRHS, l6h_cP1 a b c h1, l6h_cP2 a b c h2, hK, hh]
    rw [hb]
    simp [traceForm, J, Matrix.trace_fin_two]
    generalize √3 = s at *
    field_simp
    ring_nf
    have h4 : s ^ 4 = 9 := by nlinarith
    have h5 : s ^ 3 = 3 * s := by nlinarith
    have h6 : s ^ 5 = 9 * s := by nlinarith
    have h7 : s ^ 6 = 27 := by nlinarith
    simp only [h3, h4, h5, h6, h7]
    ring_nf

/-! ### The chart points -/

/-- `h/r³` on the chart: `reducedHam = r³ G(r, x̃)` (`l6h_reducedHam_lieChart`), with
`G(0, x̃) = 2(ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁)`. -/
private noncomputable def l6h_G (p : ℝ × (Fin 3 → ℝ)) : ℝ :=
  (2 * p.1 ^ 3 * p.2 0 ^ 2 * p.2 1 ^ 2 - 4 * p.1 ^ 3 * p.2 0 * p.2 1 * p.2 2 +
      2 * p.1 ^ 3 * p.2 2 ^ 2 + 4 * p.1 ^ 2 * p.2 0 * p.2 1 ^ 2 - 4 * p.1 ^ 2 * p.2 1 * p.2 2 +
      3 * p.1 * p.2 0 ^ 2 * p.2 2 + 6 * p.1 * p.2 0 * p.2 1 + 2 * p.1 * p.2 1 ^ 2 +
      2 * p.1 * p.2 2 ^ 2 - 3 * p.1 * p.2 2 + 6 * p.2 0 * p.2 2 + 6 * p.2 1) /
    ((1 + p.1 * p.2 0) * (3 - 2 * p.1 ^ 2 * p.2 2))

/-- `H(e₁)/r³` on the chart. -/
private noncomputable def l6h_F1 (p : ℝ × (Fin 3 → ℝ)) : ℝ :=
  6 * l6h_G p / (3 + 3 * p.1 ^ 2 - (1 + p.1 * p.2 0) ^ 2)

/-- The slope of `χ₃₂` divided by `4√3 r²` on the chart. -/
private noncomputable def l6h_F2 (p : ℝ × (Fin 3 → ℝ)) : ℝ :=
  ((1 + p.1 * p.2 0) * p.1 * l6h_G p + p.2 2) / ((1 + p.1 * p.2 0) ^ 2 - 3 * p.1 ^ 2)

private theorem l6h_reducedHam_lieChart (p : ℝ × (Fin 3 → ℝ)) (hc : 1 + p.1 * p.2 0 ≠ 0)
    (hd : 3 - 2 * p.1 ^ 2 * p.2 2 ≠ 0) :
    reducedHam (lieΛ₁ p.1 (p.2 1) (p.2 2)) (lieX p.1 (p.2 0)) = p.1 ^ 3 * l6h_G p := by
  simp only [reducedHam, traceForm, lieΛ₁, lieX, J, l6h_G]
  generalize p.1 = r at *
  generalize p.2 0 = x0 at *
  generalize p.2 1 = x1 at *
  generalize p.2 2 = x2 at *
  have hd' : 3 / 2 - r ^ 2 * x2 ≠ 0 := by intro h; apply hd; linarith
  have hd'' : 3 - r ^ 2 * 2 * x2 ≠ 0 := by intro h; apply hd; linarith
  rw [mul_div_assoc', eq_div_iff (mul_ne_zero hc hd)]
  simp [Matrix.trace_fin_two]
  field_simp
  ring

/-- The chart point on the section in closed form, `Λ_R = h K(X)` (`lieΛR_eq_reducedHam_smul`). -/
private theorem l6h_lieChart_eq (p : ℝ × (Fin 3 → ℝ)) (hc : 1 + p.1 * p.2 0 ≠ 0) :
    lieChart p = (lieX p.1 (p.2 0), lieΛ₁ p.1 (p.2 1) (p.2 2),
      reducedHam (lieΛ₁ p.1 (p.2 1) (p.2 2)) (lieX p.1 (p.2 0)) • lieΛRShape (lieX p.1 (p.2 0))) :=
          by
  rw [lieChart, lieΛR_eq_reducedHam_smul _ _ (by simp [lieX]) (by simpa [lieX] using hc)]

/-- The coordinates of a chart point near `r = 0`, and the side conditions. -/
private def l6h_good (p : ℝ × (Fin 3 → ℝ)) : Prop :=
  |p.1| < 1 / 10 ∧ |p.1 * p.2 0| < 1 / 10 ∧ |p.1 ^ 2 * p.2 2| < 1 / 10

private lemma l6h_good_facts {p : ℝ × (Fin 3 → ℝ)} (hp : l6h_good p) :
    1 + p.1 * p.2 0 ≠ 0 ∧ 3 - 2 * p.1 ^ 2 * p.2 2 ≠ 0 ∧ √3 * p.1 - (1 + p.1 * p.2 0) ≠ 0 ∧
      √3 * p.1 + (1 + p.1 * p.2 0) ≠ 0 ∧ 3 + 3 * p.1 ^ 2 - (1 + p.1 * p.2 0) ^ 2 ≠ 0 ∧
      0 < 3 + 3 * p.1 ^ 2 - (1 + p.1 * p.2 0) ^ 2 ∧ 0 < (1 + p.1 * p.2 0) ^ 2 - 3 * p.1 ^ 2 ∧
      √3 * p.1 < 1 + p.1 * p.2 0 := by
  obtain ⟨h1, h2, h3⟩ := hp
  rw [abs_lt] at h1 h2 h3
  have hs : √3 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs0 : 0 ≤ √3 := Real.sqrt_nonneg 3
  have hr1 : √3 * p.1 < 1 / 5 := by nlinarith
  have hr2 : -(1 / 5) < √3 * p.1 := by nlinarith
  have hsq : p.1 ^ 2 < 1 / 100 := by nlinarith
  refine ⟨by linarith, by linarith, by linarith, by linarith, by nlinarith, by nlinarith,
    by nlinarith, by linarith⟩

/-- The signs at `x̃_out`: `ℓ̃₂₁ < 0` and `ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁ < 0` (the latter is `6 z₃(x̃_out)`,
from `H_F(q_out, ζ) = 0`: `RR(z₁, z₂ i) = z₃/2 < 0`). -/
private theorem l6h_xTildeOut_signs : xTildeOut 2 < 0 ∧ xTildeOut 0 * xTildeOut 2 + xTildeOut 1 <
    0 := by
  obtain ⟨hq0, -, hq1⟩ := qOutCart_signs
  obtain ⟨hre0, him2, hre2⟩ := qOutCart_normalization
  have hH := hamMax_qOutCart
  set E := (qOutCart 1).re * (qOutCart 0).im - (qOutCart 0).re * (qOutCart 1).im with hEdef
  have hv : ∀ v : ℂ, ham qOutCart v = E + v.re * (qOutCart 2).re := by
    intro v
    simp only [ham, RR_eq_re_mul_add_im_mul, him2, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, hEdef]
    ring
  rw [hamMax, hv, hv, hv, ζ_sq_re, ζ_re, Complex.one_re, max_self,
    max_eq_right (by nlinarith)] at hH
  have hE : E = (qOutCart 2).re / 2 := by linarith
  have hx : xTildeOut = ![(qOutCart 0).re / (qOutCart 0).im,
      3 * (qOutCart 1).re / (2 * (qOutCart 0).im ^ 2),
      -(3 * (qOutCart 1).im) / (2 * (qOutCart 0).im ^ 2)] := rfl
  rw [hx]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  constructor
  · exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  · have e : (qOutCart 0).re / (qOutCart 0).im *
          (-(3 * (qOutCart 1).im) / (2 * (qOutCart 0).im ^ 2)) +
        3 * (qOutCart 1).re / (2 * (qOutCart 0).im ^ 2) = 3 * E / (2 * (qOutCart 0).im ^ 3) := by
      rw [hEdef]; field_simp; ring
    rw [e, hE]
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)

private lemma l6h_continuousAt_G : ContinuousAt l6h_G chartPtOut := by
  unfold l6h_G
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [chartPtOut])

private lemma l6h_G_chartPtOut :
    l6h_G chartPtOut = 2 * (xTildeOut 0 * xTildeOut 2 + xTildeOut 1) := by
  simp [l6h_G, chartPtOut]; ring

/-- Near `(0, x̃_out)` the chart coordinates are good and `H(e₁)/r³`, the slope of `χ₃₂` over
`4√3 r²` are negative. -/
private lemma l6h_eventually_good :
    ∀ᶠ p in 𝓝 chartPtOut, l6h_good p ∧ l6h_F1 p < 0 ∧ l6h_F2 p < 0 := by
  obtain ⟨hs2, hs01⟩ := l6h_xTildeOut_signs
  have hG := l6h_continuousAt_G
  have h1 : ∀ᶠ p in 𝓝 chartPtOut, |p.1| < 1 / 10 :=
    (continuous_fst.abs.continuousAt).eventually_lt continuousAt_const (by simp [chartPtOut])
  have h2 : ∀ᶠ p in 𝓝 chartPtOut, |p.1 * p.2 0| < 1 / 10 :=
    ((by fun_prop : Continuous fun p : ℝ × (Fin 3 → ℝ) ↦ |p.1 * p.2 0|).continuousAt).eventually_lt
      continuousAt_const (by simp [chartPtOut])
  have h3 : ∀ᶠ p in 𝓝 chartPtOut, |p.1 ^ 2 * p.2 2| < 1 / 10 :=
    ((by fun_prop : Continuous fun p : ℝ × (Fin 3 → ℝ) ↦
      |p.1 ^ 2 * p.2 2|).continuousAt).eventually_lt continuousAt_const (by simp [chartPtOut])
  have hF1 : ContinuousAt l6h_F1 chartPtOut := by
    unfold l6h_F1
    exact ContinuousAt.div (continuousAt_const.mul hG) (by fun_prop)
      (by simp [chartPtOut]; norm_num)
  have hF2 : ContinuousAt l6h_F2 chartPtOut := by
    unfold l6h_F2
    exact ContinuousAt.div (((by fun_prop : Continuous fun p : ℝ × (Fin 3 → ℝ) ↦
      (1 + p.1 * p.2 0) * p.1).continuousAt.mul hG).add (by fun_prop)) (by fun_prop)
      (by simp [chartPtOut])
  have h4 : ∀ᶠ p in 𝓝 chartPtOut, l6h_F1 p < 0 := hF1.eventually_lt continuousAt_const (by
    simp only [l6h_F1, l6h_G_chartPtOut]
    simp only [chartPtOut]
    norm_num
    linarith)
  have h5 : ∀ᶠ p in 𝓝 chartPtOut, l6h_F2 p < 0 := hF2.eventually_lt continuousAt_const (by
    simpa [l6h_F2, chartPtOut] using hs2)
  filter_upwards [h1, h2, h3, h4, h5] with p a1 a2 a3 a4 a5 using ⟨⟨a1, a2, a3⟩, a4, a5⟩

/-- The sign of a function vanishing at `0` with negative derivative there. -/
private lemma l6h_sign_of_hasDerivAt {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' 0)
    (h0 : f 0 = 0) (hneg : f' < 0) :
    ∃ ε > 0, (∀ t ∈ Ioo 0 ε, f t < 0) ∧ ∀ t ∈ Ioo (-ε) 0, 0 < f t := by
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t⁻¹ • (f (0 + t) - f 0) < 0 :=
    hf.tendsto_slope_zero.eventually (gt_mem_nhds hneg)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  have key : ∀ t, |t| < ε → t ≠ 0 → t⁻¹ * f t < 0 := by
    intro t ht ht0
    have := hball ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact ht, ht0⟩
    simpa [h0] using this
  refine ⟨ε, hε, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · have h := key t (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]) ht.1.ne'
    have e : f t = t * (t⁻¹ * f t) := by rw [← mul_assoc, mul_inv_cancel₀ ht.1.ne', one_mul]
    rw [e]
    exact mul_neg_of_pos_of_neg ht.1 h
  · have h := key t (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]) ht.2.ne
    have e : f t = t * (t⁻¹ * f t) := by rw [← mul_assoc, mul_inv_cancel₀ ht.2.ne, one_mul]
    rw [e]
    exact mul_pos_of_neg_of_neg ht.2 h

/-- The quantities of the section at a good chart point with `r > 0`: `H(e₁) = r³ F₁`,
`H(e₂) = H(e₃) = 0`, the slope of `χ₃₂` along `e₂` and `e₃` is `4√3 r² F₂`, and the denominators
`⟨Z_{e_k}, X⟩` do not vanish. -/
private lemma l6h_chart_values {p : ℝ × (Fin 3 → ℝ)} (hp : l6h_good p) (hr : 0 < p.1) :
    p ∈ lieChartDomain ∧ irt_Den (lieChart p) ∧
      phaseHam (lieChart p) (vertex 0) = p.1 ^ 3 * l6h_F1 p ∧
      phaseHam (lieChart p) (vertex 1) = 0 ∧ phaseHam (lieChart p) (vertex 2) = 0 ∧
      ∀ m : Fin 3, (m = 1 ∨ m = 2) →
        irt_dsw 2 1 (lieChart p).2.2 (lieChart p).1
          (iso_extremalField (vertex m) (lieChart p)).2.2
          (iso_extremalField (vertex m) (lieChart p)).1 = 4 * √3 * p.1 ^ 2 * l6h_F2 p := by
  obtain ⟨hc, hd, h1, h2, h0, h0p, hqp, hdom⟩ := l6h_good_facts hp
  have hmem : p ∈ lieChartDomain := by
    refine ⟨hr, ?_, ?_⟩
    · have : √3 - p.2 0 < 1 / p.1 := by rw [lt_div_iff₀ hr]; linarith
      linarith
    · have := (abs_lt.1 hp.2.2).2; linarith
  obtain ⟨-, hH1, hχ, -⟩ := lieChart_spec hmem
  have hH2 : phaseHam (lieChart p) (vertex 2) = 0 := by
    have := poly_hamiltonian_sub (-1) (lieChart p).2.1 (lieChart p).2.2 (lieChart p).1 1 2
    rw [hχ, hH1] at this
    simp only [phaseHam]; linarith
  set c := 1 + p.1 * p.2 0 with hcdef
  have hdet : p.1 ^ 2 + -(1 + p.1 ^ 2) / c * c + 1 = 0 := by field_simp; ring
  have hX : lieX p.1 (p.2 0) = !![p.1, -(1 + p.1 ^ 2) / c; c, -p.1] := rfl
  have hL : lieΛ₁ p.1 (p.2 1) (p.2 2) = !![p.1 ^ 2 * p.2 1,
      (9 / 4 + p.1 ^ 4 * p.2 1 ^ 2) / (3 / 2 - p.1 ^ 2 * p.2 2);
      -(3 / 2) + p.1 ^ 2 * p.2 2, -(p.1 ^ 2 * p.2 1)] := rfl
  have hLC := l6h_lieChart_eq p hc
  have hh := l6h_reducedHam_lieChart p hc hd
  refine ⟨hmem, fun k ↦ ?_, ?_, hH1, hH2, fun m hm ↦ ?_⟩
  · have e0 : traceForm (controlMatrix (vertex 0)) (lieX p.1 (p.2 0)) =
        -(3 + 3 * p.1 ^ 2 - c ^ 2) / (3 * c) := by
      rw [hX, l6h_cm0]
      simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_fin_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      field_simp
      ring
    have e1 : traceForm (controlMatrix (vertex 1)) (lieX p.1 (p.2 0)) =
        2 / 3 * (√3 * p.1 - c) := by
      rw [hX, l6h_cm1]
      simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_fin_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      ring
    have e2 : traceForm (controlMatrix (vertex 2)) (lieX p.1 (p.2 0)) =
        -(2 / 3 * (√3 * p.1 + c)) := by
      rw [hX, l6h_cm2]
      simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_fin_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      ring
    have d0 : traceForm (controlMatrix (vertex 0)) (lieX p.1 (p.2 0)) ≠ 0 := by
      rw [e0]; exact div_ne_zero (neg_ne_zero.2 h0) (mul_ne_zero three_ne_zero hc)
    have d1 : traceForm (controlMatrix (vertex 1)) (lieX p.1 (p.2 0)) ≠ 0 := by
      rw [e1]; exact mul_ne_zero (by norm_num) h1
    have d2 : traceForm (controlMatrix (vertex 2)) (lieX p.1 (p.2 0)) ≠ 0 := by
      rw [e2]; exact neg_ne_zero.2 (mul_ne_zero (by norm_num) h2)
    rw [hLC]
    change traceForm (controlMatrix (vertex k)) (lieX p.1 (p.2 0)) ≠ 0
    fin_cases k
    exacts [d0, d1, d2]
  · rw [hLC]
    change hamiltonian (-1) (lieΛ₁ p.1 (p.2 1) (p.2 2))
      (reducedHam (lieΛ₁ p.1 (p.2 1) (p.2 2)) (lieX p.1 (p.2 0)) • lieΛRShape (lieX p.1 (p.2 0)))
      (lieX p.1 (p.2 0)) (vertex 0) = _
    rw [hX, hL, l6h_ham0_eq _ _ _ _ _ _ hdet hc h0, ← hL, ← hX, hh, l6h_F1]
    ring
  · rw [hLC, hX, hL, l6h_dsw_eq m hm _ _ _ _ _ _ hdet hc h1 h2, ← hL, ← hX, hh, l6h_F2]
    field_simp
    ring

/-- **The switching structure at the chart points near the fixed point** (module docstring): for
`p` near `(0, x̃_out)` with `r > 0` and `q = lieChart p` or `q = lieChartIn p`, `p` lies in `H*`,
`H(e₁) < 0 = H(e₂) = H(e₃)` at `q`, and along the `e₃`-flow from `q`, `H(e₃) < H(e₂)` right after
`q`. -/
theorem eventually_switchStructure :
    ∀ᶠ p in 𝓝[{p | 0 < p.1}] chartPtOut, p ∈ lieChartDomain ∧
      ∀ q ∈ ({lieChart p, lieChartIn p} : Set iso_PhasePt),
        phaseHam q (vertex 0) < 0 ∧ phaseHam q (vertex 1) = 0 ∧ phaseHam q (vertex 2) = 0 ∧
        ∃ ε > 0, ∀ t ∈ Ioo 0 ε,
          phaseHam (iso_vertexFlow 2 q t) (vertex 2) <
            phaseHam (iso_vertexFlow 2 q t) (vertex 1) := by
  filter_upwards [nhdsWithin_le_nhds l6h_eventually_good, self_mem_nhdsWithin] with p hp hr
  obtain ⟨hg, hF1, hF2⟩ := hp
  have hr : 0 < p.1 := hr
  obtain ⟨hmem, hDen, hH0, hH1, hH2, hD⟩ := l6h_chart_values hg hr
  have hneg0 : phaseHam (lieChart p) (vertex 0) < 0 := by
    rw [hH0]; exact mul_neg_of_pos_of_neg (by positivity) hF1
  have hDneg : 4 * √3 * p.1 ^ 2 * l6h_F2 p < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hF2
  -- the derivative of `χ₃₂` along the flow `e_m` from `lieChart p`, at `t = 0`
  have hderiv : ∀ m : Fin 3, (m = 1 ∨ m = 2) →
      HasDerivAt (fun s ↦ irt_chi 2 1 (iso_vertexFlow m (lieChart p) s))
        (4 * √3 * p.1 ^ 2 * l6h_F2 p) 0 := by
    intro m hm
    have h := irt_chi_hasDerivAt (i := 2) (j := 1) (f := iso_vertexFlow m (lieChart p))
      (f' := iso_extremalField (vertex m) (iso_vertexFlow m (lieChart p) 0))
      (ivf_vfX_hasDerivAt m (lieChart p) 0) (ivf_vfΛR_hasDerivAt m (lieChart p) 0)
      (by rw [ivf_vertexFlow_zero]; exact hDen)
    rw [ivf_vertexFlow_zero, hD m hm] at h
    exact h
  have hχ0 : ∀ m : Fin 3, irt_chi 2 1 (iso_vertexFlow m (lieChart p) 0) = 0 := by
    intro m
    rw [ivf_vertexFlow_zero, irt_chi]
    have := poly_hamiltonian_sub (-1) (lieChart p).2.1 (lieChart p).2.2 (lieChart p).1 2 1
    simp only [phaseHam] at hH1 hH2
    rw [hH1, hH2] at this; linarith
  have hsw : ∀ i : Fin 3, vertexSwap i = ![0, 2, 1] i := fun i ↦ rfl
  refine ⟨hmem, fun q hq ↦ ?_⟩
  rcases hq with rfl | rfl
  · refine ⟨hneg0, hH1, hH2, ?_⟩
    obtain ⟨ε, hε, hpos, -⟩ := l6h_sign_of_hasDerivAt (hderiv 2 (Or.inr rfl)) (hχ0 2) hDneg
    refine ⟨ε, hε, fun t ht ↦ ?_⟩
    have h := hpos t ht
    have := poly_hamiltonian_sub (-1) (iso_vertexFlow 2 (lieChart p) t).2.1
      (iso_vertexFlow 2 (lieChart p) t).2.2 (iso_vertexFlow 2 (lieChart p) t).1 2 1
    simp only [irt_chi] at h
    simp only [phaseHam]; linarith
  · have hτ : ∀ (q : iso_PhasePt) (i : Fin 3),
        phaseHam (reinTau q) (vertex i) = phaseHam q (vertex (vertexSwap i)) :=
      fun q i ↦ (switchingFn_reinTau i 0 q).2
    simp only [lieChartIn]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hτ]; exact hneg0
    · rw [hτ]; exact hH2
    · rw [hτ]; exact hH1
    · obtain ⟨ε, hε, -, hneg⟩ := l6h_sign_of_hasDerivAt (hderiv 1 (Or.inl rfl)) (hχ0 1) hDneg
      refine ⟨ε, hε, fun t ht ↦ ?_⟩
      have h := hneg (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rw [iso_vertexFlow_reinTau, hτ, hτ]
      have := poly_hamiltonian_sub (-1) (iso_vertexFlow 1 (lieChart p) (-t)).2.1
        (iso_vertexFlow 1 (lieChart p) (-t)).2.2 (iso_vertexFlow 1 (lieChart p) (-t)).1 2 1
      simp only [irt_chi] at h
      have e1 : vertexSwap 2 = 1 := rfl
      have e2 : vertexSwap 1 = 2 := rfl
      simp only [e1, e2, phaseHam]
      linarith

end SmoothedPolygons
