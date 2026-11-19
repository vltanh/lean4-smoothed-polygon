module

public import SmoothedPolygons.Ch14.ArcParams

/-!
# Chapter 14, the unstable curve: the one-step map in closed form on the parameters

Part of the formalization's proof, without computer assistance, of the fact behind Figure 14.2
(N4, `UnstableCurveLeavesStarDomain`). **Departure from the paper**, by the user's decision: the
book reads the fact off a computed figure (Figure 14.2, TeX 11951–11991; REPORT.md E88). The proof
is written up in `docs/unstable-curve.pdf` (the note);
`SmoothedPolygons/Ch14/ArcRegionInvariant.lean` lists where each step of the note is.

This file is the real-number part of Theorem 5.1 (the next point in closed form), of
Proposition 3.1 (the relation in the form `R̃`) and of the identity of Lemma 6.3. Lemmas 6.1–6.3
are in `SmoothedPolygons/Ch14/ArcStepRegion.lean`, Lemma 6.4 in
`SmoothedPolygons/Ch14/ArcStepExit.lean`.

## Notation (§5 of the note)

`a : ArcParams` with `g₀ = 0` (a section point), `Y' = (1 + ε²)/(ε² Y)` (`ArcParams.Y'`), and
`x = Y - 2`, `y = Y' - 2` (not `a`, `b`: here `a` is the structure),
`A = 2 - Y + f₀ - q` (`ArcParams.A`), `B = Y - 1 + q` (`ArcParams.B`), `A' = 2 - Y' - p` (the
value of `ArcParams.A'` at `g₀ = 0`, written out below so that no `g₀` appears), `B' = Y' - 1 + p`
(`ArcParams.B'`), `s = e^{τ_sw}` (the switch, `ArcParams.tauSw`), `π(s) = s² - Y s + B`.

## Definitions

* `lamAlpha`, `lamBeta`, `lamGamma`: the coefficients of the costate in the eigenbasis of
  Lemma 2.2 (Proposition 3.1), carried along the arc in (5.4):
  `α = √3 ε (1 + ε²(Y + Y'A - Y B'))`, `β = -(√3/2) ε³ (Y'² - B')`, `γ = 2√3 ε³ (Y² - B)`
  (`iso_vfΛ₁_one_eq_arcParams`, `SmoothedPolygons/Ch14/ArcPoincareMap.lean`).
* `Psi`: `Ψ(s) = (Y B' - Y') s² + (Y'A + Y A') s + (Y'B - Y)`.
* `YNew`, `YNew'`, `f0New`, `pNew`: the parameters of the next point ((5.1)–(5.2)):
  `Y_new = (Y' s² - 2s + Y)/(Y - s)`, `Y'_new = Y/(Y - s)`, `f₀,new = s² Ψ(s)/(Y (Y - s)²)`
  (which is `(s/(Y - s))² g(τ_sw)`), `p_new = π(s)/(Y - s)²`; also `ε_new = ε (Y - s)/s`
  (`step_closed`).
* `psiE`: `ψ(s) = -3Y' s³ + (2YY' + 2) s² - Y²`, the expansion condition at the next point
  (Lemma 6.3, `E_new_iff`).
* `relT`: `R̃ = (Y'(f₀ - q) - Y p)² - 4pq + 2(YY' - 1)(y q + x p) + 2Y'(3 - xy) f₀` ((3.1)),
  with `R = Y² ε⁴ R̃` (`rel_eq`, Proposition 3.1).

## Statements

* `rel_eq` (Proposition 3.1): `R = Y² ε⁴ R̃`.
* `exp_tauSw_spec` (Lemma 4.3 in the variable `s = e^{τ_sw}`).
* `Y_mul_eq_of_f_eq_zero`, `g_div_sq_eq_f0New`, `neg_fDeriv_div_sq_eq_pNew`: the update rules of
  `f₀` and `p` at a zero of `f` (also used by `arcParams_reinPoincare`).
* `step_closed` (Theorem 5.1 on the parameters): `step` in closed form.
* `E_new_iff` (Lemma 6.3): the expansion condition at the next point iff `ψ(s) ≥ 0`.

All identities below were also checked exactly with sympy; the Lean proofs do not depend on these
checks.
-/

@[expose] public section

namespace SmoothedPolygons

namespace ArcParams

variable (a : ArcParams)

/-! ### The coefficients of the costate along the arc ((5.4)) -/

/-- (5.4): `α = √3 ε (1 + ε²(Y + Y'A - Y B'))`, the coefficient of `X(t) + P` in
`Λ₁(t) = α (X(t) + P) + β u⁻² V_e(t) + γ u² V_f(t)` on a section point
(`iso_vfΛ₁_one_eq_arcParams`). It is `2ε² ⟨Λ₁(0), X₀ + P⟩`. -/
noncomputable def lamAlpha : ℝ :=
  √3 * a.eps * (1 + a.eps ^ 2 * (a.Y + a.Y' * a.A - a.Y * a.B'))

/-- (5.4): `β = -(√3/2) ε³ (Y'² - B')`, the coefficient of `u⁻² V_e(t)`; it is
`ε² ⟨Λ₁(0), V_f⟩`. -/
noncomputable def lamBeta : ℝ := -(√3 / 2) * a.eps ^ 3 * (a.Y' ^ 2 - a.B')

/-- (5.4): `γ = 2√3 ε³ (Y² - B)`, the coefficient of `u² V_f(t)`; it is
`ε² ⟨Λ₁(0), V_e⟩`. -/
noncomputable def lamGamma : ℝ := 2 * √3 * a.eps ^ 3 * (a.Y ^ 2 - a.B)

/-! ### The closed forms of Theorem 5.1 ((5.1)–(2.1)) -/

/-- (5.2): `Ψ(s) = (Y B' - Y') s² + (Y'A + Y A') s + (Y'B - Y)`, with `A' = 2 - Y' - p`;
`f₀,new = s² Ψ(s)/(Y (Y - s)²)` (`f0New`). -/
noncomputable def Psi (s : ℝ) : ℝ :=
  (a.Y * a.B' - a.Y') * s ^ 2 + (a.Y' * a.A + a.Y * (2 - a.Y' - a.p)) * s + (a.Y' * a.B - a.Y)

/-- Lemma 6.3: `ψ(s) = -3Y' s³ + (2YY' + 2) s² - Y²`; E holds at the image iff
`ψ(s) ≥ 0` (`E_new_iff`). -/
noncomputable def psiE (s : ℝ) : ℝ := -3 * a.Y' * s ^ 3 + (2 * a.Y * a.Y' + 2) * s ^ 2 - a.Y ^ 2

/-- (3.1): `R̃ = (Y'(f₀ - q) - Y p)² - 4pq + 2(YY' - 1)((Y' - 2) q + (Y - 2) p)
+ 2Y'(3 - (Y - 2)(Y' - 2)) f₀`, with `R = Y² ε⁴ R̃` (`rel_eq`). -/
noncomputable def relT : ℝ :=
  (a.Y' * (a.f0 - a.q) - a.Y * a.p) ^ 2 - 4 * a.p * a.q +
    2 * (a.Y * a.Y' - 1) * ((a.Y' - 2) * a.q + (a.Y - 2) * a.p) +
    2 * a.Y' * (3 - (a.Y - 2) * (a.Y' - 2)) * a.f0

/-- (5.1): `Y_new = (Y' s² - 2s + Y)/(Y - s)`. -/
noncomputable def YNew (s : ℝ) : ℝ := (a.Y' * s ^ 2 - 2 * s + a.Y) / (a.Y - s)

/-- (5.1): `Y'_new = Y/(Y - s)`. -/
noncomputable def YNew' (s : ℝ) : ℝ := a.Y / (a.Y - s)

/-- (5.2): `f₀,new = s² Ψ(s)/(Y (Y - s)²)`. -/
noncomputable def f0New (s : ℝ) : ℝ := s ^ 2 * a.Psi s / (a.Y * (a.Y - s) ^ 2)

/-- (5.2): `p_new = π(s)/(Y - s)²`, `π(s) = s² - Y s + B`. -/
noncomputable def pNew (s : ℝ) : ℝ := (s ^ 2 - a.Y * s + a.B) / (a.Y - s) ^ 2

/-! ### Proposition 3.1, Lemma 4.3 in `s`, Theorem 5.1 on the parameters, Lemma 6.3 -/

/-- **Proposition 3.1** (pure algebra): `R = Y² ε⁴ R̃`, the relation `R = 0` (`rel`, which is
`det Λ₁ = 9/4` by `arcParams_rel_identity`) in the form (3.1) of the note (`relT`). Lemma 6.1
applies it at the next point, where it rearranges to
`2Y'(xy - 3) f₀ = 2q[(YY' - 1) y - 2p] + (Y'(f₀ - q) - Y p)² + 2(YY' - 1) x p`.

Route: substitute `Y' = (1 + ε²)/(ε² Y)` (so `YY' - 1 = 1/ε²` and `ε² Y Y' = 1 + ε²`); then
`unfold rel relT Y'`, `field_simp`, `ring`. The note derives (3.1) from the eigenbasis expansion
`Λ₁ = α (X₀ + P) + β V_e + γ V_f` (`lamAlpha`, `lamBeta`, `lamGamma`): `det Λ₁ = 9/4` reads
`α² + 4βγ + 9ε² = 0`, and `α² + 4βγ + 9ε² = 3ε² R̃/(YY' - 1)²`, which is its form (3.2),
`(3 - xy + Y'(f₀ - q) - Y p)² + 3(YY' - 1)² = 4(Y² - B)(Y'² - B')`. Lean proves `det Λ₁ = 9/4`
in the parameters directly in the frame (`arcParams_rel_identity`), the same computation
organized without the basis. -/
theorem rel_eq (he : a.eps ≠ 0) (hY : a.Y ≠ 0) : a.rel = a.Y ^ 2 * a.eps ^ 4 * a.relT := by
  unfold rel relT Y'
  field_simp
  ring

/-- **Lemma 4.3 in the variable `s = e^{τ_sw}`** (§5, "Switching"). Under P1
(`f₀ > 0`), P2 (`q ≤ 0`), `Y ≥ 1` and `F(log Y) < 0`, the switch `s = e^{τ_sw}` satisfies
`Y - 1 < s`, `1 < s < Y`, `π(s) = s² - Y s + B > 0` (`s > y₊`) and `F(log s) = 0`.

Route: `tauSw_spec` (`τ_sw > 0`, `τ_sw > log y₊`, `f(τ_sw) = 0`), `yMinus_le_one`
(`y₋ ≤ 1 ≤ y₊`, `max(Y - 1, 1) ≤ y₊`) and `tauSw_lt_log_iff` (`τ_sw < log Y`). Then
`s > y₊ ≥ Y - 1` (`Real.exp_lt_exp`, `Real.exp_log` with `y₊ ≥ 1 > 0`), `s > 1`
(`Real.one_lt_exp_iff`), `s < Y`. For `π(s) > 0`: `π(y) = (y - y₊)(y - y₋)` (`y₊ + y₋ = Y`,
`y₊ y₋ = B` from `√((Y - 2)² - 4q)² = Y² - 4B`, `Real.sq_sqrt`, the radicand is `≥ 0` as `q ≤ 0`),
and `s > y₊ ≥ 1 ≥ y₋`. `F(log s) = F(τ_sw) = e^{τ_sw} f(τ_sw) = 0` (`Real.log_exp`). -/
theorem exp_tauSw_spec (h1 : 0 < a.f0) (h2 : a.q ≤ 0) (hY : 1 ≤ a.Y)
    (hF : a.F (Real.log a.Y) < 0) :
    a.Y - 1 < Real.exp a.tauSw ∧ 1 < Real.exp a.tauSw ∧ Real.exp a.tauSw < a.Y ∧
      0 < Real.exp a.tauSw ^ 2 - a.Y * Real.exp a.tauSw + a.B ∧
      a.F (Real.log (Real.exp a.tauSw)) = 0 := by
  obtain ⟨hτ0, hτp, hfτ, -, -, -⟩ := a.tauSw_spec h1 h2
  obtain ⟨hm1, hp1, hpY⟩ := a.yMinus_le_one h2
  have hτY := (a.tauSw_lt_log_iff h1 h2 hY).2 hF
  have hyp0 : 0 < a.yPlus := by linarith
  have hsp : a.yPlus < Real.exp a.tauSw := by
    rw [← Real.exp_log hyp0]; exact Real.exp_lt_exp.2 hτp
  have hsY : Real.exp a.tauSw < a.Y := by
    rw [← Real.exp_log (by linarith : (0:ℝ) < a.Y)]; exact Real.exp_lt_exp.2 hτY
  have hs1 : 1 < Real.exp a.tauSw := Real.one_lt_exp_iff.2 hτ0
  refine ⟨lt_of_le_of_lt ((le_max_left _ _).trans hpY) hsp, hs1, hsY, ?_, ?_⟩
  · -- `π(y) = (y - y₊)(y - y₋)`
    have hrad : 0 ≤ (a.Y - 2) ^ 2 - 4 * a.q := by nlinarith [sq_nonneg (a.Y - 2)]
    have hsq := Real.sq_sqrt hrad
    have e : Real.exp a.tauSw ^ 2 - a.Y * Real.exp a.tauSw + a.B =
        (Real.exp a.tauSw - a.yPlus) * (Real.exp a.tauSw - a.yMinus) := by
      unfold yPlus yMinus B
      linear_combination (1 / 4 : ℝ) * hsq
    rw [e]
    exact mul_pos (by linarith) (by linarith)
  · rw [Real.log_exp]
    unfold F
    rw [hfτ, mul_zero]

private lemma exp_two_mul_eq (τ : ℝ) :
    Real.exp (2 * τ) = Real.exp τ ^ 2 ∧ Real.exp (-2 * τ) = (Real.exp τ ^ 2)⁻¹ ∧
      Real.exp (-τ) = (Real.exp τ)⁻¹ := by
  have h2 : Real.exp (2 * τ) = Real.exp τ ^ 2 := by
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  refine ⟨h2, ?_, Real.exp_neg τ⟩
  rw [← h2, ← Real.exp_neg]
  ring_nf

/-- **At a zero `τ` of `f`**, with `s = e^{τ}`: `Y τ = s - A - B/s` (step 1 of `step_closed`). -/
theorem Y_mul_eq_of_f_eq_zero {τ : ℝ} (hf : a.f τ = 0) :
    a.Y * τ = Real.exp τ - a.A - a.B / Real.exp τ := by
  obtain ⟨-, h2', h1⟩ := exp_two_mul_eq τ
  have hs0 : Real.exp τ ≠ 0 := (Real.exp_pos _).ne'
  have e : a.Y * τ - (Real.exp τ - a.A - a.B / Real.exp τ) = Real.exp τ * a.f τ := by
    simp only [ArcParams.f, h1, h2']
    field_simp
    ring
  linear_combination e + Real.exp τ * hf

/-- **The update rule of `f₀` at a zero `τ` of `f`** with `g₀ = 0` (step 6 of `step_closed`):
`g(τ)/k² = s² Ψ(s)/(Y (Y - s)²)`, `s = e^{τ}`, `k = Y e^{-τ} - 1`. -/
theorem g_div_sq_eq_f0New (hg0 : a.g0 = 0) {τ : ℝ} (hf : a.f τ = 0) (hY : a.Y ≠ 0)
    (hsY : a.Y - Real.exp τ ≠ 0) :
    a.g τ / (a.Y * Real.exp (-τ) - 1) ^ 2 = a.f0New (Real.exp τ) := by
  obtain ⟨h2, -, h1⟩ := exp_two_mul_eq τ
  have hs0 : Real.exp τ ≠ 0 := (Real.exp_pos _).ne'
  have hτ := a.Y_mul_eq_of_f_eq_zero hf
  have hg : a.g τ = (-a.Y + a.Y * a.A' * Real.exp τ + a.Y * a.B' * Real.exp τ ^ 2 -
      a.Y' * Real.exp τ * (Real.exp τ - a.A - a.B / Real.exp τ)) / a.Y := by
    rw [← hτ]
    simp only [ArcParams.g, h2]
    field_simp
  have hk : a.Y * (Real.exp τ)⁻¹ - 1 = (a.Y - Real.exp τ) / Real.exp τ := by
    field_simp
  rw [hg, h1, hk]
  simp only [ArcParams.f0New, ArcParams.Psi, ArcParams.A', ArcParams.B', hg0]
  field_simp
  ring

/-- **The update rule of `p` at a zero `τ` of `f`** (step 7 of `step_closed`):
`-f'(τ)/k² = π(s)/(Y - s)²`, `s = e^{τ}`, `k = Y e^{-τ} - 1`. -/
theorem neg_fDeriv_div_sq_eq_pNew {τ : ℝ} (hf : a.f τ = 0) (hsY : a.Y - Real.exp τ ≠ 0) :
    -a.fDeriv τ / (a.Y * Real.exp (-τ) - 1) ^ 2 = a.pNew (Real.exp τ) := by
  obtain ⟨-, h2', h1⟩ := exp_two_mul_eq τ
  have hs0 : Real.exp τ ≠ 0 := (Real.exp_pos _).ne'
  have hτ := a.Y_mul_eq_of_f_eq_zero hf
  have hd : a.fDeriv τ = -a.A / Real.exp τ - 2 * a.B / Real.exp τ ^ 2 +
      (a.Y - (Real.exp τ - a.A - a.B / Real.exp τ)) / Real.exp τ := by
    rw [← hτ]
    simp only [ArcParams.fDeriv, h1, h2']
    field_simp
  have hk : a.Y * (Real.exp τ)⁻¹ - 1 = (a.Y - Real.exp τ) / Real.exp τ := by
    field_simp
  rw [hd, h1, hk]
  simp only [ArcParams.pNew]
  field_simp
  ring

/-- **Theorem 5.1 on the parameters**: the one-step map `step` (Theorem 5.1) in
closed form, with `s = e^{τ_sw}`: `Y_new = (Y' s² - 2s + Y)/(Y - s)`, `Y'_new = Y/(Y - s)`,
`f₀,new = s² Ψ(s)/(Y (Y - s)²)`, `p_new = π(s)/(Y - s)²`, `ε_new = ε (Y - s)/s`, for every choice
of `q_new` (the `q` component of `step` is its argument; the proof of Theorem 6.5 only uses the
relation at the next point). The `f₀` and `p` components use `f(τ_sw) = 0` to eliminate
`τ_sw = log s`.

Route. Put `τ = τ_sw`, `s = e^{τ}`; by `exp_tauSw_spec`, `1 < s < Y`, and by `tauSw_spec`
`f(τ) = 0`. Write `e^{-τ} = 1/s`, `e^{-2τ} = 1/s²`, `e^{2τ} = s²` (`Real.exp_neg`, `Real.exp_add`
or `Real.exp_nat_mul`). Then:
1. `f(τ) = 0` reads `-1 + A/s + B/s² + Y τ/s = 0`, i.e. `Y τ = s - A - B/s` (multiply by `s`;
   `Y_mul_eq_of_f_eq_zero`).
2. `k = stepK = Y/s - 1 = (Y - s)/s`, nonzero.
3. `(step x).eps = k ε = ε (Y - s)/s` (definition).
4. `(step x).Y = 1 + (Y' s - 1)/k = (Y' s² - 2s + Y)/(Y - s)`: `field_simp`, `ring`.
5. `(step x).Y' = (1 + ε_new²)/(ε_new² Y_new) = Y/(Y - s)`: with `ε_new = ε (Y - s)/s` and
   `Y_new = N_Y/(Y - s)`, `N_Y = Y' s² - 2s + Y`, this is
   `s² + ε²(Y - s)² = ε² Y N_Y`, true by `ε² Y Y' = 1 + ε²` (`field_simp`, `ring`). It needs
   `N_Y ≠ 0`: `N_Y > 0` because `Y Y' = (1 + ε²)/ε² > 1` (discriminant `4 - 4YY' < 0`,
   `nlinarith [sq_nonneg (Y' s - 1)]`: `Y' N_Y = (Y' s - 1)² + (YY' - 1)`). (`step_Y'` does not
   apply directly: its hypothesis `1 ≤ Y' e^{τ}` need not hold here.)
6. `(step x).f0 = g(τ)/k²` with `g(τ) = -1 + A' s + B' s² - Y' τ s` and `A' = 2 - Y' - p`
   (`g₀ = 0`). By step 1, `Y g(τ) = -Y + Y A' s + Y B' s² - Y' s (s - A - B/s) = Ψ(s)`, so
   `g(τ)/k² = s² Ψ(s)/(Y (Y - s)²)` (`g_div_sq_eq_f0New`).
7. `(step x).p = -f'(τ)/k²` with `f'(τ) = -A/s - 2B/s² + Y(1 - τ)/s`
   (`fDeriv`); by step 1 `f'(τ) = (Y s - s² - B)/s²`, so `-f'(τ)/k² = (s² - Y s + B)/(Y - s)²`
   (`neg_fDeriv_div_sq_eq_pNew`). -/
theorem step_closed (he : 0 < a.eps) (hY : 1 < a.Y) (hg0 : a.g0 = 0) (h1 : 0 < a.f0)
    (h2 : a.q ≤ 0) (hF : a.F (Real.log a.Y) < 0) (x : ℝ) :
    (a.step x).Y = a.YNew (Real.exp a.tauSw) ∧ (a.step x).Y' = a.YNew' (Real.exp a.tauSw) ∧
      (a.step x).f0 = a.f0New (Real.exp a.tauSw) ∧ (a.step x).p = a.pNew (Real.exp a.tauSw) ∧
      (a.step x).eps = a.eps * (a.Y - Real.exp a.tauSw) / Real.exp a.tauSw := by
  obtain ⟨-, hs1, hsY, -, -⟩ := a.exp_tauSw_spec h1 h2 hY.le hF
  have hfτ := (a.tauSw_spec h1 h2).2.2.1
  set τ := a.tauSw with hτdef
  set s := Real.exp τ with hsdef
  have hs0 : 0 < s := by positivity
  have hYs : 0 < a.Y - s := by linarith
  have hY0 : 0 < a.Y := by linarith
  have em1 : Real.exp (-τ) = s⁻¹ := Real.exp_neg τ
  have hk : a.stepK = (a.Y - s) / s := by
    unfold stepK; rw [em1]; field_simp
  have hεn : (a.step x).eps = a.eps * (a.Y - s) / s := by
    change a.stepK * a.eps = _
    rw [hk]; ring
  have hYn : (a.step x).Y = a.YNew s := by
    change 1 + (a.Y' * Real.exp a.tauSw - 1) / a.stepK = _
    rw [hk]; unfold YNew
    field_simp
    ring
  refine ⟨hYn, ?_, ?_, ?_, hεn⟩
  · -- `Y'_new = Y/(Y - s)`, from `ε² Y Y' = 1 + ε²`
    have hYY : a.eps ^ 2 * a.Y * a.Y' = 1 + a.eps ^ 2 := by
      unfold Y'; field_simp
    have hN : 0 < a.Y' * s ^ 2 - 2 * s + a.Y := by
      have hY'0 : 0 < a.Y' := by unfold Y'; positivity
      have hYY1 : 0 < a.Y * a.Y' - 1 := by
        have : a.eps ^ 2 * (a.Y * a.Y' - 1) = 1 := by linear_combination hYY
        have he2 : 0 < a.eps ^ 2 := by positivity
        by_contra h; push Not at h; nlinarith
      have : a.Y' * (a.Y' * s ^ 2 - 2 * s + a.Y) = (a.Y' * s - 1) ^ 2 + (a.Y * a.Y' - 1) := by ring
      have : 0 < a.Y' * (a.Y' * s ^ 2 - 2 * s + a.Y) := by nlinarith [sq_nonneg (a.Y' * s - 1)]
      exact pos_of_mul_pos_right this hY'0.le
    change (1 + (a.step x).eps ^ 2) / ((a.step x).eps ^ 2 * (a.step x).Y) = _
    rw [hεn, hYn]; unfold YNew YNew'
    rw [div_eq_div_iff (by positivity) hYs.ne']
    field_simp
    linear_combination (-s ^ 2) * hYY
  · change a.g τ / (a.Y * Real.exp (-τ) - 1) ^ 2 = _
    exact a.g_div_sq_eq_f0New hg0 hfτ hY0.ne' hYs.ne'
  · change -a.fDeriv τ / (a.Y * Real.exp (-τ) - 1) ^ 2 = _
    exact a.neg_fDeriv_div_sq_eq_pNew hfτ hYs.ne'

/-- **Lemma 6.3**, the identity (the expansion condition at the next point): for `s ≠ Y`,
`(Y_new - 1)(Y'_new - 2) ≤ Y_new - 2` iff `ψ(s) ≥ 0`.

Route: the identity `(Y - s)² [(Y_new - 2) - (Y_new - 1)(Y'_new - 2)] = ψ(s)` (`unfold YNew YNew'
psiE`, `field_simp`, `ring`), and `(Y - s)² > 0`
(`mul_nonneg_iff_of_pos_left`, `sub_nonneg`). -/
theorem E_new_iff {s : ℝ} (hs : s ≠ a.Y) :
    (a.YNew s - 1) * (a.YNew' s - 2) ≤ a.YNew s - 2 ↔ 0 ≤ a.psiE s := by
  have hYs : a.Y - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
  have e : a.psiE s = (a.Y - s) ^ 2 * ((a.YNew s - 2) - (a.YNew s - 1) * (a.YNew' s - 2)) := by
    unfold psiE YNew YNew'
    field_simp
    ring
  rw [e, mul_nonneg_iff_of_pos_left (by positivity), sub_nonneg]

end ArcParams

end SmoothedPolygons
