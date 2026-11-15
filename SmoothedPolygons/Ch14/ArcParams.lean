module

public import SmoothedPolygons.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Chapter 14, N4: the parameters of an `e₂`-arc and the one-step map on them

The real-variable part of the exact structure of an `e₂`-arc (`notes/n4/proof.md`, §1.3, §2–§3),
used to reduce the numerical fact N4 (`UnstableCurveLeavesStarDomain`,
`SmoothedPolygons/Ch14/UnstableCurve.lean`) to the single-step statement `ArcRegionInvariant`
(`SmoothedPolygons/Ch14/ArcRegionInvariant.lean`).

**Departure from the paper.** The book computes the global unstable curve `W^u(q_out)` in
Mathematica and reads off that it reaches the boundary of the star domain (Figure 14.2,
TeX 11951–11991; not certified, REPORT.md E88). The formalization does not follow the curve: it
solves the Reinhardt flow along an `e₂`-arc in closed form (four-term exponential sums), turns the
Reinhardt–Poincaré map into an explicit map of the arc parameters below, and proves N4 from the
single-step statement (INV) (`ArcRegionInvariant`), which is proved in `notes/inv/inv.md` (Lean
proof in progress: `arcRegionInvariant`, `SmoothedPolygons/Ch14/ArcRegionInvariant.lean`). This file
is the part of that argument that involves only real numbers; the real-number part of the proof of
(INV) is in `SmoothedPolygons/Ch14/ArcStepClosed.lean`, `ArcStepRegion.lean`, `ArcStepExit.lean`.

## The parameters

A phase point `q = (X₀, Λ₁, Λ_R)` with `X₀` in the star domain has the arc parameters
(`arcParams`, `SmoothedPolygons/Ch14/ArcNormalForm.lean`): `ε = ρ₁(X₀)`, `Y = 1 + ρ₂(X₀)/ε`,
`f₀`, `g₀` (the normalized cleared switching numerators `N₂₁`, `N₂₃` at `q`), and `q`, `p` (two
pairings of `Λ̂ = Λ₁ + (3/2) J` with nilpotent eigenvectors of `ad(X₀ + P)`). Then
`Y' = 1 + ρ₀(X₀)/ε = (1 + ε²)/(ε² Y)` (proof.md (1.3)), and along the `e₂`-arc, with `τ = t/ε`,
`(√3/(8ε³)) N₂₁ = f(τ)`, `(√3/(8ε³)) N₂₃ = g(τ)` (Theorem 1.3, `arc_normalForm`):
* `f(τ) = -1 + A e^{-τ} + B e^{-2τ} + Y τ e^{-τ}`, `B = Y - 1 + q`, `A = 1 + f₀ - B`;
* `g(τ) = -1 + A' e^{τ} + B' e^{2τ} - Y' τ e^{τ}`, `B' = Y' - 1 + p`, `A' = 1 + g₀ - B'`.
The coefficients `-1`, `Y`, `-Y'` are universal. On a section point `g₀ = 0`, and `q` is one of
the two roots of the quadric relation `rel = 0` (proof.md (2.1), `arcParams_rel`); so the section
is parametrized by `(ε, Y, f₀, p)` and a choice of root, and the Reinhardt–Poincaré map is the
explicit map `step` (Theorem 2.1, `arcParams_reinPoincare`): with `τ_sw` the switching root of `f`
(`tauSw`), `u = e^{-τ_sw}` and `k = Y u - 1` (`stepK`),
`ε_new = k ε`, `Y_new = 1 + (Y' e^{τ_sw} - 1)/k` (equivalently `Y'_new = Y u/k`),
`f₀,new = g(τ_sw)/k²`, `g₀,new = 0`, `p_new = -f'(τ_sw)/k²`, `q_new` a root of `rel = 0`. Which
root is settled by Theorem 1 of `notes/inv/inv.md`: with `s = e^{τ_sw}`,
`q_new = Φ(s)/(Y - s)²` (`ArcParams.qNew`, `arcQ_reinPoincare`), and the other components are
rational in `s` as well (`ArcParams.step_closed`).

## Statements (proof.md numbering)

* (1.4): `f_eq`, `g_eq` (`f = b_Y + f₀ e^{-τ} + q (e^{-2τ} - e^{-τ})` and its mirror);
  `f_zero`, `g_zero`, `hasDerivAt_f`, `hasDerivAt_g_zero` (`g'(0) = g₀ + p`), `F_log`
  (`F(log Y) = A - Y + B/Y + Y log Y`, where `F(τ) = e^τ f(τ)`).
* Lemma 3.1 (`g_pos`): `g₀ = 0`, `p > 0`, `Y' ≥ 2` imply `g > 0` on `(0, ∞)`.
* Lemma 3.2 (`yMinus_le_one`, `F_monotoneOn`, `F_strictAntiOn`, `tauSw_spec`, `tauSw_lt_iff`,
  `tauSw_lt_log_iff`, `f_pos_of_F_log_nonneg`): under P1 (`f₀ > 0`) and P2 (`q ≤ 0`), `F`
  increases on `[0, log y₊]` and strictly decreases on `[log y₊, ∞)`; `f` has exactly one zero
  `τ_sw` on `(0, ∞)`, a sign change with `f'(τ_sw) < 0` and `τ_sw > log y₊`;
  `τ_sw < log Y` iff `F(log Y) < 0`.
* Lemma 3.3 (`f_pos_of_cusp`, the cusp criterion): `A + min(B, 0) > Y` implies `f > 0` on
  `[0, log Y]`.
* Proposition 3.4 (4), the parameter part (`step_spec`, `step_Y'`): the update rules give
  `f₀,new > 0`, `p_new > 0`, `0 < k < 1`, `k < 1/(Y - 1)`, `ε_new < ε`, `r_new > 0`, the
  telescoping `r_new = (ε - ε_new)/2` (Corollary 2.4) and the expansion (3.1)
  `r_new > λ_lb r`, `λ_lb = (Y - 2)/((Y - 1)(Y' - 2))` (`expansionBound`).

## Proofs (the route, proof.md §3)

1. (1.4), `f_zero`, `g_zero`, `F_log`: unfold and `ring` (with `Real.exp_neg`, `Real.exp_log`).
   `hasDerivAt_f`: `HasDerivAt.exp`, `HasDerivAt.mul`, then `ring`.
2. Lemma 3.1: put `G(τ) = e^{-τ} g(τ) = -e^{-τ} + A' + B' e^{τ} - Y' τ`; `G(0) = g₀ = 0`;
   `e^{τ} G'(τ) = B' y² - Y' y + 1` with `y = e^{τ}`; at `y = 1` this is `p > 0` (because
   `A' + B' = 1 + g₀`); its `y`-derivative `2B' y - Y' ≥ 2B' - Y' = Y' - 2 + 2p > 0` for `y ≥ 1`.
   So `G' > 0` on `[0, ∞)`, `G > 0` on `(0, ∞)`, and `g = e^{τ} G > 0`. (Monotonicity from the
   derivative: `strictMonoOn_of_deriv_pos` on `Ici 0`.)
3. Lemma 3.2: `e^{τ} F'(τ) = -(y² - Y y + B) = -(y - y₋)(y - y₊)` with `y = e^{τ}`,
   `y± = (Y ± √((Y - 2)² - 4q))/2` (the discriminant is `Y² - 4B = (Y - 2)² - 4q ≥ 0`); at `y = 1`
   the quadratic is `1 - Y + B = q ≤ 0`, so `y₋ ≤ 1 ≤ y₊`, and `y₊ ≥ (Y + |Y - 2|)/2 =
   max(Y - 1, 1)`. Hence `F' ≥ 0` on `[0, log y₊]` and `F' < 0` on `(log y₊, ∞)`. `F(0) = f₀ > 0`
   and `F(τ) → -∞` (`-e^{τ}` dominates `A + B e^{-τ} + Y τ`); by the intermediate value theorem and
   strict monotonicity `F` has exactly one zero `τ* > log y₊`, `F < 0` after it, and
   `F'(τ*) < 0`. `f = e^{-τ} F` has the same zeros and signs, `f'(τ*) = e^{-τ*} F'(τ*) < 0`, and
   `{τ > 0 | f τ = 0} = {τ*}`, so `tauSw = τ*`. For `L ≥ 0`: if `L ≤ log y₊` then `F(L) > 0` and
   `τ* > L`; otherwise `τ* < L ↔ F(L) < 0` by strict decrease (`tauSw_lt_iff`).
4. Lemma 3.3: on `[0, log Y]`, `-e^{τ} ≥ -Y`, `B e^{-τ} ≥ min(B, 0)`, `Y τ ≥ 0`, so
   `F(τ) ≥ A + min(B, 0) - Y > 0`.
5. `step_spec`: with `τ = τ_sw < log Y` (step 3 and `F(log Y) < 0`) and `u = e^{-τ}`: `k = Y u - 1
   > 0`. `τ > log y₊` gives `u < 1/y₊ ≤ 1/max(Y - 1, 1)`, so `k < Y/max(Y-1, 1) - 1 ≤ 1` and
   `k < 1/(Y - 1)`. `f₀,new = g(τ)/k² > 0` by Lemma 3.1 (`Y' > 2`, `g₀ = 0`, `p > 0`);
   `p_new = -f'(τ)/k² > 0` by step 3. `ε_new = k ε < ε`. `Y'_new = Y u/k` (`step_Y'`, using
   `ε² Y Y' = 1 + ε²`), so `r_new = ε_new (Y'_new - 2)/2 = ε (Y u - 2k)/2 = ε(1 - k)/2
   = (ε - ε_new)/2 > 0`, and `r_new/r = (1 - k)/(Y' - 2) > (1 - 1/(Y - 1))/(Y' - 2) = λ_lb`
   (`r = ε(Y' - 2)/2 > 0`). This holds for every `Y > 1` (for `Y ≤ 2`, `λ_lb ≤ 0`); proof.md states
   it for `Y ≥ 2`.

Numerical checks of all of this against a literal model of the Lean definitions (matrix
exponentials and the quadratures of `iso_vfC`, `iso_vfΛR`): `notes/n4f/check1.py`,
`notes/n4f/check2.py`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- **The parameters of an `e₂`-arc** (proof.md §1.3, §2.1): `ε = ρ₁(X₀)`, `Y = 1 + ρ₂(X₀)/ε`, the
normalized cleared switching numerators `f₀ = f(0)`, `g₀ = g(0)` at the initial point, and the
pairings `q`, `p` of `Λ̂₀ = Λ₁(0) + (3/2) J` with the nilpotent eigenvectors `V_e`, `V_f` of
`ad(X₀ + P)` (Lemma 1.2). `arcParams` (`SmoothedPolygons/Ch14/ArcNormalForm.lean`) computes them
from a phase point. -/
structure ArcParams where
  /-- `ε = ρ₁(X₀)`, the constant value of `ρ₁` along the `e₂`-arc. -/
  eps : ℝ
  /-- `Y = 1 + ρ₂(X₀)/ε`; the arc leaves the star domain at `τ = log Y`. -/
  Y : ℝ
  /-- `f₀ = f(0) = (√3/(8ε³)) N₂₁(q)`. -/
  f0 : ℝ
  /-- `g₀ = g(0) = (√3/(8ε³)) N₂₃(q)`; `0` on the section `χ₂₃ = 0`. -/
  g0 : ℝ
  /-- `q = -(√3/(6ε)) ⟨Λ̂₀, V_e⟩`. -/
  q : ℝ
  /-- `p = (2/(√3 ε)) ⟨Λ̂₀, V_f⟩`. -/
  p : ℝ

namespace ArcParams

variable (a : ArcParams)

/-- `Y' = (1 + ε²)/(ε² Y)`; for a phase point it is `1 + ρ₀(X₀)/ε` (proof.md (1.3),
`arcParams_Y'`). -/
noncomputable def Y' : ℝ := (1 + a.eps ^ 2) / (a.eps ^ 2 * a.Y)

/-- `B = Y - 1 + q`, the coefficient of `e^{-2τ}` in `f`. -/
noncomputable def B : ℝ := a.Y - 1 + a.q

/-- `A = 1 + f₀ - B`, the coefficient of `e^{-τ}` in `f`. -/
noncomputable def A : ℝ := 1 + a.f0 - a.B

/-- `B' = Y' - 1 + p`, the coefficient of `e^{2τ}` in `g`. -/
noncomputable def B' : ℝ := a.Y' - 1 + a.p

/-- `A' = 1 + g₀ - B'`, the coefficient of `e^{τ}` in `g`. -/
noncomputable def A' : ℝ := 1 + a.g0 - a.B'

/-- **The normalized cleared numerator `N₂₁`** along the arc (Theorem 1.3):
`f(τ) = -1 + A e^{-τ} + B e^{-2τ} + Y τ e^{-τ}`. -/
noncomputable def f (τ : ℝ) : ℝ :=
  -1 + a.A * Real.exp (-τ) + a.B * Real.exp (-2 * τ) + a.Y * τ * Real.exp (-τ)

/-- The derivative `f'(τ) = -A e^{-τ} - 2B e^{-2τ} + Y (1 - τ) e^{-τ}` (`hasDerivAt_f`). -/
noncomputable def fDeriv (τ : ℝ) : ℝ :=
  -a.A * Real.exp (-τ) - 2 * a.B * Real.exp (-2 * τ) + a.Y * (1 - τ) * Real.exp (-τ)

/-- **The normalized cleared numerator `N₂₃`** along the arc (Theorem 1.3):
`g(τ) = -1 + A' e^{τ} + B' e^{2τ} - Y' τ e^{τ}`. -/
noncomputable def g (τ : ℝ) : ℝ :=
  -1 + a.A' * Real.exp τ + a.B' * Real.exp (2 * τ) - a.Y' * τ * Real.exp τ

/-- `F(τ) = e^{τ} f(τ) = -e^{τ} + A + B e^{-τ} + Y τ` (proof.md §3); the sign of `F(log Y)` decides
between a switch inside the star domain and an exit (P3). -/
noncomputable def F (τ : ℝ) : ℝ := Real.exp τ * a.f τ

/-- `y₊ = (Y + √((Y - 2)² - 4q))/2`, the larger root of `y² - Y y + B` (Lemma 3.2). -/
noncomputable def yPlus : ℝ := (a.Y + √((a.Y - 2) ^ 2 - 4 * a.q)) / 2

/-- `y₋ = (Y - √((Y - 2)² - 4q))/2`, the smaller root of `y² - Y y + B` (Lemma 3.2). -/
noncomputable def yMinus : ℝ := (a.Y - √((a.Y - 2) ^ 2 - 4 * a.q)) / 2

/-- **The quadric relation** `R(ε, Y, f₀, q, p)` (proof.md (2.1), `κ = 1 + ε²`):
`R = κ²q² - 2q[κ²f₀ - Y²ε²(1 - ε²)p + 2Y²ε² - κY] + Y⁴ε⁴p² + 2Y²ε²(Y - 2)p - 2Y²ε²κf₀p
+ 4Y²ε²κf₀ - 2(2ε² + 1)κYf₀ + κ²f₀² + 4κ²f₀`.
It vanishes at every section point (`arcParams_rel`); it is `det Λ₁ = 9/4` in the parameters
(`arcParams_rel_identity`: `R = (4Y²/3)(9/4 - det Λ₁)`). It does not involve `g₀`. -/
noncomputable def rel : ℝ :=
  (1 + a.eps ^ 2) ^ 2 * a.q ^ 2 -
    2 * a.q * ((1 + a.eps ^ 2) ^ 2 * a.f0 - a.Y ^ 2 * a.eps ^ 2 * (1 - a.eps ^ 2) * a.p +
      2 * a.Y ^ 2 * a.eps ^ 2 - (1 + a.eps ^ 2) * a.Y) +
    a.Y ^ 4 * a.eps ^ 4 * a.p ^ 2 + 2 * a.Y ^ 2 * a.eps ^ 2 * (a.Y - 2) * a.p -
    2 * a.Y ^ 2 * a.eps ^ 2 * (1 + a.eps ^ 2) * a.f0 * a.p +
    4 * a.Y ^ 2 * a.eps ^ 2 * (1 + a.eps ^ 2) * a.f0 -
    2 * (2 * a.eps ^ 2 + 1) * (1 + a.eps ^ 2) * a.Y * a.f0 +
    (1 + a.eps ^ 2) ^ 2 * a.f0 ^ 2 + 4 * (1 + a.eps ^ 2) ^ 2 * a.f0

/-- The chart radius `r = ε (Y' - 2)/2`; for a phase point it is `X₁₁ = (ρ₀ - ρ₁)/2`
(`X00_eq_arcRadius`, `arcParams_radius`). -/
noncomputable def radius : ℝ := a.eps * (a.Y' - 2) / 2

/-- **The switching root** `τ_sw`: the least positive zero of `f` (as `reinSwitchTime` is the
least positive zero of `χ₂₁`, in the time `τ = t/ε`). Under P1 and P2 it is the unique positive
zero (`tauSw_spec`). -/
noncomputable def tauSw : ℝ := sInf {τ : ℝ | 0 < τ ∧ a.f τ = 0}

/-- `k = Y e^{-τ_sw} - 1 = ε_new/ε` (Theorem 2.1). -/
noncomputable def stepK : ℝ := a.Y * Real.exp (-a.tauSw) - 1

/-- **The Reinhardt–Poincaré map on the arc parameters** (Theorem 2.1), with `qNew` the root of the
quadric relation at the new point that the phase point selects: `ε_new = k ε`,
`Y_new = 1 + (Y' e^{τ_sw} - 1)/k`, `f₀,new = g(τ_sw)/k²`, `g₀,new = 0`, `p_new = -f'(τ_sw)/k²`. -/
noncomputable def step (qNew : ℝ) : ArcParams where
  eps := a.stepK * a.eps
  Y := 1 + (a.Y' * Real.exp a.tauSw - 1) / a.stepK
  f0 := a.g a.tauSw / a.stepK ^ 2
  g0 := 0
  q := qNew
  p := -a.fDeriv a.tauSw / a.stepK ^ 2

/-- The lower bound `λ_lb = (Y - 2)/((Y - 1)(Y' - 2))` of the expansion `r_new/r` (proof.md
(3.1)); `λ_lb ≥ 1` is the condition E of the region `𝒢*`. -/
noncomputable def expansionBound : ℝ := (a.Y - 2) / ((a.Y - 1) * (a.Y' - 2))

/-! ### The normal form (1.4) and elementary identities -/

/-- **(1.4)**: `f(τ) = b_Y(τ) + f₀ e^{-τ} + q (e^{-2τ} - e^{-τ})`, with
`b_Y(τ) = -1 + (2 - Y) e^{-τ} + (Y - 1) e^{-2τ} + Y τ e^{-τ}`. -/
theorem f_eq (τ : ℝ) :
    a.f τ = (-1 + (2 - a.Y) * Real.exp (-τ) + (a.Y - 1) * Real.exp (-2 * τ) +
      a.Y * τ * Real.exp (-τ)) + a.f0 * Real.exp (-τ) +
      a.q * (Real.exp (-2 * τ) - Real.exp (-τ)) := by
  simp only [f, A, B]
  ring

/-- **(1.4)**: `g(τ) = b_{Y'}(-τ) + g₀ e^{τ} + p (e^{2τ} - e^{τ})`. -/
theorem g_eq (τ : ℝ) :
    a.g τ = (-1 + (2 - a.Y') * Real.exp τ + (a.Y' - 1) * Real.exp (2 * τ) -
      a.Y' * τ * Real.exp τ) + a.g0 * Real.exp τ + a.p * (Real.exp (2 * τ) - Real.exp τ) := by
  simp only [g, A', B']
  ring

/-- `f(0) = f₀`. -/
theorem f_zero : a.f 0 = a.f0 := by
  simp only [f, A, B, neg_zero, mul_zero, Real.exp_zero]
  ring

/-- `g(0) = g₀`. -/
theorem g_zero : a.g 0 = a.g0 := by
  simp only [g, A', B', mul_zero, Real.exp_zero]
  ring

/-- `f' = fDeriv`. -/
theorem hasDerivAt_f (τ : ℝ) : HasDerivAt a.f (a.fDeriv τ) τ := by
  change HasDerivAt (fun τ => -1 + a.A * Real.exp (-τ) + a.B * Real.exp (-2 * τ) +
    a.Y * τ * Real.exp (-τ)) _ τ
  have h1 : HasDerivAt (fun τ => Real.exp (-τ)) (Real.exp (-τ) * (-1)) τ :=
    (hasDerivAt_neg' τ).exp
  have h2 : HasDerivAt (fun τ => Real.exp (-2 * τ)) (Real.exp (-2 * τ) * (-2 * 1)) τ :=
    ((hasDerivAt_id' τ).const_mul (-2)).exp
  convert (((hasDerivAt_const τ (-1 : ℝ)).add (h1.const_mul a.A)).add (h2.const_mul a.B)).add
    (((hasDerivAt_id' τ).const_mul a.Y).mul h1) using 1
  simp only [fDeriv]
  ring

/-- `g'(0) = g₀ + p`: on the section (`g₀ = 0`) the slope of `g` at the start is `p`. -/
theorem hasDerivAt_g_zero : HasDerivAt a.g (a.g0 + a.p) 0 := by
  change HasDerivAt (fun τ => -1 + a.A' * Real.exp τ + a.B' * Real.exp (2 * τ) -
    a.Y' * τ * Real.exp τ) _ 0
  have h2 : HasDerivAt (fun τ => Real.exp (2 * τ)) (Real.exp (2 * 0) * (2 * 1)) 0 :=
    ((hasDerivAt_id' 0).const_mul 2).exp
  convert ((((hasDerivAt_const 0 (-1 : ℝ)).add ((Real.hasDerivAt_exp 0).const_mul a.A')).add
    (h2.const_mul a.B')).sub (((hasDerivAt_id' 0).const_mul a.Y').mul (Real.hasDerivAt_exp 0)))
    using 1
  simp only [A', B', mul_zero, Real.exp_zero]
  ring

/-- `e^{-2x} = (e^{-x})²`. -/
private lemma exp_neg_two_mul' (x : ℝ) : Real.exp (-2 * x) = Real.exp (-x) ^ 2 := by
  rw [sq, ← Real.exp_add]
  ring_nf

/-- `e^{2x} = (e^{x})²`. -/
private lemma exp_two_mul' (x : ℝ) : Real.exp (2 * x) = Real.exp x ^ 2 := by
  rw [sq, ← Real.exp_add]
  ring_nf

/-- `e^{x} e^{-x} = 1`. -/
private lemma exp_mul_exp_neg (x : ℝ) : Real.exp x * Real.exp (-x) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- `F(log Y) = A - Y + B/Y + Y log Y` (proof.md §3). -/
theorem F_log (hY : 0 < a.Y) :
    a.F (Real.log a.Y) = a.A - a.Y + a.B / a.Y + a.Y * Real.log a.Y := by
  have h1 : Real.exp (-Real.log a.Y) = a.Y⁻¹ := by rw [Real.exp_neg, Real.exp_log hY]
  simp only [F, f, exp_neg_two_mul', h1, Real.exp_log hY]
  field_simp
  ring

/-! ### Lemmas 3.1–3.3 -/

/-- The closed form `F(τ) = -e^{τ} + A + B e^{-τ} + Y τ` (the proof of Lemma 3.2). -/
private lemma F_eq' (τ : ℝ) :
    a.F τ = -Real.exp τ + a.A + a.B * Real.exp (-τ) + a.Y * τ := by
  have h := exp_mul_exp_neg τ
  simp only [F, f, exp_neg_two_mul']
  linear_combination (a.A + a.B * Real.exp (-τ) + a.Y * τ) * h

/-- `F'(τ) = -e^{τ} - B e^{-τ} + Y`. -/
private lemma hasDerivAt_F' (τ : ℝ) :
    HasDerivAt a.F (-Real.exp τ - a.B * Real.exp (-τ) + a.Y) τ := by
  rw [show a.F = fun τ => -Real.exp τ + a.A + a.B * Real.exp (-τ) + a.Y * τ from funext a.F_eq']
  have h1 : HasDerivAt (fun τ => Real.exp (-τ)) (Real.exp (-τ) * (-1)) τ :=
    (hasDerivAt_neg' τ).exp
  convert (((Real.hasDerivAt_exp τ).neg.add_const a.A).add (h1.const_mul a.B)).add
    ((hasDerivAt_id' τ).const_mul a.Y) using 1
  ring

private lemma continuous_F' : Continuous a.F :=
  continuous_iff_continuousAt.2 fun τ => (a.hasDerivAt_F' τ).continuousAt

/-- `f(τ) = e^{-τ} F(τ)`. -/
private lemma f_eq_F (τ : ℝ) : a.f τ = Real.exp (-τ) * a.F τ := by
  rw [F, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- `f'(τ) = e^{-τ} (F'(τ) - F(τ))`. -/
private lemma fDeriv_eq (τ : ℝ) :
    a.fDeriv τ = Real.exp (-τ) * ((-Real.exp τ - a.B * Real.exp (-τ) + a.Y) - a.F τ) := by
  rw [F_eq']
  simp only [fDeriv, exp_neg_two_mul']
  ring

/-- `G(τ) = e^{-τ} g(τ) = -e^{-τ} + A' + B' e^{τ} - Y' τ` (the proof of Lemma 3.1). -/
private noncomputable def G (τ : ℝ) : ℝ := -Real.exp (-τ) + a.A' + a.B' * Real.exp τ - a.Y' * τ

/-- `G'(τ) = e^{-τ} + B' e^{τ} - Y'`. -/
private lemma hasDerivAt_G (τ : ℝ) :
    HasDerivAt a.G (Real.exp (-τ) + a.B' * Real.exp τ - a.Y') τ := by
  change HasDerivAt (fun τ => -Real.exp (-τ) + a.A' + a.B' * Real.exp τ - a.Y' * τ) _ τ
  have h1 : HasDerivAt (fun τ => Real.exp (-τ)) (Real.exp (-τ) * (-1)) τ :=
    (hasDerivAt_neg' τ).exp
  convert ((h1.neg.add_const a.A').add ((Real.hasDerivAt_exp τ).const_mul a.B')).sub
    ((hasDerivAt_id' τ).const_mul a.Y') using 1
  ring

/-- `g(τ) = e^{τ} G(τ)`. -/
private lemma g_eq_G (τ : ℝ) : a.g τ = Real.exp τ * a.G τ := by
  simp only [g, G, exp_two_mul']
  linear_combination exp_mul_exp_neg τ

/-- The discriminant `Y² - 4B = (Y - 2)² - 4q` is nonnegative under P2. -/
private lemma disc_nonneg (h2 : a.q ≤ 0) : 0 ≤ (a.Y - 2) ^ 2 - 4 * a.q := by
  nlinarith [sq_nonneg (a.Y - 2)]

/-- `F'(τ) = -e^{-τ} (e^{τ} - y₋)(e^{τ} - y₊)`. -/
private lemma FDeriv_factor (h2 : a.q ≤ 0) (τ : ℝ) :
    -Real.exp τ - a.B * Real.exp (-τ) + a.Y =
      -Real.exp (-τ) * ((Real.exp τ - a.yMinus) * (Real.exp τ - a.yPlus)) := by
  have h1 := exp_mul_exp_neg τ
  have hs := Real.sq_sqrt (a.disc_nonneg h2)
  simp only [yMinus, yPlus, B]
  linear_combination (Real.exp τ - a.Y) * h1 - Real.exp (-τ) / 4 * hs

private lemma yMinus_le_yPlus : a.yMinus ≤ a.yPlus := by
  simp only [yMinus, yPlus]
  linarith [Real.sqrt_nonneg ((a.Y - 2) ^ 2 - 4 * a.q)]

/-- **Lemma 3.1** (the `e₃` side). If `g₀ = 0`, `p > 0` and `Y' ≥ 2` (i.e. `r ≥ 0`), then `g > 0`
on `(0, ∞)`. -/
theorem g_pos (hg0 : a.g0 = 0) (hp : 0 < a.p) (hY' : 2 ≤ a.Y') {τ : ℝ} (hτ : 0 < τ) :
    0 < a.g τ := by
  have hB' : a.B' = a.Y' - 1 + a.p := rfl
  -- `G' > 0` on `[0, ∞)`: `e^{τ} G'(τ) = B' y² - Y' y + 1 = p + (y - 1)(B'(y + 1) - Y')`, `y = e^τ`
  have hG' : ∀ x, 0 ≤ x → 0 < Real.exp (-x) + a.B' * Real.exp x - a.Y' := by
    intro x hx
    have he : 1 ≤ Real.exp x := Real.one_le_exp hx
    have hB'0 : 0 < a.B' := by rw [hB']; linarith
    have h2B : a.B' * 2 ≤ a.B' * (Real.exp x + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hB'0.le
    have hprod : 0 ≤ (Real.exp x - 1) * (a.B' * (Real.exp x + 1) - a.Y') :=
      mul_nonneg (by linarith) (by rw [hB'] at h2B ⊢; linarith)
    have hq : 0 < 1 + a.B' * Real.exp x ^ 2 - a.Y' * Real.exp x := by
      have hid : 1 + a.B' * Real.exp x ^ 2 - a.Y' * Real.exp x =
          a.p + (Real.exp x - 1) * (a.B' * (Real.exp x + 1) - a.Y') := by
        rw [hB']; ring
      rw [hid]; linarith
    have hid : Real.exp (-x) + a.B' * Real.exp x - a.Y' =
        Real.exp (-x) * (1 + a.B' * Real.exp x ^ 2 - a.Y' * Real.exp x) := by
      linear_combination (-a.B' * Real.exp x + a.Y') * exp_mul_exp_neg x
    rw [hid]
    exact mul_pos (Real.exp_pos _) hq
  have hmono : StrictMonoOn a.G (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0)
      (continuous_iff_continuousAt.2 fun x => (a.hasDerivAt_G x).continuousAt).continuousOn ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [(a.hasDerivAt_G x).deriv]
    exact hG' x (le_of_lt hx)
  have hG0 : a.G 0 = 0 := by
    simp only [G, A', neg_zero, Real.exp_zero, mul_zero, hg0]
    ring
  have h := hmono (le_refl (0 : ℝ) : (0 : ℝ) ∈ Ici 0) (le_of_lt hτ : τ ∈ Ici 0) hτ
  rw [hG0] at h
  rw [g_eq_G]
  exact mul_pos (Real.exp_pos _) h

/-- **Lemma 3.2**, the roots: under P2 (`q ≤ 0`), `y₋ ≤ 1 ≤ y₊` and `y₊ ≥ max(Y - 1, 1)`. -/
theorem yMinus_le_one (h2 : a.q ≤ 0) :
    a.yMinus ≤ 1 ∧ 1 ≤ a.yPlus ∧ max (a.Y - 1) 1 ≤ a.yPlus := by
  -- `√((Y - 2)² - 4q) ≥ |Y - 2|`
  have hs : |a.Y - 2| ≤ √((a.Y - 2) ^ 2 - 4 * a.q) := Real.abs_le_sqrt (by linarith)
  have h1 := le_abs_self (a.Y - 2)
  have h2' := neg_abs_le (a.Y - 2)
  simp only [yMinus, yPlus]
  exact ⟨by linarith, by linarith, max_le (by linarith) (by linarith)⟩

/-- `F' < 0` on `(log y₊, ∞)` under P2. -/
private lemma FDeriv_neg (h2 : a.q ≤ 0) {x : ℝ} (hx : Real.log a.yPlus < x) :
    -Real.exp x - a.B * Real.exp (-x) + a.Y < 0 := by
  obtain ⟨-, hp, -⟩ := a.yMinus_le_one h2
  have he : a.yPlus < Real.exp x := (Real.log_lt_iff_lt_exp (by linarith)).1 hx
  rw [a.FDeriv_factor h2]
  have hprod : 0 < (Real.exp x - a.yMinus) * (Real.exp x - a.yPlus) :=
    mul_pos (by linarith [a.yMinus_le_yPlus]) (by linarith)
  have := mul_pos (Real.exp_pos (-x)) hprod
  linarith

/-- **Lemma 3.2**, the shape of `F`: under P2, `F` increases on `[0, log y₊]`. -/
theorem F_monotoneOn (h2 : a.q ≤ 0) : MonotoneOn a.F (Icc 0 (Real.log a.yPlus)) := by
  obtain ⟨hm, hp, -⟩ := a.yMinus_le_one h2
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) a.continuous_F'.continuousOn
    (fun x _ => (a.hasDerivAt_F' x).differentiableAt.differentiableWithinAt) ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(a.hasDerivAt_F' x).deriv, a.FDeriv_factor h2]
  have he1 : 1 < Real.exp x := Real.one_lt_exp_iff.2 hx.1
  have he2 : Real.exp x < a.yPlus := (Real.lt_log_iff_exp_lt (by linarith)).1 hx.2
  have hprod : (Real.exp x - a.yMinus) * (Real.exp x - a.yPlus) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have := mul_nonneg (Real.exp_pos (-x)).le (neg_nonneg.2 hprod)
  linarith

/-- **Lemma 3.2**, the shape of `F`: under P2, `F` strictly decreases on `[log y₊, ∞)`. -/
theorem F_strictAntiOn (h2 : a.q ≤ 0) : StrictAntiOn a.F (Ici (Real.log a.yPlus)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici _) a.continuous_F'.continuousOn ?_
  intro x hx
  rw [interior_Ici] at hx
  rw [(a.hasDerivAt_F' x).deriv]
  exact a.FDeriv_neg h2 hx

/-- `F(T) < 0` for some `T > L` (`F(τ) → -∞`: `e^{τ} ≥ 1 + τ + τ²/2` dominates
`A + B e^{-τ} + Y τ`). -/
private lemma exists_F_neg (L : ℝ) : ∃ T, L < T ∧ a.F T < 0 := by
  have hA := abs_nonneg a.A
  have hB := abs_nonneg a.B
  have hY := abs_nonneg a.Y
  have hL := le_abs_self L
  have hL0 := abs_nonneg L
  set M := |a.A| + |a.B| + |a.Y| + |L| + 1 with hM
  refine ⟨2 * M, by linarith, ?_⟩
  rw [F_eq']
  have hT : 0 ≤ 2 * M := by linarith
  have hexp := Real.quadratic_le_exp_of_nonneg hT
  have hu0 := Real.exp_pos (-(2 * M))
  have hu : Real.exp (-(2 * M)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hBu : a.B * Real.exp (-(2 * M)) ≤ |a.B| :=
    calc a.B * Real.exp (-(2 * M)) ≤ |a.B| * Real.exp (-(2 * M)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hu0.le
      _ ≤ |a.B| * 1 := mul_le_mul_of_nonneg_left hu hB
      _ = |a.B| := mul_one _
  have hYT : a.Y * (2 * M) ≤ |a.Y| * (2 * M) := mul_le_mul_of_nonneg_right (le_abs_self _) hT
  have hMM : M * (|a.A| + |a.B| + |a.Y| + 1) ≤ M * M :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hM1 : 0 ≤ (M - 1) * (|a.A| + |a.B|) := mul_nonneg (by linarith) (by linarith)
  nlinarith [le_abs_self a.A]

/-- **Lemma 3.2**, the switching root: under P1 (`f₀ > 0`) and P2 (`q ≤ 0`), `τ_sw` is a zero of
`f` with `τ_sw > log y₊ ≥ 0`, `f > 0` on `[0, τ_sw)`, `f < 0` on `(τ_sw, ∞)` (so it is the only
positive zero and a sign change), and `f'(τ_sw) < 0`. -/
theorem tauSw_spec (h1 : 0 < a.f0) (h2 : a.q ≤ 0) :
    0 < a.tauSw ∧ Real.log a.yPlus < a.tauSw ∧ a.f a.tauSw = 0 ∧ a.fDeriv a.tauSw < 0 ∧
      (∀ τ ∈ Ico 0 a.tauSw, 0 < a.f τ) ∧ ∀ τ, a.tauSw < τ → a.f τ < 0 := by
  obtain ⟨-, hp1, -⟩ := a.yMinus_le_one h2
  have hL0 : 0 ≤ Real.log a.yPlus := Real.log_nonneg hp1
  have hF0 : a.F 0 = a.f0 := by rw [F, f_zero, Real.exp_zero, one_mul]
  -- `F(log y₊) ≥ F(0) = f₀ > 0`
  have hFL : 0 < a.F (Real.log a.yPlus) :=
    lt_of_lt_of_le (hF0 ▸ h1) (a.F_monotoneOn h2 ⟨le_rfl, hL0⟩ ⟨hL0, le_rfl⟩ hL0)
  obtain ⟨T, hLT, hFT⟩ := a.exists_F_neg (Real.log a.yPlus)
  -- the intermediate value theorem on `[log y₊, T]`
  obtain ⟨c, hc, hFc⟩ : ∃ c ∈ Icc (Real.log a.yPlus) T, a.F c = 0 :=
    intermediate_value_Icc' hLT.le a.continuous_F'.continuousOn ⟨hFT.le, hFL.le⟩
  have hLc : Real.log a.yPlus < c := lt_of_le_of_ne hc.1 (by rintro rfl; linarith)
  have hpos : ∀ τ ∈ Ico 0 c, 0 < a.F τ := by
    rintro τ ⟨h0, hτc⟩
    rcases le_or_gt τ (Real.log a.yPlus) with hτL | hτL
    · exact lt_of_lt_of_le (hF0 ▸ h1) (a.F_monotoneOn h2 ⟨le_rfl, hL0⟩ ⟨h0, hτL⟩ h0)
    · rw [← hFc]
      exact a.F_strictAntiOn h2 (le_of_lt hτL : τ ∈ Ici _) (hc.1 : c ∈ Ici _) hτc
  have hneg : ∀ τ, c < τ → a.F τ < 0 := by
    intro τ hτ
    rw [← hFc]
    exact a.F_strictAntiOn h2 (hc.1 : c ∈ Ici _) (le_of_lt (hLc.trans hτ) : τ ∈ Ici _) hτ
  have hfc : a.f c = 0 := by rw [f_eq_F, hFc, mul_zero]
  have hset : {τ : ℝ | 0 < τ ∧ a.f τ = 0} = {c} := by
    ext τ
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨h0, hf⟩
      have hF : a.F τ = 0 := by rw [F, hf, mul_zero]
      rcases lt_trichotomy τ c with h | h | h
      · exact absurd hF (hpos τ ⟨h0.le, h⟩).ne'
      · exact h
      · exact absurd hF (hneg τ h).ne
    · rintro rfl
      exact ⟨hL0.trans_lt hLc, hfc⟩
  have hsw : a.tauSw = c := by rw [tauSw, hset, csInf_singleton]
  rw [hsw]
  refine ⟨hL0.trans_lt hLc, hLc, hfc, ?_, ?_, ?_⟩
  · rw [fDeriv_eq, hFc, sub_zero]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (a.FDeriv_neg h2 hLc)
  · intro τ hτ
    rw [f_eq_F]
    exact mul_pos (Real.exp_pos _) (hpos τ hτ)
  · intro τ hτ
    rw [f_eq_F]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (hneg τ hτ)

/-- **Lemma 3.2**, the position of the switch: under P1 and P2, for `L ≥ 0`, `τ_sw < L` if and
only if `F(L) < 0`. -/
theorem tauSw_lt_iff (h1 : 0 < a.f0) (h2 : a.q ≤ 0) {L : ℝ} (hL : 0 ≤ L) :
    a.tauSw < L ↔ a.F L < 0 := by
  obtain ⟨-, -, hz, -, hpos, hneg⟩ := a.tauSw_spec h1 h2
  constructor
  · intro h
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (hneg L h)
  · intro h
    by_contra h'
    rcases (not_lt.1 h').lt_or_eq with h'' | h''
    · have := mul_pos (Real.exp_pos L) (hpos L ⟨hL, h''⟩)
      exact absurd h (not_lt.2 this.le)
    · rw [h'', F, hz, mul_zero] at h
      exact lt_irrefl _ h

/-- **Lemma 3.2**: under P1, P2 and `Y ≥ 1`, the switch is inside the star domain
(`τ_sw < log Y`) if and only if `F(log Y) < 0`. -/
theorem tauSw_lt_log_iff (h1 : 0 < a.f0) (h2 : a.q ≤ 0) (hY : 1 ≤ a.Y) :
    a.tauSw < Real.log a.Y ↔ a.F (Real.log a.Y) < 0 :=
  a.tauSw_lt_iff h1 h2 (Real.log_nonneg hY)

/-- **Lemma 3.2**: under P1, P2 and `Y ≥ 1`, if `F(log Y) ≥ 0` then `f > 0` on `[0, log Y)`. -/
theorem f_pos_of_F_log_nonneg (h1 : 0 < a.f0) (h2 : a.q ≤ 0) (hY : 1 ≤ a.Y)
    (hF : 0 ≤ a.F (Real.log a.Y)) {τ : ℝ} (hτ : τ ∈ Ico 0 (Real.log a.Y)) : 0 < a.f τ := by
  have h : ¬ a.tauSw < Real.log a.Y := fun h => absurd ((a.tauSw_lt_log_iff h1 h2 hY).1 h)
    (not_lt.2 hF)
  exact (a.tauSw_spec h1 h2).2.2.2.2.1 τ ⟨hτ.1, lt_of_lt_of_le hτ.2 (not_lt.1 h)⟩

/-- **Lemma 3.3** (the cusp criterion). If `Y > 1` and `A + min(B, 0) > Y`, then `f > 0` on
`[0, log Y]`. -/
theorem f_pos_of_cusp (hY : 1 < a.Y) (hc : a.Y < a.A + min a.B 0) {τ : ℝ}
    (hτ : τ ∈ Icc 0 (Real.log a.Y)) : 0 < a.f τ := by
  rw [f_eq_F]
  refine mul_pos (Real.exp_pos _) ?_
  rw [F_eq']
  -- on `[0, log Y]`: `-e^{τ} ≥ -Y`, `B e^{-τ} ≥ min(B, 0)`, `Y τ ≥ 0`
  have he : Real.exp τ ≤ a.Y := by
    rw [← Real.exp_log (by linarith : 0 < a.Y)]
    exact Real.exp_le_exp.2 hτ.2
  have hu : Real.exp (-τ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hτ.1])
  have hu0 := Real.exp_pos (-τ)
  have hB : min a.B 0 ≤ a.B * Real.exp (-τ) := by
    rcases le_total a.B 0 with hB | hB
    · rw [min_eq_left hB]
      nlinarith
    · rw [min_eq_right hB]
      positivity
  have hYτ : 0 ≤ a.Y * τ := mul_nonneg (by linarith) hτ.1
  linarith

/-! ### The update rules: Proposition 3.4 (4), (3.1) and Corollary 2.4 on the parameters -/

/-- `Y'_new = Y e^{-τ_sw}/k` (Theorem 2.1), from `ε² Y Y' = 1 + ε²` at the old point. -/
theorem step_Y' (he : 0 < a.eps) (hY : 0 < a.Y) (hk : 0 < a.stepK)
    (h : 1 ≤ a.Y' * Real.exp a.tauSw) (qNew : ℝ) :
    (a.step qNew).Y' = a.Y * Real.exp (-a.tauSw) / a.stepK := by
  have hYY : a.Y' * (a.eps ^ 2 * a.Y) = 1 + a.eps ^ 2 := by
    rw [Y', div_mul_cancel₀]
    positivity
  have hku : a.stepK = a.Y * Real.exp (-a.tauSw) - 1 := rfl
  have heu := exp_mul_exp_neg a.tauSw
  have hden : (a.stepK * a.eps) ^ 2 * (1 + (a.Y' * Real.exp a.tauSw - 1) / a.stepK) =
      a.stepK * a.eps ^ 2 * (a.stepK + a.Y' * Real.exp a.tauSw - 1) := by
    field_simp
    ring
  have hpos : 0 < a.stepK * a.eps ^ 2 * (a.stepK + a.Y' * Real.exp a.tauSw - 1) :=
    mul_pos (by positivity) (by linarith)
  change (1 + (a.stepK * a.eps) ^ 2) /
    ((a.stepK * a.eps) ^ 2 * (1 + (a.Y' * Real.exp a.tauSw - 1) / a.stepK)) = _
  rw [hden, div_eq_div_iff hpos.ne' hk.ne']
  linear_combination (a.stepK * a.eps ^ 2 * (a.stepK - 1)) * hku - a.stepK * hYY -
    a.stepK * a.Y' * a.eps ^ 2 * a.Y * heu

/-- **Proposition 3.4 (4)**, on the parameters, with (3.1) and the telescoping of Corollary 2.4.
Let `ε > 0`, `Y > 1`, `Y' > 2` (`r > 0`), `g₀ = 0`, P1 (`f₀ > 0`), P2 (`q ≤ 0`), P4 (`p > 0`) and
`F(log Y) < 0` (the switch is inside the star domain). Then `0 < k < 1`, `k < 1/(Y - 1)`; for every
choice of `q_new` the new point has P1 and P4 (`f₀,new = g(τ_sw)/k² > 0`,
`p_new = -f'(τ_sw)/k² > 0`), `0 < ε_new < ε`, `r_new = (ε - ε_new)/2 > 0`, and
`r_new > λ_lb r`. -/
theorem step_spec (he : 0 < a.eps) (hY : 1 < a.Y) (hY' : 2 < a.Y') (hg0 : a.g0 = 0)
    (h1 : 0 < a.f0) (h2 : a.q ≤ 0) (h4 : 0 < a.p) (hF : a.F (Real.log a.Y) < 0) (qNew : ℝ) :
    0 < a.stepK ∧ a.stepK < 1 ∧ a.stepK < 1 / (a.Y - 1) ∧
      0 < (a.step qNew).f0 ∧ 0 < (a.step qNew).p ∧
      0 < (a.step qNew).eps ∧ (a.step qNew).eps < a.eps ∧
      (a.step qNew).radius = (a.eps - (a.step qNew).eps) / 2 ∧ 0 < (a.step qNew).radius ∧
      a.expansionBound * a.radius < (a.step qNew).radius := by
  have hY0 : 0 < a.Y := by linarith
  obtain ⟨hτ0, hτL, -, hfd, -, -⟩ := a.tauSw_spec h1 h2
  -- the switch is inside the star domain: `τ_sw < log Y`, so `e^{τ_sw} < Y`
  have heY : Real.exp a.tauSw < a.Y :=
    (Real.lt_log_iff_exp_lt hY0).1 ((a.tauSw_lt_log_iff h1 h2 hY.le).2 hF)
  obtain ⟨-, hp1, hpmax⟩ := a.yMinus_le_one h2
  -- `τ_sw > log y₊`, so `e^{τ_sw} > y₊`
  have hpe : a.yPlus < Real.exp a.tauSw := (Real.log_lt_iff_lt_exp (by linarith)).1 hτL
  have heu := exp_mul_exp_neg a.tauSw
  have hu0 := Real.exp_pos (-a.tauSw)
  have hku : a.stepK = a.Y * Real.exp (-a.tauSw) - 1 := rfl
  have hYp1 : a.Y - 1 ≤ a.yPlus := le_trans (le_max_left _ _) hpmax
  have hk0 : 0 < a.stepK := by
    have := mul_lt_mul_of_pos_right heY hu0
    rw [hku]
    linarith
  -- `y₊ e^{-τ_sw} < 1`
  have hpu : a.yPlus * Real.exp (-a.tauSw) < 1 := by
    have := mul_lt_mul_of_pos_right hpe hu0
    linarith
  have hk1 : a.stepK < 1 := by
    have : a.Y * Real.exp (-a.tauSw) ≤ 2 * a.yPlus * Real.exp (-a.tauSw) :=
      mul_le_mul_of_nonneg_right (by linarith) hu0.le
    rw [hku]
    linarith
  have hkY : a.stepK * (a.Y - 1) < 1 := by
    have h3 : a.Y * Real.exp (-a.tauSw) * (a.Y - 1) ≤ a.Y * Real.exp (-a.tauSw) * a.yPlus :=
      mul_le_mul_of_nonneg_left hYp1 (by positivity)
    have h4 : a.Y * (a.yPlus * Real.exp (-a.tauSw)) < a.Y * 1 := mul_lt_mul_of_pos_left hpu hY0
    rw [hku]
    linarith
  have hkY' : a.stepK < 1 / (a.Y - 1) := by
    rw [lt_div_iff₀ (by linarith)]
    exact hkY
  have hstepeps : (a.step qNew).eps = a.stepK * a.eps := rfl
  have hY'e : 1 ≤ a.Y' * Real.exp a.tauSw := by
    have := Real.one_le_exp hτ0.le
    nlinarith
  -- the telescoping `r_new = ε_new (Y'_new - 2)/2 = ε (Y u - 2k)/2 = (ε - ε_new)/2`
  have hrad : (a.step qNew).radius = (a.eps - (a.step qNew).eps) / 2 := by
    change (a.step qNew).eps * ((a.step qNew).Y' - 2) / 2 = _
    rw [a.step_Y' he hY0 hk0 hY'e qNew, hstepeps]
    have h : a.stepK * (a.Y * Real.exp (-a.tauSw) / a.stepK) = a.Y * Real.exp (-a.tauSw) :=
      mul_div_cancel₀ _ hk0.ne'
    linear_combination (a.eps / 2) * h - (a.eps / 2) * hku
  have hrad0 : 0 < (a.step qNew).radius := by
    rw [hrad, hstepeps]
    nlinarith
  refine ⟨hk0, hk1, hkY', div_pos (a.g_pos hg0 h4 hY'.le hτ0) (pow_pos hk0 2),
    div_pos (neg_pos.2 hfd) (pow_pos hk0 2), mul_pos hk0 he, ?_, hrad, hrad0, ?_⟩
  · rw [hstepeps]
    nlinarith
  · -- `λ_lb r = ε (Y - 2)/(2 (Y - 1)) < ε (1 - k)/2` because `k (Y - 1) < 1`
    rw [hrad, hstepeps]
    have hY'2 : 0 < a.Y' - 2 := by linarith
    have hY1 : 0 < a.Y - 1 := by linarith
    have : a.expansionBound * a.radius = a.eps * (a.Y - 2) / (2 * (a.Y - 1)) := by
      simp only [expansionBound, radius]
      field_simp
    rw [this, div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith [mul_pos he (sub_pos.2 hkY)]

end ArcParams

end SmoothedPolygons
