module

public import SmoothedPolygons.Defs

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
  `τ_sw` on `(0, ∞)`, a sign change with `f'(τ_sw) < 0` and `τ_sw > log y₊`; `τ_sw < log Y` iff
  `F(log Y) < 0`.
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
  sorry

/-- **(1.4)**: `g(τ) = b_{Y'}(-τ) + g₀ e^{τ} + p (e^{2τ} - e^{τ})`. -/
theorem g_eq (τ : ℝ) :
    a.g τ = (-1 + (2 - a.Y') * Real.exp τ + (a.Y' - 1) * Real.exp (2 * τ) -
      a.Y' * τ * Real.exp τ) + a.g0 * Real.exp τ + a.p * (Real.exp (2 * τ) - Real.exp τ) := by
  sorry

/-- `f(0) = f₀`. -/
theorem f_zero : a.f 0 = a.f0 := by
  sorry

/-- `g(0) = g₀`. -/
theorem g_zero : a.g 0 = a.g0 := by
  sorry

/-- `f' = fDeriv`. -/
theorem hasDerivAt_f (τ : ℝ) : HasDerivAt a.f (a.fDeriv τ) τ := by
  sorry

/-- `g'(0) = g₀ + p`: on the section (`g₀ = 0`) the slope of `g` at the start is `p`. -/
theorem hasDerivAt_g_zero : HasDerivAt a.g (a.g0 + a.p) 0 := by
  sorry

/-- `F(log Y) = A - Y + B/Y + Y log Y` (proof.md §3). -/
theorem F_log (hY : 0 < a.Y) :
    a.F (Real.log a.Y) = a.A - a.Y + a.B / a.Y + a.Y * Real.log a.Y := by
  sorry

/-! ### Lemmas 3.1–3.3 -/

/-- **Lemma 3.1** (the `e₃` side). If `g₀ = 0`, `p > 0` and `Y' ≥ 2` (i.e. `r ≥ 0`), then `g > 0`
on `(0, ∞)`. -/
theorem g_pos (hg0 : a.g0 = 0) (hp : 0 < a.p) (hY' : 2 ≤ a.Y') {τ : ℝ} (hτ : 0 < τ) :
    0 < a.g τ := by
  sorry

/-- **Lemma 3.2**, the roots: under P2 (`q ≤ 0`), `y₋ ≤ 1 ≤ y₊` and `y₊ ≥ max(Y - 1, 1)`. -/
theorem yMinus_le_one (h2 : a.q ≤ 0) :
    a.yMinus ≤ 1 ∧ 1 ≤ a.yPlus ∧ max (a.Y - 1) 1 ≤ a.yPlus := by
  sorry

/-- **Lemma 3.2**, the shape of `F`: under P2, `F` increases on `[0, log y₊]`. -/
theorem F_monotoneOn (h2 : a.q ≤ 0) : MonotoneOn a.F (Icc 0 (Real.log a.yPlus)) := by
  sorry

/-- **Lemma 3.2**, the shape of `F`: under P2, `F` strictly decreases on `[log y₊, ∞)`. -/
theorem F_strictAntiOn (h2 : a.q ≤ 0) : StrictAntiOn a.F (Ici (Real.log a.yPlus)) := by
  sorry

/-- **Lemma 3.2**, the switching root: under P1 (`f₀ > 0`) and P2 (`q ≤ 0`), `τ_sw` is a zero of
`f` with `τ_sw > log y₊ ≥ 0`, `f > 0` on `[0, τ_sw)`, `f < 0` on `(τ_sw, ∞)` (so it is the only
positive zero and a sign change), and `f'(τ_sw) < 0`. -/
theorem tauSw_spec (h1 : 0 < a.f0) (h2 : a.q ≤ 0) :
    0 < a.tauSw ∧ Real.log a.yPlus < a.tauSw ∧ a.f a.tauSw = 0 ∧ a.fDeriv a.tauSw < 0 ∧
      (∀ τ ∈ Ico 0 a.tauSw, 0 < a.f τ) ∧ ∀ τ, a.tauSw < τ → a.f τ < 0 := by
  sorry

/-- **Lemma 3.2**, the position of the switch: under P1 and P2, for `L ≥ 0`, `τ_sw < L` if and
only if `F(L) < 0`. -/
theorem tauSw_lt_iff (h1 : 0 < a.f0) (h2 : a.q ≤ 0) {L : ℝ} (hL : 0 ≤ L) :
    a.tauSw < L ↔ a.F L < 0 := by
  sorry

/-- **Lemma 3.2**: under P1, P2 and `Y ≥ 1`, the switch is inside the star domain
(`τ_sw < log Y`) if and only if `F(log Y) < 0`. -/
theorem tauSw_lt_log_iff (h1 : 0 < a.f0) (h2 : a.q ≤ 0) (hY : 1 ≤ a.Y) :
    a.tauSw < Real.log a.Y ↔ a.F (Real.log a.Y) < 0 := by
  sorry

/-- **Lemma 3.2**: under P1, P2 and `Y ≥ 1`, if `F(log Y) ≥ 0` then `f > 0` on `[0, log Y)`. -/
theorem f_pos_of_F_log_nonneg (h1 : 0 < a.f0) (h2 : a.q ≤ 0) (hY : 1 ≤ a.Y)
    (hF : 0 ≤ a.F (Real.log a.Y)) {τ : ℝ} (hτ : τ ∈ Ico 0 (Real.log a.Y)) : 0 < a.f τ := by
  sorry

/-- **Lemma 3.3** (the cusp criterion). If `Y > 1` and `A + min(B, 0) > Y`, then `f > 0` on
`[0, log Y]`. -/
theorem f_pos_of_cusp (hY : 1 < a.Y) (hc : a.Y < a.A + min a.B 0) {τ : ℝ}
    (hτ : τ ∈ Icc 0 (Real.log a.Y)) : 0 < a.f τ := by
  sorry

/-! ### The update rules: Proposition 3.4 (4), (3.1) and Corollary 2.4 on the parameters -/

/-- `Y'_new = Y e^{-τ_sw}/k` (Theorem 2.1), from `ε² Y Y' = 1 + ε²` at the old point. -/
theorem step_Y' (he : 0 < a.eps) (hY : 0 < a.Y) (hk : 0 < a.stepK)
    (h : 1 ≤ a.Y' * Real.exp a.tauSw) (qNew : ℝ) :
    (a.step qNew).Y' = a.Y * Real.exp (-a.tauSw) / a.stepK := by
  sorry

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
  sorry

end ArcParams

end SmoothedPolygons
