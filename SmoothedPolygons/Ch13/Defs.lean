module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Chapter 13: the Fuller system for triangular control — definitions

The objects of §13.2–§13.3 of Hales–Vajjha, *Packings of Smoothed Polygons* (Chapter 13,
"Fuller System for Triangular Control", TeX 10610–11455), and the vocabulary that Chapters 14–16
use:

* the sesquilinear form `RR(z₁, z₂) = Re(z̄₁ z₂)` of Chapter 10 (TeX 8456), the only coordinate of
  Chapters 10–11 that Chapter 13 needs;
* the cube root of unity `ζ = exp(2πi/3)`, the control vertices `V_T = {1, ζ, ζ²}` and their convex
  hull `U_T` (TeX 10683–10696, 11100);
* the Fuller system (13.2.1) `z₃' = z₂, z₂' = z₁, z₁' = -iu` (`IsTrajectory`, in Carathéodory's
  sense for a measurable control), its explicit solution (13.2.2) for a constant control (`flow`),
  the Hamiltonian `H_F` (13.2.3–4) (`ham`), the maximum condition (13.2.5) (`MaxCondition`), the
  condition `H_F = 0` (13.2.6), the solutions of Lemmas 13.2.1–13.2.3 (`IsExtremal`) and the
  maximized Hamiltonian `H_F⁺` (`hamMax`);
* the switching function `χ^u_{v₁-v₂}(t, z⁰) = RR(v₁ - v₂, z₃(t, z⁰, u))/√3` (TeX 10755–10784);
* the time reversal `τ(z₁, z₂, z₃) = (z̄₁, -z̄₂, z̄₃)` (TeX 10834–10837) and the virial rescaling
  `(z₁, z₂, z₃) ↦ (r z₁, r² z₂, r³ z₃)` (Lemma 13.2.1; the virial group, TeX 10820–10827);
* the walls `𝒲 = ℝ_{≤0} ∪ ℝ_{≤0}ζ ∪ ℝ_{≤0}ζ²` (TeX 10910–10926), the control vectors and the
  lexicographic order (TeX 10934–10953);
* the first control and the first switching time (TeX 10747–10753), the most recent control and
  the most recent switching time (TeX 10880–10889).

## Conventions

A point `z = (z₁, z₂, z₃)` of `ℂ³` is `z : Fin 3 → ℂ` with **`z 0 = z₁`, `z 1 = z₂`, `z 2 = z₃`**
(the index is shifted by one). The book's `z₀ := -iu` is not a coordinate of the state.

Trajectories are taken in Carathéodory's sense, as in `SmoothedPolygons.IsStateTrajectory`: the
control is measurable and each coordinate is the indefinite integral of its right-hand side. The
maximum condition (13.2.5) and `H_F = 0` (13.2.6), which the book writes for every `t`, are imposed
for almost every `t`: a trajectory does not see a change of the control on a null set.

## The first control and the first switching time (robustness)

The book defines the first control of `z⁰ ∈ ℂ³ ∖ 0` as "the optimal control starting at switching
time `t = 0` until the first positive switching time `t_sw > 0`" (TeX 10747–10753), and the
Fuller–Poincaré map as the value at `t_sw` (TeX 11236–11251). These notions are defined
semantically, for every `z⁰`, by the maximum condition along the constant-control trajectory,
without choosing roots of polynomials:

* `IsFirstControl z⁰ u`: `u ∈ V_T` and the constant control `u` satisfies the maximum condition
  along its own trajectory `t ↦ flow t z⁰ u` on some `[0, ε]`, `ε > 0`. It is unique
  (`IsFirstControl.unique`, `SmoothedPolygons/Ch13/FirstControl.lean`), exists for
  `z⁰ ≠ 0` (Lemma 13.2.6), and every extremal from `z⁰` with a measurable control follows it up to
  the first switching time (`eq_flow_of_maxCondition`, `SmoothedPolygons/Ch13/Extremals.lean`);
* `firstControl z⁰`: the first control when it exists (junk value `1` otherwise, only at `z⁰ = 0`);
* `firstSwitchTime z⁰ = inf {t > 0 | the control firstControl z⁰ is not maximizing at
  flow t z⁰ (firstControl z⁰)}`: the time at which the first control stops being optimal. It is
  positive and finite for `z⁰ ≠ 0` (Lemma 13.2.6, Corollary 13.2.7). A double root of a switching
  function at which the control stays optimal (a tangency) is not a switch.

This is the honest Pontryagin dynamics, faithful to TeX 10747–10753 and to Lemma 13.2.6: the first
control is the control that the maximum principle selects at `t = 0`, and the trajectory switches
when that control stops being optimal. The Poincaré map
`F(z⁰) = flow (firstSwitchTime z⁰) z⁰ (firstControl z⁰)` is then defined at every point
(`SmoothedPolygons/Ch13/PoincareMap.lean`).

**Chapter 15's cell maps differ from `poincare`.** Chapter 15 works with maps on closed cells
obtained by continuous extension from the interiors, and they are not restrictions of `poincare`:
* on the closed 2-cell `𝒞₂^A` the first switching time is taken to be a root of `χ_{A,0}`
  (TeX 12413–12422), double roots included, although at a double root the control stays optimal
  (a tangency) and `poincare` does not switch there;
* the identity `F⁻¹ = τ F τ` is used on closed cells (TeX 12324–12328); for `poincare` it fails
  where the first control equals the most recent one (`poincare_tau_poincare` assumes a genuine
  switching point);
* on parts of the faces of the big cells the switching time tends to `0` (TeX 12199–12202) and the
  cell maps take the limit there, whereas `firstSwitchTime` is positive at every `z⁰ ≠ 0`.

Chapter 15 will need root-based cell maps, and lemmas that they agree with `poincare` on the open
cells.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex MeasureTheory Set

/-- The sesquilinear form `RR(z₁, z₂) := Re(z̄₁ z₂)` of Chapter 10 (TeX 8456), the real inner
product of `ℂ = ℝ²`. -/
def RR (a b : ℂ) : ℝ := (starRingEnd ℂ a * b).re

/-- `RR(a, b) = Re a Re b + Im a Im b`. -/
theorem RR_eq_re_mul_add_im_mul (a b : ℂ) : RR a b = a.re * b.re + a.im * b.im := by
  simp only [RR, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- `RR` is symmetric. -/
theorem RR_comm (a b : ℂ) : RR a b = RR b a := by
  rw [RR_eq_re_mul_add_im_mul, RR_eq_re_mul_add_im_mul]; ring

/-- `RR` is additive in its first argument. -/
theorem RR_add_left (a b c : ℂ) : RR (a + b) c = RR a c + RR b c := by
  simp only [RR_eq_re_mul_add_im_mul, Complex.add_re, Complex.add_im]; ring

/-- `RR` is additive in its second argument. -/
theorem RR_add_right (a b c : ℂ) : RR a (b + c) = RR a b + RR a c := by
  simp only [RR_eq_re_mul_add_im_mul, Complex.add_re, Complex.add_im]; ring

/-- `RR` is `ℝ`-homogeneous in its first argument. -/
theorem RR_ofReal_mul_left (r : ℝ) (a c : ℂ) : RR (r * a) c = r * RR a c := by
  simp only [RR_eq_re_mul_add_im_mul, Complex.re_ofReal_mul, Complex.im_ofReal_mul]; ring

/-- `RR` is `ℝ`-homogeneous in its second argument. -/
theorem RR_ofReal_mul_right (r : ℝ) (a c : ℂ) : RR a (r * c) = r * RR a c := by
  simp only [RR_eq_re_mul_add_im_mul, Complex.re_ofReal_mul, Complex.im_ofReal_mul]; ring

/-- The derivative of `RR(f, g)` along two curves in `ℂ`. -/
theorem hasDerivAt_RR {f g : ℝ → ℂ} {f' g' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s ↦ RR (f s) (g s)) (RR f' (g t) + RR (f t) g') t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hf.star.fun_mul hg)
  have e : (fun s ↦ RR (f s) (g s)) = Complex.reCLM ∘ fun x ↦ star (f x) * g x := by
    funext s; simp [RR]
  rw [e]
  convert h using 1
  simp [RR]

namespace TriFuller

/-- The primitive cube root of unity `ζ = exp(2πi/3)` (TeX 10692). -/
noncomputable def ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- The vertices of the triangular control set, `V_T = {1, ζ, ζ²}` (TeX 10690). -/
noncomputable def VT : Set ℂ := {1, ζ, ζ ^ 2}

/-- The triangular control set `U_T`, the convex hull of `V_T` (TeX 11100). -/
noncomputable def UT : Set ℂ := convexHull ℝ VT

/-- The solution `z(t, z⁰, u)` of the Fuller system with initial value `z⁰` at `t = 0` and constant
control `u ∈ ℂ` (equation `eqn:z1z2z3`, (13.2.2), TeX 10698–10705):
`z₁(t) = -itu + z₁⁰`, `z₂(t) = -it²u/2! + z₁⁰t + z₂⁰`, `z₃(t) = -it³u/3! + z₁⁰t²/2! + z₂⁰t + z₃⁰`.
It is defined for every real `t`, negative times included. -/
noncomputable def flow (t : ℝ) (z : Fin 3 → ℂ) (u : ℂ) : Fin 3 → ℂ :=
  ![z 0 - I * t * u, z 1 + z 0 * t - I * t ^ 2 * u / 2,
    z 2 + z 1 * t + z 0 * t ^ 2 / 2 - I * t ^ 3 * u / 6]

/-- The Hamiltonian of the Fuller system, `H_F(z, u) = RR(z₁, z₂ i) + RR(u, z₃)` (the first form
of (13.2.3)–(13.2.4), TeX 10718–10721; the second form is `ham_eq_half_sum`). -/
noncomputable def ham (z : Fin 3 → ℂ) (u : ℂ) : ℝ := RR (z 0) (z 1 * I) + RR u (z 2)

/-- The maximized Hamiltonian `H_F⁺(z) = max_{u ∈ V_T} H_F(z, u)` (TeX 10732–10737). -/
noncomputable def hamMax (z : Fin 3 → ℂ) : ℝ := max (ham z 1) (max (ham z ζ) (ham z (ζ ^ 2)))

/-- The controls of `U` that maximize the Hamiltonian at `z` (used with `U = U_T` in Lemma 13.3.2,
TeX 11108–11114). -/
def hamArgmax (U : Set ℂ) (z : Fin 3 → ℂ) : Set ℂ := {v ∈ U | ∀ v' ∈ U, ham z v' ≤ ham z v}

/-- A trajectory of the Fuller system for triangular control (13.2.1) (TeX 10683–10696) on
`[t₁, t₂]` with controls in `U` (`U = V_T` for the Fuller system, `U = U_T` in Lemma 13.3.2):
`t₁ < t₂`, the control `u` is measurable with values in `U` on `[t₁, t₂]`, and
`z₁' = -iu`, `z₂' = z₁`, `z₃' = z₂` in Carathéodory's sense (each coordinate is the indefinite
integral of its right-hand side on `[t₁, t₂]`). -/
def IsTrajectory (U : Set ℂ) (t₁ t₂ : ℝ) (z : ℝ → Fin 3 → ℂ) (u : ℝ → ℂ) : Prop :=
  t₁ < t₂ ∧ Measurable u ∧ (∀ t ∈ Icc t₁ t₂, u t ∈ U) ∧
    ∀ t ∈ Icc t₁ t₂, z t 0 = z t₁ 0 + ∫ s in t₁..t, -I * u s ∧
      z t 1 = z t₁ 1 + ∫ s in t₁..t, z s 0 ∧ z t 2 = z t₁ 2 + ∫ s in t₁..t, z s 1

/-- The maximum condition (equation `eqn:max`, (13.2.5), TeX 10723–10726) with control set `U`:
for almost every `t ∈ [t₁, t₂]`, `H_F(z(t), u(t)) ≥ H_F(z(t), v)` for every `v ∈ U` (the book
compares with the vertices `ζ^k`; since `H_F` is affine in the control, the condition over `U_T`
is the same, which is the form of Lemma 13.3.2). -/
def MaxCondition (U : Set ℂ) (t₁ t₂ : ℝ) (z : ℝ → Fin 3 → ℂ) (u : ℝ → ℂ) : Prop :=
  ∀ᵐ t, t ∈ Icc t₁ t₂ → ∀ v ∈ U, ham (z t) v ≤ ham (z t) (u t)

/-- A solution of the Fuller system on `[t₁, t₂]` in the sense of Lemmas 13.2.1–13.2.3
(TeX 10794–10860): a trajectory (13.2.1) with controls in `V_T` satisfying the maximum condition
(13.2.5) and `H_F(z(t), u(t)) = 0` (equation `eqn:H0`, (13.2.6)), for almost every `t`. -/
def IsExtremal (t₁ t₂ : ℝ) (z : ℝ → Fin 3 → ℂ) (u : ℝ → ℂ) : Prop :=
  IsTrajectory VT t₁ t₂ z u ∧ MaxCondition VT t₁ t₂ z u ∧
    ∀ᵐ t, t ∈ Icc t₁ t₂ → ham (z t) (u t) = 0

/-- The switching function `χ^u_{v₁-v₂}(t, z⁰) = (1/√3) RR(v₁ - v₂, z₃(t, z⁰, u))`
(TeX 10755–10765, 10862–10868), with `d = v₁ - v₂`: the switching function from `v₁` to `v₂`
propagated with the constant control `u`. The book's `χ^k_{ij} = χ^{u_k}_{u_i-u_j}` is
`switchingFunction (ζ ^ k) (ζ ^ i - ζ ^ j)`, and `χ_{ij} = χ^i_{ij}`. -/
noncomputable def switchingFunction (u d : ℂ) (t : ℝ) (z : Fin 3 → ℂ) : ℝ :=
  RR d (flow t z u 2) / √3

/-- The time reversal `τ(z₁, z₂, z₃) = (z̄₁, -z̄₂, z̄₃)` (TeX 10834–10837). -/
noncomputable def tau (z : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![starRingEnd ℂ (z 0), -starRingEnd ℂ (z 1), starRingEnd ℂ (z 2)]

/-- The virial rescaling `(z₁, z₂, z₃) ↦ (r z₁, r² z₂, r³ z₃)` of Lemma 13.2.1 (TeX 10794–10802),
on points of `ℂ³`. -/
noncomputable def scale (r : ℝ) (z : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![r * z 0, r ^ 2 * z 1, r ^ 3 * z 2]

/-- Equivalence under the virial group `𝒢` (TeX 10820–10827), generated by the rescalings of
Lemma 13.2.1 and the rotation by `ζ` of Lemma 13.2.2 (`𝒢 ≅ ℝ_{>0} × ℤ/3`): `z ≡ w` if
`w = v · (r z₁, r² z₂, r³ z₃)` for some `r > 0` and `v ∈ V_T`. -/
def VirialEquiv (z w : Fin 3 → ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ v ∈ VT, w = v • scale r z

/-- The wall `𝒲_k = ℝ_{≤0} ζ^k` (TeX 10917–10921); `𝒲₀ = ℝ_{≤0}` is the wall between the controls
`ζ` and `ζ²`, and in general `𝒲_k` is the wall between the two controls other than `ζ^k`. -/
noncomputable def wall (k : ℕ) : Set ℂ := {w | ∃ s : ℝ, s ≤ 0 ∧ w = s * ζ ^ k}

/-- The set of walls `𝒲 = 𝒲₀ ∪ 𝒲₁ ∪ 𝒲₂` (TeX 10919–10921). -/
noncomputable def walls : Set ℂ := wall 0 ∪ wall 1 ∪ wall 2

/-- The control vector `v(z⁰, u) = (RR(z₃⁰, u), RR(z₂⁰, u), RR(z₁⁰, u))` (TeX 10934–10940; note
the backwards indexing). -/
def controlVector (z : Fin 3 → ℂ) (u : ℂ) : Fin 3 → ℝ := ![RR (z 2) u, RR (z 1) u, RR (z 0) u]

/-- `0 ≺ v` in the lexicographic order (TeX 10946–10950): the first nonzero entry of `v` is
positive. -/
def LexPos (v : Fin 3 → ℝ) : Prop := ∃ k : Fin 3, (∀ j < k, v j = 0) ∧ 0 < v k

/-- The lexicographic order `v ≺ w :⇔ 0 ≺ w - v` (TeX 10946–10950). -/
def LexLt (v w : Fin 3 → ℝ) : Prop := LexPos (w - v)

/-- `V_{T,max}`: the controls `u ∈ V_T` whose control vector `v(z⁰, u)` is maximal in the
lexicographic order (Lemma 13.2.6, TeX 10957–10963). -/
noncomputable def lexMaxControls (z : Fin 3 → ℂ) : Set ℂ :=
  {u ∈ VT | ∀ v ∈ VT, ¬ LexLt (controlVector z u) (controlVector z v)}

/-- `u` is the **first control** of `z⁰` (TeX 10747–10753): `u ∈ V_T` is the optimal control
starting at `t = 0`, that is, the constant control `u` satisfies the maximum condition (13.2.5)
along its own trajectory `t ↦ z(t, z⁰, u)` on some interval `[0, ε]`, `ε > 0`. -/
def IsFirstControl (z : Fin 3 → ℂ) (u : ℂ) : Prop :=
  u ∈ VT ∧ ∃ ε > 0, ∀ t ∈ Icc 0 ε, ∀ v ∈ VT, ham (flow t z u) v ≤ ham (flow t z u) u

/-- The first control of `z⁰` (`IsFirstControl`); the junk value `1` if there is none (which
happens only for `z⁰ = 0`, the singular locus). -/
noncomputable def firstControl (z : Fin 3 → ℂ) : ℂ :=
  open Classical in if h : ∃ u, IsFirstControl z u then h.choose else 1

/-- The first positive switching time `t_sw` of `z⁰` (TeX 10747–10753): the infimum of the times
`t > 0` at which the first control `u` is no longer maximizing along `t ↦ z(t, z⁰, u)`. The
control `u` is optimal on `[0, t_sw]` and is beaten at times arbitrarily close to `t_sw` from the
right, where the trajectory switches. -/
noncomputable def firstSwitchTime (z : Fin 3 → ℂ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∃ v ∈ VT,
    ham (flow t z (firstControl z)) (firstControl z) < ham (flow t z (firstControl z)) v}

/-- `u` is the **most recent control** of `z⁰` (TeX 10880–10883): `u ∈ V_T` is the optimal control
for small negative times until the switching time `t = 0`, that is, the constant control `u`
satisfies the maximum condition along `t ↦ z(t, z⁰, u)` on some `[-ε, 0]`, `ε > 0`. -/
def IsMostRecentControl (z : Fin 3 → ℂ) (u : ℂ) : Prop :=
  u ∈ VT ∧ ∃ ε > 0, ∀ t ∈ Icc (-ε) 0, ∀ v ∈ VT, ham (flow t z u) v ≤ ham (flow t z u) u

/-- The most recent control of `z⁰` (`IsMostRecentControl`); the junk value `1` if there is none. -/
noncomputable def mostRecentControl (z : Fin 3 → ℂ) : ℂ :=
  open Classical in if h : ∃ u, IsMostRecentControl z u then h.choose else 1

/-- The most recent switching time of `z⁰` (TeX 10895–10897): the supremum of the times `t < 0`
at which the most recent control `u` is not maximizing along `t ↦ z(t, z⁰, u)`. -/
noncomputable def mostRecentSwitchTime (z : Fin 3 → ℂ) : ℝ :=
  sSup {t : ℝ | t < 0 ∧ ∃ v ∈ VT,
    ham (flow t z (mostRecentControl z)) (mostRecentControl z) <
      ham (flow t z (mostRecentControl z)) v}

/-! ### Basic facts -/

/-- `ζ = -1/2 + (√3/2) i`. -/
theorem ζ_eq_mk : ζ = ⟨-1 / 2, √3 / 2⟩ := by
  have h : (2 * Real.pi * Complex.I / 3 : ℂ) = ((2 * Real.pi / 3 : ℝ) : ℂ) * I := by
    push_cast; ring
  have e : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  have hc : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [e, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  have hs : Real.sin (2 * Real.pi / 3) = √3 / 2 := by
    rw [e, Real.sin_pi_sub, Real.sin_pi_div_three]
  apply Complex.ext
  · rw [ζ, h, Complex.exp_ofReal_mul_I_re, hc]
  · rw [ζ, h, Complex.exp_ofReal_mul_I_im, hs]

/-- `ζ³ = 1`. -/
theorem ζ_pow_three : ζ ^ 3 = 1 := by
  rw [ζ, ← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 2
  push_cast; ring

private lemma l4b_sqrt3_mul : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

theorem ζ_re : ζ.re = -1 / 2 := by rw [ζ_eq_mk]

theorem ζ_im : ζ.im = √3 / 2 := by rw [ζ_eq_mk]

theorem ζ_sq_re : (ζ ^ 2).re = -1 / 2 := by
  rw [pow_two, Complex.mul_re, ζ_re, ζ_im]; nlinarith [l4b_sqrt3_mul]

theorem ζ_sq_im : (ζ ^ 2).im = -(√3 / 2) := by
  rw [pow_two, Complex.mul_im, ζ_re, ζ_im]; ring

/-- `ζ² = -1/2 - (√3/2) i`. -/
theorem ζ_sq_eq_mk : ζ ^ 2 = ⟨-1 / 2, -(√3 / 2)⟩ := Complex.ext ζ_sq_re ζ_sq_im

theorem norm_ζ : ‖ζ‖ = 1 := by
  rw [ζ, show (2 * Real.pi * Complex.I / 3 : ℂ) = ((2 * Real.pi / 3 : ℝ) : ℂ) * I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `ζ̄ = ζ²`. -/
theorem conj_ζ : starRingEnd ℂ ζ = ζ ^ 2 := by
  rw [ζ_sq_eq_mk, ζ_eq_mk]
  apply Complex.ext <;> simp

/-- `conj ζ² = ζ`. -/
theorem conj_ζ_sq : starRingEnd ℂ (ζ ^ 2) = ζ := by
  rw [ζ_sq_eq_mk, ζ_eq_mk]
  apply Complex.ext <;> simp

theorem ζ_ne_one : ζ ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [ζ_re, Complex.one_re] at this
  norm_num at this

theorem mem_VT {v : ℂ} : v ∈ VT ↔ v = 1 ∨ v = ζ ∨ v = ζ ^ 2 := by
  simp only [VT, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem one_mem_VT : (1 : ℂ) ∈ VT := mem_VT.2 (Or.inl rfl)

theorem ζ_mem_VT : ζ ∈ VT := mem_VT.2 (Or.inr (Or.inl rfl))

theorem ζ_sq_mem_VT : ζ ^ 2 ∈ VT := mem_VT.2 (Or.inr (Or.inr rfl))

theorem finite_VT : VT.Finite := ((Set.finite_singleton _).insert _).insert _

theorem VT_subset_UT : VT ⊆ UT := subset_convexHull ℝ VT

/-- The vertices of `U_T` lie on the unit circle, and `V_T` is closed under products and
conjugation. -/
private lemma l4n_VT_props {u v : ℂ} (hu : u ∈ VT) (hv : v ∈ VT) :
    ‖u‖ = 1 ∧ u * v ∈ VT ∧ starRingEnd ℂ u ∈ VT ∧ u⁻¹ = starRingEnd ℂ u := by
  have hn : ∀ w ∈ VT, ‖w‖ = 1 := by
    intro w hw
    rcases hw with rfl | rfl | rfl
    · simp
    · exact norm_ζ
    · simp [norm_ζ]
  have hpow : ∀ n : ℕ, ζ ^ n ∈ VT := by
    intro n
    rw [← Nat.mod_add_div n 3, pow_add, pow_mul, ζ_pow_three, one_pow, mul_one]
    have : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases n % 3 <;> simp [VT]
  have hex : ∀ w ∈ VT, ∃ n : ℕ, w = ζ ^ n := by
    intro w hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, rfl⟩
  obtain ⟨a, rfl⟩ := hex u hu
  obtain ⟨b, rfl⟩ := hex v hv
  refine ⟨hn _ hu, ?_, ?_, ?_⟩
  · rw [← pow_add]; exact hpow _
  · rw [map_pow, conj_ζ, ← pow_mul]; exact hpow _
  · rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn _ hu]
    simp

/-- The vertices of `U_T` lie on the unit circle. -/
theorem norm_eq_one_of_mem_VT {u : ℂ} (hu : u ∈ VT) : ‖u‖ = 1 := (l4n_VT_props hu hu).1

/-- `V_T` is closed under products. -/
theorem mul_mem_VT {u v : ℂ} (hu : u ∈ VT) (hv : v ∈ VT) : u * v ∈ VT := (l4n_VT_props hu hv).2.1

/-- `V_T` is closed under conjugation. -/
theorem conj_mem_VT {u : ℂ} (hu : u ∈ VT) : starRingEnd ℂ u ∈ VT := (l4n_VT_props hu hu).2.2.1

/-- `u⁻¹ = ū` on `V_T`. -/
theorem inv_eq_conj_of_mem_VT {u : ℂ} (hu : u ∈ VT) : u⁻¹ = starRingEnd ℂ u :=
  (l4n_VT_props hu hu).2.2.2

/-- A point of the walls with negative real part lies on `𝒲₀ = ℝ_{≤0}`: it is real. -/
theorem im_eq_zero_of_mem_walls {w : ℂ} (hw : w ∈ walls) (hre : w.re < 0) : w.im = 0 := by
  rcases hw with (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩
  · simp
  · rw [pow_one, Complex.re_ofReal_mul, ζ_re] at hre
    linarith
  · rw [Complex.re_ofReal_mul, ζ_sq_re] at hre
    linarith

/-- `H_F(z, v) ≤ H_F⁺(z)` for `v ∈ V_T`. -/
theorem ham_le_hamMax (w : Fin 3 → ℂ) {v : ℂ} (hv : v ∈ VT) : ham w v ≤ hamMax w := by
  rcases hv with rfl | rfl | rfl
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- The maximized Hamiltonian is the Hamiltonian at a maximizing control of `V_T`. -/
theorem hamMax_eq_of_forall_le {w : Fin 3 → ℂ} {v : ℂ} (hv : v ∈ VT)
    (h : ∀ x ∈ VT, ham w x ≤ ham w v) : hamMax w = ham w v :=
  le_antisymm (max_le (h 1 one_mem_VT) (max_le (h ζ ζ_mem_VT) (h _ ζ_sq_mem_VT)))
    (ham_le_hamMax w hv)

theorem scale_one (z : Fin 3 → ℂ) : scale 1 z = z := by
  funext i; fin_cases i <;> simp [scale]

theorem scale_scale (a b : ℝ) (z : Fin 3 → ℂ) : scale a (scale b z) = scale (a * b) z := by
  funext i; fin_cases i <;> simp [scale] <;> ring

theorem scale_smul (a : ℝ) (v : ℂ) (z : Fin 3 → ℂ) : scale a (v • z) = v • scale a z := by
  funext i; fin_cases i <;> simp [scale] <;> ring

/-- The two forms of the Fuller Hamiltonian (13.2.3)–(13.2.4) (TeX 10718–10721):
`H_F(z, u) = ½ Σ_{j=0}^{3} (-1)^j RR(z_{3-j}, i z_j)` with `z₀ = -iu`. -/
theorem ham_eq_half_sum (z : Fin 3 → ℂ) (u : ℂ) :
    ham z u = (1 / 2) * ∑ j : Fin 4, (-1) ^ (j : ℕ) *
      RR (![-I * u, z 0, z 1, z 2] (Fin.rev j)) (I * ![-I * u, z 0, z 1, z 2] j) := by
  simp only [ham, RR, Fin.sum_univ_four]
  simp [Fin.rev, Complex.mul_re, Complex.mul_im]
  ring

/-- `z(0, z⁰, u) = z⁰`. -/
theorem flow_zero (z : Fin 3 → ℂ) (u : ℂ) : flow 0 z u = z := by
  funext j
  fin_cases j <;> simp [flow]

/-- The flow property `z(s + t, z⁰, u) = z(t, z(s, z⁰, u), u)`. -/
theorem flow_add (s t : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    flow (s + t) z u = flow t (flow s z u) u := by
  funext j
  fin_cases j <;> simp [flow] <;> ring

/-- A complex cubic in a real variable has the expected derivative. -/
private lemma l4b_hasDerivAt_cubic (a b c d : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ a + b * s + c * s ^ 2 + d * s ^ 3)
      (b + 2 * c * t + 3 * d * t ^ 2) t := by
  have h1 : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have := (((h1.const_mul b).const_add a).add ((h1.fun_pow 2).const_mul c)).add
    ((h1.fun_pow 3).const_mul d)
  convert this using 1
  push_cast; ring

/-- The polynomials (13.2.2) solve the Fuller system classically:
`d/dt z(t, z⁰, u) = (-iu, z₁(t), z₂(t))`. -/
theorem hasDerivAt_flow (t : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    HasDerivAt (fun s ↦ flow s z u) ![-I * u, flow t z u 0, flow t z u 1] t := by
  rw [hasDerivAt_pi]
  intro j
  fin_cases j
  · convert l4b_hasDerivAt_cubic (z 0) (-I * u) 0 0 t using 1
    · funext s; simp [flow]; ring
    · simp
  · convert l4b_hasDerivAt_cubic (z 1) (z 0) (-I * u / 2) 0 t using 1
    · funext s; simp [flow]; ring
    · simp [flow]; ring
  · convert l4b_hasDerivAt_cubic (z 2) (z 1) (z 0 / 2) (-I * u / 6) t using 1
    · funext s; simp [flow]; ring
    · simp [flow]; ring

end TriFuller

open TriFuller

/-- The derivative of `t ↦ z(t - a, w, u)`. -/
private lemma l4b_hasDerivAt_flow_sub (a s : ℝ) (w : Fin 3 → ℂ) (u : ℂ) :
    HasDerivAt (fun x ↦ flow (x - a) w u) ![-I * u, flow (s - a) w u 0, flow (s - a) w u 1] s :=
  HasDerivAt.comp_sub_const s a (hasDerivAt_flow (s - a) w u)

/-- Integrating the Fuller system along `t ↦ z(t - a, w, u)` from `a` to `b`. -/
private lemma l4b_integral_flow (a b : ℝ) (w : Fin 3 → ℂ) (u : ℂ) (j : Fin 3) :
    ∫ s in a..b, ![-I * u, flow (s - a) w u 0, flow (s - a) w u 1] j =
      flow (b - a) w u j - w j := by
  have hd : ∀ s, HasDerivAt (fun x ↦ flow (x - a) w u j)
      (![-I * u, flow (s - a) w u 0, flow (s - a) w u 1] j) s :=
    fun s ↦ hasDerivAt_pi.1 (l4b_hasDerivAt_flow_sub a s w u) j
  have hcont : Continuous fun s ↦ flow (s - a) w u :=
    continuous_iff_continuousAt.2 fun s ↦ (l4b_hasDerivAt_flow_sub a s w u).continuousAt
  have hc : Continuous fun s ↦ ![-I * u, flow (s - a) w u 0, flow (s - a) w u 1] j := by
    fin_cases j
    · exact continuous_const
    · exact (continuous_apply 0).comp hcont
    · exact (continuous_apply 1).comp hcont
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s) (hc.intervalIntegrable _ _)]
  simp [flow_zero]

/-- **Equation `eqn:z1z2z3` (13.2.2)** (TeX 10696–10705): "When `u ∈ ℂ` is constant, we can solve
the Fuller system ODEs, to obtain (13.2.2)". For a constant control `u ∈ U`, a curve is a
trajectory (13.2.1) on `[t₁, t₂]` if and only if it is `t ↦ z(t - t₁, z(t₁), u)`.

Proof: the polynomials satisfy the integral equations (`hasDerivAt_flow` and the fundamental
theorem of calculus); conversely, integrating `z₁' = -iu`, then `z₂' = z₁`, then `z₃' = z₂` from
`t₁` gives the polynomials. -/
theorem eqn_z1z2z3 {U : Set ℂ} {u : ℂ} (hu : u ∈ U) {t₁ t₂ : ℝ} (h : t₁ < t₂)
    (z : ℝ → Fin 3 → ℂ) :
    IsTrajectory U t₁ t₂ z (fun _ ↦ u) ↔ ∀ t ∈ Icc t₁ t₂, z t = flow (t - t₁) (z t₁) u := by
  have I0 : ∀ (a b : ℝ) (w : Fin 3 → ℂ), ∫ _ in a..b, -I * u = flow (b - a) w u 0 - w 0 := by
    intro a b w; simpa using l4b_integral_flow a b w u 0
  have I1 : ∀ (a b : ℝ) (w : Fin 3 → ℂ),
      ∫ s in a..b, flow (s - a) w u 0 = flow (b - a) w u 1 - w 1 := by
    intro a b w; simpa using l4b_integral_flow a b w u 1
  have I2 : ∀ (a b : ℝ) (w : Fin 3 → ℂ),
      ∫ s in a..b, flow (s - a) w u 1 = flow (b - a) w u 2 - w 2 := by
    intro a b w; simpa using l4b_integral_flow a b w u 2
  have sub : ∀ t ∈ Icc t₁ t₂, uIcc t₁ t ⊆ Icc t₁ t₂ := fun t ht ↦ by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2
  constructor
  · rintro ⟨-, -, -, hint⟩
    have h0 : ∀ t ∈ Icc t₁ t₂, z t 0 = flow (t - t₁) (z t₁) u 0 := by
      intro t ht; rw [(hint t ht).1, I0 t₁ t (z t₁)]; ring
    have h1 : ∀ t ∈ Icc t₁ t₂, z t 1 = flow (t - t₁) (z t₁) u 1 := by
      intro t ht
      rw [(hint t ht).2.1, intervalIntegral.integral_congr (fun s hs ↦ h0 s (sub t ht hs)), I1]
      ring
    have h2 : ∀ t ∈ Icc t₁ t₂, z t 2 = flow (t - t₁) (z t₁) u 2 := by
      intro t ht
      rw [(hint t ht).2.2, intervalIntegral.integral_congr (fun s hs ↦ h1 s (sub t ht hs)), I2]
      ring
    intro t ht
    funext j
    fin_cases j
    · exact h0 t ht
    · exact h1 t ht
    · exact h2 t ht
  · intro hz
    refine ⟨h, measurable_const, fun _ _ ↦ hu, fun t ht ↦ ⟨?_, ?_, ?_⟩⟩
    · rw [I0 t₁ t (z t₁), hz t ht]; ring
    · rw [intervalIntegral.integral_congr (fun s hs ↦ congrFun (hz s (sub t ht hs)) 0), I1,
        hz t ht]
      ring
    · rw [intervalIntegral.integral_congr (fun s hs ↦ congrFun (hz s (sub t ht hs)) 1), I2,
        hz t ht]
      ring

namespace TriFuller

/-- "`H_F` is constant along every segment with constant control" (TeX 10740–10741):
`H_F(z(t, z⁰, u), u) = H_F(z⁰, u)` for every `u ∈ ℂ`. Proof:
`d/dt H_F = RR(-iu, i z₂) + RR(z₁, i z₁) + RR(u, z₂) = 0`. -/
theorem ham_flow (t : ℝ) (z : Fin 3 → ℂ) (u : ℂ) : ham (flow t z u) u = ham z u := by
  -- `d/dt H_F(z(t), u) = RR(-iu, i z₂) + RR(z₁, i z₁) + RR(u, z₂) = 0`
  have hd : ∀ s, HasDerivAt (fun s ↦ ham (flow s z u) u) 0 s := by
    intro s
    have hF := hasDerivAt_pi.1 (hasDerivAt_flow s z u)
    have h := (hasDerivAt_RR (hF 0) ((hF 1).mul_const I)).fun_add
      (hasDerivAt_RR (hasDerivAt_const s u) (hF 2))
    change HasDerivAt (fun s ↦ RR (flow s z u 0) (flow s z u 1 * I) + RR u (flow s z u 2)) 0 s
    convert h using 1
    simp [RR, Complex.mul_re, Complex.mul_im]
    ring
  have := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt) (fun s ↦ (hd s).deriv) t 0
  simpa [flow_zero] using this

end TriFuller

end SmoothedPolygons
