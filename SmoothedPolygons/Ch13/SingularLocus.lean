module

public import SmoothedPolygons.Ch13.FirstControl
public import Mathlib.Analysis.Convex.Extreme

/-!
# Chapter 13: the singular locus of the Fuller system

§13.3 of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX 11070–11157). The singular locus is
the origin of `ℂ³` (TeX 11072).

* Lemma 13.3.1 (`lem:nonzero`): a trajectory with constant control starting on a wall, away from
  `0`, never reaches `0`;
* equations (13.3.1) (`eqn:u3`) and (13.3.2) (`eqn:z3u3`): the triple integral `u₃` of the
  control and the formula `z₃ = -iu₃ + z₁⁰t²/2 + z₂⁰t + z₃⁰`;
* Lemma 13.3.2 (`lemma:no-singular`): the only singular arc is `z ≡ 0`, `u = 0` almost everywhere.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex MeasureTheory Set TriFuller

/-- **Lemma 13.3.1** (`lem:nonzero`, TeX 11078–11098). Let `z⁰ ∈ ℂ³ ∖ 0` with `z₃⁰ ∈ 𝒲`, and let
`z` be the trajectory with initial condition `z(0) = z⁰` and the constant control given by the
maximum principle (the first control). Then `z(t) ≠ 0` for all `t`.

Proof (the book's): up to equivalence (Lemma 13.2.2) the control is `u = 1`. If `z(t₀) = 0`,
solving the linear equations (13.2.2) gives `z_j⁰ = (-1)^{j+1} i t₀^j / j!`; `z⁰ ≠ 0` forces
`t₀ ≠ 0`, and then `z₃⁰ = i t₀³/6 ∉ 𝒲`, a contradiction. The argument covers every `t₀ ∈ ℝ`, and
it does not use that the control is the first control (any constant control in `V_T` will do;
inventory, gap 6). -/
theorem lemma13_3_1 {z : Fin 3 → ℂ} (hz : z ≠ 0) (h₃ : z 2 ∈ walls) (t : ℝ) :
    flow t z (firstControl z) ≠ 0 := by
  sorry

namespace TriFuller

/-- The triple integral `u₃(t) = ½ ∫_{t₁}^{t} u(s) (t - s)² ds` of a control (equation `eqn:u3`,
(13.3.1), TeX 11118–11126, written there with `t₁ = 0`). -/
noncomputable def u3 (t₁ : ℝ) (u : ℝ → ℂ) (t : ℝ) : ℂ :=
  (1 / 2) * ∫ s in t₁..t, u s * ((t - s : ℝ) : ℂ) ^ 2

/-- The triangle `U_T` lies in the closed unit disk. -/
theorem l4st_norm_le_one_of_mem_UT {v : ℂ} (hv : v ∈ UT) : ‖v‖ ≤ 1 := by
  sorry

end TriFuller

/-- **Equation `eqn:u3` (13.3.1)** (TeX 11118–11129). For a measurable control `u` with `|u| ≤ 1`
on `[t₁, t₂]`, `u₃(t) = ½ ∫_{t₁}^{t} u(s)(t - s)² ds` solves the initial value problem `u₃''' = u`,
`u₃(t₁) = u₃'(t₁) = u₃''(t₁) = 0` (the book writes `u(0) = u'(0) = u''(0) = 0` for the initial
conditions of `u₃`): in Carathéodory's sense, it is the threefold iterated integral of `u` from
`t₁` (Cauchy's formula for repeated integration). It satisfies `|u₃(t)| ≤ ½∫_{t₁}^{t} (t - s)² ds
= (t - t₁)³/6` (the book's `O(t³)`). -/
theorem eqn_u3 {t₁ t₂ : ℝ} {u : ℝ → ℂ} (hu : Measurable u) (hb : ∀ t ∈ Icc t₁ t₂, ‖u t‖ ≤ 1) :
    ∀ t ∈ Icc t₁ t₂, u3 t₁ u t = (∫ s in t₁..t, ∫ σ in t₁..s, ∫ ρ in t₁..σ, u ρ) ∧
      ‖u3 t₁ u t‖ ≤ (t - t₁) ^ 3 / 6 := by
  sorry

/-- **Equation `eqn:z3u3` (13.3.2)** (TeX 11131–11134). Along a trajectory of the Fuller system
with controls in `U_T`, `z₃(t) = -i u₃(t) + z₁⁰ (t - t₁)²/2! + z₂⁰ (t - t₁) + z₃⁰` (the book takes
`t₁ = 0`). Proof: integrate the Fuller system three times (`eqn_u3`). -/
theorem eqn_z3u3 {U : Set ℂ} (hU : U ⊆ UT) {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ}
    (h : IsTrajectory U t₁ t₂ z u) :
    ∀ t ∈ Icc t₁ t₂, z t 2 = -I * u3 t₁ u t + z t₁ 0 * ((t - t₁ : ℝ) : ℂ) ^ 2 / 2 +
      z t₁ 1 * ((t - t₁ : ℝ) : ℂ) + z t₁ 2 := by
  sorry

/-- **Lemma 13.3.2** (`lemma:no-singular`, TeX 11108–11156). Let `(z₁, z₂, z₃, u)` be a controlled
Fuller trajectory on `[t₁, t₂]`, with `z_j` absolutely continuous and `u : [t₁, t₂] → U_T`
measurable, satisfying the maximum principle for the Hamiltonian `H_F`. Suppose that the
trajectory is singular in the sense that for all `t ∈ [t₁, t₂]` the set of controls maximizing the
Hamiltonian is a face of `U_T` and not a vertex. Then `(z₁, z₂, z₃)` is identically zero and the
control is zero almost everywhere. (The book's "`z_j : [t₁, t₂] → ℂ³`" means `ℂ`.)

Proof (the book's, with its gap repaired along its lines). Write `z₃` by (13.3.2) with the bound
`|u₃(t)| ≤ (t - t₁)³/6` of (13.3.1). The set of maximizers of `v ↦ H_F(z(t), v) = RR(z₁, z₂ i) +
RR(v, z₃(t))` on `U_T` is all of `U_T` if `z₃(t) = 0`, an edge if `z₃(t)` lies on an open ray of
`𝒲`, and a vertex otherwise; so the hypothesis says `z₃(t) ∈ 𝒲` for every `t`.
1. (Book's second case, on a subinterval.) The book assumes that the maximizing edge is the same
   on the whole interval (TeX 11145–11147; inventory, gap 7). Repair: if `z₃(t₀) ≠ 0` for some
   `t₀`, then `z₃ ≠ 0` on an interval `[a, b] ∋ t₀` of positive length, and since `z₃` is
   continuous and `𝒲 ∖ 0` is the disjoint union of three open rays, `z₃` stays on one ray there,
   say `ℝ_{<0}` (rotation, Lemma 13.2.2): the maximizing face is the edge `[ζ, ζ²]` on `[a, b]`.
   Apply the book's argument on `[a, b]`: `u(t) ∈ [ζ, ζ²]` a.e., so `Re u = -½`,
   `Re u₃(t) = -(t - a)³/12` (from `a`), and `0 = RR(z₃(t), ζ - ζ²) = (√3/2)(t - a)³/3! +
   (quadratic in t)` on `[a, b]`, which is absurd. Hence `z₃ ≡ 0` on `[t₁, t₂]`.
2. (Book's first case.) `z₃ ≡ 0` and `|u₃| ≤ (t - t₁)³/6` give `z₁⁰ = z₂⁰ = z₃⁰ = 0`, then
   `u₃ ≡ 0`, so `z ≡ 0` (`z₂ = z₃'`, `z₁ = z₂'`) and `u = u₃''' = 0` almost everywhere. -/
theorem lemma13_3_2 {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsTrajectory UT t₁ t₂ z u)
    (hmax : MaxCondition UT t₁ t₂ z u)
    (hsing : ∀ t ∈ Icc t₁ t₂,
      IsExtreme ℝ UT (hamArgmax UT (z t)) ∧ (hamArgmax UT (z t)).Nontrivial) :
    (∀ t ∈ Icc t₁ t₂, z t = 0) ∧ ∀ᵐ t, t ∈ Icc t₁ t₂ → u t = 0 := by
  sorry

end SmoothedPolygons
