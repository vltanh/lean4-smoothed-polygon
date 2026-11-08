module

public import SmoothedPolygons.Ch13.Defs

/-!
# Chapter 13: symmetries of the Fuller system and the switching functions

§13.2 of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX 10745–10906):

* the polar form of the switching functions (TeX 10755–10784): the angles `θ_{ij}` with
  `u_i - u_j = √3 e^{iθ_{ij}}` (`l4st_sub_eq_sqrt_three_mul_exp`) and
  `χ^k_{ij}(t) = Σ_{m=0}^{3} (t^m/m!) r_{3-m} cos(θ_{3-m} - θ_{ij})`
  (`l4st_switchingFunction_polar`);
* Lemma 13.2.1 (`lem:rescale`): the virial rescaling of solutions;
* Lemma 13.2.2 (`lem:discrete`): the rotation by `ζ`;
* Lemma 13.2.3 (`lem:reversal`): the time reversal `τ`;
* Lemma 13.2.4 (`lem:switch-reversal`): the switching functions under time reversal;
* equation (13.2.7): the switching functions under the rotation by `ζ`;
* the identity `τ(z(-t, z⁰, u)) = z(t, τ(z⁰), ū)`, the first assertion of Lemma 13.2.5
  (`l4st_tau_flow_neg`; Lemma 13.2.5 itself is in `SmoothedPolygons/Ch13/FirstControl.lean`).

The book proves all of them "by direct substitution". For Lemmas 13.2.1–13.2.3, whose solutions
have measurable controls, the substitution is a change of variables `s = t/r` or `s = -t` in the
integral equations of `IsTrajectory`, and the image of a null set is null.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex MeasureTheory Set TriFuller

namespace TriFuller

/-- The angles `θ_{ij}` of TeX 10771–10778: `u_i - u_j = √3 e^{iθ_{ij}}` with
`θ_{i,i+1} = -π/6 + 2πi/3`, `θ_{i+1,i} = 5π/6 + 2πi/3` and `θ_{i,i-1} = π/6 + 2πi/3`, for the
controls `u_i = ζ^i` (`u_{i-1} = ζ^{i+2}`). -/
theorem l4st_sub_eq_sqrt_three_mul_exp (i : ℕ) :
    ζ ^ i - ζ ^ (i + 1) = √3 * Complex.exp ((-(Real.pi / 6) + 2 * Real.pi * i / 3) * I) ∧
      ζ ^ (i + 1) - ζ ^ i = √3 * Complex.exp ((5 * Real.pi / 6 + 2 * Real.pi * i / 3) * I) ∧
      ζ ^ i - ζ ^ (i + 2) = √3 * Complex.exp ((Real.pi / 6 + 2 * Real.pi * i / 3) * I) := by
  sorry

/-- The polar form of the switching functions (TeX 10755–10784). Write the initial condition in
polar coordinates `z_j⁰ = r_j e^{iθ_j}` (`j = 1, 2, 3`), put `r₀ = 1` and `θ₀ = 2πk/3 - π/2`, so
that `z₀⁰ = -iu = r₀ e^{iθ₀}` for the control `u = ζ^k`, and let `d = √3 e^{iα}` (for instance
`d = u_i - u_j`, `α = θ_{ij}`). Then `χ^u_d(t) = RR(e^{iα}, z₃(t, z⁰, u))` and
`χ^u_d(t) = Σ_{m=0}^{3} (t^m/m!) r_{3-m} cos(θ_{3-m} - α)`. Here `r` and `θ` are indexed by
`Fin 4`, with `r 0 = 1` and `θ 0 = 2πk/3 - π/2`. -/
theorem l4st_switchingFunction_polar (k : ℕ) (α : ℝ) (r θ : Fin 4 → ℝ) (hr₀ : r 0 = 1)
    (hθ₀ : θ 0 = 2 * Real.pi * k / 3 - Real.pi / 2) (z : Fin 3 → ℂ)
    (hz : ∀ j : Fin 3, z j = r j.succ * Complex.exp (θ j.succ * I)) (t : ℝ) :
    switchingFunction (ζ ^ k) (√3 * Complex.exp (α * I)) t z =
        RR (Complex.exp (α * I)) (flow t z (ζ ^ k) 2) ∧
      switchingFunction (ζ ^ k) (√3 * Complex.exp (α * I)) t z =
        ∑ m : Fin 4, t ^ (m : ℕ) / (m : ℕ).factorial * r (Fin.rev m) *
          Real.cos (θ (Fin.rev m) - α) := by
  sorry

/-- `τ(z(-t, z⁰, u)) = z(t, τ(z⁰), ū)` for all `t`, `z⁰` and `u ∈ ℂ` (the first assertion of
Lemma 13.2.5, TeX 10893–10895; a polynomial identity, by direct substitution in (13.2.2)). -/
theorem l4st_tau_flow_neg (t : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    tau (flow (-t) z u) = flow t (tau z) (starRingEnd ℂ u) := by
  sorry

/-- `τ` is an involution. -/
theorem l4st_tau_tau (z : Fin 3 → ℂ) : tau (tau z) = z := by
  sorry

/-- The Hamiltonian under time reversal: `H_F(τ z, v) = H_F(z, v̄)` (from
`RR(z̄₁, -i z̄₂) = RR(z₁, i z₂)`, TeX 10846–10860). -/
theorem l4st_ham_tau (z : Fin 3 → ℂ) (v : ℂ) : ham (tau z) v = ham z (starRingEnd ℂ v) := by
  sorry

/-- The Hamiltonian under the virial group: `H_F(v·(r z₁, r² z₂, r³ z₃), v u) = r³ H_F(z, u)` for
`|v| = 1`. -/
theorem l4st_ham_smul_scale {v : ℂ} (hv : ‖v‖ = 1) (r : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    ham (v • scale r z) (v * u) = r ^ 3 * ham z u := by
  sorry

end TriFuller

/-- **Lemma 13.2.1** (`lem:rescale`, TeX 10794–10802). If `(z₁, z₂, z₃, u)` is a solution of the
Fuller system on `[t₁, t₂]` satisfying (13.2.5) and (13.2.6), then so is
`(z̃₁, z̃₂, z̃₃, ũ)` on `[r t₁, r t₂]`, where `z̃_j(t) = r^j z_j(t/r)`, `ũ(t) = u(t/r)` and `r > 0`.

Proof (book: "direct substitution into the Fuller system and into the Hamiltonian"): the change
of variables `s = σ/r` in the integral equations gives `z̃₁' = -iũ`, `z̃₂' = z̃₁`, `z̃₃' = z̃₂`
(`r^j · (1/r) · z_{j-1}(t/r) = z̃_{j-1}(t)`); `H_F(z̃(t), v) = r³ H_F(z(t/r), v)` for every `v`
(`l4st_ham_smul_scale` with `v = 1`), and `r³ > 0`, so (13.2.5) and (13.2.6) are preserved; the
exceptional null set is dilated by `r`. -/
theorem lemma13_2_1 {t₁ t₂ r : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsExtremal t₁ t₂ z u)
    (hr : 0 < r) :
    IsExtremal (r * t₁) (r * t₂) (fun t ↦ scale r (z (t / r))) (fun t ↦ u (t / r)) := by
  sorry

/-- **Lemma 13.2.2** (`lem:discrete`, TeX 10809–10818). If `(z₁, z₂, z₃, u)` is a solution of the
Fuller system satisfying (13.2.5) and (13.2.6) with initial value `z⁰`, then
`(ζz₁, ζz₂, ζz₃, ζu)` is a solution satisfying the same constraints, with initial value `ζz⁰`
(the initial value of `t ↦ ζ • z t` at `t₁` is `ζ • z t₁` by definition).

Proof (book: "direct substitution"): the integral equations are `ℂ`-linear; `ζ V_T = V_T`; and
`H_F(ζ z, ζ v) = H_F(z, v)` because `|ζ| = 1` (`l4st_ham_smul_scale` with `r = 1`). -/
theorem lemma13_2_2 {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsExtremal t₁ t₂ z u) :
    IsExtremal t₁ t₂ (fun t ↦ ζ • z t) (fun t ↦ ζ * u t) := by
  sorry

/-- **Lemma 13.2.3** (`lem:reversal`, TeX 10844–10856). If `(z₁, z₂, z₃, u)` is a solution of the
Fuller system on `[t₁, t₂]` satisfying (13.2.5) and (13.2.6), then
`(z̄₁(-t), -z̄₂(-t), z̄₃(-t), ū(-t))`, that is `t ↦ τ(z(-t))` with control `t ↦ ū(-t)`, is a
solution on `[-t₂, -t₁]` satisfying the same constraints, with terminal value `τ(z⁰)` (its value
at `-t₁` is `τ(z(t₁))` by definition).

Proof (book: "direct substitution"): the change of variables `s ↦ -s` in the integral equations,
written between the endpoints `t₂` and `-t`; `conj V_T = V_T`; and
`H_F(τ w, v̄) = H_F(w, v)` (`l4st_ham_tau`). -/
theorem lemma13_2_3 {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsExtremal t₁ t₂ z u) :
    IsExtremal (-t₂) (-t₁) (fun t ↦ tau (z (-t))) (fun t ↦ starRingEnd ℂ (u (-t))) := by
  sorry

/-- **Lemma 13.2.4** (`lem:switch-reversal`, TeX 10862–10871). Let `t₀ ∈ ℝ`, `z⁰ ∈ ℂ³` and
`u ∈ ℂ`, and let `z* = z(t₀, z⁰, u)` be the value at `t₀` of the solution with constant control
`u`. For all `v₁, v₂ ∈ ℂ`,
`χ^u_{v₁-v₂}(t₀ - t, z⁰) = χ^{ū}_{v̄₁-v̄₂}(t, τ(z*))`.

Proof (book: "direct substitution"; an identity of cubic polynomials in `t`): by the flow property
(`l4st_flow_add`) and `l4st_tau_flow_neg`, `z₃(t, τ(z*), ū) = conj z₃(t₀ - t, z⁰, u)`, and
`RR(d̄, w̄) = RR(d, w)`. -/
theorem lemma13_2_4 (t₀ : ℝ) (z : Fin 3 → ℂ) (u v₁ v₂ : ℂ) (t : ℝ) :
    switchingFunction u (v₁ - v₂) (t₀ - t) z =
      switchingFunction (starRingEnd ℂ u) (starRingEnd ℂ v₁ - starRingEnd ℂ v₂) t
        (tau (flow t₀ z u)) := by
  sorry

/-- **Equation (13.2.7)** (TeX 10874–10877): invariance of the switching functions under the
rotation by `ζ`, `χ^{ζu}_{ζ(v₁-v₂)}(t, ζz⁰) = χ^u_{v₁-v₂}(t, z⁰)` (here with `d = v₁ - v₂`).
Proof: `z₃(t, ζz⁰, ζu) = ζ z₃(t, z⁰, u)` and `RR(ζa, ζb) = RR(a, b)`. -/
theorem eqn13_2_7 (u d : ℂ) (t : ℝ) (z : Fin 3 → ℂ) :
    switchingFunction (ζ * u) (ζ * d) t (ζ • z) = switchingFunction u d t z := by
  sorry

end SmoothedPolygons
