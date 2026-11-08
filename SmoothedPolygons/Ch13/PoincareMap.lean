module

public import SmoothedPolygons.Ch13.Blowup
public import SmoothedPolygons.Ch13.Extremals

/-!
# Chapter 13: the Fuller–Poincaré map

§13.5 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Dynamical System and Equilibrium
Points", TeX 11234–11290, 11429–11431):

* the Poincaré map `F(z⁰) = z(t_sw)` along the extremal from `z⁰` with the control given by the
  maximum principle, up to the first switching time (`poincare`, TeX 11236–11251). It is defined
  at every point (see `SmoothedPolygons/Ch13/Defs.lean` on robustness); on the section
  `(ℂ³ ∖ 0)_𝒲` it is well defined in the book's sense: `0 < t_sw < 10 φ(z⁰)` (Lemma 13.2.6,
  Corollary 13.2.7), `F(z⁰) ≠ 0` (Lemma 13.3.1; in fact for every `z⁰ ≠ 0`,
  `l4f_flow_firstControl_ne_zero`) and `F(z⁰)₃ ∈ 𝒲`; these uses are silent in the book
  (inventory, gap 9);
* the equivariance of `F` under `V_T` (Lemma 13.2.2, (13.2.7)) and under rescaling (Lemma 13.2.1),
  so that `F` descends to `(ℝ_{>0} × Ξ)_𝒲/V_T` and induces `F_ang` on `Ξ_𝒲` (`poincareAng`) and on
  `Ξ_𝒲/V_T` (`poincareAngQuot`) (TeX 11251–11275);
* the constancy of the Hamiltonian, so that `F` restricts to the zero set of `H_F⁺` (TeX
  11429–11431): the set `Ξ_{𝒲,0}/V_T` (`XiW0Quot`, which the book never defines formally; Remark
  13.5.1 and Lemma 13.5.5 describe it in words) and the restricted map `poincareAngZero`. On a wall
  two controls tie and give the same value of `H_F`, and the first control maximizes `H_F`, so the
  Hamiltonian at a point of the section is `H_F⁺` (`hamMax`);
* the time reversal `τ` on these spaces, with `F(τ F(z⁰)) = τ(z⁰)` when `z⁰` is a genuine switching
  point (the identity `F⁻¹ = τ F τ` of Chapter 15, from Lemmas 13.2.3 and 13.2.5).

Remark 13.5.1 (TeX 11277–11288) only fixes the notation `F` for these maps and their domains.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology

namespace TriFuller

/-- **The Poincaré map** `F` of the Fuller system (TeX 11236–11251), in Cartesian coordinates:
`F(z⁰) = z(t_sw, z⁰, u)`, the value at the first switching time `t_sw` of the solution with initial
condition `z⁰` and the constant control `u` given by the maximum principle (the first control). -/
noncomputable def poincare (z : Fin 3 → ℂ) : Fin 3 → ℂ :=
  flow (firstSwitchTime z) z (firstControl z)

/-! ### Well-definedness on the section -/

/-- `t_sw < 10 φ(z⁰)` (Corollary 13.2.7 with `r = φ(z⁰)`, since `|z_j| ≤ φ(z)^j`). -/
theorem l4st_firstSwitchTime_lt {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    firstSwitchTime z < 10 * weightedNorm z := by
  sorry

/-- `F` maps `ℂ³ ∖ 0` into `ℂ³ ∖ 0`: `l4f_flow_firstControl_ne_zero` at `t = t_sw`
(`0 < t_sw`, `l4st_firstSwitchTime_pos`). On the section `(ℂ³ ∖ 0)_𝒲` this is also Lemma 13.3.1 at
`t = t_sw`, the book's silent justification (inventory, gap 9); off the walls Lemma 13.3.1 does not
apply, and `l4st_poincare_tau_poincare` needs `τ F(z⁰) ≠ 0` for every `z⁰ ≠ 0`. -/
theorem l4st_poincare_ne_zero {z : Fin 3 → ℂ} (hz : z ≠ 0) : poincare z ≠ 0 := by
  sorry

/-- `F` lands on the walls: at `t_sw` the first control and the control that beats it right after
`t_sw` both maximize `RR(z₃(t_sw), ·)` (`l4st_firstControl_maximizes`, `l4st_firstControl_beaten`
and continuity), so `z₃(t_sw) ∈ 𝒲` (`l4st_mem_walls_of_maximizers`). -/
theorem l4st_poincare_mem_walls {z : Fin 3 → ℂ} (hz : z ≠ 0) : poincare z 2 ∈ walls := by
  sorry

/-- The control switches at `t_sw`: the first control of `F(z⁰)` differs from that of `z⁰`.

Proof route: `F(z⁰) ≠ 0` (`l4st_poincare_ne_zero`), so `firstControl (F z⁰)` is the first control
of `F(z⁰)` (`l4st_isFirstControl_firstControl`). If it were the first control `u` of `z⁰`, then `u`
would be optimal along `t ↦ z(t, F(z⁰), u) = z(t_sw + t, z⁰, u)` (`l4st_flow_add`) for
`t ∈ [0, ε]`, `ε > 0`, against `l4st_firstControl_beaten`. -/
theorem l4st_firstControl_poincare_ne {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    firstControl (poincare z) ≠ firstControl z := by
  sorry

/-! ### Equivariance -/

/-- Equivariance under `V_T` (Lemma 13.2.2 and (13.2.7)): the first control of `v z⁰` is `v` times
that of `z⁰`, the first switching time is the same, and `F(v z⁰) = v F(z⁰)`. -/
theorem l4st_poincare_smul {v : ℂ} (hv : v ∈ VT) {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    firstControl (v • z) = v * firstControl z ∧ firstSwitchTime (v • z) = firstSwitchTime z ∧
      poincare (v • z) = v • poincare z := by
  sorry

/-- Equivariance under rescaling (Lemma 13.2.1): for `r > 0`, the first control of
`(r z₁, r² z₂, r³ z₃)` is that of `z`, its first switching time is `r t_sw(z)`, and
`F(r z₁, r² z₂, r³ z₃) = (r F(z)₁, r² F(z)₂, r³ F(z)₃)`. -/
theorem l4st_poincare_scale {r : ℝ} (hr : 0 < r) {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    firstControl (scale r z) = firstControl z ∧
      firstSwitchTime (scale r z) = r * firstSwitchTime z ∧
      poincare (scale r z) = scale r (poincare z) := by
  sorry

/-- "By the scaling symmetries, … if the angular components `π_ang(q₁) = π_ang(q₂)` are equal, then
the angular components `π_ang F(q₁) = π_ang F(q₂)` of the images are equal" (TeX 11256–11260). -/
theorem l4st_ang_poincare_ang {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    ang (poincare (ang z)) = ang (poincare z) := by
  sorry

/-! ### The Hamiltonian -/

/-- `H_F⁺` under the virial group and time reversal: `H_F⁺(v·(r z₁, r² z₂, r³ z₃)) = r³ H_F⁺(z)`
for `v ∈ V_T`, `r > 0`, and `H_F⁺(τ z) = H_F⁺(z)`. -/
theorem l4st_hamMax_virial_tau {v : ℂ} (hv : v ∈ VT) {r : ℝ} (hr : 0 < r) (z : Fin 3 → ℂ) :
    hamMax (v • scale r z) = r ^ 3 * hamMax z ∧ hamMax (tau z) = hamMax z := by
  sorry

/-- **The constancy of the Hamiltonian** (TeX 11429–11431, from TeX 10740–10742):
`H_F⁺(F(z⁰)) = H_F⁺(z⁰)`. (The first control maximizes `H_F` at `0` and at `t_sw`, and `H_F` is
constant along the segment, `l4st_ham_flow`.) -/
theorem l4st_hamMax_poincare {z : Fin 3 → ℂ} (hz : z ≠ 0) : hamMax (poincare z) = hamMax z := by
  sorry

/-! ### Time reversal -/

/-- **`F⁻¹ = τ F τ` at genuine switching points** (Lemmas 13.2.3 and 13.2.5 in map form; used in
Chapter 15, TeX 12324–12328, and for the instability of `q_in` in Lemma 13.5.5). If `z⁰ ≠ 0` and
the first control `u` of `z⁰` is not also its most recent control (so that `z⁰` is a switching
point of the extremal through it), then `F(τ(F(z⁰))) = τ(z⁰)`.

Proof route: with `z* = F(z⁰)`, `τ(z⁰) = z(t_sw, τ(z*), ū)` by Lemma 13.2.5; `τ(z*) ≠ 0`
(`l4st_poincare_ne_zero`, `l4st_tau_tau`), and `ū` is optimal along this segment (the maximum
condition reverses, `l4st_ham_tau`), so it is the first control of `τ(z*)`
(`l4st_isFirstControl_unique`) and `t_sw(τ z*) ≥ t_sw(z⁰)`; equality holds because `u` is not
optimal at small negative times along `t ↦ z(t, z⁰, u)`, that is, `ū` is beaten right after
`t_sw` along the reversed segment. -/
theorem l4st_poincare_tau_poincare {z : Fin 3 → ℂ} (hz : z ≠ 0)
    (h : ¬ IsMostRecentControl z (firstControl z)) : poincare (tau (poincare z)) = tau z := by
  sorry

/-! ### The angular map on `Ξ_𝒲` and on `Ξ_𝒲/V_T` -/

/-- `F_ang` maps `Ξ_𝒲` to itself. -/
theorem l4st_ang_poincare_mem_XiW {ξ : Fin 3 → ℂ} (hξ : ξ ∈ XiW) : ang (poincare ξ) ∈ XiW := by
  sorry

/-- The Fuller–Poincaré map `F_ang : Ξ_𝒲 → Ξ_𝒲` (TeX 11256–11265), `ξ ↦ π_ang F(1, ξ)`. -/
noncomputable def poincareAng (ξ : XiW) : XiW := ⟨ang (poincare ξ), l4st_ang_poincare_mem_XiW ξ.2⟩

/-- `F_ang` is `V_T`-equivariant, so it maps orbits to orbits. -/
theorem l4st_poincareAng_orbitRel (ξ η : XiW)
    (h : MulAction.orbitRel (rootsOfUnity 3 ℂ) XiW ξ η) :
    MulAction.orbitRel (rootsOfUnity 3 ℂ) XiW (poincareAng ξ) (poincareAng η) := by
  sorry

/-- The Fuller–Poincaré map `F_ang : Ξ_𝒲/V_T → Ξ_𝒲/V_T` (TeX 11261–11265: "by equivariance"). -/
noncomputable def poincareAngQuot : XiWQuot → XiWQuot :=
  Quotient.map' poincareAng l4st_poincareAng_orbitRel

/-- `H_F⁺` is constant on the `V_T`-orbits of `Ξ_𝒲`. -/
theorem l4st_hamMax_orbitRel (ξ η : XiW) (h : MulAction.orbitRel (rootsOfUnity 3 ℂ) XiW ξ η) :
    hamMax ξ = hamMax η := by
  sorry

/-- The Hamiltonian `H_F⁺` on `Ξ_𝒲/V_T`. -/
noncomputable def hamMaxQuot : XiWQuot → ℝ :=
  Quotient.lift (fun ξ : XiW ↦ hamMax ξ) l4st_hamMax_orbitRel

/-- `Ξ_{𝒲,0}/V_T`: the subset of `Ξ_𝒲/V_T` on which the Hamiltonian vanishes (Remark 13.5.1,
Lemma 13.5.5, TeX 11280–11286, 11434–11436), with the subspace topology (which is also the
quotient topology of `Ξ_{𝒲,0} = {ξ ∈ Ξ_𝒲 | H_F⁺(ξ) = 0}`, a saturated subset). -/
abbrev XiW0Quot : Type := {x : XiWQuot // hamMaxQuot x = 0}

/-- `F_ang` preserves the zero set of the Hamiltonian ("by the constancy of the Hamiltonian, the
map `F` restricts to the zero set of the Hamiltonian", TeX 11429–11431): `H_F⁺(F_ang ξ) =
φ(F ξ)⁻³ H_F⁺(ξ)`. -/
theorem l4st_hamMaxQuot_poincareAngQuot (x : XiWQuot) :
    hamMaxQuot (poincareAngQuot x) = 0 ↔ hamMaxQuot x = 0 := by
  sorry

/-- The Fuller–Poincaré map restricted to `Ξ_{𝒲,0}/V_T` (Lemma 13.5.5, TeX 11434). -/
noncomputable def poincareAngZero (x : XiW0Quot) : XiW0Quot :=
  ⟨poincareAngQuot x.1, (l4st_hamMaxQuot_poincareAngQuot x.1).2 x.2⟩

/-- `τ` maps `Ξ_𝒲` to itself (`φ(τ ξ) = φ(ξ)`, `conj 𝒲 = 𝒲`). -/
theorem l4st_tau_mem_XiW {ξ : Fin 3 → ℂ} (hξ : ξ ∈ XiW) : tau ξ ∈ XiW := by
  sorry

/-- The time reversal `τ` on `Ξ_𝒲`. -/
noncomputable def tauXiW (ξ : XiW) : XiW := ⟨tau ξ, l4st_tau_mem_XiW ξ.2⟩

/-- `τ` maps `V_T`-orbits to `V_T`-orbits (`τ(v ξ) = v̄ τ(ξ)`). -/
theorem l4st_tauXiW_orbitRel (ξ η : XiW) (h : MulAction.orbitRel (rootsOfUnity 3 ℂ) XiW ξ η) :
    MulAction.orbitRel (rootsOfUnity 3 ℂ) XiW (tauXiW ξ) (tauXiW η) := by
  sorry

/-- The time reversal `τ` on `Ξ_𝒲/V_T`. -/
noncomputable def tauQuot : XiWQuot → XiWQuot := Quotient.map' tauXiW l4st_tauXiW_orbitRel

/-- `τ` preserves the Hamiltonian on `Ξ_𝒲/V_T`. -/
theorem l4st_hamMaxQuot_tauQuot (x : XiWQuot) : hamMaxQuot (tauQuot x) = hamMaxQuot x := by
  sorry

/-- The time reversal `τ` on `Ξ_{𝒲,0}/V_T`. -/
noncomputable def tauZero (x : XiW0Quot) : XiW0Quot :=
  ⟨tauQuot x.1, (l4st_hamMaxQuot_tauQuot x.1).trans x.2⟩

/-! ### Topology of the quotients -/

/-- `Ξ_𝒲/V_T` is a compact Hausdorff space (`Ξ_𝒲` is compact, `V_T` finite), and `Ξ_{𝒲,0}/V_T`
is closed in it (`hamMaxQuot` is continuous). -/
theorem l4st_topology_XiWQuot :
    CompactSpace XiWQuot ∧ T2Space XiWQuot ∧ IsClosed {x : XiWQuot | hamMaxQuot x = 0} := by
  sorry

/-- `τ` is a continuous involution of `Ξ_{𝒲,0}/V_T`. -/
theorem l4st_tauZero_continuous_involutive :
    Continuous tauZero ∧ Function.Involutive tauZero := by
  sorry

end TriFuller

end SmoothedPolygons
