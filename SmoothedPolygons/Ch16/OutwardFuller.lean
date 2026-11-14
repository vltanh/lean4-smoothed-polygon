module

public import SmoothedPolygons.Ch16.GlobalBasin

/-!
# Chapter 16: Theorem 16.2.1, outward and inward Fuller trajectories

§16.2 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Classification of Outward Fuller
Trajectories", TeX 12747–12779): the switching points of a trajectory of the Fuller–Poincaré
dynamical system on `(ℂ³ ∖ 0)/V_T` that emanates from the singular locus `0` all lie on the ray
`ℝ_{>0} × {q_out}` (the outward triangular spiral), and those of a trajectory that tends to `0` on
the ray `ℝ_{>0} × {q_in}` (the inward spiral). Not used by any later result of the book.

Formalized with the Poincaré map `F = poincare` on `ℂ³ ∖ 0` (the map of the dynamical system, TeX
12749–12752), a trajectory being a sequence of switching points `F^k(z⁰)` (inward) or a backward
orbit `F(z_{k+1}) = z_k` (outward), and "in `ℝ_{>0} × {q}` modulo `V_T`" being "the class of the
angular part is `q`" (`classOf`). The radial factor `ρ(x) = φ(F ξ)` (`radialFactor`) is the factor
by which one step multiplies the weighted norm `φ`, by homogeneity (Lemma 13.2.1).

## The book's proof (TeX 12763–12778), and gap G16.6

"By time reversal symmetry, it is enough to prove the second statement … Let `q ∈ Ξ_𝒲/V_T` be any
switching point of any trajectory. If `q = q_in`, then it is the inward spiral. Otherwise … by the
Fuller basin theorem and by the stability calculation near `q_in`, for large `j`, the iterates
`F_ang^j(q)` approach the outward spiral. … The outward spiral moves away from the singular locus
(because of the scaling factor `r_scale > 1`), and the Fuller trajectory must then also move away
from the singular locus."

The details the book leaves implicit (gap G16.6), supplied here:
* the basin theorem is about `Ξ_{𝒲,0}`; a trajectory tending to `0` has `H_F⁺ = 0`, because
  `H_F⁺` is constant along it and `H_F⁺(z) = φ(z)³ H_F⁺(ang z)` with `H_F⁺` bounded on the compact
  `Ξ` (`hamMax_eq_zero_of_tendsto_zero`); so the theorem holds on all of `(ℂ³ ∖ 0)/V_T` as stated;
* "the stability calculation near `q_in`" is not needed (Theorem 16.1.1 covers every `q ≠ q_in`);
* "approaches the outward spiral … must also move away": `φ(F^{k+1} z) = φ(F^k z) ρ([F^k z])`
  (`weightedNorm_poincare_eq`), `ρ` is continuous at `q_out` with `ρ(q_out) = r_scale > 1`
  (`radialFactor_qOut0`, `continuousAt_radialFactor_qOut0`; Lemma 13.5.2, Remark 13.5.3), so the
  weighted norms eventually grow geometrically;
* the time reversal: `F(τ z_k) = τ z_{k+1}` along a backward orbit, by `F⁻¹ = τ F τ` at switching
  points (`poincare_tau_poincare`; every `z_k = F(z_{k+1})` is a switching point).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

namespace TriFuller

/-- The radial factor `ρ(x) = φ(F ξ)` at `x = [ξ] ∈ Ξ_{𝒲,0}/V_T` (`ξ ∈ Ξ_𝒲`, `φ(ξ) = 1`; computed at
the representative `Quotient.out`, and independent of it, `weightedNorm_poincare_eq`): one step of
the Fuller–Poincaré map multiplies the weighted norm by `ρ`. -/
noncomputable def radialFactor (x : XiW0Quot) : ℝ :=
  weightedNorm (poincare ((Quotient.out x.1 : XiW) : Fin 3 → ℂ))

/-- `φ(F z) = φ(z) ρ([z])` for `z` in the section: `z = (φ(z) ξ₁, φ(z)² ξ₂, φ(z)³ ξ₃)` with
`ξ = ang z`, `F` commutes with the rescaling (`poincare_scale`) and with `V_T` (`poincare_smul`),
and `φ(r w) = r φ(w)`, `φ(v w) = φ(w)` (`weightedNorm_scale`, `weightedNorm_smul`). -/
theorem weightedNorm_poincare_eq {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) :
    weightedNorm (poincare z) = weightedNorm z * radialFactor (classOf z) := by
  sorry

/-- `ρ(q_out) = r_scale`: `F(qOutCart) = ζ² (r_scale qOutCart₁, r_scale² qOutCart₂, r_scale³
qOutCart₃)` (Lemma 13.5.2, `poincare_qOutCart`), so `φ(F qOutCart) = r_scale φ(qOutCart)`. -/
theorem radialFactor_qOut0 : radialFactor qOut0 = rScale := by
  sorry

/-- **The radial factor is continuous at `q_out`.** Proof route: near `q_out`, `Ξ_{𝒲,0}/V_T` is
charted by the cell coordinates on the open first box (`definition15_1_2`: `cellClass` maps
`openBoxOne` bijectively onto the open set `openCellOne`, with continuous inverse `cellCoords`);
`ρ(cellClass p) = φ(F(cellPoint p))/φ(cellPoint p)`; near `pOut` the first control is `ζ` and the
first switching time is the simple root of `χ_A` near `t_sw(pOut)` (`χ_B > 0` before it), which
depends continuously on `p` (as in `continuousAt_firstSwitchTime_of_ne_zero`); so
`p ↦ F(cellPoint p)` is continuous at `pOut`. -/
theorem continuousAt_radialFactor_qOut0 : ContinuousAt radialFactor qOut0 := by
  sorry

/-- The iterates of `F` stay in the section and their classes are the iterates of `F_ang`
(`poincare_mem_sectionZero`, `poincareAngZero_classOf`). -/
theorem classOf_poincare_iterate {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) (k : ℕ) :
    poincare^[k] z ∈ sectionZero ∧ classOf (poincare^[k] z) = poincareAngZero^[k] (classOf z) := by
  sorry

/-- **A trajectory tending to the singular locus has vanishing Hamiltonian** (gap G16.6: the
basin theorem is about `Ξ_{𝒲,0}`). `H_F⁺(F^k z) = H_F⁺(z)` (`hamMax_poincare`) and
`H_F⁺(w) = φ(w)³ H_F⁺(ang w)` (`hamMax_smul_scale_and_tau`) with `|H_F⁺|` bounded on the compact
`Ξ`; if `F^k z → 0` then `φ(F^k z) → 0` and `H_F⁺(z) = 0`. -/
theorem hamMax_eq_zero_of_tendsto_zero {z : Fin 3 → ℂ} (hz : z ≠ 0)
    (h : Tendsto (fun k : ℕ ↦ poincare^[k] z) atTop (𝓝 0)) : hamMax z = 0 := by
  sorry

end TriFuller

open TriFuller

/-- **Theorem 16.2.1** (`thm:outward-fuller`, TeX 12754–12761). "Consider the Fuller–Poincaré
dynamical system `F` on `(ℂ³ ∖ 0)/V_T`. Every outward trajectory that emanates from the singular
locus has all its switching points in the set `ℝ_{>0} × {q_out}` modulo `V_T`. Every inward
trajectory to the singular locus has all its switching points in the set `ℝ_{>0} × {q_in}` modulo
`V_T`."

Formalized: (outward) if `z_k ≠ 0`, `F(z_{k+1}) = z_k` and `z_k → 0` as `k → ∞` (the switching
points, going back in time, tend to `0`), then every `z_k` lies in the section (with `H_F⁺ = 0`) and
represents `q_out`; (inward) if `z⁰ ≠ 0` lies on a wall and `F^k(z⁰) → 0`, then every `F^k(z⁰)` lies
in the section and represents `q_in`. It depends on Theorem 16.1.1, hence on its three numerical
hypotheses.

Proof (the book's, module docstring): inward: `H_F⁺(z⁰) = 0` (`hamMax_eq_zero_of_tendsto_zero`); let
`x = classOf z⁰`; if `x ≠ q_in`, `F_ang^k(x) → q_out` (`theorem16_1_1`), so
`ρ(F_ang^k x) → r_scale > 1` (`continuousAt_radialFactor_qOut0`, `radialFactor_qOut0`) and
`φ(F^k z⁰) = φ(z⁰) ∏_{j<k} ρ(F_ang^j x)` (`weightedNorm_poincare_eq`, `classOf_poincare_iterate`)
grows geometrically, against `F^k z⁰ → 0`; so `x = q_in`, a fixed point. Outward, by time reversal:
`w_k = τ(z_k)` satisfies `F(w_k) = w_{k+1}` (`poincare_tau_poincare` at the switching point
`z_{k+1} = F(z_{k+2})`) and `w_k → 0`, so `[w_k] = q_in` and `[z_k] = τ q_in = q_out`. -/
theorem theorem16_2_1 (h₁ : DOutContracts) (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims) :
    (∀ z : ℕ → Fin 3 → ℂ, (∀ k, z k ≠ 0) → (∀ k, poincare (z (k + 1)) = z k) →
      Tendsto z atTop (𝓝 0) → ∀ k, z k ∈ sectionZero ∧ classOf (z k) = qOut0) ∧
    ∀ z₀ : Fin 3 → ℂ, z₀ ≠ 0 → z₀ 2 ∈ walls →
      Tendsto (fun k : ℕ ↦ poincare^[k] z₀) atTop (𝓝 0) →
      ∀ k, poincare^[k] z₀ ∈ sectionZero ∧ classOf (poincare^[k] z₀) = qIn0 := by
  sorry

end SmoothedPolygons
