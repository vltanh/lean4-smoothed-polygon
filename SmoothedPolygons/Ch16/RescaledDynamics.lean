module

public import SmoothedPolygons.Ch16.ClusterCoordinates
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Chapter 16: the rescaled Reinhardt dynamics near the divisor (§16.4.2, part 1)

§16.4.2 of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX 12887–12918: "In Section 14.2, the
asymptotic formulas in `r₀` for the Reinhardt switching functions are functions of rescaled time
`s` … By the earlier asymptotic formulas (adapted to this system of variables), the switching
functions extend analytically to a neighborhood of `r = 0`. When `r = 0`, the Reinhardt switching
function agrees with the Fuller switching function"), in the form the proof of N5 uses: in the
blow-up coordinates `z = (ρ y₁, ρ² y₂, ρ³ y₃)` of §16.4.1 and in rescaled time `s = t/ρ`, the
Reinhardt state–costate vector field and the Reinhardt Hamiltonians converge, as `ρ → 0⁺`, to the
Fuller vector field (13.2.1) and to `24 H_F`, **uniformly in the control `v ∈ U_T`** and in `y` on
compact sets.

* `simplexToUT`: the control `v` of the simplex as the point `Σ_m v_m ζ^m` of the triangle `U_T`
  (the correspondence `e_j ↦ ζ^{j-1}` of TeX 11655–11657, extended affinely);
* `fullerField u y = (-iu, y₁, y₂)`: the Fuller vector field (13.2.1) (`z₁' = -iu`, `z₂' = z₁`,
  `z₃' = z₂`);
* `rescaledField ρ v y`: the Reinhardt vector field `iso_extremalField v` (`λ_cost = -1`) at the
  phase point with Fuller coordinates `(ρ y₁, ρ² y₂, ρ³ y₃)`, read in Fuller coordinates
  (`fullerCoords` is `ℝ`-linear) and rescaled: `d/ds` of `scale ρ⁻¹ ẑ(q(s ρ))`;
* `tendstoUniformlyOn_rescaledField`, `tendstoUniformlyOn_rescaledHam`: the uniform convergence;
* `mapClusterPt_switchAng_mem_sectionZero`: the cluster points of the switching points lie in the
  Fuller section.

The uniformity in `v ∈ U_T` is what makes relaxed (weak-*) limits of the rescaled controls
legitimate: the Reinhardt field depends on `v` through `Z_v/⟨Z_v, X⟩` (not affinely), but its
limit is affine in `u = simplexToUT v`, so a limit of rescaled trajectories is a Fuller trajectory
with the weak limit of the controls (`SmoothedPolygons/Ch16/RescaledLimits.lean`).

## Proofs (plan)

Write `q = phaseOfFuller (scale ρ y)`: `X = J + O(ρ)`, `Λ₁ = -(3/2) J + O(ρ²)`, `Λ_R = O(ρ³)`
uniformly for `y` in a compact set (the explicit formulas of `phaseOfFuller`), and
`⟨Z_v, X⟩ = -2/3 + O(ρ)` uniformly in `v` (`⟨Z_v, J⟩ = -2/3` on the simplex). Expand
`[P, X]`, `[Λ₁, X]` and the `Λ_R`-equation with `P = Z_v/⟨Z_v, X⟩`: in Fuller coordinates
`ẑ₁' = -i u + O(ρ)`, `ẑ₂' = ẑ₁ + O(ρ²)`, `ẑ₃' = ẑ₂ + O(ρ³)` (the estimates of Theorem
`thm:ode-oh`, TeX 9249–9265, and its remark on `|z*| ≤ 1`, for triangular control), with `O`
uniform in `v`; dividing by `ρ⁰, ρ¹, ρ²` gives the field. The Hamiltonian:
`H(Z_v) = h - ⟨Λ_R, Z_v⟩/⟨X, Z_v⟩` with `h = 24 ρ³ RR(y₁, i y₂) + O(ρ⁴)` and
`⟨Λ_R, Z_v⟩ = Σ v_m ⟨Λ_R, Z_{e_m}⟩ = (4/3)·12 ρ³ RR(simplexToUT v, y₃) + O(ρ⁴)`. Checked
numerically (`ρ = 10⁻², 10⁻³, 10⁻⁴`, random `v` in the simplex): the errors are `O(ρ)`. The cluster
points: at a switching time the two
vertices adjacent to the switch maximize the Hamiltonian (continuity of `H` along the lift) and
`H = 0`; dividing by `ρ³` and passing to the limit, the cluster point `ξ` has two maximizing
controls (so `ξ₃ ∈ 𝒲`, `mem_walls_of_maximizers`) and `H_F⁺(ξ) = 0`. Size: 500–900 lines.

## Not formalized

The book's further claims of §16.4.2 — the third `s`-derivative of the rescaled switching
functions is nonzero for small `r`, so they "behave qualitatively like a monic cubic polynomial"
(at most three zeros, TeX 12888–12902), Weierstrass preparation at the roots, the Reinhardt cells
`𝒞_k^R`, parts `𝒟_i^R` and branch maps (TeX 12919–12987) — are not used by the proof of N5: the
zero count bounds the zeros of one constant-control piece, not the number of pieces (the third
derivative of `χ_ij` along the true trajectory changes sign with the control), and the
relaxed-limit argument needs neither cells nor Weierstrass polynomials.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology
open TriFuller

/-- A control `v` of the simplex as the point `Σ_m v_m ζ^m` of the triangle `U_T` (the vertex
`e_{m+1}` corresponds to `ζ^m`, TeX 11655–11657). -/
noncomputable def simplexToUT (v : Fin 3 → ℝ) : ℂ := ∑ m : Fin 3, (v m : ℂ) * ζ ^ (m : ℕ)

/-- The Fuller vector field (13.2.1) (TeX 10683–10696) with control `u`:
`(z₁, z₂, z₃)' = (-iu, z₁, z₂)`. -/
noncomputable def fullerField (u : ℂ) (y : Fin 3 → ℂ) : Fin 3 → ℂ := ![-I * u, y 0, y 1]

/-- The rescaled Reinhardt vector field: the state–costate field `iso_extremalField v`
(`λ_cost = -1`) at the phase point with Fuller coordinates `(ρ y₁, ρ² y₂, ρ³ y₃)`, in Fuller
coordinates, for the rescaled variables `y = scale ρ⁻¹ ẑ` and the rescaled time `s = t/ρ`. -/
noncomputable def rescaledField (ρ : ℝ) (v : Fin 3 → ℝ) (y : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ρ • scale ρ⁻¹ (fullerCoords (iso_extremalField v (phaseOfFuller (scale ρ y))))

/-- **The rescaled Reinhardt vector field converges to the Fuller vector field, uniformly in the
control** (§16.4.2, TeX 12908–12918, with the estimates of `thm:ode-oh`, TeX 9249–9265, for
triangular control): on `U_T × K`, `K` compact,
`rescaledField ρ v y → fullerField (simplexToUT v) y` uniformly as `ρ → 0⁺`. -/
theorem tendstoUniformlyOn_rescaledField {K : Set (Fin 3 → ℂ)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun ρ (p : (Fin 3 → ℝ) × (Fin 3 → ℂ)) ↦ rescaledField ρ p.1 p.2)
      (fun p ↦ fullerField (simplexToUT p.1) p.2) (𝓝[>] 0) (controlSimplex ×ˢ K) := by
  sorry

/-- **The rescaled Reinhardt Hamiltonians converge to the Fuller Hamiltonian, uniformly in the
control** (TeX 11651–11658 and the remark after (11.2.6), in blow-up coordinates):
`H(Z_v)/ρ³ → 24 H_F(y, simplexToUT v)` uniformly on `U_T × K` as `ρ → 0⁺`. -/
theorem tendstoUniformlyOn_rescaledHam {K : Set (Fin 3 → ℂ)} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun ρ (p : (Fin 3 → ℝ) × (Fin 3 → ℂ)) ↦ phaseHam (phaseOfFuller (scale ρ p.2)) p.1 / ρ ^ 3)
      (fun p ↦ 24 * ham p.2 (simplexToUT p.1)) (𝓝[>] 0) (controlSimplex ×ˢ K) := by
  sorry

/-- **The cluster points of the switching points lie in the Fuller section** (TeX 13028–13036:
"Consider the set of cluster points on the exceptional divisor, viewed as a union of the two big
cells"): along a chattering arc, every cluster point `ξ` of the angular components `ξ_n` of the
switching points has `ξ₃` on a wall and `H_F⁺(ξ) = 0` (the limits, after rescaling by `ρ³`, of the
tie of the two maximizing vertices at a switching time and of `H = 0`;
`tendstoUniformlyOn_rescaledHam`, `mem_walls_of_maximizers`). -/
theorem mapClusterPt_switchAng_mem_sectionZero {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ)
    {ξ : Fin 3 → ℂ} (hξ : MapClusterPt ξ atTop (switchAng X Λ₁ ΛR τ)) : ξ ∈ sectionZero := by
  sorry

end SmoothedPolygons
