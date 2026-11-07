module

public import SmoothedPolygons.Ch5.AreaBound
public import SmoothedPolygons.Ch5.EdgeBound
public import SmoothedPolygons.Ch5.Recenter
public import SmoothedPolygons.Ch3.ControlProblem
public import SmoothedPolygons.Ch7.SmoothedPolygonDisk

/-!
# Theorem 5.0.2: balanced disks whose trajectory leaves `𝔥**` are worse than the smoothed octagon

**Theorem 5.0.2** (`th:compactification`, TeX 3982–3990). Let `K` be a balanced disk with boundary
trajectory `(g, X)` and `z` the trajectory in `𝔥*` with `Φ ∘ z = X`. If some `z(t)` is not in
`𝔥**`, the cost of the trajectory, which is `area(K)`, is strictly greater than the area of the
smoothed octagon; hence `K` is not a global minimizer.

## The book's proof (TeX 4469–4513), and what it uses without stating

1. *Dihedral reduction* (TeX 4470–4479). "Everything in this subsection up until this point has
   been equivariant with respect to the action of the dihedral group on `𝔥*`", and `𝔥**` is
   invariant (`image_lftAct_R_truncatedStarDomain`, `image_reflAct_truncatedStarDomain`), so it
   suffices to treat `z` in a fundamental domain (`exists_dihedralAct_mem_fundamentalDomain`, with
   the correction `≥ 4/3` of TeX 4479). The equivariance used is that of the density bound:
   `δ(R · z) = δ(z)` and `δ(-z̄) = δ(z)` (`densityBound_dihedralAct`), because `R` and `S` permute
   the star functions (`ρ_R_conj`, `ρ_reflS_conj`; §4.6) and hence, by Lemma 5.0.4, the pairs
   `(T_i, T_i^ext)`. So the reduction acts on the points of `𝔥*` only; the action of the dihedral
   group on balanced disks and their trajectories (with time reversal for `S`) is not needed.
2. On the fundamental domain, which lies in `{x ≥ 0, y ≥ 1}`, a point outside `𝔥**` lies in `B(i∞)`
   or in `Π₀⁺ ∩ {y ≤ 4.5}` (`mem_horoball_or_edgeHalfPlane_of_mem_fundamentalDomain`, with the
   correction for `Π₂⁺` noted there).
3. `B(i∞)`: Lemma 5.0.7 (4) (`lemma5_0_7_4`). `Π₀⁺`: Lemma 5.0.7 (1) and the one-variable bound
   (`octagonDensity_lt_densityBound_of_mem_edgeHalfPlane`). Steps 1–3 give
   `octagonDensity_lt_densityBound`: `δ(z) > δ_oct` for every `z ∈ 𝔥* \ 𝔥**`.
4. Implicit steps, made explicit in `sqrt12_mul_densityBound_le_volume` and `theorem5_0_2`:
   * re-centering at the time `t₀` with `z(t₀) ∉ 𝔥**` (`IsBalancedPair.recenter`): the re-centered
     disk is balanced, in circle representation, of the same area, with `X(0) = X(t₀)`;
   * Lemma 5.0.3 (`lemma5_0_3`): `H_K(z(t₀))` is a least-area hexagon of the re-centered disk;
   * Theorem 5.0.6 (`theorem5_0_6`): `area(K) ≥ √12 δ(z(t₀))`;
   * the area of the smoothed octagon is `√12 δ_oct` (`smoothedOctagon_volume`; E12,
     `greatestPackingDensity_of_isBalancedPair`), and the cost of the trajectory is `area(K)`
     (`eqn_cost`, the area formula of §3.2);
   * "hence `K` is not a global minimizer": the smoothed octagon's trajectory is admissible
     (`smoothedPolygonDisk_spec`, Theorem 7.5.6) with smaller cost, and has smaller greatest
     packing density (`greatestPackingDensity_of_isBalancedPair`).

Sizes: `densityBound_dihedralAct` 150–300 lines; `octagonDensity_lt_densityBound` 100–200;
`sqrt12_mul_densityBound_le_volume` and `theorem5_0_2` 150–300.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix

/-- **The density bound is invariant under the dihedral group** (TeX 4470–4471, "everything …
has been equivariant"): `δ(S^b R^n · z) = δ(z)` on `𝔥*`. -/
theorem densityBound_dihedralAct (n : ℕ) (b : Bool) {z : ℝ × ℝ} (hz : z ∈ starDomain) :
    densityBound (dihedralAct n b z) = densityBound z := by
  sorry

/-- **`δ > δ_oct` off `𝔥**`** (the content of the proof of Theorem 5.0.2, TeX 4469–4513): for every
`z ∈ 𝔥* \ 𝔥**`, `δ(z) > δ_oct`. -/
theorem octagonDensity_lt_densityBound {z : ℝ × ℝ} (hz : z ∈ starDomain)
    (hout : z ∉ truncatedStarDomain) : octagonDensity < densityBound z := by
  sorry

/-- **The density bound along the trajectory** (Theorem 5.0.6 at every time, TeX 4486–4489 and
4332–4348): for a balanced disk `K` in circle representation with boundary trajectory `(g, X)`,
`σ_j(t) = g(t) s_j*`, `X = g⁻¹g' = Φ ∘ z`, and every time `t₀`, `area(K) ≥ √12 δ(z(t₀))`. -/
theorem sqrt12_mul_densityBound_le_volume {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    {tf : ℝ} (hKσ : IsBalancedPair K σ tf) (hcirc : IsCircleRepresentation σ) {g X : ℝ → Mat2}
    (hg : ∀ j t, σ j t = g t *ᵥ sixthRoot j)
    (hX : ∀ t, X t = (g t)⁻¹ * derivEntrywise g t) {z : ℝ → ℝ × ℝ}
    (hz : ∀ t, z t ∈ starDomain ∧ X t = Φ (z t).1 (z t).2) (t₀ : ℝ) :
    √12 * densityBound (z t₀) ≤ volume.real K := by
  sorry

/-- **Theorem 5.0.2** (`th:compactification`). Let `K` be a balanced disk in circle representation
with boundary trajectory `(g, X)` (`σ_j(t) = g(t) s_j*`, `σ_j(t + t_f) = σ_{j+1}(t)`,
`X = g⁻¹g'`), and let `z` be the trajectory in `𝔥*` with `Φ ∘ z = X`. If some point `z(t₀)` is not
in `𝔥**`, then the cost of the trajectory, which is `area(K)`, is strictly greater than the area of
the smoothed octagon. Hence `K` is not a global minimizer: the smoothed octagon has a smaller
greatest packing density, and `(g, X)` is not a global minimizer of the Reinhardt control problem
(Problem 3.6.2). -/
theorem theorem5_0_2 {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hKσ : IsBalancedPair K σ tf) (hcirc : IsCircleRepresentation σ) {g X : ℝ → Mat2}
    (hg : ∀ j t, σ j t = g t *ᵥ sixthRoot j) (hshift : ∀ j t, σ j (t + tf) = σ (j + 1) t)
    (hX : ∀ t, X t = (g t)⁻¹ * derivEntrywise g t) {z : ℝ → ℝ × ℝ}
    (hz : ∀ t, z t ∈ starDomain ∧ X t = Φ (z t).1 (z t).2) {t₀ : ℝ}
    (hout : z t₀ ∉ truncatedStarDomain) :
    volume.real (smoothedPolygonDisk 1) < reinhardtCost tf X ∧
      reinhardtCost tf X = volume.real K ∧
      greatestPackingDensity (smoothedPolygonDisk 1) < greatestPackingDensity K ∧
      ∀ u : ℝ → Fin 3 → ℝ, ¬ IsReinhardtMinimizer tf u g X := by
  sorry

end SmoothedPolygons
