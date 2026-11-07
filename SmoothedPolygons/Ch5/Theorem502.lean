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

## Proofs

* `densityBound_dihedralAct`: by Lemma 5.0.4, `δ(z)` is a symmetric function of the three star
  functions `ρⱼ(Φ(z))` (the pair `(T_i, T_i^ext)` is `((√3/4) ρ_a ρ_b, √3 ρ_c²)` with `{a, b, c}`
  the three indices); `Φ(R^n · z) = R^n Φ(z) R^{-n}` (`Φ_lftAct`) and `Φ(-z̄) = -SΦ(z)S⁻¹`
  (`reflS_conj_Φ`), and `R`, `S` permute the star functions (`ρ_R_conj`, `ρ_reflS_conj`).
* `octagonDensity_lt_densityBound`: steps 1–3 above.
* `sqrt12_mul_densityBound_le_volume`: `IsBalancedPair.recenter`, `lemma5_0_3`, `theorem5_0_6`.
  (The hypothesis `IsCircleRepresentation σ` is not used: the re-centered disk is in circle
  representation whatever `σ(0)` is.)
* `theorem5_0_2`: `eqn_cost` (the curve `g` is differentiable because its columns are `σ₀` and
  `(2σ₁ - σ₀)/√3`, and `g' = gX` since `det g = 1`), `smoothedOctagon_volume`,
  `greatestPackingDensity_of_isBalancedPair`, and the admissibility of the smoothed octagon's
  trajectory (`smoothedPolygonDisk_spec`, `theorem7_5_6`).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix

/-! ### The density bound as a symmetric function of the star functions -/

/-- The term `I area` of a pair `(T, T^ext) = ((√3/4) p q, √3 e²)` (Lemma 5.0.4): `T - √(T^ext T)`
if `T^ext ≤ T`, and `0` otherwise. -/
private noncomputable def eb_term (e p q : ℝ) : ℝ :=
  if √3 * e ^ 2 ≤ √3 / 4 * p * q then √3 / 4 * p * q - √(√3 * e ^ 2 * (√3 / 4 * p * q)) else 0

/-- The density bound in terms of the star functions `a = ρ₀`, `b = ρ₁`, `c = ρ₂`
(Lemma 5.0.4: the pair `i = 0` is `((√3/4)ρ₀ρ₂, √3ρ₁²)`, `i = 1` is `((√3/4)ρ₀ρ₁, √3ρ₂²)`,
`i = 2` is `((√3/4)ρ₁ρ₂, √3ρ₀²)`). -/
private noncomputable def eb_G (a b c : ℝ) : ℝ :=
  (3 * √3 / 2 + 2 * (eb_term b a c + eb_term c a b + eb_term a b c)) / √12

private lemma eb_term_comm (e p q : ℝ) : eb_term e p q = eb_term e q p := by
  simp only [eb_term, mul_right_comm (√3 / 4) p q]

/-- `G` is invariant under the cyclic permutation of the star functions. -/
private lemma eb_G_rot (a b c : ℝ) : eb_G c a b = eb_G a b c := by
  simp only [eb_G]
  rw [eb_term_comm a c b, eb_term_comm b c a]
  ring

/-- `G` is invariant under the transposition `ρ₀ ↔ ρ₁` of the star functions. -/
private lemma eb_G_swap (a b c : ℝ) : eb_G b a c = eb_G a b c := by
  simp only [eb_G]
  rw [eb_term_comm c b a]
  ring

/-- On `𝔥*`, the term `I_i area_i` of the pair `(T_i, T_i^ext) = ((√3/4) p q, √3 e²)`. -/
private lemma eb_indicator_eq {x y : ℝ} (hz : (x, y) ∈ starDomain) {i : Fin 3} {e p q : ℝ}
    (hT : triArea x y i = √3 / 4 * p * q) (hE : extTriArea x y i = √3 * e ^ 2) :
    (hRegion i).indicator (areaFn i) (x, y) = eb_term e p q := by
  unfold eb_term
  split_ifs with h
  · have hm : (x, y) ∈ hRegion i := ⟨hz, by rw [hT, hE]; exact h⟩
    rw [Set.indicator_of_mem hm, areaFn, hT, hE]
  · exact Set.indicator_of_notMem (fun hm ↦ h (by rw [← hT, ← hE]; exact hm.2)) _

/-- On `𝔥*`, `δ(z) = G(ρ₀, ρ₁, ρ₂)` with `ρⱼ = ρⱼ(Φ(z))`, by Lemma 5.0.4. -/
private lemma eb_densityBound_eq_G {z : ℝ × ℝ} (hz : z ∈ starDomain) :
    densityBound z = eb_G (ρ₀ (Φ z.1 z.2)) (ρ₁ (Φ z.1 z.2)) (ρ₂ (Φ z.1 z.2)) := by
  obtain ⟨x, y⟩ := z
  obtain ⟨h0, h1, h2, e0, e1, e2, -⟩ := lemma5_0_4 hz
  rw [densityBound, eb_G, Fin.sum_univ_three, eb_indicator_eq hz h0 e0, eb_indicator_eq hz h1 e1,
    eb_indicator_eq hz h2 e2]

/-- `Φ` has trace zero. -/
private lemma eb_trace_Φ (x y : ℝ) : (Φ x y).trace = 0 := by
  simp [Φ, Matrix.trace_fin_two]; ring

/-- `det R = 1`. -/
private lemma eb_det_R : R.det = 1 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp [R, Matrix.det_fin_two]
  nlinarith

/-- The rotations `R^n` permute the star functions of a traceless matrix, so they preserve `G`
(§4.6, `ρ_R_conj`). -/
private lemma eb_G_R_pow (n : ℕ) {X : Mat2} (hX : X.trace = 0) :
    eb_G (ρ₀ (R ^ n * X * (R ^ n)⁻¹)) (ρ₁ (R ^ n * X * (R ^ n)⁻¹)) (ρ₂ (R ^ n * X * (R ^ n)⁻¹)) =
      eb_G (ρ₀ X) (ρ₁ X) (ρ₂ X) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hu : IsUnit (R ^ n).det := by rw [Matrix.det_pow, eb_det_R, one_pow]; exact isUnit_one
    have htr : (R ^ n * X * (R ^ n)⁻¹).trace = 0 := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
        Matrix.one_mul, hX]
    have e : R ^ (n + 1) * X * (R ^ (n + 1))⁻¹ = R * (R ^ n * X * (R ^ n)⁻¹) * R⁻¹ := by
      rw [pow_succ', Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    obtain ⟨r0, r1, r2⟩ := ρ_R_conj _ htr
    rw [e, r0, r1, r2, eb_G_rot, ih]

/-- **The density bound is invariant under the dihedral group** (TeX 4470–4471, "everything …
has been equivariant"): `δ(S^b R^n · z) = δ(z)` on `𝔥*`.

Proof: by Lemma 5.0.4, `δ(z)` is a symmetric function `G` of the three star functions
`ρⱼ(Φ(z))` (`eb_densityBound_eq_G`); `Φ(R^n · z) = R^n Φ(z) R^{-n}` (`Φ_lftAct`, Remark 4.2.2)
and `Φ(-z̄) = -SΦ(z)S⁻¹` (`reflS_conj_Φ`), and `R`, `S` permute the star functions (§4.6,
`ρ_R_conj`, `ρ_reflS_conj`). -/
theorem densityBound_dihedralAct (n : ℕ) (b : Bool) {z : ℝ × ℝ} (hz : z ∈ starDomain) :
    densityBound (dihedralAct n b z) = densityBound z := by
  have hw : dihedralAct n b z ∈ starDomain := (dihedralAct_mem_iff n b hz.1).1.2 hz
  rw [eb_densityBound_eq_G hw, eb_densityBound_eq_G hz]
  have hRn : (R ^ n).det = 1 := by rw [Matrix.det_pow, eb_det_R, one_pow]
  have hΦ := Φ_lftAct (R ^ n) hRn hz.1
  cases b with
  | false =>
    simp only [dihedralAct, Bool.false_eq_true, ↓reduceIte]
    rw [hΦ, eb_G_R_pow n (eb_trace_Φ _ _)]
  | true =>
    simp only [dihedralAct, ↓reduceIte, reflAct]
    set w := lftAct (R ^ n) z
    have htr : (Φ w.1 w.2).trace = 0 := eb_trace_Φ _ _
    obtain ⟨s0, s1, s2⟩ := ρ_reflS_conj _ htr
    rw [← reflS_conj_Φ, s0, s1, s2, eb_G_swap, hΦ, eb_G_R_pow n (eb_trace_Φ _ _)]

/-- **`δ > δ_oct` off `𝔥**`** (the content of the proof of Theorem 5.0.2, TeX 4469–4513): for every
`z ∈ 𝔥* \ 𝔥**`, `δ(z) > δ_oct`.

The book's proof: move `z` into the fundamental domain by the dihedral group (which preserves `δ`
and `𝔥**`); there a point outside `𝔥**` lies in `B(i∞)` (Lemma 5.0.7 (4)) or in
`Π₀⁺ ∩ {1 ≤ y ≤ 4.5}` (Lemma 5.0.7 (1) and the one-variable bound). -/
theorem octagonDensity_lt_densityBound {z : ℝ × ℝ} (hz : z ∈ starDomain)
    (hout : z ∉ truncatedStarDomain) : octagonDensity < densityBound z := by
  obtain ⟨n, b, hfd⟩ := exists_dihedralAct_mem_fundamentalDomain hz
  have hwS : dihedralAct n b z ∈ starDomain := hfd.1
  have hwout : dihedralAct n b z ∉ truncatedStarDomain := by
    rw [(dihedralAct_mem_iff n b hz.1).2]; exact hout
  rw [← densityBound_dihedralAct n b hz]
  obtain ⟨-, hy1, hcases⟩ := mem_horoball_or_edgeHalfPlane_of_mem_fundamentalDomain hfd
  rcases hcases hwout with h | ⟨hP, hy⟩
  · exact lemma5_0_7_4 ⟨hwS.2.1, hwS.2.2.1⟩ (le_of_lt h)
  · exact octagonDensity_lt_densityBound_of_mem_edgeHalfPlane hwS hP hy1 hy

/-- **The density bound along the trajectory** (Theorem 5.0.6 at every time, TeX 4486–4489 and
4332–4348): for a balanced disk `K` in circle representation with boundary trajectory `(g, X)`,
`σ_j(t) = g(t) s_j*`, `X = g⁻¹g' = Φ ∘ z`, and every time `t₀`, `area(K) ≥ √12 δ(z(t₀))`.

Proof: re-center `K` at `t₀` (`IsBalancedPair.recenter`: `g(t₀)⁻¹K` is a balanced disk in circle
representation, of the same area, whose `X` at time `0` is `X(t₀) = Φ(z(t₀))`); by Lemma 5.0.3
its critical hexagon is `H_K(z(t₀))`, and Theorem 5.0.6 bounds its area by
`3√3/2 + 2 Σ I_i area_i = √12 δ(z(t₀))`. -/
theorem sqrt12_mul_densityBound_le_volume {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    {tf : ℝ} (hKσ : IsBalancedPair K σ tf) (hcirc : IsCircleRepresentation σ) {g X : ℝ → Mat2}
    (hg : ∀ j t, σ j t = g t *ᵥ sixthRoot j)
    (hX : ∀ t, X t = (g t)⁻¹ * derivEntrywise g t) {z : ℝ → ℝ × ℝ}
    (hz : ∀ t, z t ∈ starDomain ∧ X t = Φ (z t).1 (z t).2) (t₀ : ℝ) :
    √12 * densityBound (z t₀) ≤ volume.real K := by
  obtain ⟨hbal, hcirc', hg', hX', hvol⟩ := hKσ.recenter hg t₀
  have hX0 : ((g t₀)⁻¹ * g (0 + t₀))⁻¹ * derivEntrywise (fun s ↦ (g t₀)⁻¹ * g (s + t₀)) 0 =
      Φ (z t₀).1 (z t₀).2 := by
    rw [hX' 0, zero_add, ← hX, (hz t₀).2]
  have hzt := (hz t₀).1
  have hvol' : volume.real ((fun v ↦ (g t₀)⁻¹ *ᵥ v) '' K) = volume.real K := by
    rw [measureReal_def, measureReal_def, hvol]
  rw [← hvol']
  generalize z t₀ = w at hzt hX0 ⊢
  obtain ⟨x, y⟩ := w
  obtain ⟨-, -, -, hcrit⟩ := lemma5_0_3 hzt
  have hH := (hcrit _ _ tf (fun s ↦ (g t₀)⁻¹ * g (s + t₀)) hbal hcirc' hg' hX0).1
  have h6 := theorem5_0_6 hbal hcirc' hzt hH
  have h12 : (0 : ℝ) < √12 := by positivity
  rw [densityBound, mul_div_cancel₀ _ h12.ne']
  exact h6

/-- The matrix curve `g` of a balanced disk with `σ_j = g s_j*` is differentiable, entry by entry:
its columns are `σ₀` and `(2σ₁ - σ₀)/√3`. -/
private lemma eb_hasDerivAtEntrywise {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    {tf : ℝ} (hKσ : IsBalancedPair K σ tf) {g : ℝ → Mat2}
    (hg : ∀ j t, σ j t = g t *ᵥ sixthRoot j) (t : ℝ) :
    HasDerivAtEntrywise g (derivEntrywise g t) t := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hd : ∀ j i, DifferentiableAt ℝ (fun s ↦ σ j s i) t := fun j ↦
    differentiableAt_pi.1 (((hKσ.2.1 j).1.differentiable one_ne_zero) t)
  have hc0 : ∀ i, (fun s ↦ g s i 0) = fun s ↦ σ 0 s i := by
    intro i; funext s
    rw [hg 0 s, algA_sixthRoot_zero]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hc1 : ∀ i, (fun s ↦ g s i 1) = fun s ↦ (2 * σ 1 s i - σ 0 s i) / √3 := by
    intro i; funext s
    rw [hg 0 s, hg 1 s, algA_sixthRoot_zero, algA_sixthRoot_one]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    ring
  intro i j
  have hdiff : DifferentiableAt ℝ (fun s ↦ g s i j) t := by
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue]; rw [hc0 i]; exact hd 0 i
    · simp only [Fin.mk_one, Fin.isValue]; rw [hc1 i]
      exact (((hd 1 i).const_mul 2).sub (hd 0 i)).div_const _
  simpa [derivEntrywise] using hdiff.hasDerivAt

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
  have h12 : (0 : ℝ) < √12 := by positivity
  -- `area(K) ≥ √12 δ(z(t₀)) > √12 δ_oct` (Theorem 5.0.6 and the density bound off `𝔥**`)
  have hδ := octagonDensity_lt_densityBound (hz t₀).1 hout
  have hle := sqrt12_mul_densityBound_le_volume hKσ hcirc hg hX hz t₀
  -- the smoothed octagon: a balanced disk of area `√12 δ_oct`, with an admissible trajectory
  obtain ⟨hst, hg0, hX0, -, -, hbal8, -, hvol8⟩ := smoothedPolygonDisk_spec 1 le_rfl
  obtain ⟨-, Λ₁, ΛR, lam, hPE⟩ := (theorem7_5_6 1 le_rfl).2 _ _ hst hg0 hX0
  have hadm8 : IsReinhardtAdmissible (SmoothedPolygons.tf 1) (polygonControl 1) (smoothedPolygonG 1)
      (smoothedPolygonX 1) := ⟨hst, hg0, hPE.2.2.1, hPE.2.2.2.1⟩
  have hoct : volume.real (smoothedPolygonDisk 1) = √12 * octagonDensity := by
    rw [octagonDensity, ← smoothedOctagon_volume.2, measureReal_def, mul_div_cancel₀ _ h12.ne']
  have hcost8 : reinhardtCost (SmoothedPolygons.tf 1) (smoothedPolygonX 1) ≤
      volume.real (smoothedPolygonDisk 1) := by
    rw [measureReal_def, hvol8, ENNReal.toReal_ofReal']
    exact le_max_left _ _
  have hlt : volume.real (smoothedPolygonDisk 1) < volume.real K := by
    rw [hoct]
    exact (mul_lt_mul_of_pos_left hδ h12).trans_le hle
  -- the cost of the trajectory is the area of `K` (`eqn:cost`)
  have hcost : reinhardtCost tf X = volume.real K := by
    have hderiv : ∀ t ∈ Ioo 0 tf, HasDerivAtEntrywise g (g t * X t) t := by
      intro t ht
      have hdet : (g t).det = 1 := oct_det_eq_one hKσ (fun j s _ ↦ hg j s) (Ioo_subset_Icc_self ht)
      rw [hX t, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_one),
        Matrix.one_mul]
      exact eb_hasDerivAtEntrywise hKσ hg t
    have hvol := eqn_cost hKσ g X (fun j s _ ↦ hg j s) hderiv hshift
    have hK : volume.real K = max (reinhardtCost tf X) 0 := by
      rw [measureReal_def, hvol, ENNReal.toReal_ofReal']
    have hpos : 0 < volume.real K := lt_of_le_of_lt measureReal_nonneg hlt
    rw [hK] at hpos ⊢
    rcases le_total (reinhardtCost tf X) 0 with h | h
    · rw [max_eq_right h] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact (max_eq_left h).symm
  refine ⟨hcost ▸ hlt, hcost, ?_, ?_⟩
  · -- densities `area/√12` (E12)
    rw [greatestPackingDensity_of_isBalancedPair hbal8,
      greatestPackingDensity_of_isBalancedPair hKσ]
    exact div_lt_div_of_pos_right hlt h12
  · -- the octagon's trajectory is admissible and cheaper
    rintro u ⟨-, hmin⟩
    have := hmin _ _ _ _ hadm8
    linarith

end SmoothedPolygons
