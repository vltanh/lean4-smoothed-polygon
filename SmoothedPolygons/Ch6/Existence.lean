module

public import SmoothedPolygons.Ch5.Theorem502
public import SmoothedPolygons.Ch6.AdmissibleDisk
public import SmoothedPolygons.Ch6.MatrixExtremal
public import SmoothedPolygons.Ch6.Hamiltonian
public import SmoothedPolygons.Ch4.TerminalTime
public import OptimalControl.ODE.StateConstraint

/-!
# Existence of an optimal control (§6.1)

§6.1 (`sec:existence-opt-control`, TeX 4520–4600) argues that the Reinhardt control problem
(Problem 3.6.2) has an optimal control, by Filippov's theorem (Theorem 6.1.1,
`External.filippov`). With the lift of every global minimizer to a Pontryagin extremal (§6.2,
`exists_isPontryaginExtremal_of_isReinhardtMinimizer`), this gives a global minimizer that is a
Pontryagin extremal (`exists_isReinhardtMinimizer_isPontryaginExtremal`), the premise of
Proposition 8.1.3 ("We have seen that the global minimizer must be extremal", TeX 6791).

## The book's argument (TeX 4553–4600)

* the control set `U_T` is compact; the velocity sets are convex (Lemma 6.1.2, `lemma6_1_2`);
* "Recall that Reinhardt has proved the existence of an optimal solution to the Reinhardt problem.
  We claim that the velocity sets can be assumed to be compactly supported": by Theorem 5.0.2,
  "we may assume that `z` lies in the compact set `𝔥**`", so `Φ(z)` and the field
  `[Z_u, Φ(z)]/⟨Z_u, Φ(z)⟩` are bounded; `t_f ≤ π/3` by Lemma 4.3.1 and Gronwall's inequality
  (App. A.1) bound `g`;
* the fields are multiplied by a smooth cut-off `ψ` with `ψ = 1` on `𝔥**`, and Filippov's theorem is
  applied to the cut-off system.

## Gaps, and their repair along the book's lines (inventory, Part I §3.5)

1. *Theorem 5.0.2 is about balanced disks; §6.1 applies it to admissible trajectories.* That needs
   the converse of Problem 3.6.2 (E15), which is false for trajectories of higher winding number
   (`exists_isReinhardtAdmissible_not_isWindingOne`). Repair: higher winding costs at least `7π/2`
   (`isWindingOne_of_reinhardtCost_lt`, `SmoothedPolygons/Ch6/Winding.lean`), more than the
   smoothed octagon, and the converse holds for winding number one
   (`exists_isBalancedPair_of_isReinhardtAdmissible`). Together with Theorem 5.0.2:
   `IsReinhardtAdmissible.forall_mem_truncatedStarDomain`.
2. *The cut-off.* A minimizer of the cut-off problem need not be a Reinhardt trajectory (`ψ`
   changes the dynamics outside `𝔥**`). Repair: impose the closed state constraint `z ∈ 𝔥**`, as
   the book's "we may assume that `z` lies in the compact set `𝔥**`" says, and use Filippov's
   theorem with a state constraint (`ControlSystem.exists_optimal_constrained`,
   `OptimalControl/ODE/StateConstraint.lean`; same proof as Theorem 6.1.1).
3. *Boundary conditions.* `X(0)` is free and the endpoints are coupled (`g(0) = I`, `g(t_f) = R`,
   `X(t_f) = R⁻¹X(0)R`), while Theorem 6.1.1 fixes the initial point. Repair: the same theorem with
   a compact set of initial points and a closed endpoint relation.
4. *Time bound.* Lemma 4.3.1 assumes a minimizer. Repair: the cost density `-(3/2)⟨J, X⟩` is at
   least `3` on star states (`three_mul_le_reinhardtCost`, the argument of Lemma 4.3.1 stated for
   every state trajectory), so every competitor cheaper than the smoothed octagon (`< π`) has
   `t_f < π/3`.
5. *Reinhardt's existence theorem* (TeX 4569–4572) concerns `K_min`, not the control problem; the
   argument does not use it (see `SmoothedPolygons/Ch6/WorstDisk.lean` for the identification).

## Proof of `exists_isReinhardtMinimizer`

On the matrix system of Layer 1 (`MatrixState`, `matrixField`, `matrixCost`, `controlSimplex`;
`SmoothedPolygons/Ch6/MatrixSystem.lean`), with `C` from `exists_bound_of_forall_mem_truncated`:

* state constraint `S = {q | det (stateG q) = 1, |(stateG q)ᵢⱼ| ≤ C, stateX q ∈ Φ(𝔥**)}`,
  compact (closed, inside a box times the compact `Φ(𝔥**)`: `isCompact_truncatedStarDomain`, `Φ`
  continuous on `y > 0`) and inside `matrixDomain`, on which `matrixField` and `matrixCost` are
  continuous (`isC1On_matrixField`, `isC1On_matrixCost`); so the velocities are bounded on the
  compact `S × U_T`. Initial set `K₀ = S` (compact); endpoint relation `N = matrixEndpoints`, the
  zero set of the continuous `matrixBoundary` (closed); window `[0, π/3]`;
* convexity of the extended velocity sets: `convex_image_matrixField` (Lemma 6.1.2 transported by
  the tangent map of `Φ`, Lemma 4.5.2; the cost does not depend on `u`);
* the class is nonempty: the smoothed octagon's trajectory (`smoothedPolygonDisk_spec`, admissible
  by Theorem 7.5.6) costs the area of the smoothed octagon, so it lies in `𝔥**` with `t_f < π/3`
  (`IsReinhardtAdmissible.forall_mem_truncatedStarDomain`: Theorem 5.0.2 applied to its own disk;
  `three_mul_le_reinhardtCost`, cost `< π`), and `|g| ≤ C`;
* `ControlSystem.exists_optimal_constrained` gives a minimizer `(τ, u, q)` of the constrained
  problem; `τ > 0` since `stateG q(0) = I ≠ R`; it projects to a Reinhardt-admissible trajectory
  (`isReinhardtAdmissible_of_mem_matrixEndpoints`), of cost the constrained minimum
  (`cost_matrixCost`);
* global minimality: a competitor costlier than the octagon costs more than the constrained minimum
  (the octagon is in the class); one at most as costly lies in `𝔥**` with `t_f < π/3`
  (`IsReinhardtAdmissible.forall_mem_truncatedStarDomain`) and has `|g| ≤ C`, so it is in the class
  (`IsStateTrajectory.isAdmissibleIn_matrix`).

Departure from the book (besides the repairs): the book applies Filippov's theorem to the
half-plane system `(g, z)` (Problem 4.5.1), the formalization to the matrix system `(g, X)` of
Layer 1, whose admissible pairs are already translated to Reinhardt trajectories; the convexity is
Lemma 6.1.2 carried over by `Φ`.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix

/-! ### `Φ(𝔥**)` -/

/-- The coordinates `slCoords (Φ(z))` are continuous on the upper half-plane. -/
private lemma ex_continuousOn_slCoords_Φ :
    ContinuousOn (fun z : ℝ × ℝ ↦ slCoords (Φ z.1 z.2)) {z | 0 < z.2} := by
  have hy : ∀ z ∈ {z : ℝ × ℝ | 0 < z.2}, z.2 ≠ 0 := fun z hz ↦ ne_of_gt hz
  refine continuousOn_pi.2 fun k ↦ ?_
  fin_cases k
  · exact continuousOn_fst.div continuousOn_snd hy
  · exact ((continuousOn_fst.pow 2).add (continuousOn_snd.pow 2)).neg.div continuousOn_snd hy
  · exact continuousOn_const.div continuousOn_snd hy

/-- The coordinates of the points of `Φ(𝔥**)`. -/
private noncomputable def ex_Kx : Set (Fin 3 → ℝ) :=
  (fun z : ℝ × ℝ ↦ slCoords (Φ z.1 z.2)) '' truncatedStarDomain

/-- `Φ(𝔥**)` is compact (`isCompact_truncatedStarDomain`, `Φ` continuous on `y > 0`). -/
private lemma ex_isCompact_Kx : IsCompact ex_Kx :=
  isCompact_truncatedStarDomain.image_of_continuousOn
    (ex_continuousOn_slCoords_Φ.mono fun _ hz ↦ hz.1.1)

/-- `Φ(z)` is traceless. -/
private lemma ex_trace_Φ (x y : ℝ) : (Φ x y).trace = 0 := by
  simp [Φ, Matrix.trace_fin_two, neg_div]

/-- The entries of `Φ` are bounded on `𝔥**`. -/
private lemma ex_exists_bound_Φ :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ truncatedStarDomain, ∀ i j, |Φ z.1 z.2 i j| ≤ B := by
  obtain ⟨B, hB⟩ := ex_isCompact_Kx.isBounded.exists_norm_le
  refine ⟨max B 0, le_max_right _ _, fun z hz i j ↦ ?_⟩
  have hk : ∀ k, |slCoords (Φ z.1 z.2) k| ≤ max B 0 := fun k ↦ by
    have h1 := norm_le_pi_norm (slCoords (Φ z.1 z.2)) k
    rw [Real.norm_eq_abs] at h1
    exact (h1.trans (hB _ ⟨z, hz, rfl⟩)).trans (le_max_left _ _)
  rw [← slMatrix_slCoords (ex_trace_Φ z.1 z.2)]
  fin_cases i <;> fin_cases j
  · simpa [slMatrix] using hk 0
  · simpa [slMatrix] using hk 1
  · simpa [slMatrix] using hk 2
  · simpa [slMatrix] using hk 0

/-! ### Gronwall's bound on `g` -/

/-- **Gronwall's bound on `g`** (§6.1, TeX 4583–4586, citing App. A.1): there is a constant `C`
bounding the entries of `g` along every state trajectory with `g(0) = I`, `T ≤ π/3` and
`X(t) ∈ Φ(𝔥**)`.

Proof: the entries of `X = Φ(z)` are bounded by some `B` on the compact `𝔥**`; with
`φ = ∑ᵢⱼ |gᵢⱼ|`, `g = I + ∫ gX` gives `φ(t) ≤ 4 + 4B ∫₀ᵗ φ`, and Gronwall's inequality
(`ControlSystem.le_mul_exp_of_le_add_integral`) gives `φ(t) ≤ 4 e^{4Bt} ≤ 4 e^{4Bπ/3}`. -/
theorem exists_bound_of_forall_mem_truncated :
    ∃ C : ℝ, ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsStateTrajectory T u g X →
      g 0 = 1 → T ≤ Real.pi / 3 → (∀ t ∈ Icc 0 T, ∃ z ∈ truncatedStarDomain, X t = Φ z.1 z.2) →
      ∀ t ∈ Icc 0 T, ∀ i j, |g t i j| ≤ C := by
  obtain ⟨B, hB0, hB⟩ := ex_exists_bound_Φ
  refine ⟨4 * Real.exp (4 * B * (Real.pi / 3)), ?_⟩
  intro T u g X h hg0 hT hX t ht i j
  obtain ⟨hTpos, -, -, -, hgI, -⟩ := h
  have hgc : ContinuousOn g (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hgI
  have hgij : ∀ i j, ContinuousOn (fun s ↦ g s i j) (Icc 0 T) := fun i j ↦
    continuousOn_pi.1 (continuousOn_pi.1 hgc i) j
  set φ : ℝ → ℝ := fun s ↦ |g s 0 0| + |g s 0 1| + |g s 1 0| + |g s 1 1| with hφ
  have hφc : ContinuousOn φ (Icc 0 T) :=
    ((((hgij 0 0).abs).add (hgij 0 1).abs).add (hgij 1 0).abs).add (hgij 1 1).abs
  have hφ0 : ∀ s ∈ Icc 0 T, 0 ≤ φ s := fun s _ ↦ by positivity
  have hle : ∀ s i j, |g s i j| ≤ φ s := by
    intro s i j
    have := abs_nonneg (g s 0 0); have := abs_nonneg (g s 0 1)
    have := abs_nonneg (g s 1 0); have := abs_nonneg (g s 1 1)
    fin_cases i <;> fin_cases j <;> simp only [hφ, Fin.zero_eta, Fin.mk_one] <;> linarith
  -- `|(gX)ᵢⱼ| ≤ B φ` along the trajectory
  have hgX : ∀ s ∈ Icc 0 T, ∀ i j, |(g s * X s) i j| ≤ B * φ s := by
    intro s hs i j
    obtain ⟨z, hzS, hXz⟩ := hX s hs
    have hXb : ∀ k l, |X s k l| ≤ B := fun k l ↦ hXz ▸ hB z hzS k l
    have := abs_nonneg (g s 0 0); have := abs_nonneg (g s 0 1)
    have := abs_nonneg (g s 1 0); have := abs_nonneg (g s 1 1)
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    calc |g s i 0 * X s 0 j + g s i 1 * X s 1 j| ≤ |g s i 0| * B + |g s i 1| * B := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;>
            exact mul_le_mul_of_nonneg_left (hXb _ _) (abs_nonneg _)
      _ ≤ B * φ s := by
          fin_cases i <;> simp only [hφ, Fin.zero_eta, Fin.mk_one] <;> nlinarith
  -- `φ(s) ≤ 4 + 4B ∫₀ˢ φ`
  have hint : ∀ s ∈ Icc 0 T, φ s ≤ 4 + 4 * B * ∫ r in (0 : ℝ)..s, φ r := by
    intro s hs
    have hsub : uIcc 0 s ⊆ uIcc 0 T := by
      rw [uIcc_of_le hTpos.le, uIcc_of_le hs.1]; exact Icc_subset_Icc_right hs.2
    have hφs : IntervalIntegrable φ volume 0 s :=
      (hφc.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1
    have hentry : ∀ i j, |g s i j| ≤ 1 + B * ∫ r in (0 : ℝ)..s, φ r := by
      intro i j
      have hI : IntervalIntegrable (fun r ↦ (g r * X r) i j) volume 0 s :=
        (hgI i j).1.mono_set hsub
      rw [(hgI i j).2 s hs, hg0]
      calc |(1 : Mat2) i j + ∫ r in (0 : ℝ)..s, (g r * X r) i j|
          ≤ |(1 : Mat2) i j| + |∫ r in (0 : ℝ)..s, (g r * X r) i j| := abs_add_le _ _
        _ ≤ 1 + ∫ r in (0 : ℝ)..s, B * φ r := by
          gcongr
          · rw [Matrix.one_apply]; split_ifs <;> simp
          · refine (intervalIntegral.abs_integral_le_integral_abs hs.1).trans ?_
            exact intervalIntegral.integral_mono_on hs.1 hI.abs (hφs.const_mul B)
              fun r hr ↦ hgX r ⟨hr.1, hr.2.trans hs.2⟩ i j
        _ = 1 + B * ∫ r in (0 : ℝ)..s, φ r := by rw [intervalIntegral.integral_const_mul]
    have := hentry 0 0; have := hentry 0 1; have := hentry 1 0; have := hentry 1 1
    simp only [hφ] at *
    linarith
  -- Gronwall's inequality
  have hG := ControlSystem.le_mul_exp_of_le_add_integral (by positivity : (0 : ℝ) ≤ 4 * B) hφc
    hφ0 hint t ht
  calc |g t i j| ≤ φ t := hle t i j
    _ ≤ 4 * Real.exp (4 * B * (t - 0)) := hG
    _ ≤ 4 * Real.exp (4 * B * (Real.pi / 3)) := by
        have : 4 * B * (t - 0) ≤ 4 * B * (Real.pi / 3) := by nlinarith [ht.1, ht.2]
        have := Real.exp_le_exp.2 this
        linarith

/-! ### Convexity -/

/-- `[Y_z(f(z, u)), Φ(z)] = [P_u, Φ(z)]` at every `z ∈ 𝔥*`: the tangent map of `Φ` sends the
half-plane velocity `f(z, u)` of Problem 4.5.1 to the velocity `[P_u, X]` of `X = Φ(z)`
(Lemma 4.5.2, `eqn:tangent-map-f1f2`, as an identity at one point). -/
private lemma ex_tangentLift_halfPlaneField {x y : ℝ} (hz : (x, y) ∈ starDomain)
    {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) :
    tangentLift x y (halfPlaneF₁ x y u) (halfPlaneF₂ x y u) * Φ x y -
        Φ x y * tangentLift x y (halfPlaneF₁ x y u) (halfPlaneF₂ x y u) =
      controlP u (Φ x y) * Φ x y - Φ x y * controlP u (Φ x y) := by
  have hy : 0 < y := hz.1
  have hy0 : y ≠ 0 := hy.ne'
  have hXstar := (theorem4_4_1 x y hy).2 hz
  have hneg := (lemma3_3_4 (Φ x y) hXstar.1).1 hXstar.2.2 u hu
  have hZ11 : controlMatrix u 1 1 = -controlMatrix u 0 0 := by simp [controlMatrix]; ring
  have htf : traceForm (controlMatrix u) (Φ x y) =
      (2 * controlMatrix u 0 0 * x + controlMatrix u 0 1 - controlMatrix u 1 0 * x ^ 2 -
        controlMatrix u 1 0 * y ^ 2) / y := by
    rw [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two, hZ11]
    simp only [Φ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    ring
  have hden : 2 * controlMatrix u 0 0 * x + controlMatrix u 0 1 - controlMatrix u 1 0 * x ^ 2 -
      controlMatrix u 1 0 * y ^ 2 ≠ 0 := by
    intro h; rw [htf, h, zero_div] at hneg; exact lt_irrefl _ hneg
  have hZ : controlMatrix u = !![controlMatrix u 0 0, controlMatrix u 0 1;
      controlMatrix u 1 0, -controlMatrix u 0 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hZ11]
  rw [controlP, htf, hZ]
  simp only [halfPlaneF₁, halfPlaneF₂]
  generalize controlMatrix u 0 0 = a at hden ⊢
  generalize controlMatrix u 0 1 = b at hden ⊢
  generalize controlMatrix u 1 0 = c at hden ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tangentLift, Φ] <;> field_simp <;> ring

/-- **Convex velocity sets of the matrix system** (Lemma 6.1.2 in the matrix coordinates): at a
state with `X = Φ(z)`, `z ∈ 𝔥*`, the velocity set of `(g, X)' = (gX, [P, X])` extended by the cost
`-(3/2)⟨J, X⟩` is convex. It is the image of the half-plane velocity set `f(z, U_T)` of
Lemma 6.1.2 under the linear map `v ↦ (gX, TΦ_z v, -(3/2)⟨J, X⟩)` (Lemma 4.5.2: `TΦ(f(z, u))` is
`[P, X]`). -/
theorem convex_image_matrixField {q : MatrixState}
    (hq : ∃ z ∈ starDomain, stateX q = Φ z.1 z.2) :
    Convex ℝ ((fun u ↦ (matrixField q u, matrixCost q u)) '' controlSimplex) := by
  obtain ⟨⟨x, y⟩, hz, hX⟩ := hq
  -- the affine map `v ↦ (gX, TΦ_z v, -(3/2)⟨J, X⟩)`
  let A : (Fin 2 → ℝ) → MatrixState × ℝ := fun v ↦
    (((fun i j ↦ (stateG q * stateX q) i j),
      slCoords (tangentLift x y (v 0) (v 1) * Φ x y - Φ x y * tangentLift x y (v 0) (v 1))),
      matrixCost q 0)
  have key : ∀ u ∈ controlSimplex,
      (matrixField q u, matrixCost q u) = A (halfPlaneField x y u) := by
    intro u hu
    simp only [A, halfPlaneField, Matrix.cons_val_zero, Matrix.cons_val_one,
      ex_tangentLift_halfPlaneField hz hu, matrixField, matrixCost, hX]
  have haff : ∀ (v w : Fin 2 → ℝ) (a b : ℝ), a + b = 1 →
      A (a • v + b • w) = a • A v + b • A w := by
    intro v w a b hab
    obtain rfl : b = 1 - a := by linarith
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · funext i j
      simp only [A, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · funext k
      fin_cases k <;>
        simp [A, slCoords, tangentLift, Φ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    · simp only [A, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      ring
  rintro _ ⟨u₁, hu₁, rfl⟩ _ ⟨u₂, hu₂, rfl⟩ a b ha hb hab
  obtain ⟨u₃, hu₃, h₃⟩ := (lemma6_1_2 x y hz).2.1 ⟨u₁, hu₁, rfl⟩ ⟨u₂, hu₂, rfl⟩ ha hb hab
  refine ⟨u₃, hu₃, ?_⟩
  dsimp only
  rw [key u₃ hu₃, key u₁ hu₁, key u₂ hu₂, ← haff _ _ _ _ hab, h₃]

/-! ### Competitors at most as costly as the smoothed octagon -/

/-- A star state is `Φ(z)` for some `z ∈ 𝔥*` (Lemmas 4.1.1, 4.2.1 and Theorem 4.4.1). -/
private lemma ex_exists_starDomain {X : Mat2} (hX : IsStarState X) :
    ∃ z ∈ starDomain, X = Φ z.1 z.2 := by
  have hmem : X ∈ adjointOrbit J := by
    rw [← lemma4_1_1]
    exact ⟨hX.1, hX.2.1, poly_traceForm_J_neg hX⟩
  obtain ⟨z, -, hz⟩ := lemma4_2_1.surjOn hmem
  have hX' : X = Φ z.re z.im := by rw [← hz, ΦH]
  exact ⟨(z.re, z.im), (theorem4_4_1 _ _ z.im_pos).1 (hX' ▸ hX), hX'⟩

/-- **The smoothed octagon** (Theorem 7.5.6 and the example before it, `smoothedPolygonDisk_spec`):
its trajectory is admissible for Problem 3.6.2, its cost is the area of the smoothed octagon, and
that area is less than `π`. -/
private lemma ex_octagon :
    IsReinhardtAdmissible (tf 1) (polygonControl 1) (smoothedPolygonG 1) (smoothedPolygonX 1) ∧
      reinhardtCost (tf 1) (smoothedPolygonX 1) = volume.real (smoothedPolygonDisk 1) ∧
      volume.real (smoothedPolygonDisk 1) < Real.pi := by
  obtain ⟨hst, hg0, hX0, -, -, -, -, hvol⟩ := smoothedPolygonDisk_spec 1 le_rfl
  obtain ⟨-, Λ₁, ΛR, lam, hP⟩ := (theorem7_5_6 1 le_rfl).2 _ _ hst hg0 hX0
  have hlt := (example7_5_smoothedOctagon.2.2.2.2 _ _ hst hg0 hX0).2.2.1
  have hpos : 0 ≤ reinhardtCost (tf 1) (smoothedPolygonX 1) := by
    have := three_mul_le_reinhardtCost hst
    linarith [hst.1]
  have hreal : volume.real (smoothedPolygonDisk 1) = reinhardtCost (tf 1) (smoothedPolygonX 1) := by
    rw [measureReal_def, hvol, ENNReal.toReal_ofReal hpos]
  exact ⟨⟨hst, hg0, hP.2.2.1, hP.2.2.2.1⟩, hreal.symm, hreal ▸ hlt⟩

/-- **Every competitor at most as costly as the smoothed octagon lies in `𝔥**`** (§6.1, TeX 4579:
"By Theorem 5.0.2, we may assume that `z` lies in the compact set `𝔥**`"). An admissible trajectory
of the Reinhardt control problem with cost at most the area of the smoothed octagon has
`t_f < π/3`, and `X(t) = Φ(z)` with `z ∈ 𝔥**` for all `t ∈ [0, t_f]`. (Proof: winding number one
by `isWindingOne_of_reinhardtCost_lt`, the balanced disk of
`exists_isBalancedPair_of_isReinhardtAdmissible`, and Theorem 5.0.2, `theorem5_0_2`.) -/
theorem IsReinhardtAdmissible.forall_mem_truncatedStarDomain {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsReinhardtAdmissible T u g X)
    (hc : reinhardtCost T X ≤ volume.real (smoothedPolygonDisk 1)) :
    T < Real.pi / 3 ∧ ∀ t ∈ Icc 0 T, ∃ z ∈ truncatedStarDomain, X t = Φ z.1 z.2 := by
  obtain ⟨-, -, hoct⟩ := ex_octagon
  have hT3 := three_mul_le_reinhardtCost h.1
  refine ⟨by linarith, ?_⟩
  -- winding number one, since the cost is less than `π < 7π/2`
  have hw : IsWindingOne T g := isWindingOne_of_reinhardtCost_lt h (by linarith [Real.pi_pos])
  -- the balanced disk bounded by the trajectory (the converse of Problem 3.6.2)
  obtain ⟨K, σ, G, -, hGX, hstar, hσ, hshift, hKσ, -, -⟩ :=
    exists_isBalancedPair_of_isReinhardtAdmissible h hw
  set X' : ℝ → Mat2 := fun t ↦ (G t)⁻¹ * derivEntrywise G t with hX'
  choose z hz using fun t ↦ ex_exists_starDomain (hstar t)
  have hcost : reinhardtCost T X' = reinhardtCost T X := by
    simp only [reinhardtCost]
    congr 1
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le h.1.1.le] at ht
    simp only [hX', hGX t ht]
  intro t ht
  by_contra hout
  have hzout : z t ∉ truncatedStarDomain := fun hm ↦
    hout ⟨z t, hm, by rw [← hGX t ht]; exact (hz t).2⟩
  -- Theorem 5.0.2: the cost would exceed the area of the smoothed octagon
  have := (theorem5_0_2 hKσ hσ hshift (fun _ ↦ rfl) hz hzout).1
  rw [hcost] at this
  linarith

/-! ### The constrained problem -/

/-- The state constraint of the constrained matrix problem: `det g = 1`, `|gᵢⱼ| ≤ C` and
`X ∈ Φ(𝔥**)`. -/
private def ex_S (C : ℝ) : Set MatrixState :=
  {q | (stateG q).det = 1 ∧ (∀ i j, |stateG q i j| ≤ C) ∧ q.2 ∈ ex_Kx}

/-- `X = Φ(z)` with `z ∈ 𝔥**` on the state constraint. -/
private lemma ex_S_stateX {C : ℝ} {q : MatrixState} (hq : q ∈ ex_S C) :
    ∃ z ∈ truncatedStarDomain, stateX q = Φ z.1 z.2 := by
  obtain ⟨-, -, z, hz, hzq⟩ := hq
  exact ⟨z, hz, by rw [stateX, ← hzq, slMatrix_slCoords (ex_trace_Φ _ _)]⟩

/-- The state constraint lies in `GL₂⁺(ℝ) × C`. -/
private lemma ex_S_subset_matrixDomain (C : ℝ) : ex_S C ⊆ matrixDomain := by
  intro q hq
  obtain ⟨z, hz, hX⟩ := ex_S_stateX hq
  obtain ⟨-, -, h0, h1, h2⟩ := (theorem4_4_1 z.1 z.2 hz.1.1).2 hz.1
  refine ⟨by rw [hq.1]; exact one_pos, ?_, ?_, ?_⟩ <;> rw [hX] <;> assumption

/-- The state constraint is compact: closed, inside the box `|gᵢⱼ| ≤ C` times `Φ(𝔥**)`. -/
private lemma ex_isCompact_S (C : ℝ) : IsCompact (ex_S C) := by
  have hbox : IsCompact ((Set.pi univ fun _ : Fin 2 ↦ Set.pi univ fun _ : Fin 2 ↦ Icc (-C) C) ×ˢ
      ex_Kx) :=
    (isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc).prod ex_isCompact_Kx
  refine hbox.of_isClosed_subset ?_ ?_
  · have hdet : Continuous fun q : MatrixState ↦ (stateG q).det := by
      simp only [stateG, Matrix.det_fin_two, Matrix.of_apply]; fun_prop
    have e : ex_S C = {q : MatrixState | (stateG q).det = 1} ∩
        ((⋂ i, ⋂ j, {q : MatrixState | |q.1 i j| ≤ C}) ∩ Prod.snd ⁻¹' ex_Kx) := by
      ext q; simp [ex_S, stateG]
    rw [e]
    refine (isClosed_eq hdet continuous_const).inter
      ((isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ ?_).inter
        (ex_isCompact_Kx.isClosed.preimage continuous_snd))
    exact isClosed_le (by fun_prop) continuous_const
  · rintro q ⟨-, hg, hx⟩
    exact ⟨fun i _ j _ ↦ abs_le.1 (hg i j), hx⟩

/-- The boundary condition of the matrix system is closed. -/
private lemma ex_isClosed_matrixEndpoints : IsClosed matrixEndpoints :=
  isClosed_eq contDiff_matrixBoundary.continuous continuous_const

/-- The cost of the matrix pair of a state trajectory is its Reinhardt cost. -/
private lemma ex_integral_matrixCost {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) :
    ∫ t in (0 : ℝ)..T, matrixCost (toMatrixState (g t) (X t)) (u t) = reinhardtCost T X := by
  change Pontryagin.cost matrixCost T u (fun t ↦ toMatrixState (g t) (X t)) = _
  rw [cost_matrixCost]
  simp only [reinhardtCost]
  congr 1
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le h.1.le] at ht
  simp only [stateX_toMatrixState _ (h.2.2.2.1 t ht).2.1]

/-- **The competitors of the constrained problem.** An admissible trajectory of Problem 3.6.2 at
most as costly as the smoothed octagon gives an admissible pair of the matrix system on
`[0, T]`, `T ≤ π/3`, in the state constraint `ex_S C` (with `C` from Gronwall's bound), satisfying
the boundary condition. -/
private lemma ex_mem_class {C : ℝ}
    (hC : ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsStateTrajectory T u g X →
      g 0 = 1 → T ≤ Real.pi / 3 → (∀ t ∈ Icc 0 T, ∃ z ∈ truncatedStarDomain, X t = Φ z.1 z.2) →
      ∀ t ∈ Icc 0 T, ∀ i j, |g t i j| ≤ C)
    {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (h : IsReinhardtAdmissible T u g X)
    (hc : reinhardtCost T X ≤ volume.real (smoothedPolygonDisk 1)) :
    T ∈ Icc 0 (Real.pi / 3) ∧
      ControlSystem.IsAdmissible matrixField controlSimplex (toMatrixState (g 0) (X 0)) T u
        (fun t ↦ toMatrixState (g t) (X t)) ∧
      toMatrixState (g 0) (X 0) ∈ ex_S C ∧
      (∀ t ∈ Icc 0 T, toMatrixState (g t) (X t) ∈ ex_S C) ∧
      (toMatrixState (g 0) (X 0), toMatrixState (g T) (X T)) ∈ matrixEndpoints := by
  obtain ⟨hTlt, hz⟩ := h.forall_mem_truncatedStarDomain hc
  have hst := h.1
  have hg := hC T u g X hst h.2.1 hTlt.le hz
  have hmem : ∀ t ∈ Icc 0 T, toMatrixState (g t) (X t) ∈ ex_S C := by
    intro t ht
    obtain ⟨z, hzS, hXz⟩ := hz t ht
    exact ⟨(hst.2.2.2.1 t ht).1, fun i j ↦ hg t ht i j, z, hzS, by
      change slCoords (Φ z.1 z.2) = slCoords (X t)
      rw [hXz]⟩
  exact ⟨⟨hst.1.le, hTlt.le⟩, hst.isAdmissibleIn_matrix.1, hmem 0 ⟨le_rfl, hst.1.le⟩, hmem,
    h.mem_matrixEndpoints⟩

/-- **Existence of an optimal control** (§6.1, `sec:existence-opt-control`, TeX 4520–4600): the
Reinhardt control problem (Problem 3.6.2) has a global minimizer. -/
theorem exists_isReinhardtMinimizer :
    ∃ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsReinhardtMinimizer T u g X := by
  obtain ⟨C, hC⟩ := exists_bound_of_forall_mem_truncated
  have hSc := ex_isCompact_S C
  have hSdom := ex_S_subset_matrixDomain C
  -- continuity on `S × U_T` (`S ⊆ GL₂⁺(ℝ) × C`), and bounded velocities on the compact `S × U_T`
  have hFc : ContinuousOn (fun p : MatrixState × (Fin 3 → ℝ) ↦ matrixField p.1 p.2)
      (ex_S C ×ˢ controlSimplex) :=
    isC1On_matrixField.continuousOn.mono (prod_mono hSdom subset_rfl)
  have hφc : ContinuousOn (fun p : MatrixState × (Fin 3 → ℝ) ↦ matrixCost p.1 p.2)
      (ex_S C ×ˢ controlSimplex) :=
    isC1On_matrixCost.continuousOn.mono (prod_mono hSdom subset_rfl)
  obtain ⟨M, hM⟩ := (hSc.prod isCompact_controlSimplex).exists_bound_of_continuousOn hFc
  -- convex extended velocity sets (Lemma 6.1.2)
  have hconv : ∀ q ∈ ex_S C,
      Convex ℝ ((fun w ↦ (matrixField q w, matrixCost q w)) '' controlSimplex) := by
    intro q hq
    obtain ⟨z, hz, hX⟩ := ex_S_stateX hq
    exact convex_image_matrixField ⟨z, hz.1, hX⟩
  -- the smoothed octagon is a competitor
  obtain ⟨hoct, hoctc, -⟩ := ex_octagon
  obtain ⟨hT₀, hadm₀, h0₀, hS₀, hN₀⟩ := ex_mem_class hC hoct hoctc.le
  -- Filippov's theorem with a state constraint
  obtain ⟨τ, hτ, u, x, hadm, -, hS, hN, hmin⟩ :=
    ControlSystem.exists_optimal_constrained (F := matrixField) (φ := matrixCost)
      (N := matrixEndpoints) isCompact_controlSimplex hSc.isClosed hSc
      ex_isClosed_matrixEndpoints hFc hφc hconv (fun q hq w hw ↦ hM (q, w) ⟨hq, hw⟩) le_rfl
      ⟨tf 1, hT₀, polygonControl 1, _, hadm₀, h0₀, hS₀, hN₀⟩
  -- `τ > 0`: `g(0) = I ≠ R = g(τ)`
  have hτ0 : 0 < τ := by
    refine lt_of_le_of_ne hτ.1 fun h0 ↦ ?_
    subst h0
    have hb : matrixBoundary (x 0, x 0) = 0 := hN
    simp only [matrixBoundary, Prod.mk_eq_zero] at hb
    have e1 := congrFun (congrFun hb.1 0) 0
    have e2 := congrFun hb.2.1 0
    simp [R] at e1 e2
    linarith
  have hR := isReinhardtAdmissible_of_mem_matrixEndpoints hτ0 ⟨hadm, fun t ht ↦ hSdom (hS t ht)⟩
    hN
  refine ⟨τ, u, _, _, hR, fun T' u' g' X' h' ↦ ?_⟩
  rw [← cost_matrixCost τ u x]
  by_cases hc : reinhardtCost T' X' ≤ volume.real (smoothedPolygonDisk 1)
  -- a competitor at most as costly as the octagon is a competitor of the constrained problem
  · obtain ⟨hT', hadm', h0', hS', hN'⟩ := ex_mem_class hC h' hc
    calc Pontryagin.cost matrixCost τ u x
        ≤ ∫ t in (0 : ℝ)..T', matrixCost (toMatrixState (g' t) (X' t)) (u' t) :=
          hmin T' hT' u' _ hadm' h0' hS' hN'
      _ = reinhardtCost T' X' := ex_integral_matrixCost h'.1
  -- a costlier one costs more than the octagon, a competitor of the constrained problem
  · replace hc := not_le.1 hc
    calc Pontryagin.cost matrixCost τ u x
        ≤ ∫ t in (0 : ℝ)..tf 1,
            matrixCost (toMatrixState (smoothedPolygonG 1 t) (smoothedPolygonX 1 t))
              (polygonControl 1 t) :=
          hmin _ hT₀ _ _ hadm₀ h0₀ hS₀ hN₀
      _ = reinhardtCost (tf 1) (smoothedPolygonX 1) := ex_integral_matrixCost hoct.1
      _ ≤ reinhardtCost T' X' := hoctc.trans_le hc.le

/-- A global minimizer of the Reinhardt control problem costs at most the smoothed octagon, has
terminal time `t_f < π/3`, and its trajectory lies in `𝔥**` (§6.1 with Theorem 5.0.2). -/
theorem IsReinhardtMinimizer.forall_mem_truncatedStarDomain {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsReinhardtMinimizer T u g X) :
    reinhardtCost T X ≤ volume.real (smoothedPolygonDisk 1) ∧ T < Real.pi / 3 ∧
      ∀ t ∈ Icc 0 T, ∃ z ∈ truncatedStarDomain, X t = Φ z.1 z.2 := by
  obtain ⟨hadm, hcost, -⟩ := ex_octagon
  have hc : reinhardtCost T X ≤ volume.real (smoothedPolygonDisk 1) :=
    hcost ▸ h.2 _ _ _ _ hadm
  exact ⟨hc, lemma4_3_1 T u g X h, (h.1.forall_mem_truncatedStarDomain hc).2⟩

/-- **A global minimizer exists, and it is a Pontryagin extremal** (§6.1 and §6.2): the
Reinhardt control problem has a global minimizer (`exists_isReinhardtMinimizer`), and every global
minimizer lifts to a Pontryagin extremal
(`exists_isPontryaginExtremal_of_isReinhardtMinimizer`). This is the premise of Proposition 8.1.3
(TeX 6791). -/
theorem exists_isReinhardtMinimizer_isPontryaginExtremal :
    ∃ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ),
      IsReinhardtMinimizer T u g X ∧ IsPontryaginExtremal T u g X Λ₁ ΛR lam := by
  obtain ⟨T, u, g, X, h⟩ := exists_isReinhardtMinimizer
  obtain ⟨Λ₁, ΛR, lam, hP⟩ := exists_isPontryaginExtremal_of_isReinhardtMinimizer h
  exact ⟨T, u, g, X, Λ₁, ΛR, lam, h, hP⟩

end SmoothedPolygons
