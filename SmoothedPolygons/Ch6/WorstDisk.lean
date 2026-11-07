module

public import SmoothedPolygons.Ch6.Existence
public import SmoothedPolygons.Ch2.Boundary
public import SmoothedPolygons.Ch2.Density
public import SmoothedPolygons.Ch6.WdTrajectory

/-!
# The minimizer of the control problem and Reinhardt's `K_min`

§6.1 says (TeX 4569–4572) "Recall that Reinhardt has proved the existence of an optimal solution to
the Reinhardt problem", and the later chapters identify the global minimizer of the control
problem with Reinhardt's minimizer `K_min` (a centrally symmetric convex disk of least greatest
packing density, `IsWorstDisk`): Proposition 8.1.3 speaks of "the global solution of the
Reinhardt problem" (TeX 6786), and Theorem 16.3.1 (`thm:mahler`, TeX 12789–12795) concludes from
"the global minimizer of the Reinhardt optimal control problem is a bang-bang solution with
finitely many switches" that "the minimizer `K_min` of the Reinhardt problem is a finite-sided
smoothed polygon". The book does not prove the identification; Chapters 2–3 derive the control
problem from `K_min` (Problem 3.6.2: "The convex disks in `𝔎_bal` in circle representation arise
via the following optimal control problem"). Inventory, Part I §3.5, item 5.

What the later chapters need:

* `exists_isReinhardtMinimizer_of_isWorstDisk`: after a linear normalization, every `K_min` is the
  disk of a global minimizer of Problem 3.6.2 (so the second sentence of Theorem 16.3.1 follows
  from the first);
* `isWorstDisk_of_isReinhardtMinimizer`: conversely, the disk bounded by a global minimizer is a
  `K_min`, and `δ_min = cost/√12`.

Both rest on `exists_isReinhardtAdmissible_of_isWorstDisk` (the inventory's step B1): every
`K_min`, after a linear normalization, is a balanced disk in circle representation whose boundary
trajectory, parameterized with `det X = 1`, is admissible.

## Proofs

* `exists_isReinhardtAdmissible_of_isWorstDisk` (B1) assembles the formalized results of
  Chapters 2–3, each of which takes the multi-curve as a hypothesis; the multi-curve is produced in
  `SmoothedPolygons/Ch6/WdBoundaryParam.lean` and the trajectory in
  `SmoothedPolygons/Ch6/WdTrajectory.lean`:
  1. the linear normalization to circle representation (`wd_exists_normalize`; worst disks and
     critical hexagons are invariant under orientation-preserving linear maps,
     `bdy_isWorstLatticeDisk_image`, `bdy_isLeastAreaHexagon_image`);
  2. a balanced pair in circle representation (`wd_exists_balancedPair`): the arclength
     parameterization `σ₀` of the boundary, `C¹` because the support line is unique at each
     boundary point (Lemma 2.2.5); `σ_j` the edge midpoints of the critical hexagons (Lemma 2.2.7,
     `lemma2_2_7`); regularity and Lipschitz tangents (Lemmas 2.4.2, 2.4.3); the star and
     curvature conditions (Lemmas 2.4.5, 2.4.6);
  3. the reparameterization with `det X = 1` (`wd_exists_balancedPair_det_one`, Corollary 3.1.6,
     Proposition 3.1.9);
  4. the shift `σ_j(t + t_f) = σ_{j+1}(t)` (`wd_shift`; §3.5 takes it for granted);
  5. the admissibility (`wd_isReinhardtAdmissible`: Corollary 3.1.6, Proposition 3.1.9,
     Lemma 3.3.1, Theorem 3.4.2, the boundary conditions of §3.5) and the area formula `eqn_cost`.
* `exists_isReinhardtMinimizer_of_isWorstDisk`: the trajectory of B1 is admissible with cost
  `area(A K) = √12 δ_min` (E12, `greatestPackingDensity_of_isBalancedPair`; `A K` is again a worst
  disk); a competitor of cost `< 7π/2` has winding number one and bounds a balanced disk of area its
  cost (`isWindingOne_of_reinhardtCost_lt`, `exists_isBalancedPair_of_isReinhardtAdmissible`),
  whose density is at least `δ_min`; a competitor of cost `≥ 7π/2` costs more than the smoothed
  octagon (`area < π`), and `√12 δ_min ≤ area(K_oct)`.
* `isWorstDisk_of_isReinhardtMinimizer`: `area(K) = cost` (`eqn_cost`), `cost ≤ cost(K_min)` by
  minimality against the trajectory of a `K_min` (`rein_exists_worst`, B1), so
  `δ(K) = area(K)/√12 ≤ δ_min`. (The hypothesis `hcirc` is not needed.)
* `exists_isReinhardtMinimizer_isPontryaginExtremal_isWorstDisk`: as its docstring says.

This module is the bridge to Chapters 8 and 16 (Layer 3); it does not enter the existence proof.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix

/-! ### Helper lemmas -/

/-- The linear map `v ↦ A v` of an invertible matrix, as a continuous linear equivalence. -/
noncomputable def wd_linEquiv (A : Mat2) (hA : A.det ≠ 0) : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  (Matrix.toLinearEquiv' A
    (Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.2 hA))).toContinuousLinearEquiv

lemma wd_linEquiv_apply (A : Mat2) (hA : A.det ≠ 0) (v : Fin 2 → ℝ) :
    wd_linEquiv A hA v = A *ᵥ v := rfl

/-- **Worst disks are invariant under orientation-preserving linear maps** (Theorem 2.1.3 with the
invariance of the lattice packing density, `bdy_isWorstLatticeDisk_image`). -/
lemma wd_isWorstDisk_image {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) {A : Mat2}
    (hA : 0 < A.det) : IsWorstDisk ((fun v ↦ A *ᵥ v) '' K) := by
  have h := bdy_isWorstLatticeDisk_image (wd_linEquiv A hA.ne') hA
    (fun x y ↦ by simp only [wd_linEquiv_apply]; exact oct_det2_mulVec A x y)
    (ch2_isWorstLatticeDisk_iff_isWorstDisk.2 hK)
  have e : (wd_linEquiv A hA.ne') '' K = (fun v ↦ A *ᵥ v) '' K := by
    ext x; simp only [mem_image, wd_linEquiv_apply]
  rw [← e]
  exact ch2_isWorstLatticeDisk_iff_isWorstDisk.1 h

/-- Along a state trajectory, `g' = gX` at every interior time (FTC-1: `g` is the integral of the
continuous curve `gX`). -/
lemma wd_hasDerivAt_g {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAtEntrywise g (g t * X t) t := by
  obtain ⟨-, -, -, -, hgI, hXI⟩ := h
  have hgc := Matrix.continuousOn_of_eq_add_integral hgI
  have hXc := Matrix.continuousOn_of_eq_add_integral hXI
  have hc : ContinuousOn (fun s ↦ g s * X s) (Icc 0 T) := hgc.mul hXc
  exact Matrix.hasDerivAtEntrywise_of_eq_add_integral hgI ht
    (hc.continuousAt (Icc_mem_nhds ht.1 ht.2))

/-- The cost of a state trajectory is positive (`three_mul_le_reinhardtCost`). -/
lemma wd_reinhardtCost_pos {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) : 0 < reinhardtCost T X := by
  have := three_mul_le_reinhardtCost h
  linarith [h.1]

/-- A set whose measure is `ofReal c` with `c ≥ 0` has real measure `c`. -/
lemma wd_measureReal_eq {S : Set (Fin 2 → ℝ)} {c : ℝ} (hc : 0 ≤ c)
    (h : volume S = ENNReal.ofReal c) : volume.real S = c := by
  rw [measureReal_def, h, ENNReal.toReal_ofReal hc]

/-- `δ_min ≤ δ(K)` for every centrally symmetric convex disk. -/
lemma wd_minimaxDensity_le {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) :
    minimaxDensity ≤ greatestPackingDensity K :=
  csInf_le ⟨0, fun _ ⟨K', _, hd⟩ ↦ hd ▸ ch2_greatestPackingDensity_nonneg K'⟩ ⟨K, hK, rfl⟩

/-- The area of the smoothed octagon is less than `π` (the example before Theorem 7.5.6). -/
lemma wd_volume_octagon_lt : volume.real (smoothedPolygonDisk 1) < Real.pi := by
  obtain ⟨hst, hg0, hX0⟩ := smoothedPolygon_isStateTrajectory 1 le_rfl
  obtain ⟨-, -, -, -, h⟩ := example7_5_smoothedOctagon
  obtain ⟨-, -, hlt, -⟩ := h _ _ hst hg0 hX0
  rw [wd_measureReal_eq (wd_reinhardtCost_pos hst).le (smoothedPolygonDisk_volume 1 le_rfl)]
  exact hlt

/-- The density of a balanced disk whose area is the cost `c` of a trajectory is `c/√12`. -/
lemma wd_greatestPackingDensity_eq {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {T c : ℝ}
    (hKσ : IsBalancedPair K σ T) (hc : 0 ≤ c) (hvol : volume K = ENNReal.ofReal c) :
    greatestPackingDensity K = c / √12 := by
  rw [greatestPackingDensity_of_isBalancedPair hKσ, wd_measureReal_eq hc hvol]

/-- The minimax density is `c/√12` for the cost `c` of the boundary trajectory of a worst disk
given by step B1 (`exists_isReinhardtAdmissible_of_isWorstDisk`). -/
lemma wd_minimaxDensity_eq {K : Set (Fin 2 → ℝ)} {A : Mat2} {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (hK : IsWorstDisk K) (hA : 0 < A.det)
    (hKσ : IsBalancedPair ((fun v ↦ A *ᵥ v) '' K) σ T) (h : IsReinhardtAdmissible T u g X)
    (hvol : volume ((fun v ↦ A *ᵥ v) '' K) = ENNReal.ofReal (reinhardtCost T X)) :
    minimaxDensity = reinhardtCost T X / √12 := by
  rw [← (wd_isWorstDisk_image hK hA).2,
    wd_greatestPackingDensity_eq hKσ (wd_reinhardtCost_pos h.1).le hvol]

/-- **Step B1: a worst disk gives an admissible trajectory.** For every `K_min` (a centrally
symmetric convex disk of least greatest packing density), some linear image `A K_min`,
`det A > 0`, is a balanced disk in circle representation whose multi-curve `σ_j = g s_j*`, with
`σ_j(t + t_f) = σ_{j+1}(t)`, comes from an admissible trajectory `(g, X)` of Problem 3.6.2 of cost
`area(A K_min)` (Chapters 2–3; Problem 3.6.2, "The convex disks in `𝔎_bal` in circle
representation arise via the following optimal control problem"). -/
theorem exists_isReinhardtAdmissible_of_isWorstDisk {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) :
    ∃ (A : Mat2) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2),
      0 < A.det ∧ IsBalancedPair ((fun v ↦ A *ᵥ v) '' K) σ T ∧ IsCircleRepresentation σ ∧
      (∀ j t, σ j t = g t *ᵥ sixthRoot j) ∧ (∀ j t, σ j (t + T) = σ (j + 1) t) ∧
      IsReinhardtAdmissible T u g X ∧
      volume ((fun v ↦ A *ᵥ v) '' K) = ENNReal.ofReal (reinhardtCost T X) := by
  -- the linear normalization to circle representation
  obtain ⟨A, hA, v, hv, hvm⟩ := wd_exists_normalize hK
  have hK' := wd_isWorstDisk_image hK hA
  -- a balanced pair in circle representation (Lemma 2.2.7, Lemmas 2.4.2–2.4.6)
  obtain ⟨σ₀, tf, hbal₀, hc₀⟩ := wd_exists_balancedPair hK' hv hvm
  -- the parameterization with `det X = 1` (Proposition 3.1.9)
  obtain ⟨σ, T, g, hbal, hc, hg, hdet⟩ := wd_exists_balancedPair_det_one hbal₀ hc₀
  -- `σ_j(t + t_f) = σ_{j+1}(t)` (§3.5)
  have hshift := wd_shift hK' hbal hc hg hdet
  -- the trajectory is admissible (Corollary 3.1.6, Lemma 3.3.1, Theorem 3.4.2, §3.5)
  obtain ⟨u, hadm⟩ := wd_isReinhardtAdmissible hbal hc hg hdet hshift
  refine ⟨A, σ, T, u, g, _, hA, hbal, hc, hg, hshift, hadm, ?_⟩
  -- the area is the cost (`eqn:cost`)
  exact eqn_cost hbal g _ (fun j t _ ↦ hg j t) (fun t ht ↦ wd_hasDerivAt_g hadm.1 ht) hshift

/-- **Every `K_min` is the disk of a global minimizer of the control problem**
(`sec:existence-opt-control:kmin`, label of this formalization; the identification
used by Theorem 16.3.1, TeX 12793–12795, and by Proposition 8.1.3, TeX 6786): some linear image
`A K_min`, `det A > 0`, is a balanced disk in circle representation whose boundary trajectory is a
global minimizer of Problem 3.6.2. -/
theorem exists_isReinhardtMinimizer_of_isWorstDisk {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) :
    ∃ (A : Mat2) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2),
      0 < A.det ∧ IsBalancedPair ((fun v ↦ A *ᵥ v) '' K) σ T ∧ IsCircleRepresentation σ ∧
      (∀ j t, σ j t = g t *ᵥ sixthRoot j) ∧ (∀ j t, σ j (t + T) = σ (j + 1) t) ∧
      IsReinhardtMinimizer T u g X := by
  obtain ⟨A, σ, T, u, g, X, hA, hKσ, hcirc, hσ, hshift, hadm, hvol⟩ :=
    exists_isReinhardtAdmissible_of_isWorstDisk hK
  refine ⟨A, σ, T, u, g, X, hA, hKσ, hcirc, hσ, hshift, hadm, fun T' u' g' X' h' ↦ ?_⟩
  -- `δ_min = cost/√12` (E12; worst disks are invariant under linear maps)
  have hδ := wd_minimaxDensity_eq hK hA hKσ hadm hvol
  have h12 : (0 : ℝ) < √12 := by positivity
  by_cases hc' : reinhardtCost T' X' < 7 * Real.pi / 2
  · -- a cheaper competitor has winding number one and bounds a balanced disk of area its cost,
    -- whose density is at least `δ_min`
    obtain ⟨K', σ', G, -, -, -, -, -, hbal', -, hvol'⟩ :=
      exists_isBalancedPair_of_isReinhardtAdmissible h' (isWindingOne_of_reinhardtCost_lt h' hc')
    have h1 := wd_minimaxDensity_le hbal'.1
    rw [hδ, wd_greatestPackingDensity_eq hbal' (wd_reinhardtCost_pos h'.1).le hvol'] at h1
    exact (div_le_div_iff_of_pos_right h12).1 h1
  · -- otherwise compare with the smoothed octagon: `√12 δ_min ≤ area(K_oct) < π`
    obtain ⟨hbalO, -⟩ := smoothedPolygonDisk_isBalancedPair 1 le_rfl
    have h1 := wd_minimaxDensity_le hbalO.1
    rw [hδ, greatestPackingDensity_of_isBalancedPair hbalO] at h1
    have h2 := (div_le_div_iff_of_pos_right h12).1 h1
    have := wd_volume_octagon_lt
    push Not at hc'
    nlinarith [Real.pi_pos]

/-- **The disk of a global minimizer is a `K_min`** (`sec:existence-opt-control:kmin`, label of this
formalization; TeX 4569–4572): if `(g, X)` is a global
minimizer of Problem 3.6.2 on `[0, T]` and `(K, σ)` a balanced pair in circle representation with
`σ_j = g s_j*` on `[0, T]` and `σ_j(t + T) = σ_{j+1}(t)`, then `K` is a centrally symmetric convex
disk of least greatest packing density, and `δ_min = cost/√12`. -/
theorem isWorstDisk_of_isReinhardtMinimizer {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtMinimizer T u g X) {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hKσ : IsBalancedPair K σ T) (hcirc : IsCircleRepresentation σ)
    (hg : ∀ j, ∀ t ∈ Icc 0 T, σ j t = g t *ᵥ sixthRoot j)
    (hshift : ∀ j t, σ j (t + T) = σ (j + 1) t) :
    IsWorstDisk K ∧ minimaxDensity = reinhardtCost T X / √12 := by
  have hst := h.1.1
  have hc := wd_reinhardtCost_pos hst
  -- `area(K) = cost` (`eqn:cost`), so `δ(K) = cost/√12` (E12)
  have hvol : volume K = ENNReal.ofReal (reinhardtCost T X) :=
    eqn_cost hKσ g X hg (fun t ht ↦ wd_hasDerivAt_g hst ht) hshift
  have hδK := wd_greatestPackingDensity_eq hKσ hc.le hvol
  -- the trajectory of a worst disk `K_min` (Reinhardt's existence and step B1)
  obtain ⟨K₀, hK₀⟩ := rein_exists_worst
  have hK₀' := ch2_isWorstLatticeDisk_iff_isWorstDisk.1 hK₀
  obtain ⟨A, σ₀, T₀, u₀, g₀, X₀, hA, hKσ₀, -, -, -, hadm₀, hvol₀⟩ :=
    exists_isReinhardtAdmissible_of_isWorstDisk hK₀'
  have hδ₀ := wd_minimaxDensity_eq hK₀' hA hKσ₀ hadm₀ hvol₀
  -- `cost ≤ cost(K_min)` by minimality, so `δ(K) ≤ δ_min`
  have hle : reinhardtCost T X ≤ reinhardtCost T₀ X₀ := h.2 _ _ _ _ hadm₀
  have heq : greatestPackingDensity K = minimaxDensity := by
    refine le_antisymm ?_ (wd_minimaxDensity_le hKσ.1)
    rw [hδK, hδ₀]
    exact div_le_div_of_nonneg_right hle (by positivity)
  exact ⟨⟨hKσ.1, heq⟩, by rw [← heq, hδK]⟩

/-- **The layer's result** (§6.1 with §6.2, and the identification with `K_min` that Proposition
8.1.3 and Theorem 16.3.1 use): the Reinhardt control problem (Problem 3.6.2) has a global
minimizer; it lifts to a Pontryagin extremal, and it is the boundary trajectory of a balanced disk
`K` in circle representation that is a `K_min`, with `δ_min = cost/√12`. Assembled from
`exists_isReinhardtMinimizer_isPontryaginExtremal`,
`IsReinhardtMinimizer.forall_mem_truncatedStarDomain` (the cost is at most the octagon's, below
`7π/2`), `isWindingOne_of_reinhardtCost_lt`, `exists_isBalancedPair_of_isReinhardtAdmissible`
and `isWorstDisk_of_isReinhardtMinimizer`. -/
theorem exists_isReinhardtMinimizer_isPontryaginExtremal_isWorstDisk :
    ∃ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ)
      (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ),
      IsReinhardtMinimizer T u g X ∧ IsPontryaginExtremal T u g X Λ₁ ΛR lam ∧
      IsBalancedPair K σ T ∧ IsCircleRepresentation σ ∧
      (∀ j, ∀ t ∈ Icc 0 T, σ j t = g t *ᵥ sixthRoot j) ∧
      (∀ j t, σ j (t + T) = σ (j + 1) t) ∧
      IsWorstDisk K ∧ minimaxDensity = reinhardtCost T X / √12 := by
  obtain ⟨T, u, g, X, Λ₁, ΛR, lam, hmin, hext⟩ := exists_isReinhardtMinimizer_isPontryaginExtremal
  -- the cost is at most the octagon's, below `7π/2`, so the winding number is one
  have hc := (IsReinhardtMinimizer.forall_mem_truncatedStarDomain hmin).1
  have hc' : reinhardtCost T X < 7 * Real.pi / 2 := by
    have := wd_volume_octagon_lt
    nlinarith [Real.pi_pos]
  -- the balanced disk bounded by the minimizer (the converse of Problem 3.6.2)
  obtain ⟨K, σ, G, hGg, -, -, hσG, hshift, hKσ, hcirc, -⟩ :=
    exists_isBalancedPair_of_isReinhardtAdmissible hmin.1
      (isWindingOne_of_reinhardtCost_lt hmin.1 hc')
  have hσg : ∀ j, ∀ t ∈ Icc 0 T, σ j t = g t *ᵥ sixthRoot j := fun j t ht ↦ by
    rw [hσG, hGg t ht]
  obtain ⟨hw, hδ⟩ := isWorstDisk_of_isReinhardtMinimizer hmin hKσ hcirc hσg hshift
  exact ⟨T, u, g, X, Λ₁, ΛR, lam, K, σ, hmin, hext, hKσ, hcirc, hσg, hshift, hw, hδ⟩

end SmoothedPolygons
