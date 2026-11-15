module

public import SmoothedPolygons.Ch15.Involution

/-!
# Chapter 15: the topology of the parts `𝒟₀, …, 𝒟₄` (towards Proposition 15.3.2)

The clauses of `Proposition15_3_2` (`SmoothedPolygons/Ch15/Involution.lean`) that follow from the
way the parts are defined, with no dynamics beyond "the first control changes at the switch":

* the boxes are products of intervals: `closure openBoxOne = closedBoxOne`,
  `interior closedBoxOne = openBoxOne`, and the same for the second box;
* every part lies in its closed box, and its interior in the open box;
* `𝒟₀ = closure (closedBoxOne \ (𝒟₁ ∪ 𝒟₄))` and `𝒟₁` (the closure of a union of connected
  components of an open set) are regular closed (`closure_interior_partD0`,
  `closure_interior_partD1`);
* `𝒟₀, 𝒟₁, 𝒟₄` cover the closed first box, and the interior of `𝒟₀` meets neither `𝒟₁` nor `𝒟₄`
  (`closedBoxOne_subset_partD`, `disjoint_interior_partD0_partD1`,
  `disjoint_interior_partD0_partD4`);
* on the open boxes the switch sets cover: the first control of `F(z)` differs from that of `z`
  (`firstControl_poincare_ne`), so on the open first box it is `1` or `ζ²` and on the open second
  box `1` or `ζ` (`switchSet_openBoxOne_union`, `switchSet_openBoxTwo_union`); hence
  `𝒟₂ ∪ 𝒟₃ = closedBoxTwo` (`partD2_union_partD3`);
* the separation criterion for `𝒟₁` and `𝒟₄` (`disjoint_interior_partD1_partD4_of_separating`): a
  set `V` that contains the points of the open first box switching to `ζ²` off `∂_A ∪ ∂_res`, is
  relatively clopen in the complement of `∂_A ∪ ∂_res`, and whose closure misses the top face,
  forces the interiors of `𝒟₁` and `𝒟₄` apart;
* the image clauses from dense subsets (`image_eq_image_of_dense`): for continuous maps on compact
  closures into a Hausdorff space, two images agree once each dense part maps into the other image.

The analytic clauses (the regularity of `𝒟₂, 𝒟₃, 𝒟₄`, the disjointness of the interiors of
`𝒟₂, 𝒟₃`, the set `V` above, the continuous extensions `F_i` and the action of the involution) are
in `SmoothedPolygons/Ch15/PartExtensions.lean` and `SmoothedPolygons/Ch15/PartitionCellTwo.lean`,
with the reduction `proposition15_3_2_of_remaining`.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology
open scoped Real

namespace TriFuller

/-! ### The boxes as products of intervals -/

private lemma p15_mem_pi3 (a b c : Set ℝ) (p : Fin 3 → ℝ) :
    p ∈ univ.pi ![a, b, c] ↔ p 0 ∈ a ∧ p 1 ∈ b ∧ p 2 ∈ c := by
  simp only [mem_univ_pi]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

private lemma p15_closure_pi3 (a b c : Set ℝ) :
    closure (univ.pi ![a, b, c]) = univ.pi ![closure a, closure b, closure c] := by
  rw [closure_pi_set]
  congr 1
  funext i
  fin_cases i <;> rfl

private lemma p15_interior_pi3 (a b c : Set ℝ) :
    interior (univ.pi ![a, b, c]) = univ.pi ![interior a, interior b, interior c] := by
  rw [interior_pi_set finite_univ]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem openBoxOne_eq_pi : openBoxOne = univ.pi ![Ioo 0 1, Ioo 0 π, Ioo 0 π] := by
  ext p
  rw [p15_mem_pi3]
  rfl

theorem closedBoxOne_eq_pi : closedBoxOne = univ.pi ![Icc 0 1, Icc 0 π, Icc 0 π] := by
  ext p
  rw [p15_mem_pi3]
  rfl

theorem openBoxTwo_eq_pi : openBoxTwo = univ.pi ![Ioo 0 1, Ioo 0 π, Ioo (-π) 0] := by
  ext p
  rw [p15_mem_pi3]
  rfl

theorem closedBoxTwo_eq_pi : closedBoxTwo = univ.pi ![Icc 0 1, Icc 0 π, Icc (-π) 0] := by
  ext p
  rw [p15_mem_pi3]
  rfl

theorem isOpen_openBoxOne : IsOpen openBoxOne := by
  rw [openBoxOne_eq_pi]
  exact isOpen_set_pi finite_univ fun i _ ↦ by fin_cases i <;> exact isOpen_Ioo

theorem isOpen_openBoxTwo : IsOpen openBoxTwo := by
  rw [openBoxTwo_eq_pi]
  exact isOpen_set_pi finite_univ fun i _ ↦ by fin_cases i <;> exact isOpen_Ioo

theorem isClosed_closedBoxOne : IsClosed closedBoxOne := by
  rw [closedBoxOne_eq_pi]
  exact isClosed_set_pi fun i _ ↦ by fin_cases i <;> exact isClosed_Icc

theorem isClosed_closedBoxTwo : IsClosed closedBoxTwo := by
  rw [closedBoxTwo_eq_pi]
  exact isClosed_set_pi fun i _ ↦ by fin_cases i <;> exact isClosed_Icc

theorem closure_openBoxOne : closure openBoxOne = closedBoxOne := by
  rw [openBoxOne_eq_pi, closedBoxOne_eq_pi, p15_closure_pi3, closure_Ioo zero_ne_one,
    closure_Ioo Real.pi_pos.ne]

theorem closure_openBoxTwo : closure openBoxTwo = closedBoxTwo := by
  rw [openBoxTwo_eq_pi, closedBoxTwo_eq_pi, p15_closure_pi3, closure_Ioo zero_ne_one,
    closure_Ioo Real.pi_pos.ne, closure_Ioo (by linarith [Real.pi_pos] : -π ≠ 0)]

theorem interior_closedBoxOne : interior closedBoxOne = openBoxOne := by
  rw [openBoxOne_eq_pi, closedBoxOne_eq_pi, p15_interior_pi3, interior_Icc, interior_Icc]

theorem interior_closedBoxTwo : interior closedBoxTwo = openBoxTwo := by
  rw [openBoxTwo_eq_pi, closedBoxTwo_eq_pi, p15_interior_pi3, interior_Icc, interior_Icc,
    interior_Icc]

theorem openBoxOne_subset_closedBoxOne : openBoxOne ⊆ closedBoxOne :=
  closure_openBoxOne ▸ subset_closure

theorem openBoxTwo_subset_closedBoxTwo : openBoxTwo ⊆ closedBoxTwo :=
  closure_openBoxTwo ▸ subset_closure

theorem isCompact_closedBoxOne : IsCompact closedBoxOne := by
  rw [closedBoxOne_eq_pi]
  exact isCompact_univ_pi fun i ↦ by fin_cases i <;> exact isCompact_Icc

theorem isCompact_closedBoxTwo : IsCompact closedBoxTwo := by
  rw [closedBoxTwo_eq_pi]
  exact isCompact_univ_pi fun i ↦ by fin_cases i <;> exact isCompact_Icc

/-! ### General facts about regular closed sets -/

/-- The closure of an open set is regular closed. -/
private lemma p15_closure_interior_closure_of_isOpen {α : Type*} [TopologicalSpace α] {U : Set α}
    (hU : IsOpen U) : closure (interior (closure U)) = closure U := by
  apply Subset.antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · exact closure_mono (hU.subset_interior_iff.2 subset_closure)

/-- A closed set `K = closure O`, `O` open, minus a closed set `C`: `closure (K \ C)` is the
closure of the open set `O \ C`. -/
private lemma p15_closure_diff {α : Type*} [TopologicalSpace α] {O C : Set α} (hC : IsClosed C) :
    closure (closure O \ C) = closure (O \ C) := by
  apply Subset.antisymm
  · refine closure_minimal (fun x hx ↦ ?_) isClosed_closure
    have : x ∈ closure O ∩ Cᶜ := ⟨hx.1, hx.2⟩
    exact hC.isOpen_compl.closure_inter this
  · exact closure_mono (sdiff_subset_sdiff_left subset_closure)

/-! ### The parts lie in their boxes -/

theorem partD1_subset : partD1 ⊆ closedBoxOne := by
  rw [← closure_openBoxOne]
  exact closure_mono fun p hp ↦ hp.1.1

theorem partD4_subset : partD4 ⊆ closedBoxOne := by
  rw [← closure_openBoxOne]
  exact closure_mono fun p hp ↦ hp.1

theorem partD0_subset : partD0 ⊆ closedBoxOne :=
  closure_minimal sdiff_subset isClosed_closedBoxOne

theorem partD2_subset : partD2 ⊆ closedBoxTwo := by
  rw [← closure_openBoxTwo]
  exact closure_mono fun p hp ↦ hp.1

theorem partD3_subset : partD3 ⊆ closedBoxTwo := by
  rw [← closure_openBoxTwo]
  exact closure_mono fun p hp ↦ hp.1

/-- The interior of a subset of the closed first box lies in the open box. -/
theorem interior_subset_openBoxOne {D : Set (Fin 3 → ℝ)} (hD : D ⊆ closedBoxOne) :
    interior D ⊆ openBoxOne :=
  interior_closedBoxOne ▸ interior_mono hD

/-- The interior of a subset of the closed second box lies in the open box. -/
theorem interior_subset_openBoxTwo {D : Set (Fin 3 → ℝ)} (hD : D ⊆ closedBoxTwo) :
    interior D ⊆ openBoxTwo :=
  interior_closedBoxTwo ▸ interior_mono hD

/-! ### `𝒟₀` and `𝒟₁` are regular closed -/

/-- The open set whose components define `𝒟₁`: the open first box minus the closure of the
`∂_A ∪ ∂_res` points. -/
noncomputable def openBoxOneOff : Set (Fin 3 → ℝ) :=
  openBoxOne \ closure (boxCoords (bdA ∪ bdRes))

theorem isOpen_openBoxOneOff : IsOpen openBoxOneOff :=
  isOpen_openBoxOne.sdiff isClosed_closure

/-- The union of the components of `openBoxOneOff` whose closures meet the top face (so that
`𝒟₁ = closure partD1Core`). -/
noncomputable def partD1Core : Set (Fin 3 → ℝ) :=
  {p | p ∈ openBoxOneOff ∧
    (closure (connectedComponentIn openBoxOneOff p) ∩ topFaceOne).Nonempty}

theorem partD1_eq : partD1 = closure partD1Core := rfl

/-- The union of components defining `𝒟₁` is open: each component of an open subset of `ℝ³` is
open (`IsOpen.connectedComponentIn`), and lies in the union. -/
theorem isOpen_partD1Core : IsOpen partD1Core := by
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨hp, hne⟩
  have hO := isOpen_openBoxOneOff
  refine Filter.mem_of_superset ((hO.connectedComponentIn).mem_nhds (mem_connectedComponentIn hp))
    fun q hq ↦ ⟨connectedComponentIn_subset _ _ hq, ?_⟩
  rwa [← connectedComponentIn_eq hq]

/-- **`𝒟₁` is regular closed**: it is the closure of an open set. -/
theorem closure_interior_partD1 : closure (interior partD1) = partD1 :=
  p15_closure_interior_closure_of_isOpen isOpen_partD1Core

theorem isClosed_partD (i : Fin 5) : IsClosed (partD i) := by
  fin_cases i <;> exact isClosed_closure

/-- **`𝒟₀` is regular closed**: `closedBoxOne \ (𝒟₁ ∪ 𝒟₄)` has the same closure as the open set
`openBoxOne \ (𝒟₁ ∪ 𝒟₄)`. -/
theorem closure_interior_partD0 : closure (interior partD0) = partD0 := by
  have hC : IsClosed (partD1 ∪ partD4) := isClosed_closure.union isClosed_closure
  have h : partD0 = closure (openBoxOne \ (partD1 ∪ partD4)) := by
    rw [partD0, ← closure_openBoxOne, p15_closure_diff hC]
  rw [h]
  exact p15_closure_interior_closure_of_isOpen (isOpen_openBoxOne.sdiff hC)

/-! ### Covering and the interiors of `𝒟₀` -/

/-- `𝒟₀, 𝒟₁, 𝒟₄` cover the closed first box. -/
theorem closedBoxOne_subset_partD {p : Fin 3 → ℝ} (hp : p ∈ closedBoxOne) :
    p ∈ partD0 ∨ p ∈ partD1 ∨ p ∈ partD4 := by
  by_cases h1 : p ∈ partD1
  · exact Or.inr (Or.inl h1)
  by_cases h4 : p ∈ partD4
  · exact Or.inr (Or.inr h4)
  exact Or.inl (subset_closure ⟨hp, fun h ↦ h.elim h1 h4⟩)

/-- The interior of `𝒟₀` does not meet the interior of `𝒟₁` (nor `𝒟₁` itself, by the same
argument): `𝒟₀` is the closure of a set disjoint from `𝒟₁`. -/
theorem disjoint_interior_partD0_partD1 : Disjoint (interior partD0) (interior partD1) := by
  rw [Set.disjoint_left]
  intro p _ hp1
  have hp0 : p ∈ partD0 := interior_subset ‹_›
  obtain ⟨q, hq, hq'⟩ := mem_closure_iff.1 hp0 (interior partD1) isOpen_interior hp1
  exact hq'.2 (Or.inl (interior_subset hq))

theorem disjoint_interior_partD0_partD4 : Disjoint (interior partD0) (interior partD4) := by
  rw [Set.disjoint_left]
  intro p _ hp4
  have hp0 : p ∈ partD0 := interior_subset ‹_›
  obtain ⟨q, hq, hq'⟩ := mem_closure_iff.1 hp0 (interior partD4) isOpen_interior hp4
  exact hq'.2 (Or.inr (interior_subset hq))

/-! ### The switch sets on the open boxes -/

private lemma p15_cellPoint_ne_zero {p : Fin 3 → ℝ} (hp : p ∈ cellDomain) : cellPoint p ≠ 0 :=
  (cellPoint_mem_sectionZero hp).1

private lemma p15_openBoxOne_sub {p : Fin 3 → ℝ} (hp : p ∈ openBoxOne) : p ∈ cellDomain :=
  ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2.1,
    ⟨by linarith [hp.2.2.1, Real.pi_pos], hp.2.2.2.le⟩⟩

private lemma p15_openBoxTwo_sub {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo) : p ∈ cellDomain :=
  ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2.1,
    ⟨hp.2.2.1.le, by linarith [hp.2.2.2, Real.pi_pos]⟩⟩

/-- On the open first box the Poincaré map switches from `ζ` to `1` or to `ζ²`. -/
theorem firstControl_poincare_openBoxOne {p : Fin 3 → ℝ} (hp : p ∈ openBoxOne) :
    firstControl (poincare (cellPoint p)) = 1 ∨
      firstControl (poincare (cellPoint p)) = ζ ^ 2 := by
  have hne := firstControl_poincare_ne (p15_cellPoint_ne_zero (p15_openBoxOne_sub hp))
  rw [definition15_1_2.2.2.2.2.2.1 p hp] at hne
  rcases mem_VT.1 (firstControl_mem_VT (poincare (cellPoint p))) with h | h | h
  · exact Or.inl h
  · exact absurd h hne
  · exact Or.inr h

/-- On the open second box the Poincaré map switches from `ζ²` to `1` or to `ζ`. -/
theorem firstControl_poincare_openBoxTwo {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo) :
    firstControl (poincare (cellPoint p)) = 1 ∨
      firstControl (poincare (cellPoint p)) = ζ := by
  have hne := firstControl_poincare_ne (p15_cellPoint_ne_zero (p15_openBoxTwo_sub hp))
  rw [definition15_1_2.2.2.2.2.2.2.1 p hp] at hne
  rcases mem_VT.1 (firstControl_mem_VT (poincare (cellPoint p))) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hne

theorem switchSet_openBoxOne_union :
    switchSet openBoxOne 1 ∪ switchSet openBoxOne (ζ ^ 2) = openBoxOne := by
  apply Subset.antisymm
  · rintro p (hp | hp) <;> exact hp.1
  · intro p hp
    rcases firstControl_poincare_openBoxOne hp with h | h
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, h⟩

theorem switchSet_openBoxTwo_union :
    switchSet openBoxTwo 1 ∪ switchSet openBoxTwo ζ = openBoxTwo := by
  apply Subset.antisymm
  · rintro p (hp | hp) <;> exact hp.1
  · intro p hp
    rcases firstControl_poincare_openBoxTwo hp with h | h
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, h⟩

/-- **`𝒟₂` and `𝒟₃` cover the closed second box**: `𝒟₂ ∪ 𝒟₃` is the closure of the open second
box. -/
theorem partD2_union_partD3 : partD2 ∪ partD3 = closedBoxTwo := by
  rw [partD2, partD3, ← closure_union, switchSet_openBoxTwo_union, closure_openBoxTwo]

/-- The disjointness of the interiors of `𝒟₂` and `𝒟₃` holds as soon as the points of the open
second box that are limits of both switch sets form a set with empty interior. -/
theorem disjoint_interior_partD2_partD3_of
    (h : interior (closure (switchSet openBoxTwo 1) ∩ closure (switchSet openBoxTwo ζ)) = ∅) :
    Disjoint (interior partD2) (interior partD3) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← interior_inter]
  exact h

/-! ### Separating `𝒟₁` from `𝒟₄` -/

/-- **A criterion for `int 𝒟₁ ∩ int 𝒟₄ = ∅`.** Let `O = openBoxOne \ closure (∂_A ∪ ∂_res)` and
let `V` be a set such that `O ∩ V` is relatively clopen in `O` (`O ∩ V` and `O \ V` are open), the
closure of `V` misses the top face `𝒞₂(ζ, 0, 2)`, and every point of `O` switching to `ζ²` lies in
`V`. Then a component of `O` meeting `V` lies in `V` and its closure misses the top face, so the
core of `𝒟₁` misses `V`; an open set in both `𝒟₁` and `𝒟₄` would contain a point of the core
switching to `ζ²`. -/
theorem disjoint_interior_partD1_partD4_of_separating (V : Set (Fin 3 → ℝ))
    (hV₁ : IsOpen (openBoxOneOff ∩ V)) (hV₂ : IsOpen (openBoxOneOff \ V))
    (hVtop : Disjoint (closure V) topFaceOne)
    (hB : ∀ p ∈ switchSet openBoxOne (ζ ^ 2), p ∈ openBoxOneOff → p ∈ V) :
    Disjoint (interior partD1) (interior partD4) := by
  -- the core of `𝒟₁` misses `V`
  have hcore : ∀ p ∈ partD1Core, p ∉ V := by
    rintro p ⟨hpO, hne⟩ hpV
    -- the component of `p` lies in `V`: it is preconnected and `O ∩ V`, `O \ V` split `O`
    have hsub : connectedComponentIn openBoxOneOff p ⊆ V := by
      have hpre := isPreconnected_connectedComponentIn (F := openBoxOneOff) (x := p)
      have hcov : connectedComponentIn openBoxOneOff p ⊆
          (openBoxOneOff ∩ V) ∪ (openBoxOneOff \ V) := fun q hq ↦ by
        have := connectedComponentIn_subset _ _ hq
        by_cases hqV : q ∈ V
        · exact Or.inl ⟨this, hqV⟩
        · exact Or.inr ⟨this, hqV⟩
      rcases IsPreconnected.subset_or_subset hV₁ hV₂ (by
          rw [Set.disjoint_iff]
          rintro q ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
          exact h2 h1) hcov hpre with h | h
      · exact fun q hq ↦ (h hq).2
      · exact absurd hpV (h (mem_connectedComponentIn hpO)).2
    obtain ⟨x, hx1, hx2⟩ := hne
    exact Set.disjoint_left.1 hVtop (closure_mono hsub hx1) hx2
  rw [Set.disjoint_iff_inter_eq_empty, ← interior_inter, Set.eq_empty_iff_forall_notMem]
  intro p hp
  -- an open set inside `𝒟₁ ∩ 𝒟₄` meets the core of `𝒟₁` in an open set
  set N := interior (partD1 ∩ partD4) with hN
  have hNo : IsOpen N := isOpen_interior
  have hN1 : N ⊆ closure partD1Core := fun q hq ↦ (interior_subset hq).1
  have hN4 : N ⊆ closure (switchSet openBoxOne (ζ ^ 2)) := fun q hq ↦ (interior_subset hq).2
  obtain ⟨q, hqN, hqC⟩ := mem_closure_iff.1 (hN1 hp) N hNo hp
  have hW : IsOpen (N ∩ partD1Core) := hNo.inter isOpen_partD1Core
  obtain ⟨y, hyW, hyB⟩ := mem_closure_iff.1 (hN4 hqN) _ hW ⟨hqN, hqC⟩
  exact hcore y hyW.2 (hB y hyB hyW.2.1)

/-! ### The image clauses from dense subsets -/

/-- **Images of compact closures.** Let `f`, `g` be continuous on compact sets `K = closure E`,
`L = closure E'` with values in a Hausdorff space. If `f` maps `E` into `g '' L` and `g` maps `E'`
into `f '' K`, then `f '' K = g '' L`. (The action of the involution on the parts reduces to its
action on dense subsets of their interiors, where `F_i = F`.) -/
theorem image_eq_image_of_dense {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [T2Space β] {f g : α → β} {E E' K L : Set α} (hK : IsCompact K) (hL : IsCompact L)
    (hEK : closure E = K) (hEL : closure E' = L) (hf : ContinuousOn f K) (hg : ContinuousOn g L)
    (h1 : f '' E ⊆ g '' L) (h2 : g '' E' ⊆ f '' K) : f '' K = g '' L := by
  have hgL : IsClosed (g '' L) := (hL.image_of_continuousOn hg).isClosed
  have hfK : IsClosed (f '' K) := (hK.image_of_continuousOn hf).isClosed
  apply Subset.antisymm
  · rw [← hEK]
    refine (ContinuousOn.image_closure (hEK ▸ hf)).trans ?_
    exact closure_minimal h1 hgL
  · rw [← hEL]
    refine (ContinuousOn.image_closure (hEL ▸ hg)).trans ?_
    exact closure_minimal h2 hfK

end TriFuller

end SmoothedPolygons
