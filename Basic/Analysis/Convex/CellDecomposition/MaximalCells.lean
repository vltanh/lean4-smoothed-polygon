module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Topology.Semicontinuity.Basic
public import Basic.Analysis.Convex.CellDecomposition.Defs

/-!
# (A) A maximal family of cells

Part of the proof of the cell lemma (`Basic.Analysis.Convex.CellDecomposition`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PlaneConvex

/-! ### Separating lines -/

/-- Two convex sets of the plane with nonempty disjoint interiors are separated by a line:
there are `u` with `‖u‖ = 1` (Mathlib's sup norm; any normalization will do) and `t` with
`⟨u, x⟩ ≤ t` on `A` and `t ≤ ⟨u, y⟩` on `B`. -/
private theorem exists_separating_line {A B : Set (Fin 2 → ℝ)} (hA : Convex ℝ A)
    (hB : Convex ℝ B) (hAi : (interior A).Nonempty) (hBi : (interior B).Nonempty)
    (hAB : Disjoint (interior A) (interior B)) :
    ∃ u : Fin 2 → ℝ, ‖u‖ = 1 ∧ ∃ t : ℝ, (∀ x ∈ A, u ⬝ᵥ x ≤ t) ∧ ∀ y ∈ B, t ≤ u ⬝ᵥ y := by
  obtain ⟨f, s, hfA, hfB⟩ := geometric_hahn_banach_open_open hA.interior isOpen_interior
    hB.interior isOpen_interior hAB
  -- `f` extends to the closures: `A ⊆ closure (interior A)`.
  have hA' : ∀ x ∈ A, f x ≤ s := by
    intro x hx
    have hx' : x ∈ closure (interior A) := by
      rw [hA.closure_interior_eq_closure_of_nonempty_interior hAi]; exact subset_closure hx
    exact closure_minimal (fun y hy ↦ (hfA y hy).le) (isClosed_le f.continuous continuous_const)
      hx'
  have hB' : ∀ y ∈ B, s ≤ f y := by
    intro y hy
    have hy' : y ∈ closure (interior B) := by
      rw [hB.closure_interior_eq_closure_of_nonempty_interior hBi]; exact subset_closure hy
    exact closure_minimal (fun z hz ↦ (hfB z hz).le) (isClosed_le continuous_const f.continuous)
      hy'
  -- `f` is a dot product.
  set v : Fin 2 → ℝ := fun k ↦ f fun j ↦ if k = j then 1 else 0 with hv
  have hfv : ∀ x, f x = v ⬝ᵥ x := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) x
    rw [dotProduct_comm]
    simpa [dotProduct, hv, smul_eq_mul] using this
  have hv0 : v ≠ 0 := by
    rintro h0
    obtain ⟨a, ha⟩ := hAi
    obtain ⟨b, hb⟩ := hBi
    have h1 := hfA a ha
    have h2 := hfB b hb
    rw [hfv, h0, zero_dotProduct] at h1 h2
    linarith
  have hr : 0 < ‖v‖ := norm_pos_iff.2 hv0
  refine ⟨‖v‖⁻¹ • v, ?_, ‖v‖⁻¹ * s, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  · intro x hx
    rw [smul_dotProduct, smul_eq_mul, ← hfv]
    exact mul_le_mul_of_nonneg_left (hA' x hx) (inv_nonneg.2 hr.le)
  · intro y hy
    rw [smul_dotProduct, smul_eq_mul, ← hfv]
    exact mul_le_mul_of_nonneg_left (hB' y hy) (inv_nonneg.2 hr.le)

/-- Sets on the two sides of a line `⟨u, x⟩ = t` (`u ≠ 0`) have disjoint interiors. -/
private theorem disjoint_interior_of_le_of_le {A B : Set (Fin 2 → ℝ)} {u : Fin 2 → ℝ}
    (hu : u ≠ 0) {t : ℝ} (hA : ∀ x ∈ A, u ⬝ᵥ x ≤ t) (hB : ∀ y ∈ B, t ≤ u ⬝ᵥ y) :
    Disjoint (interior A) (interior B) := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  have hmem : interior A ∩ interior B ∈ 𝓝 x :=
    inter_mem (isOpen_interior.mem_nhds hxA) (isOpen_interior.mem_nhds hxB)
  have hcont : Tendsto (fun s : ℝ ↦ x + s • u) (𝓝[>] 0) (𝓝 x) := by
    have : Continuous (fun s : ℝ ↦ x + s • u) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨s, ⟨hsA, hsB⟩, hs⟩ := ((hcont.eventually hmem).and self_mem_nhdsWithin).exists
  have h1 := hA _ (interior_subset hsA)
  have h2 := hB _ (interior_subset hsB)
  have h3 := hA _ (interior_subset hxA)
  have h4 := hB _ (interior_subset hxB)
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h1 h2
  have huu : u ⬝ᵥ u = 0 := by
    have : s * (u ⬝ᵥ u) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (ne_of_gt hs)
  exact hu (dotProduct_self_eq_zero.1 huu)

/-! ### The cells `P_i(λ)` -/

/-- The cell `P_i(λ) = Q ∩ ⋂_j {⟨u_ij, x⟩ ≤ t_ij}` for parameters `λ i j = (u_ij, t_ij)`. -/
private def cell {m n : ℕ} (b : Fin m → Fin 2 → ℝ) (d : Fin m → ℝ)
    (L : Fin n → Fin n → (Fin 2 → ℝ) × ℝ) (i : Fin n) : Set (Fin 2 → ℝ) :=
  halfPlanesInter (Fin.append b fun j ↦ (L i j).1) (Fin.append d fun j ↦ (L i j).2)

private theorem mem_cell {m n : ℕ} {b : Fin m → Fin 2 → ℝ} {d : Fin m → ℝ}
    {L : Fin n → Fin n → (Fin 2 → ℝ) × ℝ} {i : Fin n} {x : Fin 2 → ℝ} :
    x ∈ cell b d L i ↔ x ∈ halfPlanesInter b d ∧ ∀ j, (L i j).1 ⬝ᵥ x ≤ (L i j).2 := by
  simp only [cell, halfPlanesInter, mem_ofPred_eq, Fin.forall_fin_add, Fin.append_left,
    Fin.append_right]

private theorem cell_subset {m n : ℕ} (b : Fin m → Fin 2 → ℝ) (d : Fin m → ℝ)
    (L : Fin n → Fin n → (Fin 2 → ℝ) × ℝ) (i : Fin n) : cell b d L i ⊆ halfPlanesInter b d :=
  fun _ hx ↦ (mem_cell.1 hx).1

/-- The graph `{(λ, x) | x ∈ P_i(λ)}` is closed. -/
private theorem isClosed_graph_cell {m n : ℕ} (b : Fin m → Fin 2 → ℝ) (d : Fin m → ℝ)
    (i : Fin n) :
    IsClosed {z : (Fin n → Fin n → (Fin 2 → ℝ) × ℝ) × (Fin 2 → ℝ) | z.2 ∈ cell b d z.1 i} := by
  have : {z : (Fin n → Fin n → (Fin 2 → ℝ) × ℝ) × (Fin 2 → ℝ) | z.2 ∈ cell b d z.1 i} =
      Prod.snd ⁻¹' halfPlanesInter b d ∩ ⋂ j, {z | (z.1 i j).1 ⬝ᵥ z.2 ≤ (z.1 i j).2} := by
    ext z; simp [mem_cell]
  rw [this]
  exact ((isClosed_halfPlanesInter b d).preimage continuous_snd).inter
    (isClosed_iInter fun j ↦ isClosed_le (by fun_prop) (by fun_prop))

/-- `λ ↦ |P_i(λ)|` is upper semicontinuous (`P_i(λ)` depends upper semicontinuously on `λ`, inside
the compact set `Q`). -/
private theorem upperSemicontinuous_volume_cell {m n : ℕ} (b : Fin m → Fin 2 → ℝ)
    (d : Fin m → ℝ) (hQ : Bornology.IsBounded (halfPlanesInter b d)) (i : Fin n) :
    UpperSemicontinuous fun L ↦ volume (cell b d L i) := by
  rw [upperSemicontinuous_iff]
  intro L₀
  rw [upperSemicontinuousAt_iff]
  intro c hc
  obtain ⟨U, hUsup, hUopen, hUc⟩ := Set.exists_isOpen_lt_of_lt (cell b d L₀ i) c hc
  have hZ : IsCompact (halfPlanesInter b d \ U) :=
    (Metric.isCompact_of_isClosed_isBounded (isClosed_halfPlanesInter b d) hQ).diff hUopen
  have hev : ∀ᶠ L in 𝓝 L₀, ∀ y ∈ halfPlanesInter b d \ U, y ∉ cell b d L i :=
    hZ.eventually_forall_of_forall_eventually fun y hy ↦
      (isClosed_graph_cell b d i).isOpen_compl.mem_nhds fun h ↦ hy.2 (hUsup h)
  filter_upwards [hev] with L hL
  refine lt_of_le_of_lt (measure_mono fun y hy ↦ ?_) hUc
  by_contra hyU
  exact hL y ⟨cell_subset b d L i hy, hyU⟩ hy

/-! ### The parameter set `Λ` -/

/-- The parameters: `‖u_ij‖ ≤ 1`, `|t_ij| ≤ M`, `‖u_ij‖ = 1` and `λ j i = -λ i j` for `i ≠ j`, and
`K i ⊆ P_i(λ)`. -/
private def params {n : ℕ} (K : Fin n → Set (Fin 2 → ℝ)) (M : ℝ) :
    Set (Fin n → Fin n → (Fin 2 → ℝ) × ℝ) :=
  {L | (∀ i j, ‖(L i j).1‖ ≤ 1 ∧ ‖(L i j).2‖ ≤ M) ∧
    (∀ i j, i ≠ j → ‖(L i j).1‖ = 1 ∧ L j i = -L i j) ∧
    ∀ i, ∀ x ∈ K i, ∀ j, (L i j).1 ⬝ᵥ x ≤ (L i j).2}

private theorem isCompact_params {n : ℕ} (K : Fin n → Set (Fin 2 → ℝ)) (M : ℝ) :
    IsCompact (params K M) := by
  have hclosed : IsClosed (params K M) := by
    simp only [params, ofPred_and, ofPred_forall]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
        (isClosed_le (by fun_prop) continuous_const).inter
          (isClosed_le (by fun_prop) continuous_const)
    · exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
        (isClosed_eq (by fun_prop) continuous_const).inter
          (isClosed_eq (by fun_prop) (by fun_prop))
    · exact isClosed_iInter fun i ↦ isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦
        isClosed_iInter fun j ↦ isClosed_le (by fun_prop) (by fun_prop)
  refine (isCompact_closedBall (0 : Fin n → Fin n → (Fin 2 → ℝ) × ℝ) (max 1 M)).of_isClosed_subset
    hclosed fun L hL ↦ ?_
  have h0 : (0 : ℝ) ≤ max 1 M := le_max_of_le_left zero_le_one
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg h0]
  intro i
  rw [pi_norm_le_iff_of_nonneg h0]
  intro j
  rw [norm_prod_le_iff]
  exact ⟨(hL.1 i j).1.trans (le_max_left _ _), (hL.1 i j).2.trans (le_max_right _ _)⟩

/-! ### Domination and the maximum -/

/-- A bound `M ≥ 0` for `|⟨u, x⟩|`, `‖u‖ ≤ 1`, `x ∈ Q`, `Q` compact. -/
private theorem exists_bound_dotProduct {Q : Set (Fin 2 → ℝ)} (hQ : IsCompact Q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u x, ‖u‖ ≤ 1 → x ∈ Q → ‖u ⬝ᵥ x‖ ≤ M := by
  obtain ⟨M, hM⟩ :=
    ((isCompact_closedBall (0 : Fin 2 → ℝ) 1).prod hQ).exists_bound_of_continuousOn
      (f := fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) ↦ p.1 ⬝ᵥ p.2) (by fun_prop)
  exact ⟨max M 0, le_max_right _ _, fun u x hu hx ↦
    (hM (u, x) ⟨mem_closedBall_zero_iff.2 hu, hx⟩).trans (le_max_left _ _)⟩

/-- (4) Every non-overlapping family of convex sets `K i ⊆ C' i ⊆ Q` is dominated by the cells
`P_i(λ)` of some `λ ∈ Λ`: separate `C' i` and `C' j` by a line for `i < j`. -/
private theorem exists_params_subset_cell {m n : ℕ} {b : Fin m → Fin 2 → ℝ} {d : Fin m → ℝ}
    {K : Fin n → Set (Fin 2 → ℝ)} (hK : ∀ i, (interior (K i)).Nonempty) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u x, ‖u‖ ≤ 1 → x ∈ halfPlanesInter b d → ‖u ⬝ᵥ x‖ ≤ M)
    {C' : Fin n → Set (Fin 2 → ℝ)} (hC' : ∀ i, Convex ℝ (C' i)) (hKC : ∀ i, K i ⊆ C' i)
    (hCQ : ∀ i, C' i ⊆ halfPlanesInter b d) (hdisj : NonOverlapping C') :
    ∃ L ∈ params K M, ∀ i, C' i ⊆ cell b d L i := by
  have hint : ∀ i, (interior (C' i)).Nonempty := fun i ↦ (hK i).mono (interior_mono (hKC i))
  have hne : ∀ i, (C' i).Nonempty := fun i ↦ (hint i).mono interior_subset
  have hsep : ∀ i j, i ≠ j → ∃ u : Fin 2 → ℝ, ‖u‖ = 1 ∧ ∃ t : ℝ,
      (∀ x ∈ C' i, u ⬝ᵥ x ≤ t) ∧ ∀ y ∈ C' j, t ≤ u ⬝ᵥ y := fun i j hij ↦
    exists_separating_line (hC' i) (hC' j) (hint i) (hint j) (hdisj hij)
  choose! u hu t ht using hsep
  have htM : ∀ i j, i ≠ j → ‖t i j‖ ≤ M := by
    intro i j hij
    obtain ⟨x, hx⟩ := hne i
    obtain ⟨y, hy⟩ := hne j
    have h1 := (ht i j hij).1 x hx
    have h2 := (ht i j hij).2 y hy
    have h3 := hM (u i j) x (hu i j hij).le (hCQ i hx)
    have h4 := hM (u i j) y (hu i j hij).le (hCQ j hy)
    rw [Real.norm_eq_abs, abs_le] at h3 h4 ⊢
    constructor <;> linarith [h3.1, h4.2]
  let L : Fin n → Fin n → (Fin 2 → ℝ) × ℝ := fun i j ↦
    if i < j then (u i j, t i j) else if j < i then -(u j i, t j i) else 0
  have hL0 : ∀ i j, ‖(L i j).1‖ ≤ 1 ∧ ‖(L i j).2‖ ≤ M := by
    intro i j
    by_cases h : i < j
    · simp only [L, h, ↓reduceIte]
      exact ⟨(hu i j h.ne).le, htM i j h.ne⟩
    by_cases h' : j < i
    · simp only [L, h, h', ↓reduceIte, Prod.fst_neg, Prod.snd_neg, norm_neg]
      exact ⟨(hu j i h'.ne).le, htM j i h'.ne⟩
    · simp only [L, h, h', ↓reduceIte, Prod.fst_zero, Prod.snd_zero, norm_zero]
      exact ⟨zero_le_one, hM0⟩
  have hL1 : ∀ i j, i ≠ j → ‖(L i j).1‖ = 1 ∧ L j i = -L i j := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · simp only [L, h, lt_asymm h, ↓reduceIte, and_true]
      exact hu i j hij
    · simp only [L, h, lt_asymm h, ↓reduceIte, Prod.fst_neg, norm_neg, neg_neg, and_true]
      exact hu j i hij.symm
  have hLC : ∀ i, ∀ x ∈ C' i, ∀ j, (L i j).1 ⬝ᵥ x ≤ (L i j).2 := by
    intro i x hx j
    by_cases h : i < j
    · simp only [L, h, ↓reduceIte]
      exact (ht i j h.ne).1 x hx
    by_cases h' : j < i
    · simp only [L, h, h', ↓reduceIte, Prod.fst_neg, Prod.snd_neg, neg_dotProduct,
        neg_le_neg_iff]
      exact (ht j i h'.ne).2 x hx
    · simp [L, h, h']
  exact ⟨L, ⟨hL0, hL1, fun i x hx j ↦ hLC i x (hKC i hx) j⟩,
    fun i x hx ↦ mem_cell.2 ⟨hCQ i hx, hLC i x hx⟩⟩

/-- **(A) A maximal family of cells exists.** Let `Q = halfPlanesInter b d` be bounded and
`K i ⊆ Q` (`i < n`) non-overlapping compact convex sets with nonempty interiors. Then there are
convex polygons `C i` with `K i ⊆ C i ⊆ Q`, non-overlapping, of maximal total area among all
non-overlapping families of convex sets `K i ⊆ C' i ⊆ Q` (`IsMaximalCells`).

Argument. (1) *Separation.* Two convex sets with nonempty disjoint interiors are separated by a
line (`geometric_hahn_banach_open_open` applied to the interiors, extended to the sets by
`Convex.closure_interior_eq_closure_of_nonempty_interior`): there are `‖u‖ = 1` and `t` with
`⟨u, x⟩ ≤ t` on the first set and `≥ t` on the second.
(2) *Parametrization.* The parameters `λ i j = (u_ij, t_ij)` with `‖u_ij‖ ≤ 1`, `|t_ij| ≤ M`
(`M` bounds `|⟨u, x⟩|` on `Q`), `‖u_ij‖ = 1` and `λ j i = -λ i j` for `i ≠ j`, and
`sup_{K i} ⟨u_ij, ·⟩ ≤ t_ij`, form a compact set `Λ`. The cells
`P_i(λ) = Q ∩ ⋂_j {⟨u_ij, x⟩ ≤ t_ij}` are convex polygons (bounded, `⊇ K i`), contain `K i`, and
are non-overlapping (`P_i ⊆ {⟨u_ij, ·⟩ ≤ t_ij}`, `P_j ⊆ {⟨u_ij, ·⟩ ≥ t_ij}`).
(3) *The maximum.* `λ ↦ ∑ |P_i(λ)|` is upper semicontinuous: the graph `{(λ, x) | x ∈ P_i(λ)}` is
closed, so for an open `U ⊇ P_i(λ₀)` (outer regularity) the compact set `Q \ U` misses `P_i(λ)`
for `λ` near `λ₀` (`IsCompact.eventually_forall_of_forall_eventually`). So the maximum on the
compact set `Λ` is attained (`UpperSemicontinuousOn.exists_isMaxOn`) at some `λ₀`; put
`C i = P_i(λ₀)`.
(4) *Maximality among all convex families.* If `C' i` are convex, non-overlapping, with
`K i ⊆ C' i ⊆ Q`, then each `C' i` has nonempty interior, so `C' i` and `C' j` are separated by a
line as in (1); this gives `λ ∈ Λ` with `C' i ⊆ P_i(λ)`, hence
`∑ |C' i| ≤ ∑ |P_i(λ)| ≤ ∑ |C i|`. (`Λ` is nonempty by (4) applied to `C' = K`.)

The plan for step (3) was continuity of `λ ↦ ∑ |P_i(λ)|` by dominated convergence; upper
semicontinuity suffices for the maximum and needs no null-set argument. -/
theorem exists_isMaximalCells {m n : ℕ} (b : Fin m → Fin 2 → ℝ) (d : Fin m → ℝ)
    (hQ : Bornology.IsBounded (halfPlanesInter b d)) (K : Fin n → Set (Fin 2 → ℝ))
    (hK : ∀ i, Convex ℝ (K i) ∧ IsCompact (K i) ∧ (interior (K i)).Nonempty)
    (hKQ : ∀ i, K i ⊆ halfPlanesInter b d) (hdisj : NonOverlapping K) :
    ∃ C : Fin n → Set (Fin 2 → ℝ), (∀ i, IsConvexPolygon (C i)) ∧ (∀ i, K i ⊆ C i) ∧
      (∀ i, C i ⊆ halfPlanesInter b d) ∧ NonOverlapping C ∧
      IsMaximalCells (halfPlanesInter b d) K C := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_dotProduct
    (Metric.isCompact_of_isClosed_isBounded (isClosed_halfPlanesInter b d) hQ)
  -- `Λ` is nonempty.
  obtain ⟨L₁, hL₁, -⟩ := exists_params_subset_cell (b := b) (d := d) (fun i ↦ (hK i).2.2) hM0 hM
    (fun i ↦ (hK i).1) (fun i ↦ subset_rfl) hKQ hdisj
  -- The maximum of `λ ↦ ∑ |P_i(λ)|` on `Λ`.
  have husc : UpperSemicontinuous fun L : Fin n → Fin n → (Fin 2 → ℝ) × ℝ ↦
      ∑ i, volume (cell b d L i) :=
    upperSemicontinuous_sum fun i _ ↦ upperSemicontinuous_volume_cell b d hQ i
  obtain ⟨L₀, hL₀, hmax⟩ :=
    (husc.upperSemicontinuousOn _).exists_isMaxOn ⟨L₁, hL₁⟩ (isCompact_params K M)
  have hKC : ∀ i, K i ⊆ cell b d L₀ i := fun i x hx ↦ mem_cell.2 ⟨hKQ i hx, hL₀.2.2 i x hx⟩
  refine ⟨cell b d L₀, fun i ↦ ?_, hKC, cell_subset b d L₀, ?_, ?_⟩
  · exact ⟨⟨m + n, _, _, rfl⟩, hQ.subset (cell_subset b d L₀ i),
      (hK i).2.2.mono (interior_mono (hKC i))⟩
  · intro i j hij
    obtain ⟨hu1, hji⟩ := hL₀.2.1 i j hij
    refine disjoint_interior_of_le_of_le (u := (L₀ i j).1) (t := (L₀ i j).2) ?_
      (fun x hx ↦ (mem_cell.1 hx).2 j) fun y hy ↦ ?_
    · intro h0
      rw [h0, norm_zero] at hu1
      exact zero_ne_one hu1
    · have := (mem_cell.1 hy).2 i
      rwa [hji, Prod.fst_neg, Prod.snd_neg, neg_dotProduct, neg_le_neg_iff] at this
  · intro C' hC' hKC' hCQ hdisj'
    obtain ⟨L, hL, hsub⟩ :=
      exists_params_subset_cell (fun i ↦ (hK i).2.2) hM0 hM hC' hKC' hCQ hdisj'
    exact (Finset.sum_le_sum fun i _ ↦ measure_mono (hsub i)).trans (isMaxOn_iff.1 hmax L hL)

end PlaneConvex
