module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Order.Zorn

/-!
# Lattice packings of centrally symmetric convex disks (Reinhardt's lemma)

Let `L ⊆ ℝ²` be a lattice and `K` a compact convex set, symmetric about the origin, with `0` in its
interior, whose translates `K + l`, `l ∈ L`, have pairwise disjoint interiors. Then `K` lies in a
centrally symmetric convex set `C` whose translates by `L` still have disjoint interiors and which
is cut out by two or three strips `|⟨a, x⟩| ≤ 1` (a parallelogram or a centrally symmetric
hexagon): `PlaneLattice.exists_halfLatticeFree_eq_strips`. This is Reinhardt's lemma in the form
"`K` lies in a parallelogram or centrally symmetric hexagon `H` with `area(H) ≤ det(L)`"
(`PlaneLattice.volume_real_le_covolume`).

## Proof

For centrally symmetric convex `C`, the translates by `L` have disjoint interiors iff no point `m`
of `½L \ {0}` is interior to `C` (`HalfLatticeFree`; `halfLatticeFree_of_isPacking`,
`isPacking_of_halfLatticeFree`). Such sets have area at most `det(L)` (Blichfeldt), hence are
uniformly bounded once they contain a fixed ball, and Zorn's lemma gives a maximal one `C ⊇ K`
(`exists_maximal`). Let `P = C ∩ ½L \ {0}` (finite, on the boundary of `C`).

* (Enlargement, `subset_of_maximal`) A closed centrally symmetric convex `Q ⊇ C` with no point of
  `P` in its interior equals `C`: otherwise `Q ∩ (1 + ε) C` is a larger admissible set.
* (Edges, `exists_uniq_of_edge`) If a support line `{⟨f, x⟩ = 1}` of `C` meets `C` in two points,
  some `m ∈ P` has it as its only support line: otherwise choose at each `m ∈ P` a support line
  other than `±f`; the strips they bound form such a `Q`, so they cut out `C`, but the midpoint of
  the two points lies strictly inside all of them.
* (Corners, `exists_uniq_abs_eq_one`) Every `c ∈ P` lies on such a support line `{|⟨f, x⟩| = 1}`
  with `f` the only support line at some `m ∈ P`: at a corner choose a support line touching `C`
  only at `c`; the strips cut out `C`, so another strip is tight at `c`, and it is an edge.
* Hence `C` is cut out by the strips of the functionals `f` that are the only support line at a
  point of `P` (`eq_iInter_strips`). For two such functionals `f ≠ ±f'`, at `m, m'`, the triangle
  `0, m, m'` contains no other point of `½L` (its other points are interior to `C`), so `m, m'` is a
  basis of `½L` (`isHalfBasis_of_uniq`). Four vectors pairwise forming bases do not exist
  (`false_of_four`), so there are at most three such functionals up to sign.

No Euler characteristic or angle count is needed.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Pointwise

namespace PlaneLattice

/-! ### Linear functionals of the plane -/

theorem dotProduct_two (a x : Fin 2 → ℝ) : a ⬝ᵥ x = a 0 * x 0 + a 1 * x 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- Cramer's rule in the plane. -/
theorem cramer (u v x : Fin 2 → ℝ) :
    (u 0 * v 1 - u 1 * v 0) • x = (x 0 * v 1 - x 1 * v 0) • u + (u 0 * x 1 - u 1 * x 0) • v := by
  ext i; fin_cases i <;> simp <;> ring

/-- Two linear functionals agreeing on two independent vectors are equal. -/
theorem eq_of_dotProduct_eq {a b x y : Fin 2 → ℝ} (hxy : x 0 * y 1 - x 1 * y 0 ≠ 0)
    (hx : a ⬝ᵥ x = b ⬝ᵥ x) (hy : a ⬝ᵥ y = b ⬝ᵥ y) : a = b := by
  rw [dotProduct_two, dotProduct_two] at hx hy
  have h0 : (a 0 - b 0) * (x 0 * y 1 - x 1 * y 0) = 0 := by
    linear_combination y 1 * hx - x 1 * hy
  have h1 : (a 1 - b 1) * (x 0 * y 1 - x 1 * y 0) = 0 := by
    linear_combination x 0 * hy - y 0 * hx
  have e0 := (mul_eq_zero.1 h0).resolve_right hxy
  have e1 := (mul_eq_zero.1 h1).resolve_right hxy
  ext i; fin_cases i
  · simp only [Fin.zero_eta]; linarith
  · simp only [Fin.mk_one]; linarith

/-- Two distinct points on a line `⟨f, x⟩ = 1` are linearly independent. -/
theorem det_ne_zero_of_dotProduct_eq_one {f x y : Fin 2 → ℝ} (hx : f ⬝ᵥ x = 1)
    (hy : f ⬝ᵥ y = 1) (hxy : x ≠ y) : x 0 * y 1 - x 1 * y 0 ≠ 0 := by
  intro h
  rw [dotProduct_two] at hx hy
  apply hxy
  have e0 : y 0 - x 0 = 0 := by
    linear_combination (-(y 0 - x 0)) * hx + x 0 * (hy - hx) - f 1 * h
  have e1 : y 1 - x 1 = 0 := by
    linear_combination (-(y 1 - x 1)) * hx + x 1 * (hy - hx) + f 0 * h
  ext i; fin_cases i
  · simp only [Fin.zero_eta]; linarith
  · simp only [Fin.mk_one]; linarith

/-- A nonzero functional has a nonzero kernel vector. -/
theorem dotProduct_kernel (a : Fin 2 → ℝ) : a ⬝ᵥ ![a 1, -a 0] = 0 := by
  rw [dotProduct_two]; simp; ring

theorem kernel_ne_zero {a : Fin 2 → ℝ} (ha : a ≠ 0) : (![a 1, -a 0] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  apply ha
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp at h0 h1
  ext i; fin_cases i
  · simpa using h1
  · simpa using h0

/-- From an interior point one can move a little in any direction. -/
theorem exists_add_smul_mem_of_mem_interior {S : Set (Fin 2 → ℝ)} {x : Fin 2 → ℝ}
    (hx : x ∈ interior S) (v : Fin 2 → ℝ) : ∃ t : ℝ, 0 < t ∧ x + t • v ∈ S := by
  have hc : Continuous fun t : ℝ ↦ x + t • v := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • v ∈ S :=
    hc.continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 hx)
  obtain ⟨t, htS, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  exact ⟨t, ht, htS⟩

/-- A point where a functional bounded by `1` on `Q` equals `1` is not interior to `Q`. -/
theorem notMem_interior_of_dotProduct {Q : Set (Fin 2 → ℝ)} {a x : Fin 2 → ℝ}
    (hQ : ∀ y ∈ Q, a ⬝ᵥ y ≤ 1) (hx : a ⬝ᵥ x = 1) : x ∉ interior Q := by
  intro hxi
  obtain ⟨t, ht, hmem⟩ := exists_add_smul_mem_of_mem_interior hxi x
  have := hQ _ hmem
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hx] at this
  linarith

theorem notMem_interior_of_abs_dotProduct {Q : Set (Fin 2 → ℝ)} {a x : Fin 2 → ℝ}
    (hQ : ∀ y ∈ Q, |a ⬝ᵥ y| ≤ 1) (hx : |a ⬝ᵥ x| = 1) : x ∉ interior Q := by
  intro hxi
  obtain ⟨t, ht, hmem⟩ := exists_add_smul_mem_of_mem_interior hxi x
  have := hQ _ hmem
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul,
    show a ⬝ᵥ x + t * (a ⬝ᵥ x) = (1 + t) * (a ⬝ᵥ x) by ring, abs_mul, hx,
    abs_of_pos (by linarith)] at this
  linarith

/-- A support line at a non-interior point of a convex set with `0` in its interior. -/
theorem exists_support {C : Set (Fin 2 → ℝ)} (hC : Convex ℝ C)
    (h0 : (0 : Fin 2 → ℝ) ∈ interior C) {x : Fin 2 → ℝ} (hx : x ∉ interior C) :
    ∃ a : Fin 2 → ℝ, (∀ y ∈ C, a ⬝ᵥ y ≤ 1) ∧ a ⬝ᵥ x = 1 := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hC.interior isOpen_interior hx
  have hfC : ∀ y ∈ C, f y ≤ f x := by
    intro y hy
    have hy' : y ∈ closure (interior C) := by
      rw [hC.closure_interior_eq_closure_of_nonempty_interior ⟨0, h0⟩]
      exact subset_closure hy
    exact closure_minimal (fun a ha ↦ (hf a ha).le)
      (isClosed_le f.continuous continuous_const) hy'
  have hpos : 0 < f x := by simpa using hf 0 h0
  have hrep : ∀ y : Fin 2 → ℝ, f y = ![f (Pi.single 0 1), f (Pi.single 1 1)] ⬝ᵥ y := by
    intro y
    have hy : y = y 0 • (Pi.single 0 1 : Fin 2 → ℝ) + y 1 • Pi.single 1 1 := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [hy]
    rw [map_add, map_smul, map_smul, dotProduct_two]
    simp only [smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  refine ⟨(f x)⁻¹ • ![f (Pi.single 0 1), f (Pi.single 1 1)], fun y hy ↦ ?_, ?_⟩
  · rw [smul_dotProduct, ← hrep, smul_eq_mul, inv_mul_le_iff₀ hpos, mul_one]
    exact hfC y hy
  · rw [smul_dotProduct, ← hrep, smul_eq_mul, inv_mul_cancel₀ hpos.ne']

theorem neg_mem_interior {S : Set (Fin 2 → ℝ)} (hS : ∀ x ∈ S, -x ∈ S) {x : Fin 2 → ℝ}
    (hx : x ∈ interior S) : -x ∈ interior S := by
  have hU : IsOpen {y : Fin 2 → ℝ | -y ∈ interior S} := isOpen_interior.preimage continuous_neg
  refine interior_maximal (fun y hy ↦ ?_) hU (by simpa using hx)
  simpa using hS _ (interior_subset hy)

theorem interior_image_add_right (S : Set (Fin 2 → ℝ)) (l : Fin 2 → ℝ) :
    interior ((fun x ↦ x + l) '' S) = (fun x ↦ x + l) '' interior S := by
  rw [show (fun x : Fin 2 → ℝ ↦ x + l) = ⇑(Homeomorph.addRight l) from rfl,
    ← Homeomorph.image_interior]

/-- A convex combination `a x + b y` (`a, b ≥ 0`, `a + b ≤ 1`) of points of a convex set
containing `0`. -/
theorem smul_add_smul_mem {C : Set (Fin 2 → ℝ)} (hC : Convex ℝ C) (h0 : (0 : Fin 2 → ℝ) ∈ C)
    {x y : Fin 2 → ℝ} (hx : x ∈ C) (hy : y ∈ C) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) : a • x + b • y ∈ C := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simpa [ha0, hb0] using h0
  · have hz : (a / (a + b)) • x + (b / (a + b)) • y ∈ C :=
      hC hx hy (div_nonneg ha h.le) (div_nonneg hb h.le) (by field_simp)
    have := hC.smul_mem_of_zero_mem h0 hz ⟨h.le, hab⟩
    convert this using 1
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h.ne', mul_div_cancel₀ _ h.ne']

/-! ### Packings and half-lattice points -/

/-- The translates `S + l`, `l ∈ L`, have pairwise disjoint interiors. -/
def IsPacking (L : Submodule ℤ (Fin 2 → ℝ)) (S : Set (Fin 2 → ℝ)) : Prop :=
  ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' →
    Disjoint (interior ((fun x ↦ x + l) '' S)) (interior ((fun x ↦ x + l') '' S))

/-- No point `m ≠ 0` of `½ L` lies in the interior of `C`. -/
def HalfLatticeFree (L : Submodule ℤ (Fin 2 → ℝ)) (C : Set (Fin 2 → ℝ)) : Prop :=
  ∀ m : Fin 2 → ℝ, m ≠ 0 → (2 : ℝ) • m ∈ L → m ∉ interior C

theorem halfLatticeFree_of_isPacking {L : Submodule ℤ (Fin 2 → ℝ)} {C : Set (Fin 2 → ℝ)}
    (hCs : ∀ x ∈ C, -x ∈ C) (hP : IsPacking L C) : HalfLatticeFree L C := by
  intro m hm hmL hmi
  have hne : (0 : Fin 2 → ℝ) ≠ (2 : ℝ) • m := by
    intro h; apply hm
    have := congrArg (fun z ↦ (1 / 2 : ℝ) • z) h
    simp only [smul_zero, smul_smul] at this
    norm_num at this
    exact this.symm
  have h1 : m ∈ interior ((fun x ↦ x + 0) '' C) := by simpa using hmi
  have h2 : m ∈ interior ((fun x ↦ x + (2 : ℝ) • m) '' C) := by
    rw [interior_image_add_right]
    refine ⟨-m, neg_mem_interior hCs hmi, ?_⟩
    simp only
    rw [two_smul]; abel
  exact Set.disjoint_left.1 (hP 0 (zero_mem _) _ hmL hne) h1 h2

theorem isPacking_of_halfLatticeFree {L : Submodule ℤ (Fin 2 → ℝ)} {C : Set (Fin 2 → ℝ)}
    (hCc : Convex ℝ C) (hCs : ∀ x ∈ C, -x ∈ C) (hC : HalfLatticeFree L C) : IsPacking L C := by
  intro l hl l' hl' hne
  rw [Set.disjoint_left]
  intro y hy1 hy2
  rw [interior_image_add_right] at hy1 hy2
  obtain ⟨x, hx, rfl⟩ := hy1
  obtain ⟨x', hx', hxx⟩ := hy2
  have hm := hCc.interior hx (neg_mem_interior hCs hx') (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have heq : x' = x + l - l' := by simp only at hxx; rw [← hxx]; abel
  refine hC ((1 / 2 : ℝ) • (l' - l)) ?_ ?_ ?_
  · intro h
    apply hne
    have := congrArg (fun z ↦ (2 : ℝ) • z) h
    simp only [smul_zero, smul_smul] at this
    norm_num at this
    exact (sub_eq_zero.1 this).symm
  · rw [smul_smul]; norm_num; exact sub_mem hl' hl
  · convert hm using 1
    rw [heq]; module

/-! ### Area -/

/-- **Blichfeldt**: a convex compact set whose lattice translates have disjoint interiors has
area at most the covolume of the lattice. -/
theorem volume_real_le_covolume (L : Submodule ℤ (Fin 2 → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] {H : Set (Fin 2 → ℝ)} (hHc : Convex ℝ H) (hP : IsPacking L H) :
    volume.real H ≤ ZLattice.covolume L := by
  set b := Module.Free.chooseBasis ℤ L
  have fund := ZLattice.isAddFundamentalDomain b volume
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume fund]
  have : MeasurableVAdd L (Fin 2 → ℝ) := (inferInstance : MeasurableVAdd L.toAddSubgroup _)
  have : VAddInvariantMeasure L (Fin 2 → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup _ volume)
  have hle : volume (interior H) ≤ volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨x, y, hxy, hnd⟩ := exists_pair_mem_lattice_not_disjoint_vadd fund
      isOpen_interior.measurableSet.nullMeasurableSet hlt
    apply hnd
    have e : ∀ g : L, g +ᵥ interior H = interior ((fun z ↦ z + (g : Fin 2 → ℝ)) '' H) := by
      intro g
      rw [interior_image_add_right, ← Set.image_vadd]
      congr 1
      funext z
      rw [Submodule.vadd_def, vadd_eq_add, add_comm]
    rw [e, e]
    exact hP x x.2 y y.2 (fun h ↦ hxy (Subtype.ext h))
  have hfin : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hH : volume H ≤ volume (interior H) := by
    calc volume H ≤ volume (interior H ∪ frontier H) := by
          apply measure_mono
          rw [← closure_eq_interior_union_frontier]
          exact subset_closure
      _ ≤ volume (interior H) + volume (frontier H) := measure_union_le _ _
      _ = volume (interior H) := by rw [hHc.addHaar_frontier volume, add_zero]
  exact ENNReal.toReal_mono hfin (hH.trans hle)

/-- A centrally symmetric convex set containing `x` and `y` has area at least `|det(x, y)|`. -/
theorem ofReal_abs_det_le_volume {C : Set (Fin 2 → ℝ)} (hC : Convex ℝ C)
    (hCs : ∀ x ∈ C, -x ∈ C) {x y : Fin 2 → ℝ} (hx : x ∈ C) (hy : y ∈ C) :
    ENNReal.ofReal |x 0 * y 1 - x 1 * y 0| ≤ volume C := by
  have h0 : (0 : Fin 2 → ℝ) ∈ C := by
    have := hC hx (hCs x hx) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simpa using this
  set f := Matrix.toLin' !![x 0, y 0; x 1, y 1]
  have hf : ∀ v : Fin 2 → ℝ, f v = v 0 • x + v 1 • y := by
    intro v; ext i
    fin_cases i <;> simp [f, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  set S : Set (Fin 2 → ℝ) := Icc (fun _ ↦ -(1 / 2)) (fun _ ↦ 1 / 2)
  have hSC : f '' S ⊆ C := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hf]
    have h0' : -(1 / 2 : ℝ) ≤ v 0 ∧ v 0 ≤ 1 / 2 := ⟨hv.1 0, hv.2 0⟩
    have h1' : -(1 / 2 : ℝ) ≤ v 1 ∧ v 1 ≤ 1 / 2 := ⟨hv.1 1, hv.2 1⟩
    have key : ∀ (s : ℝ) (z : Fin 2 → ℝ), z ∈ C → s • z = |s| • (if 0 ≤ s then z else -z) ∧
        (if 0 ≤ s then z else -z) ∈ C := by
      intro s z hz
      split_ifs with hs
      · exact ⟨by rw [abs_of_nonneg hs], hz⟩
      · push Not at hs
        exact ⟨by rw [abs_of_neg hs, neg_smul, smul_neg, neg_neg], hCs z hz⟩
    obtain ⟨e0, m0⟩ := key (v 0) x hx
    obtain ⟨e1, m1⟩ := key (v 1) y hy
    rw [e0, e1]
    exact smul_add_smul_mem hC h0 m0 m1 (abs_nonneg _) (abs_nonneg _)
      (by cases abs_cases (v 0) <;> cases abs_cases (v 1) <;>
        linarith [h0'.1, h0'.2, h1'.1, h1'.2])
  have hvolS : volume S = 1 := by
    rw [Real.volume_Icc_pi]
    simp
    norm_num
  calc ENNReal.ofReal |x 0 * y 1 - x 1 * y 0| = volume (f '' S) := by
        rw [MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin', hvolS,
          mul_one, Matrix.det_fin_two_of]
        congr 2; ring
    _ ≤ volume C := measure_mono hSC

/-- Admissible sets containing the ball `closedBall 0 r` are uniformly bounded. -/
theorem norm_le_of_halfLatticeFree (L : Submodule ℤ (Fin 2 → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] {C : Set (Fin 2 → ℝ)} (hCc : Convex ℝ C) (hCk : IsCompact C)
    (hCs : ∀ x ∈ C, -x ∈ C) (hCL : HalfLatticeFree L C) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall 0 r ⊆ C) {x : Fin 2 → ℝ} (hx : x ∈ C) :
    ‖x‖ ≤ ZLattice.covolume L / r := by
  have hV := volume_real_le_covolume L hCc (isPacking_of_halfLatticeFree hCc hCs hCL)
  have hfin : volume C ≠ ⊤ := hCk.measure_lt_top.ne
  have hy0 : (![0, r] : Fin 2 → ℝ) ∈ C := hball (by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hr.le]
    intro i; fin_cases i <;> simp [abs_of_pos hr, hr.le])
  have hy1 : (![r, 0] : Fin 2 → ℝ) ∈ C := hball (by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hr.le]
    intro i; fin_cases i <;> simp [abs_of_pos hr, hr.le])
  have e0 := (ENNReal.ofReal_le_iff_le_toReal hfin).1 (ofReal_abs_det_le_volume hCc hCs hx hy0)
  have e1 := (ENNReal.ofReal_le_iff_le_toReal hfin).1 (ofReal_abs_det_le_volume hCc hCs hx hy1)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, sub_zero, zero_sub,
    abs_neg, abs_mul, abs_of_pos hr] at e0 e1
  change _ ≤ volume.real C at e0 e1
  have hcov : 0 ≤ ZLattice.covolume L := measureReal_nonneg.trans hV
  rw [pi_norm_le_iff_of_nonneg (div_nonneg hcov hr.le)]
  intro i; fin_cases i
  · simp only [Fin.zero_eta, Real.norm_eq_abs]; rw [le_div_iff₀ hr]; linarith
  · simp only [Fin.mk_one, Real.norm_eq_abs]; rw [le_div_iff₀ hr]; linarith

/-! ### A maximal admissible set -/

/-- The compact convex centrally symmetric sets containing `K` with no point of `½ L \ {0}` in
their interior (equivalently, whose `L`-translates do not overlap). -/
def admissibleBodies (L : Submodule ℤ (Fin 2 → ℝ)) (K : Set (Fin 2 → ℝ)) :
    Set (Set (Fin 2 → ℝ)) :=
  {C | Convex ℝ C ∧ IsCompact C ∧ K ⊆ C ∧ (∀ x ∈ C, -x ∈ C) ∧ HalfLatticeFree L C}

/-- A maximal admissible set containing `K` (Zorn's lemma; chains are bounded since admissible
sets have area at most `det(L)`). -/
theorem exists_maximal (L : Submodule ℤ (Fin 2 → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {K : Set (Fin 2 → ℝ)} (hK : K ∈ admissibleBodies L K)
    (hK0 : (0 : Fin 2 → ℝ) ∈ interior K) :
    ∃ C, K ⊆ C ∧ Maximal (· ∈ admissibleBodies L K) C := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior 0 hK0
  have hball' : Metric.closedBall (0 : Fin 2 → ℝ) (r / 2) ⊆ K := fun x hx ↦
    interior_subset (hball (by
      rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hx; linarith))
  have hbd : ∀ C ∈ admissibleBodies L K,
      C ⊆ Metric.closedBall 0 (ZLattice.covolume L / (r / 2)) := fun C hC x hx ↦ by
    rw [mem_closedBall_zero_iff]
    exact norm_le_of_halfLatticeFree L hC.1 hC.2.1 hC.2.2.2.1 hC.2.2.2.2 (by positivity)
      (hball'.trans hC.2.2.1) hx
  refine zorn_subset_nonempty _ (fun c hcS hchain hne ↦ ?_) K hK
  set U := ⋃₀ c
  have hUc : Convex ℝ U := hchain.directedOn.convex_sUnion (fun A hA ↦ (hcS hA).1)
  obtain ⟨A0, hA0⟩ := hne
  have hKU : K ⊆ U := (hcS hA0).2.2.1.trans (subset_sUnion_of_mem hA0)
  have hUb : U ⊆ Metric.closedBall 0 (ZLattice.covolume L / (r / 2)) :=
    sUnion_subset fun A hA ↦ hbd A (hcS hA)
  have h0U : (0 : Fin 2 → ℝ) ∈ interior U := interior_mono hKU hK0
  refine ⟨closure U, ⟨hUc.closure, ?_, hKU.trans subset_closure, ?_, ?_⟩,
    fun A hA ↦ (subset_sUnion_of_mem hA).trans subset_closure⟩
  · exact (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure
      (closure_minimal hUb Metric.isClosed_closedBall)
  · intro x hx
    refine map_mem_closure continuous_neg hx (fun y hy ↦ ?_)
    obtain ⟨A, hA, hyA⟩ := hy
    exact ⟨A, hA, (hcS hA).2.2.2.1 y hyA⟩
  · intro m hm hmL hmi
    rw [hUc.interior_closure_eq_interior_of_nonempty_interior ⟨0, h0U⟩] at hmi
    obtain ⟨t, ht, hmt⟩ := exists_add_smul_mem_of_mem_interior hmi m
    obtain ⟨A, hA, hmA⟩ := hmt
    have h0A : (0 : Fin 2 → ℝ) ∈ interior A := interior_mono (hcS hA).2.2.1 hK0
    have := (hcS hA).1.combo_self_interior_mem_interior hmA h0A (a := 1 / (1 + t))
      (b := t / (1 + t)) (by positivity) (by positivity) (by field_simp)
    apply (hcS hA).2.2.2.2 m hm hmL
    convert this using 1
    rw [smul_zero, add_zero, smul_add, smul_smul]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp

section Maximal

variable {L : Submodule ℤ (Fin 2 → ℝ)} {K C : Set (Fin 2 → ℝ)}

/-- The points of `½ L \ {0}` in `C`. -/
def halfPoints (L : Submodule ℤ (Fin 2 → ℝ)) (C : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  {m | m ≠ 0 ∧ (2 : ℝ) • m ∈ L ∧ m ∈ C}

theorem finite_halfLattice_closedBall [DiscreteTopology L] (R : ℝ) :
    (Metric.closedBall (0 : Fin 2 → ℝ) R ∩ {m | (2 : ℝ) • m ∈ L}).Finite := by
  have hfin := Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 2 * R))
    L.toAddSubgroup.isClosed_of_discreteTopology
  refine (hfin.image (fun l ↦ (1 / 2 : ℝ) • l)).subset ?_
  rintro m ⟨hmR, hmL⟩
  refine ⟨(2 : ℝ) • m, ⟨?_, hmL⟩, ?_⟩
  · rw [mem_closedBall_zero_iff] at hmR ⊢
    rw [norm_smul, Real.norm_two]; linarith
  · simp only [smul_smul]; norm_num

theorem halfPoints_finite [DiscreteTopology L] (hCk : IsCompact C) :
    (halfPoints L C).Finite := by
  obtain ⟨R, hR⟩ := hCk.isBounded.subset_closedBall 0
  exact (finite_halfLattice_closedBall (L := L) R).subset fun m hm ↦ ⟨hR hm.2.2, hm.2.1⟩

/-- Enlarging `C` by a factor `1 + ε` adds no point of `½ L`. -/
theorem exists_eps [DiscreteTopology L] (hCk : IsCompact C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m : Fin 2 → ℝ, (2 : ℝ) • m ∈ L → (1 + ε)⁻¹ • m ∈ C → m ∈ C := by
  obtain ⟨R, hR⟩ := hCk.isBounded.subset_closedBall 0
  set F := Metric.closedBall (0 : Fin 2 → ℝ) (2 * R) ∩ {m | (2 : ℝ) • m ∈ L}
  have hF : F.Finite := finite_halfLattice_closedBall _
  have hev : ∀ m ∈ F, ∀ᶠ ε in 𝓝 (0 : ℝ), m ∈ C ∨ (1 + ε)⁻¹ • m ∉ C := by
    intro m _
    by_cases hmC : m ∈ C
    · exact Eventually.of_forall fun _ ↦ Or.inl hmC
    · have hc : ContinuousAt (fun ε : ℝ ↦ (1 + ε)⁻¹ • m) 0 :=
        ((continuousAt_const.add continuousAt_id).inv₀ (by norm_num)).smul continuousAt_const
      have : ∀ᶠ ε in 𝓝 (0 : ℝ), (1 + ε)⁻¹ • m ∈ Cᶜ :=
        hc.preimage_mem_nhds (hCk.isClosed.isOpen_compl.mem_nhds (by simpa using hmC))
      exact this.mono fun _ h ↦ Or.inr h
  have hall := (eventually_all_finite hF).2 hev
  have hlt : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 := eventually_lt_nhds (by norm_num)
  obtain ⟨ε, ⟨h1, h2⟩, hε⟩ := (((hall.and hlt).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  refine ⟨ε, hε, fun m hmL hmC ↦ ?_⟩
  have hε' : (0 : ℝ) < 1 + ε := by linarith [show (0 : ℝ) < ε from hε]
  have hmF : m ∈ F := by
    refine ⟨?_, hmL⟩
    have := hR hmC
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε',
      inv_mul_le_iff₀ hε'] at this
    have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (mem_closedBall_zero_iff.1 (hR hmC))
    rw [mem_closedBall_zero_iff]
    nlinarith
  rcases h1 m hmF with h | h
  · exact h
  · exact absurd hmC h

/-- **Enlargement.** A closed centrally symmetric convex set `Q ⊇ C` with no point of
`½ L \ {0}` of `C` in its interior is contained in `C`, when `C` is maximal. -/
theorem subset_of_maximal [DiscreteTopology L] (hmax : Maximal (· ∈ admissibleBodies L K) C)
    (h0 : (0 : Fin 2 → ℝ) ∈ interior C) {Q : Set (Fin 2 → ℝ)} (hQc : Convex ℝ Q)
    (hQcl : IsClosed Q) (hQs : ∀ x ∈ Q, -x ∈ Q) (hCQ : C ⊆ Q)
    (hP : ∀ m ∈ halfPoints L C, m ∉ interior Q) : Q ⊆ C := by
  obtain ⟨hCc, hCk, hKC, hCs, hCL⟩ := hmax.1
  have h0C : (0 : Fin 2 → ℝ) ∈ C := interior_subset h0
  have hstar : ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • x ∈ C :=
    fun x hx t ht0 ht1 ↦ hCc.smul_mem_of_zero_mem h0C hx ⟨ht0, ht1⟩
  obtain ⟨ε, hε, hεC⟩ := exists_eps (L := L) hCk
  set S := {x : Fin 2 → ℝ | (1 + ε)⁻¹ • x ∈ C}
  have hCS : C ⊆ S := fun x hx ↦
    hstar x hx _ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
  have hmemS : Q ∩ S ∈ admissibleBodies L K := by
    refine ⟨hQc.inter ?_, ?_, hKC.trans (subset_inter hCQ hCS), ?_, ?_⟩
    · intro x hx y hy a b ha hb hab
      change (1 + ε)⁻¹ • (a • x + b • y) ∈ C
      rw [smul_add, smul_comm _ a, smul_comm _ b]
      exact hCc hx hy ha hb hab
    · have himg : IsCompact ((fun x ↦ (1 + ε) • x) '' C) :=
        hCk.image (continuous_const_smul _)
      refine himg.of_isClosed_subset
        (hQcl.inter (hCk.isClosed.preimage (continuous_const_smul _))) ?_
      rintro x ⟨-, hx⟩
      refine ⟨(1 + ε)⁻¹ • x, hx, ?_⟩
      simp only [smul_smul]
      rw [mul_inv_cancel₀ (by positivity), one_smul]
    · rintro x ⟨hxQ, hxS⟩
      refine ⟨hQs x hxQ, ?_⟩
      change (1 + ε)⁻¹ • -x ∈ C
      rw [smul_neg]; exact hCs _ hxS
    · intro m hm hmL hmi
      have hmC : m ∈ C := hεC m hmL (interior_subset hmi).2
      exact hP m ⟨hm, hmL, hmC⟩ (interior_mono inter_subset_left hmi)
  have hsub : Q ∩ S ⊆ C := hmax.2 hmemS (subset_inter hCQ hCS)
  intro z hz
  by_contra hzC
  -- the last point of `C` on the segment `[0, z]`
  set T := {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ t • z ∈ C}
  have hTcl : IsClosed T :=
    isClosed_Icc.inter (hCk.isClosed.preimage (continuous_id.smul continuous_const))
  have hTne : T.Nonempty := ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa using h0C⟩
  have hTbdd : BddAbove T := ⟨1, fun t ht ↦ ht.1.2⟩
  have hsT : sSup T ∈ T := hTcl.csSup_mem hTne hTbdd
  set s := sSup T
  have hs1 : s < 1 := by
    rcases eq_or_lt_of_le hsT.1.2 with h | h
    · exfalso; apply hzC; have := hsT.2; rwa [h, one_smul] at this
    · exact h
  have hs0 : 0 < s := by
    obtain ⟨t, ht, htz⟩ := exists_add_smul_mem_of_mem_interior h0 z
    rw [zero_add] at htz
    have hmin : min t 1 ∈ T := ⟨⟨le_min ht.le zero_le_one, min_le_right _ _⟩, by
      have := hstar _ htz (min t 1 / t) (by positivity) (div_le_one_of_le₀ (min_le_left _ _) ht.le)
      rwa [smul_smul, div_mul_cancel₀ _ ht.ne'] at this⟩
    exact lt_of_lt_of_le (lt_min ht one_pos) (le_csSup hTbdd hmin)
  set t₁ := min 1 (s * (1 + ε))
  have ht₁s : s < t₁ := lt_min hs1 (by nlinarith)
  have ht₁0 : 0 ≤ t₁ := le_min zero_le_one (by positivity)
  have hy : t₁ • z ∈ Q ∩ S := by
    refine ⟨hQc.smul_mem_of_zero_mem (hCQ h0C) hz ⟨ht₁0, min_le_left _ _⟩, ?_⟩
    change (1 + ε)⁻¹ • t₁ • z ∈ C
    have hc : (1 + ε)⁻¹ * t₁ / s ≤ 1 := by
      rw [div_le_one hs0, inv_mul_le_iff₀ (by linarith)]
      calc t₁ ≤ s * (1 + ε) := min_le_right _ _
        _ = (1 + ε) * s := by ring
    have := hstar _ hsT.2 ((1 + ε)⁻¹ * t₁ / s) (by positivity) hc
    rwa [smul_smul, div_mul_cancel₀ _ hs0.ne', ← smul_smul] at this
  have ht₁T : t₁ ∈ T := ⟨⟨ht₁0, min_le_left _ _⟩, hsub hy⟩
  exact absurd (le_csSup hTbdd ht₁T) (not_le.2 ht₁s)

theorem continuous_dotProduct_left (a : Fin 2 → ℝ) :
    Continuous fun z : Fin 2 → ℝ ↦ a ⬝ᵥ z := by
  simp_rw [dotProduct_two]; fun_prop

/-- Strips of support functionals, one tight at each point of `½ L \ {0}` in `C`, cut out the
maximal set `C`. -/
theorem strips_subset [DiscreteTopology L] (hmax : Maximal (· ∈ admissibleBodies L K) C)
    (h0 : (0 : Fin 2 → ℝ) ∈ interior C) {F : Set (Fin 2 → ℝ)}
    (hF : ∀ f ∈ F, ∀ z ∈ C, f ⬝ᵥ z ≤ 1)
    (hcov : ∀ m ∈ halfPoints L C, ∃ f ∈ F, |f ⬝ᵥ m| = 1) :
    {z | ∀ f ∈ F, |f ⬝ᵥ z| ≤ 1} ⊆ C := by
  obtain ⟨hCc, hCk, hKC, hCs, hCL⟩ := hmax.1
  apply subset_of_maximal hmax h0
  · intro x hx y hy a b ha hb hab f hf
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    calc |a * (f ⬝ᵥ x) + b * (f ⬝ᵥ y)| ≤ |a * (f ⬝ᵥ x)| + |b * (f ⬝ᵥ y)| := abs_add_le _ _
      _ = a * |f ⬝ᵥ x| + b * |f ⬝ᵥ y| := by rw [abs_mul, abs_mul, abs_of_nonneg ha,
          abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := by gcongr <;> [exact hx f hf; exact hy f hf]
      _ = 1 := by rw [mul_one, mul_one, hab]
  · have : {z : Fin 2 → ℝ | ∀ f ∈ F, |f ⬝ᵥ z| ≤ 1} = ⋂ f ∈ F, {z | |f ⬝ᵥ z| ≤ 1} := by
      ext; simp
    rw [this]
    exact isClosed_biInter fun f _ ↦
      isClosed_le (continuous_dotProduct_left f).abs continuous_const
  · intro x hx f hf
    rw [dotProduct_neg, abs_neg]; exact hx f hf
  · intro z hz f hf
    have h1 := hF f hf z hz
    have h2 := hF f hf (-z) (hCs z hz)
    rw [dotProduct_neg] at h2
    exact abs_le.2 ⟨by linarith, h1⟩
  · intro m hm
    obtain ⟨f, hf, hfm⟩ := hcov m hm
    exact notMem_interior_of_abs_dotProduct (fun y hy ↦ hy f hf) hfm

/-- `f` is a support functional of `C` (`⟨f, x⟩ ≤ 1` on `C`), equal to `1` at `m`, and the only
one. -/
def IsUniqSupport (C : Set (Fin 2 → ℝ)) (m f : Fin 2 → ℝ) : Prop :=
  (∀ z ∈ C, f ⬝ᵥ z ≤ 1) ∧ f ⬝ᵥ m = 1 ∧ ∀ g, (∀ z ∈ C, g ⬝ᵥ z ≤ 1) → g ⬝ᵥ m = 1 → g = f

theorem neg_mem_halfPoints (hCs : ∀ x ∈ C, -x ∈ C) {m : Fin 2 → ℝ}
    (hm : m ∈ halfPoints L C) : -m ∈ halfPoints L C :=
  ⟨neg_ne_zero.2 hm.1, by rw [smul_neg]; exact neg_mem hm.2.1, hCs m hm.2.2⟩

/-- **Edges.** If a support line of the maximal set `C` meets it in two points, it is the only
support line at some point of `½ L \ {0}`. -/
theorem exists_uniq_of_edge [DiscreteTopology L] (hmax : Maximal (· ∈ admissibleBodies L K) C)
    (h0 : (0 : Fin 2 → ℝ) ∈ interior C) {f x y : Fin 2 → ℝ} (hf : ∀ z ∈ C, f ⬝ᵥ z ≤ 1)
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) (hfx : f ⬝ᵥ x = 1) (hfy : f ⬝ᵥ y = 1) :
    ∃ m ∈ halfPoints L C, IsUniqSupport C m f := by
  obtain ⟨hCc, hCk, hKC, hCs, hCL⟩ := hmax.1
  by_contra hno
  push Not at hno
  have hg : ∀ m ∈ halfPoints L C, ∃ g : Fin 2 → ℝ, (∀ z ∈ C, g ⬝ᵥ z ≤ 1) ∧ g ⬝ᵥ m = 1 ∧
      g ≠ f ∧ g ≠ -f := by
    intro m hm
    obtain ⟨a, ha, ham⟩ := exists_support hCc h0 (hCL m hm.1 hm.2.1)
    by_cases h1 : f ⬝ᵥ m = 1
    · have := hno m hm
      simp only [IsUniqSupport, not_and, not_forall] at this
      obtain ⟨g, hg, hgm, hgf⟩ := this hf h1
      refine ⟨g, hg, hgm, hgf, ?_⟩
      rintro rfl; rw [neg_dotProduct, h1] at hgm; norm_num at hgm
    · by_cases h2 : f ⬝ᵥ m = -1
      · have := hno (-m) (neg_mem_halfPoints hCs hm)
        simp only [IsUniqSupport, not_and, not_forall] at this
        obtain ⟨g', hg', hgm', hgf'⟩ := this hf (by rw [dotProduct_neg, h2, neg_neg])
        refine ⟨-g', fun z hz ↦ ?_, ?_, ?_, ?_⟩
        · rw [neg_dotProduct, ← dotProduct_neg]; exact hg' _ (hCs z hz)
        · rw [neg_dotProduct, ← dotProduct_neg]; exact hgm'
        · intro h; apply h1; rw [← h, neg_dotProduct, ← dotProduct_neg]; exact hgm'
        · intro h; exact hgf' (neg_inj.1 h)
      · refine ⟨a, ha, ham, ?_, ?_⟩
        · rintro rfl; exact h1 ham
        · rintro rfl; apply h2; rw [neg_dotProduct] at ham; linarith
  choose! g hgsup hgm hgf hgnf using hg
  have hsub := strips_subset hmax h0 (F := g '' halfPoints L C)
    (by rintro _ ⟨m, hm, rfl⟩; exact hgsup m hm)
    (fun m hm ↦ ⟨g m, ⟨m, hm, rfl⟩, by rw [hgm m hm, abs_one]⟩)
  set w := (1 / 2 : ℝ) • (x + y)
  have hwC : w ∈ C := by
    have := hCc hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simpa [w, smul_add] using this
  have hfw : f ⬝ᵥ w = 1 := by
    simp only [w, dotProduct_smul, dotProduct_add, hfx, hfy, smul_eq_mul]; norm_num
  have hdet := det_ne_zero_of_dotProduct_eq_one hfx hfy hxy
  have hstrict : ∀ m ∈ halfPoints L C, |g m ⬝ᵥ w| < 1 := by
    intro m hm
    have hgx := hgsup m hm x hx
    have hgy := hgsup m hm y hy
    have hgx' := hgsup m hm (-x) (hCs x hx)
    have hgy' := hgsup m hm (-y) (hCs y hy)
    rw [dotProduct_neg] at hgx' hgy'
    have hgw : g m ⬝ᵥ w = (g m ⬝ᵥ x + g m ⬝ᵥ y) / 2 := by
      simp only [w, dotProduct_smul, dotProduct_add, smul_eq_mul]; ring
    rw [abs_lt, hgw]
    constructor
    · by_contra hc
      push Not at hc
      have e1 : g m ⬝ᵥ x = -1 := by linarith
      have e2 : g m ⬝ᵥ y = -1 := by linarith
      apply hgnf m hm
      have := eq_of_dotProduct_eq hdet (a := -g m) (b := f)
        (by rw [neg_dotProduct, e1, hfx]; norm_num) (by rw [neg_dotProduct, e2, hfy]; norm_num)
      rw [← this, neg_neg]
    · by_contra hc
      push Not at hc
      have e1 : g m ⬝ᵥ x = 1 := by linarith
      have e2 : g m ⬝ᵥ y = 1 := by linarith
      exact hgf m hm (eq_of_dotProduct_eq hdet (by rw [e1, hfx]) (by rw [e2, hfy]))
  have hopen : IsOpen {z : Fin 2 → ℝ | ∀ m ∈ halfPoints L C, |g m ⬝ᵥ z| < 1} := by
    have : {z : Fin 2 → ℝ | ∀ m ∈ halfPoints L C, |g m ⬝ᵥ z| < 1} =
        ⋂ m ∈ halfPoints L C, {z | |g m ⬝ᵥ z| < 1} := by ext; simp
    rw [this]
    exact (halfPoints_finite hCk).isOpen_biInter fun m _ ↦
      isOpen_lt (continuous_dotProduct_left _).abs continuous_const
  have hwi : w ∈ interior C := by
    refine interior_maximal (fun z hz ↦ hsub ?_) hopen hstrict
    rintro _ ⟨m, hm, rfl⟩
    exact (hz m hm).le
  exact notMem_interior_of_dotProduct hf hfw hwi

/-- **Corners.** Every point `c` of `½ L \ {0}` in the maximal set `C` lies on a line
`|⟨f, x⟩| = 1` where `f` is the only support functional at some point of `½ L \ {0}`. -/
theorem exists_uniq_abs_eq_one [DiscreteTopology L]
    (hmax : Maximal (· ∈ admissibleBodies L K) C) (h0 : (0 : Fin 2 → ℝ) ∈ interior C)
    {c : Fin 2 → ℝ} (hc : c ∈ halfPoints L C) :
    ∃ f, (∃ m ∈ halfPoints L C, IsUniqSupport C m f) ∧ |f ⬝ᵥ c| = 1 := by
  obtain ⟨hCc, hCk, hKC, hCs, hCL⟩ := hmax.1
  by_cases hu : ∃ f, IsUniqSupport C c f
  · obtain ⟨f, hf⟩ := hu
    exact ⟨f, ⟨c, hc, hf⟩, by rw [hf.2.1, abs_one]⟩
  push Not at hu
  -- at each point a support functional which is unique or touches `C` only there
  have hφ : ∀ m ∈ halfPoints L C, ∃ φ : Fin 2 → ℝ, (∀ z ∈ C, φ ⬝ᵥ z ≤ 1) ∧ φ ⬝ᵥ m = 1 ∧
      (IsUniqSupport C m φ ∨ ∀ z ∈ C, φ ⬝ᵥ z = 1 → z = m) := by
    intro m hm
    by_cases hum : ∃ f, IsUniqSupport C m f
    · obtain ⟨f, hf⟩ := hum
      exact ⟨f, hf.1, hf.2.1, Or.inl hf⟩
    · push Not at hum
      obtain ⟨a, ha, ham⟩ := exists_support hCc h0 (hCL m hm.1 hm.2.1)
      have := hum a
      simp only [IsUniqSupport, not_and, not_forall] at this
      obtain ⟨b, hb, hbm, hba⟩ := this ha ham
      refine ⟨(1 / 2 : ℝ) • (a + b), fun z hz ↦ ?_, ?_, Or.inr fun z hz hz1 ↦ ?_⟩
      · rw [smul_dotProduct, add_dotProduct, smul_eq_mul]; linarith [ha z hz, hb z hz]
      · rw [smul_dotProduct, add_dotProduct, ham, hbm, smul_eq_mul]; norm_num
      · rw [smul_dotProduct, add_dotProduct, smul_eq_mul] at hz1
        have e1 : a ⬝ᵥ z = 1 := by linarith [ha z hz, hb z hz]
        have e2 : b ⬝ᵥ z = 1 := by linarith [ha z hz, hb z hz]
        by_contra hzm
        exact hba (eq_of_dotProduct_eq (det_ne_zero_of_dotProduct_eq_one ham e1 (Ne.symm hzm))
          (by rw [hbm, ham]) (by rw [e1, e2]))
  choose! φ hφsup hφm hφp using hφ
  have hsub := strips_subset hmax h0 (F := φ '' halfPoints L C)
    (by rintro _ ⟨m, hm, rfl⟩; exact hφsup m hm)
    (fun m hm ↦ ⟨φ m, ⟨m, hm, rfl⟩, by rw [hφm m hm, abs_one]⟩)
  have hface : ∀ z ∈ C, φ c ⬝ᵥ z = 1 → z = c := by
    rcases hφp c hc with h | h
    · exact absurd h (hu _)
    · exact h
  have hnc := neg_mem_halfPoints hCs hc
  -- another strip is tight at `c`
  have hex : ∃ m ∈ halfPoints L C, m ≠ c ∧ m ≠ -c ∧ |φ m ⬝ᵥ c| = 1 := by
    by_contra hno
    push Not at hno
    have hlt : ∀ m ∈ halfPoints L C, m ≠ c → m ≠ -c → |φ m ⬝ᵥ c| < 1 := by
      intro m hm h1 h2
      refine lt_of_le_of_ne (abs_le.2 ⟨?_, hφsup m hm c hc.2.2⟩) (hno m hm h1 h2)
      have := hφsup m hm (-c) (hCs c hc.2.2)
      rw [dotProduct_neg] at this; linarith
    have hφc0 : φ c ≠ 0 := by
      intro h; have := hφm c hc; rw [h, zero_dotProduct] at this; norm_num at this
    set d : Fin 2 → ℝ := ![φ c 1, -φ c 0]
    have hd0 : φ c ⬝ᵥ d = 0 := dotProduct_kernel _
    have hd : d ≠ 0 := kernel_ne_zero hφc0
    obtain ⟨e, he0, he1, hene⟩ : ∃ e : Fin 2 → ℝ, φ c ⬝ᵥ e = 0 ∧ 0 ≤ φ (-c) ⬝ᵥ e ∧ e ≠ 0 := by
      by_cases h : 0 ≤ φ (-c) ⬝ᵥ d
      · exact ⟨d, hd0, h, hd⟩
      · refine ⟨-d, by rw [dotProduct_neg, hd0, neg_zero], ?_, neg_ne_zero.2 hd⟩
        rw [dotProduct_neg]; linarith
    have hev1 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ m ∈ {m | m ∈ halfPoints L C ∧ m ≠ c ∧ m ≠ -c},
        |φ m ⬝ᵥ (c + t • e)| < 1 := by
      rw [eventually_all_finite ((halfPoints_finite hCk).subset
        (fun m (hm : m ∈ {m | m ∈ halfPoints L C ∧ m ≠ c ∧ m ≠ -c}) ↦ hm.1))]
      rintro m ⟨hm, h1, h2⟩
      have hcont : Continuous fun t : ℝ ↦ |φ m ⬝ᵥ (c + t • e)| := by
        simp_rw [dotProduct_add, dotProduct_smul, smul_eq_mul]; fun_prop
      exact hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hlt m hm h1 h2)
    have hev2 : ∀ᶠ t in 𝓝 (0 : ℝ), t * (φ (-c) ⬝ᵥ e) < 2 := by
      have hcont : Continuous fun t : ℝ ↦ t * (φ (-c) ⬝ᵥ e) := by fun_prop
      exact hcont.continuousAt.eventually_lt continuousAt_const (by simp)
    obtain ⟨t, ⟨ht1, ht2⟩, ht⟩ := (((hev1.and hev2).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
    have ht0 : (0 : ℝ) < t := ht
    have hmem : c + t • e ∈ C := by
      apply hsub
      rintro _ ⟨m, hm, rfl⟩
      by_cases h1 : m = c
      · rw [h1, dotProduct_add, dotProduct_smul, he0, hφm c hc]; simp
      · by_cases h2 : m = -c
        · rw [h2]
          have hφnc : φ (-c) ⬝ᵥ c = -1 := by
            have := hφm (-c) hnc; rw [dotProduct_neg] at this; linarith
          rw [dotProduct_add, dotProduct_smul, hφnc, smul_eq_mul, abs_le]
          constructor <;> nlinarith [mul_nonneg ht0.le he1]
        · exact (ht1 m ⟨hm, h1, h2⟩).le
    have := hface _ hmem (by rw [dotProduct_add, dotProduct_smul, he0, hφm c hc]; simp)
    apply hene
    have h' : t • e = 0 := by
      have := congrArg (fun z ↦ z - c) this; simpa using this
    exact (smul_eq_zero.1 h').resolve_left ht0.ne'
  obtain ⟨m, hm, hmc, hmnc, habs⟩ := hex
  rcases (abs_eq zero_le_one).1 habs with h | h
  · obtain ⟨m', hm', hu'⟩ := exists_uniq_of_edge hmax h0 (hφsup m hm) hm.2.2 hc.2.2 hmc
      (hφm m hm) h
    exact ⟨φ m, ⟨m', hm', hu'⟩, habs⟩
  · obtain ⟨m', hm', hu'⟩ := exists_uniq_of_edge hmax h0 (hφsup m hm) hm.2.2 (hCs c hc.2.2)
      hmnc (hφm m hm) (by rw [dotProduct_neg, h, neg_neg])
    exact ⟨φ m, ⟨m', hm', hu'⟩, habs⟩

/-- The functionals that are the only support functional at some point of `½ L \ {0}` in `C`. -/
def uniqSupports (L : Submodule ℤ (Fin 2 → ℝ)) (C : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  {f | ∃ m ∈ halfPoints L C, IsUniqSupport C m f}

/-- The maximal set `C` is cut out by the strips of its unique support functionals. -/
theorem eq_iInter_strips [DiscreteTopology L] (hmax : Maximal (· ∈ admissibleBodies L K) C)
    (h0 : (0 : Fin 2 → ℝ) ∈ interior C) :
    C = {z | ∀ f ∈ uniqSupports L C, |f ⬝ᵥ z| ≤ 1} := by
  obtain ⟨hCc, hCk, hKC, hCs, hCL⟩ := hmax.1
  refine Subset.antisymm (fun z hz f ⟨m, hm, hf⟩ ↦ abs_le.2 ⟨?_, hf.1 z hz⟩)
    (strips_subset hmax h0 (fun f ⟨m, hm, hf⟩ ↦ hf.1)
      (fun c hc ↦ exists_uniq_abs_eq_one hmax h0 hc))
  have := hf.1 (-z) (hCs z hz)
  rw [dotProduct_neg] at this; linarith

/-! ### Bases of `½ L` -/

/-- `m, m'` is a basis of `½ L`. -/
def IsHalfBasis (L : Submodule ℤ (Fin 2 → ℝ)) (m m' : Fin 2 → ℝ) : Prop :=
  m 0 * m' 1 - m 1 * m' 0 ≠ 0 ∧
    ∀ l : Fin 2 → ℝ, (2 : ℝ) • l ∈ L → ∃ a b : ℤ, l = (a : ℝ) • m + (b : ℝ) • m'

theorem IsHalfBasis.symm {m m' : Fin 2 → ℝ} (h : IsHalfBasis L m m') : IsHalfBasis L m' m := by
  refine ⟨fun h' ↦ h.1 (by linarith), fun l hl ↦ ?_⟩
  obtain ⟨a, b, e⟩ := h.2 l hl
  exact ⟨b, a, by rw [e, add_comm]⟩

theorem smul_mem_of_two_smul_mem {x : Fin 2 → ℝ} (hx : (2 : ℝ) • x ∈ L) (p : ℤ) :
    (2 : ℝ) • ((p : ℝ) • x) ∈ L := by
  rw [smul_comm, Int.cast_smul_eq_zsmul]; exact L.smul_mem p hx

/-- A lattice triangle `0, m, m'` with no other point of `½ L` gives a basis of `½ L`. -/
theorem isHalfBasis_of_triangle {m m' : Fin 2 → ℝ} (hm : (2 : ℝ) • m ∈ L)
    (hm' : (2 : ℝ) • m' ∈ L) (hdet : m 0 * m' 1 - m 1 * m' 0 ≠ 0)
    (htri : ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → α + β ≤ 1 → (2 : ℝ) • (α • m + β • m') ∈ L →
      (α = 0 ∧ β = 0) ∨ (α = 1 ∧ β = 0) ∨ (α = 0 ∧ β = 1)) :
    IsHalfBasis L m m' := by
  refine ⟨hdet, fun l hl ↦ ?_⟩
  set D := m 0 * m' 1 - m 1 * m' 0
  set a := (l 0 * m' 1 - l 1 * m' 0) / D
  set b := (m 0 * l 1 - m 1 * l 0) / D
  have hl_eq : l = a • m + b • m' := by
    have := cramer m m' l
    simp only [a, b]
    rw [div_eq_inv_mul, div_eq_inv_mul, ← smul_smul, ← smul_smul, ← smul_add, ← this,
      smul_smul, inv_mul_cancel₀ hdet, one_smul]
  have hmem : ∀ p q : ℤ, (2 : ℝ) • (l - (p : ℝ) • m - (q : ℝ) • m') ∈ L := by
    intro p q
    rw [smul_sub, smul_sub]
    exact sub_mem (sub_mem hl (smul_mem_of_two_smul_mem hm p))
      (smul_mem_of_two_smul_mem hm' q)
  have hfa := Int.fract_nonneg a
  have hfb := Int.fract_nonneg b
  have hfa1 := Int.fract_lt_one a
  have hfb1 := Int.fract_lt_one b
  have hl' : l - (⌊a⌋ : ℝ) • m - (⌊b⌋ : ℝ) • m' = Int.fract a • m + Int.fract b • m' := by
    rw [hl_eq, Int.fract, Int.fract]; module
  by_cases hsum : Int.fract a + Int.fract b ≤ 1
  · have h2 := hmem ⌊a⌋ ⌊b⌋
    rw [hl'] at h2
    rcases htri _ _ hfa hfb hsum h2 with ⟨h1, h2⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
    · refine ⟨⌊a⌋, ⌊b⌋, ?_⟩
      have := hl'
      rw [h1, h2, zero_smul, zero_smul, add_zero, sub_sub, sub_eq_zero] at this
      exact this
    · linarith
    · linarith
  · push Not at hsum
    have h2 : (2 : ℝ) • ((1 - Int.fract a) • m + (1 - Int.fract b) • m') ∈ L := by
      have e : (1 - Int.fract a) • m + (1 - Int.fract b) • m' =
          -(l - ((⌊a⌋ + 1 : ℤ) : ℝ) • m - ((⌊b⌋ + 1 : ℤ) : ℝ) • m') := by
        rw [hl_eq, Int.fract, Int.fract]; push_cast; module
      rw [e, smul_neg]
      exact neg_mem (hmem _ _)
    rcases htri _ _ (by linarith) (by linarith) (by linarith) h2 with
      ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h1, -⟩ <;> linarith

/-- Two points of `½ L \ {0}` with distinct (up to sign) unique support functionals form a basis
of `½ L`. -/
theorem isHalfBasis_of_uniq [DiscreteTopology L] (hmax : Maximal (· ∈ admissibleBodies L K) C)
    (h0 : (0 : Fin 2 → ℝ) ∈ interior C) {f f' m m' : Fin 2 → ℝ} (hm : m ∈ halfPoints L C)
    (hm' : m' ∈ halfPoints L C) (hf : IsUniqSupport C m f) (hf' : IsUniqSupport C m' f')
    (hne : f' ≠ f) (hne' : f' ≠ -f) : IsHalfBasis L m m' := by
  obtain ⟨hCc, hCk, hKC, hCs, hCL⟩ := hmax.1
  have hneg : ∀ g, (∀ z ∈ C, g ⬝ᵥ z ≤ 1) → ∀ z ∈ C, -1 ≤ g ⬝ᵥ z := by
    intro g hg z hz
    have := hg (-z) (hCs z hz); rw [dotProduct_neg] at this; linarith
  have hdet : m 0 * m' 1 - m 1 * m' 0 ≠ 0 := by
    intro hdet0
    have hfm := hf.2.1
    have hfm' := hf'.2.1
    rw [dotProduct_two] at hfm hfm'
    have e1 : m' = (f ⬝ᵥ m') • m := by
      ext i; fin_cases i <;> simp
      · linear_combination (-(m' 0)) * hfm - f 1 * hdet0
      · linear_combination (-(m' 1)) * hfm + f 0 * hdet0
    have e2 : m = (f' ⬝ᵥ m) • m' := by
      ext i; fin_cases i <;> simp
      · linear_combination (-(m 0)) * hfm' + f' 1 * hdet0
      · linear_combination (-(m 1)) * hfm' - f' 0 * hdet0
    set s := f ⬝ᵥ m'
    set s' := f' ⬝ᵥ m
    have hs1 := hf.1 m' hm'.2.2
    have hs2 := hneg f hf.1 m' hm'.2.2
    have hs1' := hf'.1 m hm.2.2
    have hs2' := hneg f' hf'.1 m hm.2.2
    have hss : s' * s = 1 := by
      have h3 : m = (s' * s) • m := by
        conv_lhs => rw [e2]
        rw [e1, smul_smul]
      have h4 : (s' * s - 1) • m = 0 := by rw [sub_smul, one_smul, ← h3, sub_self]
      have := (smul_eq_zero.1 h4).resolve_right hm.1
      linarith
    have hs : s = 1 ∨ s = -1 := by
      rcases le_or_gt 0 s with h | h
      · left; nlinarith
      · right; nlinarith
    rcases hs with h | h
    · apply hne
      refine hf.2.2 f' hf'.1 ?_
      rw [e2, dotProduct_smul, hf'.2.1, smul_eq_mul, mul_one]
      have : s' = 1 := by rw [h, mul_one] at hss; exact hss
      exact this
    · apply hne'
      have hneg' : -f' = f := by
        refine hf.2.2 (-f') (fun z hz ↦ ?_) ?_
        · rw [neg_dotProduct, ← dotProduct_neg]; exact hf'.1 _ (hCs z hz)
        · rw [neg_dotProduct]
          have : s' = -1 := by rw [h] at hss; linarith
          rw [show f' ⬝ᵥ m = s' from rfl, this, neg_neg]
      rw [← hneg', neg_neg]
  refine isHalfBasis_of_triangle hm.2.1 hm'.2.1 hdet fun α β hα hβ hαβ hmem ↦ ?_
  set x := α • m + β • m'
  by_cases hx0 : x = 0
  · left
    have e0 := congrFun hx0 0
    have e1 := congrFun hx0 1
    simp only [x, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e0 e1
    constructor
    · have : α * (m 0 * m' 1 - m 1 * m' 0) = 0 := by linear_combination m' 1 * e0 - m' 0 * e1
      exact (mul_eq_zero.1 this).resolve_right hdet
    · have : β * (m 0 * m' 1 - m 1 * m' 0) = 0 := by linear_combination m 0 * e1 - m 1 * e0
      exact (mul_eq_zero.1 this).resolve_right hdet
  have hxi : x ∉ interior C := hCL x hx0 hmem
  have hpos : 0 < α + β := by
    rcases eq_or_lt_of_le (add_nonneg hα hβ) with h | h
    · exfalso; apply hx0
      have ha : α = 0 := by linarith
      have hb : β = 0 := by linarith
      simp [x, ha, hb]
    · exact h
  rcases eq_or_lt_of_le hαβ with hs | hs
  · by_cases ha0 : α = 0
    · right; right; exact ⟨ha0, by linarith⟩
    by_cases hb0 : β = 0
    · right; left; exact ⟨by linarith, hb0⟩
    exfalso
    obtain ⟨g, hg, hgx⟩ := exists_support hCc h0 hxi
    have hgm := hg m hm.2.2
    have hgm' := hg m' hm'.2.2
    have hsum : α * (g ⬝ᵥ m) + β * (g ⬝ᵥ m') = 1 := by
      rw [← hgx]; simp [x, dotProduct_add, dotProduct_smul]
    have hα' : 0 < α := lt_of_le_of_ne hα (Ne.symm ha0)
    have hβ' : 0 < β := lt_of_le_of_ne hβ (Ne.symm hb0)
    have e1 : g ⬝ᵥ m = 1 := by nlinarith
    have e2 : g ⬝ᵥ m' = 1 := by nlinarith
    exact hne ((hf'.2.2 g hg e2).symm.trans (hf.2.2 g hg e1))
  · exfalso
    apply hxi
    have hq : (α / (α + β)) • m + (β / (α + β)) • m' ∈ C :=
      hCc hm.2.2 hm'.2.2 (div_nonneg hα hpos.le) (div_nonneg hβ hpos.le) (by field_simp)
    have := hCc.combo_self_interior_mem_interior hq h0 (a := α + β) (b := 1 - (α + β))
      hpos.le (by linarith) (by ring)
    convert this using 1
    rw [smul_zero, add_zero, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hpos.ne',
      mul_div_cancel₀ _ hpos.ne']

theorem det_eq_of_eq_comb {x u v w : Fin 2 → ℝ} {p q : ℝ} (h : x = p • u + q • v) :
    w 0 * x 1 - w 1 * x 0 = p * (w 0 * u 1 - w 1 * u 0) + q * (w 0 * v 1 - w 1 * v 0) := by
  subst h; simp; ring

/-- The coefficients of a basis vector in another basis sharing a vector are units. -/
theorem coeff_eq_one_or_neg_one {u v w : Fin 2 → ℝ} (h : IsHalfBasis L u v)
    (h' : IsHalfBasis L u w) (hv : (2 : ℝ) • v ∈ L) {a b : ℤ}
    (hw : w = (a : ℝ) • u + (b : ℝ) • v) : b = 1 ∨ b = -1 := by
  obtain ⟨c, d, hv'⟩ := h'.2 v hv
  have e1 := det_eq_of_eq_comb (w := u) hw
  have e2 := det_eq_of_eq_comb (w := u) hv'
  have huu : u 0 * u 1 - u 1 * u 0 = 0 := by ring
  rw [huu, mul_zero, zero_add] at e1 e2
  rw [e1] at e2
  have hdb : ((d * b : ℤ) : ℝ) = 1 := by
    have := h.1
    push_cast
    have h3 : (1 - (d : ℝ) * b) * (u 0 * v 1 - u 1 * v 0) = 0 := by linarith
    have := (mul_eq_zero.1 h3).resolve_right h.1
    linarith
  have hdb' : d * b = 1 := by exact_mod_cast hdb
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdb' with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

/-- Four vectors of `½ L` cannot pairwise form bases of `½ L`. -/
theorem false_of_four {m₁ m₂ m₃ m₄ : Fin 2 → ℝ} (h12 : IsHalfBasis L m₁ m₂)
    (h13 : IsHalfBasis L m₁ m₃) (h23 : IsHalfBasis L m₂ m₃) (h14 : IsHalfBasis L m₁ m₄)
    (h24 : IsHalfBasis L m₂ m₄) (h34 : IsHalfBasis L m₃ m₄) (hm₁ : (2 : ℝ) • m₁ ∈ L)
    (hm₂ : (2 : ℝ) • m₂ ∈ L) (hm₃ : (2 : ℝ) • m₃ ∈ L) (hm₄ : (2 : ℝ) • m₄ ∈ L) : False := by
  obtain ⟨a, b, e3⟩ := h12.2 m₃ hm₃
  obtain ⟨a', b', e4⟩ := h12.2 m₄ hm₄
  have hb := coeff_eq_one_or_neg_one h12 h13 hm₂ e3
  have ha := coeff_eq_one_or_neg_one h12.symm h23 hm₁ (by rw [e3, add_comm])
  have hb' := coeff_eq_one_or_neg_one h12 h14 hm₂ e4
  have ha' := coeff_eq_one_or_neg_one h12.symm h24 hm₁ (by rw [e4, add_comm])
  obtain ⟨e, e', e1⟩ := h34.2 m₁ hm₁
  -- `det(m₁, m₄) = e det(m₃, m₄)`
  have k1 : m₄ 0 * m₁ 1 - m₄ 1 * m₁ 0 =
      e * (m₄ 0 * m₃ 1 - m₄ 1 * m₃ 0) + e' * (m₄ 0 * m₄ 1 - m₄ 1 * m₄ 0) :=
    det_eq_of_eq_comb e1
  have k2 := det_eq_of_eq_comb (w := m₁) e4
  have k3 := det_eq_of_eq_comb (w := m₃) e4
  have k4 := det_eq_of_eq_comb (w := m₁) e3
  have k5 := det_eq_of_eq_comb (w := m₂) e3
  set D := m₁ 0 * m₂ 1 - m₁ 1 * m₂ 0
  have hD := h12.1
  have key : ((b' - e * (a * b' - b * a') : ℤ) : ℝ) * D = 0 := by
    push_cast
    have r1 : m₄ 0 * m₁ 1 - m₄ 1 * m₁ 0 = -(b' * D) := by
      rw [show m₄ 0 * m₁ 1 - m₄ 1 * m₁ 0 = -(m₁ 0 * m₄ 1 - m₁ 1 * m₄ 0) by ring, k2]; ring
    have r2 : m₄ 0 * m₃ 1 - m₄ 1 * m₃ 0 = -((a * b' - b * a') * D) := by
      rw [show m₄ 0 * m₃ 1 - m₄ 1 * m₃ 0 = -(m₃ 0 * m₄ 1 - m₃ 1 * m₄ 0) by ring, k3]
      rw [show m₃ 0 * m₁ 1 - m₃ 1 * m₁ 0 = -(m₁ 0 * m₃ 1 - m₁ 1 * m₃ 0) by ring, k4,
        show m₃ 0 * m₂ 1 - m₃ 1 * m₂ 0 = -(m₂ 0 * m₃ 1 - m₂ 1 * m₃ 0) by ring, k5]
      ring
    rw [r1, r2] at k1
    linear_combination -k1
  have key' : b' - e * (a * b' - b * a') = 0 := by
    have := (mul_eq_zero.1 key).resolve_right hD
    exact_mod_cast this
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases ha' with rfl | rfl <;>
    rcases hb' with rfl | rfl <;> omega

end Maximal

/-! ### Reinhardt's lemma -/

/-- **Reinhardt's lemma.** Let `L` be a lattice in the plane and `K` a compact convex set,
symmetric about `0` with `0` in its interior, whose `L`-translates do not overlap (no point of
`½ L \ {0}` is interior to `K`). Then `K` lies in a compact convex centrally symmetric set `C`
whose `L`-translates do not overlap and which is a parallelogram `|⟨a, x⟩|, |⟨b, x⟩| ≤ 1` or the
intersection of three strips `|⟨a, x⟩|, |⟨b, x⟩|, |⟨c, x⟩| ≤ 1` (`a, b` independent). -/
theorem exists_halfLatticeFree_eq_strips (L : Submodule ℤ (Fin 2 → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] {K : Set (Fin 2 → ℝ)} (hKc : Convex ℝ K) (hKk : IsCompact K)
    (hK0 : (0 : Fin 2 → ℝ) ∈ interior K) (hKs : ∀ x ∈ K, -x ∈ K)
    (hKL : HalfLatticeFree L K) :
    ∃ C : Set (Fin 2 → ℝ), Convex ℝ C ∧ IsCompact C ∧ K ⊆ C ∧ (∀ x ∈ C, -x ∈ C) ∧
      HalfLatticeFree L C ∧ ∃ a b : Fin 2 → ℝ, a 0 * b 1 - a 1 * b 0 ≠ 0 ∧
        (C = {x | |a ⬝ᵥ x| ≤ 1 ∧ |b ⬝ᵥ x| ≤ 1} ∨
          ∃ c : Fin 2 → ℝ, C = {x | |a ⬝ᵥ x| ≤ 1 ∧ |b ⬝ᵥ x| ≤ 1 ∧ |c ⬝ᵥ x| ≤ 1}) := by
  obtain ⟨C, hKC, hmax⟩ := exists_maximal L ⟨hKc, hKk, subset_rfl, hKs, hKL⟩ hK0
  obtain ⟨hCc, hCk, -, hCs, hCL⟩ := hmax.1
  have h0 : (0 : Fin 2 → ℝ) ∈ interior C := interior_mono hKC hK0
  refine ⟨C, hCc, hCk, hKC, hCs, hCL, ?_⟩
  have hrep := eq_iInter_strips hmax h0
  set F := uniqSupports L C
  obtain ⟨R, hR⟩ := hCk.isBounded.subset_closedBall 0
  have hunb : ∀ d : Fin 2 → ℝ, d ≠ 0 → (∀ t : ℝ, t • d ∈ C) → False := by
    intro d hd ht
    have := hR (ht ((|R| + 1) / ‖d‖))
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < |R| + 1), abs_norm,
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hd)] at this
    linarith [le_abs_self R]
  have hstrip : ∀ f₁ ∈ F, (∀ f ∈ F, f = f₁ ∨ f = -f₁) → False := by
    intro f₁ hf₁ hall
    obtain ⟨m, hm, hu⟩ := hf₁
    have hf₁0 : f₁ ≠ 0 := by
      intro h; have := hu.2.1; rw [h, zero_dotProduct] at this; norm_num at this
    apply hunb _ (kernel_ne_zero hf₁0) (fun t ↦ ?_)
    rw [hrep]
    intro f hf
    rcases hall f hf with rfl | rfl
    · rw [dotProduct_smul, dotProduct_kernel]; simp
    · rw [neg_dotProduct, dotProduct_smul, dotProduct_kernel]; simp
  obtain ⟨f₁, hf₁⟩ : F.Nonempty := by
    by_contra hF
    rw [not_nonempty_iff_eq_empty] at hF
    apply hunb (![1, 0]) (by intro h; have := congrFun h 0; simp at this) (fun t ↦ ?_)
    rw [hrep, hF]; simp
  obtain ⟨f₂, hf₂, h21, h21'⟩ : ∃ f₂ ∈ F, f₂ ≠ f₁ ∧ f₂ ≠ -f₁ := by
    by_contra hno
    push Not at hno
    exact hstrip f₁ hf₁ fun f hf ↦ by
      by_cases h : f = f₁
      · exact Or.inl h
      · exact Or.inr (hno f hf h)
  obtain ⟨m₁, hm₁, hu₁⟩ := hf₁
  obtain ⟨m₂, hm₂, hu₂⟩ := hf₂
  -- `f₁, f₂` are independent
  have hdet : f₁ 0 * f₂ 1 - f₁ 1 * f₂ 0 ≠ 0 := by
    intro h
    have hneg : ∀ g, (∀ z ∈ C, g ⬝ᵥ z ≤ 1) → ∀ z ∈ C, -1 ≤ g ⬝ᵥ z := by
      intro g hg z hz
      have := hg (-z) (hCs z hz); rw [dotProduct_neg] at this; linarith
    have hm1 := hu₁.2.1
    rw [dotProduct_two] at hm1
    have e : f₂ = (f₂ ⬝ᵥ m₁) • f₁ := by
      ext i; fin_cases i <;> simp
      · linear_combination (-(f₂ 0)) * hm1 - m₁ 1 * h
      · linear_combination (-(f₂ 1)) * hm1 + m₁ 0 * h
    set s := f₂ ⬝ᵥ m₁
    have hs1 := hu₂.1 m₁ hm₁.2.2
    have hs2 := hneg f₂ hu₂.1 m₁ hm₁.2.2
    have h2 := hu₂.2.1
    rw [e, smul_dotProduct, smul_eq_mul] at h2
    have h3 := hu₁.1 m₂ hm₂.2.2
    have h4 := hneg f₁ hu₁.1 m₂ hm₂.2.2
    have hs : s = 1 ∨ s = -1 := by
      rcases le_or_gt 0 s with h' | h'
      · left; nlinarith
      · right; nlinarith
    rcases hs with h' | h'
    · exact h21 (by rw [e, h', one_smul])
    · exact h21' (by rw [e, h', neg_one_smul])
  refine ⟨f₁, f₂, hdet, ?_⟩
  by_cases h3 : ∃ f₃ ∈ F, f₃ ≠ f₁ ∧ f₃ ≠ -f₁ ∧ f₃ ≠ f₂ ∧ f₃ ≠ -f₂
  · obtain ⟨f₃, ⟨m₃, hm₃, hu₃⟩, h31, h31', h32, h32'⟩ := h3
    have hall : ∀ f ∈ F, f = f₁ ∨ f = -f₁ ∨ f = f₂ ∨ f = -f₂ ∨ f = f₃ ∨ f = -f₃ := by
      intro f ⟨m₄, hm₄, hu₄⟩
      by_contra hno
      push Not at hno
      obtain ⟨h41, h41', h42, h42', h43, h43'⟩ := hno
      exact false_of_four (isHalfBasis_of_uniq hmax h0 hm₁ hm₂ hu₁ hu₂ h21 h21')
        (isHalfBasis_of_uniq hmax h0 hm₁ hm₃ hu₁ hu₃ h31 h31')
        (isHalfBasis_of_uniq hmax h0 hm₂ hm₃ hu₂ hu₃ h32 h32')
        (isHalfBasis_of_uniq hmax h0 hm₁ hm₄ hu₁ hu₄ h41 h41')
        (isHalfBasis_of_uniq hmax h0 hm₂ hm₄ hu₂ hu₄ h42 h42')
        (isHalfBasis_of_uniq hmax h0 hm₃ hm₄ hu₃ hu₄ h43 h43')
        hm₁.2.1 hm₂.2.1 hm₃.2.1 hm₄.2.1
    right
    refine ⟨f₃, ?_⟩
    rw [hrep]
    ext z
    simp only [mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨h f₁ ⟨m₁, hm₁, hu₁⟩, h f₂ ⟨m₂, hm₂, hu₂⟩, h f₃ ⟨m₃, hm₃, hu₃⟩⟩
    · rintro ⟨g1, g2, g3⟩ f hf
      rcases hall f hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | assumption | (simp only [neg_dotProduct, abs_neg]; assumption)
  · push Not at h3
    left
    rw [hrep]
    ext z
    simp only [mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨h f₁ ⟨m₁, hm₁, hu₁⟩, h f₂ ⟨m₂, hm₂, hu₂⟩⟩
    · rintro ⟨g1, g2⟩ f hf
      by_cases e1 : f = f₁
      · rw [e1]; exact g1
      by_cases e2 : f = -f₁
      · rw [e2, neg_dotProduct, abs_neg]; exact g1
      by_cases e3 : f = f₂
      · rw [e3]; exact g2
      rw [h3 f hf e1 e2 e3, neg_dotProduct, abs_neg]; exact g2

end PlaneLattice
