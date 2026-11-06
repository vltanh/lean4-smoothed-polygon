module

public import Basic.Analysis.Convex.CellDecomposition.Defs
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# The structure of the holes of a family of cells with the rotation property

Part (B) of the cell lemma (`Basic.Analysis.Convex.CellDecomposition`): let `Q` be a bounded
convex polygon and `C 0, …, C (n-1)`, `n ≥ 1`, non-overlapping convex polygons in `Q` with the
*rotation property* (`PlaneConvex.pin_HasRotationProperty`, a consequence of the maximality of the
total area). Then every hole `H = closure U` (`U` a connected component of `Q \ ⋃ C i`) lies in
`interior Q`, is convex, and every extreme point of `H` is a side point of some cell
(`PlaneConvex.hole_structure`; in fact every point of `H \ U` is, `hole_Cfg.sidePoint_of_mem_H`).
This is the core of Böröczky's Lemma 5 (pinwheel holes); it gives
`PlaneConvex.pin_hole_structure_of_rotation` in `PinwheelHoles`.

The first section collects results moved here from `PinwheelHoles` (unchanged), which this file
needs.

## The argument

Write `J` for the quarter turn `hole_rot o` (`o = ±1` fixes an orientation). A *state*
`(i, q, u)` (`hole_Cfg.IsState`) is a side `[q, q + L u]` of the cell `C i`, traversed from its
first endpoint `q` in the direction `u`, with `C i` on the right (`⟨J u, x - q⟩ ≤ 0` on `C i`) and
the hole `U` on the left near `q` (a thin triangle `hole_tri o q (q + T u) ε` over the beginning of
the side lies in `U`).

* *Rotation lemma* (`hole_Cfg.rotation_contra`): a whole side `[q, q']` of a cell cannot have a
  thin triangle over it inside `Q \ ⋃ C j`: the point `y` above its midpoint violates only the
  constraint of that side, and `conv ({y} ∪ [q, q'])` meets no other cell, contradicting the
  rotation property.
* *Darts* (`hole_Cfg.IsState.dart`): the side of a state is bordered by `U` from `q` up to the
  first point `q' = q + T u` where another cell touches it; by the rotation lemma `q'` lies in the
  relative interior of the side, so `q'` is a side point of `C i`.
* *Sweep* (`hole_Cfg.sweep`): at a point `z` of `H`, turning from a direction into `U` towards a
  direction into a cell, the first cell met gives a state at `z`. At the end `q'` of a dart this
  gives a new state starting at `q'` (`hole_Cfg.IsState.next`).
* *Counting* (`hole_Cfg.star`): the end point of the dart of a state determines the state
  (`hole_Cfg.end_inj`: the cell with a side point at `q'` and the side are determined by `q'`).
  So `state ↦ end point` is an injection from the finite set of states into the set of base
  points of states which are side points; hence every base point of a state is a side point.
* *Consequences.* Every point of `H` in a cell is a side point of some cell
  (`hole_Cfg.sidePoint_of_mem`; otherwise the sweep gives a state at a non-side point). A point of
  `H ∩ ∂Q` is never a side point, so no cell meets `H ∩ ∂Q`; then `H` contains a neighbourhood of
  each of its points on `∂Q` in `Q`, so `∂Q ⊆ H` (`∂Q` is connected), and the lexicographically
  largest point of the cells would be a point of `H` in a cell which is not a side point. Hence
  `H ⊆ interior Q`, `U` is open, and `U` is convex: a segment of `H` leaving `U` at a side point of
  a cell would enter the interior of that cell.

Departure from the paper: Böröczky counts segment ends around the boundary cycles of `H` (each
boundary segment on a side of a cell has an end in the relative interior of that side, by the
rotation lemma; at a corner at most one of the two segment ends does) and excludes pinched
corners, a cycle along `∂Q` and islands of cells by turning. We keep the two local facts and
replace the boundary cycles by the injectivity of `state ↦ end of its dart`, which needs no
Jordan-curve or turning argument; convexity comes from the connectedness of the open set `U`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PlaneConvex

/-! ### Results moved from `PinwheelHoles` -/

theorem pin_convex_of_isConvexPolygon {P : Set (Fin 2 → ℝ)} (hP : IsConvexPolygon P) :
    Convex ℝ P := by
  obtain ⟨⟨k, a, c, rfl⟩, -, -⟩ := hP
  exact convex_halfPlanesInter a c

theorem pin_isClosed_of_isConvexPolygon {P : Set (Fin 2 → ℝ)} (hP : IsConvexPolygon P) :
    IsClosed P := by
  obtain ⟨⟨k, a, c, rfl⟩, -, -⟩ := hP
  exact isClosed_halfPlanesInter a c

/-- The frontier of an intersection of half-planes lies on the lines with nonzero normal. -/
theorem pin_frontier_halfPlanesInter_subset {ι : Type*} [Finite ι] (a : ι → Fin 2 → ℝ)
    (c : ι → ℝ) : frontier (halfPlanesInter a c) ⊆ ⋃ l, ⋃ (_ : a l ≠ 0), {x | a l ⬝ᵥ x = c l} := by
  intro p hp
  have hpS : p ∈ halfPlanesInter a c := (isClosed_halfPlanesInter a c).frontier_subset hp
  by_contra hcon
  simp only [mem_iUnion, mem_ofPred_eq, not_exists] at hcon
  apply hp.2
  set O := ⋂ l, {x : Fin 2 → ℝ | a l ≠ 0 → a l ⬝ᵥ x < c l}
  have hO : IsOpen O := by
    refine isOpen_iInter_of_finite fun l ↦ ?_
    by_cases hl : a l = 0
    · have : {x : Fin 2 → ℝ | a l ≠ 0 → a l ⬝ᵥ x < c l} = univ := by ext; simp [hl]
      rw [this]; exact isOpen_univ
    · have : {x : Fin 2 → ℝ | a l ≠ 0 → a l ⬝ᵥ x < c l} = {x | a l ⬝ᵥ x < c l} := by
        ext; simp [hl]
      rw [this]; exact isOpen_lt (by fun_prop) continuous_const
  have hOS : O ⊆ halfPlanesInter a c := by
    intro x hx l
    by_cases hl : a l = 0
    · have := hpS l
      simp only [hl, zero_dotProduct] at this ⊢
      exact this
    · exact (mem_iInter.1 hx l hl).le
  have hpO : p ∈ O := mem_iInter.2 fun l hl ↦ lt_of_le_of_ne (hpS l) (hcon l hl)
  exact mem_interior.2 ⟨O, hOS, hO, hpO⟩

/-- A point of a cell is not in the interior of another cell. -/
theorem pin_inter_interior_eq_empty {n : ℕ} {C : Fin n → Set (Fin 2 → ℝ)}
    (hC : ∀ i, IsConvexPolygon (C i)) (hdisj : NonOverlapping C) {i j : Fin n} (hij : i ≠ j) :
    C i ∩ interior (C j) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzi, hzj⟩
  have hcl : z ∈ closure (interior (C i)) := by
    rw [(pin_convex_of_isConvexPolygon (hC i)).closure_interior_eq_closure_of_nonempty_interior
      (hC i).2.2]
    exact subset_closure hzi
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hcl _ isOpen_interior hzj
  exact Set.disjoint_left.1 (hdisj hij) hw2 hw1

/-- The *rotation property* of a family of cells in `Q`: if a point `y ∈ Q` violates exactly one
constraint `l` of a cell `C i = halfPlanesInter a c` (so that `conv (C i ∪ {y})` adds to `C i` the
triangle-like set `conv (S ∪ {y})` over the side `S = C i ∩ {⟨a l, x⟩ = c l}`), then the interior of
some other cell meets `conv (S ∪ {y})`. Rotating the side `S` outwards about one of its endpoints
is the case where `y` lies on the line of the adjacent side. -/
def pin_HasRotationProperty {n : ℕ} (Q : Set (Fin 2 → ℝ)) (C : Fin n → Set (Fin 2 → ℝ)) :
    Prop :=
  ∀ i, ∀ {k : ℕ} (a : Fin k → Fin 2 → ℝ) (c : Fin k → ℝ), C i = halfPlanesInter a c →
    ∀ l, ∀ y ∈ Q, c l < a l ⬝ᵥ y → (∀ m, m ≠ l → a m ⬝ᵥ y ≤ c m) →
      ∃ j, j ≠ i ∧ (interior (C j) ∩
        convexHull ℝ (insert y (C i ∩ {x | a l ⬝ᵥ x = c l}))).Nonempty

/-- **Local cone structure of a polygon.** Near a point `p` of `halfPlanesInter a c`, only the
constraints active at `p` matter. -/
theorem pin_local_cone {ι : Type*} [Finite ι] (a : ι → Fin 2 → ℝ) (c : ι → ℝ) {p : Fin 2 → ℝ}
    (hp : p ∈ halfPlanesInter a c) :
    ∃ r > 0, ∀ x ∈ Metric.ball p r,
      (x ∈ halfPlanesInter a c ↔ ∀ l, a l ⬝ᵥ p = c l → a l ⬝ᵥ (x - p) ≤ 0) := by
  set O := ⋂ l, {x : Fin 2 → ℝ | a l ⬝ᵥ p < c l → a l ⬝ᵥ x < c l}
  have hO : IsOpen O := by
    refine isOpen_iInter_of_finite fun l ↦ ?_
    by_cases hl : a l ⬝ᵥ p < c l
    · have : {x : Fin 2 → ℝ | a l ⬝ᵥ p < c l → a l ⬝ᵥ x < c l} = {x | a l ⬝ᵥ x < c l} := by
        ext x; simp only [mem_ofPred_eq]; exact ⟨fun h ↦ h hl, fun h _ ↦ h⟩
      rw [this]; exact isOpen_lt (by fun_prop) continuous_const
    · have : {x : Fin 2 → ℝ | a l ⬝ᵥ p < c l → a l ⬝ᵥ x < c l} = univ := by
        ext x; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact fun h ↦ absurd h hl
      rw [this]; exact isOpen_univ
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO p (mem_iInter.2 fun l h ↦ h)
  refine ⟨r, hr, fun x hx ↦ ⟨fun hxP l hl ↦ ?_, fun h l ↦ ?_⟩⟩
  · rw [dotProduct_sub, hl]; linarith [hxP l]
  · by_cases hl : a l ⬝ᵥ p = c l
    · have := h l hl
      rw [dotProduct_sub, hl] at this
      linarith
    · exact (mem_iInter.1 (hrO hx) l (lt_of_le_of_ne (hp l) hl)).le

/-- A scaled point stays in the ball. -/
theorem pin_mem_ball_scale {p x : Fin 2 → ℝ} {r t : ℝ} (hx : x ∈ Metric.ball p r) (ht : 0 < t)
    (ht1 : t ≤ 1) : p + t • (x - p) ∈ Metric.ball p r := by
  rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  calc t * ‖x - p‖ ≤ 1 * ‖x - p‖ := mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
    _ < r := by rw [one_mul]; exact hx

/-- An intersection of half-planes is conic near any point. -/
theorem pin_conic_halfPlanesInter {ι : Type*} [Finite ι] (a : ι → Fin 2 → ℝ) (c : ι → ℝ)
    (p : Fin 2 → ℝ) : ∃ r > 0, ∀ x ∈ Metric.ball p r, ∀ t : ℝ, 0 < t → t ≤ 1 →
      (x ∈ halfPlanesInter a c ↔ p + t • (x - p) ∈ halfPlanesInter a c) := by
  by_cases hp : p ∈ halfPlanesInter a c
  · obtain ⟨r, hr, hcone⟩ := pin_local_cone a c hp
    refine ⟨r, hr, fun x hx t ht ht1 ↦ ?_⟩
    rw [hcone x hx, hcone _ (pin_mem_ball_scale hx ht ht1)]
    simp only [add_sub_cancel_left, dotProduct_smul, smul_eq_mul]
    refine forall_congr' fun l ↦ imp_congr_right fun _ ↦ ?_
    constructor
    · intro h; nlinarith
    · intro h
      by_contra h'
      push Not at h'
      nlinarith
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isClosed_halfPlanesInter a c).isOpen_compl p hp
    refine ⟨r, hr, fun x hx t ht ht1 ↦ ?_⟩
    exact iff_of_false (hball hx) (hball (pin_mem_ball_scale hx ht ht1))

/-! ### Planar vector algebra -/

/-- The quarter turn `v ↦ o • (-v₁, v₀)`; for `o = 1` it is counterclockwise, for `o = -1`
clockwise. -/
def hole_rot (o : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ := ![-(o * v 1), o * v 0]

section Vec

variable {o : ℝ}

@[simp] lemma hole_rot_zero_apply (v : Fin 2 → ℝ) : hole_rot o v 0 = -(o * v 1) := rfl

@[simp] lemma hole_rot_one_apply (v : Fin 2 → ℝ) : hole_rot o v 1 = o * v 0 := rfl

lemma hole_dot2 (v w : Fin 2 → ℝ) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 := by
  simp [dotProduct, Fin.sum_univ_two]

lemma hole_ext2 {v w : Fin 2 → ℝ} (h0 : v 0 = w 0) (h1 : v 1 = w 1) : v = w := by
  ext i; fin_cases i
  · exact h0
  · exact h1

lemma hole_rot_add (v w : Fin 2 → ℝ) : hole_rot o (v + w) = hole_rot o v + hole_rot o w :=
  hole_ext2 (by simp; ring) (by simp; ring)

lemma hole_rot_sub (v w : Fin 2 → ℝ) : hole_rot o (v - w) = hole_rot o v - hole_rot o w :=
  hole_ext2 (by simp; ring) (by simp; ring)

lemma hole_rot_smul (s : ℝ) (v : Fin 2 → ℝ) : hole_rot o (s • v) = s • hole_rot o v :=
  hole_ext2 (by simp; ring) (by simp; ring)

lemma hole_rot_neg (v : Fin 2 → ℝ) : hole_rot o (-v) = -hole_rot o v :=
  hole_ext2 (by simp) (by simp)

lemma hole_rot_neg_o (v : Fin 2 → ℝ) : hole_rot (-o) v = -hole_rot o v :=
  hole_ext2 (by simp) (by simp)

lemma hole_rot_rot (ho : o * o = 1) (v : Fin 2 → ℝ) : hole_rot o (hole_rot o v) = -v :=
  hole_ext2 (by simp; linear_combination (v 0) * ho) (by simp; linear_combination (v 1) * ho)

lemma hole_rot_dot_self (v : Fin 2 → ℝ) : hole_rot o v ⬝ᵥ v = 0 := by
  rw [hole_dot2]; simp; ring

lemma hole_dot_rot_self (v : Fin 2 → ℝ) : v ⬝ᵥ hole_rot o v = 0 := by
  rw [hole_dot2]; simp; ring

lemma hole_rot_dot_rot (ho : o * o = 1) (v w : Fin 2 → ℝ) :
    hole_rot o v ⬝ᵥ hole_rot o w = v ⬝ᵥ w := by
  rw [hole_dot2, hole_dot2]; simp; linear_combination (v 1 * w 1 + v 0 * w 0) * ho

lemma hole_rot_dot_comm (v w : Fin 2 → ℝ) : hole_rot o v ⬝ᵥ w = -(v ⬝ᵥ hole_rot o w) := by
  rw [hole_dot2, hole_dot2]; simp; ring

lemma hole_dot_self_pos {v : Fin 2 → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  rw [hole_dot2]
  by_contra h
  apply hv
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  exact hole_ext2 (by simpa using h0) (by simpa using h1)

lemma hole_o_ne_zero (ho : o * o = 1) : o ≠ 0 := by
  rintro rfl; simp at ho

lemma hole_rot_ne_zero (ho : o * o = 1) {v : Fin 2 → ℝ} (hv : v ≠ 0) : hole_rot o v ≠ 0 := by
  intro h
  have := hole_rot_dot_rot ho v v
  rw [h, zero_dotProduct] at this
  exact (hole_dot_self_pos hv).ne this

lemma hole_rot_dot_rot_self_pos (ho : o * o = 1) {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    0 < hole_rot o v ⬝ᵥ hole_rot o v := by
  rw [hole_rot_dot_rot ho]; exact hole_dot_self_pos hv

/-- Two vectors orthogonal to the same nonzero vector `d` are parallel. -/
lemma hole_cross_eq_zero {d n v : Fin 2 → ℝ} (hd : d ≠ 0) (hn : n ⬝ᵥ d = 0) (hv : v ⬝ᵥ d = 0) :
    n 0 * v 1 - n 1 * v 0 = 0 := by
  rw [hole_dot2] at hn hv
  by_cases h0 : d 0 = 0
  · have h1 : d 1 ≠ 0 := fun h1 ↦ hd (hole_ext2 (by simpa using h0) (by simpa using h1))
    have : (n 0 * v 1 - n 1 * v 0) * d 1 = 0 := by linear_combination (-v 0) * hn + n 0 * hv
    exact (mul_eq_zero.1 this).resolve_right h1
  · have : (n 0 * v 1 - n 1 * v 0) * d 0 = 0 := by linear_combination v 1 * hn - n 1 * hv
    exact (mul_eq_zero.1 this).resolve_right h0

/-- A vector `v` with vanishing cross product against `n ≠ 0` is a multiple of `n`. -/
lemma hole_eq_smul_of_cross {n v : Fin 2 → ℝ} (hn : n ≠ 0) (h : n 0 * v 1 - n 1 * v 0 = 0) :
    v = (v ⬝ᵥ n / (n ⬝ᵥ n)) • n := by
  have hne := (hole_dot_self_pos hn).ne'
  rw [hole_dot2] at hne
  refine hole_ext2 ?_ ?_ <;> simp only [Pi.smul_apply, smul_eq_mul, hole_dot2] <;>
    rw [div_mul_eq_mul_div, eq_div_iff hne]
  · linear_combination (-n 1) * h
  · linear_combination (n 0) * h


/-- Two vectors orthogonal to the same nonzero vector are parallel. -/
lemma hole_eq_smul_of_perp {d n v : Fin 2 → ℝ} (hd : d ≠ 0) (hn0 : n ≠ 0) (hn : n ⬝ᵥ d = 0)
    (hv : v ⬝ᵥ d = 0) : v = (v ⬝ᵥ n / (n ⬝ᵥ n)) • n :=
  hole_eq_smul_of_cross hn0 (hole_cross_eq_zero hd hn hv)

/-- A vector orthogonal to `J u` is a multiple of `u`. -/
lemma hole_eq_smul_of_rot_dot (ho : o * o = 1) {u v : Fin 2 → ℝ} (hu : u ≠ 0)
    (h : hole_rot o u ⬝ᵥ v = 0) : v = (v ⬝ᵥ u / (u ⬝ᵥ u)) • u := by
  refine hole_eq_smul_of_cross hu ?_
  rw [hole_dot2] at h
  simp only [hole_rot_zero_apply, hole_rot_one_apply] at h
  have h' : o * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination h
  exact (mul_eq_zero.1 h').resolve_left (hole_o_ne_zero ho)

/-- Coordinates in the basis `u, w` (independent: `⟨J u, w⟩ ≠ 0`). -/
lemma hole_decomp (ho : o * o = 1) {u w : Fin 2 → ℝ} (h : hole_rot o u ⬝ᵥ w ≠ 0)
    (v : Fin 2 → ℝ) :
    v = (hole_rot o w ⬝ᵥ v / (hole_rot o w ⬝ᵥ u)) • u +
      (hole_rot o u ⬝ᵥ v / (hole_rot o u ⬝ᵥ w)) • w := by
  have hoo : o ≠ 0 := hole_o_ne_zero ho
  set D := u 0 * w 1 - u 1 * w 0 with hD
  have e1 : hole_rot o w ⬝ᵥ u = -(o * D) := by rw [hole_dot2]; simp [hD]; ring
  have e2 : hole_rot o u ⬝ᵥ w = o * D := by rw [hole_dot2]; simp [hD]; ring
  have e3 : hole_rot o w ⬝ᵥ v = o * (w 0 * v 1 - w 1 * v 0) := by rw [hole_dot2]; simp; ring
  have e4 : hole_rot o u ⬝ᵥ v = o * (u 0 * v 1 - u 1 * v 0) := by rw [hole_dot2]; simp; ring
  have hD0 : D ≠ 0 := by
    intro h0; apply h; rw [e2, h0, mul_zero]
  have c1 : hole_rot o w ⬝ᵥ v / (hole_rot o w ⬝ᵥ u) = -(w 0 * v 1 - w 1 * v 0) / D := by
    rw [e1, e3]; field_simp
  have c2 : hole_rot o u ⬝ᵥ v / (hole_rot o u ⬝ᵥ w) = (u 0 * v 1 - u 1 * v 0) / D := by
    rw [e2, e4]; field_simp
  rw [c1, c2]
  refine hole_ext2 ?_ ?_ <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
    field_simp <;> rw [hD] <;> ring

/-- Coordinates in the orthogonal basis `w, J w`. -/
lemma hole_decomp_orth (ho : o * o = 1) {w : Fin 2 → ℝ} (hw : w ≠ 0) (v : Fin 2 → ℝ) :
    v = (v ⬝ᵥ w / (w ⬝ᵥ w)) • w + (v ⬝ᵥ hole_rot o w / (w ⬝ᵥ w)) • hole_rot o w := by
  have hne := (hole_dot_self_pos hw).ne'
  simp only [hole_dot2] at hne ⊢
  refine hole_ext2 ?_ ?_ <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    hole_rot_zero_apply, hole_rot_one_apply] <;>
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hne]
  · linear_combination (-(v 0 * w 1 ^ 2 - v 1 * w 0 * w 1)) * ho
  · linear_combination (-(v 1 * w 0 ^ 2 - v 0 * w 0 * w 1)) * ho

/-- A convex combination of three points of a convex set lies in it. -/
lemma hole_convex_three {E : Set (Fin 2 → ℝ)} (hE : Convex ℝ E) {p₁ p₂ p₃ : Fin 2 → ℝ}
    (h₁ : p₁ ∈ E) (h₂ : p₂ ∈ E) (h₃ : p₃ ∈ E) {w₁ w₂ w₃ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hw₃ : 0 ≤ w₃) (hw : w₁ + w₂ + w₃ = 1) : w₁ • p₁ + w₂ • p₂ + w₃ • p₃ ∈ E := by
  have := hE.sum_mem (t := Finset.univ) (w := ![w₁, w₂, w₃]) (z := ![p₁, p₂, p₃])
    (by intro i _; fin_cases i <;> simpa) (by simpa [Fin.sum_univ_three] using hw)
    (by intro i _; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_three] using this

/-- A convex combination of three points of a convex set with positive weight on an interior
point lies in the interior. -/
lemma hole_convex_three_interior {E : Set (Fin 2 → ℝ)} (hE : Convex ℝ E) {p₁ p₂ p₃ : Fin 2 → ℝ}
    (h₁ : p₁ ∈ E) (h₂ : p₂ ∈ E) (h₃ : p₃ ∈ interior E) {w₁ w₂ w₃ : ℝ} (hw₁ : 0 ≤ w₁)
    (hw₂ : 0 ≤ w₂) (hw₃ : 0 < w₃) (hw : w₁ + w₂ + w₃ = 1) :
    w₁ • p₁ + w₂ • p₂ + w₃ • p₃ ∈ interior E := by
  rcases (add_nonneg hw₁ hw₂).eq_or_lt with h0 | h0
  · have e1 : w₁ = 0 := by linarith
    have e2 : w₂ = 0 := by linarith
    have e3 : w₃ = 1 := by linarith
    simpa [e1, e2, e3] using h₃
  · set y := (w₁ / (w₁ + w₂)) • p₁ + (w₂ / (w₁ + w₂)) • p₂
    have hy : y ∈ E := hE h₁ h₂ (div_nonneg hw₁ h0.le) (div_nonneg hw₂ h0.le)
      (by field_simp)
    have := hE.combo_interior_self_mem_interior h₃ hy hw₃ h0.le (by linarith)
    convert this using 1
    simp only [y, smul_add, smul_smul]
    rw [mul_div_cancel₀ _ h0.ne', mul_div_cancel₀ _ h0.ne']
    abel

/-- Positive numbers below which finitely many properties hold simultaneously. -/
lemma hole_exists_pos_forall {ι : Type*} [Finite ι] {P : ι → ℝ → Prop}
    (h : ∀ j, ∃ ε > 0, ∀ ε', 0 < ε' → ε' ≤ ε → P j ε') : ∃ ε > 0, ∀ j, P j ε := by
  have hev : ∀ j, ∀ᶠ ε' in 𝓝[>] (0 : ℝ), P j ε' := by
    intro j
    obtain ⟨ε, hε, hP⟩ := h j
    filter_upwards [Ioc_mem_nhdsGT hε] with ε' hε'
    exact hP ε' hε'.1 hε'.2
  obtain ⟨ε, hP, hε⟩ := ((Filter.eventually_all.2 hev).and self_mem_nhdsWithin).exists
  exact ⟨ε, hε, hP⟩

/-! ### Thin triangles over a segment -/

/-- The open thin triangle over the segment `[q, q']`, on the side of `J (q' - q)`, of slope `ε`
at both ends: the points `q + t (q' - q) + s J (q' - q)` with `0 < s < ε min (t, 1 - t)`. -/
def hole_tri (o : ℝ) (q q' : Fin 2 → ℝ) (ε : ℝ) : Set (Fin 2 → ℝ) :=
  {x | ∃ t s : ℝ, 0 < s ∧ s < ε * t ∧ s < ε * (1 - t) ∧
    x = q + t • (q' - q) + s • hole_rot o (q' - q)}

lemma hole_convex_tri (o : ℝ) (q q' : Fin 2 → ℝ) (ε : ℝ) : Convex ℝ (hole_tri o q q' ε) := by
  rintro x ⟨t, s, hs, hst, hst', rfl⟩ y ⟨t', s', hs', hst2, hst2', rfl⟩ a b ha hb hab
  refine ⟨a * t + b * t', a * s + b * s', ?_, ?_, ?_, ?_⟩
  · rcases ha.eq_or_lt with h | h
    · subst h
      obtain rfl : b = 1 := by linarith
      simpa using hs'
    · positivity
  · rcases ha.eq_or_lt with h | h
    · subst h
      obtain rfl : b = 1 := by linarith
      simpa using hst2
    · nlinarith
  · rcases ha.eq_or_lt with h | h
    · subst h
      obtain rfl : b = 1 := by linarith
      simpa using hst2'
    · have : 1 - (a * t + b * t') = a * (1 - t) + b * (1 - t') := by
        linear_combination (-1 : ℝ) * hab
      rw [this]; nlinarith
  · obtain rfl : b = 1 - a := by linarith
    module

lemma hole_tri_mono {o : ℝ} {q q' : Fin 2 → ℝ} {ε ε' : ℝ} (h : ε ≤ ε') :
    hole_tri o q q' ε ⊆ hole_tri o q q' ε' := by
  rintro x ⟨t, s, hs, h1, h2, rfl⟩
  have h2' : s < ε - ε * t := by rw [mul_sub, mul_one] at h2; exact h2
  have hε : 0 < ε := by linarith
  have ht : 0 < t := by
    by_contra ht; push Not at ht; nlinarith
  have ht1 : 0 < 1 - t := by
    by_contra ht; push Not at ht; nlinarith
  exact ⟨t, s, hs, by nlinarith, by nlinarith, rfl⟩

/-- Points near `x` in a fixed direction stay in an open set. -/
lemma hole_eventually_add_smul_mem {O : Set (Fin 2 → ℝ)} (hO : IsOpen O) {x : Fin 2 → ℝ}
    (hx : x ∈ O) (v : Fin 2 → ℝ) : ∀ᶠ δ in 𝓝 (0 : ℝ), x + δ • v ∈ O := by
  have hc : Continuous fun δ : ℝ ↦ x + δ • v := by fun_prop
  have := hc.tendsto 0
  simp only [zero_smul, add_zero] at this
  exact this.eventually (hO.mem_nhds hx)

lemma hole_exists_pos_of_eventually {P : ℝ → Prop} (h : ∀ᶠ δ in 𝓝 (0 : ℝ), P δ) :
    ∃ δ > 0, P δ := by
  obtain ⟨δ, hP, hδ⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  exact ⟨δ, hδ, hP⟩

/-! ### Points beside the relative interior of a segment -/

/-- The barycentric coordinates of a point beside the relative interior of `[a, b]`, on the side
of `p`. -/
lemma hole_bump_core (ho : o * o = 1) {a b p : Fin 2 → ℝ}
    (hpos : 0 < hole_rot o (b - a) ⬝ᵥ (p - a)) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ σ₀ > (0 : ℝ), ∀ σ : ℝ, 0 < σ → σ ≤ σ₀ → ∃ w₁ w₂ w₃ : ℝ, 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ 0 < w₃ ∧
      w₁ + w₂ + w₃ = 1 ∧ a + θ • (b - a) + σ • hole_rot o (b - a) = w₁ • a + w₂ • b + w₃ • p := by
  have hw : b - a ≠ 0 := by
    intro h; rw [h] at hpos; simp [hole_rot] at hpos
  set α := (p - a) ⬝ᵥ (b - a) / ((b - a) ⬝ᵥ (b - a)) with hα
  set β := (p - a) ⬝ᵥ hole_rot o (b - a) / ((b - a) ⬝ᵥ (b - a)) with hβ
  have hdec := hole_decomp_orth ho hw (p - a)
  rw [← hα, ← hβ] at hdec
  have hβ0 : 0 < β := by
    rw [hβ, dotProduct_comm]; exact div_pos hpos (hole_dot_self_pos hw)
  have hp : p = a + α • (b - a) + β • hole_rot o (b - a) := by
    rw [add_assoc, ← hdec]; abel
  set M := |α| + |1 - α| + 1 with hM
  have hM0 : 0 < M := by positivity
  refine ⟨β * min θ (1 - θ) / M, by have := lt_min hθ0 (sub_pos.2 hθ1); positivity, ?_⟩
  intro σ hσ hσ₀
  obtain ⟨w₃, rfl⟩ : ∃ w₃, σ = w₃ * β := ⟨σ / β, by field_simp⟩
  have hw₃ : 0 < w₃ := by
    by_contra h; push Not at h; nlinarith
  have hw₃' : w₃ * M ≤ min θ (1 - θ) := by
    rw [le_div_iff₀ hM0] at hσ₀
    nlinarith
  have hm1 := min_le_left θ (1 - θ)
  have hm2 := min_le_right θ (1 - θ)
  have hα1 : w₃ * |α| ≤ w₃ * M := by
    apply mul_le_mul_of_nonneg_left _ hw₃.le; rw [hM]; linarith [abs_nonneg (1 - α)]
  have hα2 : w₃ * |1 - α| ≤ w₃ * M := by
    apply mul_le_mul_of_nonneg_left _ hw₃.le; rw [hM]; linarith [abs_nonneg α]
  refine ⟨1 - θ - w₃ * (1 - α), θ - w₃ * α, w₃, ?_, ?_, hw₃, by ring, ?_⟩
  · have := le_abs_self (1 - α)
    nlinarith
  · have := le_abs_self α
    nlinarith
  · rw [hp]; module

/-- Points just beside the relative interior of a segment `[a, b]` of a convex set `E`, on the
side of a point `p ∈ E`, lie in `E`. -/
lemma hole_bump (ho : o * o = 1) {E : Set (Fin 2 → ℝ)} (hE : Convex ℝ E) {a b p : Fin 2 → ℝ}
    (ha : a ∈ E) (hb : b ∈ E) (hp : p ∈ E) (hpos : 0 < hole_rot o (b - a) ⬝ᵥ (p - a))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ σ₀ > (0 : ℝ), ∀ σ : ℝ, 0 < σ → σ ≤ σ₀ → a + θ • (b - a) + σ • hole_rot o (b - a) ∈ E := by
  obtain ⟨σ₀, hσ₀, h⟩ := hole_bump_core ho hpos hθ0 hθ1
  refine ⟨σ₀, hσ₀, fun σ hσ hσ' ↦ ?_⟩
  obtain ⟨w₁, w₂, w₃, h1, h2, h3, hs, he⟩ := h σ hσ hσ'
  rw [he]; exact hole_convex_three hE ha hb hp h1 h2 h3.le hs

/-- The interior version of `hole_bump`. -/
lemma hole_bump_interior (ho : o * o = 1) {E : Set (Fin 2 → ℝ)} (hE : Convex ℝ E)
    {a b p : Fin 2 → ℝ} (ha : a ∈ E) (hb : b ∈ E) (hp : p ∈ interior E)
    (hpos : 0 < hole_rot o (b - a) ⬝ᵥ (p - a)) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ σ₀ > (0 : ℝ), ∀ σ : ℝ, 0 < σ → σ ≤ σ₀ →
      a + θ • (b - a) + σ • hole_rot o (b - a) ∈ interior E := by
  obtain ⟨σ₀, hσ₀, h⟩ := hole_bump_core ho hpos hθ0 hθ1
  refine ⟨σ₀, hσ₀, fun σ hσ hσ' ↦ ?_⟩
  obtain ⟨w₁, w₂, w₃, h1, h2, h3, hs, he⟩ := h σ hσ hσ'
  rw [he]; exact hole_convex_three_interior hE ha hb hp h1 h2 h3 hs

/-! ### The relative interior of a side of a polygon -/

/-- Let `[p, p']` be a segment of a polygon `P` on a supporting line `⟨n, x - p⟩ = 0`. At a point
`m` of its relative interior every active constraint of `P` is a nonnegative multiple of `n`, one
of them a positive multiple, and `m` is a side point of `P` with outer normal `n`. -/
lemma hole_relint {ι : Type*} [Finite ι] (a : ι → Fin 2 → ℝ) (c : ι → ℝ)
    (hint : (interior (halfPlanesInter a c)).Nonempty) {n p p' : Fin 2 → ℝ} (hn : n ≠ 0)
    (hsupp : ∀ x ∈ halfPlanesInter a c, n ⬝ᵥ (x - p) ≤ 0) (hp : p ∈ halfPlanesInter a c)
    (hp' : p' ∈ halfPlanesInter a c) (hpp' : p ≠ p') (hperp : n ⬝ᵥ (p' - p) = 0) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∀ l, a l ⬝ᵥ (p + θ • (p' - p)) = c l → ∃ μ : ℝ, 0 ≤ μ ∧ a l = μ • n) ∧
    (∃ l, a l ⬝ᵥ (p + θ • (p' - p)) = c l ∧ ∃ μ : ℝ, 0 < μ ∧ a l = μ • n) ∧
    (∃ ε > 0, ∀ x, dist x (p + θ • (p' - p)) < ε →
      (x ∈ halfPlanesInter a c ↔ n ⬝ᵥ (x - (p + θ • (p' - p))) ≤ 0)) := by
  set P := halfPlanesInter a c
  set m := p + θ • (p' - p) with hm
  have hd : p' - p ≠ 0 := sub_ne_zero.2 (Ne.symm hpp')
  have hmP : m ∈ P := by
    have := (convex_halfPlanesInter a c) hp hp' (by linarith : (0 : ℝ) ≤ 1 - θ) hθ0.le
      (by ring)
    convert this using 1; rw [hm]; module
  have hnm : ∀ x, n ⬝ᵥ (x - m) = n ⬝ᵥ (x - p) := by
    intro x
    rw [hm, show x - (p + θ • (p' - p)) = (x - p) - θ • (p' - p) by abel, dotProduct_sub,
      dotProduct_smul, hperp, smul_zero, sub_zero]
  -- (i)
  have hi : ∀ l, a l ⬝ᵥ m = c l → ∃ μ : ℝ, 0 ≤ μ ∧ a l = μ • n := by
    intro l hl
    have h1 := hp l
    have h2 := hp' l
    have hml : a l ⬝ᵥ m = a l ⬝ᵥ p + θ * (a l ⬝ᵥ (p' - p)) := by
      rw [hm, dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hlp : a l ⬝ᵥ (p' - p) = 0 := by
      rw [dotProduct_sub] at hml ⊢
      nlinarith
    have hpar := hole_eq_smul_of_perp hd hn hperp hlp
    refine ⟨a l ⬝ᵥ n / (n ⬝ᵥ n), ?_, hpar⟩
    by_contra hμ
    push Not at hμ
    set μ := a l ⬝ᵥ n / (n ⬝ᵥ n)
    have hflat : ∀ y ∈ P, n ⬝ᵥ (y - m) = 0 := by
      intro y hy
      have hy1 := hy l
      have : μ * (n ⬝ᵥ (y - m)) ≤ 0 := by
        have e : a l ⬝ᵥ (y - m) = μ * (n ⬝ᵥ (y - m)) := by
          rw [hpar, smul_dotProduct, smul_eq_mul]
        rw [← e, dotProduct_sub, hl]
        linarith
      have h2 : 0 ≤ n ⬝ᵥ (y - m) := by nlinarith
      have h3 := hsupp y hy
      rw [← hnm] at h3
      linarith
    obtain ⟨x, hx⟩ := hint
    obtain ⟨δ, hδ, hδx⟩ := hole_exists_pos_of_eventually
      (hole_eventually_add_smul_mem isOpen_interior hx n)
    have e1 := hflat x (interior_subset hx)
    have e2 := hflat _ (interior_subset hδx)
    rw [show x + δ • n - m = (x - m) + δ • n by abel, dotProduct_add, e1, dotProduct_smul,
      smul_eq_mul, zero_add] at e2
    have := hole_dot_self_pos hn
    have : δ * (n ⬝ᵥ n) > 0 := by positivity
    linarith
  -- (iii)
  have hiii : ∃ l, a l ⬝ᵥ m = c l ∧ ∃ μ : ℝ, 0 < μ ∧ a l = μ • n := by
    have hfr : m ∈ frontier P := by
      refine ⟨subset_closure hmP, fun hmi ↦ ?_⟩
      obtain ⟨δ, hδ, hδm⟩ := hole_exists_pos_of_eventually
        (hole_eventually_add_smul_mem isOpen_interior hmi n)
      have := hsupp _ (interior_subset hδm)
      rw [← hnm, show m + δ • n - m = δ • n by abel, dotProduct_smul, smul_eq_mul] at this
      have := hole_dot_self_pos hn
      nlinarith
    obtain ⟨l, hl0, hl⟩ := mem_iUnion₂.1 (pin_frontier_halfPlanesInter_subset a c hfr)
    obtain ⟨μ, hμ, hμn⟩ := hi l hl
    refine ⟨l, hl, μ, lt_of_le_of_ne hμ ?_, hμn⟩
    rintro rfl; rw [zero_smul] at hμn; exact hl0 hμn
  refine ⟨hi, hiii, ?_⟩
  obtain ⟨r, hr, hcone⟩ := pin_local_cone a c hmP
  obtain ⟨l₀, hl₀, μ₀, hμ₀, hμ₀n⟩ := hiii
  refine ⟨r, hr, fun x hx ↦ ?_⟩
  rw [hcone x (Metric.mem_ball.2 hx)]
  constructor
  · intro h
    have := h l₀ hl₀
    rw [hμ₀n, smul_dotProduct, smul_eq_mul] at this
    nlinarith
  · intro h l hl
    obtain ⟨μ, hμ, hμn⟩ := hi l hl
    rw [hμn, smul_dotProduct, smul_eq_mul]
    nlinarith

/-- A segment of the plane is compact. -/
lemma hole_isCompact_segment (q q' : Fin 2 → ℝ) : IsCompact (segment ℝ q q') := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

/-- An estimate used for thin triangles: if `0 < A`, `0 < s < ε t` with `ε = A / (|B| + 1)`, then
`t A + s B > 0`. -/
lemma hole_lin_pos {A B s t ε : ℝ} (hA : 0 < A) (hε : ε = A / (|B| + 1)) (hs : 0 < s)
    (hst : s < ε * t) : 0 < t * A + s * B := by
  have hB : 0 < |B| + 1 := by positivity
  have hε0 : 0 < ε := by rw [hε]; positivity
  have ht : 0 < t := by by_contra h; push Not at h; nlinarith
  have h1 : -(s * |B|) ≤ s * B := by
    have := neg_abs_le B; nlinarith
  have h2 : s * |B| ≤ ε * t * |B| := mul_le_mul_of_nonneg_right hst.le (abs_nonneg B)
  have h3 : ε * (|B| + 1) = A := by rw [hε]; field_simp
  nlinarith

/-- **Thin triangles avoid a polygon** which misses the open segment `(q, q')`. -/
lemma hole_avoid_tri {ι : Type*} [Finite ι] (a : ι → Fin 2 → ℝ) (c : ι → ℝ) (o : ℝ)
    {q q' : Fin 2 → ℝ}
    (havoid : ∀ t : ℝ, 0 < t → t < 1 → q + t • (q' - q) ∉ halfPlanesInter a c) :
    ∃ ε > (0 : ℝ), ∀ x ∈ hole_tri o q q' ε, x ∉ halfPlanesInter a c := by
  set P := halfPlanesInter a c
  set R := hole_rot o (q' - q)
  by_cases hq : q ∈ P
  · obtain ⟨r, hr, hcone⟩ := pin_local_cone a c hq
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), q + t • (q' - q) ∈ Metric.ball q r ∧ t < 1 :=
      (hole_eventually_add_smul_mem Metric.isOpen_ball (Metric.mem_ball_self hr) _).and
        (eventually_lt_nhds one_pos)
    obtain ⟨t, ht, htb, ht1⟩ := hole_exists_pos_of_eventually hev
    have hnot := havoid t ht ht1
    rw [hcone _ htb] at hnot
    push Not at hnot
    obtain ⟨l, hl, hlt⟩ := hnot
    rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul] at hlt
    have hA : 0 < a l ⬝ᵥ (q' - q) := by nlinarith
    refine ⟨a l ⬝ᵥ (q' - q) / (|a l ⬝ᵥ R| + 1), by positivity, ?_⟩
    rintro x ⟨t, s, hs, h1, h2, rfl⟩ hx
    have := hx l
    rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, hl] at this
    have := hole_lin_pos hA rfl hs h1
    linarith
  by_cases hq' : q' ∈ P
  · obtain ⟨r, hr, hcone⟩ := pin_local_cone a c hq'
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), q' + t • (q - q') ∈ Metric.ball q' r ∧ t < 1 :=
      (hole_eventually_add_smul_mem Metric.isOpen_ball (Metric.mem_ball_self hr) _).and
        (eventually_lt_nhds one_pos)
    obtain ⟨t, ht, htb, ht1⟩ := hole_exists_pos_of_eventually hev
    have hnot := havoid (1 - t) (by linarith) (by linarith)
    rw [show q + (1 - t) • (q' - q) = q' + t • (q - q') by module, hcone _ htb] at hnot
    push Not at hnot
    obtain ⟨l, hl, hlt⟩ := hnot
    rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul] at hlt
    have hA : 0 < a l ⬝ᵥ (q - q') := by nlinarith
    refine ⟨a l ⬝ᵥ (q - q') / (|a l ⬝ᵥ R| + 1), by positivity, ?_⟩
    rintro x ⟨t, s, hs, h1, h2, rfl⟩ hx
    have := hx l
    have e : q + t • (q' - q) + s • R = q' + (1 - t) • (q - q') + s • R := by module
    rw [e, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, hl] at this
    have := hole_lin_pos hA rfl hs h2
    linarith
  · have hseg : segment ℝ q q' ⊆ Pᶜ := by
      rw [segment_eq_image']
      rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
      rcases ht0.eq_or_lt with h0 | h0
      · subst h0; simpa using hq
      rcases ht1.eq_or_lt with h1 | h1
      · subst h1; simpa using hq'
      exact havoid t h0 h1
    obtain ⟨δ, hδ, hth⟩ := (hole_isCompact_segment q q').exists_thickening_subset_open
      (isClosed_halfPlanesInter a c).isOpen_compl hseg
    refine ⟨δ / (‖R‖ + 1), by positivity, ?_⟩
    rintro x ⟨t, s, hs, h1, h2, rfl⟩
    have hε : 0 < δ / (‖R‖ + 1) := by positivity
    have ht0 : 0 < t := by by_contra h; push Not at h; nlinarith
    have ht1 : t < 1 := by by_contra h; push Not at h; nlinarith
    have hsε : s < δ / (‖R‖ + 1) := by nlinarith
    apply hth
    rw [Metric.mem_thickening_iff]
    refine ⟨q + t • (q' - q), ?_, ?_⟩
    · rw [segment_eq_image']; exact ⟨t, ⟨ht0.le, ht1.le⟩, rfl⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
      calc s * ‖R‖ ≤ δ / (‖R‖ + 1) * ‖R‖ := mul_le_mul_of_nonneg_right hsε.le (norm_nonneg _)
        _ < δ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg R]

/-- A point of the thin triangle over `[q, q + T u]`, in unscaled coordinates. -/
lemma hole_mem_tri {o : ℝ} {q u : Fin 2 → ℝ} {T ε τ σ : ℝ} (hT : 0 < T) (hσ : 0 < σ)
    (h1 : σ < ε * τ) (h2 : σ < ε * (T - τ)) :
    q + τ • u + σ • hole_rot o u ∈ hole_tri o q (q + T • u) ε := by
  refine ⟨τ / T, σ / T, by positivity, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ hT, mul_assoc, div_mul_cancel₀ _ hT.ne']; exact h1
  · rw [div_lt_iff₀ hT, mul_assoc, sub_mul, one_mul, div_mul_cancel₀ _ hT.ne']; exact h2
  · rw [add_sub_cancel_left, hole_rot_smul, smul_smul, smul_smul, div_mul_cancel₀ _ hT.ne',
      div_mul_cancel₀ _ hT.ne']

/-- The points of the thin triangle over `[q, q + T u]`, in unscaled coordinates. -/
lemma hole_tri_elim {o : ℝ} {q u x : Fin 2 → ℝ} {T ε : ℝ} (hT : 0 < T)
    (hx : x ∈ hole_tri o q (q + T • u) ε) : ∃ τ σ : ℝ, 0 < σ ∧ σ < ε * τ ∧ σ < ε * (T - τ) ∧
      x = q + τ • u + σ • hole_rot o u := by
  obtain ⟨t, s, hs, h1, h2, rfl⟩ := hx
  refine ⟨t * T, s * T, by positivity, by nlinarith, by nlinarith, ?_⟩
  rw [add_sub_cancel_left, hole_rot_smul, smul_smul, smul_smul]

end Vec

/-! ### The configuration -/

/-- The data of `pin_hole_structure_of_rotation`: the polygon `Q = halfPlanesInter b d`, the cells
`C i = halfPlanesInter (a i) (c i)`, bounded with nonempty interiors, non-overlapping, in `Q`,
with the rotation property, and a point `x₀ ∈ Q \ ⋃ C i`, whose component `U` and hole
`H = closure U` are studied. -/
structure hole_Cfg (n : ℕ) where
  /-- the number of constraints of `Q` -/
  m : ℕ
  /-- the normals of `Q` -/
  b : Fin m → Fin 2 → ℝ
  /-- the offsets of `Q` -/
  d : Fin m → ℝ
  hQ : Bornology.IsBounded (halfPlanesInter b d)
  /-- the cells -/
  C : Fin n → Set (Fin 2 → ℝ)
  /-- the number of constraints of each cell -/
  k : Fin n → ℕ
  /-- the normals of the cells -/
  a : (i : Fin n) → Fin (k i) → Fin 2 → ℝ
  /-- the offsets of the cells -/
  c : (i : Fin n) → Fin (k i) → ℝ
  hac : ∀ i, C i = halfPlanesInter (a i) (c i)
  hbdd : ∀ i, Bornology.IsBounded (C i)
  hint : ∀ i, (interior (C i)).Nonempty
  hCQ : ∀ i, C i ⊆ halfPlanesInter b d
  hdisj : NonOverlapping C
  hrot : pin_HasRotationProperty (halfPlanesInter b d) C
  /-- a base point of the hole -/
  x₀ : Fin 2 → ℝ
  hx₀ : x₀ ∈ halfPlanesInter b d \ ⋃ i, C i

namespace hole_Cfg

variable {n : ℕ} (S : hole_Cfg n)

/-- The container polygon. -/
def Q : Set (Fin 2 → ℝ) := halfPlanesInter S.b S.d

/-- The uncovered part of the container. -/
def F : Set (Fin 2 → ℝ) := S.Q \ ⋃ i, S.C i

/-- The component of `x₀` in the uncovered part. -/
noncomputable def U : Set (Fin 2 → ℝ) := connectedComponentIn S.F S.x₀

/-- The hole. -/
noncomputable def H : Set (Fin 2 → ℝ) := closure S.U

lemma isConvexPolygon (i : Fin n) : IsConvexPolygon (S.C i) :=
  ⟨⟨S.k i, S.a i, S.c i, S.hac i⟩, S.hbdd i, S.hint i⟩

lemma isClosed_C (i : Fin n) : IsClosed (S.C i) := by
  rw [S.hac i]; exact isClosed_halfPlanesInter _ _

lemma convex_C (i : Fin n) : Convex ℝ (S.C i) := by
  rw [S.hac i]; exact convex_halfPlanesInter _ _

lemma isClosed_Q : IsClosed S.Q := isClosed_halfPlanesInter _ _

lemma convex_Q : Convex ℝ S.Q := convex_halfPlanesInter _ _

lemma C_subset_Q (i : Fin n) : S.C i ⊆ S.Q := S.hCQ i

lemma isClosed_iUnion_C : IsClosed (⋃ i, S.C i) := isClosed_iUnion_of_finite S.isClosed_C

lemma U_subset_F : S.U ⊆ S.F := connectedComponentIn_subset _ _

lemma U_subset_Q : S.U ⊆ S.Q := fun _ hx ↦ (S.U_subset_F hx).1

lemma notMem_C_of_mem_U {x : Fin 2 → ℝ} (hx : x ∈ S.U) (i : Fin n) : x ∉ S.C i :=
  fun h ↦ (S.U_subset_F hx).2 (mem_iUnion.2 ⟨i, h⟩)

lemma notMem_C_of_mem_F {x : Fin 2 → ℝ} (hx : x ∈ S.F) (i : Fin n) : x ∉ S.C i :=
  fun h ↦ hx.2 (mem_iUnion.2 ⟨i, h⟩)

lemma H_subset_Q : S.H ⊆ S.Q := closure_minimal S.U_subset_Q S.isClosed_Q

lemma disjoint_interior_H (i : Fin n) : Disjoint (interior (S.C i)) S.H := by
  refine Disjoint.closure_right ?_ isOpen_interior
  rw [Set.disjoint_left]
  exact fun x hx hxU ↦ S.notMem_C_of_mem_U hxU i (interior_subset hx)

lemma inter_interior {i j : Fin n} (hij : i ≠ j) : S.C i ∩ interior (S.C j) = ∅ :=
  pin_inter_interior_eq_empty S.isConvexPolygon S.hdisj hij

lemma notMem_interior {i j : Fin n} (hij : i ≠ j) {x : Fin 2 → ℝ} (hx : x ∈ S.C i) :
    x ∉ interior (S.C j) := fun h ↦ by
  have := S.inter_interior hij
  exact (Set.eq_empty_iff_forall_notMem.1 this) x ⟨hx, h⟩

/-- A preconnected subset of `F` meeting `U` lies in `U`. -/
lemma subset_U {T : Set (Fin 2 → ℝ)} (hT : IsPreconnected T) (hTF : T ⊆ S.F) {x : Fin 2 → ℝ}
    (hxT : x ∈ T) (hxU : x ∈ S.U) : T ⊆ S.U := by
  have := hT.subset_connectedComponentIn hxT hTF
  rwa [← connectedComponentIn_eq hxU] at this

/-- All cells are conic near `z` within a common radius. -/
lemma conic (z : Fin 2 → ℝ) : ∃ r > (0 : ℝ), ∀ i, ∀ x ∈ Metric.ball z r, ∀ t : ℝ, 0 < t →
    t ≤ 1 → (x ∈ S.C i ↔ z + t • (x - z) ∈ S.C i) := by
  have h : ∀ i, ∃ r > (0 : ℝ), ∀ r', 0 < r' → r' ≤ r → ∀ x ∈ Metric.ball z r', ∀ t : ℝ,
      0 < t → t ≤ 1 → (x ∈ S.C i ↔ z + t • (x - z) ∈ S.C i) := by
    intro i
    obtain ⟨r, hr, h⟩ := pin_conic_halfPlanesInter (S.a i) (S.c i) z
    refine ⟨r, hr, fun r' _ hr' x hx t ht ht1 ↦ ?_⟩
    rw [S.hac i]
    exact h x (Metric.ball_subset_ball hr' hx) t ht ht1
  obtain ⟨r, hr, h⟩ := hole_exists_pos_forall h
  exact ⟨r, hr, fun i ↦ h i⟩

/-! ### The rotation lemma -/

/-- **Rotation lemma.** No side `[q, q']` of a cell has a thin triangle over it (on the outer
side) inside `Q \ ⋃ C j`: the point `y` above the midpoint violates only the constraint of the
side, and `conv ({y} ∪ [q, q'])` meets the interior of no other cell, contradicting the rotation
property. -/
lemma rotation_contra {o : ℝ} (i : Fin n) (l : Fin (S.k i)) {q q' : Fin 2 → ℝ}
    (hqq' : q ≠ q') (hq : q ∈ S.C i) (hq' : q' ∈ S.C i) (hlq : S.a i l ⬝ᵥ q = S.c i l)
    (hlq' : S.a i l ⬝ᵥ q' = S.c i l)
    (hface : S.C i ∩ {x | S.a i l ⬝ᵥ x = S.c i l} ⊆ segment ℝ q q')
    (hout : 0 < S.a i l ⬝ᵥ hole_rot o (q' - q)) {ε : ℝ} (hε : 0 < ε)
    (htri : hole_tri o q q' ε ⊆ S.F) : False := by
  classical
  set a := S.a i
  set c := S.c i
  set mid := q + (1 / 2 : ℝ) • (q' - q) with hmid
  set R := hole_rot o (q' - q) with hR
  have hCi : S.C i = halfPlanesInter a c := S.hac i
  have hal0 : a l ≠ 0 := by
    intro h; rw [h, zero_dotProduct] at hout; exact lt_irrefl _ hout
  have hsupp : ∀ x ∈ halfPlanesInter a c, a l ⬝ᵥ (x - q) ≤ 0 := fun x hx ↦ by
    rw [dotProduct_sub, hlq]; linarith [hx l]
  have hperp : a l ⬝ᵥ (q' - q) = 0 := by rw [dotProduct_sub, hlq, hlq', sub_self]
  have hint : (interior (halfPlanesInter a c)).Nonempty := hCi ▸ S.hint i
  obtain ⟨hi, -, -⟩ := hole_relint a c hint hal0 hsupp (hCi ▸ hq) (hCi ▸ hq') hqq' hperp
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hmidC : mid ∈ halfPlanesInter a c := by
    have := (convex_halfPlanesInter a c) (hCi ▸ hq) (hCi ▸ hq') (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert this using 1; rw [hmid]; module
  have hmidl : a l ⬝ᵥ mid = c l := by
    rw [hmid, dotProduct_add, dotProduct_smul, hperp, smul_zero, add_zero, hlq]
  -- the cleaned representation: drop the other constraints active at the midpoint
  set act : Fin (S.k i) → Prop := fun m ↦ m ≠ l ∧ a m ⬝ᵥ mid = c m
  set a' : Fin (S.k i) → Fin 2 → ℝ := fun m ↦ if act m then 0 else a m
  set c' : Fin (S.k i) → ℝ := fun m ↦ if act m then 0 else c m
  have hl' : ¬ act l := fun h ↦ h.1 rfl
  have ha'l : a' l = a l := by simp only [a', hl', ite_false]
  have hc'l : c' l = c l := by simp only [c', hl', ite_false]
  have hrep : S.C i = halfPlanesInter a' c' := by
    rw [hCi]; ext x; constructor
    · intro hx m
      by_cases hm : act m
      · simp [a', c', hm]
      · simp only [a', c', hm, ite_false]; exact hx m
    · intro hx m
      by_cases hm : act m
      · obtain ⟨μ, hμ, hμa⟩ := hi m hm.2
        have hxl := hx l
        rw [ha'l, hc'l] at hxl
        have hcm : c m = μ * c l := by
          rw [← hm.2, hμa, smul_dotProduct, hmidl, smul_eq_mul]
        rw [hμa, smul_dotProduct, smul_eq_mul, hcm]
        exact mul_le_mul_of_nonneg_left hxl hμ
      · have := hx m; simp only [a', c', hm, ite_false] at this; exact this
  -- the point `y` above the midpoint
  have hev : ∀ᶠ κ in 𝓝 (0 : ℝ), κ < ε / 2 ∧
      ∀ m, ¬ act m → m ≠ l → a m ⬝ᵥ (mid + κ • R) < c m := by
    refine (eventually_lt_nhds (by positivity)).and ?_
    rw [Filter.eventually_all]
    intro m
    by_cases hm : ¬ act m ∧ m ≠ l
    · have hlt : a m ⬝ᵥ mid < c m := by
        refine lt_of_le_of_ne (hmidC m) fun h ↦ hm.1 ⟨hm.2, h⟩
      have hc : ContinuousAt (fun κ : ℝ ↦ a m ⬝ᵥ (mid + κ • R)) 0 := by fun_prop
      filter_upwards [hc.eventually_lt continuousAt_const (by simpa using hlt)] with κ hκ
      exact fun _ _ ↦ hκ
    · filter_upwards with κ
      intro h1 h2; exact absurd ⟨h1, h2⟩ hm
  obtain ⟨κ, hκ, hκε, hκm⟩ := hole_exists_pos_of_eventually hev
  set y := mid + κ • R with hy
  have hyT : y ∈ hole_tri o q q' ε :=
    ⟨1 / 2, κ, hκ, by linarith, by linarith, by rw [hy, hmid]⟩
  have hyQ : y ∈ S.Q := (htri hyT).1
  have hviol : c' l < a' l ⬝ᵥ y := by
    rw [ha'l, hc'l, hy, dotProduct_add, dotProduct_smul, smul_eq_mul, hmidl]
    have : 0 < κ * (a l ⬝ᵥ R) := mul_pos hκ hout
    linarith
  have hothers : ∀ m, m ≠ l → a' m ⬝ᵥ y ≤ c' m := by
    intro m hml
    by_cases hm : act m
    · simp [a', c', hm]
    · simp only [a', c', hm, ite_false]; exact (hκm m hm hml).le
  obtain ⟨j, hji, w, hwj, hwconv⟩ := S.hrot i a' c' hrep l y hyQ hviol hothers
  rw [ha'l, hc'l] at hwconv
  have hsub : convexHull ℝ (insert y (S.C i ∩ {x | a l ⬝ᵥ x = c l})) ⊆
      convexJoin ℝ {y} (segment ℝ q q') := by
    calc convexHull ℝ (insert y (S.C i ∩ {x | a l ⬝ᵥ x = c l}))
        ⊆ convexHull ℝ (insert y (segment ℝ q q')) := convexHull_mono (insert_subset_insert hface)
      _ = convexJoin ℝ {y} (segment ℝ q q') := by
        rw [convexHull_insert ⟨q, left_mem_segment ℝ q q'⟩, (convex_segment q q').convexHull_eq]
  obtain ⟨y', hy', x, hx, hw⟩ := mem_convexJoin.1 (hsub hwconv)
  rw [mem_singleton_iff] at hy'
  subst hy'
  rw [segment_eq_image'] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hw
  rcases hα.eq_or_lt with h0 | h0
  · -- `w` lies on the side
    subst h0
    have hβ1 : β = 1 := by linarith
    subst hβ1
    have hwC : q + t • (q' - q) ∈ S.C i := by
      have := (S.convex_C i) hq hq' (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
      convert this using 1; module
    exact S.notMem_interior (Ne.symm hji) hwC (by simpa using hwj)
  · -- `w` lies in the thin triangle
    have hwT : α • y + β • (q + t • (q' - q)) ∈ hole_tri o q q' ε := by
      have h1 : α * κ < α * (ε / 2) := mul_lt_mul_of_pos_left hκε h0
      refine ⟨α / 2 + β * t, α * κ, by positivity, ?_, ?_, ?_⟩
      · have : 0 ≤ ε * (β * t) := by positivity
        have e : ε * (α / 2 + β * t) = α * (ε / 2) + ε * (β * t) := by ring
        linarith
      · have : 1 - (α / 2 + β * t) = α / 2 + β * (1 - t) := by
          linear_combination (-1 : ℝ) * hαβ
        have h2 : 0 ≤ ε * (β * (1 - t)) := mul_nonneg hε.le (mul_nonneg hβ (by linarith))
        have e : ε * (α / 2 + β * (1 - t)) = α * (ε / 2) + ε * (β * (1 - t)) := by ring
        rw [this]; linarith
      · obtain rfl : β = 1 - α := by linarith
        rw [hy, hmid]; module
    exact S.notMem_C_of_mem_F (htri hwT) j (interior_subset hwj)

end hole_Cfg

/-- A closed set containing `z + τ v` for all small `τ > 0` contains `z`. -/
lemma hole_mem_of_forall_pos {E : Set (Fin 2 → ℝ)} (hE : IsClosed E) {z v : Fin 2 → ℝ} {T : ℝ}
    (hT : 0 < T) (h : ∀ τ : ℝ, 0 < τ → τ ≤ T → z + τ • v ∈ E) : z ∈ E := by
  have ht : Tendsto (fun τ : ℝ ↦ z + τ • v) (𝓝[>] 0) (𝓝 z) := by
    have hc : Continuous fun τ : ℝ ↦ z + τ • v := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine hE.mem_of_tendsto ht ?_
  filter_upwards [Ioc_mem_nhdsGT hT] with τ hτ using h τ hτ.1 hτ.2

/-- An eventual property in `𝓝[>] 0` holds on an interval `(0, δ)`. -/
lemma hole_exists_Ioo_of_eventually {P : ℝ → Prop} (h : ∀ᶠ τ in 𝓝[>] (0 : ℝ), P τ) :
    ∃ δ > (0 : ℝ), ∀ τ, 0 < τ → τ < δ → P τ := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  exact ⟨δ, hδ, fun τ h0 h1 ↦ hsub ⟨h0, h1⟩⟩

/-- Near a side point `q'` of `C` with outer normal `w`, the points strictly inside lie in the
interior of `C`. -/
lemma hole_mem_interior_of_side {C : Set (Fin 2 → ℝ)} {q' w : Fin 2 → ℝ} {ε : ℝ}
    (hside : ∀ x, dist x q' < ε → (x ∈ C ↔ w ⬝ᵥ (x - q') ≤ 0)) {x : Fin 2 → ℝ}
    (hx : dist x q' < ε) (hneg : w ⬝ᵥ (x - q') < 0) : x ∈ interior C := by
  have hO : IsOpen {y : Fin 2 → ℝ | dist y q' < ε ∧ w ⬝ᵥ (y - q') < 0} :=
    (Metric.isOpen_ball (x := q') (ε := ε)).inter
      (isOpen_lt (by fun_prop : Continuous fun y : Fin 2 → ℝ ↦ w ⬝ᵥ (y - q')) continuous_const)
  exact interior_maximal (t := {y : Fin 2 → ℝ | dist y q' < ε ∧ w ⬝ᵥ (y - q') < 0})
    (fun y hy ↦ (hside y hy.1).2 hy.2.le) hO ⟨hx, hneg⟩

/-- The frontier of a bounded convex set of the plane with an interior point is preconnected (it
is the image of the punctured plane under `v ↦ o + v / gauge v`). -/
lemma hole_isPreconnected_frontier {K : Set (Fin 2 → ℝ)} (hconv : Convex ℝ K)
    (hbdd : Bornology.IsBounded K) {o : Fin 2 → ℝ} (ho : o ∈ interior K) :
    IsPreconnected (frontier K) := by
  set s := (Homeomorph.addLeft o) ⁻¹' K with hs
  have hsK : s = (fun v ↦ o + v) ⁻¹' K := rfl
  have hsconv : Convex ℝ s := by rw [hsK]; exact hconv.translate_preimage_right o
  have hs0 : s ∈ 𝓝 (0 : Fin 2 → ℝ) := by
    rw [hsK]
    have hc : ContinuousAt (fun v : Fin 2 → ℝ ↦ o + v) 0 := by fun_prop
    exact hc.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 ho)
  have hsb : Bornology.IsBounded s := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hbdd
    refine isBounded_iff_forall_norm_le.2 ⟨R + ‖o‖, fun v hv ↦ ?_⟩
    have h1 : ‖o + v‖ ≤ R := hR _ hv
    calc ‖v‖ = ‖(o + v) - o‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖o + v‖ + ‖o‖ := norm_sub_le _ _
      _ ≤ R + ‖o‖ := by linarith
  have hpos : ∀ v : Fin 2 → ℝ, v ≠ 0 → 0 < gauge s v := fun v hv ↦
    (gauge_pos (absorbent_nhds_zero hs0) ((NormedSpace.isVonNBounded_iff ℝ).2 hsb)).2 hv
  have hfr : frontier s = (fun v ↦ o + v) ⁻¹' frontier K := by
    rw [hs, ← Homeomorph.preimage_frontier]; rfl
  set f : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun v ↦ o + (gauge s v)⁻¹ • v with hf
  have himage : f '' {0}ᶜ = frontier K := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : v ≠ 0 := hv
      have h1 : gauge s ((gauge s v)⁻¹ • v) = 1 := by
        rw [gauge_smul_of_nonneg (inv_nonneg.2 (hpos v hv').le), smul_eq_mul,
          inv_mul_cancel₀ (hpos v hv').ne']
      have := (gauge_eq_one_iff_mem_frontier hsconv hs0).1 h1
      rw [hfr] at this
      exact this
    · intro hx
      refine ⟨x - o, ?_, ?_⟩
      · have hx' : x - o ∈ frontier s := by rw [hfr]; simpa using hx
        have h1 := (gauge_eq_one_iff_mem_frontier hsconv hs0).2 hx'
        intro h0
        rw [mem_singleton_iff] at h0
        rw [h0, gauge_zero] at h1
        exact zero_ne_one h1
      · have hx' : x - o ∈ frontier s := by rw [hfr]; simpa using hx
        have h1 := (gauge_eq_one_iff_mem_frontier hsconv hs0).2 hx'
        simp only [hf, h1, inv_one, one_smul, add_sub_cancel]
  have hcont : ContinuousOn f {0}ᶜ := by
    have hg := continuous_gauge hsconv hs0
    have h2 : ContinuousOn (fun v ↦ (gauge s v)⁻¹) {0}ᶜ :=
      (hg.continuousOn).inv₀ fun v hv ↦ (hpos v hv).ne'
    exact continuousOn_const.add (h2.smul continuousOn_id)
  rw [← himage]
  exact ((isConnected_compl_singleton_of_one_lt_rank (by rw [rank_fin_fun]; norm_num) 0).image
    f hcont).isPreconnected

/-- **Counting.** Let `e` be injective on a finite set `s` of states, with `P (e x)` for all
`x ∈ s`, and every `e x` the base point of some state. Then every base point satisfies `P`:
otherwise `e '' s` would be a proper subset of `base '' s`, of size at least `#s`. -/
lemma hole_count {α β : Type*} {s : Set α} (hs : s.Finite) (base e : α → β) (P : β → Prop)
    (hinj : Set.InjOn e s) (hP : ∀ x ∈ s, P (e x)) (hnext : ∀ x ∈ s, ∃ y ∈ s, base y = e x) :
    ∀ x ∈ s, P (base x) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀, hPx₀⟩ := hcon
  set A := base '' s
  have hA : A.Finite := hs.image base
  have hEA : e '' s ⊆ A ∩ {b | P b} := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hnext x hx
    exact ⟨⟨y, hy, hyx⟩, hP x hx⟩
  have hss : A ∩ {b | P b} ⊂ A :=
    ⟨inter_subset_left, fun h ↦ hPx₀ (h ⟨x₀, hx₀, rfl⟩).2⟩
  have h1 : (e '' s).ncard = s.ncard := hinj.ncard_image
  have h2 : (e '' s).ncard ≤ (A ∩ {b | P b}).ncard :=
    ncard_le_ncard hEA (hA.subset inter_subset_left)
  have h3 : (A ∩ {b | P b}).ncard < A.ncard := ncard_lt_ncard hss hA
  have h4 : A.ncard ≤ s.ncard := ncard_image_le hs
  omega

namespace hole_Cfg

variable {n : ℕ} (S : hole_Cfg n)

/-! ### States -/

/-- A *state* `(i, q, u)`: the side of `C i` on the line through `q` with direction `u` starts at
`q` (`C i` contains some `q + T u`, `T > 0`, but no `q - t u`, `t > 0`), `C i` lies on the right of
this line (`⟨J u, x - q⟩ ≤ 0`), and `U` lies on its left near `q` (a thin triangle over the
beginning of the side lies in `U`). -/
def IsState (o : ℝ) (i : Fin n) (q u : Fin 2 → ℝ) : Prop :=
  u ≠ 0 ∧ q ∈ S.C i ∧ (∃ T > (0 : ℝ), q + T • u ∈ S.C i) ∧
    (∀ t : ℝ, 0 < t → q - t • u ∉ S.C i) ∧ (∀ x ∈ S.C i, hole_rot o u ⬝ᵥ (x - q) ≤ 0) ∧
    (∃ T > (0 : ℝ), ∃ ε > (0 : ℝ), hole_tri o q (q + T • u) ε ⊆ S.U)

variable {S}

lemma IsState.smul {o : ℝ} {i : Fin n} {q u : Fin 2 → ℝ} (hs : S.IsState o i q u) {r : ℝ}
    (hr : 0 < r) : S.IsState o i q (r • u) := by
  obtain ⟨hu, hq, ⟨T, hT, hTC⟩, hback, hright, ⟨T', hT', ε, hε, htri⟩⟩ := hs
  refine ⟨smul_ne_zero hr.ne' hu, hq, ⟨T / r, by positivity, ?_⟩, fun t ht ↦ ?_, fun x hx ↦ ?_,
    ⟨T' / r, by positivity, ε, hε, ?_⟩⟩
  · rwa [smul_smul, div_mul_cancel₀ _ hr.ne']
  · rw [smul_smul]; exact hback _ (by positivity)
  · rw [hole_rot_smul, smul_dotProduct, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hr.le (hright x hx)
  · rwa [smul_smul, div_mul_cancel₀ _ hr.ne']

lemma IsState.unique {o : ℝ} (ho : o * o = 1) {i : Fin n} {q q' u : Fin 2 → ℝ}
    (h₁ : S.IsState o i q u) (h₂ : S.IsState o i q' u) : q = q' := by
  have hu := h₁.1
  have e1 := h₁.2.2.2.2.1 q' h₂.2.1
  have e2 := h₂.2.2.2.2.1 q h₁.2.1
  have hz : hole_rot o u ⬝ᵥ (q' - q) = 0 := by
    rw [show q - q' = -(q' - q) by abel, dotProduct_neg] at e2
    linarith
  have hpar := hole_eq_smul_of_rot_dot ho hu hz
  set τ := (q' - q) ⬝ᵥ u / (u ⬝ᵥ u)
  rcases lt_trichotomy τ 0 with hτ | hτ | hτ
  · exfalso
    apply h₁.2.2.2.1 (-τ) (by linarith)
    have : q - (-τ) • u = q' := by rw [neg_smul, sub_neg_eq_add, ← hpar]; abel
    rw [this]; exact h₂.2.1
  · rw [hτ, zero_smul, sub_eq_zero] at hpar; exact hpar.symm
  · exfalso
    apply h₂.2.2.2.1 τ hτ
    have : q' - τ • u = q := by rw [← hpar]; abel
    rw [this]; exact h₁.2.1

/-- The interior of the cell of a state lies strictly on the right. -/
lemma IsState.interior_right {o : ℝ} (ho : o * o = 1) {i : Fin n} {q u : Fin 2 → ℝ}
    (hs : S.IsState o i q u) {p : Fin 2 → ℝ} (hp : p ∈ interior (S.C i)) :
    hole_rot o u ⬝ᵥ (p - q) < 0 := by
  obtain ⟨δ, hδ, hδp⟩ := hole_exists_pos_of_eventually
    (hole_eventually_add_smul_mem isOpen_interior hp (hole_rot o u))
  have := hs.2.2.2.2.1 _ (interior_subset hδp)
  rw [show p + δ • hole_rot o u - q = (p - q) + δ • hole_rot o u by abel, dotProduct_add,
    dotProduct_smul, smul_eq_mul] at this
  have := hole_rot_dot_rot_self_pos ho hs.1
  nlinarith

/-- **The side of a state.** It is `[q, q + L u]`, carried by a constraint `l` of `C i` whose
normal is a positive multiple of `J u`. -/
lemma IsState.face {o : ℝ} (ho : o * o = 1) {i : Fin n} {q u : Fin 2 → ℝ}
    (hs : S.IsState o i q u) : ∃ L > (0 : ℝ), (∀ τ : ℝ, 0 ≤ τ → τ ≤ L → q + τ • u ∈ S.C i) ∧
      (∀ τ : ℝ, L < τ → q + τ • u ∉ S.C i) ∧ ∃ l : Fin (S.k i),
        (∃ μ > (0 : ℝ), S.a i l = μ • hole_rot o u) ∧ S.a i l ⬝ᵥ q = S.c i l ∧
        S.C i ∩ {x | S.a i l ⬝ᵥ x = S.c i l} ⊆ segment ℝ q (q + L • u) := by
  obtain ⟨hu, hq, ⟨T, hT, hTC⟩, hback, hright, -⟩ := hs
  set A := {τ : ℝ | 0 ≤ τ ∧ q + τ • u ∈ S.C i}
  have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (S.hbdd i)
  have hbdd : BddAbove A := by
    refine ⟨(R + ‖q‖) / ‖u‖, fun τ hτ ↦ ?_⟩
    rw [le_div_iff₀ hnu]
    have h1 := hR _ hτ.2
    have h2 : ‖τ • u‖ ≤ ‖q + τ • u‖ + ‖q‖ := by
      calc ‖τ • u‖ = ‖(q + τ • u) - q‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖q + τ • u‖ + ‖q‖ := norm_sub_le _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1] at h2
    linarith
  have hclosed : IsClosed A :=
    isClosed_Ici.inter ((S.isClosed_C i).preimage (by fun_prop))
  have hTA : T ∈ A := ⟨hT.le, hTC⟩
  set L := sSup A
  have hLA : L ∈ A := hclosed.csSup_mem ⟨T, hTA⟩ hbdd
  have hTL : T ≤ L := le_csSup hbdd hTA
  have hL : 0 < L := hT.trans_le hTL
  have hseg : ∀ τ : ℝ, 0 ≤ τ → τ ≤ L → q + τ • u ∈ S.C i := by
    intro τ h0 h1
    have := (S.convex_C i) hq hLA.2
      (by rw [sub_nonneg]; exact div_le_one_of_le₀ h1 hL.le : (0 : ℝ) ≤ 1 - τ / L)
      (div_nonneg h0 hL.le) (by ring)
    convert this using 1
    rw [smul_add, smul_smul, div_mul_cancel₀ _ hL.ne']; module
  have hbeyond : ∀ τ : ℝ, L < τ → q + τ • u ∉ S.C i := fun τ hτ h ↦
    absurd (le_csSup hbdd ⟨(hL.trans hτ).le, h⟩) (not_le.2 hτ)
  refine ⟨L, hL, hseg, hbeyond, ?_⟩
  -- the constraint carrying the side
  have hCi := S.hac i
  have hTu : T • u ≠ 0 := smul_ne_zero hT.ne' hu
  obtain ⟨-, ⟨l, hl, μ, hμ, hμl⟩, -⟩ := hole_relint (S.a i) (S.c i) (hCi ▸ S.hint i)
    (hole_rot_ne_zero ho hu) (fun x hx ↦ hright x (hCi ▸ hx)) (hCi ▸ hq) (hCi ▸ hTC)
    (by intro h; apply hTu; rw [← add_sub_cancel_left q (T • u), ← h, sub_self])
    (by rw [add_sub_cancel_left, dotProduct_smul, hole_rot_dot_self, smul_zero])
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hlq : S.a i l ⬝ᵥ q = S.c i l := by
    rw [← hl, hμl, smul_dotProduct, smul_dotProduct, add_sub_cancel_left, dotProduct_add,
      dotProduct_smul, dotProduct_smul, hole_rot_dot_self, smul_zero, smul_zero, add_zero]
  refine ⟨l, ⟨μ, hμ, hμl⟩, hlq, ?_⟩
  rintro x ⟨hx, hxl⟩
  have hz : hole_rot o u ⬝ᵥ (x - q) = 0 := by
    have : S.a i l ⬝ᵥ (x - q) = 0 := by
      rw [dotProduct_sub, hlq]; simp only [mem_ofPred_eq] at hxl; rw [hxl, sub_self]
    rw [hμl, smul_dotProduct, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hμ.ne'
  have hpar := hole_eq_smul_of_rot_dot ho hu hz
  set τ := (x - q) ⬝ᵥ u / (u ⬝ᵥ u)
  have hxq : x = q + τ • u := by rw [← hpar]; abel
  have hτ0 : 0 ≤ τ := by
    by_contra h; push Not at h
    exact hback (-τ) (by linarith) (by rw [neg_smul, sub_neg_eq_add, ← hxq]; exact hx)
  have hτL : τ ≤ L := by
    by_contra h; push Not at h
    exact hbeyond τ h (hxq ▸ hx)
  rw [segment_eq_image']
  refine ⟨τ / L, ⟨div_nonneg hτ0 hL.le, div_le_one_of_le₀ hτL hL.le⟩, ?_⟩
  simp only [hxq, add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hL.ne']

/-- A cell other than that of a state cannot contain the beginning of its side. -/
lemma IsState.not_touch {o : ℝ} (ho : o * o = 1) {i : Fin n} {q u : Fin 2 → ℝ}
    (hs : S.IsState o i q u) {j : Fin n} (hji : j ≠ i) {T₁ : ℝ} (hT₁ : 0 < T₁)
    (h : ∀ τ : ℝ, 0 < τ → τ ≤ T₁ → q + τ • u ∈ S.C j) : False := by
  obtain ⟨L, hL, hseg, -, -⟩ := hs.face ho
  have hright' : ∀ p ∈ interior (S.C i), hole_rot o u ⬝ᵥ (p - q) < 0 :=
    fun p hp ↦ hs.interior_right ho hp
  obtain ⟨hu, hq, -, -, -, ⟨T₀, hT₀, ε₀, hε₀, htri⟩⟩ := hs
  have hqj : q ∈ S.C j := hole_mem_of_forall_pos (S.isClosed_C j) hT₁ h
  set τ₁ := min T₁ (min L T₀) with hτ₁
  have hτ₁0 : 0 < τ₁ := lt_min hT₁ (lt_min hL hT₀)
  have hτ₁T₁ : τ₁ ≤ T₁ := min_le_left _ _
  have hτ₁L : τ₁ ≤ L := (min_le_right _ _).trans (min_le_left _ _)
  have hτ₁T₀ : τ₁ ≤ T₀ := (min_le_right _ _).trans (min_le_right _ _)
  set b := q + τ₁ • u with hb
  have hbj : b ∈ S.C j := h τ₁ hτ₁0 hτ₁T₁
  have hbi : b ∈ S.C i := hseg τ₁ hτ₁0.le hτ₁L
  have hbq : b - q = τ₁ • u := add_sub_cancel_left _ _
  have hrr := hole_rot_dot_rot_self_pos ho hu
  -- an interior point of `C j` off the line
  obtain ⟨p, hp, hpne⟩ : ∃ p ∈ interior (S.C j), hole_rot o u ⬝ᵥ (p - q) ≠ 0 := by
    obtain ⟨p₀, hp₀⟩ := S.hint j
    by_cases h0 : hole_rot o u ⬝ᵥ (p₀ - q) = 0
    · obtain ⟨δ, hδ, hδp⟩ := hole_exists_pos_of_eventually
        (hole_eventually_add_smul_mem isOpen_interior hp₀ (hole_rot o u))
      refine ⟨_, hδp, ?_⟩
      rw [show p₀ + δ • hole_rot o u - q = (p₀ - q) + δ • hole_rot o u by abel, dotProduct_add,
        h0, dotProduct_smul, smul_eq_mul, zero_add]
      exact (mul_pos hδ hrr).ne'
    · exact ⟨p₀, hp₀, h0⟩
  rcases hpne.lt_or_gt with hneg | hpos
  · -- `C j` reaches into the interior of `C i`
    have ho' : (-o) * (-o) = 1 := by rw [neg_mul_neg]; exact ho
    have hj' : 0 < hole_rot (-o) (b - q) ⬝ᵥ (p - q) := by
      rw [hbq, hole_rot_neg_o, hole_rot_smul, neg_dotProduct, smul_dotProduct, smul_eq_mul]
      nlinarith
    obtain ⟨pi, hpi⟩ := S.hint i
    have hi' : 0 < hole_rot (-o) (b - q) ⬝ᵥ (pi - q) := by
      rw [hbq, hole_rot_neg_o, hole_rot_smul, neg_dotProduct, smul_dotProduct, smul_eq_mul]
      have := hright' pi hpi
      nlinarith
    obtain ⟨σ₁, hσ₁, h₁⟩ := hole_bump_interior ho' (S.convex_C j) hqj hbj hp hj'
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    obtain ⟨σ₂, hσ₂, h₂⟩ := hole_bump_interior ho' (S.convex_C i) hq hbi hpi hi'
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hσ := lt_min hσ₁ hσ₂
    exact Set.disjoint_left.1 (S.hdisj hji) (h₁ _ hσ (min_le_left _ _))
      (h₂ _ hσ (min_le_right _ _))
  · -- `C j` reaches into `U`
    have hj' : 0 < hole_rot o (b - q) ⬝ᵥ (p - q) := by
      rw [hbq, hole_rot_smul, smul_dotProduct, smul_eq_mul]; positivity
    obtain ⟨σ₁, hσ₁, h₁⟩ := hole_bump_interior ho (S.convex_C j) hqj hbj hp hj'
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    set σ := min σ₁ (ε₀ / 4)
    have hσ : 0 < σ := lt_min hσ₁ (by positivity)
    have hzj := h₁ σ hσ (min_le_left _ _)
    have hz : q + (1 / 2 : ℝ) • (b - q) + σ • hole_rot o (b - q) =
        q + (τ₁ / 2) • u + (σ * τ₁) • hole_rot o u := by
      rw [hbq, hole_rot_smul]; module
    rw [hz] at hzj
    have hσ4 : σ ≤ ε₀ / 4 := min_le_right _ _
    have hb4 := mul_le_mul_of_nonneg_right hσ4 hτ₁0.le
    have hzU := htri (hole_mem_tri (τ := τ₁ / 2) (σ := σ * τ₁) hT₀ (mul_pos hσ hτ₁0)
      (by nlinarith) (by nlinarith))
    exact S.notMem_C_of_mem_U hzU j (interior_subset hzj)

/-- Near the first endpoint of the side of a state, no other cell meets the side. -/
lemma IsState.eventually_notMem {o : ℝ} (ho : o * o = 1) {i : Fin n} {q u : Fin 2 → ℝ}
    (hs : S.IsState o i q u) :
    ∃ δ > (0 : ℝ), ∀ j, j ≠ i → ∀ τ : ℝ, 0 < τ → τ < δ → q + τ • u ∉ S.C j := by
  obtain ⟨r, hr, hcon⟩ := S.conic q
  have hev : ∀ j, ∀ᶠ τ in 𝓝[>] (0 : ℝ), j ≠ i → q + τ • u ∉ S.C j := by
    intro j
    by_cases hqj : q ∈ S.C j
    · have hball : ∀ᶠ τ in 𝓝[>] (0 : ℝ), q + τ • u ∈ Metric.ball q r :=
        (hole_eventually_add_smul_mem Metric.isOpen_ball (Metric.mem_ball_self hr) u).filter_mono
          nhdsWithin_le_nhds
      filter_upwards [hball, self_mem_nhdsWithin] with τ hτb hτ0 hji hτj
      apply hs.not_touch ho hji hτ0
      intro τ' hτ' hτ'τ
      have := (hcon j (q + τ • u) hτb (τ' / τ) (div_pos hτ' hτ0)
        (div_le_one_of_le₀ hτ'τ (le_of_lt hτ0))).1 hτj
      rwa [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ (ne_of_gt hτ0)] at this
    · have : ∀ᶠ τ in 𝓝 (0 : ℝ), q + τ • u ∈ (S.C j)ᶜ :=
        hole_eventually_add_smul_mem (S.isClosed_C j).isOpen_compl hqj u
      filter_upwards [this.filter_mono nhdsWithin_le_nhds] with τ hτ _ using hτ
  obtain ⟨δ, hδ, h⟩ := hole_exists_Ioo_of_eventually (Filter.eventually_all.2 hev)
  exact ⟨δ, hδ, fun j hji τ h0 h1 ↦ h τ h0 h1 j hji⟩

/-- A thin triangle over a part `[q, q + T u]` of the side of a state which no other cell meets
lies in `U`. -/
lemma IsState.tri_subset {o : ℝ} (ho : o * o = 1) {i : Fin n} {q u : Fin 2 → ℝ}
    (hs : S.IsState o i q u) {L : ℝ} (hL : 0 < L)
    (hseg : ∀ τ : ℝ, 0 ≤ τ → τ ≤ L → q + τ • u ∈ S.C i) {T : ℝ} (hT : 0 < T) (hTL : T ≤ L)
    (havoid : ∀ j, j ≠ i → ∀ τ : ℝ, 0 < τ → τ < T → q + τ • u ∉ S.C j) :
    ∃ ε > (0 : ℝ), hole_tri o q (q + T • u) ε ⊆ S.U := by
  obtain ⟨hu, hq, -, -, hright, ⟨T₀, hT₀, ε₀, hε₀, htri₀⟩⟩ := hs
  have hrr := hole_rot_dot_rot_self_pos ho hu
  -- the other cells
  have hcells : ∀ j, ∃ ε > (0 : ℝ), ∀ ε', 0 < ε' → ε' ≤ ε →
      (j ≠ i → ∀ x ∈ hole_tri o q (q + T • u) ε', x ∉ S.C j) := by
    intro j
    by_cases hji : j = i
    · exact ⟨1, one_pos, fun _ _ _ h ↦ absurd hji h⟩
    obtain ⟨ε, hε, h⟩ := hole_avoid_tri (S.a j) (S.c j) o (q := q) (q' := q + T • u)
      (fun t ht0 ht1 ↦ by
        rw [← S.hac j, add_sub_cancel_left, smul_smul]
        exact havoid j hji _ (by positivity) (by nlinarith))
    refine ⟨ε, hε, fun ε' _ hε' _ x hx ↦ ?_⟩
    rw [S.hac j]; exact h x (hole_tri_mono hε' hx)
  obtain ⟨ε₁, hε₁, h₁⟩ := hole_exists_pos_forall hcells
  -- the container
  have hp₀ : q + (T₀ / 2) • u + (ε₀ * T₀ / 4) • hole_rot o u ∈ S.Q :=
    S.U_subset_Q (htri₀ (hole_mem_tri (τ := T₀ / 2) (σ := ε₀ * T₀ / 4) hT₀ (by positivity)
      (by nlinarith) (by nlinarith)))
  have hqL : q + L • u ∈ S.Q := S.C_subset_Q i (hseg L hL.le le_rfl)
  have hpos : 0 < hole_rot o ((q + L • u) - q) ⬝ᵥ
      ((q + (T₀ / 2) • u + (ε₀ * T₀ / 4) • hole_rot o u) - q) := by
    rw [add_sub_cancel_left, show q + (T₀ / 2) • u + (ε₀ * T₀ / 4) • hole_rot o u - q =
      (T₀ / 2) • u + (ε₀ * T₀ / 4) • hole_rot o u by abel, hole_rot_smul, smul_dotProduct,
      dotProduct_add, dotProduct_smul, dotProduct_smul, hole_rot_dot_self, smul_zero, zero_add,
      smul_eq_mul, smul_eq_mul]
    positivity
  obtain ⟨σ₀, hσ₀, hbump⟩ := hole_bump ho S.convex_Q (S.C_subset_Q i hq) hqL hp₀ hpos
    (θ := T / (2 * L)) (by positivity) (by rw [div_lt_one (by positivity)]; linarith)
  have hy := hbump σ₀ hσ₀ le_rfl
  set κ := σ₀ * L with hκ
  have hκ0 : 0 < κ := by positivity
  have hyeq : q + (T / (2 * L)) • ((q + L • u) - q) + σ₀ • hole_rot o ((q + L • u) - q) =
      q + (T / 2) • u + κ • hole_rot o u := by
    rw [add_sub_cancel_left, hole_rot_smul, smul_smul, smul_smul]
    congr 2; field_simp
  rw [hyeq] at hy
  have hqT : q + T • u ∈ S.Q := S.C_subset_Q i (hseg T hT.le hTL)
  have hQ : ∀ x ∈ hole_tri o q (q + T • u) (2 * κ / T), x ∈ S.Q := by
    intro x hx
    obtain ⟨τ, σ, hσ, h1, h2, rfl⟩ := hole_tri_elim hT hx
    rw [div_mul_eq_mul_div, lt_div_iff₀ hT] at h1 h2
    have := hole_convex_three S.convex_Q (S.C_subset_Q i hq) hqT hy
      (w₁ := 1 - τ / T - σ / (2 * κ)) (w₂ := τ / T - σ / (2 * κ)) (w₃ := σ / κ)
      (by rw [sub_sub, sub_nonneg, div_add_div _ _ hT.ne' (by positivity),
        div_le_one (by positivity)]; nlinarith)
      (by rw [sub_nonneg, div_le_div_iff₀ (by positivity) hT]; nlinarith)
      (by positivity) (by ring)
    convert this using 1
    simp only [smul_add, smul_smul]
    match_scalars <;> field_simp <;> ring
  set ε := min ε₁ (2 * κ / T) with hεdef
  have hε : 0 < ε := lt_min hε₁ (by positivity)
  have hTF : hole_tri o q (q + T • u) ε ⊆ S.F := by
    intro x hx
    refine ⟨hQ x (hole_tri_mono (min_le_right _ _) hx), ?_⟩
    rw [mem_iUnion]
    rintro ⟨j, hxj⟩
    by_cases hji : j = i
    · subst hji
      obtain ⟨τ, σ, hσ, -, -, rfl⟩ := hole_tri_elim hT hx
      have := hright _ hxj
      rw [show q + τ • u + σ • hole_rot o u - q = τ • u + σ • hole_rot o u by abel,
        dotProduct_add, dotProduct_smul, dotProduct_smul, hole_rot_dot_self, smul_zero,
        zero_add, smul_eq_mul] at this
      nlinarith
    · exact h₁ j hji x (hole_tri_mono (min_le_left _ _) hx) hxj
  set τc := min T T₀ / 2
  have hτc : 0 < τc := by positivity
  have hτcT : τc ≤ T / 2 := by
    have := min_le_left T T₀; simp only [τc]; linarith
  have hτcT₀ : τc ≤ T₀ / 2 := by
    have := min_le_right T T₀; simp only [τc]; linarith
  set σc := min ε ε₀ * τc / 2
  have hσc : 0 < σc := by have := lt_min hε hε₀; positivity
  have hσce : σc = min ε ε₀ * τc / 2 := rfl
  have hm1 := mul_le_mul_of_nonneg_right (min_le_left ε ε₀) hτc.le
  have hm2 := mul_le_mul_of_nonneg_right (min_le_right ε ε₀) hτc.le
  have hk1 := mul_le_mul_of_nonneg_left (by linarith : τc ≤ T - τc) hε.le
  have hk2 := mul_le_mul_of_nonneg_left (by linarith : τc ≤ T₀ - τc) hε₀.le
  have hετ : 0 < ε * τc := mul_pos hε hτc
  have hε₀τ : 0 < ε₀ * τc := mul_pos hε₀ hτc
  have hz : q + τc • u + σc • hole_rot o u ∈ hole_tri o q (q + T • u) ε :=
    hole_mem_tri hT hσc (by linarith) (by linarith)
  have hz₀ : q + τc • u + σc • hole_rot o u ∈ hole_tri o q (q + T₀ • u) ε₀ :=
    hole_mem_tri hT₀ hσc (by linarith) (by linarith)
  exact ⟨ε, hε, S.subset_U (hole_convex_tri o _ _ ε).isPreconnected hTF hz (htri₀ hz₀)⟩

/-- **The dart of a state.** From `q` on, the side of `C i` is bordered by `U` up to the first
point `q' = q + T u` met by another cell; by the rotation lemma `q'` lies in the relative interior
of the side, so it is a side point of `C i` with outer normal `J u`. -/
lemma IsState.dart {o : ℝ} (ho : o * o = 1) {i : Fin n} {q u : Fin 2 → ℝ}
    (hs : S.IsState o i q u) : ∃ T > (0 : ℝ),
      (∃ ε > (0 : ℝ), hole_tri o q (q + T • u) ε ⊆ S.U) ∧ (∃ j, j ≠ i ∧ q + T • u ∈ S.C j) ∧
      (∃ ε > (0 : ℝ), ∀ x, dist x (q + T • u) < ε →
        (x ∈ S.C i ↔ hole_rot o u ⬝ᵥ (x - (q + T • u)) ≤ 0)) := by
  obtain ⟨L, hL, hseg, -, l, ⟨μ, hμ, hμl⟩, hlq, hface⟩ := hs.face ho
  obtain ⟨δ, hδ, hD2⟩ := hs.eventually_notMem ho
  have hu := hs.1
  have hq := hs.2.1
  have hright := hs.2.2.2.2.1
  have hLu : L • u ≠ 0 := smul_ne_zero hL.ne' hu
  have hqL : q ≠ q + L • u := by
    intro h; apply hLu; rw [← add_sub_cancel_left q (L • u), ← h, sub_self]
  -- by the rotation lemma, another cell meets the open side
  have hex : ∃ j, j ≠ i ∧ ∃ τ : ℝ, 0 < τ ∧ τ < L ∧ q + τ • u ∈ S.C j := by
    by_contra hcon
    push Not at hcon
    obtain ⟨ε, hε, htri⟩ := hs.tri_subset ho hL hseg hL le_rfl
      (fun j hji τ h0 h1 ↦ hcon j hji τ h0 h1)
    refine S.rotation_contra i l (q' := q + L • u) hqL hq (hseg L hL.le le_rfl) hlq ?_ hface ?_
      hε (htri.trans S.U_subset_F)
    · rw [dotProduct_add, hlq, hμl, smul_dotProduct, dotProduct_smul, hole_rot_dot_self,
        smul_zero, smul_zero, add_zero]
    · rw [add_sub_cancel_left, hμl, hole_rot_smul, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, smul_eq_mul]
      have := hole_rot_dot_rot_self_pos ho hu
      positivity
  obtain ⟨j₀, hj₀i, τw, hτw0, hτwL, hτwj⟩ := hex
  have hτwδ : δ ≤ τw := by
    by_contra h; push Not at h; exact hD2 j₀ hj₀i τw hτw0 h hτwj
  set B := {τ : ℝ | δ ≤ τ ∧ ∃ j, j ≠ i ∧ q + τ • u ∈ S.C j} with hB
  have hBeq : B = Ici δ ∩ ⋃ j : {j : Fin n // j ≠ i}, (fun τ : ℝ ↦ q + τ • u) ⁻¹' S.C j := by
    ext τ
    simp only [hB, mem_ofPred_eq, mem_inter_iff, mem_Ici, mem_iUnion, mem_preimage,
      Subtype.exists, exists_prop]
  have hBc : IsClosed B := by
    rw [hBeq]
    exact isClosed_Ici.inter
      (isClosed_iUnion_of_finite fun j ↦ (S.isClosed_C j).preimage (by fun_prop))
  have hBne : B.Nonempty := ⟨τw, hτwδ, j₀, hj₀i, hτwj⟩
  have hBbdd : BddBelow B := ⟨δ, fun τ hτ ↦ hτ.1⟩
  set T := sInf B with hTdef
  have hTB : T ∈ B := hBc.csInf_mem hBne hBbdd
  have hT0 : 0 < T := hδ.trans_le hTB.1
  have hTL : T < L := (csInf_le hBbdd ⟨hτwδ, j₀, hj₀i, hτwj⟩).trans_lt hτwL
  have havoid : ∀ j, j ≠ i → ∀ τ : ℝ, 0 < τ → τ < T → q + τ • u ∉ S.C j := by
    intro j hji τ h0 h1 hτj
    by_cases hτδ : τ < δ
    · exact hD2 j hji τ h0 hτδ hτj
    · push Not at hτδ
      exact absurd (csInf_le hBbdd ⟨hτδ, j, hji, hτj⟩) (not_le.2 h1)
  obtain ⟨ε, hε, htri⟩ := hs.tri_subset ho hL hseg hT0 hTL.le havoid
  obtain ⟨j, hji, hTj⟩ := hTB.2
  refine ⟨T, hT0, ⟨ε, hε, htri⟩, ⟨j, hji, hTj⟩, ?_⟩
  -- the end point is a side point of `C i`
  have hCi := S.hac i
  obtain ⟨-, -, ε', hε', hside⟩ := hole_relint (S.a i) (S.c i) (hCi ▸ S.hint i)
    (hole_rot_ne_zero ho hu) (fun x hx ↦ hright x (hCi ▸ hx)) (hCi ▸ hq)
    (hCi ▸ hseg L hL.le le_rfl) hqL
    (by rw [add_sub_cancel_left, dotProduct_smul, hole_rot_dot_self, smul_zero])
    (div_pos hT0 hL) (by rw [div_lt_one hL]; exact hTL)
  have hm : q + (T / L) • (q + L • u - q) = q + T • u := by
    rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hL.ne']
  rw [hm] at hside
  refine ⟨ε', hε', fun x hx ↦ ?_⟩
  rw [hCi]; exact hside x hx

/-- **The sweep.** At a point `z`, turning from a direction `w₀` into `U` towards a direction `w₁`
into a cell `C j` (`⟨J w₁, w₀⟩ > 0`), let `u = (1 - θ) w₀ + θ w₁` be the first direction into a
cell `C i`. Then `C i` contains `z` and some `z + T u`, lies on the right of the line through `z`
with direction `u`, and a thin triangle on the left of this line lies in `U`. -/
lemma sweep {o : ℝ} (ho : o * o = 1) {z w₀ w₁ : Fin 2 → ℝ} {j : Fin n}
    (h₀ : ∀ t : ℝ, 0 < t → t ≤ 1 → z + t • w₀ ∈ S.U)
    (h₁ : ∀ t : ℝ, 0 < t → t ≤ 1 → z + t • w₁ ∈ S.C j)
    (hw : 0 < hole_rot o w₁ ⬝ᵥ w₀) :
    ∃ i, ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ z ∈ S.C i ∧
      (∃ T > (0 : ℝ), z + T • ((1 - θ) • w₀ + θ • w₁) ∈ S.C i) ∧
      (∀ x ∈ S.C i, hole_rot o ((1 - θ) • w₀ + θ • w₁) ⬝ᵥ (x - z) ≤ 0) ∧
      (∃ T > (0 : ℝ), ∃ ε > (0 : ℝ),
        hole_tri o z (z + T • ((1 - θ) • w₀ + θ • w₁)) ε ⊆ S.U) := by
  obtain ⟨r, hr, hcon⟩ := S.conic z
  set W : ℝ → Fin 2 → ℝ := fun θ ↦ (1 - θ) • w₀ + θ • w₁ with hW
  set M := ‖w₀‖ + ‖w₁‖ + 1 with hM
  have hM0 : 0 < M := by positivity
  set t₀ := min 1 (r / (2 * M)) with ht₀
  have ht₀0 : 0 < t₀ := lt_min one_pos (by positivity)
  have ht₀1 : t₀ ≤ 1 := min_le_left _ _
  have ht₀r : t₀ * M ≤ r / 2 := by
    have := min_le_right 1 (r / (2 * M))
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hWnorm : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ‖W θ‖ ≤ M := by
    intro θ h0 h1
    calc ‖W θ‖ ≤ ‖(1 - θ) • w₀‖ + ‖θ • w₁‖ := norm_add_le _ _
      _ = (1 - θ) * ‖w₀‖ + θ * ‖w₁‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
          abs_of_nonneg (by linarith)]
      _ ≤ M := by
        have := norm_nonneg w₀; have := norm_nonneg w₁; rw [hM]; nlinarith
  have hball : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ t : ℝ, 0 ≤ t → t ≤ t₀ →
      z + t • W θ ∈ Metric.ball z (r / 2 + r / 4) := by
    intro θ h0 h1 t ht ht'
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht]
    have := hWnorm θ h0 h1
    have : t * ‖W θ‖ ≤ t₀ * M := mul_le_mul ht' this (norm_nonneg _) ht₀0.le
    linarith
  have hball' : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ t : ℝ, 0 ≤ t → t ≤ t₀ →
      z + t • W θ ∈ Metric.ball z r := fun θ h0 h1 t ht ht' ↦
    Metric.ball_subset_ball (by linarith) (hball θ h0 h1 t ht ht')
  -- the set of directions into cells
  set Λ := {θ : ℝ | θ ∈ Icc (0 : ℝ) 1 ∧ z + t₀ • W θ ∈ ⋃ k, S.C k} with hΛ
  have hΛc : IsClosed Λ :=
    isClosed_Icc.inter (S.isClosed_iUnion_C.preimage (by fun_prop))
  have h1Λ : (1 : ℝ) ∈ Λ := by
    refine ⟨⟨zero_le_one, le_rfl⟩, mem_iUnion.2 ⟨j, ?_⟩⟩
    simpa [W] using h₁ t₀ ht₀0 ht₀1
  have h0Λ : (0 : ℝ) ∉ Λ := by
    rintro ⟨-, h⟩
    obtain ⟨k, hk⟩ := mem_iUnion.1 h
    simp only [W, sub_zero, one_smul, zero_smul, add_zero] at hk
    exact S.notMem_C_of_mem_U (h₀ t₀ ht₀0 ht₀1) k hk
  have hΛbdd : BddBelow Λ := ⟨0, fun θ hθ ↦ hθ.1.1⟩
  set θs := sInf Λ with hθs
  have hθsΛ : θs ∈ Λ := hΛc.csInf_mem ⟨1, h1Λ⟩ hΛbdd
  have hθs0 : 0 < θs := lt_of_le_of_ne hθsΛ.1.1 fun h ↦ h0Λ (h ▸ hθsΛ)
  have hθs1 : θs ≤ 1 := hθsΛ.1.2
  -- no cell in the directions before `θs`
  have hK1 : ∀ θ : ℝ, 0 ≤ θ → θ < θs → ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ k, z + t • W θ ∉ S.C k := by
    intro θ h0 h1 t ht ht' k hk
    have hθ1 : θ ≤ 1 := (h1.trans_le hθs1).le
    have hx := hball' θ h0 hθ1 t₀ ht₀0.le le_rfl
    have hmem : z + t₀ • W θ ∈ S.C k := by
      have := (hcon k _ hx (t / t₀) (div_pos ht ht₀0) (div_le_one_of_le₀ ht' ht₀0.le)).2
      rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ ht₀0.ne'] at this
      exact this hk
    exact absurd (csInf_le hΛbdd ⟨⟨h0, hθ1⟩, mem_iUnion.2 ⟨k, hmem⟩⟩) (not_le.2 h1)
  -- the sector before `θs` lies in `U`
  set Sec := (fun p : ℝ × ℝ ↦ z + p.1 • W p.2) '' (Ioc 0 t₀ ×ˢ Ico 0 θs) with hSec
  have hSecF : Sec ⊆ S.F := by
    rintro _ ⟨⟨t, θ⟩, ⟨⟨ht, ht'⟩, ⟨hθ, hθ'⟩⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have h0' := S.U_subset_Q (h₀ t ht (ht'.trans ht₀1))
      have h1' := S.C_subset_Q j (h₁ t ht (ht'.trans ht₀1))
      have := S.convex_Q h0' h1' (sub_nonneg.2 (hθ'.trans_le hθs1).le) hθ (by ring)
      convert this using 1
      simp only [W]; module
    · rw [mem_iUnion]; rintro ⟨k, hk⟩; exact hK1 θ hθ hθ' t ht ht' k hk
  have hSecpc : IsPreconnected Sec :=
    (isPreconnected_Ioc.prod isPreconnected_Ico).image _
      (by fun_prop : Continuous fun p : ℝ × ℝ ↦ z + p.1 • W p.2).continuousOn
  have hz0 : z + t₀ • W 0 ∈ S.U := by
    simpa [W] using h₀ t₀ ht₀0 ht₀1
  have hSecU : Sec ⊆ S.U :=
    S.subset_U hSecpc hSecF ⟨(t₀, 0), ⟨⟨ht₀0, le_rfl⟩, ⟨le_rfl, hθs0⟩⟩, rfl⟩ hz0
  set u := W θs with hu
  have hrw : 0 < hole_rot o u ⬝ᵥ w₀ := by
    have : hole_rot o u ⬝ᵥ w₀ = θs * (hole_rot o w₁ ⬝ᵥ w₀) := by
      simp only [u, W, hole_rot_add, hole_rot_smul, add_dotProduct, smul_dotProduct,
        hole_rot_dot_self, smul_eq_mul, mul_zero, zero_add]
    rw [this]; positivity
  have hmemSec : ∀ α β : ℝ, 0 < α → 0 < β → α + β ≤ t₀ → z + α • u + β • w₀ ∈ S.U := by
    intro α β hα hβ hαβ
    apply hSecU
    refine ⟨(α + β, α * θs / (α + β)), ⟨⟨by positivity, hαβ⟩, ⟨by positivity, ?_⟩⟩, ?_⟩
    · rw [div_lt_iff₀ (by positivity)]; nlinarith
    · have hab : α + β ≠ 0 := by positivity
      have e1 : (α + β) * (1 - α * θs / (α + β)) = α * (1 - θs) + β := by
        field_simp; ring
      have e2 : (α + β) * (α * θs / (α + β)) = α * θs := by field_simp
      simp only [u, W]
      rw [smul_add, smul_smul, smul_smul, e1, e2]
      module
  obtain ⟨i, hi⟩ := mem_iUnion.1 hθsΛ.2
  have hray : ∀ t : ℝ, 0 < t → t ≤ t₀ → z + t • u ∈ S.C i := by
    intro t ht ht'
    have := (hcon i _ (hball' θs hθs0.le hθs1 t₀ ht₀0.le le_rfl) (t / t₀) (div_pos ht ht₀0)
      (div_le_one_of_le₀ ht' ht₀0.le)).1 hi
    rwa [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ ht₀0.ne'] at this
  have hzi : z ∈ S.C i := hole_mem_of_forall_pos (S.isClosed_C i) ht₀0 hray
  have hne : hole_rot o u ⬝ᵥ w₀ ≠ 0 := hrw.ne'
  have hne' : hole_rot o w₀ ⬝ᵥ u ≠ 0 := by
    rw [hole_rot_dot_comm, dotProduct_comm]; exact neg_ne_zero.2 hne
  refine ⟨i, θs, hθs0, hθs1, hzi, ⟨t₀, ht₀0, hray t₀ ht₀0 le_rfl⟩, ?_, ?_⟩
  · -- `C i` lies on the right
    intro x hx
    by_contra hpos
    push Not at hpos
    set G := hole_rot o w₀ ⬝ᵥ (x - z) / (hole_rot o w₀ ⬝ᵥ u) with hG
    have hev : ∀ᶠ κ in 𝓝 (0 : ℝ), 0 < (1 - κ) * t₀ + κ * G ∧
        (z + t₀ • u) + κ • (x - (z + t₀ • u)) ∈ Metric.ball z r ∧ κ < 1 := by
      refine (continuousAt_const.eventually_lt
        (?_ : ContinuousAt (fun κ : ℝ ↦ (1 - κ) * t₀ + κ * G) 0) (by simpa using ht₀0)).and
        ((hole_eventually_add_smul_mem Metric.isOpen_ball
          (hball' θs hθs0.le hθs1 t₀ ht₀0.le le_rfl) _).and (eventually_lt_nhds one_pos))
      fun_prop
    obtain ⟨κ, hκ, hαpos, hκball, hκ1⟩ := hole_exists_pos_of_eventually hev
    set p := (z + t₀ • u) + κ • (x - (z + t₀ • u)) with hp
    have hpi : p ∈ S.C i := by
      have := (S.convex_C i) (hray t₀ ht₀0 le_rfl) hx (by linarith : (0 : ℝ) ≤ 1 - κ) hκ.le
        (by ring)
      convert this using 1; rw [hp]; module
    set d := p - z with hd
    have hdec := hole_decomp ho hne d
    set α := hole_rot o w₀ ⬝ᵥ d / (hole_rot o w₀ ⬝ᵥ u) with hα
    set β := hole_rot o u ⬝ᵥ d / (hole_rot o u ⬝ᵥ w₀) with hβ
    have hdz : d = (1 - κ) • (t₀ • u) + κ • (x - z) := by rw [hd, hp]; module
    have hαe : α = (1 - κ) * t₀ + κ * G := by
      rw [hα, hdz, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_smul,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, hG]
      field_simp
    have hβpos : 0 < β := by
      rw [hβ, hdz, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_smul,
        hole_rot_dot_self, smul_zero, smul_zero, zero_add, smul_eq_mul]
      positivity
    have hαpos' : 0 < α := hαe ▸ hαpos
    set s := min 1 (t₀ / (α + β)) with hs
    have hs0 : 0 < s := lt_min one_pos (by positivity)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hsab : s * (α + β) ≤ t₀ := by
      have := min_le_right 1 (t₀ / (α + β))
      rw [le_div_iff₀ (by positivity)] at this; linarith
    have hin : z + s • (p - z) ∈ S.C i := (hcon i p hκball s hs0 hs1).1 hpi
    have heq : z + s • (p - z) = z + (s * α) • u + (s * β) • w₀ := by
      rw [← hd, hdec, smul_add, smul_smul, smul_smul, add_assoc]
    rw [heq] at hin
    exact S.notMem_C_of_mem_U (hmemSec _ _ (by positivity) (by positivity) (by nlinarith)) i hin
  · -- the thin triangle on the left lies in `U`
    set G := hole_rot o w₀ ⬝ᵥ hole_rot o u / (hole_rot o w₀ ⬝ᵥ u) with hG
    set N := hole_rot o u ⬝ᵥ hole_rot o u / (hole_rot o u ⬝ᵥ w₀) with hN
    have hu0 : u ≠ 0 := by intro h; rw [h] at hrw; simp [hole_rot] at hrw
    have hN0 : 0 < N := by
      rw [hN]; exact div_pos (hole_rot_dot_rot_self_pos ho hu0) hrw
    set ε := 1 / (|G| + N + 1) with hεdef
    have hε : 0 < ε := by positivity
    have hεsum : ε * (|G| + N + 1) = 1 := by rw [hεdef]; field_simp
    have h5 : ε * |G| < 1 := by nlinarith
    have h6 : ε * (|G| + N) < 1 := by nlinarith
    refine ⟨t₀ / 2, by positivity, ε, hε, ?_⟩
    intro x hx
    obtain ⟨τ, σ, hσ, h1, h2, rfl⟩ := hole_tri_elim (by positivity) hx
    have hτ0 : 0 < τ := by by_contra h; push Not at h; nlinarith
    have hτT : τ < t₀ / 2 := by by_contra h; push Not at h; nlinarith
    set v := τ • u + σ • hole_rot o u with hv
    have hdec := hole_decomp ho hne v
    set α := hole_rot o w₀ ⬝ᵥ v / (hole_rot o w₀ ⬝ᵥ u) with hα
    set β := hole_rot o u ⬝ᵥ v / (hole_rot o u ⬝ᵥ w₀) with hβ
    have hαe : α = τ + σ * G := by
      rw [hα, hv, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        hG]
      field_simp
    have hβe : β = σ * N := by
      rw [hβ, hv, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        hole_rot_dot_self, mul_zero, zero_add, hN]
      field_simp
    have h4 : σ * |G| ≤ ε * τ * |G| := mul_le_mul_of_nonneg_right h1.le (abs_nonneg G)
    have h4' : σ * (|G| + N) ≤ ε * τ * (|G| + N) :=
      mul_le_mul_of_nonneg_right h1.le (by positivity)
    have hσG : -(σ * |G|) ≤ σ * G := by nlinarith [neg_abs_le G]
    have hσG' : σ * G ≤ σ * |G| := by nlinarith [le_abs_self G]
    have h7 : τ * (ε * |G|) < τ := mul_lt_of_lt_one_right hτ0 h5
    have h8 : τ * (ε * (|G| + N)) < τ := mul_lt_of_lt_one_right hτ0 h6
    have hαpos : 0 < α := by rw [hαe]; linarith
    have hβpos : 0 < β := by rw [hβe]; positivity
    have hsum : α + β ≤ t₀ := by
      have : σ * G + σ * N ≤ σ * (|G| + N) := by linarith
      rw [hαe, hβe]; linarith
    have hx : z + τ • u + σ • hole_rot o u = z + α • u + β • w₀ := by
      rw [add_assoc, ← hv, hdec, add_assoc]
    rw [hx]
    exact hmemSec α β hαpos hβpos hsum

/-- **The next state.** At the end `q' = q + T u` of the dart of a state, sweeping from the
direction back along the side (on the side of `U`) towards a direction into the cell met at `q'`
gives a state starting at `q'`. -/
lemma IsState.next {o : ℝ} (ho : o * o = 1) {i : Fin n} {q u : Fin 2 → ℝ}
    (hs : S.IsState o i q u) {T : ℝ} (hT : 0 < T)
    (htri : ∃ ε > (0 : ℝ), hole_tri o q (q + T • u) ε ⊆ S.U)
    (hj : ∃ j, j ≠ i ∧ q + T • u ∈ S.C j)
    (hside : ∃ ε > (0 : ℝ), ∀ x, dist x (q + T • u) < ε →
      (x ∈ S.C i ↔ hole_rot o u ⬝ᵥ (x - (q + T • u)) ≤ 0)) :
    ∃ i' u', S.IsState o i' (q + T • u) u' := by
  obtain ⟨εt, hεt, htri⟩ := htri
  obtain ⟨j, hji, hqj⟩ := hj
  obtain ⟨εs, hεs, hside⟩ := hside
  set q' := q + T • u with hq'
  have hu := hs.1
  have hrr := hole_rot_dot_rot_self_pos ho hu
  -- a direction into `C j`, strictly on the side of `U`
  obtain ⟨p, hp⟩ := S.hint j
  have hp_left : 0 ≤ hole_rot o u ⬝ᵥ (p - q') := by
    by_contra hneg
    push Not at hneg
    obtain ⟨η, hη, hηb, hη1⟩ := hole_exists_pos_of_eventually
      ((hole_eventually_add_smul_mem Metric.isOpen_ball (Metric.mem_ball_self hεs) (p - q')).and
        (eventually_lt_nhds one_pos))
    have hyj : q' + η • (p - q') ∈ interior (S.C j) := by
      have := (S.convex_C j).combo_interior_self_mem_interior hp hqj (a := η) (b := 1 - η) hη
        (by linarith) (by ring)
      convert this using 1; module
    have hyi : q' + η • (p - q') ∈ interior (S.C i) := by
      refine hole_mem_interior_of_side hside hηb ?_
      rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul]; nlinarith
    exact Set.disjoint_left.1 (S.hdisj hji) hyj hyi
  obtain ⟨η, hη, hηp⟩ := hole_exists_pos_of_eventually
    (hole_eventually_add_smul_mem isOpen_interior hp (hole_rot o u))
  set w₁ := (p + η • hole_rot o u) - q' with hw₁
  have hA : 0 < hole_rot o u ⬝ᵥ w₁ := by
    rw [hw₁, show p + η • hole_rot o u - q' = (p - q') + η • hole_rot o u by abel,
      dotProduct_add, dotProduct_smul, smul_eq_mul]
    have := mul_pos hη hrr; linarith
  have h₁ : ∀ t : ℝ, 0 < t → t ≤ 1 → q' + t • w₁ ∈ S.C j := by
    intro t ht ht1
    have := (S.convex_C j) hqj (interior_subset hηp) (by linarith : (0 : ℝ) ≤ 1 - t) ht.le
      (by ring)
    convert this using 1; rw [hw₁]; module
  -- the direction back along the side, turned towards `U`
  set A := hole_rot o u ⬝ᵥ w₁ with hAdef
  set B := |w₁ ⬝ᵥ u| with hB
  set κ := min (εt / 2) (A / (2 * (B + 1))) with hκdef
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  have hκε : κ < εt := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hκB : κ * B ≤ A / 2 := by
    have h := min_le_right (εt / 2) (A / (2 * (B + 1)))
    have hB0 : 0 ≤ B := abs_nonneg _
    calc κ * B ≤ A / (2 * (B + 1)) * B := mul_le_mul_of_nonneg_right h hB0
      _ ≤ A / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  set ρ := εt * T / (2 * (κ + εt)) with hρdef
  have hρ : 0 < ρ := by positivity
  have hρκ : ρ * (κ + εt) = εt * T / 2 := by rw [hρdef]; field_simp
  set w₀ := ρ • (-u + κ • hole_rot o u) with hw₀
  have h₀ : ∀ t : ℝ, 0 < t → t ≤ 1 → q' + t • w₀ ∈ S.U := by
    intro t ht ht1
    apply htri
    have e : q' + t • w₀ = q + (T - t * ρ) • u + (t * ρ * κ) • hole_rot o u := by
      rw [hq', hw₀]; module
    rw [e]
    have h1 : t * ρ * (κ + εt) ≤ ρ * (κ + εt) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    refine hole_mem_tri hT (by positivity) ?_ ?_
    · nlinarith
    · have : t * ρ * κ < εt * (t * ρ) := by
        have := mul_pos ht hρ; nlinarith
      linarith
  have hw : 0 < hole_rot o w₁ ⬝ᵥ w₀ := by
    have e : hole_rot o w₁ ⬝ᵥ w₀ = ρ * (A + κ * (w₁ ⬝ᵥ u)) := by
      rw [hw₀, dotProduct_smul, dotProduct_add, dotProduct_neg, dotProduct_smul,
        hole_rot_dot_rot ho, hole_rot_dot_comm, dotProduct_comm w₁ (hole_rot o u), hAdef,
        smul_eq_mul, smul_eq_mul]
      ring
    rw [e]
    have := neg_abs_le (w₁ ⬝ᵥ u)
    have : -(κ * B) ≤ κ * (w₁ ⬝ᵥ u) := by rw [hB]; nlinarith
    exact mul_pos hρ (by linarith)
  obtain ⟨i', θ, hθ0, hθ1, hzi', ⟨T', hT', hT'i'⟩, hright', hleft'⟩ := S.sweep ho h₀ h₁ hw
  set u' := (1 - θ) • w₀ + θ • w₁ with hu'
  have hrot_u' : 0 < hole_rot o u ⬝ᵥ u' := by
    have e : hole_rot o u ⬝ᵥ u' = (1 - θ) * (ρ * κ * (hole_rot o u ⬝ᵥ hole_rot o u)) + θ * A := by
      rw [hu', hw₀, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_smul,
        dotProduct_add, dotProduct_neg, dotProduct_smul, hole_rot_dot_self, smul_eq_mul,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, hAdef]
      ring
    rw [e]
    have : 0 ≤ (1 - θ) * (ρ * κ * (hole_rot o u ⬝ᵥ hole_rot o u)) :=
      mul_nonneg (by linarith) (by positivity)
    have : 0 < θ * A := mul_pos hθ0 hA
    linarith
  have hu'0 : u' ≠ 0 := by intro h; rw [h, dotProduct_zero] at hrot_u'; exact lt_irrefl _ hrot_u'
  refine ⟨i', u', hu'0, hzi', ⟨T', hT', hT'i'⟩, ?_, hright', hleft'⟩
  -- the side of `C i'` starts at `q'`
  intro t ht hmem
  obtain ⟨t', ht', ht'b, ht't⟩ := hole_exists_pos_of_eventually
    ((hole_eventually_add_smul_mem Metric.isOpen_ball (Metric.mem_ball_self hεs) (-u')).and
      (eventually_lt_nhds ht))
  have hmem' : q' - t' • u' ∈ S.C i' := by
    have := (S.convex_C i') hzi' hmem (by
      rw [sub_nonneg, div_le_one ht]; exact ht't.le : (0 : ℝ) ≤ 1 - t' / t)
      (div_nonneg ht'.le ht.le) (by ring)
    convert this using 1
    rw [smul_sub, smul_smul, div_mul_cancel₀ _ ht.ne']; module
  have hint' : q' - t' • u' ∈ interior (S.C i) := by
    refine hole_mem_interior_of_side hside ?_ ?_
    · rw [sub_eq_add_neg, ← smul_neg]; exact ht'b
    · rw [sub_sub_cancel_left, dotProduct_neg, dotProduct_smul, smul_eq_mul]
      have := mul_pos ht' hrot_u'; linarith
  have hii : i' = i := by
    by_contra h; exact S.notMem_interior h hmem' hint'
  subst hii
  have := hs.2.2.2.2.1 _ hT'i'
  rw [hq', show q + T • u + T' • u' - q = T • u + T' • u' by abel, dotProduct_add,
    dotProduct_smul, dotProduct_smul, hole_rot_dot_self, smul_zero, zero_add, smul_eq_mul] at this
  have := mul_pos hT' hrot_u'
  linarith

/-- **The end point of a dart determines its state.** At the end `q'` both cells have a side
point with outer normals `J u₁`, `J u₂`, and `U` lies on the left of both darts; so `u₁ = u₂`,
the cells coincide, and so do the first endpoints of the sides. -/
lemma end_inj {o : ℝ} (ho : o * o = 1) {i₁ i₂ : Fin n} {q₁ q₂ u₁ u₂ : Fin 2 → ℝ}
    (hs₁ : S.IsState o i₁ q₁ u₁) (hs₂ : S.IsState o i₂ q₂ u₂) (hn₁ : ‖u₁‖ = 1)
    (hn₂ : ‖u₂‖ = 1) {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (heq : q₁ + T₁ • u₁ = q₂ + T₂ • u₂)
    (htri₁ : ∃ ε > (0 : ℝ), hole_tri o q₁ (q₁ + T₁ • u₁) ε ⊆ S.U)
    (htri₂ : ∃ ε > (0 : ℝ), hole_tri o q₂ (q₂ + T₂ • u₂) ε ⊆ S.U)
    (hside₁ : ∃ ε > (0 : ℝ), ∀ x, dist x (q₁ + T₁ • u₁) < ε →
      (x ∈ S.C i₁ ↔ hole_rot o u₁ ⬝ᵥ (x - (q₁ + T₁ • u₁)) ≤ 0))
    (hside₂ : ∃ ε > (0 : ℝ), ∀ x, dist x (q₂ + T₂ • u₂) < ε →
      (x ∈ S.C i₂ ↔ hole_rot o u₂ ⬝ᵥ (x - (q₂ + T₂ • u₂)) ≤ 0)) :
    i₁ = i₂ ∧ q₁ = q₂ ∧ u₁ = u₂ := by
  set q' := q₁ + T₁ • u₁ with hq'
  rw [← heq] at hside₂
  obtain ⟨ε₁, hε₁, htri₁⟩ := htri₁
  obtain ⟨ε₂, hε₂, htri₂⟩ := htri₂
  obtain ⟨e₁, he₁, hside₁⟩ := hside₁
  obtain ⟨e₂, he₂, hside₂⟩ := hside₂
  have hu₁ := hs₁.1
  have hu₂ := hs₂.1
  -- points of `U` on the left of the darts near `q'`
  have hleft : ∀ {q u : Fin 2 → ℝ} {T ε : ℝ}, 0 < T → q' = q + T • u →
      hole_tri o q (q + T • u) ε ⊆ S.U → ∀ c : ℝ, 0 < c → c < ε → ∀ τ : ℝ, 0 < τ → τ ≤ T / 2 →
        q' + τ • (-u + c • hole_rot o u) ∈ S.U := by
    intro q u T ε hT he htri c hc hcε τ hτ hτT
    apply htri
    have e : q' + τ • (-u + c • hole_rot o u) = q + (T - τ) • u + (τ * c) • hole_rot o u := by
      rw [he]; module
    rw [e]
    have hε : 0 < ε := hc.trans hcε
    have h1 : τ * c < τ * ε := mul_lt_mul_of_pos_left hcε hτ
    have h2 : ε * τ ≤ ε * (T - τ) := mul_le_mul_of_nonneg_left (by linarith) hε.le
    refine hole_mem_tri hT (by positivity) (by linarith) ?_
    rw [show T - (T - τ) = τ by ring]; linarith
  -- eventually near `q'`
  have hnear : ∀ (d : Fin 2 → ℝ) (e : ℝ), 0 < e → (T : ℝ) → 0 < T →
      ∃ τ > (0 : ℝ), τ ≤ T / 2 ∧ dist (q' + τ • d) q' < e := by
    intro d e he T hT
    obtain ⟨τ, hτ, hτb, hτT⟩ := hole_exists_pos_of_eventually
      ((hole_eventually_add_smul_mem Metric.isOpen_ball (Metric.mem_ball_self he) d).and
        (eventually_le_nhds (by positivity : (0 : ℝ) < T / 2)))
    exact ⟨τ, hτ, hτT, hτb⟩
  have hT₂' : q' = q₂ + T₂ • u₂ := heq
  -- step 1: `⟨J u₂, u₁⟩ ≤ 0` and `⟨J u₁, u₂⟩ ≤ 0`
  have hstep : ∀ {ia ib : Fin n} {qa ua ub : Fin 2 → ℝ} {Ta εa eb : ℝ}, 0 < Ta →
      q' = qa + Ta • ua → hole_tri o qa (qa + Ta • ua) εa ⊆ S.U → 0 < εa → 0 < eb →
      (∀ x, dist x q' < eb → (x ∈ S.C ib ↔ hole_rot o ub ⬝ᵥ (x - q') ≤ 0)) →
      hole_rot o ub ⬝ᵥ ua ≤ 0 := by
    intro ia ib qa ua ub Ta εa eb hTa hea htria hεa heb hsideb
    by_contra hpos
    push Not at hpos
    set Aa := hole_rot o ub ⬝ᵥ ua
    set Ba := |hole_rot o ub ⬝ᵥ hole_rot o ua|
    set c := min (εa / 2) (Aa / (2 * (Ba + 1)))
    have hc : 0 < c := lt_min (by positivity) (by positivity)
    have hcε : c < εa := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hcB : c * Ba ≤ Aa / 2 := by
      have h := min_le_right (εa / 2) (Aa / (2 * (Ba + 1)))
      calc c * Ba ≤ Aa / (2 * (Ba + 1)) * Ba := mul_le_mul_of_nonneg_right h (abs_nonneg _)
        _ ≤ Aa / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have := abs_nonneg (hole_rot o ub ⬝ᵥ hole_rot o ua); nlinarith
    obtain ⟨τ, hτ, hτT, hτd⟩ := hnear (-ua + c • hole_rot o ua) eb heb Ta hTa
    have hU := hleft hTa hea htria c hc hcε τ hτ hτT
    have hC : q' + τ • (-ua + c • hole_rot o ua) ∈ S.C ib := by
      have e : hole_rot o ub ⬝ᵥ (q' + τ • (-ua + c • hole_rot o ua) - q') =
          τ * (-Aa + c * (hole_rot o ub ⬝ᵥ hole_rot o ua)) := by
        rw [add_sub_cancel_left, dotProduct_smul, dotProduct_add, dotProduct_neg,
          dotProduct_smul, smul_eq_mul, smul_eq_mul]
      rw [hsideb _ hτd, e]
      have : c * (hole_rot o ub ⬝ᵥ hole_rot o ua) ≤ c * Ba :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hc.le
      exact (mul_neg_of_pos_of_neg hτ (by linarith)).le
    exact S.notMem_C_of_mem_U hU ib hC
  have h12 := hstep (ia := i₁) hT₁ hq' htri₁ hε₁ he₂ hside₂
  have h21 := hstep (ia := i₂) (ib := i₁) hT₂ hT₂' htri₂ hε₂ he₁ hside₁
  have hz : hole_rot o u₂ ⬝ᵥ u₁ = 0 := by
    rw [hole_rot_dot_comm, dotProduct_comm] at h21
    linarith
  have hpar := hole_eq_smul_of_rot_dot ho hu₂ hz
  set c' := u₁ ⬝ᵥ u₂ / (u₂ ⬝ᵥ u₂) with hc'
  -- step 2: `c' > 0`
  have hc'pos : 0 < c' := by
    by_contra hneg
    push Not at hneg
    have hc'0 : c' ≠ 0 := by
      intro h; rw [h, zero_smul] at hpar; exact hu₁ hpar
    have hc'n : c' < 0 := lt_of_le_of_ne hneg hc'0
    obtain ⟨τ, hτ, hτT, hτd⟩ := hnear (-u₁ + (ε₁ / 2) • hole_rot o u₁) e₂ he₂ T₁ hT₁
    have hU := hleft hT₁ hq' htri₁ (ε₁ / 2) (by positivity) (by linarith) τ hτ hτT
    have hC : q' + τ • (-u₁ + (ε₁ / 2) • hole_rot o u₁) ∈ S.C i₂ := by
      have hrr := hole_rot_dot_rot_self_pos ho hu₂
      have e : hole_rot o u₂ ⬝ᵥ (q' + τ • (-u₁ + (ε₁ / 2) • hole_rot o u₁) - q') =
          τ * ((ε₁ / 2) * (c' * (hole_rot o u₂ ⬝ᵥ hole_rot o u₂))) := by
        rw [add_sub_cancel_left, dotProduct_smul, dotProduct_add, dotProduct_neg,
          dotProduct_smul, hz]
        conv_lhs => rw [hpar]
        rw [hole_rot_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
        ring
      rw [hside₂ _ hτd, e]
      have : c' * (hole_rot o u₂ ⬝ᵥ hole_rot o u₂) < 0 := mul_neg_of_neg_of_pos hc'n hrr
      have : (ε₁ / 2) * (c' * (hole_rot o u₂ ⬝ᵥ hole_rot o u₂)) < 0 :=
        mul_neg_of_pos_of_neg (by positivity) this
      exact (mul_neg_of_pos_of_neg hτ this).le
    exact S.notMem_C_of_mem_U hU i₂ hC
  have hu : u₁ = u₂ := by
    have hn : ‖u₁‖ = c' * ‖u₂‖ := by
      rw [hpar, norm_smul, Real.norm_eq_abs, abs_of_pos hc'pos]
    rw [hn₁, hn₂, mul_one] at hn
    rw [hpar, ← hn, one_smul]
  subst hu
  -- step 3: the cells coincide
  have hi : i₁ = i₂ := by
    by_contra hne
    have hrr := hole_rot_dot_rot_self_pos ho hu₁
    obtain ⟨σ, hσ, hσd⟩ := hole_exists_pos_of_eventually
      (hole_eventually_add_smul_mem Metric.isOpen_ball (Metric.mem_ball_self (lt_min he₁ he₂))
        (-hole_rot o u₁))
    have hd1 : dist (q' + σ • -hole_rot o u₁) q' < e₁ :=
      lt_of_lt_of_le hσd (min_le_left _ _)
    have hd2 : dist (q' + σ • -hole_rot o u₁) q' < e₂ :=
      lt_of_lt_of_le hσd (min_le_right _ _)
    have hneg : hole_rot o u₁ ⬝ᵥ (q' + σ • -hole_rot o u₁ - q') < 0 := by
      rw [add_sub_cancel_left, dotProduct_smul, dotProduct_neg, smul_eq_mul]
      nlinarith
    have hm1 : q' + σ • -hole_rot o u₁ ∈ S.C i₁ := (hside₁ _ hd1).2 hneg.le
    have hm2 := hole_mem_interior_of_side hside₂ hd2 hneg
    exact S.notMem_interior hne hm1 hm2
  subst hi
  exact ⟨rfl, hs₁.unique ho hs₂, rfl⟩

/-- The direction of a state is the unit direction of one of the sides of its cell. -/
lemma IsState.dir {o : ℝ} (ho : o * o = 1) {i : Fin n} {q u : Fin 2 → ℝ}
    (hs : S.IsState o i q u) (hn : ‖u‖ = 1) :
    ∃ l : Fin (S.k i), u = ‖hole_rot o (S.a i l)‖⁻¹ • -hole_rot o (S.a i l) := by
  obtain ⟨-, -, -, -, l, ⟨μ, hμ, hμl⟩, -, -⟩ := hs.face ho
  refine ⟨l, ?_⟩
  have e : -hole_rot o (S.a i l) = μ • u := by
    rw [hμl, hole_rot_smul, hole_rot_rot ho, smul_neg, neg_neg]
  have hnorm : ‖hole_rot o (S.a i l)‖ = μ := by
    rw [← norm_neg, e, norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos hμ]
  rw [e, hnorm, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]

variable (S) in
/-- The states of orientation `o` with unit direction. -/
def states (o : ℝ) : Set (Fin n × (Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
  {s | S.IsState o s.1 s.2.1 s.2.2 ∧ ‖s.2.2‖ = 1}

variable (S) in
/-- There are finitely many states: the direction of a state is the direction of a side of its
cell, and the cell and the direction determine the first endpoint. -/
lemma states_finite {o : ℝ} (ho : o * o = 1) : (S.states o).Finite := by
  have hsub : S.states o ⊆ ⋃ i : Fin n, ⋃ l : Fin (S.k i), {s | s ∈ S.states o ∧ s.1 = i ∧
      s.2.2 = ‖hole_rot o (S.a i l)‖⁻¹ • -hole_rot o (S.a i l)} := by
    intro s hs
    obtain ⟨l, hl⟩ := hs.1.dir ho hs.2
    exact mem_iUnion₂.2 ⟨s.1, l, hs, rfl, hl⟩
  refine Set.Finite.subset (Set.finite_iUnion fun i ↦ Set.finite_iUnion fun l ↦
    Set.Subsingleton.finite ?_) hsub
  intro s₁ hs₁ s₂ hs₂
  obtain ⟨h₁, hi₁, hu₁⟩ := hs₁
  obtain ⟨h₂, hi₂, hu₂⟩ := hs₂
  have hi : s₁.1 = s₂.1 := hi₁.trans hi₂.symm
  have hu : s₁.2.2 = s₂.2.2 := hu₁.trans hu₂.symm
  have h₂' := h₂.1
  rw [← hi, ← hu] at h₂'
  have hq : s₁.2.1 = s₂.2.1 := h₁.1.unique ho h₂'
  exact Prod.ext hi (Prod.ext hq hu)

variable (S) in
/-- **Every first endpoint of a state is a side point of some cell.** The map
`state ↦ end of its dart` is injective (`end_inj`), its values are side points (`dart`) and base
points of states (`IsState.next`); conclude by counting (`hole_count`). -/
theorem star {o : ℝ} (ho : o * o = 1) {i : Fin n} {q u : Fin 2 → ℝ} (hs : S.IsState o i q u) :
    ∃ k, IsSidePoint (S.C k) q := by
  classical
  have hd : ∀ s ∈ S.states o, ∃ T > (0 : ℝ),
      (∃ ε > (0 : ℝ), hole_tri o s.2.1 (s.2.1 + T • s.2.2) ε ⊆ S.U) ∧
      (∃ j, j ≠ s.1 ∧ s.2.1 + T • s.2.2 ∈ S.C j) ∧
      (∃ ε > (0 : ℝ), ∀ x, dist x (s.2.1 + T • s.2.2) < ε →
        (x ∈ S.C s.1 ↔ hole_rot o s.2.2 ⬝ᵥ (x - (s.2.1 + T • s.2.2)) ≤ 0)) :=
    fun s hs ↦ hs.1.dart ho
  choose! T hT htri hj hside using hd
  have hnorm : ∀ {v : Fin 2 → ℝ}, v ≠ 0 → ‖‖v‖⁻¹ • v‖ = 1 := fun hv ↦ by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  have key := hole_count (S.states_finite ho) (fun s ↦ s.2.1) (fun s ↦ s.2.1 + T s • s.2.2)
    (fun p ↦ ∃ k, IsSidePoint (S.C k) p) ?_ ?_ ?_
  · exact key (i, q, ‖u‖⁻¹ • u)
      ⟨hs.smul (inv_pos.2 (norm_pos_iff.2 hs.1)), hnorm hs.1⟩
  · rintro ⟨i₁, q₁, u₁⟩ h₁ ⟨i₂, q₂, u₂⟩ h₂ heq
    obtain ⟨hi, hq, hu⟩ := S.end_inj ho h₁.1 h₂.1 h₁.2 h₂.2 (hT _ h₁) (hT _ h₂) heq (htri _ h₁)
      (htri _ h₂) (hside _ h₁) (hside _ h₂)
    subst hi hq hu; rfl
  · intro s hs
    obtain ⟨ε, hε, h⟩ := hside s hs
    exact ⟨s.1, hole_rot o s.2.2, hole_rot_ne_zero ho hs.1.1, ε, hε, h⟩
  · intro s hs
    obtain ⟨i', u', hst⟩ := hs.1.next ho (hT s hs) (htri s hs) (hj s hs) (hside s hs)
    exact ⟨(i', s.2.1 + T s • s.2.2, ‖u'‖⁻¹ • u'),
      ⟨hst.smul (inv_pos.2 (norm_pos_iff.2 hst.1)), hnorm hst.1⟩, rfl⟩

/-! ### Points of the hole in a cell are side points -/

variable (S) in
/-- From a point of `H \ U` some segment enters `U`. -/
lemma exists_dir {z : Fin 2 → ℝ} (hz : z ∈ S.H) (hzU : z ∉ S.U) :
    ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → z + t • w ∈ S.U := by
  obtain ⟨r, hr, hcon⟩ := S.conic z
  obtain ⟨x, hxU, hxz⟩ := Metric.mem_closure_iff.1 hz r hr
  have hxb : x ∈ Metric.ball z r := by rw [Metric.mem_ball, dist_comm]; exact hxz
  refine ⟨x - z, sub_ne_zero.2 fun h ↦ hzU (h ▸ hxU), ?_⟩
  have hzQ : z ∈ S.Q := S.H_subset_Q hz
  set Seg := (fun t : ℝ ↦ z + t • (x - z)) '' Ioc 0 1 with hSeg
  have hSegF : Seg ⊆ S.F := by
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have := S.convex_Q hzQ (S.U_subset_Q hxU) (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le
        (by ring)
      convert this using 1; module
    · rw [mem_iUnion]; rintro ⟨k, hk⟩
      exact S.notMem_C_of_mem_U hxU k ((hcon k x hxb t ht0 ht1).2 hk)
  have hpc : IsPreconnected Seg := isPreconnected_Ioc.image _
    (by fun_prop : Continuous fun t : ℝ ↦ z + t • (x - z)).continuousOn
  have hSegU := S.subset_U hpc hSegF ⟨1, ⟨one_pos, le_rfl⟩, by simp⟩ hxU
  exact fun t ht ht1 ↦ hSegU ⟨t, ⟨ht, ht1⟩, rfl⟩

variable (S) in
/-- At a point of `H` in a cell which is a side point of no cell, the sweep gives a state. -/
lemma exists_state {z : Fin 2 → ℝ} (hz : z ∈ S.H) {j : Fin n} (hzj : z ∈ S.C j)
    (hns : ∀ k, ¬ IsSidePoint (S.C k) z) :
    ∃ o : ℝ, o * o = 1 ∧ ∃ i u, S.IsState o i z u := by
  have hzU : z ∉ S.U := fun h ↦ S.notMem_C_of_mem_U h j hzj
  obtain ⟨w₀, hw₀, h₀⟩ := S.exists_dir hz hzU
  have ho1 : (1 : ℝ) * 1 = 1 := by norm_num
  -- a direction into the interior of `C j`, not parallel to `w₀`
  obtain ⟨p, hp, hpar⟩ : ∃ p ∈ interior (S.C j), hole_rot 1 (p - z) ⬝ᵥ w₀ ≠ 0 := by
    obtain ⟨p₀, hp₀⟩ := S.hint j
    by_cases h0 : hole_rot 1 (p₀ - z) ⬝ᵥ w₀ = 0
    · obtain ⟨δ, hδ, hδp⟩ := hole_exists_pos_of_eventually
        (hole_eventually_add_smul_mem isOpen_interior hp₀ (hole_rot 1 w₀))
      refine ⟨_, hδp, ?_⟩
      rw [show p₀ + δ • hole_rot 1 w₀ - z = (p₀ - z) + δ • hole_rot 1 w₀ by abel, hole_rot_add,
        add_dotProduct, h0, hole_rot_smul, hole_rot_rot ho1, smul_dotProduct, neg_dotProduct,
        smul_eq_mul, zero_add]
      have := hole_dot_self_pos hw₀
      have : 0 < δ * (w₀ ⬝ᵥ w₀) := mul_pos hδ this
      linarith
    · exact ⟨p₀, hp₀, h0⟩
  set w₁ := p - z with hw₁
  have h₁ : ∀ t : ℝ, 0 < t → t ≤ 1 → z + t • w₁ ∈ S.C j := fun t ht ht1 ↦ by
    have := (S.convex_C j) hzj (interior_subset hp) (by linarith : (0 : ℝ) ≤ 1 - t) ht.le
      (by ring)
    convert this using 1; rw [hw₁]; module
  -- the orientation
  obtain ⟨o, ho, hw⟩ : ∃ o : ℝ, o * o = 1 ∧ 0 < hole_rot o w₁ ⬝ᵥ w₀ := by
    rcases hpar.lt_or_gt with hneg | hpos
    · refine ⟨-1, by norm_num, ?_⟩
      rw [hole_rot_neg_o, neg_dotProduct]; linarith
    · exact ⟨1, ho1, hpos⟩
  obtain ⟨i, θ, hθ0, hθ1, hzi, hS1, hright, hleft⟩ := S.sweep ho h₀ h₁ hw
  set u := (1 - θ) • w₀ + θ • w₁ with hu
  have hrw : 0 < hole_rot o u ⬝ᵥ w₀ := by
    have : hole_rot o u ⬝ᵥ w₀ = θ * (hole_rot o w₁ ⬝ᵥ w₀) := by
      simp only [hu, hole_rot_add, hole_rot_smul, add_dotProduct, smul_dotProduct,
        hole_rot_dot_self, smul_eq_mul, mul_zero, zero_add]
    rw [this]; positivity
  have hu0 : u ≠ 0 := by intro h; rw [h] at hrw; simp [hole_rot] at hrw
  refine ⟨o, ho, i, u, hu0, hzi, hS1, ?_, hright, hleft⟩
  intro t ht hmem
  -- otherwise `z` is a side point of `C i`
  obtain ⟨T, hT, hTi⟩ := hS1
  apply hns i
  have hCi := S.hac i
  have hne : z - t • u ≠ z + T • u := by
    intro h
    have : (t + T) • u = 0 := by
      rw [show (t + T) • u = (z + T • u) - (z - t • u) by module, h, sub_self]
    rcases smul_eq_zero.1 this with h' | h'
    · linarith
    · exact hu0 h'
  obtain ⟨-, -, ε, hε, hside⟩ := hole_relint (S.a i) (S.c i) (hCi ▸ S.hint i)
    (hole_rot_ne_zero ho hu0) (p := z - t • u) (p' := z + T • u)
    (fun x hx ↦ by
      rw [show x - (z - t • u) = (x - z) + t • u by abel, dotProduct_add, dotProduct_smul,
        hole_rot_dot_self, smul_zero, add_zero]
      exact hright x (hCi ▸ hx))
    (hCi ▸ hmem) (hCi ▸ hTi) hne
    (by rw [show z + T • u - (z - t • u) = (T + t) • u by module, dotProduct_smul,
      hole_rot_dot_self, smul_zero])
    (θ := t / (t + T)) (by positivity) (by rw [div_lt_one (by positivity)]; linarith)
  have hm : z - t • u + (t / (t + T)) • (z + T • u - (z - t • u)) = z := by
    rw [show z + T • u - (z - t • u) = (t + T) • u by module, smul_smul,
      div_mul_cancel₀ _ (by positivity : t + T ≠ 0)]
    abel
  rw [hm] at hside
  exact ⟨hole_rot o u, hole_rot_ne_zero ho hu0, ε, hε, fun x hx ↦ by rw [hCi]; exact hside x hx⟩

variable (S) in
/-- **Every point of the hole lying in a cell is a side point of some cell.** -/
theorem sidePoint_of_mem {z : Fin 2 → ℝ} (hz : z ∈ S.H) {j : Fin n} (hzj : z ∈ S.C j) :
    ∃ k, IsSidePoint (S.C k) z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨o, ho, i, u, hs⟩ := S.exists_state hz hzj hcon
  obtain ⟨k, hk⟩ := S.star ho hs
  exact hcon k hk

/-! ### The hole lies in the interior of `Q` -/

variable (S) in
/-- A point of `H` on the frontier of `Q` is not a side point of a cell (the cell would fill `Q`
near it). -/
lemma not_sidePoint_of_frontier {z : Fin 2 → ℝ} (hz : z ∈ S.H) (hzQ : z ∈ frontier S.Q)
    (k : Fin n) : ¬ IsSidePoint (S.C k) z := by
  rintro ⟨w, hw, ε, hε, hside⟩
  obtain ⟨l, hl0, hl⟩ := mem_iUnion₂.1 (pin_frontier_halfPlanesInter_subset S.b S.d hzQ)
  have hQsupp : ∀ x ∈ S.Q, S.b l ⬝ᵥ (x - z) ≤ 0 := fun x hx ↦ by
    rw [dotProduct_sub]; simp only [mem_ofPred_eq] at hl; rw [hl]; linarith [hx l]
  have hhalf : ∀ v : Fin 2 → ℝ, w ⬝ᵥ v ≤ 0 → S.b l ⬝ᵥ v ≤ 0 := by
    intro v hv
    obtain ⟨δ, hδ, hδb⟩ := hole_exists_pos_of_eventually
      (hole_eventually_add_smul_mem Metric.isOpen_ball (Metric.mem_ball_self hε) v)
    have hmem : z + δ • v ∈ S.C k := by
      refine (hside _ hδb).2 ?_
      rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos hδ.le hv
    have := hQsupp _ (S.C_subset_Q k hmem)
    rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul] at this
    exact nonpos_of_mul_nonpos_right this hδ
  have ho1 : (1 : ℝ) * 1 = 1 := by norm_num
  have h1 := hhalf (hole_rot 1 w) (by rw [hole_dot_rot_self])
  have h2 := hhalf (-hole_rot 1 w) (by rw [dotProduct_neg, hole_dot_rot_self, neg_zero])
  rw [dotProduct_neg] at h2
  have hz0 : hole_rot 1 w ⬝ᵥ S.b l = 0 := by rw [dotProduct_comm]; linarith
  have hpar := hole_eq_smul_of_rot_dot ho1 hw hz0
  set μ := S.b l ⬝ᵥ w / (w ⬝ᵥ w)
  have h3 := hhalf (-w) (by rw [dotProduct_neg]; have := hole_dot_self_pos hw; linarith)
  have hμ : 0 < μ := by
    rw [hpar, dotProduct_neg, smul_dotProduct, smul_eq_mul] at h3
    have := hole_dot_self_pos hw
    have hμ0 : 0 ≤ μ := by nlinarith
    refine lt_of_le_of_ne hμ0 fun h ↦ hl0 ?_
    rw [hpar, ← h, zero_smul]
  -- `Q` coincides with `C k` near `z`, so `U` misses a neighbourhood of `z`
  obtain ⟨x, hxU, hxz⟩ := Metric.mem_closure_iff.1 hz ε hε
  have hxQ := S.U_subset_Q hxU
  have hxC : x ∈ S.C k := by
    refine (hside x (by rw [dist_comm]; exact hxz)).2 ?_
    have := hQsupp x hxQ
    rw [hpar, smul_dotProduct, smul_eq_mul] at this
    exact nonpos_of_mul_nonpos_right this hμ
  exact S.notMem_C_of_mem_U hxU k hxC

/-- The lexicographically largest point of a nonempty compact set. -/
lemma hole_exists_lexMax {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ z ∈ K, ∀ y ∈ K, y 0 < z 0 ∨ (y 0 = z 0 ∧ y 1 ≤ z 1) := by
  obtain ⟨z₁, hz₁, hmax₁⟩ := hK.exists_isMaxOn hne (continuous_apply 0).continuousOn
  set K₁ := K ∩ {y | y 0 = z₁ 0}
  have hK₁ : IsCompact K₁ := hK.inter_right (isClosed_eq (continuous_apply 0) continuous_const)
  obtain ⟨z, ⟨hzK, hz0⟩, hmax⟩ := hK₁.exists_isMaxOn ⟨z₁, hz₁, rfl⟩
    (continuous_apply 1).continuousOn
  refine ⟨z, hzK, fun y hy ↦ ?_⟩
  have h0 : y 0 ≤ z 0 := by
    have := hmax₁ hy; simp only [mem_ofPred_eq] at this hz0; rw [hz0]; exact this
  rcases h0.lt_or_eq with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, hmax ⟨hy, ?_⟩⟩
    simp only [mem_ofPred_eq] at hz0 ⊢; rw [h, hz0]

variable (S) in
/-- **The hole lies in the interior of `Q`.** No cell meets `H ∩ ∂Q` (its points are not side
points), so `H` contains `Q` near each of its points on `∂Q`; as `∂Q` is connected, `∂Q ⊆ H`.
Then the lexicographically largest point of the cells lies in `interior Q`, and the ray from it
in the direction `e₀` runs through `U` to `∂Q`, so it is a point of `H` in a cell which is not a
side point, contradicting `sidePoint_of_mem`. -/
theorem H_subset_interior (hn : Nonempty (Fin n)) : S.H ⊆ interior S.Q := by
  -- no cell meets `H ∩ ∂Q`
  have hA : ∀ z ∈ S.H, z ∈ frontier S.Q → ∀ k, z ∉ S.C k := by
    intro z hz hzf k hzk
    obtain ⟨k', hk'⟩ := S.sidePoint_of_mem hz hzk
    exact S.not_sidePoint_of_frontier hz hzf k' hk'
  -- `U` contains `Q` near the points of `H ∩ ∂Q`
  have hB : ∀ z ∈ S.H, z ∈ frontier S.Q → ∃ r > (0 : ℝ), S.Q ∩ Metric.ball z r ⊆ S.U := by
    intro z hz hzf
    have hz' : z ∉ ⋃ k, S.C k := by
      rw [mem_iUnion]; rintro ⟨k, hk⟩; exact hA z hz hzf k hk
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 S.isClosed_iUnion_C.isOpen_compl z hz'
    refine ⟨r, hr, ?_⟩
    have hF : S.Q ∩ Metric.ball z r ⊆ S.F := fun x hx ↦ ⟨hx.1, hball hx.2⟩
    obtain ⟨x, hxU, hxz⟩ := Metric.mem_closure_iff.1 hz r hr
    exact S.subset_U (S.convex_Q.inter (convex_ball z r)).isPreconnected hF
      ⟨S.U_subset_Q hxU, by rw [Metric.mem_ball, dist_comm]; exact hxz⟩ hxU
  obtain ⟨i₀⟩ := hn
  obtain ⟨o, ho⟩ : (interior S.Q).Nonempty :=
    (S.hint i₀).mono (interior_mono (S.C_subset_Q i₀))
  intro z hz
  by_contra hzi
  have hzf : z ∈ frontier S.Q := ⟨subset_closure (S.H_subset_Q hz), hzi⟩
  -- `∂Q ⊆ H`
  have hfrH : frontier S.Q ⊆ S.H := by
    choose! r hr hrU using hB
    have hconn := hole_isPreconnected_frontier S.convex_Q S.hQ ho
    by_contra hcon
    obtain ⟨y, hyf, hyH⟩ := not_subset.1 hcon
    obtain ⟨w, hwf, hwu, hwv⟩ := hconn (⋃ y ∈ S.H ∩ frontier S.Q, Metric.ball y (r y)) S.Hᶜ
      (isOpen_biUnion fun _ _ ↦ Metric.isOpen_ball) isClosed_closure.isOpen_compl
      (fun x hx ↦ by
        by_cases hxH : x ∈ S.H
        · exact Or.inl (mem_iUnion₂.2 ⟨x, ⟨hxH, hx⟩, Metric.mem_ball_self (hr x hxH hx)⟩)
        · exact Or.inr hxH)
      ⟨z, hzf, mem_iUnion₂.2 ⟨z, ⟨hz, hzf⟩, Metric.mem_ball_self (hr z hz hzf)⟩⟩
      ⟨y, hyf, hyH⟩
    obtain ⟨y', ⟨hy'H, hy'f⟩, hwb⟩ := mem_iUnion₂.1 hwu
    have hwQ : w ∈ S.Q := S.isClosed_Q.frontier_subset hwf
    exact hwv (subset_closure (hrU y' hy'H hy'f ⟨hwQ, hwb⟩))
  -- the lexicographically largest point of the cells
  have hKc : IsCompact (⋃ k, S.C k) :=
    isCompact_iUnion fun k ↦ Metric.isCompact_of_isClosed_isBounded (S.isClosed_C k) (S.hbdd k)
  obtain ⟨zs, hzsK, hlex⟩ := hole_exists_lexMax hKc
    (let ⟨p, hp⟩ := S.hint i₀; ⟨p, mem_iUnion.2 ⟨i₀, interior_subset hp⟩⟩)
  obtain ⟨k₀, hk₀⟩ := mem_iUnion.1 hzsK
  have hzsQ : zs ∈ S.Q := S.C_subset_Q k₀ hk₀
  have hzsi : zs ∈ interior S.Q := by
    by_contra h
    exact hA zs (hfrH ⟨subset_closure hzsQ, h⟩) ⟨subset_closure hzsQ, h⟩ k₀ hk₀
  -- the ray in the direction `e₀`
  set e₀ : Fin 2 → ℝ := ![1, 0] with he₀
  set A := {t : ℝ | 0 ≤ t ∧ zs + t • e₀ ∈ S.Q}
  have hAbdd : BddAbove A := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 S.hQ
    refine ⟨R + ‖zs‖, fun t ht ↦ ?_⟩
    have h1 := hR _ ht.2
    have h2 : ‖t • e₀‖ ≤ ‖zs + t • e₀‖ + ‖zs‖ := by
      calc ‖t • e₀‖ = ‖(zs + t • e₀) - zs‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖zs + t • e₀‖ + ‖zs‖ := norm_sub_le _ _
    have he : 1 ≤ ‖e₀‖ := by
      have := norm_le_pi_norm e₀ 0; simpa [he₀] using this
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at h2
    have := mul_le_mul_of_nonneg_left he ht.1
    linarith
  have hAc : IsClosed A := isClosed_Ici.inter (S.isClosed_Q.preimage (by fun_prop))
  have h0A : (0 : ℝ) ∈ A := ⟨le_rfl, by simpa using hzsQ⟩
  set T := sSup A
  have hTA : T ∈ A := hAc.csSup_mem ⟨0, h0A⟩ hAbdd
  obtain ⟨δ, hδ, hδQ⟩ := hole_exists_pos_of_eventually
    (hole_eventually_add_smul_mem isOpen_interior hzsi e₀)
  have hT0 : 0 < T := hδ.trans_le (le_csSup hAbdd ⟨hδ.le, interior_subset hδQ⟩)
  set w' := zs + T • e₀ with hw'
  have hw'f : w' ∈ frontier S.Q := by
    refine ⟨subset_closure hTA.2, fun hint ↦ ?_⟩
    obtain ⟨δ', hδ', hδ'Q⟩ := hole_exists_pos_of_eventually
      (hole_eventually_add_smul_mem isOpen_interior hint e₀)
    have : T + δ' ∈ A := ⟨by linarith, by
      rw [add_smul, ← add_assoc]; exact interior_subset hδ'Q⟩
    linarith [le_csSup hAbdd this]
  have hw'H := hfrH hw'f
  obtain ⟨r, hr, hrU⟩ := hB w' hw'H hw'f
  have hw'U : w' ∈ S.U := hrU ⟨hTA.2, Metric.mem_ball_self hr⟩
  -- the open segment from `zs` to `w'` lies in `U`
  have hseg0 : ∀ t : ℝ, 0 < t → t ≤ T → (zs + t • e₀) 0 = zs 0 + t := by
    intro t _ _; simp [he₀]
  set Seg := (fun t : ℝ ↦ zs + t • e₀) '' Ioc 0 T
  have hSegF : Seg ⊆ S.F := by
    rintro _ ⟨t, ⟨ht0, htT⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have := S.convex_Q hzsQ hTA.2 (by
        rw [sub_nonneg, div_le_one hT0]; exact htT : (0 : ℝ) ≤ 1 - t / T)
        (div_nonneg ht0.le hT0.le) (by ring)
      convert this using 1
      rw [smul_add, smul_smul, div_mul_cancel₀ _ hT0.ne']; module
    · rw [mem_iUnion]
      rintro ⟨k, hk⟩
      have e : (zs + t • e₀) 0 = zs 0 + t := hseg0 t ht0 htT
      rcases hlex _ (mem_iUnion.2 ⟨k, hk⟩) with h | ⟨h, -⟩
      · change (zs + t • e₀) 0 < zs 0 at h; linarith
      · change (zs + t • e₀) 0 = zs 0 at h; linarith
  have hSegU : Seg ⊆ S.U := S.subset_U (isPreconnected_Ioc.image _
    (by fun_prop : Continuous fun t : ℝ ↦ zs + t • e₀).continuousOn) hSegF
    ⟨T, ⟨hT0, le_rfl⟩, rfl⟩ hw'U
  have hzsH : zs ∈ S.H := hole_mem_of_forall_pos isClosed_closure hT0
    fun t ht htT ↦ subset_closure (hSegU ⟨t, ⟨ht, htT⟩, rfl⟩)
  -- `zs` would be a side point of a cell
  obtain ⟨k, w, hw, ε, hε, hside⟩ := S.sidePoint_of_mem hzsH hk₀
  -- a lexicographically positive direction into `C k`
  obtain ⟨v, hv, hvpos⟩ : ∃ v : Fin 2 → ℝ, w ⬝ᵥ v ≤ 0 ∧ (0 < v 0 ∨ (v 0 = 0 ∧ 0 < v 1)) := by
    by_cases hw0 : w 0 ≤ 0
    · refine ⟨e₀, ?_, Or.inl ?_⟩
      · rw [hole_dot2]; change w 0 * 1 + w 1 * 0 ≤ 0; linarith
      · change (0 : ℝ) < 1; exact one_pos
    push Not at hw0
    by_cases hw1 : 0 < w 1
    · refine ⟨![w 1, -w 0], ?_, Or.inl hw1⟩
      rw [hole_dot2]; change w 0 * w 1 + w 1 * -w 0 ≤ 0; linarith
    · push Not at hw1
      refine ⟨![-w 1, w 0], ?_, ?_⟩
      · rw [hole_dot2]; change w 0 * -w 1 + w 1 * w 0 ≤ 0; linarith
      · rcases hw1.lt_or_eq with hw1' | hw1'
        · left; change 0 < -w 1; linarith
        · right; change -w 1 = 0 ∧ 0 < w 0; exact ⟨by rw [hw1', neg_zero], hw0⟩
  obtain ⟨η, hη, hηb⟩ := hole_exists_pos_of_eventually
    (hole_eventually_add_smul_mem Metric.isOpen_ball (Metric.mem_ball_self hε) v)
  have hmem : zs + η • v ∈ S.C k := by
    refine (hside _ hηb).2 ?_
    rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hη.le hv
  rcases hlex _ (mem_iUnion.2 ⟨k, hmem⟩) with h | ⟨h, h'⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    rcases hvpos with hv0 | ⟨hv0, hv1⟩
    · nlinarith
    · rw [hv0, mul_zero, add_zero] at h; exact lt_irrefl _ h
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h h'
    rcases hvpos with hv0 | ⟨hv0, hv1⟩
    · nlinarith
    · nlinarith

/-! ### The hole is convex -/

variable (S) in
lemma isOpen_U (hHQ : S.H ⊆ interior S.Q) : IsOpen S.U := by
  rw [Metric.isOpen_iff]
  intro x hx
  have hx' : x ∈ interior S.Q ∩ (⋃ k, S.C k)ᶜ :=
    ⟨hHQ (subset_closure hx), fun h ↦ (S.U_subset_F hx).2 h⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1
    (isOpen_interior.inter S.isClosed_iUnion_C.isOpen_compl) x hx'
  exact ⟨r, hr, S.subset_U (convex_ball x r).isPreconnected
    (fun y hy ↦ ⟨interior_subset (hball hy).1, (hball hy).2⟩) (Metric.mem_ball_self hr) hx⟩

variable (S) in
/-- Every point of `H \ U` is a side point of some cell. -/
lemma sidePoint_of_mem_H (hHQ : S.H ⊆ interior S.Q) {z : Fin 2 → ℝ} (hz : z ∈ S.H)
    (hzU : z ∉ S.U) : ∃ k, IsSidePoint (S.C k) z := by
  by_cases hzC : z ∈ ⋃ k, S.C k
  · obtain ⟨j, hj⟩ := mem_iUnion.1 hzC
    exact S.sidePoint_of_mem hz hj
  · exfalso
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1
      (isOpen_interior.inter S.isClosed_iUnion_C.isOpen_compl) z ⟨hHQ hz, hzC⟩
    obtain ⟨x, hxU, hxz⟩ := Metric.mem_closure_iff.1 hz r hr
    have := S.subset_U (convex_ball z r).isPreconnected
      (fun y hy ↦ ⟨interior_subset (hball hy).1, (hball hy).2⟩)
      (by rw [Metric.mem_ball, dist_comm]; exact hxz) hxU
    exact hzU (this (Metric.mem_ball_self hr))

variable (S) in
/-- **`U` is convex.** For `x ∈ U`, the set of `y ∈ U` with `[x, y] ⊆ U` is open, and closed in
`U`: if `[x, y] ⊆ H` left `U`, it would leave it at a side point `z` of a cell `C k`, coming from
the outside of `C k` (from `U`) and continuing into the interior of `C k`, which misses `H`. -/
theorem convex_U (hHQ : S.H ⊆ interior S.Q) : Convex ℝ S.U := by
  have hUo := S.isOpen_U hHQ
  intro x hx
  set A := {y | y ∈ S.U ∧ segment ℝ x y ⊆ S.U} with hA
  -- `A` is open
  have hAo : IsOpen A := by
    rw [Metric.isOpen_iff]
    rintro y ⟨hyU, hseg⟩
    obtain ⟨δ, hδ, hth⟩ := (hole_isCompact_segment x y).exists_thickening_subset_open hUo hseg
    refine ⟨δ, hδ, fun y' hy' ↦ ⟨hth ?_, ?_⟩⟩
    · exact Metric.mem_thickening_iff.2 ⟨y, right_mem_segment ℝ x y, hy'⟩
    · rw [segment_eq_image']
      rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
      apply hth
      refine Metric.mem_thickening_iff.2 ⟨x + t • (y - x), by
        rw [segment_eq_image']; exact ⟨t, ⟨ht0, ht1⟩, rfl⟩, ?_⟩
      rw [dist_eq_norm, show x + t • (y' - x) - (x + t • (y - x)) = t • (y' - y) by module,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, ← dist_eq_norm]
      calc t * dist y' y ≤ 1 * dist y' y := mul_le_mul_of_nonneg_right ht1 dist_nonneg
        _ < δ := by rw [one_mul]; exact hy'
  -- the closure of `A` within `U`
  have hcl : ∀ y ∈ S.U, y ∈ closure A → y ∈ A := by
    intro y hyU hycl
    refine ⟨hyU, ?_⟩
    -- `[x, y] ⊆ H`
    have hH : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ S.H := by
      have hcA : closure A ⊆ {y' | ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y' - x) ∈ S.H} := by
        refine closure_minimal (fun y' hy' t ht ↦ subset_closure (hy'.2 ?_)) ?_
        · rw [segment_eq_image']; exact ⟨t, ht, rfl⟩
        · simp only [Set.ofPred_forall]
          exact isClosed_iInter fun t ↦ isClosed_iInter fun _ ↦
            isClosed_closure.preimage (by fun_prop)
      exact hcA hycl
    by_contra hseg
    rw [segment_eq_image'] at hseg
    obtain ⟨_, ⟨t₁, ht₁, rfl⟩, ht₁U⟩ := not_subset.1 hseg
    set Z := {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ x + t • (y - x) ∉ S.U} with hZ
    have hZc : IsClosed Z := isClosed_Icc.inter (hUo.isClosed_compl.preimage (by fun_prop))
    have hZne : Z.Nonempty := ⟨t₁, ht₁, ht₁U⟩
    have hZbdd : BddBelow Z := ⟨0, fun t ht ↦ ht.1.1⟩
    set t₀ := sInf Z
    have ht₀Z : t₀ ∈ Z := hZc.csInf_mem hZne hZbdd
    have ht₀0 : 0 < t₀ := by
      refine lt_of_le_of_ne ht₀Z.1.1 fun h ↦ ht₀Z.2 ?_
      rw [← h, zero_smul, add_zero]; exact hx
    have ht₀1 : t₀ < 1 := by
      refine lt_of_le_of_ne ht₀Z.1.2 fun h ↦ ht₀Z.2 ?_
      rw [h, one_smul, add_sub_cancel]; exact hyU
    set z := x + t₀ • (y - x) with hzdef
    have hzH : z ∈ S.H := hH t₀ ht₀Z.1
    obtain ⟨k, w, hw, ε, hε, hside⟩ := S.sidePoint_of_mem_H hHQ hzH ht₀Z.2
    -- points of the segment near `z`
    obtain ⟨s, hs, ⟨hsb1, hsb2⟩, hs1, hs2⟩ := hole_exists_pos_of_eventually
      (((hole_eventually_add_smul_mem Metric.isOpen_ball (Metric.mem_ball_self hε) (y - x)).and
        (hole_eventually_add_smul_mem Metric.isOpen_ball (Metric.mem_ball_self hε) (-(y - x)))).and
        ((eventually_lt_nhds ht₀0).and (eventually_lt_nhds (sub_pos.2 ht₀1))))
    -- before `z`: in `U`, hence outside `C k`
    have hbefore : x + (t₀ - s) • (y - x) ∈ S.U := by
      by_contra h
      have := csInf_le hZbdd ⟨⟨by linarith, by linarith⟩, h⟩
      linarith
    have hb' : x + (t₀ - s) • (y - x) = z + s • -(y - x) := by rw [hzdef]; module
    have h1 : 0 < s * -(w ⬝ᵥ (y - x)) := by
      have hnot : x + (t₀ - s) • (y - x) ∉ S.C k := S.notMem_C_of_mem_U hbefore k
      rw [hb', hside _ hsb2, add_sub_cancel_left, dotProduct_smul, dotProduct_neg,
        smul_eq_mul] at hnot
      push Not at hnot; exact hnot
    -- after `z`: in `H` and in the interior of `C k`
    have hafter : z + s • (y - x) ∈ S.H := by
      have := hH (t₀ + s) ⟨by linarith, by linarith⟩
      convert this using 1; rw [hzdef]; module
    have hint : z + s • (y - x) ∈ interior (S.C k) := by
      refine hole_mem_interior_of_side hside hsb1 ?_
      rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul]
      linarith [show s * -(w ⬝ᵥ (y - x)) = -(s * (w ⬝ᵥ (y - x))) by ring]
    exact Set.disjoint_left.1 (S.disjoint_interior_H k) hint hafter
  -- conclude by connectedness of `U`
  have hpc : IsPreconnected S.U := isPreconnected_connectedComponentIn
  have hxA : x ∈ A := ⟨hx, by rw [segment_same]; exact singleton_subset_iff.2 hx⟩
  have hUA : S.U ⊆ A := by
    by_contra hcon
    obtain ⟨y₀, hy₀U, hy₀A⟩ := not_subset.1 hcon
    obtain ⟨w, hwU, hwA, hwc⟩ := hpc A (closure A)ᶜ hAo isClosed_closure.isOpen_compl
      (fun y hy ↦ by
        by_cases h : y ∈ closure A
        · exact Or.inl (hcl y hy h)
        · exact Or.inr h)
      ⟨x, hx, hxA⟩ ⟨y₀, hy₀U, fun h ↦ hy₀A (hcl y₀ hy₀U h)⟩
    exact hwc (subset_closure hwA)
  intro y hy a b ha hb hab
  exact (hUA hy).2 ⟨a, b, ha, hb, hab, rfl⟩

end hole_Cfg

/-- **The core of Böröczky's Lemma 5** (the structure of the holes of a family of cells with the
rotation property). Let `Q = halfPlanesInter b d` be bounded and `C 0, …, C (n-1)`, `n ≥ 1`,
non-overlapping convex polygons in `Q` with the rotation property. Then every hole `H` lies in
`interior Q`, is convex, and every extreme point of `H` is a side point of some cell. -/
theorem hole_structure {m n : ℕ} (hn : 1 ≤ n) (b : Fin m → Fin 2 → ℝ) (d : Fin m → ℝ)
    (hQ : Bornology.IsBounded (halfPlanesInter b d)) (C : Fin n → Set (Fin 2 → ℝ))
    (hC : ∀ i, IsConvexPolygon (C i)) (hCQ : ∀ i, C i ⊆ halfPlanesInter b d)
    (hdisj : NonOverlapping C) (hrot : pin_HasRotationProperty (halfPlanesInter b d) C)
    {H : Set (Fin 2 → ℝ)} (hH : H ∈ holes (halfPlanesInter b d) C) :
    H ⊆ interior (halfPlanesInter b d) ∧ Convex ℝ H ∧
      (∀ v ∈ extremePoints ℝ H, ∃ i, IsSidePoint (C i) v) := by
  classical
  obtain ⟨x₀, hx₀, rfl⟩ := hH
  choose k a c hac using fun i ↦ (hC i).1
  let S : hole_Cfg n := ⟨m, b, d, hQ, C, k, a, c, hac, fun i ↦ (hC i).2.1, fun i ↦ (hC i).2.2,
    hCQ, hdisj, hrot, x₀, hx₀⟩
  have hHQ : S.H ⊆ interior S.Q := S.H_subset_interior ⟨⟨0, hn⟩⟩
  have hUo := S.isOpen_U hHQ
  have hUc := S.convex_U hHQ
  refine ⟨hHQ, hUc.closure, fun v hv ↦ ?_⟩
  have hvH : v ∈ S.H := hv.1
  have hvU : v ∉ S.U := by
    intro hvU
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hUo v hvU
    set e : Fin 2 → ℝ := (r / 2) • ![1, 0]
    have he : ‖e‖ < r := by
      have h1 : ‖(![1, 0] : Fin 2 → ℝ)‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ ?_
        fin_cases i <;> simp
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      nlinarith
    have he0 : e ≠ 0 := by
      intro h
      have := congrFun h 0
      simp [e] at this
      linarith
    have h1 : v + e ∈ S.H := subset_closure (hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact he))
    have h2 : v - e ∈ S.H := subset_closure (hball (by
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact he))
    have := (mem_extremePoints.1 hv).2 _ h1 _ h2
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
    exact he0 (by have := this.1; rw [add_eq_left] at this; exact this)
  exact S.sidePoint_of_mem_H hHQ hvH hvU

end PlaneConvex
