module

public import SmoothedPolygons.Ch2.Reinhardt
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Centrally symmetric hexagons

Helper lemmas on the centrally symmetric hexagons of §2.2 (`IsCSHexagon`, `hexagonOf`,
`hexMidpoint`, defined in `SmoothedPolygons.Ch2.Reinhardt`), shared by §2.3 (Theorem 2.3.9,
`SmoothedPolygons.Ch2.Mahler`) and by the density of balanced disks
(`SmoothedPolygons.Ch2.BalancedDensity`): their area, their description by three strips, and the
position of the edge midpoints of a least-area hexagon circumscribing a centrally symmetric convex
disk.

* `hex_volume_hexagonOf`: the area of a centrally symmetric hexagon is `4 det(m₀, m₁)`, where
  `m₀, m₁` are the midpoints of two consecutive edges. A centrally symmetric hexagon is
  `hex_mk a b c`, with vertices `a, b, c, -a, -b, -c` (`hex_eq_mk`); it is a convex hexagon iff
  `hex_Cond a b c` (`hex_isCSHexagon_mk_iff`). It is the intersection of three strips
  (`hex_mem_hexagonOf_iff`) and the union of the six triangles `[0, v_j, v_{j+1}]`
  (`hex_hexagonOf_eq`), which lie in the six angles cut out by the lines `ℝa, ℝb, ℝc` and so meet
  in null sets. The triangle `[0, u, w]` is the image of the standard triangle under the linear
  map with columns `u, w`, of area `|det(u, w)|/2` (`hex_volume_tri`). Hence
  `area = det(a, b) + det(b, c) + det(a, c)` (`hex_volume_mk`), which is `4 det(m₀, m₁)`.
* `hex_hexMidpoint_mem_frontier`: the edge midpoints of a least-area centrally symmetric hexagon
  circumscribing `K` lie on the boundary of `K` (§2.2, stated in the book). This is the book's
  rotation argument (`hex_midpoint_mem_of_least`, TeX ~1395–1400), for the edge `[a, b]` after a
  shift of indices. If `m₀ ∉ K`, the points of `K` on the line of the edge lie on one side of
  `m₀`. Move `a` along the line of the edge `[-c, a]` and `b` along the edge `[b, c]`, at speeds
  for which the edge line turns about a point `λ₀` of the edge between those points and `m₀`. To
  first order the area changes by `-c₀² τ` (`c₀ = 1 - 2λ₀ ≠ 0`), and by compactness of `K` the
  turned line still supports `K` for small `τ > 0`: a smaller circumscribed hexagon. The
  midpoint then lies in `K` and on the edge, so on `∂K`.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set

/-- The edge midpoints of a centrally symmetric hexagon satisfy `m₁ - m₀ = m₂`. -/
lemma hex_hexMidpoint_sub {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
    hexMidpoint v 1 - hexMidpoint v 0 = hexMidpoint v 2 := by
  have h3 : v 3 = -v 0 := by simpa using (hv 0).1
  have h21 : (2 : ZMod 6) + 1 = 3 := by decide
  have h11 : (1 : ZMod 6) + 1 = 2 := by decide
  simp only [hexMidpoint, midpoint_eq_smul_add, h21, h11, zero_add, h3]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- The edge midpoints of a centrally symmetric hexagon turn counterclockwise:
`det(m₀, m₁) > 0`. -/
lemma hex_det2_hexMidpoint_pos {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
    0 < det2 (hexMidpoint v 0) (hexMidpoint v 1) := by
  have h3 : v 3 = -v 0 := by simpa using (hv 0).1
  have h01 := (hv 0).2.1
  have h12 := (hv 1).2.1
  have h23 := (hv 2).2.1
  have h21 : (2 : ZMod 6) + 1 = 3 := by decide
  have h11 : (1 : ZMod 6) + 1 = 2 := by decide
  simp only [zero_add, h11, h21, h3] at h01 h12 h23
  simp only [hexMidpoint, midpoint_eq_smul_add, zero_add, h11]
  simp only [det2, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul, invOf_eq_inv] at *
  nlinarith [h01, h12, h23]

/-! ### Triangles and their areas -/

/-- The standard triangle `{p | 0 ≤ p₀, 0 ≤ p₁, p₀ + p₁ ≤ 1}`. -/
def hex_stdTri : Set (Fin 2 → ℝ) := {p | 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + p 1 ≤ 1}

/-- The linear map `p ↦ p₀ u + p₁ w`. -/
noncomputable def hex_lin (u w : Fin 2 → ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.toLin' !![u 0, w 0; u 1, w 1]

lemma hex_lin_apply (u w p : Fin 2 → ℝ) : hex_lin u w p = p 0 • u + p 1 • w := by
  ext i
  fin_cases i <;> simp [hex_lin, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

lemma hex_det_lin (u w : Fin 2 → ℝ) : LinearMap.det (hex_lin u w) = det2 u w := by
  rw [hex_lin, LinearMap.det_toLin', Matrix.det_fin_two_of, det2]
  ring

/-- The triangle with vertices `0, u, w`. -/
noncomputable def hex_tri (u w : Fin 2 → ℝ) : Set (Fin 2 → ℝ) := hex_lin u w '' hex_stdTri

/-- The points of `[0, u, w]` are the combinations `s u + t w`, `s, t ≥ 0`, `s + t ≤ 1`. -/
lemma hex_mem_tri {u w x : Fin 2 → ℝ} :
    x ∈ hex_tri u w ↔ ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 ∧ x = s • u + t • w := by
  constructor
  · rintro ⟨p, ⟨h0, h1, h2⟩, rfl⟩
    exact ⟨p 0, p 1, h0, h1, h2, hex_lin_apply ..⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    refine ⟨![s, t], ⟨hs, ht, hst⟩, ?_⟩
    rw [hex_lin_apply]
    simp

lemma hex_isCompact_stdTri : IsCompact hex_stdTri := by
  refine (isCompact_Icc (a := (0 : Fin 2 → ℝ)) (b := 1)).of_isClosed_subset ?_ ?_
  · have h0 : Continuous fun p : Fin 2 → ℝ ↦ p 0 := continuous_apply 0
    have h1 : Continuous fun p : Fin 2 → ℝ ↦ p 1 := continuous_apply 1
    exact (isClosed_le continuous_const h0).inter
      ((isClosed_le continuous_const h1).inter (isClosed_le (h0.add h1) continuous_const))
  · rintro p ⟨h0, h1, h2⟩
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;> fin_cases i <;> simp <;> linarith

lemma hex_isCompact_tri (u w : Fin 2 → ℝ) : IsCompact (hex_tri u w) :=
  hex_isCompact_stdTri.image (hex_lin u w).continuous_of_finiteDimensional

/-- The triangle `[0, u, w]` lies in every convex set containing `0, u, w`. -/
lemma hex_tri_subset {S : Set (Fin 2 → ℝ)} (hS : Convex ℝ S) {u w : Fin 2 → ℝ} (h0 : 0 ∈ S)
    (hu : u ∈ S) (hw : w ∈ S) : hex_tri u w ⊆ S := by
  intro x hx
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hex_mem_tri.1 hx
  have := hS.sum_mem (t := Finset.univ) (w := ![1 - s - t, s, t]) (z := ![0, u, w])
    (fun i _ ↦ by fin_cases i <;> simp <;> linarith) (by simp [Fin.sum_univ_three]; ring)
    (fun i _ ↦ by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_three] using this

/-- A line through the origin is a null set. -/
lemma hex_volume_line {u : Fin 2 → ℝ} (hu : u ≠ 0) : volume {x : Fin 2 → ℝ | det2 u x = 0} = 0 := by
  let L : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := u 0 • LinearMap.proj 1 - u 1 • LinearMap.proj 0
  have hL : {x : Fin 2 → ℝ | det2 u x = 0} = (LinearMap.ker L : Set (Fin 2 → ℝ)) := by
    ext x
    simp [L, det2, mul_comm]
  rw [hL]
  refine Measure.addHaar_submodule _ _ fun h ↦ hu ?_
  have h' : L ![-u 1, u 0] = 0 := by
    rw [← LinearMap.mem_ker, h]
    trivial
  simp [L] at h'
  ext i
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]

lemma hex_volume_tri_eq (u w : Fin 2 → ℝ) :
    volume (hex_tri u w) = ENNReal.ofReal |det2 u w| * volume hex_stdTri := by
  rw [hex_tri, Measure.addHaar_image_linearMap, hex_det_lin]

/-- The standard triangle has area `1/2`: the unit square is the union of the triangles
`[0, e₀, e₀ + e₁]` and `[0, e₀ + e₁, e₁]`, both linear images of it with determinant `±1`, which
meet in the diagonal. -/
lemma hex_volume_stdTri : volume hex_stdTri = ENNReal.ofReal (1 / 2) := by
  have hsq : Icc (0 : Fin 2 → ℝ) 1 = hex_tri ![1, 0] ![1, 1] ∪ hex_tri ![1, 1] ![0, 1] := by
    ext x
    simp only [mem_Icc, mem_union, hex_mem_tri]
    constructor
    · rintro ⟨h0, h1⟩
      have h00 := h0 0; have h01 := h0 1; have h10 := h1 0; have h11 := h1 1
      simp only [Pi.zero_apply, Pi.one_apply] at h00 h01 h10 h11
      rcases le_total (x 1) (x 0) with h | h
      · left
        refine ⟨x 0 - x 1, x 1, by linarith, h01, by linarith, ?_⟩
        ext i; fin_cases i <;> simp
      · right
        refine ⟨x 0, x 1 - x 0, h00, by linarith, by linarith, ?_⟩
        ext i; fin_cases i <;> simp
    · rintro (⟨s, t, hs, ht, hst, rfl⟩ | ⟨s, t, hs, ht, hst, rfl⟩) <;>
        refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;> fin_cases i <;> simp <;> linarith
  have hdisj : AEDisjoint volume (hex_tri ![1, 0] ![1, 1]) (hex_tri ![1, 1] ![0, 1]) := by
    refine measure_mono_null (fun x ⟨h1, h2⟩ ↦ ?_) (hex_volume_line (u := ![1, 1]) ?_)
    · obtain ⟨s, t, hs, ht, -, rfl⟩ := hex_mem_tri.1 h1
      obtain ⟨s', t', hs', ht', -, h⟩ := hex_mem_tri.1 h2
      have e0 := congrFun h 0
      have e1 := congrFun h 1
      simp at e0 e1
      simp [det2]
      linarith
    · intro h
      simpa using congrFun h 0
  have hvol := Real.volume_Icc_pi (a := (0 : Fin 2 → ℝ)) (b := 1)
  rw [hsq, measure_union₀ (hex_isCompact_tri _ _).measurableSet.nullMeasurableSet hdisj,
    hex_volume_tri_eq, hex_volume_tri_eq] at hvol
  have d1 : det2 ![1, 0] ![1, 1] = 1 := by simp [det2]
  have d2 : det2 ![1, 1] ![0, 1] = 1 := by simp [det2]
  have hprod : ∏ i : Fin 2, ENNReal.ofReal ((1 : Fin 2 → ℝ) i - (0 : Fin 2 → ℝ) i) = 1 := by
    simp
  rw [d1, d2, abs_one, ENNReal.ofReal_one, one_mul, hprod] at hvol
  have hfin : volume hex_stdTri ≠ ⊤ := by
    intro h; rw [h] at hvol; simp at hvol
  have := congrArg ENNReal.toReal hvol
  rw [ENNReal.toReal_add hfin hfin, ENNReal.toReal_one] at this
  rw [← ENNReal.ofReal_toReal hfin]
  congr 1
  linarith

/-- The area of the triangle `[0, u, w]` is `|det(u, w)|/2`. -/
lemma hex_volume_tri (u w : Fin 2 → ℝ) :
    volume (hex_tri u w) = ENNReal.ofReal (|det2 u w| / 2) := by
  rw [hex_volume_tri_eq, hex_volume_stdTri, ← ENNReal.ofReal_mul (abs_nonneg _)]
  ring_nf

/-- A point of the angle from `u` to `w` (counterclockwise), on the side of `0` of the line
through `u` and `w`, lies in the triangle `[0, u, w]`. -/
lemma hex_mem_tri_of {u w x : Fin 2 → ℝ} (hD : 0 < det2 u w) (h1 : 0 ≤ det2 u x)
    (h2 : det2 w x ≤ 0) (h3 : det2 (u - w) x ≤ det2 u w) : x ∈ hex_tri u w := by
  rw [hex_mem_tri]
  refine ⟨-det2 w x / det2 u w, det2 u x / det2 u w, div_nonneg (by linarith) hD.le,
    div_nonneg h1 hD.le, ?_, ?_⟩
  · rw [← add_div, div_le_one hD]
    have : det2 (u - w) x = det2 u x - det2 w x := by simp [det2]; ring
    linarith
  · ext i
    have hD0 : det2 u w ≠ 0 := hD.ne'
    fin_cases i <;> simp <;> field_simp <;> simp only [det2] <;> ring

/-- A linear functional `det(y, ·)` that has the sign `ε` at `u` and `w` has the sign `ε` on the
triangle `[0, u, w]`. -/
lemma hex_cone_sign {u w x y : Fin 2 → ℝ} {ε : ℝ} (hx : x ∈ hex_tri u w)
    (hu : 0 ≤ ε * det2 y u) (hw : 0 ≤ ε * det2 y w) : 0 ≤ ε * det2 y x := by
  obtain ⟨s, t, hs, ht, -, rfl⟩ := hex_mem_tri.1 hx
  have : ε * det2 y (s • u + t • w) = s * (ε * det2 y u) + t * (ε * det2 y w) := by
    simp [det2]; ring
  rw [this]
  positivity

/-! ### Centrally symmetric hexagons -/

/-- The centrally symmetric hexagon with vertices `a, b, c, -a, -b, -c`. -/
def hex_mk (a b c : Fin 2 → ℝ) : ZMod 6 → Fin 2 → ℝ :=
  fun k ↦ (![a, b, c, -a, -b, -c] : Fin 6 → Fin 2 → ℝ) k

/-- The six elements of `ℤ/6ℤ`. -/
lemma hex_cases (k : ZMod 6) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by
  revert k; decide

section Hex

variable {a b c x : Fin 2 → ℝ}

lemma hex_mk_zero : hex_mk a b c 0 = a := rfl
lemma hex_mk_one : hex_mk a b c 1 = b := rfl
lemma hex_mk_two : hex_mk a b c 2 = c := rfl
lemma hex_mk_three : hex_mk a b c 3 = -a := rfl
lemma hex_mk_four : hex_mk a b c 4 = -b := rfl
lemma hex_mk_five : hex_mk a b c 5 = -c := rfl

/-- Additions of numerals in `ℤ/6ℤ`. -/
lemma hex_zmod_facts :
    (0 : ZMod 6) + 1 = 1 ∧ (1 : ZMod 6) + 1 = 2 ∧ (2 : ZMod 6) + 1 = 3 ∧ (3 : ZMod 6) + 1 = 4 ∧
    (4 : ZMod 6) + 1 = 5 ∧ (5 : ZMod 6) + 1 = 0 ∧ (0 : ZMod 6) + 2 = 2 ∧ (1 : ZMod 6) + 2 = 3 ∧
    (2 : ZMod 6) + 2 = 4 ∧ (3 : ZMod 6) + 2 = 5 ∧ (4 : ZMod 6) + 2 = 0 ∧ (5 : ZMod 6) + 2 = 1 ∧
    (0 : ZMod 6) + 3 = 3 ∧ (1 : ZMod 6) + 3 = 4 ∧ (2 : ZMod 6) + 3 = 5 ∧ (3 : ZMod 6) + 3 = 0 ∧
    (4 : ZMod 6) + 3 = 1 ∧ (5 : ZMod 6) + 3 = 2 := by decide

/-- A centrally symmetric hexagon is `hex_mk (v 0) (v 1) (v 2)`. -/
lemma hex_eq_mk {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) : v = hex_mk (v 0) (v 1) (v 2) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, f03, f13, f23, -, -, -⟩ := hex_zmod_facts
  funext k
  rcases hex_cases k with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · have := (hv 0).1; rw [f03] at this; rw [this]; rfl
  · have := (hv 1).1; rw [f13] at this; rw [this]; rfl
  · have := (hv 2).1; rw [f23] at this; rw [this]; rfl

/-- The conditions on `a, b, c` that make `hex_mk a b c` a convex hexagon (`IsCSHexagon`). -/
structure hex_Cond (a b c : Fin 2 → ℝ) : Prop where
  hA : 0 < det2 a b
  hB : 0 < det2 b c
  hC : 0 < det2 a c
  h0 : det2 a c < det2 a b + det2 b c
  h1 : det2 a b < det2 b c + det2 a c
  h2 : det2 b c < det2 a b + det2 a c

/-- `hex_mk a b c` is a convex hexagon iff `hex_Cond a b c`. -/
lemma hex_isCSHexagon_mk_iff : IsCSHexagon (hex_mk a b c) ↔ hex_Cond a b c := by
  obtain ⟨f01, f11, f21, f31, f41, f51, f02, f12, f22, f32, f42, f52, f03, f13, f23, f33, f43,
    f53⟩ := hex_zmod_facts
  constructor
  · intro hv
    have e0 := hv 0
    have e1 := hv 1
    have e2 := hv 2
    simp only [f01, f11, f21, f02, f12, f22, hex_mk_zero, hex_mk_one, hex_mk_two,
      hex_mk_three, hex_mk_four] at e0 e1 e2
    obtain ⟨-, hA, t0⟩ := e0
    obtain ⟨-, hB, t1⟩ := e1
    obtain ⟨-, hC, t2⟩ := e2
    simp only [det2, Pi.sub_apply, Pi.neg_apply] at hA hB hC t0 t1 t2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [det2] <;> nlinarith
  · rintro ⟨hA, hB, hC, h0, h1, h2⟩
    simp only [det2] at hA hB hC h0 h1 h2
    intro k
    rcases hex_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [f01, f11, f21, f31, f41, f51, f02, f12, f22, f32, f42, f52, f03, f13, f23, f33,
        f43, f53, hex_mk_zero, hex_mk_one, hex_mk_two, hex_mk_three, hex_mk_four,
        hex_mk_five, neg_neg, true_and, det2, Pi.sub_apply, Pi.neg_apply] <;>
      refine ⟨?_, ?_⟩ <;> nlinarith

/-- The hexagon `hex_mk a b c` is the intersection of three strips. -/
def hex_strips (a b c x : Fin 2 → ℝ) : Prop :=
  |det2 (a - b) x| ≤ det2 a b ∧ |det2 (b - c) x| ≤ det2 b c ∧ |det2 (c + a) x| ≤ det2 a c

lemma hex_convex_abs_det2_le (u : Fin 2 → ℝ) (k : ℝ) : Convex ℝ {x | |det2 u x| ≤ k} := by
  intro x hx y hy s t hs ht hst
  simp only [mem_ofPred_eq] at *
  have : det2 u (s • x + t • y) = s * det2 u x + t * det2 u y := by simp [det2]; ring
  rw [this]
  calc |s * det2 u x + t * det2 u y| ≤ |s * det2 u x| + |t * det2 u y| := abs_add_le _ _
    _ = s * |det2 u x| + t * |det2 u y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
    _ ≤ s * k + t * k := by gcongr
    _ = k := by rw [← add_mul, hst, one_mul]

lemma hex_convex_strips : Convex ℝ {x | hex_strips a b c x} :=
  (hex_convex_abs_det2_le _ _).inter ((hex_convex_abs_det2_le _ _).inter
    (hex_convex_abs_det2_le _ _))

/-- The hexagon lies in the three strips: they are convex and contain its vertices. -/
lemma hex_strips_of_mem (h : hex_Cond a b c) (hx : x ∈ hexagonOf (hex_mk a b c)) :
    hex_strips a b c x := by
  refine convexHull_min (range_subset_iff.2 fun k ↦ ?_) hex_convex_strips hx
  obtain ⟨hA, hB, hC, h0, h1, h2⟩ := h
  simp only [det2] at hA hB hC h0 h1 h2
  simp only [mem_ofPred_eq, hex_strips, abs_le]
  rcases hex_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [hex_mk_zero, hex_mk_one, hex_mk_two, hex_mk_three, hex_mk_four,
      hex_mk_five, det2, Pi.sub_apply, Pi.neg_apply, Pi.add_apply] <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

/-- The vertices `v_j` of the hexagon `hex_mk a b c`, indexed by `Fin 6`. -/
def hex_us (a b c : Fin 2 → ℝ) : Fin 6 → Fin 2 → ℝ := ![a, b, c, -a, -b, -c]
/-- The vertices `v_{j+1}` of the hexagon `hex_mk a b c`, indexed by `Fin 6`. -/
def hex_ws (a b c : Fin 2 → ℝ) : Fin 6 → Fin 2 → ℝ := ![b, c, -a, -b, -c, a]
/-- The six triangles `[0, v_j, v_{j+1}]` into which the hexagon `hex_mk a b c` is cut. -/
noncomputable def hex_piece (a b c : Fin 2 → ℝ) (i : Fin 6) : Set (Fin 2 → ℝ) :=
  hex_tri (hex_us a b c i) (hex_ws a b c i)

/-- Every point of the three strips lies in one of the six triangles: the one whose angle at `0`
contains it. -/
lemma hex_exists_piece (h : hex_Cond a b c) (hx : hex_strips a b c x) :
    ∃ i, x ∈ hex_piece a b c i := by
  obtain ⟨hA, hB, hC, h0, h1, h2⟩ := h
  obtain ⟨s0, s1, s2⟩ := hx
  rw [abs_le] at s0 s1 s2
  have e (u w : Fin 2 → ℝ) : det2 (-u) w = -det2 u w := by simp [det2]; ring
  have e' (u w : Fin 2 → ℝ) : det2 u (-w) = -det2 u w := by simp [det2]; ring
  have es (u w : Fin 2 → ℝ) : det2 (u - w) x = det2 u x - det2 w x := by simp [det2]; ring
  have ea (u w : Fin 2 → ℝ) : det2 (u + w) x = det2 u x + det2 w x := by simp [det2]; ring
  have eca : det2 c (-a) = det2 a c := by simp [det2]; ring
  have eac : det2 c a = -det2 a c := by simp [det2]; ring
  rw [es] at s0 s1
  rw [ea] at s2
  rcases le_or_gt 0 (det2 a x) with ha | ha
  · rcases le_or_gt (det2 b x) 0 with hb | hb
    · exact ⟨0, show x ∈ hex_tri a b from hex_mem_tri_of hA ha hb (by rw [es]; linarith)⟩
    · rcases le_or_gt (det2 c x) 0 with hc | hc
      · exact ⟨1, show x ∈ hex_tri b c from hex_mem_tri_of hB hb.le hc (by rw [es]; linarith)⟩
      · exact ⟨2, show x ∈ hex_tri c (-a) from hex_mem_tri_of (by rwa [eca]) hc.le
          (by rw [e]; linarith) (by rw [es, e, eca]; linarith)⟩
  · rcases le_or_gt 0 (det2 b x) with hb | hb
    · exact ⟨3, show x ∈ hex_tri (-a) (-b) from hex_mem_tri_of (by rwa [e, e', neg_neg])
        (by rw [e]; linarith) (by rw [e]; linarith) (by rw [es, e, e, e, e', neg_neg]; linarith)⟩
    · rcases le_or_gt 0 (det2 c x) with hc | hc
      · exact ⟨4, show x ∈ hex_tri (-b) (-c) from hex_mem_tri_of (by rwa [e, e', neg_neg])
          (by rw [e]; linarith) (by rw [e]; linarith)
          (by rw [es, e, e, e, e', neg_neg]; linarith)⟩
      · refine ⟨5, show x ∈ hex_tri (-c) a from hex_mem_tri_of
          (by rw [e, eac]; linarith) (by rw [e]; linarith) ha.le
          (by rw [es, e, e, eac]; linarith)⟩

lemma hex_vertex_mem (k : ZMod 6) : hex_mk a b c k ∈ hexagonOf (hex_mk a b c) :=
  subset_convexHull ℝ _ (mem_range_self k)

lemma hex_zero_mem : (0 : Fin 2 → ℝ) ∈ hexagonOf (hex_mk a b c) := by
  have := convex_convexHull ℝ (range (hex_mk a b c)) (hex_vertex_mem 0) (hex_vertex_mem 3)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [hex_mk_zero, hex_mk_three, smul_neg, add_neg_cancel] at this
  exact this

lemma hex_piece_subset (i : Fin 6) : hex_piece a b c i ⊆ hexagonOf (hex_mk a b c) := by
  refine hex_tri_subset (convex_convexHull ℝ _) hex_zero_mem ?_ ?_ <;>
    fin_cases i
  all_goals first
    | exact hex_vertex_mem 0 | exact hex_vertex_mem 1 | exact hex_vertex_mem 2
    | exact hex_vertex_mem 3 | exact hex_vertex_mem 4 | exact hex_vertex_mem 5

/-- The hexagon is the union of its six triangles `[0, v_j, v_{j+1}]`. -/
lemma hex_hexagonOf_eq (h : hex_Cond a b c) :
    hexagonOf (hex_mk a b c) = ⋃ i, hex_piece a b c i := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := hex_exists_piece h (hex_strips_of_mem h hx)
    exact mem_iUnion.2 ⟨i, hi⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    exact hex_piece_subset i hi

/-- The hexagon is the intersection of three strips. -/
lemma hex_mem_hexagonOf_iff (h : hex_Cond a b c) :
    x ∈ hexagonOf (hex_mk a b c) ↔ hex_strips a b c x := by
  refine ⟨hex_strips_of_mem h, fun hx ↦ ?_⟩
  obtain ⟨i, hi⟩ := hex_exists_piece h hx
  exact hex_piece_subset i hi

/-- The signs of `det(a, x), det(b, x), det(c, x)` on the six triangles of the hexagon; they
differ for any two triangles. -/
lemma hex_piece_signs (h : hex_Cond a b c) (i : Fin 6) (hx : x ∈ hex_piece a b c i) :
    0 ≤ (![1, 1, 1, -1, -1, -1] : Fin 6 → ℝ) i * det2 a x ∧
      0 ≤ (![-1, 1, 1, 1, -1, -1] : Fin 6 → ℝ) i * det2 b x ∧
      0 ≤ (![-1, -1, 1, 1, 1, -1] : Fin 6 → ℝ) i * det2 c x := by
  obtain ⟨hA, hB, hC, -, -, -⟩ := h
  simp only [det2] at hA hB hC
  refine ⟨hex_cone_sign hx ?_ ?_, hex_cone_sign hx ?_ ?_, hex_cone_sign hx ?_ ?_⟩ <;>
    fin_cases i <;> simp [hex_us, hex_ws, det2] <;> nlinarith

lemma hex_ne_zero_left (h : hex_Cond a b c) : a ≠ 0 := by
  rintro rfl; have := h.hA; simp [det2] at this

lemma hex_ne_zero_mid (h : hex_Cond a b c) : b ≠ 0 := by
  rintro rfl; have := h.hA; simp [det2] at this

lemma hex_ne_zero_right (h : hex_Cond a b c) : c ≠ 0 := by
  rintro rfl; have := h.hB; simp [det2] at this

/-- Two triangles of the hexagon meet in a null set (in one of the lines `ℝa, ℝb, ℝc`). -/
lemma hex_piece_aedisjoint (h : hex_Cond a b c) :
    Pairwise (Function.onFun (AEDisjoint volume) (hex_piece a b c)) := by
  have hN : volume ({x : Fin 2 → ℝ | det2 a x = 0} ∪ {x | det2 b x = 0} ∪
      {x | det2 c x = 0}) = 0 :=
    measure_union_null (measure_union_null (hex_volume_line (hex_ne_zero_left h))
      (hex_volume_line (hex_ne_zero_mid h))) (hex_volume_line (hex_ne_zero_right h))
  intro i j hij
  refine measure_mono_null (fun x hx ↦ ?_) hN
  have si := hex_piece_signs h i hx.1
  have sj := hex_piece_signs h j hx.2
  simp only [mem_union, mem_ofPred_eq]
  fin_cases i <;> fin_cases j <;> simp at hij si sj <;>
    first | (left; left; linarith) | (left; right; linarith) | (right; linarith)

/-- The area of the hexagon `hex_mk a b c` is `det(a, b) + det(b, c) + det(a, c)`. -/
lemma hex_volume_mk (h : hex_Cond a b c) :
    volume (hexagonOf (hex_mk a b c)) = ENNReal.ofReal (det2 a b + det2 b c + det2 a c) := by
  rw [hex_hexagonOf_eq h, measure_iUnion₀ (hex_piece_aedisjoint h)
    (fun i ↦ (hex_isCompact_tri _ _).measurableSet.nullMeasurableSet), tsum_fintype]
  simp only [hex_piece, hex_volume_tri]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by positivity)]
  congr 1
  have e1 : det2 c (-a) = det2 a c := by simp [det2]; ring
  have e2 : det2 (-a) (-b) = det2 a b := by simp [det2]
  have e3 : det2 (-b) (-c) = det2 b c := by simp [det2]
  have e4 : det2 (-c) a = det2 a c := by simp [det2]; ring
  simp only [Fin.sum_univ_six, hex_us, hex_ws, Matrix.cons_val, e1, e2, e3, e4,
    abs_of_pos h.hA, abs_of_pos h.hB, abs_of_pos h.hC]
  ring

/-- The area of the hexagon `hex_mk a b c`, as a real number. -/
lemma hex_volume_real_mk (h : hex_Cond a b c) :
    volume.real (hexagonOf (hex_mk a b c)) = det2 a b + det2 b c + det2 a c := by
  rw [measureReal_def, hex_volume_mk h, ENNReal.toReal_ofReal]
  linarith [h.hA, h.hB, h.hC]

end Hex

/-- The area of a centrally symmetric hexagon is `4 det(m₀, m₁)`, where `m₀, m₁` are the midpoints
of two consecutive edges (§2.2: `det(s_j, s_{j+1})` is a fixed fraction of `area(H_K)`). -/
lemma hex_volume_hexagonOf {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
    volume.real (hexagonOf v) = 4 * det2 (hexMidpoint v 0) (hexMidpoint v 1) := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, v = hex_mk a b c := ⟨_, _, _, hex_eq_mk hv⟩
  rw [hex_volume_real_mk (hex_isCSHexagon_mk_iff.1 hv)]
  simp only [hexMidpoint, zero_add, show (1 : ZMod 6) + 1 = 2 from rfl, hex_mk_zero,
    hex_mk_one, hex_mk_two, midpoint_eq_smul_add]
  simp only [det2, Pi.smul_apply, Pi.add_apply, smul_eq_mul, invOf_eq_inv]
  ring

/-! ### Edge midpoints of a least-area hexagon -/

/-- `det(f(τ), g(τ))` is continuous in `τ`. -/
lemma hex_continuous_det2 {f g : ℝ → Fin 2 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun τ ↦ det2 (f τ) (g τ) := by
  unfold det2
  fun_prop

open Filter Topology in
/-- The conditions `hex_Cond` persist under small perturbations of `a` and `b`. -/
lemma hex_eventually_cond {a b c : Fin 2 → ℝ} (h : hex_Cond a b c)
    {a' b' : ℝ → Fin 2 → ℝ} (ha : Continuous a') (hb : Continuous b') (ha0 : a' 0 = a)
    (hb0 : b' 0 = b) : ∀ᶠ τ in 𝓝 0, hex_Cond (a' τ) (b' τ) c := by
  have dab := hex_continuous_det2 ha hb
  have dbc := hex_continuous_det2 hb (continuous_const (y := c))
  have dac := hex_continuous_det2 ha (continuous_const (y := c))
  have e1 : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 < det2 (a' τ) (b' τ) :=
    continuousAt_const.eventually_lt dab.continuousAt (by simpa [ha0, hb0] using h.hA)
  have e2 : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 < det2 (b' τ) c :=
    continuousAt_const.eventually_lt dbc.continuousAt (by simpa [hb0] using h.hB)
  have e3 : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 < det2 (a' τ) c :=
    continuousAt_const.eventually_lt dac.continuousAt (by simpa [ha0] using h.hC)
  have e4 : ∀ᶠ τ in 𝓝 (0 : ℝ), det2 (a' τ) c < det2 (a' τ) (b' τ) + det2 (b' τ) c :=
    dac.continuousAt.eventually_lt (dab.add dbc).continuousAt (by simpa [ha0, hb0] using h.h0)
  have e5 : ∀ᶠ τ in 𝓝 (0 : ℝ), det2 (a' τ) (b' τ) < det2 (b' τ) c + det2 (a' τ) c :=
    dab.continuousAt.eventually_lt (dbc.add dac).continuousAt (by simpa [ha0, hb0] using h.h1)
  have e6 : ∀ᶠ τ in 𝓝 (0 : ℝ), det2 (b' τ) c < det2 (a' τ) (b' τ) + det2 (a' τ) c :=
    dbc.continuousAt.eventually_lt (dab.add dac).continuousAt (by simpa [ha0, hb0] using h.h2)
  filter_upwards [e1, e2, e3, e4, e5, e6] with τ h1 h2 h3 h4 h5 h6 using ⟨h1, h2, h3, h4, h5, h6⟩

lemma hex_det2_smul_left (k : ℝ) (u x : Fin 2 → ℝ) : det2 (k • u) x = k * det2 u x := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]; ring

lemma hex_det2_neg_right (u x : Fin 2 → ℝ) : det2 u (-x) = -det2 u x := by
  simp only [det2, Pi.neg_apply]; ring

open Filter Topology in
/-- **The rotation argument** (§2.2, TeX ~1395–1400). If the midpoint of the edge `[a, b]` of a
circumscribed hexagon `hex_mk a b c` is not in `K`, then the line of that edge can be turned
about a point of the edge (moving the vertices `a` and `b` along the adjacent edge lines) so
that the hexagon still contains `K` and has smaller area. -/
lemma hex_midpoint_mem_of_least {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {a b c : Fin 2 → ℝ}
    (h : hex_Cond a b c) (hKH : K ⊆ hexagonOf (hex_mk a b c))
    (hmin : ∀ a' b' : Fin 2 → ℝ, hex_Cond a' b' c → K ⊆ hexagonOf (hex_mk a' b' c) →
      det2 a b + det2 b c + det2 a c ≤ det2 a' b' + det2 b' c + det2 a' c) :
    midpoint ℝ a b ∈ K := by
  obtain ⟨hconv, hcomp, -, hsymm⟩ := hK
  have hstrip : ∀ x ∈ K, hex_strips a b c x := fun x hx ↦ (hex_mem_hexagonOf_iff h).1 (hKH hx)
  have hA0 : det2 a b ≠ 0 := h.hA.ne'
  by_contra hm
  -- the support functional `f ≥ 0` of the edge `[a, b]`, vanishing on its line
  let f : (Fin 2 → ℝ) → ℝ := fun x ↦ det2 a b - det2 (a - b) x
  have hf_cont : Continuous f := by simp only [f, det2]; fun_prop
  have hf_nonneg : ∀ x ∈ K, 0 ≤ f x := fun x hx ↦ by
    have := (hstrip x hx).1
    simp only [f]
    linarith [le_abs_self (det2 (a - b) x)]
  -- the position `λ` along the edge: `x = (1 - λ) a + λ b` on its line
  let lam : (Fin 2 → ℝ) → ℝ := fun x ↦ det2 a x / det2 a b
  have hlam_cont : Continuous lam := by simp only [lam, det2]; fun_prop
  have hline : ∀ x, f x = 0 → x = (1 - lam x) • a + lam x • b := by
    intro x hx
    simp only [f, lam] at hx ⊢
    ext i
    fin_cases i <;> simp <;> field_simp <;> simp only [det2, Pi.sub_apply] at hx ⊢
    · linear_combination (-a 0) * hx
    · linear_combination (-a 1) * hx
  -- the contact set `Z = K ∩ {f = 0}` lies on one side of the midpoint
  let Z := K ∩ f ⁻¹' {0}
  have hZc : IsCompact Z := hcomp.inter_right (isClosed_singleton.preimage hf_cont)
  have hZconv : Convex ℝ Z := by
    refine hconv.inter fun x hx y hy s t hs ht hst ↦ ?_
    simp only [mem_preimage, mem_singleton_iff, f] at hx hy ⊢
    simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    linear_combination s * hx + t * hy - (a 0 * b 1 - a 1 * b 0) * hst
  have hdich : (∀ x ∈ Z, lam x < 1 / 2) ∨ (∀ x ∈ Z, 1 / 2 < lam x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨x₁, hx₁, h₁⟩, ⟨x₂, hx₂, h₂⟩⟩ := hcon
    obtain ⟨x, hxZ, hx⟩ := hZconv.isPreconnected.intermediate_value hx₂ hx₁
      hlam_cont.continuousOn ⟨h₂, h₁⟩
    apply hm
    have hx' := hline x hxZ.2
    rw [hx] at hx'
    have : midpoint ℝ a b = x := by
      rw [midpoint_eq_smul_add, hx']
      ext i
      simp
      ring
    rw [this]
    exact hxZ.1
  -- a point `λ₀` of the edge between the contact set and the midpoint, `c₀ = 1 - 2 λ₀`
  obtain ⟨l₀, c₀, hc₀, hc₀def, hpos⟩ : ∃ l₀ c₀ : ℝ, c₀ ≠ 0 ∧ c₀ = 1 - 2 * l₀ ∧
      ∀ x ∈ Z, 0 < c₀ * (l₀ - lam x) := by
    rcases hdich with hL | hR
    · obtain ⟨e, he, hle⟩ := hZc.exists_forall_le' (f := fun x ↦ 1 / 2 - lam x)
        (continuous_const.sub hlam_cont).continuousOn (a := 0)
        (fun x hx ↦ by have := hL x hx; linarith)
      refine ⟨1 / 2 - e / 2, e, he.ne', by ring, fun x hx ↦ mul_pos he ?_⟩
      have := hle x hx
      linarith
    · obtain ⟨e, he, hle⟩ := hZc.exists_forall_le' (f := fun x ↦ lam x - 1 / 2)
        (hlam_cont.sub continuous_const).continuousOn (a := 0)
        (fun x hx ↦ by have := hR x hx; linarith)
      refine ⟨1 / 2 + e / 2, -e, neg_ne_zero.2 he.ne', by ring,
        fun x hx ↦ mul_pos_of_neg_of_neg (by linarith) ?_⟩
      have := hle x hx
      linarith
  -- the turning angles: `a` moves along the line of the edge `[-c, a]`, `b` along `[b, c]`
  obtain ⟨α, hα⟩ : ∃ α, α = det2 a b + det2 a c - det2 b c := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = det2 a b + det2 b c - det2 a c := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = det2 b c + det2 a c - det2 a b := ⟨_, rfl⟩
  have hαpos : 0 < α := by rw [hα]; linarith [h.h2]
  have hβpos : 0 < β := by rw [hβ]; linarith [h.h0]
  obtain ⟨p, hp⟩ : ∃ p, p = l₀ * c₀ / α := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = (1 - l₀) * c₀ / β := ⟨_, rfl⟩
  have hpα : p * α = l₀ * c₀ := by rw [hp, div_mul_cancel₀ _ hαpos.ne']
  have hqβ : q * β = (1 - l₀) * c₀ := by rw [hq, div_mul_cancel₀ _ hβpos.ne']
  -- the first-order change `G` of the support functional; it is positive on the contact set
  let G : (Fin 2 → ℝ) → ℝ := fun x ↦
    q * det2 (c - b) (x - a) - p * det2 (a + c) (x - a) + p * α
  have hG_cont : Continuous G := by simp only [G, det2]; fun_prop
  have hGZ : ∀ x ∈ Z, 0 < G x := by
    intro x hx
    have hx' := hline x hx.2
    have key : G x = c₀ * (l₀ - lam x) := by
      generalize lam x = l at hx' ⊢
      subst hx'
      have e1 : det2 (c - b) ((1 - l) • a + l • b - a) = -l * β := by
        rw [hβ]
        simp only [det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have e2 : det2 (a + c) ((1 - l) • a + l • b - a) = l * α := by
        rw [hα]
        simp only [det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      simp only [G]
      rw [e1, e2]
      linear_combination (1 - l) * hpα - l * hqβ
    rw [key]
    exact hpos x hx
  have hE : ∀ τ x, det2 (a + (τ * p) • (a + c)) (b + (τ * q) • (c - b)) -
      det2 (a + (τ * p) • (a + c) - (b + (τ * q) • (c - b))) x =
      f x + τ * G x + τ ^ 2 * (p * q * γ) := by
    intro τ x
    simp only [f, G, hα, hγ, det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have harea : ∀ τ, det2 (a + (τ * p) • (a + c)) (b + (τ * q) • (c - b)) +
      det2 (b + (τ * q) • (c - b)) c + det2 (a + (τ * p) • (a + c)) c -
      (det2 a b + det2 b c + det2 a c) = τ * (p * α - q * β) + τ ^ 2 * (p * q * γ) := by
    intro τ
    simp only [hα, hβ, hγ, det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- uniform bounds from compactness
  obtain ⟨η, hη, hηZ⟩ := hZc.exists_forall_le' hG_cont.continuousOn (a := 0) hGZ
  let K₁ := K ∩ {x | G x ≤ η / 2}
  have hK₁c : IsCompact K₁ := hcomp.inter_right (isClosed_le hG_cont continuous_const)
  have hfK₁ : ∀ x ∈ K₁, 0 < f x := by
    intro x hx
    rcases (hf_nonneg x hx.1).lt_or_eq with h' | h'
    · exact h'
    · have h1 := hηZ x ⟨hx.1, h'.symm⟩
      have h2 : G x ≤ η / 2 := hx.2
      linarith
  obtain ⟨δ, hδ, hδK₁⟩ := hK₁c.exists_forall_le' hf_cont.continuousOn (a := 0) hfK₁
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hG_cont.continuousOn
  obtain ⟨R, hR⟩ : ∃ R, R = |p * q * γ| := ⟨_, rfl⟩
  -- a small turning angle `τ > 0`
  have ev1 : ∀ᶠ τ in 𝓝 (0 : ℝ), τ * M + τ ^ 2 * R < δ := by
    have : Continuous fun τ : ℝ ↦ τ * M + τ ^ 2 * R := by fun_prop
    exact this.continuousAt.eventually_lt continuousAt_const (by simpa using hδ)
  have ev2 : ∀ᶠ τ in 𝓝 (0 : ℝ), τ * R < η / 2 := by
    have : Continuous fun τ : ℝ ↦ τ * R := by fun_prop
    exact this.continuousAt.eventually_lt continuousAt_const (by simpa using half_pos hη)
  have ev3 : ∀ᶠ τ in 𝓝 (0 : ℝ), τ * (p * q * γ) < c₀ ^ 2 := by
    have : Continuous fun τ : ℝ ↦ τ * (p * q * γ) := by fun_prop
    exact this.continuousAt.eventually_lt continuousAt_const (by simp only [zero_mul]; positivity)
  have ev4 := hex_eventually_cond h (a' := fun τ ↦ a + (τ * p) • (a + c))
    (b' := fun τ ↦ b + (τ * q) • (c - b)) (by fun_prop) (by fun_prop) (by simp) (by simp)
  obtain ⟨τ, ⟨⟨⟨h1, h2⟩, h3⟩, hhex⟩, hτ⟩ := ((((ev1.and ev2).and ev3).and ev4).filter_mono
    nhdsWithin_le_nhds |>.and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hτ0 : 0 < τ := hτ
  -- the turned support line still supports `K`
  have hE_nonneg : ∀ x ∈ K, 0 ≤ f x + τ * G x + τ ^ 2 * (p * q * γ) := by
    intro x hx
    have hRb : -(τ ^ 2 * R) ≤ τ ^ 2 * (p * q * γ) := by
      have := mul_nonneg (sq_nonneg τ)
        (show 0 ≤ p * q * γ + R by rw [hR]; linarith [neg_abs_le (p * q * γ)])
      nlinarith
    rcases le_or_gt (G x) (η / 2) with hGx | hGx
    · have hfx := hδK₁ x ⟨hx, hGx⟩
      have hGM : |G x| ≤ M := by simpa [Real.norm_eq_abs] using hM x hx
      have : -(τ * M) ≤ τ * G x := by
        have := neg_abs_le (G x)
        nlinarith
      linarith
    · have hfx := hf_nonneg x hx
      have e1 : τ * (η / 2) ≤ τ * G x := mul_le_mul_of_nonneg_left hGx.le hτ0.le
      have e2 : τ ^ 2 * R ≤ τ * (η / 2) := by nlinarith
      linarith
  have hKsub : K ⊆ hexagonOf (hex_mk (a + (τ * p) • (a + c)) (b + (τ * q) • (c - b)) c) := by
    intro x hx
    rw [hex_mem_hexagonOf_iff hhex]
    have hE1 := hE_nonneg x hx
    have hE2 := hE_nonneg (-x) (hsymm x hx)
    rw [← hE] at hE1 hE2
    rw [hex_det2_neg_right] at hE2
    obtain ⟨-, s1, s2⟩ := hstrip x hx
    have hb' : b + (τ * q) • (c - b) - c = (1 - τ * q) • (b - c) := by module
    have hca' : c + (a + (τ * p) • (a + c)) = (1 + τ * p) • (c + a) := by module
    have hdb : det2 (b + (τ * q) • (c - b)) c = (1 - τ * q) * det2 b c := by
      simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hda : det2 (a + (τ * p) • (a + c)) c = (1 + τ * p) * det2 a c := by
      simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hq1 : 0 < 1 - τ * q := by
      have := hhex.hB
      rw [hdb] at this
      by_contra hh
      push Not at hh
      nlinarith [h.hB]
    have hp1 : 0 < 1 + τ * p := by
      have := hhex.hC
      rw [hda] at this
      by_contra hh
      push Not at hh
      nlinarith [h.hC]
    refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · rw [hb', hex_det2_smul_left, abs_mul, abs_of_pos hq1, hdb]
      exact mul_le_mul_of_nonneg_left s1 hq1.le
    · rw [hca', hex_det2_smul_left, abs_mul, abs_of_pos hp1, hda]
      exact mul_le_mul_of_nonneg_left s2 hp1.le
  -- and the turned hexagon has smaller area
  have hle := hmin _ _ hhex hKsub
  have ha := harea τ
  have key : τ * (p * α - q * β) + τ ^ 2 * (p * q * γ) =
      -(τ * (c₀ ^ 2 - τ * (p * q * γ))) := by
    rw [hpα, hqβ, hc₀def]
    ring
  linarith [mul_pos hτ0 (sub_pos.2 h3)]

open Filter Topology in
/-- The midpoint of the edge `[a, b]` of a least-area hexagon `hex_mk a b c` circumscribing `K`
is a boundary point of `K`: it is in `K` (`hex_midpoint_mem_of_least`) and on a support line. -/
lemma hex_midpoint_mem_frontier_of_least {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {a b c : Fin 2 → ℝ} (h : hex_Cond a b c) (hKH : K ⊆ hexagonOf (hex_mk a b c))
    (hmin : ∀ a' b' : Fin 2 → ℝ, hex_Cond a' b' c → K ⊆ hexagonOf (hex_mk a' b' c) →
      det2 a b + det2 b c + det2 a c ≤ det2 a' b' + det2 b' c + det2 a' c) :
    midpoint ℝ a b ∈ frontier K := by
  have hmK := hex_midpoint_mem_of_least hK h hKH hmin
  refine ⟨subset_closure hmK, fun hmi ↦ ?_⟩
  have hc : Continuous fun ε : ℝ ↦ midpoint ℝ a b + ε • a := by fun_prop
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), midpoint ℝ a b + ε • a ∈ K :=
    hc.continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 hmi)
  obtain ⟨ε, hεK, hε⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hε0 : (0 : ℝ) < ε := hε
  have := ((hex_mem_hexagonOf_iff h).1 (hKH hεK)).1
  have e : det2 (a - b) (midpoint ℝ a b + ε • a) = (1 + ε) * det2 a b := by
    rw [midpoint_eq_smul_add]
    simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, invOf_eq_inv]
    ring
  rw [e, abs_le] at this
  nlinarith [h.hA]

/-- `hex_hexMidpoint_mem_frontier` for the edge `j = 0`. -/
lemma hex_hexMidpoint_zero_mem_frontier {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) : hexMidpoint v 0 ∈ frontier K := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, v = hex_mk a b c := ⟨_, _, _, hex_eq_mk hv.1⟩
  have h := hex_isCSHexagon_mk_iff.1 hv.1
  have hm : hexMidpoint (hex_mk a b c) 0 = midpoint ℝ a b := rfl
  rw [hm]
  refine hex_midpoint_mem_frontier_of_least hK h hv.2.1 fun a' b' h' hK' ↦ ?_
  have := hv.2.2 _ (hex_isCSHexagon_mk_iff.2 h') hK'
  rw [hex_volume_mk h, hex_volume_mk h'] at this
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith [h'.hA, h'.hB, h'.hC])).1 this

/-- The midpoints of the edges of a least-area centrally symmetric hexagon circumscribing `K` lie
on the boundary of `K` (§2.2, before Definition 2.2.3). -/
lemma hex_hexMidpoint_mem_frontier {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) (j : ZMod 6) :
    hexMidpoint v j ∈ frontier K := by
  let v' : ZMod 6 → Fin 2 → ℝ := fun k ↦ v (k + j)
  have hrange : range v' = range v := (Equiv.addRight j).surjective.range_comp v
  have hhex : hexagonOf v' = hexagonOf v := by simp only [hexagonOf, hrange]
  have hcs : IsCSHexagon v' := by
    intro k
    obtain ⟨h1, h2, h3⟩ := hv.1 (k + j)
    refine ⟨?_, ?_, ?_⟩
    · simp only [v']; rw [show k + 3 + j = k + j + 3 by ring]; exact h1
    · simp only [v']; rw [show k + 1 + j = k + j + 1 by ring]; exact h2
    · simp only [v']
      rw [show k + 1 + j = k + j + 1 by ring, show k + 2 + j = k + j + 2 by ring]
      exact h3
  have hv' : IsLeastAreaHexagon K v' :=
    ⟨hcs, hhex ▸ hv.2.1, fun w hw hKw ↦ hhex ▸ hv.2.2 w hw hKw⟩
  have hm : hexMidpoint v' 0 = hexMidpoint v j := by
    simp only [hexMidpoint, v', zero_add]
    rw [add_comm 1 j]
  rw [← hm]
  exact hex_hexMidpoint_zero_mem_frontier hK hv'

end SmoothedPolygons
