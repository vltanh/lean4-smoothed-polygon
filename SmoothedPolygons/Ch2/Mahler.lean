module

public import SmoothedPolygons.Ch2.Reinhardt
public import External.Mahler1947
public import External.MinkowskiMahler
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Mahler's approach (§2.3)

Admissible and critical lattices, the minimal determinant `Δ(K)` and irreducible disks
(Definitions 2.3.1–2.3.5), the theorems of Minkowski and Mahler on critical lattices and
circumscribed hexagons (Theorems 2.3.6 and 2.3.7, cited), Mahler's critical hexagons
(Definition 2.3.8), and their relation to Reinhardt's (Theorem 2.3.9, Corollary 2.3.10). The
proof of Theorem 2.3.9 needs some geometry of centrally symmetric hexagons (their area, their
description by the lines of their edges, `mm_*`).

Conventions. A support line of a centrally symmetric convex disk `K` at a boundary point does not
pass through the origin, an interior point of `K`, so it is `{x | a · x = 1}` for a unique vector
`a`; the side of the line that contains `K` is the half-plane `{x | a · x ≤ 1}`. Six symmetric
support lines `ℓ_j = {x | a_j · x = 1}`, `a_{j+3} = -a_j`, bound the hexagon
`polarHexagon a = {x | a_j · x ≤ 1 for all j}`. The lattice with basis `u₀, u₁` is
`latticeSpan u₀ u₁ = ℤ u₀ + ℤ u₁`.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix

/-! ### Definitions 2.3.1–2.3.5 -/

/-- **Definition 2.3.1** (admissible lattice; `def:admissible`). For `K ∈ 𝔎_ccs` centered at the
origin, a lattice `L` is `K`-admissible if no point of `L` other than `0` lies in the interior of
`K`. -/
def IsAdmissible (K : Set (Fin 2 → ℝ)) (L : Submodule ℤ (Fin 2 → ℝ)) : Prop :=
  ∀ x ∈ L, x ∈ interior K → x = 0

/-- The lattice `ℤ u₀ + ℤ u₁` with basis `u₀, u₁`. -/
def latticeSpan (u₀ u₁ : Fin 2 → ℝ) : Submodule ℤ (Fin 2 → ℝ) :=
  Submodule.span ℤ {u₀, u₁}

/-- `u₀, u₁` is a basis of the lattice `L`: they are linearly independent over `ℤ` and generate
`L`. -/
def IsLatticeBasis (L : Submodule ℤ (Fin 2 → ℝ)) (u₀ u₁ : Fin 2 → ℝ) : Prop :=
  LinearIndependent ℤ ![u₀, u₁] ∧ latticeSpan u₀ u₁ = L

/-- **Definition 2.3.2** (determinant of a lattice; `def:lattice-determinant`). For any lattice `L`
with basis `u₀, u₁`, the determinant `det(L)` (`latticeDet`, Mathlib's covolume) is equal to the
absolute value `|det(u₀, u₁)|`. -/
theorem definition2_3_2 {L : Submodule ℤ (Fin 2 → ℝ)} (hL : IsPlaneLattice L)
    {u₀ u₁ : Fin 2 → ℝ} (hu : IsLatticeBasis L u₀ u₁) :
    latticeDet L = |det2 u₀ u₁| := by
  obtain ⟨hd, hs⟩ := hL
  have : IsZLattice ℝ L := ⟨hs⟩
  obtain ⟨hli, hspan⟩ := hu
  have heq : Submodule.span ℤ (Set.range ![u₀, u₁]) = L := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
    exact hspan
  let b : Module.Basis (Fin 2) ℤ L := (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ heq)
  have hb : (Subtype.val ∘ ⇑b) = ![u₀, u₁] := by
    ext i : 1
    simp [b, Module.Basis.span_apply]
  rw [latticeDet, ZLattice.covolume_eq_det L b, hb, Matrix.det_fin_two]
  simp [det2]

/-- **Definition 2.3.3** (minimal determinant). For `K ∈ 𝔎_ccs`,
`Δ(K) = inf {det(L) | L a K-admissible lattice}`. -/
noncomputable def minDeterminant (K : Set (Fin 2 → ℝ)) : ℝ :=
  sInf {d | ∃ L, IsPlaneLattice L ∧ IsAdmissible K L ∧ latticeDet L = d}

/-- **Definition 2.3.4** (critical lattice). A lattice is critical for a convex disk `K` if its
determinant is equal to the minimal determinant of `K`. As in the sources (Minkowski, Mahler), a
critical lattice is a `K`-admissible lattice: the determinant is compared with the infimum over
admissible lattices, and Theorem 2.3.6 is false for lattices that are not admissible. -/
def IsCriticalLattice (K : Set (Fin 2 → ℝ)) (L : Submodule ℤ (Fin 2 → ℝ)) : Prop :=
  IsPlaneLattice L ∧ IsAdmissible K L ∧ latticeDet L = minDeterminant K

/-- **Definition 2.3.5** (irreducible disk; `def:irreducible`). A convex disk `K ∈ 𝔎_ccs` is
irreducible if every boundary point of `K` lies on a critical lattice of `K`. -/
def IsIrreducible (K : Set (Fin 2 → ℝ)) : Prop :=
  IsCCSDisk K ∧ ∀ u ∈ frontier K, ∃ L, IsCriticalLattice K L ∧ u ∈ L

/-! ### Theorem 2.3.6 (Minkowski, Mahler) -/

/-- **Theorem 2.3.6** (Minkowski, Mahler; `thm:minkowski-inscribe`; cited). Let `L` be a critical
lattice of a convex disk `K ∈ 𝔎_ccs`. Then `L` contains three points `s₀, s₁, s₂` on the boundary
of `K` such that (i) `s₀, s₁` is a basis of `L`, and (ii) `0 s₀ s₁ s₂` is a parallelogram (that
is, `s₁ = s₀ + s₂`) of area `det(L) = |det(s₀, s₁)| = Δ(K)`. Conversely, if `s₀, s₁, s₂` are three
points on the boundary of `K` such that `0 s₀ s₁ s₂` is a parallelogram, then the area
`|det(s₀, s₁)|` of this parallelogram is not less than `Δ(K)`, and is equal to `Δ(K)` if and only
if the lattice with basis `s₀, s₁` is critical. -/
theorem theorem2_3_6 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) :
    (∀ L, IsCriticalLattice K L →
      ∃ s₀ s₁ s₂ : Fin 2 → ℝ, s₀ ∈ L ∧ s₁ ∈ L ∧ s₂ ∈ L ∧
        s₀ ∈ frontier K ∧ s₁ ∈ frontier K ∧ s₂ ∈ frontier K ∧
        IsLatticeBasis L s₀ s₁ ∧ s₁ = s₀ + s₂ ∧
        latticeDet L = |det2 s₀ s₁| ∧ |det2 s₀ s₁| = minDeterminant K) ∧
    ∀ s₀ s₁ s₂ : Fin 2 → ℝ, s₀ ∈ frontier K → s₁ ∈ frontier K → s₂ ∈ frontier K →
      s₁ = s₀ + s₂ →
        minDeterminant K ≤ |det2 s₀ s₁| ∧
          (|det2 s₀ s₁| = minDeterminant K ↔ IsCriticalLattice K (latticeSpan s₀ s₁)) :=
  -- The definitions of the source (`External.MinkowskiMahler`) unfold to those of the book.
  External.minkowski_mahler hK

/-! ### Theorem 2.3.7 (Mahler 1947) and critical hexagons -/

/-- The hexagon `{x | a_j · x ≤ 1 for all j}` bounded by the lines `ℓ_j = {x | a_j · x = 1}`. -/
def polarHexagon (a : ZMod 6 → Fin 2 → ℝ) : Set (Fin 2 → ℝ) := {x | ∀ j, a j ⬝ᵥ x ≤ 1}

/-- The support lines of Theorem 2.3.7. The lines `ℓ_j = {x | a_j · x = 1}` are symmetric support
lines of `K` at the points `s_j` (`a_{j+3} = -a_j`, `s_j ∈ ℓ_j`), the unique support lines of `K`
at these points, such that

1. no two of these lines coincide;
2. the area of the centrally symmetric hexagon `H_K` bounded by the lines is `4Δ(K)`;
3. each side of `H_K` is bisected at the point `s_j` where it touches the boundary of `K`;
4. `H_K` is minimal: `area(H_K) = inf_H area(H)` over all hexagons `H` bounded by six distinct
   symmetric support lines of `K`. -/
def IsMahlerSupportSystem (K : Set (Fin 2 → ℝ)) (s a : ZMod 6 → Fin 2 → ℝ) : Prop :=
  (∀ j, a (j + 3) = -a j) ∧
  (∀ j, IsSupportLine K {x | a j ⬝ᵥ x = 1} ∧ a j ⬝ᵥ s j = 1) ∧
  (∀ j ℓ, IsSupportLine K ℓ → s j ∈ ℓ → ℓ = {x | a j ⬝ᵥ x = 1}) ∧
  (∀ i j, i ≠ j → a i ≠ a j) ∧
  volume.real (polarHexagon a) = 4 * minDeterminant K ∧
  (∀ j, ∃ p q, polarHexagon a ∩ {x | a j ⬝ᵥ x = 1} = segment ℝ p q ∧ s j = midpoint ℝ p q) ∧
  ∀ b : ZMod 6 → Fin 2 → ℝ, (∀ j, b (j + 3) = -b j) → (∀ i j, i ≠ j → b i ≠ b j) →
    (∀ j, IsSupportLine K {x | b j ⬝ᵥ x = 1}) →
      volume (polarHexagon a) ≤ volume (polarHexagon b)

/-- A support line in the sense of Definition 2.2.3 is a tac-line in the sense of Mahler
(`External.Mahler1947.IsTacLine`): a line that meets `K` separates no two points of `K` iff `K`
lies on one side of it. -/
lemma ch2_isSupportLine_iff_isTacLine (K ℓ : Set (Fin 2 → ℝ)) :
    IsSupportLine K ℓ ↔ External.Mahler1947.IsTacLine K ℓ := by
  refine and_congr_left fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨a, ha, c, rfl, hsep⟩
    by_cases h : ∃ x ∈ K, c < a ⬝ᵥ x
    · obtain ⟨x, hx, hxc⟩ := h
      refine ⟨-a, neg_ne_zero.2 ha, -c, ?_, fun y hy ↦ ?_⟩
      · ext z
        simp only [mem_ofPred_eq, neg_dotProduct, neg_inj]
      · have := hsep x hx y hy
        rw [neg_dotProduct, neg_le_neg_iff]
        by_contra hy'
        nlinarith [not_le.1 hy']
    · exact ⟨a, ha, c, rfl, fun x hx ↦ not_lt.1 fun h' ↦ h ⟨x, hx, h'⟩⟩
  · rintro ⟨a, ha, c, rfl, hle⟩
    refine ⟨a, ha, c, rfl, fun x hx y hy ↦ ?_⟩
    have := hle x hx
    have := hle y hy
    nlinarith

/-- **Theorem 2.3.7** (Mahler 1947; `thm:mahler-circumscribe`; cited). Let `K ∈ 𝔎_ccs` be a convex
disk which is not a parallelogram. Let `L` be a critical lattice of `K` with lattice points
`s₀, …, s₅` on the boundary of `K` satisfying `s₀ - s₁ + s₂ = 0` and `s_{j+3} = -s_j`. Then there
are unique symmetric support lines `ℓ_j` of `K` at these points such that (1) no two of these lines
coincide; (2) the area of the centrally symmetric hexagon `H_K` bounded by the support lines is
`area(H_K) = 4Δ(K)`; (3) each side of `H_K` is bisected at the lattice point `s_j` where it
touches the boundary of `K`; (4) `H_K` is minimal: `area(H_K) = inf_H area(H)` over all hexagons
`H` bounded by symmetric support lines of `K` (`IsMahlerSupportSystem`). -/
theorem theorem2_3_7 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (hpar : ¬ IsParallelogram K)
    {L : Submodule ℤ (Fin 2 → ℝ)} (hL : IsCriticalLattice K L) {s : ZMod 6 → Fin 2 → ℝ}
    (hsL : ∀ j, s j ∈ L) (hsK : ∀ j, s j ∈ frontier K) (h012 : s 0 - s 1 + s 2 = 0)
    (hsymm : ∀ j, s (j + 3) = -s j) :
    ∃! a, IsMahlerSupportSystem K s a := by
  have key : ∀ a, IsMahlerSupportSystem K s a ↔ External.Mahler1947.IsMahlerHexagon K s a := by
    intro a
    simp only [IsMahlerSupportSystem, External.Mahler1947.IsMahlerHexagon,
      ch2_isSupportLine_iff_isTacLine]
    rfl
  exact (existsUnique_congr key).2 (External.mahler_1947 hK hpar hL hsL hsK h012 hsymm)

/-- **Definition 2.3.8** (critical hexagon; `def:critical-hexagon`). For a convex disk
`K ∈ 𝔎_ccs`, a hexagon `H_K` given by the construction of Theorem 2.3.7 is called a critical
hexagon: `H_K` is bounded by the support lines of Theorem 2.3.7 at the points `s₀, …, s₅` of a
critical lattice of `K`. Theorem 2.3.7 assumes that `K` is not a parallelogram, and so does the
definition. -/
def IsCriticalHexagon (K H : Set (Fin 2 → ℝ)) : Prop :=
  ¬ IsParallelogram K ∧
  ∃ (L : Submodule ℤ (Fin 2 → ℝ)) (s a : ZMod 6 → Fin 2 → ℝ), IsCriticalLattice K L ∧
    (∀ j, s j ∈ L ∧ s j ∈ frontier K) ∧ s 0 - s 1 + s 2 = 0 ∧ (∀ j, s (j + 3) = -s j) ∧
    IsMahlerSupportSystem K s a ∧ H = polarHexagon a

/-! ### The proof of Theorem 2.3.9

The hexagon toolkit below (`mm_hex`, `mm_mem_hexagonOf_iff`, `mm_volume_hexagonOf`, …) is a copy
of the one of `SmoothedPolygons/Ch2/BalancedDensity.lean` (`bal_hex`, `bal_mem_hexagonOf_iff`,
`ch2_volume_hexagonOf`, …), which is downstream of this file; the two can be merged once the
toolkit is moved upstream. -/

/-- The edge midpoints of a centrally symmetric hexagon satisfy `m₁ - m₀ = m₂`. -/
lemma mm_hexMidpoint_sub {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
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
lemma mm_det2_hexMidpoint_pos {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
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
def mm_stdTri : Set (Fin 2 → ℝ) := {p | 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + p 1 ≤ 1}

/-- The linear map `p ↦ p₀ u + p₁ w`. -/
noncomputable def mm_lin (u w : Fin 2 → ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.toLin' !![u 0, w 0; u 1, w 1]

lemma mm_lin_apply (u w p : Fin 2 → ℝ) : mm_lin u w p = p 0 • u + p 1 • w := by
  ext i
  fin_cases i <;> simp [mm_lin, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

lemma mm_det_lin (u w : Fin 2 → ℝ) : LinearMap.det (mm_lin u w) = det2 u w := by
  rw [mm_lin, LinearMap.det_toLin', Matrix.det_fin_two_of, det2]
  ring

/-- The triangle with vertices `0, u, w`. -/
noncomputable def mm_tri (u w : Fin 2 → ℝ) : Set (Fin 2 → ℝ) := mm_lin u w '' mm_stdTri

/-- The points of `[0, u, w]` are the combinations `s u + t w`, `s, t ≥ 0`, `s + t ≤ 1`. -/
lemma mm_mem_tri {u w x : Fin 2 → ℝ} :
    x ∈ mm_tri u w ↔ ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 ∧ x = s • u + t • w := by
  constructor
  · rintro ⟨p, ⟨h0, h1, h2⟩, rfl⟩
    exact ⟨p 0, p 1, h0, h1, h2, mm_lin_apply ..⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    refine ⟨![s, t], ⟨hs, ht, hst⟩, ?_⟩
    rw [mm_lin_apply]
    simp

lemma mm_isCompact_stdTri : IsCompact mm_stdTri := by
  refine (isCompact_Icc (a := (0 : Fin 2 → ℝ)) (b := 1)).of_isClosed_subset ?_ ?_
  · have h0 : Continuous fun p : Fin 2 → ℝ ↦ p 0 := continuous_apply 0
    have h1 : Continuous fun p : Fin 2 → ℝ ↦ p 1 := continuous_apply 1
    exact (isClosed_le continuous_const h0).inter
      ((isClosed_le continuous_const h1).inter (isClosed_le (h0.add h1) continuous_const))
  · rintro p ⟨h0, h1, h2⟩
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;> fin_cases i <;> simp <;> linarith

lemma mm_isCompact_tri (u w : Fin 2 → ℝ) : IsCompact (mm_tri u w) :=
  mm_isCompact_stdTri.image (mm_lin u w).continuous_of_finiteDimensional

/-- The triangle `[0, u, w]` lies in every convex set containing `0, u, w`. -/
lemma mm_tri_subset {S : Set (Fin 2 → ℝ)} (hS : Convex ℝ S) {u w : Fin 2 → ℝ} (h0 : 0 ∈ S)
    (hu : u ∈ S) (hw : w ∈ S) : mm_tri u w ⊆ S := by
  intro x hx
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := mm_mem_tri.1 hx
  have := hS.sum_mem (t := Finset.univ) (w := ![1 - s - t, s, t]) (z := ![0, u, w])
    (fun i _ ↦ by fin_cases i <;> simp <;> linarith) (by simp [Fin.sum_univ_three]; ring)
    (fun i _ ↦ by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_three] using this

/-- A line through the origin is a null set. -/
lemma mm_volume_line {u : Fin 2 → ℝ} (hu : u ≠ 0) : volume {x : Fin 2 → ℝ | det2 u x = 0} = 0 := by
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

lemma mm_volume_tri_eq (u w : Fin 2 → ℝ) :
    volume (mm_tri u w) = ENNReal.ofReal |det2 u w| * volume mm_stdTri := by
  rw [mm_tri, Measure.addHaar_image_linearMap, mm_det_lin]

/-- The standard triangle has area `1/2`: the unit square is the union of the triangles
`[0, e₀, e₀ + e₁]` and `[0, e₀ + e₁, e₁]`, both linear images of it with determinant `±1`, which
meet in the diagonal. -/
lemma mm_volume_stdTri : volume mm_stdTri = ENNReal.ofReal (1 / 2) := by
  have hsq : Icc (0 : Fin 2 → ℝ) 1 = mm_tri ![1, 0] ![1, 1] ∪ mm_tri ![1, 1] ![0, 1] := by
    ext x
    simp only [mem_Icc, mem_union, mm_mem_tri]
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
  have hdisj : AEDisjoint volume (mm_tri ![1, 0] ![1, 1]) (mm_tri ![1, 1] ![0, 1]) := by
    refine measure_mono_null (fun x ⟨h1, h2⟩ ↦ ?_) (mm_volume_line (u := ![1, 1]) ?_)
    · obtain ⟨s, t, hs, ht, -, rfl⟩ := mm_mem_tri.1 h1
      obtain ⟨s', t', hs', ht', -, h⟩ := mm_mem_tri.1 h2
      have e0 := congrFun h 0
      have e1 := congrFun h 1
      simp at e0 e1
      simp [det2]
      linarith
    · intro h
      simpa using congrFun h 0
  have hvol := Real.volume_Icc_pi (a := (0 : Fin 2 → ℝ)) (b := 1)
  rw [hsq, measure_union₀ (mm_isCompact_tri _ _).measurableSet.nullMeasurableSet hdisj,
    mm_volume_tri_eq, mm_volume_tri_eq] at hvol
  have d1 : det2 ![1, 0] ![1, 1] = 1 := by simp [det2]
  have d2 : det2 ![1, 1] ![0, 1] = 1 := by simp [det2]
  have hprod : ∏ i : Fin 2, ENNReal.ofReal ((1 : Fin 2 → ℝ) i - (0 : Fin 2 → ℝ) i) = 1 := by
    simp
  rw [d1, d2, abs_one, ENNReal.ofReal_one, one_mul, hprod] at hvol
  have hfin : volume mm_stdTri ≠ ⊤ := by
    intro h; rw [h] at hvol; simp at hvol
  have := congrArg ENNReal.toReal hvol
  rw [ENNReal.toReal_add hfin hfin, ENNReal.toReal_one] at this
  rw [← ENNReal.ofReal_toReal hfin]
  congr 1
  linarith

/-- The area of the triangle `[0, u, w]` is `|det(u, w)|/2`. -/
lemma mm_volume_tri (u w : Fin 2 → ℝ) :
    volume (mm_tri u w) = ENNReal.ofReal (|det2 u w| / 2) := by
  rw [mm_volume_tri_eq, mm_volume_stdTri, ← ENNReal.ofReal_mul (abs_nonneg _)]
  ring_nf

/-- A point of the angle from `u` to `w` (counterclockwise), on the side of `0` of the line
through `u` and `w`, lies in the triangle `[0, u, w]`. -/
lemma mm_mem_tri_of {u w x : Fin 2 → ℝ} (hD : 0 < det2 u w) (h1 : 0 ≤ det2 u x)
    (h2 : det2 w x ≤ 0) (h3 : det2 (u - w) x ≤ det2 u w) : x ∈ mm_tri u w := by
  rw [mm_mem_tri]
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
lemma mm_cone_sign {u w x y : Fin 2 → ℝ} {ε : ℝ} (hx : x ∈ mm_tri u w)
    (hu : 0 ≤ ε * det2 y u) (hw : 0 ≤ ε * det2 y w) : 0 ≤ ε * det2 y x := by
  obtain ⟨s, t, hs, ht, -, rfl⟩ := mm_mem_tri.1 hx
  have : ε * det2 y (s • u + t • w) = s * (ε * det2 y u) + t * (ε * det2 y w) := by
    simp [det2]; ring
  rw [this]
  positivity

/-! ### Centrally symmetric hexagons -/

/-- The centrally symmetric hexagon with vertices `a, b, c, -a, -b, -c`. -/
def mm_hex (a b c : Fin 2 → ℝ) : ZMod 6 → Fin 2 → ℝ :=
  fun k ↦ (![a, b, c, -a, -b, -c] : Fin 6 → Fin 2 → ℝ) k

/-- The six elements of `ℤ/6ℤ`. -/
lemma mm_cases (k : ZMod 6) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by
  revert k; decide

section mm_Hex

variable {a b c x : Fin 2 → ℝ}

lemma mm_hex_zero : mm_hex a b c 0 = a := rfl
lemma mm_hex_one : mm_hex a b c 1 = b := rfl
lemma mm_hex_two : mm_hex a b c 2 = c := rfl
lemma mm_hex_three : mm_hex a b c 3 = -a := rfl
lemma mm_hex_four : mm_hex a b c 4 = -b := rfl
lemma mm_hex_five : mm_hex a b c 5 = -c := rfl

/-- Additions of numerals in `ℤ/6ℤ`. -/
lemma mm_zmod_facts :
    (0 : ZMod 6) + 1 = 1 ∧ (1 : ZMod 6) + 1 = 2 ∧ (2 : ZMod 6) + 1 = 3 ∧ (3 : ZMod 6) + 1 = 4 ∧
    (4 : ZMod 6) + 1 = 5 ∧ (5 : ZMod 6) + 1 = 0 ∧ (0 : ZMod 6) + 2 = 2 ∧ (1 : ZMod 6) + 2 = 3 ∧
    (2 : ZMod 6) + 2 = 4 ∧ (3 : ZMod 6) + 2 = 5 ∧ (4 : ZMod 6) + 2 = 0 ∧ (5 : ZMod 6) + 2 = 1 ∧
    (0 : ZMod 6) + 3 = 3 ∧ (1 : ZMod 6) + 3 = 4 ∧ (2 : ZMod 6) + 3 = 5 ∧ (3 : ZMod 6) + 3 = 0 ∧
    (4 : ZMod 6) + 3 = 1 ∧ (5 : ZMod 6) + 3 = 2 := by decide

/-- A centrally symmetric hexagon is `mm_hex (v 0) (v 1) (v 2)`. -/
lemma mm_eq_hex {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) : v = mm_hex (v 0) (v 1) (v 2) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, f03, f13, f23, -, -, -⟩ := mm_zmod_facts
  funext k
  rcases mm_cases k with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · have := (hv 0).1; rw [f03] at this; rw [this]; rfl
  · have := (hv 1).1; rw [f13] at this; rw [this]; rfl
  · have := (hv 2).1; rw [f23] at this; rw [this]; rfl

/-- The conditions on `a, b, c` that make `mm_hex a b c` a convex hexagon (`IsCSHexagon`). -/
structure mm_HexCond (a b c : Fin 2 → ℝ) : Prop where
  hA : 0 < det2 a b
  hB : 0 < det2 b c
  hC : 0 < det2 a c
  h0 : det2 a c < det2 a b + det2 b c
  h1 : det2 a b < det2 b c + det2 a c
  h2 : det2 b c < det2 a b + det2 a c

/-- `mm_hex a b c` is a convex hexagon iff `mm_HexCond a b c`. -/
lemma mm_isCSHexagon_iff : IsCSHexagon (mm_hex a b c) ↔ mm_HexCond a b c := by
  obtain ⟨f01, f11, f21, f31, f41, f51, f02, f12, f22, f32, f42, f52, f03, f13, f23, f33, f43,
    f53⟩ := mm_zmod_facts
  constructor
  · intro hv
    have e0 := hv 0
    have e1 := hv 1
    have e2 := hv 2
    simp only [f01, f11, f21, f02, f12, f22, mm_hex_zero, mm_hex_one, mm_hex_two,
      mm_hex_three, mm_hex_four] at e0 e1 e2
    obtain ⟨-, hA, t0⟩ := e0
    obtain ⟨-, hB, t1⟩ := e1
    obtain ⟨-, hC, t2⟩ := e2
    simp only [det2, Pi.sub_apply, Pi.neg_apply] at hA hB hC t0 t1 t2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [det2] <;> nlinarith
  · rintro ⟨hA, hB, hC, h0, h1, h2⟩
    simp only [det2] at hA hB hC h0 h1 h2
    intro k
    rcases mm_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [f01, f11, f21, f31, f41, f51, f02, f12, f22, f32, f42, f52, f03, f13, f23, f33,
        f43, f53, mm_hex_zero, mm_hex_one, mm_hex_two, mm_hex_three, mm_hex_four,
        mm_hex_five, neg_neg, true_and, det2, Pi.sub_apply, Pi.neg_apply] <;>
      refine ⟨?_, ?_⟩ <;> nlinarith

/-- The hexagon `mm_hex a b c` is the intersection of three strips. -/
def mm_strips (a b c x : Fin 2 → ℝ) : Prop :=
  |det2 (a - b) x| ≤ det2 a b ∧ |det2 (b - c) x| ≤ det2 b c ∧ |det2 (c + a) x| ≤ det2 a c

lemma mm_convex_abs_det2_le (u : Fin 2 → ℝ) (k : ℝ) : Convex ℝ {x | |det2 u x| ≤ k} := by
  intro x hx y hy s t hs ht hst
  simp only [mem_ofPred_eq] at *
  have : det2 u (s • x + t • y) = s * det2 u x + t * det2 u y := by simp [det2]; ring
  rw [this]
  calc |s * det2 u x + t * det2 u y| ≤ |s * det2 u x| + |t * det2 u y| := abs_add_le _ _
    _ = s * |det2 u x| + t * |det2 u y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
    _ ≤ s * k + t * k := by gcongr
    _ = k := by rw [← add_mul, hst, one_mul]

lemma mm_convex_strips : Convex ℝ {x | mm_strips a b c x} :=
  (mm_convex_abs_det2_le _ _).inter ((mm_convex_abs_det2_le _ _).inter
    (mm_convex_abs_det2_le _ _))

/-- The hexagon lies in the three strips: they are convex and contain its vertices. -/
lemma mm_strips_of_mem (h : mm_HexCond a b c) (hx : x ∈ hexagonOf (mm_hex a b c)) :
    mm_strips a b c x := by
  refine convexHull_min (range_subset_iff.2 fun k ↦ ?_) mm_convex_strips hx
  obtain ⟨hA, hB, hC, h0, h1, h2⟩ := h
  simp only [det2] at hA hB hC h0 h1 h2
  simp only [mem_ofPred_eq, mm_strips, abs_le]
  rcases mm_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [mm_hex_zero, mm_hex_one, mm_hex_two, mm_hex_three, mm_hex_four,
      mm_hex_five, det2, Pi.sub_apply, Pi.neg_apply, Pi.add_apply] <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

/-- The vertices `v_j` of the hexagon `mm_hex a b c`, indexed by `Fin 6`. -/
def mm_us (a b c : Fin 2 → ℝ) : Fin 6 → Fin 2 → ℝ := ![a, b, c, -a, -b, -c]
/-- The vertices `v_{j+1}` of the hexagon `mm_hex a b c`, indexed by `Fin 6`. -/
def mm_ws (a b c : Fin 2 → ℝ) : Fin 6 → Fin 2 → ℝ := ![b, c, -a, -b, -c, a]
/-- The six triangles `[0, v_j, v_{j+1}]` into which the hexagon `mm_hex a b c` is cut. -/
noncomputable def mm_piece (a b c : Fin 2 → ℝ) (i : Fin 6) : Set (Fin 2 → ℝ) :=
  mm_tri (mm_us a b c i) (mm_ws a b c i)

/-- Every point of the three strips lies in one of the six triangles: the one whose angle at `0`
contains it. -/
lemma mm_exists_piece (h : mm_HexCond a b c) (hx : mm_strips a b c x) :
    ∃ i, x ∈ mm_piece a b c i := by
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
    · exact ⟨0, show x ∈ mm_tri a b from mm_mem_tri_of hA ha hb (by rw [es]; linarith)⟩
    · rcases le_or_gt (det2 c x) 0 with hc | hc
      · exact ⟨1, show x ∈ mm_tri b c from mm_mem_tri_of hB hb.le hc (by rw [es]; linarith)⟩
      · exact ⟨2, show x ∈ mm_tri c (-a) from mm_mem_tri_of (by rwa [eca]) hc.le
          (by rw [e]; linarith) (by rw [es, e, eca]; linarith)⟩
  · rcases le_or_gt 0 (det2 b x) with hb | hb
    · exact ⟨3, show x ∈ mm_tri (-a) (-b) from mm_mem_tri_of (by rwa [e, e', neg_neg])
        (by rw [e]; linarith) (by rw [e]; linarith) (by rw [es, e, e, e, e', neg_neg]; linarith)⟩
    · rcases le_or_gt 0 (det2 c x) with hc | hc
      · exact ⟨4, show x ∈ mm_tri (-b) (-c) from mm_mem_tri_of (by rwa [e, e', neg_neg])
          (by rw [e]; linarith) (by rw [e]; linarith)
          (by rw [es, e, e, e, e', neg_neg]; linarith)⟩
      · refine ⟨5, show x ∈ mm_tri (-c) a from mm_mem_tri_of
          (by rw [e, eac]; linarith) (by rw [e]; linarith) ha.le
          (by rw [es, e, e, eac]; linarith)⟩

lemma mm_vertex_mem (k : ZMod 6) : mm_hex a b c k ∈ hexagonOf (mm_hex a b c) :=
  subset_convexHull ℝ _ (mem_range_self k)

lemma mm_zero_mem_hex : (0 : Fin 2 → ℝ) ∈ hexagonOf (mm_hex a b c) := by
  have := convex_convexHull ℝ (range (mm_hex a b c)) (mm_vertex_mem 0) (mm_vertex_mem 3)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [mm_hex_zero, mm_hex_three, smul_neg, add_neg_cancel] at this
  exact this

lemma mm_piece_subset (i : Fin 6) : mm_piece a b c i ⊆ hexagonOf (mm_hex a b c) := by
  refine mm_tri_subset (convex_convexHull ℝ _) mm_zero_mem_hex ?_ ?_ <;>
    fin_cases i
  all_goals first
    | exact mm_vertex_mem 0 | exact mm_vertex_mem 1 | exact mm_vertex_mem 2
    | exact mm_vertex_mem 3 | exact mm_vertex_mem 4 | exact mm_vertex_mem 5

/-- The hexagon is the union of its six triangles `[0, v_j, v_{j+1}]`. -/
lemma mm_hexagonOf_eq (h : mm_HexCond a b c) :
    hexagonOf (mm_hex a b c) = ⋃ i, mm_piece a b c i := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mm_exists_piece h (mm_strips_of_mem h hx)
    exact mem_iUnion.2 ⟨i, hi⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    exact mm_piece_subset i hi

/-- The hexagon is the intersection of three strips. -/
lemma mm_mem_hexagonOf_iff (h : mm_HexCond a b c) :
    x ∈ hexagonOf (mm_hex a b c) ↔ mm_strips a b c x := by
  refine ⟨mm_strips_of_mem h, fun hx ↦ ?_⟩
  obtain ⟨i, hi⟩ := mm_exists_piece h hx
  exact mm_piece_subset i hi

/-- The signs of `det(a, x), det(b, x), det(c, x)` on the six triangles of the hexagon; they
differ for any two triangles. -/
lemma mm_piece_signs (h : mm_HexCond a b c) (i : Fin 6) (hx : x ∈ mm_piece a b c i) :
    0 ≤ (![1, 1, 1, -1, -1, -1] : Fin 6 → ℝ) i * det2 a x ∧
      0 ≤ (![-1, 1, 1, 1, -1, -1] : Fin 6 → ℝ) i * det2 b x ∧
      0 ≤ (![-1, -1, 1, 1, 1, -1] : Fin 6 → ℝ) i * det2 c x := by
  obtain ⟨hA, hB, hC, -, -, -⟩ := h
  simp only [det2] at hA hB hC
  refine ⟨mm_cone_sign hx ?_ ?_, mm_cone_sign hx ?_ ?_, mm_cone_sign hx ?_ ?_⟩ <;>
    fin_cases i <;> simp [mm_us, mm_ws, det2] <;> nlinarith

lemma mm_ne_zero_left (h : mm_HexCond a b c) : a ≠ 0 := by
  rintro rfl; have := h.hA; simp [det2] at this

lemma mm_ne_zero_mid (h : mm_HexCond a b c) : b ≠ 0 := by
  rintro rfl; have := h.hA; simp [det2] at this

lemma mm_ne_zero_right (h : mm_HexCond a b c) : c ≠ 0 := by
  rintro rfl; have := h.hB; simp [det2] at this

/-- Two triangles of the hexagon meet in a null set (in one of the lines `ℝa, ℝb, ℝc`). -/
lemma mm_piece_aedisjoint (h : mm_HexCond a b c) :
    Pairwise (Function.onFun (AEDisjoint volume) (mm_piece a b c)) := by
  have hN : volume ({x : Fin 2 → ℝ | det2 a x = 0} ∪ {x | det2 b x = 0} ∪
      {x | det2 c x = 0}) = 0 :=
    measure_union_null (measure_union_null (mm_volume_line (mm_ne_zero_left h))
      (mm_volume_line (mm_ne_zero_mid h))) (mm_volume_line (mm_ne_zero_right h))
  intro i j hij
  refine measure_mono_null (fun x hx ↦ ?_) hN
  have si := mm_piece_signs h i hx.1
  have sj := mm_piece_signs h j hx.2
  simp only [mem_union, mem_ofPred_eq]
  fin_cases i <;> fin_cases j <;> simp at hij si sj <;>
    first | (left; left; linarith) | (left; right; linarith) | (right; linarith)

/-- The area of the hexagon `mm_hex a b c` is `det(a, b) + det(b, c) + det(a, c)`. -/
lemma mm_volume_hex (h : mm_HexCond a b c) :
    volume (hexagonOf (mm_hex a b c)) = ENNReal.ofReal (det2 a b + det2 b c + det2 a c) := by
  rw [mm_hexagonOf_eq h, measure_iUnion₀ (mm_piece_aedisjoint h)
    (fun i ↦ (mm_isCompact_tri _ _).measurableSet.nullMeasurableSet), tsum_fintype]
  simp only [mm_piece, mm_volume_tri]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by positivity)]
  congr 1
  have e1 : det2 c (-a) = det2 a c := by simp [det2]; ring
  have e2 : det2 (-a) (-b) = det2 a b := by simp [det2]
  have e3 : det2 (-b) (-c) = det2 b c := by simp [det2]
  have e4 : det2 (-c) a = det2 a c := by simp [det2]; ring
  simp only [Fin.sum_univ_six, mm_us, mm_ws, Matrix.cons_val, e1, e2, e3, e4,
    abs_of_pos h.hA, abs_of_pos h.hB, abs_of_pos h.hC]
  ring

/-- The area of the hexagon `mm_hex a b c`, as a real number. -/
lemma mm_volume_real_hex (h : mm_HexCond a b c) :
    volume.real (hexagonOf (mm_hex a b c)) = det2 a b + det2 b c + det2 a c := by
  rw [measureReal_def, mm_volume_hex h, ENNReal.toReal_ofReal]
  linarith [h.hA, h.hB, h.hC]

end mm_Hex

/-- The area of a centrally symmetric hexagon is `4 det(m₀, m₁)`, where `m₀, m₁` are the midpoints
of two consecutive edges (§2.2: `det(s_j, s_{j+1})` is a fixed fraction of `area(H_K)`). -/
lemma mm_volume_hexagonOf {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
    volume.real (hexagonOf v) = 4 * det2 (hexMidpoint v 0) (hexMidpoint v 1) := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, v = mm_hex a b c := ⟨_, _, _, mm_eq_hex hv⟩
  rw [mm_volume_real_hex (mm_isCSHexagon_iff.1 hv)]
  simp only [hexMidpoint, zero_add, show (1 : ZMod 6) + 1 = 2 from rfl, mm_hex_zero,
    mm_hex_one, mm_hex_two, midpoint_eq_smul_add]
  simp only [det2, Pi.smul_apply, Pi.add_apply, smul_eq_mul, invOf_eq_inv]
  ring

/-! ### Edge lines of a centrally symmetric hexagon -/

section mm_edges

variable {v : ZMod 6 → Fin 2 → ℝ}

/-- The vector `a_j` of the line `{x | a_j · x = 1}` of the edge `[v_j, v_{j+1}]`. -/
noncomputable def mm_normal (v : ZMod 6 → Fin 2 → ℝ) (j : ZMod 6) : Fin 2 → ℝ :=
  (det2 (v j) (v (j + 1)))⁻¹ • ![(v (j + 1) - v j) 1, -(v (j + 1) - v j) 0]

lemma mm_normal_dot (v : ZMod 6 → Fin 2 → ℝ) (j : ZMod 6) (x : Fin 2 → ℝ) :
    mm_normal v j ⬝ᵥ x = det2 x (v (j + 1) - v j) / det2 (v j) (v (j + 1)) := by
  simp only [mm_normal, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, det2, Pi.sub_apply]
  ring

lemma mm_normal_dot_le_iff (hv : IsCSHexagon v) (j : ZMod 6) (x : Fin 2 → ℝ) :
    mm_normal v j ⬝ᵥ x ≤ 1 ↔ det2 x (v (j + 1) - v j) ≤ det2 (v j) (v (j + 1)) := by
  rw [mm_normal_dot, div_le_one (hv j).2.1]

/-- The hexagon is the intersection of the half-planes `a_j · x ≤ 1` of its edges. -/
lemma mm_polarHexagon_normal (hv : IsCSHexagon v) : polarHexagon (mm_normal v) = hexagonOf v := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, v = mm_hex a b c := ⟨_, _, _, mm_eq_hex hv⟩
  have h := mm_isCSHexagon_iff.1 hv
  obtain ⟨f01, f11, f21, f31, f41, f51, -⟩ := mm_zmod_facts
  ext x
  rw [mm_mem_hexagonOf_iff h, polarHexagon, mem_ofPred_eq]
  simp only [mm_normal_dot_le_iff hv]
  constructor
  · intro hx
    have e0 := hx 0
    have e1 := hx 1
    have e2 := hx 2
    have e3 := hx 3
    have e4 := hx 4
    have e5 := hx 5
    simp only [f01, f11, f21, f31, f41, f51, mm_hex_zero, mm_hex_one, mm_hex_two,
      mm_hex_three, mm_hex_four, mm_hex_five] at e0 e1 e2 e3 e4 e5
    simp only [mm_strips, abs_le]
    simp only [det2, Pi.sub_apply, Pi.neg_apply, Pi.add_apply] at *
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  · rintro ⟨s0, s1, s2⟩ j
    rw [abs_le] at s0 s1 s2
    simp only [det2, Pi.sub_apply, Pi.add_apply] at s0 s1 s2
    rcases mm_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [f01, f11, f21, f31, f41, f51, mm_hex_zero, mm_hex_one, mm_hex_two,
        mm_hex_three, mm_hex_four, mm_hex_five, det2, Pi.sub_apply, Pi.neg_apply] <;>
      linarith

lemma mm_normal_dot_le (hv : IsCSHexagon v) (j : ZMod 6) {x : Fin 2 → ℝ}
    (hx : x ∈ hexagonOf v) : mm_normal v j ⬝ᵥ x ≤ 1 := by
  rw [← mm_polarHexagon_normal hv] at hx
  exact hx j

lemma mm_normal_dot_self (hv : IsCSHexagon v) (j : ZMod 6) :
    mm_normal v j ⬝ᵥ v j = 1 ∧ mm_normal v j ⬝ᵥ v (j + 1) = 1 := by
  have h := (hv j).2.1
  rw [mm_normal_dot, mm_normal_dot]
  constructor <;> rw [div_eq_one_iff_eq h.ne'] <;> simp only [det2, Pi.sub_apply] <;> ring

lemma mm_normal_dot_midpoint (hv : IsCSHexagon v) (j : ZMod 6) :
    mm_normal v j ⬝ᵥ hexMidpoint v j = 1 := by
  obtain ⟨h1, h2⟩ := mm_normal_dot_self hv j
  rw [hexMidpoint, midpoint_eq_smul_add, dotProduct_smul, dotProduct_add, h1, h2]
  norm_num

lemma mm_normal_ne_zero (hv : IsCSHexagon v) (j : ZMod 6) : mm_normal v j ≠ 0 := by
  intro h
  have := (mm_normal_dot_self hv j).1
  rw [h, zero_dotProduct] at this
  exact zero_ne_one this

/-- A point `p` with `a · p = 1` is not interior to a set lying in the half-plane `a · x ≤ 1`. -/
lemma mm_not_mem_interior {S : Set (Fin 2 → ℝ)} {a p : Fin 2 → ℝ} (ha : a ≠ 0)
    (hS : ∀ x ∈ S, a ⬝ᵥ x ≤ 1) (hp : a ⬝ᵥ p = 1) : p ∉ interior S := by
  intro hint
  have hcont : Continuous fun t : ℝ ↦ p + t • a := by fun_prop
  have hev : ∀ᶠ t in nhds (0 : ℝ), p + t • a ∈ S := by
    have := hcont.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact (this.eventually (isOpen_interior.mem_nhds hint)).mono fun t ht ↦ interior_subset ht
  have hpos : 0 < a ⬝ᵥ a := by
    have : a ⬝ᵥ a = a 0 ^ 2 + a 1 ^ 2 := by simp [dotProduct, Fin.sum_univ_two]; ring
    rw [this]
    by_contra hle
    apply ha
    ext i; fin_cases i <;> simp <;> nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
  obtain ⟨t, ht, htpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ nhdsWithin 0 (Ioi 0))).exists
  have := hS _ ht
  rw [dotProduct_add, dotProduct_smul, hp, smul_eq_mul] at this
  have htpos' : 0 < t := htpos
  nlinarith

/-- Two lines `{a · x = 1}`, `{b · x = 1}` that coincide have `a = b`. -/
lemma mm_eq_of_line_subset {a b : Fin 2 → ℝ} (ha : a ≠ 0)
    (h : {x : Fin 2 → ℝ | a ⬝ᵥ x = 1} ⊆ {x | b ⬝ᵥ x = 1}) : b = a := by
  have hN : 0 < a 0 ^ 2 + a 1 ^ 2 := by
    by_contra hle
    apply ha
    ext i; fin_cases i <;> simp <;> nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
  have hN' := hN.ne'
  have hp : a ⬝ᵥ ![a 0 / (a 0 ^ 2 + a 1 ^ 2), a 1 / (a 0 ^ 2 + a 1 ^ 2)] = 1 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
  have hq : a ⬝ᵥ ![a 0 / (a 0 ^ 2 + a 1 ^ 2) - a 1, a 1 / (a 0 ^ 2 + a 1 ^ 2) + a 0] = 1 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  have hbp : b ⬝ᵥ _ = 1 := h hp
  have hbq : b ⬝ᵥ _ = 1 := h hq
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hbp hbq
  have e1 : b 0 * a 0 + b 1 * a 1 = a 0 ^ 2 + a 1 ^ 2 := by
    field_simp at hbp
    linarith
  have e2 : b 1 * a 0 - b 0 * a 1 = 0 := by linarith
  have h0 : b 0 = a 0 := by
    apply mul_right_cancel₀ hN'
    linear_combination a 0 * e1 - a 1 * e2
  have h1 : b 1 = a 1 := by
    apply mul_right_cancel₀ hN'
    linear_combination a 1 * e1 + a 0 * e2
  ext i; fin_cases i
  · exact h0
  · exact h1

lemma mm_eq_of_line_eq {a b : Fin 2 → ℝ}
    (h : {x : Fin 2 → ℝ | a ⬝ᵥ x = 1} = {x | b ⬝ᵥ x = 1}) : a = b := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · rw [ha, hb]
    · exact (mm_eq_of_line_subset hb h.symm.subset)
  · exact (mm_eq_of_line_subset ha h.subset).symm

end mm_edges

/-! ### Least-area hexagons -/

section mm_least

variable {K : Set (Fin 2 → ℝ)} {v : ZMod 6 → Fin 2 → ℝ}

lemma mm_det2_comb (α β γ δ : ℝ) (u w : Fin 2 → ℝ) :
    det2 (α • u + β • w) (γ • u + δ • w) = (α * δ - β * γ) * det2 u w := by
  simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- Cramer: a vector `y` with `det(y, e₁) = det(y, e₂) = 0` for independent `e₁, e₂` is `0`. -/
lemma mm_eq_zero_of_det2 {y e₁ e₂ : Fin 2 → ℝ} (h : det2 e₁ e₂ ≠ 0) (h1 : det2 y e₁ = 0)
    (h2 : det2 y e₂ = 0) : y = 0 := by
  simp only [det2] at h h1 h2
  ext i; fin_cases i
  · have : y 0 * (e₁ 0 * e₂ 1 - e₁ 1 * e₂ 0) = 0 := by
      linear_combination e₁ 0 * h2 - e₂ 0 * h1
    simpa using (mul_eq_zero.1 this).resolve_right h
  · have : y 1 * (e₁ 0 * e₂ 1 - e₁ 1 * e₂ 0) = 0 := by
      linear_combination e₁ 1 * h2 - e₂ 1 * h1
    simpa using (mul_eq_zero.1 this).resolve_right h

/-- Two vectors on a line `ℝ p` through the origin have `det(x, y) = 0`. -/
lemma mm_det2_eq_zero_of_parallel {p x y : Fin 2 → ℝ} (hp : p ≠ 0) (hx : det2 p x = 0)
    (hy : det2 p y = 0) : det2 x y = 0 := by
  simp only [det2] at hx hy ⊢
  by_cases h0 : p 0 = 0
  · have h1 : p 1 ≠ 0 := by
      intro h1; apply hp; ext i; fin_cases i <;> simp [h0, h1]
    have : p 1 * (x 0 * y 1 - x 1 * y 0) = 0 := by linear_combination x 1 * hy - y 1 * hx
    exact (mul_eq_zero.1 this).resolve_left h1
  · have : p 0 * (x 0 * y 1 - x 1 * y 0) = 0 := by linear_combination x 0 * hy - y 0 * hx
    exact (mul_eq_zero.1 this).resolve_left h0

/-- The edge midpoints of a centrally symmetric hexagon are centrally symmetric. -/
lemma mm_hexMidpoint_add_three (hv : IsCSHexagon v) (j : ZMod 6) :
    hexMidpoint v (j + 3) = -hexMidpoint v j := by
  have h1 := (hv j).1
  have h2 := (hv (j + 1)).1
  simp only [hexMidpoint, show j + 3 + 1 = j + 1 + 3 by ring, h1, h2, midpoint_eq_smul_add]
  rw [← neg_add, smul_neg]

/-- The edge midpoints of a least-area circumscribed hexagon lie on the boundary of `K`: they lie
in `K` (Remark 2.2.4, Reinhardt) and on the edges of the hexagon. -/
lemma mm_hexMidpoint_mem_frontier (hK : IsCCSDisk K) (hv : IsLeastAreaHexagon K v)
    (j : ZMod 6) : hexMidpoint v j ∈ frontier K := by
  obtain ⟨ε, hε, h⟩ := remark2_2_4 hK hv j
  have hmem : hexMidpoint v j ∈ K := h _ (by simpa using hε) rfl
  rw [hK.2.1.isClosed.frontier_eq]
  exact ⟨hmem, mm_not_mem_interior (mm_normal_ne_zero hv.1 j)
    (fun x hx ↦ mm_normal_dot_le hv.1 j (hv.2.1 hx)) (mm_normal_dot_midpoint hv.1 j)⟩

/-- The line of an edge of a least-area circumscribed hexagon is a support line of `K` at the
midpoint of the edge. -/
lemma mm_isSupportLine_normal (hK : IsCCSDisk K) (hv : IsLeastAreaHexagon K v) (j : ZMod 6) :
    IsSupportLine K {x | mm_normal v j ⬝ᵥ x = 1} := by
  refine ⟨⟨mm_normal v j, mm_normal_ne_zero hv.1 j, 1, rfl, fun x hx y hy ↦ ?_⟩,
    ⟨hexMidpoint v j, mm_normal_dot_midpoint hv.1 j, ?_⟩⟩
  · have h1 := mm_normal_dot_le hv.1 j (hv.2.1 hx)
    have h2 := mm_normal_dot_le hv.1 j (hv.2.1 hy)
    nlinarith
  · exact External.MinkowskiMahler.mm_mem_of_frontier hK (mm_hexMidpoint_mem_frontier hK hv j)

lemma mm_volume_real_pos (hK : IsCCSDisk K) : 0 < volume.real K :=
  ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior _ hK.2.2.1).ne'
    hK.2.1.measure_lt_top.ne

lemma mm_isCompact_hexagonOf (v : ZMod 6 → Fin 2 → ℝ) : IsCompact (hexagonOf v) :=
  (Set.finite_range v).isCompact_convexHull (𝕜 := ℝ)

/-- The comparison of Theorem 2.3.9 (`area(H_K) ≤ 4 det(L)` for every admissible lattice `L`),
from the density formula of Theorem 2.2.2 and Theorem 2.1.3: `L` is `K`-admissible, so `2L` gives
a lattice packing of `K` (the remark after Definition 2.3.1), of density
`area(K)/det(2L) ≤ δ_L(K) = δ(K) = area(K)/area(H_K)`. -/
lemma mm_volume_le (hK : IsCCSDisk K) (hpar : ¬ IsParallelogram K) (hv : IsLeastAreaHexagon K v)
    {L : Submodule ℤ (Fin 2 → ℝ)} (hL : IsPlaneLattice L) (hadm : IsAdmissible K L) :
    volume.real (hexagonOf v) ≤ 4 * latticeDet L := by
  obtain ⟨a, b, hab, hc⟩ := External.MinkowskiMahler.mm_exists_basis hL
  have hdetL : latticeDet L = |det2 a b| := definition2_3_2 hL hab
  have e2 : det2 ((2 : ℝ) • a) ((2 : ℝ) • b) = 4 * det2 a b := by
    simp only [det2, Pi.smul_apply, smul_eq_mul]; ring
  have hc2 : det2 ((2 : ℝ) • a) ((2 : ℝ) • b) ≠ 0 := by
    rw [e2]; exact mul_ne_zero (by norm_num) hc
  set L₂ := latticeSpan ((2 : ℝ) • a) ((2 : ℝ) • b) with hL₂def
  have hL₂ : IsPlaneLattice L₂ := External.MinkowskiMahler.mm_isLattice_span hc2
  have hdet₂ : latticeDet L₂ = 4 * latticeDet L := by
    rw [hdetL, show latticeDet L₂ = |det2 ((2 : ℝ) • a) ((2 : ℝ) • b)| from
      External.MinkowskiMahler.mm_det_span hc2, e2, abs_mul]
    norm_num
  have hpack : IsLatticePacking K L₂ := by
    intro l hl l' hl' hne
    have i1 : interior ((fun x ↦ x + l) '' K) = (fun x ↦ x + l) '' interior K :=
      ((Homeomorph.addRight l).image_interior K).symm
    have i2 : interior ((fun x ↦ x + l') '' K) = (fun x ↦ x + l') '' interior K :=
      ((Homeomorph.addRight l').image_interior K).symm
    rw [i1, i2, Set.disjoint_left]
    rintro z ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
    apply hne
    obtain ⟨m, n, hmn⟩ := External.MinkowskiMahler.mm_mem_span_pair.1 (L₂.sub_mem hl' hl)
    have hhalf : (1 / 2 : ℝ) • (l' - l) ∈ interior K := by
      have hq' := External.MinkowskiMahler.mm_neg_mem_interior hK hq
      have := hK.1.interior hp hq' (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      convert this using 1
      have : l' - l = p - q := by
        simp only at hpq
        ext i
        have := congrFun hpq i
        simp only [Pi.add_apply] at this
        simp only [Pi.sub_apply]
        linarith
      rw [this]; module
    have hmem : (1 / 2 : ℝ) • (l' - l) ∈ L := by
      rw [← hmn, ← hab.2]
      exact External.MinkowskiMahler.mm_mem_span_pair.2 ⟨m, n, by module⟩
    have h0 := hadm _ hmem hhalf
    have : l' - l = 0 := by
      have := congrArg ((2 : ℝ) • ·) h0
      simpa [smul_smul] using this
    exact (sub_eq_zero.1 this).symm
  have hKpos := mm_volume_real_pos hK
  have hHpos : 0 < volume.real (hexagonOf v) :=
    hKpos.trans_le (measureReal_mono hv.2.1 (mm_isCompact_hexagonOf v).measure_lt_top.ne)
  have hδ := (theorem2_2_2 hK hpar).2 v hv
  have hFT := theorem2_1_3 hK
  have hbdd : BddAbove
      {d | ∃ L, IsPlaneLattice L ∧ IsLatticePacking K L ∧ latticePackingDensity K L = d} := by
    by_contra hnb
    have h0 : greatestLatticePackingDensity K = 0 := by
      rw [greatestLatticePackingDensity, csSup_of_not_bddAbove hnb, Real.sSup_empty]
    rw [← hFT, hδ] at h0
    exact (div_pos hKpos hHpos).ne' h0
  have hle : latticePackingDensity K L₂ ≤ greatestLatticePackingDensity K :=
    le_csSup hbdd ⟨L₂, hL₂, hpack, rfl⟩
  have hLpos : 0 < latticeDet L := by
    rw [hdetL]; exact abs_pos.2 hc
  rw [ch2_latticePackingDensity_eq ⟨hK.1, hK.2.1, hK.2.2.1⟩ hL₂ hpack, ← hFT, hδ, hdet₂,
    div_le_div_iff_of_pos_left hKpos (by positivity) hHpos] at hle
  exact hle

/-- A vertex `v_j` is the only point of the hexagon on both lines of the edges at `v_j`. -/
lemma mm_eq_vertex (hv : IsCSHexagon v) (j : ZMod 6) {x : Fin 2 → ℝ}
    (h1 : mm_normal v (j - 1) ⬝ᵥ x = 1) (h2 : mm_normal v j ⬝ᵥ x = 1) : x = v j := by
  have hj : j - 1 + 1 = j := by ring
  have hj2 : j - 1 + 2 = j + 1 := by ring
  have hturn := (hv (j - 1)).2.2
  rw [hj, hj2] at hturn
  have hD1 := (hv (j - 1)).2.1
  have hD2 := (hv j).2.1
  rw [hj] at hD1
  rw [mm_normal_dot, hj, div_eq_one_iff_eq hD1.ne'] at h1
  rw [mm_normal_dot, div_eq_one_iff_eq hD2.ne'] at h2
  have := mm_eq_zero_of_det2 (y := x - v j) hturn.ne'
    (by simp only [det2, Pi.sub_apply] at h1 ⊢; linarith)
    (by simp only [det2, Pi.sub_apply] at h2 ⊢; linarith)
  exact sub_eq_zero.1 this

/-- **`K` is not a parallelogram.** Definition 2.3.8 (as formalized) requires it; the book's proof
of Theorem 2.3.9 uses it implicitly when it applies Theorem 2.3.7. A centrally symmetric
parallelogram `K = {s u + t w | |s|, |t| ≤ 1}` lies in the hexagons with vertices
`r(u - w), r u + w, u + r w, …` (`r > 1`) of area `(3r² + 2r - 1) det(u, w) → area(K)`, so a
least-area hexagon `H_K` has `area(H_K) ≤ area(K)` and hence `H_K = K`; but each vertex `v_j` of
`H_K` is the only maximum point on `H_K` of `(a_{j-1} + a_j) · x`, so it is a vertex `±u ± w` of
the parallelogram, and three consecutive vertices `v₀, v₁, v₂` cannot lie on the two diagonals
`ℝ(u + w)`, `ℝ(u - w)` with `det(v₀, v₁), det(v₁, v₂), det(v₀, v₂) > 0`. -/
lemma mm_not_isParallelogram (hK : IsCCSDisk K) (hv : IsLeastAreaHexagon K v) :
    ¬ IsParallelogram K := by
  rintro ⟨c, u₀, w₀, huw₀, hKeq⟩
  have hmem₀ : ∀ x, x ∈ K ↔ ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = c + s • u₀ + t • w₀ :=
    fun x ↦ by rw [hKeq]; rfl
  -- the center is the origin
  have hc : c = 0 := by
    obtain ⟨s₁, t₁, hs₁, ht₁, e₁⟩ := (hmem₀ _).1 (hK.2.2.2 _ ((hmem₀ (c + u₀ + w₀)).2
      ⟨1, 1, by norm_num, by norm_num, by simp⟩))
    obtain ⟨s₂, t₂, hs₂, ht₂, e₂⟩ := (hmem₀ _).1 (hK.2.2.2 _ ((hmem₀ (c - u₀ - w₀)).2
      ⟨-1, -1, by norm_num, by norm_num, by simp; abel⟩))
    have h0 : (s₁ - s₂ + 2) * u₀ 0 + (t₁ - t₂ + 2) * w₀ 0 = 0 := by
      have a := congrFun e₁ 0
      have b := congrFun e₂ 0
      simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b
      linarith
    have h1 : (s₁ - s₂ + 2) * u₀ 1 + (t₁ - t₂ + 2) * w₀ 1 = 0 := by
      have a := congrFun e₁ 1
      have b := congrFun e₂ 1
      simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b
      linarith
    simp only [det2] at huw₀
    have z0 : (s₁ - s₂ + 2) * (u₀ 0 * w₀ 1 - u₀ 1 * w₀ 0) = 0 := by
      linear_combination w₀ 1 * h0 - w₀ 0 * h1
    have z1 : (t₁ - t₂ + 2) * (u₀ 0 * w₀ 1 - u₀ 1 * w₀ 0) = 0 := by
      linear_combination u₀ 0 * h1 - u₀ 1 * h0
    have z0' := (mul_eq_zero.1 z0).resolve_right huw₀
    have z1' := (mul_eq_zero.1 z1).resolve_right huw₀
    rw [abs_le] at hs₁ ht₁ hs₂ ht₂
    have hs : s₁ = -1 := by linarith
    have ht : t₁ = -1 := by linarith
    rw [hs, ht] at e₁
    ext i
    have := congrFun e₁ i
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Pi.zero_apply]
    linarith
  subst hc
  -- an oriented basis
  obtain ⟨u, w, hD, hmem⟩ : ∃ u w : Fin 2 → ℝ, 0 < det2 u w ∧
      ∀ x, x ∈ K ↔ ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • u + t • w := by
    rcases lt_or_gt_of_ne huw₀ with h | h
    · refine ⟨u₀, -w₀, by simp only [det2, Pi.neg_apply] at h ⊢; linarith, fun x ↦ ?_⟩
      rw [hmem₀]
      constructor
      · rintro ⟨s, t, hs, ht, rfl⟩; exact ⟨s, -t, hs, by rwa [abs_neg], by simp⟩
      · rintro ⟨s, t, hs, ht, rfl⟩; exact ⟨s, -t, hs, by rwa [abs_neg], by simp⟩
    · refine ⟨u₀, w₀, h, fun x ↦ ?_⟩
      rw [hmem₀]
      simp
  set D := det2 u w with hDdef
  have hHfin : volume (hexagonOf v) ≠ ⊤ := (mm_isCompact_hexagonOf v).measure_lt_top.ne
  -- the comparison hexagons
  have hcomp : ∀ r : ℝ, 1 < r → volume.real (hexagonOf v) ≤ (3 * r ^ 2 + 2 * r - 1) * D := by
    intro r hr
    have dAB : det2 (r • u + (-r) • w) (r • u + (1 : ℝ) • w) = (r + r ^ 2) * D := by
      rw [mm_det2_comb]; ring
    have dBC : det2 (r • u + (1 : ℝ) • w) ((1 : ℝ) • u + r • w) = (r ^ 2 - 1) * D := by
      rw [mm_det2_comb]; ring
    have dAC : det2 (r • u + (-r) • w) ((1 : ℝ) • u + r • w) = (r ^ 2 + r) * D := by
      rw [mm_det2_comb]; ring
    have hr2 : 0 < r ^ 2 - 1 := by nlinarith
    have hcond : mm_HexCond (r • u + (-r) • w) (r • u + (1 : ℝ) • w) ((1 : ℝ) • u + r • w) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [dAB, dBC, dAC] <;> nlinarith
    have hsub : K ⊆ hexagonOf (mm_hex (r • u + (-r) • w) (r • u + (1 : ℝ) • w)
        ((1 : ℝ) • u + r • w)) := by
      intro x hx
      obtain ⟨s, t, hs, ht, rfl⟩ := (hmem x).1 hx
      rw [mm_mem_hexagonOf_iff hcond]
      rw [abs_le] at hs ht
      have eAB : r • u + (-r) • w - (r • u + (1 : ℝ) • w) = (0 : ℝ) • u + (-r - 1) • w := by
        module
      have eBC : r • u + (1 : ℝ) • w - ((1 : ℝ) • u + r • w) = (r - 1) • u + (1 - r) • w := by
        module
      have eCA : (1 : ℝ) • u + r • w + (r • u + (-r) • w) = (1 + r) • u + (0 : ℝ) • w := by
        module
      have hr1 : 0 ≤ r + 1 := by linarith
      have hr1' : 0 ≤ r - 1 := by linarith
      refine ⟨?_, ?_, ?_⟩
      · rw [eAB, mm_det2_comb, dAB, ← hDdef, abs_le]
        constructor
        · nlinarith [mul_nonneg (mul_nonneg hr1 hD.le) (show 0 ≤ s + r by linarith)]
        · nlinarith [mul_nonneg (mul_nonneg hr1 hD.le) (show 0 ≤ r - s by linarith)]
      · rw [eBC, mm_det2_comb, dBC, ← hDdef, abs_le]
        constructor
        · nlinarith [mul_nonneg (mul_nonneg hr1' hD.le) (show 0 ≤ s + t + r + 1 by linarith)]
        · nlinarith [mul_nonneg (mul_nonneg hr1' hD.le) (show 0 ≤ r + 1 - s - t by linarith)]
      · rw [eCA, mm_det2_comb, dAC, ← hDdef, abs_le]
        constructor
        · nlinarith [mul_nonneg (mul_nonneg hr1 hD.le) (show 0 ≤ t + r by linarith)]
        · nlinarith [mul_nonneg (mul_nonneg hr1 hD.le) (show 0 ≤ r - t by linarith)]
    have hle := hv.2.2 _ (mm_isCSHexagon_iff.2 hcond) hsub
    have hfin : volume (hexagonOf (mm_hex (r • u + (-r) • w) (r • u + (1 : ℝ) • w)
        ((1 : ℝ) • u + r • w))) ≠ ⊤ := (mm_isCompact_hexagonOf _).measure_lt_top.ne
    have := ENNReal.toReal_mono hfin hle
    rw [← measureReal_def, ← measureReal_def, mm_volume_real_hex hcond, dAB, dBC, dAC] at this
    linarith
  -- the area of `K`
  have hKimg : K = mm_lin u w '' Icc (-1) 1 := by
    ext x
    rw [hmem]
    constructor
    · rintro ⟨s, t, hs, ht, rfl⟩
      rw [abs_le] at hs ht
      refine ⟨![s, t], ⟨fun i ↦ ?_, fun i ↦ ?_⟩, by rw [mm_lin_apply]; simp⟩ <;>
        fin_cases i <;> simp <;> linarith
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p 0, p 1, abs_le.2 ⟨hp.1 0, hp.2 0⟩, abs_le.2 ⟨hp.1 1, hp.2 1⟩, mm_lin_apply _ _ _⟩
  have hvolK : volume.real K = 4 * D := by
    rw [hKimg, measureReal_def, Measure.addHaar_image_linearMap, mm_det_lin, Real.volume_Icc_pi]
    simp only [Fin.prod_univ_two, Pi.one_apply, Pi.neg_apply]
    rw [← hDdef, abs_of_pos hD, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul hD.le, ENNReal.toReal_ofReal (by positivity)]
    ring
  -- hence `area(H_K) ≤ area(K)`
  have hHK : volume.real (hexagonOf v) ≤ volume.real K := by
    rw [hvolK]
    by_contra hlt
    push Not at hlt
    set δ := volume.real (hexagonOf v) - 4 * D
    have hδ : 0 < δ := by simp only [δ]; linarith
    set r := 1 + min 1 (δ / (12 * D))
    have hm1 : min 1 (δ / (12 * D)) ≤ 1 := min_le_left _ _
    have hm2 : min 1 (δ / (12 * D)) ≤ δ / (12 * D) := min_le_right _ _
    have hm0 : 0 < min 1 (δ / (12 * D)) := lt_min one_pos (by positivity)
    have hm3 : min 1 (δ / (12 * D)) * (12 * D) ≤ δ := by
      rwa [le_div_iff₀ (by positivity)] at hm2
    have := hcomp r (by simp only [r]; linarith)
    simp only [r] at this
    nlinarith
  -- so `H_K = K`
  have hHsubK : hexagonOf v ⊆ K := by
    intro x hx
    by_contra hxK
    have hintH : (interior (hexagonOf v)).Nonempty :=
      hK.2.2.1.mono (interior_mono hv.2.1)
    have hcl : x ∈ closure (interior (hexagonOf v)) := by
      have hconv : Convex ℝ (hexagonOf v) := convex_convexHull ℝ _
      rw [hconv.closure_interior_eq_closure_of_nonempty_interior hintH]
      exact subset_closure hx
    obtain ⟨y, hyK, hyH⟩ := mem_closure_iff.1 hcl _ hK.2.1.isClosed.isOpen_compl hxK
    set U := Kᶜ ∩ interior (hexagonOf v)
    have hUpos : 0 < volume U :=
      (hK.2.1.isClosed.isOpen_compl.inter isOpen_interior).measure_pos volume ⟨y, hyK, hyH⟩
    have hsub : K ∪ U ⊆ hexagonOf v := union_subset hv.2.1 fun z hz ↦ interior_subset hz.2
    have hU : volume K + volume U ≤ volume (hexagonOf v) := by
      rw [← measure_union (disjoint_compl_right.mono_right inter_subset_left)
        (hK.2.1.isClosed.isOpen_compl.inter isOpen_interior).measurableSet]
      exact measure_mono hsub
    have hKfin : volume K ≠ ⊤ := hK.2.1.measure_lt_top.ne
    have hHK' : volume (hexagonOf v) ≤ volume K := by
      rw [← ENNReal.ofReal_toReal hHfin, ← ENNReal.ofReal_toReal hKfin]
      exact ENNReal.ofReal_le_ofReal hHK
    have : volume K + volume U ≤ volume K + 0 := by rw [add_zero]; exact hU.trans hHK'
    exact hUpos.ne' (le_antisymm ((ENNReal.add_le_add_iff_left hKfin).1 this) bot_le)
  -- every vertex of `H_K` is a vertex `±u ± w` of `K`
  have hp0 : u + w ≠ 0 := by
    intro h
    have hw : w = -u := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h
    have := hD
    rw [hDdef, hw] at this
    simp only [det2, Pi.neg_apply] at this
    nlinarith
  have hq0 : u - w ≠ 0 := by
    intro h
    have hw : w = u := (sub_eq_zero.1 h).symm
    have := hD
    rw [hDdef, hw] at this
    simp only [det2] at this
    nlinarith
  have hcorner : ∀ j, det2 (u + w) (v j) = 0 ∨ det2 (u - w) (v j) = 0 := by
    intro j
    set ψ := mm_normal v (j - 1) + mm_normal v j
    have hψH : ∀ x ∈ hexagonOf v, ψ ⬝ᵥ x ≤ 2 := fun x hx ↦ by
      rw [add_dotProduct]
      linarith [mm_normal_dot_le hv.1 (j - 1) hx, mm_normal_dot_le hv.1 j hx]
    have hvj : ψ ⬝ᵥ v j = 2 := by
      have h1 := (mm_normal_dot_self hv.1 (j - 1)).2
      rw [show j - 1 + 1 = j by ring] at h1
      rw [add_dotProduct, h1, (mm_normal_dot_self hv.1 j).1]; norm_num
    obtain ⟨s, t, hs, ht, hst⟩ := (hmem (v j)).1 (hHsubK (subset_convexHull ℝ _ (mem_range_self j)))
    set σ : ℝ := if 0 ≤ ψ ⬝ᵥ u then 1 else -1 with hσdef
    set τ : ℝ := if 0 ≤ ψ ⬝ᵥ w then 1 else -1 with hτdef
    have hσ : σ * (ψ ⬝ᵥ u) = |ψ ⬝ᵥ u| ∧ (σ = 1 ∨ σ = -1) := by
      by_cases h : 0 ≤ ψ ⬝ᵥ u
      · have e : σ = 1 := by simp only [hσdef, h, ↓reduceIte]
        rw [e, one_mul, abs_of_nonneg h]; exact ⟨rfl, Or.inl rfl⟩
      · have e : σ = -1 := by simp only [hσdef, h, ↓reduceIte]
        rw [e, neg_one_mul, abs_of_neg (not_le.1 h)]; exact ⟨rfl, Or.inr rfl⟩
    have hτ : τ * (ψ ⬝ᵥ w) = |ψ ⬝ᵥ w| ∧ (τ = 1 ∨ τ = -1) := by
      by_cases h : 0 ≤ ψ ⬝ᵥ w
      · have e : τ = 1 := by simp only [hτdef, h, ↓reduceIte]
        rw [e, one_mul, abs_of_nonneg h]; exact ⟨rfl, Or.inl rfl⟩
      · have e : τ = -1 := by simp only [hτdef, h, ↓reduceIte]
        rw [e, neg_one_mul, abs_of_neg (not_le.1 h)]; exact ⟨rfl, Or.inr rfl⟩
    have hcK : σ • u + τ • w ∈ K := (hmem _).2 ⟨σ, τ, by rcases hσ.2 with h | h <;> simp [h],
      by rcases hτ.2 with h | h <;> simp [h], rfl⟩
    have h1 : ψ ⬝ᵥ (σ • u + τ • w) = |ψ ⬝ᵥ u| + |ψ ⬝ᵥ w| := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hσ.1, hτ.1]
    have h2 : ψ ⬝ᵥ v j ≤ |ψ ⬝ᵥ u| + |ψ ⬝ᵥ w| := by
      rw [hst, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      have a1 : s * (ψ ⬝ᵥ u) ≤ |ψ ⬝ᵥ u| := by
        calc s * (ψ ⬝ᵥ u) ≤ |s * (ψ ⬝ᵥ u)| := le_abs_self _
          _ = |s| * |ψ ⬝ᵥ u| := abs_mul _ _
          _ ≤ 1 * |ψ ⬝ᵥ u| := by gcongr
          _ = _ := one_mul _
      have a2 : t * (ψ ⬝ᵥ w) ≤ |ψ ⬝ᵥ w| := by
        calc t * (ψ ⬝ᵥ w) ≤ |t * (ψ ⬝ᵥ w)| := le_abs_self _
          _ = |t| * |ψ ⬝ᵥ w| := abs_mul _ _
          _ ≤ 1 * |ψ ⬝ᵥ w| := by gcongr
          _ = _ := one_mul _
      linarith
    have h3 := hψH _ (hv.2.1 hcK)
    have heq : σ • u + τ • w = v j := by
      have hψ2 : ψ ⬝ᵥ (σ • u + τ • w) = 2 := by linarith
      rw [add_dotProduct] at hψ2
      have := mm_normal_dot_le hv.1 (j - 1) (hv.2.1 hcK)
      have := mm_normal_dot_le hv.1 j (hv.2.1 hcK)
      exact mm_eq_vertex hv.1 j (by linarith) (by linarith)
    rw [← heq]
    rcases hσ.2 with h | h <;> rcases hτ.2 with h' | h' <;> rw [h, h'] <;>
      simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
      first | (left; ring1) | (right; ring1)
  -- three consecutive vertices cannot lie on the two diagonals
  have hA := (hv.1 0).2.1
  have hB := (hv.1 1).2.1
  have hC := (hv.1 2).2.1
  have h3 : v 3 = -v 0 := (hv.1 0).1
  rw [show (0 : ZMod 6) + 1 = 1 from rfl] at hA
  rw [show (1 : ZMod 6) + 1 = 2 from rfl] at hB
  rw [show (2 : ZMod 6) + 1 = 3 from rfl, h3] at hC
  have hC' : 0 < det2 (v 0) (v 2) := by simp only [det2, Pi.neg_apply] at hC ⊢; linarith
  rcases hcorner 0 with h0 | h0 <;> rcases hcorner 1 with h1 | h1 <;>
    rcases hcorner 2 with h2 | h2
  · exact hA.ne' (mm_det2_eq_zero_of_parallel hp0 h0 h1)
  · exact hA.ne' (mm_det2_eq_zero_of_parallel hp0 h0 h1)
  · exact hC'.ne' (mm_det2_eq_zero_of_parallel hp0 h0 h2)
  · exact hB.ne' (mm_det2_eq_zero_of_parallel hq0 h1 h2)
  · exact hB.ne' (mm_det2_eq_zero_of_parallel hp0 h1 h2)
  · exact hC'.ne' (mm_det2_eq_zero_of_parallel hq0 h0 h2)
  · exact hA.ne' (mm_det2_eq_zero_of_parallel hq0 h0 h1)
  · exact hA.ne' (mm_det2_eq_zero_of_parallel hq0 h0 h1)

/-- **The proof of Theorem 2.3.9.** For a least-area centrally symmetric hexagon `H_K` around
`K`, with edge midpoints `s_j`: `K` is not a parallelogram, the `s_j` lie on the boundary of `K`
and satisfy the multi-point conditions, and the lattice `L` generated by `s₀, s₁` is a critical
lattice of `K` containing all the `s_j`. -/
lemma mm_leastArea_critical (hK : IsCCSDisk K) (hv : IsLeastAreaHexagon K v) :
    ¬ IsParallelogram K ∧
      IsCriticalLattice K (latticeSpan (hexMidpoint v 0) (hexMidpoint v 1)) ∧
      (∀ j, hexMidpoint v j ∈ latticeSpan (hexMidpoint v 0) (hexMidpoint v 1) ∧
        hexMidpoint v j ∈ frontier K) ∧
      hexMidpoint v 0 - hexMidpoint v 1 + hexMidpoint v 2 = 0 ∧
      ∀ j, hexMidpoint v (j + 3) = -hexMidpoint v j := by
  have hpar := mm_not_isParallelogram hK hv
  set s := hexMidpoint v with hs
  have hsymm : ∀ j, s (j + 3) = -s j := mm_hexMidpoint_add_three hv.1
  have hsub : s 1 - s 0 = s 2 := mm_hexMidpoint_sub hv.1
  have h012 : s 0 - s 1 + s 2 = 0 := by rw [← hsub]; abel
  have h1 : s 1 = s 0 + s 2 := by rw [← hsub]; abel
  have hfr : ∀ j, s j ∈ frontier K := mm_hexMidpoint_mem_frontier hK hv
  -- Theorem 2.3.6 (converse part): `Δ(K) ≤ |det(s₀, s₁)|`, with equality iff `L` is critical
  have h236 := (theorem2_3_6 hK).2 (s 0) (s 1) (s 2) (hfr 0) (hfr 1) (hfr 2) h1
  -- `L` is admissible (Mahler's Lemma 1)
  have hadm : IsAdmissible K (latticeSpan (s 0) (s 1)) := by
    have := External.MinkowskiMahler.mm_isAdmissible hK (hfr 0) (hfr 2) (by rw [← h1]; exact hfr 1)
    rwa [← h1] at this
  have hpos : 0 < det2 (s 0) (s 1) := mm_det2_hexMidpoint_pos hv.1
  have hlat : IsPlaneLattice (latticeSpan (s 0) (s 1)) :=
    External.MinkowskiMahler.mm_isLattice_span hpos.ne'
  -- `area(H_K) = 4 |det(s₀, s₁)| = det(2L)`, and `area(H_K) ≤ 4 det(L')` for admissible `L'`
  have harea : volume.real (hexagonOf v) = 4 * det2 (s 0) (s 1) := mm_volume_hexagonOf hv.1
  have hle : |det2 (s 0) (s 1)| ≤ minDeterminant K := by
    unfold minDeterminant
    refine le_csInf ⟨_, latticeSpan (s 0) (s 1), hlat, hadm, rfl⟩ ?_
    rintro d ⟨L', hL', hadm', rfl⟩
    have := mm_volume_le hK hpar hv hL' hadm'
    rw [abs_of_pos hpos]
    linarith
  have hcrit := h236.2.1 (le_antisymm hle h236.1)
  refine ⟨hpar, hcrit, fun j ↦ ⟨?_, hfr j⟩, h012, hsymm⟩
  have m0 : s 0 ∈ latticeSpan (s 0) (s 1) := Submodule.subset_span (by simp)
  have m1 : s 1 ∈ latticeSpan (s 0) (s 1) := Submodule.subset_span (by simp)
  have m2 : s 2 ∈ latticeSpan (s 0) (s 1) := by
    rw [← hsub]; exact Submodule.sub_mem _ m1 m0
  rcases mm_cases j with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m0
  · exact m1
  · exact m2
  · rw [show (3 : ZMod 6) = 0 + 3 from rfl, hsymm]; exact Submodule.neg_mem _ m0
  · rw [show (4 : ZMod 6) = 1 + 3 from rfl, hsymm]; exact Submodule.neg_mem _ m1
  · rw [show (5 : ZMod 6) = 2 + 3 from rfl, hsymm]; exact Submodule.neg_mem _ m2

end mm_least

/-- **Theorem 2.3.9** (`thm:min-critical`). Let `K ∈ 𝔎_ccs`. Let `H_K` be a centrally symmetric
hexagon of least area circumscribing `K`. Then `H_K` is a critical hexagon in the sense of
Definition 2.3.8.

Proof (the book's, `mm_leastArea_critical`). The edge midpoints `s_j` of `H_K` lie on the boundary
of `K` (Remark 2.2.4) and satisfy the multi-point conditions; `L = ℤ s₀ + ℤ s₁` is `K`-admissible,
and `area(H_K) = det(2L) = 4 |det(s₀, s₁)|` (`mm_volume_hexagonOf`). `L` is critical because
`area(H_K) ≤ 4 det(L')` for every admissible lattice `L'`. Finally Theorem 2.3.7, applied to `L`
and the `s_j`, gives support lines `ℓ_j` at the `s_j` with the properties listed there; they are
the unique support lines at the `s_j`, hence the lines of the edges of `H_K`, which bound `H_K`.

Departures from the paper:
* `K` is not a parallelogram (Definition 2.3.8 requires it, and the book applies Theorem 2.3.7):
  proved in `mm_not_isParallelogram` (a parallelogram has circumscribed hexagons of area
  arbitrarily close to its own, and none of equal area).
* The admissibility of `L` is Mahler's Lemma 1 (the converse part of Theorem 2.3.6,
  `External.MinkowskiMahler.mm_isAdmissible`) instead of the tiling of the plane by translates
  of `H_K`, and `area(H_K) = 4 det(s₀, s₁)` is computed (`mm_volume_hexagonOf`) instead of using
  that `H_K` is a fundamental domain of `2L`.
* The book proves `area(H_K) ≤ 4Δ(K)` by comparing `H_K` with the critical hexagon `H̃_K` of a
  critical lattice `L̃` of `K`; neither the existence of a critical lattice nor the fact that
  `H̃_K` is a centrally symmetric hexagon in the sense of `IsCSHexagon` is established (by the
  book or here). Instead (`mm_volume_le`): an admissible `L'` gives the lattice packing `K + 2L'`
  (the remark after Definition 2.3.1), so `area(K)/det(2L') ≤ δ_L(K) = δ(K) = area(K)/area(H_K)`
  by Theorems 2.1.3 and 2.2.2, that is, `area(H_K) ≤ 4 det(L')`. -/
theorem theorem2_3_9 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {v : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) : IsCriticalHexagon K (hexagonOf v) := by
  -- the edge midpoints `s_j` and the critical lattice `L = ℤ s₀ + ℤ s₁`
  obtain ⟨hpar, hcrit, hmem, h012, hsymm⟩ := mm_leastArea_critical hK hv
  -- Theorem 2.3.7 for `L`: its support lines are the unique support lines at the `s_j`, so they
  -- are the lines `ℓ_j` of the edges of `H_K`
  obtain ⟨a, ha, -⟩ := theorem2_3_7 hK hpar hcrit (fun j ↦ (hmem j).1) (fun j ↦ (hmem j).2)
    h012 hsymm
  have hna : a = mm_normal v := by
    funext j
    exact mm_eq_of_line_eq (ha.2.2.1 j _ (mm_isSupportLine_normal hK hv j)
      (mm_normal_dot_midpoint hv.1 j)).symm
  refine ⟨hpar, _, hexMidpoint v, a, hcrit, hmem, h012, hsymm, ha, ?_⟩
  rw [hna, mm_polarHexagon_normal hv.1]

/-- **Corollary 2.3.10**. Let `K = K_min` have worst greatest packing density. Then `K` is
irreducible.

Proof (the book's). By Reinhardt (Lemma 2.2.7) every boundary point of `K` is the midpoint of an
edge of an area-minimizing centrally symmetric circumscribed hexagon `H_K`; by Theorem 2.3.9 and
its proof (`mm_leastArea_critical`) it is a point of the critical lattice spanned by two
consecutive edge midpoints of `H_K`. -/
theorem corollary2_3_10 {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) : IsIrreducible K := by
  refine ⟨hK.1, fun u hu ↦ ?_⟩
  -- by Reinhardt (Lemma 2.2.7), `u` is the midpoint of an edge of a least-area hexagon `H_K`
  obtain ⟨H, ⟨v, hv, -, j, hj⟩, -⟩ := (lemma2_2_7 hK).1 u hu
  -- by the proof of Theorem 2.3.9, the edge midpoints of `H_K` lie on a critical lattice
  obtain ⟨-, hcrit, hmem, -, -⟩ := mm_leastArea_critical hK.1 hv
  exact ⟨_, hcrit, hj ▸ (hmem j).1⟩

end SmoothedPolygons
