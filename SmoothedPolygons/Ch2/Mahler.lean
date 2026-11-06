module

public import SmoothedPolygons.Ch2.Reinhardt
public import SmoothedPolygons.Ch2.Hexagon
public import Basic.Algebra.Module.ZLattice.PlaneCritical
public import External.Mahler1947
public import External.MinkowskiMahler
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Mahler's approach (§2.3)

Admissible and critical lattices, the minimal determinant `Δ(K)` and irreducible disks
(Definitions 2.3.1–2.3.5), the theorems of Minkowski and Mahler on critical lattices and
circumscribed hexagons (Theorems 2.3.6 and 2.3.7, cited), Mahler's critical hexagons
(Definition 2.3.8), and their relation to Reinhardt's (Theorem 2.3.9, Corollary 2.3.10). The
proof of Theorem 2.3.9 needs the existence of a critical lattice (`crit_exists_critical`, Mahler's
compactness theorem, `Basic.Algebra.Module.ZLattice.PlaneCritical`) and some geometry of
centrally symmetric hexagons (their area, edge midpoints and lattice tiling,
`SmoothedPolygons.Ch2.Reinhardt` and `SmoothedPolygons.Ch2.Hexagon`; the lines of their edges,
`mm_*`, `crit_*`, and `irr_eq_of_line_eq` of `SmoothedPolygons.Ch2.Irreducible`).

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

/-- **The remark after Definition 2.3.5** (`rem:irreducible-original`, label of this
formalization; the definition is `def:irreducible`). Definition 2.3.5 is not the original
definition of irreducibility of a convex disk; by Mahler 1947, Lemma 3, it is equivalent to the
original definition: a convex disk `K ∈ 𝔎_ccs` is irreducible in the sense of Definition 2.3.5 if
and only if it is irreducible in Mahler's sense (`External.MahlerIrreducible.IsIrreducible`: every
centrally symmetric convex disk `K' ⊆ K` other than `K` has `Δ(K') < Δ(K)`). The definitions of the
source unfold to those of the book. -/
theorem isIrreducible_iff_mahlerIrreducible (K : Set (Fin 2 → ℝ)) :
    IsIrreducible K ↔ External.MahlerIrreducible.IsIrreducible K :=
  ⟨fun h ↦ (External.mahler_irreducible_iff h.1).2 h.2,
    fun h ↦ ⟨h.1, (External.mahler_irreducible_iff h.1).1 h⟩⟩

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

The proof compares a least-area hexagon `H_K` with the critical hexagon of a critical lattice of
`K`. That a critical lattice exists is Mahler's compactness theorem in the plane
(`crit_exists_critical`, from `PlaneLattice.exists_admissible_covolume_le`), which the book does
not state. The comparison uses the geometry of centrally symmetric hexagons: their area and the
position of the edge midpoints of a least-area hexagon (`SmoothedPolygons.Ch2.Reinhardt`,
`SmoothedPolygons.Ch2.Hexagon`), and the lines of their edges (below). -/

/-- **Existence of critical lattices.** Every `K ∈ 𝔎_ccs` has a critical lattice: the infimum
`Δ(K)` of Definition 2.3.3 is attained. The book uses a critical lattice of `K` in the proof of
Theorem 2.3.9 without showing that one exists. This is Mahler's compactness theorem in the plane
(`PlaneLattice.exists_admissible_covolume_le`, for the open set `interior K`); the lattice
`R ℤ²` is admissible when `K` lies in the square `|x₀|, |x₁| < R`. -/
lemma crit_exists_critical {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) :
    ∃ L, IsCriticalLattice K L := by
  -- an admissible lattice: `R ℤ²` with `K` inside the square `|x₀|, |x₁| < R`
  obtain ⟨R₀, hR₀⟩ := hK.2.1.isBounded.subset_closedBall 0
  set R := |R₀| + 1 with hRdef
  have hR : 0 < R := by positivity
  have hdet : (![R, 0] : Fin 2 → ℝ) 0 * (![0, R] : Fin 2 → ℝ) 1 -
      (![R, 0] : Fin 2 → ℝ) 1 * (![0, R] : Fin 2 → ℝ) 0 ≠ 0 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, sub_zero]
    positivity
  obtain ⟨hd₀, hs₀⟩ := PlaneLattice.discreteTopology_span_pair hdet
  have hint : ∀ m : ℤ, |(m : ℝ) * R| ≤ R₀ → m = 0 := by
    intro m hm
    rw [abs_mul, abs_of_pos hR] at hm
    have h1 : |(m : ℝ)| < 1 := by
      by_contra h
      push Not at h
      have := mul_le_mul_of_nonneg_right h hR.le
      linarith [le_abs_self R₀]
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast h1)
  have hadm₀ : IsAdmissible K (Submodule.span ℤ {![R, 0], ![0, R]}) := by
    intro x hx hxK
    obtain ⟨m, n, rfl⟩ := PlaneLattice.mem_span_pair_iff.1 hx
    have hxb := hR₀ (interior_subset hxK)
    rw [mem_closedBall_zero_iff] at hxb
    have h0 := (norm_le_pi_norm _ 0).trans hxb
    have h1 := (norm_le_pi_norm _ 1).trans hxb
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_zero, add_zero, zero_add, Real.norm_eq_abs] at h0 h1
    rw [hint m h0, hint n h1]
    simp
  -- a lattice of least determinant among the admissible ones
  obtain ⟨L, hLd, hLs, hLadm, hLmin⟩ := PlaneLattice.exists_admissible_covolume_le isOpen_interior
    (External.MinkowskiMahler.mm_zero_mem_interior hK) hd₀ hs₀ hadm₀
  refine ⟨L, ⟨hLd, hLs⟩, hLadm, ?_⟩
  unfold minDeterminant
  refine Eq.symm (IsLeast.csInf_eq ⟨⟨L, ⟨hLd, hLs⟩, hLadm, rfl⟩, ?_⟩)
  rintro d ⟨L', ⟨hL'd, hL's⟩, hL'adm, rfl⟩
  exact hLmin L' hL'd hL's hL'adm

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
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, v = rein_hex3 a b c := ⟨_, _, _, rein_eq_hex3 hv⟩
  have h := rein_isCSHexagon_iff_hexCond.1 hv
  obtain ⟨f01, f11, f21, f31, f41, f51, -⟩ := hex_zmod_facts
  ext x
  rw [rein_mem_hexagonOf_iff_strips h, polarHexagon, mem_ofPred_eq]
  simp only [mm_normal_dot_le_iff hv]
  constructor
  · intro hx
    have e0 := hx 0
    have e1 := hx 1
    have e2 := hx 2
    have e3 := hx 3
    have e4 := hx 4
    have e5 := hx 5
    simp only [f01, f11, f21, f31, f41, f51, rein_hex3_zero, rein_hex3_one, rein_hex3_two,
      rein_hex3_three, rein_hex3_four, rein_hex3_five] at e0 e1 e2 e3 e4 e5
    simp only [rein_strips, abs_le]
    simp only [det2, Pi.sub_apply, Pi.neg_apply, Pi.add_apply] at *
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  · rintro ⟨s0, s1, s2⟩ j
    rw [abs_le] at s0 s1 s2
    simp only [det2, Pi.sub_apply, Pi.add_apply] at s0 s1 s2
    rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [f01, f11, f21, f31, f41, f51, rein_hex3_zero, rein_hex3_one, rein_hex3_two,
        rein_hex3_three, rein_hex3_four, rein_hex3_five, det2, Pi.sub_apply, Pi.neg_apply] <;>
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

/-- The line of an edge of a least-area circumscribed hexagon is a support line of `K` at the
midpoint of the edge. -/
lemma mm_isSupportLine_normal (hK : IsCCSDisk K) (hv : IsLeastAreaHexagon K v) (j : ZMod 6) :
    IsSupportLine K {x | mm_normal v j ⬝ᵥ x = 1} := by
  refine ⟨⟨mm_normal v j, mm_normal_ne_zero hv.1 j, 1, rfl, fun x hx y hy ↦ ?_⟩,
    ⟨hexMidpoint v j, mm_normal_dot_midpoint hv.1 j, ?_⟩⟩
  · have h1 := mm_normal_dot_le hv.1 j (hv.2.1 hx)
    have h2 := mm_normal_dot_le hv.1 j (hv.2.1 hy)
    nlinarith
  · exact External.MinkowskiMahler.mm_mem_of_frontier hK (rein_hexMidpoint_mem_frontier hK hv j)

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

/-- **`K` is not a parallelogram.** The book excludes parallelograms by convention (TeX
1356–1357), and Definition 2.3.8 and Theorem 2.3.7 require it; for `K` with a least-area hexagon
`H_K` it is proved here. A centrally symmetric
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
  have hHfin : volume (hexagonOf v) ≠ ⊤ := (rein_isCompact_hexagonOf v).measure_lt_top.ne
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
    have hcond : rein_HexCond (r • u + (-r) • w) (r • u + (1 : ℝ) • w) ((1 : ℝ) • u + r • w) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [dAB, dBC, dAC] <;> nlinarith
    have hsub : K ⊆ hexagonOf (rein_hex3 (r • u + (-r) • w) (r • u + (1 : ℝ) • w)
        ((1 : ℝ) • u + r • w)) := by
      intro x hx
      obtain ⟨s, t, hs, ht, rfl⟩ := (hmem x).1 hx
      rw [rein_mem_hexagonOf_iff_strips hcond]
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
    have hle := hv.2.2 _ (rein_isCSHexagon_iff_hexCond.2 hcond) hsub
    have hfin : volume (hexagonOf (rein_hex3 (r • u + (-r) • w) (r • u + (1 : ℝ) • w)
        ((1 : ℝ) • u + r • w))) ≠ ⊤ := (rein_isCompact_hexagonOf _).measure_lt_top.ne
    have := ENNReal.toReal_mono hfin hle
    rw [← measureReal_def, ← measureReal_def, hex_volume_real_mk hcond, dAB, dBC, dAC] at this
    linarith
  -- the area of `K`
  have hKimg : K = hex_lin u w '' Icc (-1) 1 := by
    ext x
    rw [hmem]
    constructor
    · rintro ⟨s, t, hs, ht, rfl⟩
      rw [abs_le] at hs ht
      refine ⟨![s, t], ⟨fun i ↦ ?_, fun i ↦ ?_⟩, by rw [hex_lin_apply]; simp⟩ <;>
        fin_cases i <;> simp <;> linarith
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p 0, p 1, abs_le.2 ⟨hp.1 0, hp.2 0⟩, abs_le.2 ⟨hp.1 1, hp.2 1⟩, hex_lin_apply _ _ _⟩
  have hvolK : volume.real K = 4 * D := by
    rw [hKimg, measureReal_def, Measure.addHaar_image_linearMap, hex_det_lin, Real.volume_Icc_pi]
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

/-- Two vectors with the same values at two independent vectors are equal. -/
lemma crit_eq_of_dot {x y b c : Fin 2 → ℝ} (h : det2 x y ≠ 0) (hx : b ⬝ᵥ x = c ⬝ᵥ x)
    (hy : b ⬝ᵥ y = c ⬝ᵥ y) : b = c := by
  simp only [dotProduct, Fin.sum_univ_two] at hx hy
  simp only [det2] at h
  ext i
  fin_cases i
  · have : (b 0 - c 0) * (x 0 * y 1 - x 1 * y 0) = 0 := by
      linear_combination y 1 * hx - x 1 * hy
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h)
  · have : (b 1 - c 1) * (x 0 * y 1 - x 1 * y 0) = 0 := by
      linear_combination x 0 * hy - y 0 * hx
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h)

/-- The edge lines of a centrally symmetric hexagon are symmetric: `a_{j+3} = -a_j`. -/
lemma crit_normal_add_three (hv : IsCSHexagon v) (j : ZMod 6) :
    mm_normal v (j + 3) = -mm_normal v j := by
  have h1 := mm_normal_dot_self hv (j + 3)
  have h2 := mm_normal_dot_self hv j
  have e3 : v (j + 3) = -v j := (hv j).1
  have e4 : v (j + 3 + 1) = -v (j + 1) := by
    rw [show j + 3 + 1 = j + 1 + 3 by ring]; exact (hv (j + 1)).1
  refine crit_eq_of_dot (hv (j + 3)).2.1.ne' ?_ ?_
  · rw [h1.1, e3, neg_dotProduct, dotProduct_neg, neg_neg, h2.1]
  · rw [h1.2, e4, neg_dotProduct, dotProduct_neg, neg_neg, h2.2]

/-- The vertex `v_{j+2}` lies strictly inside the half-plane of the edge `j`. -/
lemma crit_normal_dot_add_two_lt (hv : IsCSHexagon v) (j : ZMod 6) :
    mm_normal v j ⬝ᵥ v (j + 2) < 1 := by
  rw [mm_normal_dot, div_lt_one (hv j).2.1]
  have := (hv j).2.2
  simp only [det2, Pi.sub_apply] at this ⊢
  linarith

/-- The vertex `v_{j-1}` lies strictly inside the half-plane of the edge `j`. -/
lemma crit_normal_dot_sub_one_lt (hv : IsCSHexagon v) (j : ZMod 6) :
    mm_normal v j ⬝ᵥ v (j - 1) < 1 := by
  rw [mm_normal_dot, div_lt_one (hv j).2.1]
  have := (hv (j - 1)).2.2
  rw [show j - 1 + 1 = j by ring, show j - 1 + 2 = j + 1 by ring] at this
  simp only [det2, Pi.sub_apply] at this ⊢
  linarith

/-- No two edges of a centrally symmetric hexagon lie on the same line. -/
lemma crit_normal_injective (hv : IsCSHexagon v) {i j : ZMod 6} (hij : i ≠ j) :
    mm_normal v i ≠ mm_normal v j := by
  intro heq
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by ring⟩
  have self := mm_normal_dot_self hv i
  have hneg : ∀ k, mm_normal v k ⬝ᵥ v (k + 3) = -1 := fun k ↦ by
    rw [(hv k).1, dotProduct_neg, (mm_normal_dot_self hv k).1]
  have hneg' : ∀ k, mm_normal v k ⬝ᵥ v (k + 4) = -1 := fun k ↦ by
    rw [show k + 4 = k + 1 + 3 by ring, (hv (k + 1)).1, dotProduct_neg,
      (mm_normal_dot_self hv k).2]
  rcases rein_zmod6_cases d with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hij (by simp)
  · have := crit_normal_dot_sub_one_lt hv (i + 1)
    rw [show i + 1 - 1 = i by ring, ← heq, self.1] at this
    exact lt_irrefl _ this
  · have := hneg' (i + 2)
    rw [show i + 2 + 4 = i + (2 + 4) by ring, show (2 + 4 : ZMod 6) = 0 by decide, add_zero,
      ← heq, self.1] at this
    norm_num at this
  · have h := self.1
    rw [heq, crit_normal_add_three hv i, neg_dotProduct, self.1] at h
    norm_num at h
  · have := hneg (i + 4)
    rw [show i + 4 + 3 = i + 1 + (3 + 3) by ring, show (3 + 3 : ZMod 6) = 0 by decide, add_zero,
      ← heq, self.2] at this
    norm_num at this
  · have := crit_normal_dot_add_two_lt hv (i + 5)
    rw [show i + 5 + 2 = i + 1 + (3 + 3) by ring, show (3 + 3 : ZMod 6) = 0 by decide, add_zero,
      ← heq, self.2] at this
    exact lt_irrefl _ this

/-- `K` lies on the side of each of its support lines `a · x = 1` that contains the origin. -/
lemma crit_dot_le_one (hK : IsCCSDisk K) {a : Fin 2 → ℝ} (ha : IsSupportLine K {x | a ⬝ᵥ x = 1})
    {x : Fin 2 → ℝ} (hx : x ∈ K) : a ⬝ᵥ x ≤ 1 := by
  obtain ⟨⟨b, -, c, hℓ, hsep⟩, -⟩ := ha
  have h0 : (0 : Fin 2 → ℝ) ∈ K :=
    interior_subset (External.MinkowskiMahler.mm_zero_mem_interior hK)
  have hc : c ≠ 0 := by
    rintro rfl
    have : (0 : Fin 2 → ℝ) ∈ {x : Fin 2 → ℝ | a ⬝ᵥ x = 1} := by rw [hℓ]; simp
    simp at this
  have hba : c⁻¹ • b = a := by
    refine irr_eq_of_line_eq (Set.ext fun y ↦ ?_)
    have := Set.ext_iff.1 hℓ y
    simp only [mem_ofPred_eq] at this ⊢
    rw [smul_dotProduct, smul_eq_mul, inv_mul_eq_one₀ hc, this, eq_comm]
  have hbx : b ⬝ᵥ x = c * (a ⬝ᵥ x) := by
    rw [← hba, smul_dotProduct, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have key : (b ⬝ᵥ x - c) * (b ⬝ᵥ 0 - c) = -(c ^ 2 * (a ⬝ᵥ x - 1)) := by
    rw [hbx, dotProduct_zero]; ring
  have hsx := hsep x hx 0 h0
  rw [key] at hsx
  have hc2 : 0 < c ^ 2 := by positivity
  by_contra h
  push Not at h
  have := mul_pos hc2 (sub_pos.2 h)
  linarith

/-- The six vertices of a hexagon bounded by symmetric lines `a_j · x = 1` (`a_{j+3} = -a_j`)
through the points `s_j = ±e, ±(e + f), ±f`, in terms of `α_j = a_j · s_{j+1} ∈ (0, 1)`:
`w₀ = ℓ₅ ∩ ℓ₀`, `w₁ = ℓ₀ ∩ ℓ₁`, `w₂ = ℓ₁ ∩ ℓ₂`. The edges are `w₁ - w₀ = λ₀ t₀`,
`w₂ - w₁ = λ₁ t₁`, `-w₀ - w₂ = λ₂ t₂` with `λ_j > 0` and `t_j` the directions of the lines, which
turn counterclockwise, so the six points are the vertices of a convex hexagon. -/
lemma crit_hexagon_of_dots {e f a₀ a₁ a₂ : Fin 2 → ℝ} {α₀ α₁ α₂ : ℝ} (hD : 0 < det2 e f)
    (h0 : 0 < α₀) (h0' : α₀ < 1) (h1 : 0 < α₁) (h1' : α₁ < 1) (h2 : 0 < α₂) (h2' : α₂ < 1)
    (d0e : a₀ ⬝ᵥ e = 1) (d0f : a₀ ⬝ᵥ f = α₀ - 1) (d1e : a₁ ⬝ᵥ e = 1 - α₁) (d1f : a₁ ⬝ᵥ f = α₁)
    (d2e : a₂ ⬝ᵥ e = -α₂) (d2f : a₂ ⬝ᵥ f = 1) :
    ∃ w₀ w₁ w₂ : Fin 2 → ℝ, rein_HexCond w₀ w₁ w₂ ∧ a₀ ⬝ᵥ w₀ = 1 ∧ a₀ ⬝ᵥ w₁ = 1 ∧
      a₁ ⬝ᵥ w₁ = 1 ∧ a₁ ⬝ᵥ w₂ = 1 ∧ a₂ ⬝ᵥ w₂ = 1 ∧ a₂ ⬝ᵥ -w₀ = 1 := by
  -- the vertices `w₀ = ℓ₅ ∩ ℓ₀`, `w₁ = ℓ₀ ∩ ℓ₁`, `w₂ = ℓ₁ ∩ ℓ₂`
  obtain ⟨D₀, hD₀def⟩ : ∃ x : ℝ, x = 1 - α₀ + α₀ * α₁ := ⟨_, rfl⟩
  obtain ⟨D₁, hD₁def⟩ : ∃ x : ℝ, x = 1 - α₁ + α₁ * α₂ := ⟨_, rfl⟩
  obtain ⟨D₂, hD₂def⟩ : ∃ x : ℝ, x = 1 - α₂ + α₂ * α₀ := ⟨_, rfl⟩
  have hD₀ : 0 < D₀ := by rw [hD₀def]; nlinarith
  have hD₁ : 0 < D₁ := by rw [hD₁def]; nlinarith
  have hD₂ : 0 < D₂ := by rw [hD₂def]; nlinarith
  have hD₀' := hD₀.ne'
  have hD₁' := hD₁.ne'
  have hD₂' := hD₂.ne'
  obtain ⟨w₀, hw₀⟩ : ∃ w : Fin 2 → ℝ, w = (α₀ / D₂) • e + (-(1 - α₂) / D₂) • f := ⟨_, rfl⟩
  obtain ⟨w₁, hw₁⟩ : ∃ w : Fin 2 → ℝ, w = ((1 - α₀ + α₁) / D₀) • e + (α₁ / D₀) • f := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w : Fin 2 → ℝ, w = ((1 - α₁) / D₁) • e + ((1 - α₁ + α₂) / D₁) • f :=
    ⟨_, rfl⟩
  -- the edge lengths `λ_j` (relative to the directions `t_j` of the lines)
  obtain ⟨l₀, hl₀⟩ : ∃ x : ℝ, x = α₁ / D₀ + (1 - α₂) / D₂ := ⟨_, rfl⟩
  obtain ⟨l₁, hl₁⟩ : ∃ x : ℝ, x = α₂ / D₁ + (1 - α₀) / D₀ := ⟨_, rfl⟩
  obtain ⟨l₂, hl₂⟩ : ∃ x : ℝ, x = α₀ / D₂ + (1 - α₁) / D₁ := ⟨_, rfl⟩
  have hl₀p : 0 < l₀ := hl₀ ▸ add_pos (div_pos h1 hD₀) (div_pos (by linarith) hD₂)
  have hl₁p : 0 < l₁ := hl₁ ▸ add_pos (div_pos h2 hD₁) (div_pos (by linarith) hD₀)
  have hl₂p : 0 < l₂ := hl₂ ▸ add_pos (div_pos h0 hD₂) (div_pos (by linarith) hD₁)
  have hcomb : ∀ p q r t : ℝ, det2 (p • e + q • f) (r • e + t • f) = (p * t - q * r) * det2 e f :=
    fun p q r t ↦ by simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have eA : det2 w₀ w₁ = l₀ * det2 e f := by
    rw [hw₀, hw₁, hcomb, hl₀]
    congr 1
    field_simp
    rw [hD₀def, hD₂def]
    ring
  have eB : det2 w₁ w₂ = l₁ * det2 e f := by
    rw [hw₁, hw₂, hcomb, hl₁]
    congr 1
    field_simp
    rw [hD₀def, hD₁def]
    ring
  have eC : det2 w₀ w₂ = l₂ * det2 e f := by
    rw [hw₀, hw₂, hcomb, hl₂]
    congr 1
    field_simp
    rw [hD₁def, hD₂def]
    ring
  have t01 : l₀ + l₁ - l₂ = l₀ * l₁ * ((1 - α₀) * (1 - α₁) + α₁) := by
    rw [hl₀, hl₁, hl₂]
    field_simp
    rw [hD₀def, hD₁def, hD₂def]
    ring
  have t12 : l₁ + l₂ - l₀ = l₁ * l₂ * (α₁ * α₂ + (1 - α₁)) := by
    rw [hl₀, hl₁, hl₂]
    field_simp
    rw [hD₀def, hD₁def, hD₂def]
    ring
  have t02 : l₀ + l₂ - l₁ = l₀ * l₂ * (1 - α₂ + α₀ * α₂) := by
    rw [hl₀, hl₁, hl₂]
    field_simp
    rw [hD₀def, hD₁def, hD₂def]
    ring
  have c01 : 0 < (1 - α₀) * (1 - α₁) + α₁ := by nlinarith
  have c12 : 0 < α₁ * α₂ + (1 - α₁) := by nlinarith
  have c02 : 0 < 1 - α₂ + α₀ * α₂ := by nlinarith
  refine ⟨w₀, w₁, w₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eA]; exact mul_pos hl₀p hD
  · rw [eB]; exact mul_pos hl₁p hD
  · rw [eC]; exact mul_pos hl₂p hD
  · rw [eA, eB, eC]
    have key : l₀ * det2 e f + l₁ * det2 e f - l₂ * det2 e f =
        l₀ * l₁ * ((1 - α₀) * (1 - α₁) + α₁) * det2 e f := by rw [← t01]; ring
    have := mul_pos (mul_pos (mul_pos hl₀p hl₁p) c01) hD
    linarith
  · rw [eA, eB, eC]
    have key : l₁ * det2 e f + l₂ * det2 e f - l₀ * det2 e f =
        l₁ * l₂ * (α₁ * α₂ + (1 - α₁)) * det2 e f := by rw [← t12]; ring
    have := mul_pos (mul_pos (mul_pos hl₁p hl₂p) c12) hD
    linarith
  · rw [eA, eB, eC]
    have key : l₀ * det2 e f + l₂ * det2 e f - l₁ * det2 e f =
        l₀ * l₂ * (1 - α₂ + α₀ * α₂) * det2 e f := by rw [← t02]; ring
    have := mul_pos (mul_pos (mul_pos hl₀p hl₂p) c02) hD
    linarith
  · rw [hw₀]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, d0e, d0f]
    field_simp
    rw [hD₂def]
    ring
  · rw [hw₁]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, d0e, d0f]
    field_simp
    rw [hD₀def]
    ring
  · rw [hw₁]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, d1e, d1f]
    field_simp
    rw [hD₀def]
    ring
  · rw [hw₂]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, d1e, d1f]
    field_simp
    rw [hD₁def]
    ring
  · rw [hw₂]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, d2e, d2f]
    field_simp
    rw [hD₁def]
    ring
  · rw [hw₀]
    simp only [dotProduct_neg, dotProduct_add, dotProduct_smul, smul_eq_mul, d2e, d2f]
    field_simp
    rw [hD₂def]
    ring

/-- **The critical hexagon `H̃_K` is a centrally symmetric hexagon.** Let `s₀, …, s₅` be points of
`K` with `s₀ - s₁ + s₂ = 0`, `s_{j+3} = -s_j` and `det(s₀, s₁) > 0`, and let `ℓ_j = {a_j · x = 1}`
be the support lines of Theorem 2.3.7 at the `s_j`. Then the hexagon `H̃_K` bounded by the `ℓ_j`
is `hexagonOf w` for a centrally symmetric hexagon `w` (`IsCSHexagon`), whose edges lie on the
`ℓ_j`. The book takes this for granted ("the centrally symmetric hexagon `H_K` bounded by the
support lines", Theorem 2.3.7). Since `ℓ_j` is the only support line at `s_j` and no two of the
lines coincide, `s_j` lies on no other `ℓ_k`; in the basis `e = s₀, f = s₂` this says
`α_j = a_j · s_{j+1} ∈ (0, 1)`, and `crit_hexagon_of_dots` gives the vertices. -/
lemma crit_exists_isCSHexagon (hK : IsCCSDisk K) {s a : ZMod 6 → Fin 2 → ℝ}
    (h012 : s 0 - s 1 + s 2 = 0) (hsymm : ∀ j, s (j + 3) = -s j) (hsK : ∀ j, s j ∈ K)
    (hpos : 0 < det2 (s 0) (s 1)) (ha : IsMahlerSupportSystem K s a) :
    ∃ w, IsCSHexagon w ∧ hexagonOf w = polarHexagon a := by
  obtain ⟨hasymm, hsupp, huniq, hdist, -, -, -⟩ := ha
  -- `a_k · s_j ≤ 1`, with equality only for `k = j`
  have hle : ∀ k j, a k ⬝ᵥ s j ≤ 1 := fun k j ↦ crit_dot_le_one hK (hsupp k).1 (hsK j)
  have hlt : ∀ k j, k ≠ j → a k ⬝ᵥ s j < 1 := by
    intro k j hkj
    refine (hle k j).lt_of_ne fun heq ↦ hdist k j hkj ?_
    exact irr_eq_of_line_eq (huniq j _ (hsupp k).1 heq)
  -- the points in the basis `e = s₀`, `f = s₂`
  have hs1 : s 1 = s 0 + s 2 := by rw [← sub_eq_zero, ← neg_eq_zero, ← h012]; abel
  have hs3 : s 3 = -s 0 := hsymm 0
  have hs5 : s 5 = -s 2 := hsymm 2
  have hD : 0 < det2 (s 0) (s 2) := by
    have : det2 (s 0) (s 1) = det2 (s 0) (s 2) := by
      rw [hs1]; simp only [det2, Pi.add_apply]; ring
    linarith
  have d0e : a 0 ⬝ᵥ s 0 = 1 := (hsupp 0).2
  have d0f : a 0 ⬝ᵥ s 2 = a 0 ⬝ᵥ s 1 - 1 := by rw [hs1, dotProduct_add, d0e]; ring
  have d1e : a 1 ⬝ᵥ s 0 = 1 - a 1 ⬝ᵥ s 2 := by
    have h := (hsupp 1).2
    rw [hs1, dotProduct_add] at h
    linarith
  have d2f : a 2 ⬝ᵥ s 2 = 1 := (hsupp 2).2
  have d2e : a 2 ⬝ᵥ s 0 = -(a 2 ⬝ᵥ s 3) := by rw [hs3, dotProduct_neg, neg_neg]
  -- `α_j ∈ (0, 1)`
  have h0' : a 0 ⬝ᵥ s 1 < 1 := hlt 0 1 (by decide)
  have h0 : 0 < a 0 ⬝ᵥ s 1 := by
    have := hlt 0 5 (by decide)
    rw [hs5, dotProduct_neg, d0f] at this
    linarith
  have h1' : a 1 ⬝ᵥ s 2 < 1 := hlt 1 2 (by decide)
  have h1 : 0 < a 1 ⬝ᵥ s 2 := by
    have := hlt 1 0 (by decide)
    rw [d1e] at this
    linarith
  have h2' : a 2 ⬝ᵥ s 3 < 1 := hlt 2 3 (by decide)
  have h2 : 0 < a 2 ⬝ᵥ s 3 := by
    have := hlt 2 1 (by decide)
    rw [hs1, dotProduct_add, d2e, d2f] at this
    linarith
  obtain ⟨w₀, w₁, w₂, hc, l00, l01, l11, l12, l22, l23⟩ :=
    crit_hexagon_of_dots hD h0 h0' h1 h1' h2 h2' d0e d0f d1e rfl d2e d2f
  -- the hexagon `w` and its edge lines
  have hw : IsCSHexagon (rein_hex3 w₀ w₁ w₂) := rein_isCSHexagon_iff_hexCond.2 hc
  set w := rein_hex3 w₀ w₁ w₂ with hwdef
  have hline3 : ∀ j, a j ⬝ᵥ w j = 1 ∧ a j ⬝ᵥ w (j + 1) = 1 →
      a (j + 3) ⬝ᵥ w (j + 3) = 1 ∧ a (j + 3) ⬝ᵥ w (j + 3 + 1) = 1 := by
    rintro j ⟨e1, e2⟩
    rw [show j + 3 + 1 = j + 1 + 3 by ring, (hw j).1, (hw (j + 1)).1, hasymm j, neg_dotProduct,
      neg_dotProduct, dotProduct_neg, dotProduct_neg, neg_neg, neg_neg]
    exact ⟨e1, e2⟩
  have hl0 : a 0 ⬝ᵥ w 0 = 1 ∧ a 0 ⬝ᵥ w (0 + 1) = 1 := ⟨l00, l01⟩
  have hl1 : a 1 ⬝ᵥ w 1 = 1 ∧ a 1 ⬝ᵥ w (1 + 1) = 1 := ⟨l11, l12⟩
  have hl2 : a 2 ⬝ᵥ w 2 = 1 ∧ a 2 ⬝ᵥ w (2 + 1) = 1 := ⟨l22, l23⟩
  have hline : ∀ j, a j ⬝ᵥ w j = 1 ∧ a j ⬝ᵥ w (j + 1) = 1 := by
    intro j
    rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hl0
    · exact hl1
    · exact hl2
    · exact hline3 0 hl0
    · exact hline3 1 hl1
    · exact hline3 2 hl2
  have hn : mm_normal w = a := by
    funext j
    have := mm_normal_dot_self hw j
    exact crit_eq_of_dot (hw j).2.1.ne' (this.1.trans (hline j).1.symm)
      (this.2.trans (hline j).2.symm)
  exact ⟨w, hw, by rw [← hn, mm_polarHexagon_normal hw]⟩

/-- The six lattice points of Theorem 2.3.6 for a critical lattice `L`: `s₀, s₁, s₂` and their
reflections, numbered counterclockwise. -/
lemma crit_six_points (hK : IsCCSDisk K) {L : Submodule ℤ (Fin 2 → ℝ)}
    (hL : IsCriticalLattice K L) :
    ∃ s : ZMod 6 → Fin 2 → ℝ, (∀ j, s j ∈ L) ∧ (∀ j, s j ∈ frontier K) ∧ s 0 - s 1 + s 2 = 0 ∧
      (∀ j, s (j + 3) = -s j) ∧ 0 < det2 (s 0) (s 1) := by
  obtain ⟨s₀, s₁, s₂, h0L, h1L, h2L, h0K, h1K, h2K, -, h1, hdetL, -⟩ := (theorem2_3_6 hK).1 L hL
  have hne : det2 s₀ s₁ ≠ 0 := by
    intro h
    obtain ⟨hd, hs⟩ := hL.1
    have : IsZLattice ℝ L := ⟨hs⟩
    have hpos : 0 < latticeDet L := by unfold latticeDet; exact ZLattice.covolume_pos L
    rw [hdetL, h, abs_zero] at hpos
    exact lt_irrefl _ hpos
  have hneg : ∀ x ∈ frontier K, -x ∈ frontier K :=
    fun x hx ↦ External.MinkowskiMahler.mm_neg_mem_frontier hK hx
  obtain ⟨f01, f11, f21, f31, f41, f51, -, -, -, -, -, -, f03, f13, f23, f33, f43, f53⟩ :=
    hex_zmod_facts
  have hsym : ∀ a b c : Fin 2 → ℝ, ∀ j, rein_hex3 a b c (j + 3) = -rein_hex3 a b c j := by
    intro a b c j
    rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [f03]; rfl
    · rw [f13]; rfl
    · rw [f23]; rfl
    · rw [f33]; exact (neg_neg a).symm
    · rw [f43]; exact (neg_neg b).symm
    · rw [f53]; exact (neg_neg c).symm
  have hall : ∀ (P : (Fin 2 → ℝ) → Prop) (a b c : Fin 2 → ℝ), (∀ x, P x → P (-x)) → P a → P b →
      P c → ∀ j, P (rein_hex3 a b c j) := by
    intro P a b c hP ha hb hc j
    rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hP _ ha
    · exact hP _ hb
    · exact hP _ hc
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- clockwise: take `s₀, -s₂, -s₁`
    refine ⟨rein_hex3 s₀ (-s₂) (-s₁), hall (· ∈ L) _ _ _ (fun x hx ↦ L.neg_mem hx) h0L
      (L.neg_mem h2L) (L.neg_mem h1L), hall (· ∈ frontier K) _ _ _ hneg h0K (hneg _ h2K)
      (hneg _ h1K), ?_, hsym _ _ _, ?_⟩
    · change s₀ - -s₂ + -s₁ = 0
      rw [h1]; abel
    · change 0 < det2 s₀ (-s₂)
      have : det2 s₀ (-s₂) = -det2 s₀ s₁ := by
        rw [h1]; simp only [det2, Pi.neg_apply, Pi.add_apply]; ring
      rw [this]; linarith
  · refine ⟨rein_hex3 s₀ s₁ s₂, hall (· ∈ L) _ _ _ (fun x hx ↦ L.neg_mem hx) h0L h1L h2L,
      hall (· ∈ frontier K) _ _ _ hneg h0K h1K h2K, ?_, hsym _ _ _, hgt⟩
    change s₀ - s₁ + s₂ = 0
    rw [h1]; abel

/-- **The area of a least-area hexagon is `4Δ(K)`** (the book's proof of Theorem 2.3.9). Let
`L̃` be a critical lattice of `K` (`crit_exists_critical`) and `H̃_K` its critical hexagon: the
hexagon bounded by the support lines of Theorem 2.3.7 at the six points of `L̃` on the boundary
of `K` given by Theorem 2.3.6. Both `H_K` and `H̃_K` have least area among the centrally
symmetric hexagons circumscribing `K`: `H̃_K` is such a hexagon (`crit_exists_isCSHexagon`), so
`area(H_K) ≤ area(H̃_K)`; the edges of `H_K` are symmetric support lines of `K`
(`mm_isSupportLine_normal`), no two of them equal, so `area(H̃_K) ≤ area(H_K)` by
Theorem 2.3.7 (4). Hence `area(H_K) = area(H̃_K) = 4Δ(K)` by Theorem 2.3.7 (2). -/
lemma crit_volume_eq (hK : IsCCSDisk K) (hpar : ¬ IsParallelogram K)
    (hv : IsLeastAreaHexagon K v) : volume.real (hexagonOf v) = 4 * minDeterminant K := by
  -- a critical lattice `L̃`, its six boundary points (Theorem 2.3.6) and its critical hexagon
  -- (Theorem 2.3.7)
  obtain ⟨L, hL⟩ := crit_exists_critical hK
  obtain ⟨s, hsL, hsK, h012, hsymm, hpos⟩ := crit_six_points hK hL
  obtain ⟨a, ha, -⟩ := theorem2_3_7 hK hpar hL hsL hsK h012 hsymm
  have hsK' : ∀ j, s j ∈ K := fun j ↦ External.MinkowskiMahler.mm_mem_of_frontier hK (hsK j)
  obtain ⟨w, hw, hwa⟩ := crit_exists_isCSHexagon hK h012 hsymm hsK' hpos ha
  -- `area(H_K) ≤ area(H̃_K)`: `H̃_K` is a centrally symmetric hexagon circumscribing `K`
  have hKw : K ⊆ hexagonOf w := by
    rw [hwa]
    exact fun x hx j ↦ crit_dot_le_one hK (ha.2.1 j).1 hx
  have hle := hv.2.2 w hw hKw
  -- `area(H̃_K) ≤ area(H_K)`: Theorem 2.3.7 (4) for the edge lines of `H_K`
  have hge := ha.2.2.2.2.2.2 (mm_normal v) (crit_normal_add_three hv.1)
    (fun i j hij ↦ crit_normal_injective hv.1 hij) (mm_isSupportLine_normal hK hv)
  rw [mm_polarHexagon_normal hv.1, ← hwa] at hge
  have heq : volume (hexagonOf v) = volume (hexagonOf w) := le_antisymm hle hge
  rw [measureReal_def, heq, ← measureReal_def, hwa]
  exact ha.2.2.2.2.1

/-- Doubling the basis of a lattice multiplies its determinant by `4`: `det(2L) = 4 det(L)`. -/
lemma mm_latticeDet_two_smul {u w : Fin 2 → ℝ} (h : det2 u w ≠ 0) :
    latticeDet (latticeSpan ((2 : ℝ) • u) ((2 : ℝ) • w)) = 4 * latticeDet (latticeSpan u w) := by
  have e : det2 ((2 : ℝ) • u) ((2 : ℝ) • w) = 4 * det2 u w := by
    simp only [det2, Pi.smul_apply, smul_eq_mul]; ring
  have h2 : det2 ((2 : ℝ) • u) ((2 : ℝ) • w) ≠ 0 := by rw [e]; exact mul_ne_zero (by norm_num) h
  rw [show latticeDet (latticeSpan ((2 : ℝ) • u) ((2 : ℝ) • w)) =
      |det2 ((2 : ℝ) • u) ((2 : ℝ) • w)| from External.MinkowskiMahler.mm_det_span h2,
    show latticeDet (latticeSpan u w) = |det2 u w| from External.MinkowskiMahler.mm_det_span h, e,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]

/-- The packing part of `rein_hex_lattice`, for the hexagon with vertices `±a, ±b, ±c` and the
lattice generated by `a + b` and `b + c`, with the same proof: a nonzero vector of the lattice
leaves one of the three strips of the hexagon of twice the width (`rein_interior_strips`,
`rein_lattice_arith`). -/
private lemma mm_hex3_packing {a b c : Fin 2 → ℝ} (h : IsCSHexagon (rein_hex3 a b c)) :
    IsLatticePacking (hexagonOf (rein_hex3 a b c)) (latticeSpan (a + b) (b + c)) := by
  obtain ⟨h1, h2, h3, -, h5, h6⟩ := (rein_isCSHexagon_hex3_iff a b c).1 h
  set u1 := a + b with hu1
  set u2 := b + c with hu2
  intro l hl l' hl' hne
  rw [Set.disjoint_left]
  intro y hy1 hy2
  rw [show (fun x : Fin 2 → ℝ ↦ x + l) = ⇑(Homeomorph.addRight l) from rfl,
    ← Homeomorph.image_interior] at hy1
  rw [show (fun x : Fin 2 → ℝ ↦ x + l') = ⇑(Homeomorph.addRight l') from rfl,
    ← Homeomorph.image_interior] at hy2
  obtain ⟨x, hx, rfl⟩ := hy1
  obtain ⟨x', hx', hxx⟩ := hy2
  simp only [Homeomorph.coe_addRight] at hxx
  have hd : l' - l ∈ latticeSpan u1 u2 := sub_mem hl' hl
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.1 hd
  rw [← Int.cast_smul_eq_zsmul ℝ p, ← Int.cast_smul_eq_zsmul ℝ q] at hpq
  have hs1 := rein_interior_strips h hx
  have hs2 := rein_interior_strips h hx'
  have hx'eq : x' = x - (l' - l) := by
    rw [eq_sub_iff_add_eq, ← add_sub_assoc, hxx, add_sub_cancel_right]
  rw [hx'eq, ← hpq] at hs2
  have G : ∀ w : Fin 2 → ℝ, det2 w (x - ((p : ℝ) • u1 + (q : ℝ) • u2)) =
      det2 w x - (p * det2 w u1 + q * det2 w u2) := by
    intro w; simp only [det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [G, G, G] at hs2
  have v0a : det2 (a - b) u1 = 2 * det2 a b := by
    simp only [hu1, det2, Pi.sub_apply, Pi.add_apply]; ring
  have v0b : det2 (a - b) u2 = det2 a b + det2 a c - det2 b c := by
    simp only [hu2, det2, Pi.sub_apply, Pi.add_apply]; ring
  have v1a : det2 (b - c) u1 = det2 b c + det2 a c - det2 a b := by
    simp only [hu1, det2, Pi.sub_apply, Pi.add_apply]; ring
  have v1b : det2 (b - c) u2 = 2 * det2 b c := by
    simp only [hu2, det2, Pi.sub_apply, Pi.add_apply]; ring
  have v2a : det2 (c + a) u1 = det2 a b - det2 b c - det2 a c := by
    simp only [hu1, det2, Pi.add_apply]; ring
  have v2b : det2 (c + a) u2 = det2 a b + det2 a c - det2 b c := by
    simp only [hu2, det2, Pi.add_apply]; ring
  rw [v0a, v0b, v1a, v1b, v2a, v2b] at hs2
  obtain ⟨s1, s2, s3⟩ := hs1
  obtain ⟨t1, t2, t3⟩ := hs2
  rw [abs_lt] at s1 s2 s3 t1 t2 t3
  refine rein_lattice_arith h1 h2 h3 h5 h6 (p := p) (q := q) ?_ ?_ ?_ ?_
  · rintro ⟨rfl, rfl⟩
    simp only [Int.cast_zero, zero_smul, add_zero] at hpq
    exact hne (sub_eq_zero.1 hpq.symm).symm
  all_goals rw [abs_lt]; constructor <;> nlinarith

/-- **The lattice tiling by a centrally symmetric hexagon** (§2.2: "every centrally symmetric
hexagon tiles the plane"; `rein_hex_lattice` with its lattice made explicit). Let `s_j` be the
edge midpoints of a centrally symmetric hexagon `H` and `L = ℤ s₀ + ℤ s₁`. The translates of `H`
by the lattice `2L`, generated by `2 s₀ = v₀ + v₁` and `2 s₁ = v₁ + v₂` (the lattice of
`rein_hex_lattice`), have pairwise disjoint interiors, and `det(2L) = area(H)`: `H` is a
fundamental domain of `2L`. -/
lemma mm_hex_lattice (hv : IsCSHexagon v) :
    IsPlaneLattice (latticeSpan ((2 : ℝ) • hexMidpoint v 0) ((2 : ℝ) • hexMidpoint v 1)) ∧
      latticeDet (latticeSpan ((2 : ℝ) • hexMidpoint v 0) ((2 : ℝ) • hexMidpoint v 1)) =
        volume.real (hexagonOf v) ∧
      IsLatticePacking (hexagonOf v)
        (latticeSpan ((2 : ℝ) • hexMidpoint v 0) ((2 : ℝ) • hexMidpoint v 1)) := by
  have hpos := rein_det2_hexMidpoint_pos hv
  have hne : det2 ((2 : ℝ) • hexMidpoint v 0) ((2 : ℝ) • hexMidpoint v 1) ≠ 0 := by
    have : det2 ((2 : ℝ) • hexMidpoint v 0) ((2 : ℝ) • hexMidpoint v 1) =
        4 * det2 (hexMidpoint v 0) (hexMidpoint v 1) := by
      simp only [det2, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]; positivity
  refine ⟨External.MinkowskiMahler.mm_isLattice_span hne, ?_, ?_⟩
  · -- `det(2L) = 4 det(s₀, s₁) = area(H)`
    rw [mm_latticeDet_two_smul hpos.ne', show latticeDet (latticeSpan (hexMidpoint v 0)
      (hexMidpoint v 1)) = |det2 (hexMidpoint v 0) (hexMidpoint v 1)| from
      External.MinkowskiMahler.mm_det_span hpos.ne', abs_of_pos hpos, hex_volume_hexagonOf hv]
  · -- the packing: `2 s₀ = v₀ + v₁`, `2 s₁ = v₁ + v₂`
    have hm : ∀ j, (2 : ℝ) • hexMidpoint v j = v j + v (j + 1) := fun j ↦ by
      rw [hexMidpoint, midpoint_eq_smul_add, smul_smul]; norm_num
    have h3 := rein_eq_hex3 hv
    rw [hm, hm, show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl]
    have := mm_hex3_packing (a := v 0) (b := v 1) (c := v 2) (by rw [← h3]; exact hv)
    rwa [← h3] at this

/-- **Overlapping tiles.** If an interior point `x` of a convex set `H` with nonempty interior lies
in the translate `H + y`, then the interiors of `H = H + 0` and `H + y` meet. -/
lemma mm_not_disjoint_interior {H : Set (Fin 2 → ℝ)} (hc : Convex ℝ H)
    (hH : (interior H).Nonempty) {x y : Fin 2 → ℝ} (hx : x ∈ interior H) (hy : x - y ∈ H) :
    ¬ Disjoint (interior ((fun z ↦ z + 0) '' H)) (interior ((fun z ↦ z + y) '' H)) := by
  -- `x - y` is a limit of interior points `w` of `H`, and `w + y` is near `x`
  have hcl : x - y ∈ closure (interior H) := by
    rw [hc.closure_interior_eq_closure_of_nonempty_interior hH]
    exact subset_closure hy
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hcl ((fun z ↦ z + y) ⁻¹' interior H)
    (isOpen_interior.preimage (continuous_id.add continuous_const)) (by simpa using hx)
  rw [Set.not_disjoint_iff]
  refine ⟨w + y, by simpa using hw1, ?_⟩
  rw [show (fun z : Fin 2 → ℝ ↦ z + y) = ⇑(Homeomorph.addRight y) from rfl,
    ← Homeomorph.image_interior]
  exact ⟨w, hw2, rfl⟩

/-- **The proof of Theorem 2.3.9.** For a least-area centrally symmetric hexagon `H_K` around
`K`, with edge midpoints `s_j`: `K` is not a parallelogram, the `s_j` lie on the boundary of `K`
and satisfy the multi-point conditions, and the lattice `L` generated by `s₀, s₁` is a critical
lattice of `K` containing all the `s_j`.

The book's proof. Tile the plane with the translates of `H_K` by `2L`, the lattice of their
centres (`mm_hex_lattice`). A point of `L` with one or two odd coordinates is the midpoint `s_j`
of an edge of a tile `H_K + y` centred at an adjacent point `y` of `2L`, and a point of `2L` is the
centre of its tile; so a nonzero point of `L` in the interior of `K` would be inside `H_K` and in
another tile, or would be `0` or some `s_j ∈ ∂K`: `L` is `K`-admissible. `H_K` is a fundamental
domain of `2L`, so `area(H_K) = det(2L) = 4 det(L)` (the book writes `4Δ(K)` for `4 det(L)` here,
TeX 1903, before `L` is known to be critical; E7). Both `H_K` and the critical hexagon of a
critical lattice have least area, and the latter has area `4Δ(K)` (`crit_volume_eq`), so
`det(L) = Δ(K)`: `L` is critical. -/
lemma mm_leastArea_critical (hK : IsCCSDisk K) (hv : IsLeastAreaHexagon K v) :
    ¬ IsParallelogram K ∧
      IsCriticalLattice K (latticeSpan (hexMidpoint v 0) (hexMidpoint v 1)) ∧
      (∀ j, hexMidpoint v j ∈ latticeSpan (hexMidpoint v 0) (hexMidpoint v 1) ∧
        hexMidpoint v j ∈ frontier K) ∧
      hexMidpoint v 0 - hexMidpoint v 1 + hexMidpoint v 2 = 0 ∧
      ∀ j, hexMidpoint v (j + 3) = -hexMidpoint v j := by
  have hpar := mm_not_isParallelogram hK hv
  -- the edge midpoints `s_j` lie on the boundary of `K` and satisfy the multi-point conditions
  set s := hexMidpoint v with hs
  have hsymm : ∀ j, s (j + 3) = -s j := rein_hexMidpoint_add_three hv.1
  have hsub : s 1 - s 0 = s 2 := hex_hexMidpoint_sub hv.1
  have h012 : s 0 - s 1 + s 2 = 0 := by rw [← hsub]; abel
  have hfr : ∀ j, s j ∈ frontier K := rein_hexMidpoint_mem_frontier hK hv
  have hpos : 0 < det2 (s 0) (s 1) := rein_det2_hexMidpoint_pos hv.1
  have hlat : IsPlaneLattice (latticeSpan (s 0) (s 1)) :=
    External.MinkowskiMahler.mm_isLattice_span hpos.ne'
  -- tile the plane with translates of `H_K`: the centres of the tiles form the lattice `2L`
  -- generated by `2 s₀` and `2 s₁`, and `H_K` is a fundamental domain of `2L`
  obtain ⟨-, hdet2, hpack⟩ := mm_hex_lattice hv.1
  -- `L` is `K`-admissible
  have hadm : IsAdmissible K (latticeSpan (s 0) (s 1)) := by
    intro x hxL hxK
    by_contra hx0
    have hxH : x ∈ interior (hexagonOf v) := interior_mono hv.2.1 hxK
    -- `x` is not the centre (`c = 0`) or an edge midpoint (`c = s_j`) of a tile `H_K + y`
    have key : ∀ y ∈ latticeSpan ((2 : ℝ) • s 0) ((2 : ℝ) • s 1), ∀ c,
        (c = 0 ∨ c ∈ frontier K) → x = c + y → False := by
      intro y hy c hc hxy
      by_cases hy0 : y = 0
      · -- `y = 0`: `x = c` is `0` or a boundary point of `K`, not an interior point
        rw [hy0, add_zero] at hxy
        rcases hc with rfl | hc
        · exact hx0 hxy
        · exact hc.2 (hxy ▸ hxK)
      · -- `y ≠ 0`: `x` lies in the interior of the tile `H_K` and in the tile `H_K + y`
        have hcH : c ∈ hexagonOf v := by
          rcases hc with rfl | hc
          · exact hv.2.1 (interior_subset (rein_zero_mem_interior hK))
          · exact hv.2.1 (External.MinkowskiMahler.mm_mem_of_frontier hK hc)
        exact mm_not_disjoint_interior (convex_convexHull ℝ _)
          (hK.2.2.1.mono (interior_mono hv.2.1)) hxH (by rwa [hxy, add_sub_cancel_right])
          (hpack 0 (zero_mem _) y hy (Ne.symm hy0))
    -- the parity of the coordinates of `x = p s₀ + q s₁`
    obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.1 hxL
    have mem2 : ∀ m n : ℤ,
        m • ((2 : ℝ) • s 0) + n • ((2 : ℝ) • s 1) ∈ latticeSpan ((2 : ℝ) • s 0) ((2 : ℝ) • s 1) :=
      fun m n ↦ Submodule.mem_span_pair.2 ⟨m, n, rfl⟩
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' p <;> obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' q
    · -- both even: `x ∈ 2L` is the centre of the tile `H_K + x`
      refine key _ (mem2 m n) 0 (Or.inl rfl) ?_
      module
    · -- `p` even, `q` odd: `x = s₁ + y`, an edge midpoint of the tile `H_K + y`
      refine key _ (mem2 m n) (s 1) (Or.inr (hfr 1)) ?_
      module
    · -- `p` odd, `q` even: `x = s₀ + y`
      refine key _ (mem2 m n) (s 0) (Or.inr (hfr 0)) ?_
      module
    · -- both odd: `x = s₂ + y`, as `s₀ + s₁ = s₂ + 2 s₀`
      refine key _ (mem2 (m + 1) n) (s 2) (Or.inr (hfr 2)) ?_
      rw [← hsub]
      module
  -- `H_K` is a fundamental domain of `2L`: `area(H_K) = det(2L) = 4 det(L)`
  have harea : volume.real (hexagonOf v) = 4 * latticeDet (latticeSpan (s 0) (s 1)) := by
    rw [← hdet2, mm_latticeDet_two_smul hpos.ne']
  -- `L` is critical: `area(H_K) = 4Δ(K)` (`crit_volume_eq`)
  have hdet : latticeDet (latticeSpan (s 0) (s 1)) = minDeterminant K := by
    have := crit_volume_eq hK hpar hv
    linarith
  refine ⟨hpar, ⟨hlat, hadm, hdet⟩, fun j ↦ ⟨?_, hfr j⟩, h012, hsymm⟩
  have m0 : s 0 ∈ latticeSpan (s 0) (s 1) := Submodule.subset_span (by simp)
  have m1 : s 1 ∈ latticeSpan (s 0) (s 1) := Submodule.subset_span (by simp)
  have m2 : s 2 ∈ latticeSpan (s 0) (s 1) := by
    rw [← hsub]; exact Submodule.sub_mem _ m1 m0
  rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
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
of `K` (`rein_hexMidpoint_mem_frontier`) and satisfy the multi-point conditions. Tile the plane
with translates of `H_K`; their centres form the lattice `2L`, `L = ℤ s₀ + ℤ s₁`, and `H_K` is a
fundamental domain of `2L` (`mm_hex_lattice`, the lattice tiling of `rein_hex_lattice`). A nonzero
point of `L` is either a point of `2L`, the centre of another tile, or `s_j + y` with `y ∈ 2L`, the
midpoint of an edge of the tile `H_K + y`; it is not in the interior of `K`, as for `y ≠ 0` the
tile `H_K + y` would overlap `H_K` (`mm_not_disjoint_interior`) and `s_j ∈ ∂K`. So `L` is
`K`-admissible, and `area(H_K) = det(2L) = 4 det(L)`. `L` is critical (`crit_volume_eq`): let `L̃`
be a critical lattice of `K` (`crit_exists_critical`), with six points on the boundary of `K`
(Theorem 2.3.6) and critical hexagon `H̃_K` (Theorem 2.3.7). Both `H_K` and `H̃_K` have least
area among the centrally symmetric circumscribing hexagons (for `H̃_K`, Theorem 2.3.7 (4)), so
their areas are equal, and `area(H̃_K) = 4Δ(K)` (Theorem 2.3.7 (2)); hence `det(L) = Δ(K)`.
Finally Theorem 2.3.7, applied to `L` and the `s_j`, gives support lines `ℓ_j` at the `s_j` with
the properties listed there; they are the unique support lines at the `s_j`, hence the lines of
the edges of `H_K`, which bound `H_K`.

A slip of the book, corrected (E7): it writes `4Δ(K) = det(2L) = area(H_K)` (TeX 1903) before
showing that `L` is critical; at that point only `4 det(L) = det(2L) = area(H_K)` holds, and
`det(L) = Δ(K)` is the conclusion of the next step.

`K` is not a parallelogram: the book excludes parallelograms by convention (TeX 1356–1357: "We
exclude this exception from our further discussions"), and Definition 2.3.8 and Theorem 2.3.7
require it. For a least-area hexagon `H_K` it is proved in `mm_not_isParallelogram` (a
parallelogram has circumscribed hexagons of area arbitrarily close to its own, and none of equal
area).

Gaps of the book's comparison of `H_K` with `H̃_K`, filled along its lines: a critical lattice
`L̃` exists (`crit_exists_critical`, by Mahler's compactness theorem, which the book does not
state); `H̃_K` is a centrally symmetric hexagon in the sense of `IsCSHexagon`
(`crit_exists_isCSHexagon`, from the uniqueness and distinctness of the support lines in
Theorem 2.3.7); and the edges of `H_K` lie on six distinct symmetric support lines
(`crit_normal_injective`, `crit_normal_add_three`, `mm_isSupportLine_normal`), so that
Theorem 2.3.7 (4) applies to `H_K`. -/
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
    exact irr_eq_of_line_eq (ha.2.2.1 j _ (mm_isSupportLine_normal hK hv j)
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
