module

public import SmoothedPolygons.Ch2.MultiCurve
public import External.FejesToth
public import External.Gruber
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Packing densities (§2.1)

The greatest packing density `δ(K)` (Definition 2.1.1) and the greatest lattice packing density
`δ_L(K)` (Definition 2.1.2) of a convex disk, the cited fact `δ(K, L) = area(K)/det(L)` that
Definition 2.1.2 contains (Gruber, *Convex and Discrete Geometry*, Corollary 30.1), the theorem
of Fejes Tóth `δ(K) = δ_L(K)` for centrally symmetric disks (Theorem 2.1.3), the minimax density
`δ_min` and the worst disks `K_min`.

Conventions. The plane is `Fin 2 → ℝ` with Lebesgue measure `volume` (the area). The disk `B_r` of
the book is the Euclidean disk `euclidDisk r` (Mathlib's `Metric.closedBall` on `Fin 2 → ℝ` is a
square, for the sup metric). A packing is a *set* of convex disks, so that `Σ_{K' ∈ P}` sums over
its members. The ratios of the densities are taken in `[0, ∞]`, where `limsup` and `liminf` always
exist; a density *exists* when the upper and lower densities are finite and coincide. A lattice is
a `ℤ`-submodule of `ℝ²` that is discrete and spans `ℝ²` (`IsPlaneLattice`); its determinant
`det(L)` (Definition 2.3.2) is Mathlib's covolume, which is `|det(u₀, u₁)|` for every basis
`u₀, u₁` (`definition2_3_2`).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Filter Set Matrix
open scoped ENNReal

/-! ### Definition 2.1.1 -/

/-- The Euclidean disk `B_r = {x | x₀² + x₁² ≤ r²}` of radius `r` centered at the origin
(Definition 2.1.1). -/
def euclidDisk (r : ℝ) : Set (Fin 2 → ℝ) := {x | x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2}

/-- `K'` is a congruent copy of `K` (§2.1): its image `{A x + b | x ∈ K}` under a Euclidean
isometry, with `A` an orthogonal matrix. -/
def IsCongruentCopy (K K' : Set (Fin 2 → ℝ)) : Prop :=
  ∃ A ∈ Matrix.orthogonalGroup (Fin 2) ℝ, ∃ b : Fin 2 → ℝ, K' = (fun x ↦ A *ᵥ x + b) '' K

/-- A packing (§2.1): a family of convex disks, any two distinct members of which do not overlap,
that is, have disjoint interiors. -/
def IsPacking (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  (∀ K' ∈ P, IsConvexDisk K') ∧ P.Pairwise fun A B ↦ Disjoint (interior A) (interior B)

/-- A packing with congruent copies of `K` (Definition 2.1.1). -/
def IsPackingOfCopies (K : Set (Fin 2 → ℝ)) (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  IsPacking P ∧ ∀ K' ∈ P, IsCongruentCopy K K'

/-- The ratio `(1/area(B_r)) Σ_{K' ∈ P} area(K' ∩ B_r)` of Definition 2.1.1, in `[0, ∞]`. -/
noncomputable def packingRatio (P : Set (Set (Fin 2 → ℝ))) (r : ℝ) : ℝ≥0∞ :=
  (∑' K' : P, volume ((K' : Set (Fin 2 → ℝ)) ∩ euclidDisk r)) / volume (euclidDisk r)

/-- The upper density `limsup_{r → ∞} (1/area(B_r)) Σ_{K' ∈ P} area(K' ∩ B_r)` of a packing
(Definition 2.1.1). -/
noncomputable def upperDensity (P : Set (Set (Fin 2 → ℝ))) : ℝ≥0∞ :=
  limsup (packingRatio P) atTop

/-- The lower density `liminf_{r → ∞} (1/area(B_r)) Σ_{K' ∈ P} area(K' ∩ B_r)` of a packing
(Definition 2.1.1). -/
noncomputable def lowerDensity (P : Set (Set (Fin 2 → ℝ))) : ℝ≥0∞ :=
  liminf (packingRatio P) atTop

/-- The density of `P` exists (Definition 2.1.1): the upper and lower densities exist (are
finite) and coincide. -/
def HasDensity (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  upperDensity P ≠ ∞ ∧ upperDensity P = lowerDensity P

/-- The density `δ(K, P)` of a packing (Definition 2.1.1): the common value of the upper and
lower densities, when the density exists (`HasDensity`). -/
noncomputable def packingDensity (P : Set (Set (Fin 2 → ℝ))) : ℝ :=
  (upperDensity P).toReal

/-- **Definition 2.1.1** (greatest packing density).
`δ(K) = sup {δ(K, P) | δ(K, P) exists, and P is a packing with congruent copies of K}`. -/
noncomputable def greatestPackingDensity (K : Set (Fin 2 → ℝ)) : ℝ :=
  sSup {d | ∃ P, IsPackingOfCopies K P ∧ HasDensity P ∧ packingDensity P = d}

/-! ### Definition 2.1.2 -/

/-- A lattice (§2.1): a discrete additive subgroup of `ℝ²` of full rank, that is, a discrete
`ℤ`-submodule of `ℝ²` that spans `ℝ²` over `ℝ` (Mathlib's `IsZLattice ℝ L`). -/
def IsPlaneLattice (L : Submodule ℤ (Fin 2 → ℝ)) : Prop :=
  DiscreteTopology L ∧ Submodule.span ℝ (L : Set (Fin 2 → ℝ)) = ⊤

/-- The determinant `det(L)` of a lattice (Definition 2.3.2), also called its covolume: the area
of a fundamental domain, which is `|det(u₀, u₁)|` for every basis `u₀, u₁` of `L`
(`definition2_3_2`). -/
noncomputable def latticeDet (L : Submodule ℤ (Fin 2 → ℝ)) : ℝ :=
  ZLattice.covolume L

/-- `K + L` is a packing (a lattice packing, §2.1): the translates `K + l`, `l ∈ L`, have
pairwise disjoint interiors. -/
def IsLatticePacking (K : Set (Fin 2 → ℝ)) (L : Submodule ℤ (Fin 2 → ℝ)) : Prop :=
  ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' →
    Disjoint (interior ((fun x ↦ x + l) '' K)) (interior ((fun x ↦ x + l') '' K))

/-- The ratio `Σ_{l ∈ L} area(B_r ∩ (K + l)) / area(B_r)` of Definition 2.1.2, in `[0, ∞]`. -/
noncomputable def latticeRatio (K : Set (Fin 2 → ℝ)) (L : Submodule ℤ (Fin 2 → ℝ)) (r : ℝ) :
    ℝ≥0∞ :=
  (∑' l : L, volume (euclidDisk r ∩ (fun x ↦ x + (l : Fin 2 → ℝ)) '' K)) / volume (euclidDisk r)

/-- The upper density of the lattice packing `K + L` (Definition 2.1.2). -/
noncomputable def upperLatticeDensity (K : Set (Fin 2 → ℝ)) (L : Submodule ℤ (Fin 2 → ℝ)) :
    ℝ≥0∞ :=
  limsup (latticeRatio K L) atTop

/-- The lower density of the lattice packing `K + L` (Definition 2.1.2). -/
noncomputable def lowerLatticeDensity (K : Set (Fin 2 → ℝ)) (L : Submodule ℤ (Fin 2 → ℝ)) :
    ℝ≥0∞ :=
  liminf (latticeRatio K L) atTop

/-- The density `δ(K, L)` of the lattice packing `K + L` (Definition 2.1.2): the common value of
its upper and lower densities, which is `area(K)/det(L)` (`definition2_1_2`). -/
noncomputable def latticePackingDensity (K : Set (Fin 2 → ℝ)) (L : Submodule ℤ (Fin 2 → ℝ)) :
    ℝ :=
  (upperLatticeDensity K L).toReal

/-- **Definition 2.1.2** (greatest lattice packing density).
`δ_L(K) = sup {δ(K, L) | L a lattice in ℝ² such that K + L is a packing}`. -/
noncomputable def greatestLatticePackingDensity (K : Set (Fin 2 → ℝ)) : ℝ :=
  sSup {d | ∃ L, IsPlaneLattice L ∧ IsLatticePacking K L ∧ latticePackingDensity K L = d}

/-- **Definition 2.1.2** (the cited fact it contains; Gruber, *Convex and Discrete Geometry*,
Corollary 30.1). Given a convex disk `K` and a lattice `L` such that the `L`-translates of `K`
have disjoint interiors, the upper and lower densities of the lattice packing `K + L` coincide
and are both equal to `δ(K, L) = area(K)/det(L)`. -/
theorem definition2_1_2 {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K)
    {L : Submodule ℤ (Fin 2 → ℝ)} (hL : IsPlaneLattice L) (hKL : IsLatticePacking K L) :
    upperLatticeDensity K L = ENNReal.ofReal (volume.real K / latticeDet L) ∧
      lowerLatticeDensity K L = ENNReal.ofReal (volume.real K / latticeDet L) := by
  -- Gruber's statement (`External.gruber_corollary_30_1`) for a basis `b` of `L`: his lattice
  -- `ℤ b₀ + ℤ b₁` is `L`, his `d(L) = |det b|` is the covolume, his ball is `B_r`.
  obtain ⟨hd, hs⟩ := hL
  have : IsZLattice ℝ L := ⟨hs⟩
  have hrank : Module.finrank ℤ L = 2 := by rw [ZLattice.rank ℝ L]; simp
  let bZ : Module.Basis (Fin 2) ℤ L := Module.finBasisOfFinrankEq ℤ L hrank
  let bR : Module.Basis (Fin 2) ℝ (Fin 2 → ℝ) := bZ.ofZLatticeBasis ℝ L
  have hlat : External.Gruber.lattice bR = L := bZ.ofZLatticeBasis_span ℝ L
  have hdet : External.Gruber.latticeDet bR = latticeDet L := by
    rw [latticeDet, ZLattice.covolume_eq_det L bZ, External.Gruber.latticeDet]
    congr 2
    ext i j
    simp [bR, Module.Basis.ofZLatticeBasis_apply]
  have hpack : External.Gruber.IsLatticePacking K bR := by
    rw [External.Gruber.IsLatticePacking, hlat]
    exact hKL
  have hball : ∀ r, External.Gruber.ball (ι := Fin 2) r = euclidDisk r := by
    intro r
    ext x
    simp [External.Gruber.ball, euclidDisk, Fin.sum_univ_two]
  have hratio : External.Gruber.densityRatio K bR = latticeRatio K L := by
    funext r
    rw [External.Gruber.densityRatio, latticeRatio, hball]
    congr 1
    let e : External.Gruber.lattice bR ≃ L := Equiv.subtypeEquivRight fun x ↦ by rw [hlat]
    rw [← e.tsum_eq]
    refine tsum_congr fun l ↦ ?_
    rw [inter_comm]
    rfl
  obtain ⟨h1, h2⟩ := External.gruber_corollary_30_1 hK hpack
  rw [External.Gruber.upperDensity, hratio, hdet] at h1
  rw [External.Gruber.lowerDensity, hratio, hdet] at h2
  exact ⟨h1, h2⟩

/-- The density of a lattice packing is `δ(K, L) = area(K)/det(L)` (Definition 2.1.2). -/
theorem ch2_latticePackingDensity_eq {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K)
    {L : Submodule ℤ (Fin 2 → ℝ)} (hL : IsPlaneLattice L) (hKL : IsLatticePacking K L) :
    latticePackingDensity K L = volume.real K / latticeDet L := by
  rw [latticePackingDensity, (definition2_1_2 hK hL hKL).1, ENNReal.toReal_ofReal]
  exact div_nonneg measureReal_nonneg ENNReal.toReal_nonneg

/-! ### Theorem 2.1.3 -/

/-- **Theorem 2.1.3** (Fejes Tóth; `thm:fejes-toth-packing`, equation `eqn:fejes-toth`). If
`K ⊂ ℝ²` is a centrally symmetric convex disk, then `δ(K) = δ_L(K)`. -/
theorem theorem2_1_3 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) :
    greatestPackingDensity K = greatestLatticePackingDensity K := by
  sorry

/-! ### The minimax density and the worst disks -/

/-- The minimax density `δ_min = inf_{K ∈ 𝔎_ccs} δ(K)` (§2.1): the least greatest packing density
among all centrally symmetric convex disks. -/
noncomputable def minimaxDensity : ℝ :=
  sInf {d | ∃ K, IsCCSDisk K ∧ greatestPackingDensity K = d}

/-- `K` is a worst disk `K_min` (§2.1): a centrally symmetric convex disk with
`δ(K_min) = δ_min`, the worst greatest packing density. -/
def IsWorstDisk (K : Set (Fin 2 → ℝ)) : Prop :=
  IsCCSDisk K ∧ greatestPackingDensity K = minimaxDensity

/-- `K` has the worst greatest density lattice packing (Lemma 2.2.5): a centrally symmetric convex
disk whose greatest lattice packing density is least among all centrally symmetric convex disks.
By Theorem 2.1.3 these are the worst disks `K_min` (`ch2_isWorstLatticeDisk_iff_isWorstDisk`). -/
def IsWorstLatticeDisk (K : Set (Fin 2 → ℝ)) : Prop :=
  IsCCSDisk K ∧
    ∀ K', IsCCSDisk K' → greatestLatticePackingDensity K ≤ greatestLatticePackingDensity K'

lemma ch2_greatestPackingDensity_nonneg (K : Set (Fin 2 → ℝ)) : 0 ≤ greatestPackingDensity K :=
  Real.sSup_nonneg fun _ ⟨_, _, _, hd⟩ ↦ hd ▸ ENNReal.toReal_nonneg

/-- A centrally symmetric convex disk is a worst disk iff its greatest packing density is at most
that of every centrally symmetric convex disk. -/
lemma ch2_isWorstDisk_iff {K : Set (Fin 2 → ℝ)} :
    IsWorstDisk K ↔
      IsCCSDisk K ∧ ∀ K', IsCCSDisk K' → greatestPackingDensity K ≤ greatestPackingDensity K' := by
  have hbdd : BddBelow {d | ∃ K, IsCCSDisk K ∧ greatestPackingDensity K = d} :=
    ⟨0, fun _ ⟨K', _, hd⟩ ↦ hd ▸ ch2_greatestPackingDensity_nonneg K'⟩
  constructor
  · rintro ⟨hK, h⟩
    exact ⟨hK, fun K' hK' ↦ h ▸ csInf_le hbdd ⟨K', hK', rfl⟩⟩
  · rintro ⟨hK, h⟩
    refine ⟨hK, (IsLeast.csInf_eq (s := {d | ∃ K, IsCCSDisk K ∧ greatestPackingDensity K = d})
      ⟨⟨K, hK, rfl⟩, ?_⟩).symm⟩
    rintro _ ⟨K', hK', rfl⟩
    exact h K' hK'

/-- By Theorem 2.1.3, the disks with the worst greatest density lattice packing are the worst disks
`K_min`. -/
lemma ch2_isWorstLatticeDisk_iff_isWorstDisk {K : Set (Fin 2 → ℝ)} :
    IsWorstLatticeDisk K ↔ IsWorstDisk K := by
  rw [ch2_isWorstDisk_iff, IsWorstLatticeDisk]
  refine and_congr_right fun hK ↦ forall_congr' fun K' ↦ imp_congr_right fun hK' ↦ ?_
  rw [theorem2_1_3 hK, theorem2_1_3 hK']

end SmoothedPolygons
