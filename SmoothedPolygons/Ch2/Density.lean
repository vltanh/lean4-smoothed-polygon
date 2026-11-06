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

/-- The image `{A x + b | x ∈ K}` of a convex set under an affine map is convex. -/
private lemma dens_convex_image {K : Set (Fin 2 → ℝ)} (hK : Convex ℝ K)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) : Convex ℝ ((fun x ↦ A *ᵥ x + b) '' K) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a c ha hc hac
  refine ⟨a • x + c • y, hK hx hy ha hc hac, ?_⟩
  change A *ᵥ (a • x + c • y) + b = a • (A *ᵥ x + b) + c • (A *ᵥ y + b)
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_add, smul_add,
    add_add_add_comm, ← add_smul, hac, one_smul]

/-- A translate `K + l` of a convex disk is a convex disk. -/
private lemma dens_isConvexDisk_translate {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K)
    (l : Fin 2 → ℝ) : IsConvexDisk ((fun x ↦ x + l) '' K) := by
  obtain ⟨hc, hcomp, hint⟩ := hK
  refine ⟨?_, hcomp.image (continuous_id.add continuous_const), ?_⟩
  · simpa only [Matrix.one_mulVec] using dens_convex_image hc 1 l
  · have := (Homeomorph.addRight l).image_interior K
    rw [Homeomorph.coe_addRight] at this
    exact this ▸ hint.image _

/-- The translates `K + l` of a nonempty compact set are distinct: if `K + l = K + l'`, then a
point `x ∈ K` maximizing `⟨x, l - l'⟩` has `x + (l - l') ∈ K`, so `|l - l'|² ≤ 0`. -/
private lemma dens_translate_injective {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) : Function.Injective fun l : Fin 2 → ℝ ↦ (fun x ↦ x + l) '' K := by
  intro l l' h
  obtain ⟨x, hxK, hmax⟩ := hK.exists_isMaxOn hne
    (f := fun y : Fin 2 → ℝ ↦ y 0 * (l 0 - l' 0) + y 1 * (l 1 - l' 1))
    (Continuous.continuousOn (by fun_prop))
  have h' : (fun x ↦ x + l) '' K = (fun x ↦ x + l') '' K := h
  have hx : x + l ∈ (fun y ↦ y + l') '' K := h' ▸ mem_image_of_mem _ hxK
  obtain ⟨y, hyK, hy⟩ := hx
  have h0 : y 0 = x 0 + l 0 - l' 0 := by
    have := congr_fun hy 0
    simp only [Pi.add_apply] at this
    linarith
  have h1 : y 1 = x 1 + l 1 - l' 1 := by
    have := congr_fun hy 1
    simp only [Pi.add_apply] at this
    linarith
  have hle := isMaxOn_iff.mp hmax y hyK
  simp only [h0, h1] at hle
  have hsq : (l 0 - l' 0) ^ 2 + (l 1 - l' 1) ^ 2 ≤ 0 := by nlinarith
  have e0 : l 0 - l' 0 = 0 := (pow_eq_zero_iff (n := 2) two_ne_zero).mp
    (le_antisymm (by nlinarith [sq_nonneg (l 1 - l' 1)]) (sq_nonneg _))
  have e1 : l 1 - l' 1 = 0 := (pow_eq_zero_iff (n := 2) two_ne_zero).mp
    (le_antisymm (by nlinarith [sq_nonneg (l 0 - l' 0)]) (sq_nonneg _))
  funext i
  fin_cases i
  · exact sub_eq_zero.mp e0
  · exact sub_eq_zero.mp e1

/-- For convex sets with pairwise disjoint interiors, `Σ area(A ∩ D) ≤ area(D)`: the boundary of
a convex set has measure zero (`Convex.addHaar_frontier`), and the interiors are disjoint. -/
private lemma dens_tsum_le_volume {𝒜 : Set (Set (Fin 2 → ℝ))} (hconv : ∀ A ∈ 𝒜, Convex ℝ A)
    (hdisj : 𝒜.Pairwise fun A B ↦ Disjoint (interior A) (interior B)) {D : Set (Fin 2 → ℝ)}
    (hD : MeasurableSet D) : ∑' A : 𝒜, volume ((A : Set (Fin 2 → ℝ)) ∩ D) ≤ volume D := by
  calc ∑' A : 𝒜, volume ((A : Set (Fin 2 → ℝ)) ∩ D)
      ≤ ∑' A : 𝒜, volume (interior (A : Set (Fin 2 → ℝ)) ∩ D) := by
        refine tsum_le_tsum fun A ↦ ?_
        calc volume ((A : Set (Fin 2 → ℝ)) ∩ D)
            ≤ volume (interior (A : Set (Fin 2 → ℝ)) ∩ D ∪ frontier (A : Set (Fin 2 → ℝ))) := by
              refine measure_mono fun x ⟨hxA, hxD⟩ ↦ ?_
              by_cases hx : x ∈ interior (A : Set (Fin 2 → ℝ))
              · exact Or.inl ⟨hx, hxD⟩
              · exact Or.inr ⟨subset_closure hxA, hx⟩
          _ ≤ volume (interior (A : Set (Fin 2 → ℝ)) ∩ D) +
              volume (frontier (A : Set (Fin 2 → ℝ))) := measure_union_le _ _
          _ = volume (interior (A : Set (Fin 2 → ℝ)) ∩ D) := by
              rw [Convex.addHaar_frontier volume (hconv A A.2), add_zero]
    _ ≤ volume (⋃ A : 𝒜, interior (A : Set (Fin 2 → ℝ)) ∩ D) :=
        tsum_meas_le_meas_iUnion_of_disjoint volume
          (fun _ ↦ isOpen_interior.measurableSet.inter hD)
          (fun A B hAB ↦ (hdisj A.2 B.2 fun h ↦ hAB (Subtype.ext h)).mono inter_subset_left
            inter_subset_left)
    _ ≤ volume D := measure_mono (iUnion_subset fun _ ↦ inter_subset_right)

/-- Every family of convex sets with pairwise disjoint interiors has upper density at most `1`. -/
private lemma dens_upperDensity_le_one {𝒜 : Set (Set (Fin 2 → ℝ))}
    (hconv : ∀ A ∈ 𝒜, Convex ℝ A)
    (hdisj : 𝒜.Pairwise fun A B ↦ Disjoint (interior A) (interior B)) :
    External.FejesToth.upperDensity 𝒜 ≤ 1 := by
  refine limsup_le_of_le (h := Eventually.of_forall fun r ↦ ENNReal.div_le_of_le_mul ?_)
  rw [one_mul]
  exact dens_tsum_le_volume hconv hdisj (isClosed_le (by fun_prop) continuous_const).measurableSet

/-- `K + L` is a packing in the sense of the source iff the `L`-translates of `K` have disjoint
interiors. -/
private lemma dens_isPacking_translates_iff {K : Set (Fin 2 → ℝ)}
    (hinj : Function.Injective fun l : Fin 2 → ℝ ↦ (fun x ↦ x + l) '' K)
    (L : Submodule ℤ (Fin 2 → ℝ)) :
    External.FejesToth.IsPacking (External.FejesToth.translates K L) ↔ IsLatticePacking K L := by
  constructor
  · intro hP l hl l' hl' hll'
    exact hP (mem_range_self (⟨l, hl⟩ : L)) (mem_range_self (⟨l', hl'⟩ : L))
      fun h ↦ hll' (hinj h)
  · rintro hKL _ ⟨l, rfl⟩ _ ⟨l', rfl⟩ hne
    exact hKL l l.2 l' l'.2 fun h ↦ hne (by simp only [h])

/-- The ratio of the packing `K + L` is the ratio of the lattice packing `K + L`. -/
private lemma dens_packingRatio_translates {K : Set (Fin 2 → ℝ)}
    (hinj : Function.Injective fun l : Fin 2 → ℝ ↦ (fun x ↦ x + l) '' K)
    (L : Submodule ℤ (Fin 2 → ℝ)) :
    packingRatio (External.FejesToth.translates K L) = latticeRatio K L := by
  funext r
  rw [packingRatio, latticeRatio, External.FejesToth.translates,
    tsum_range (g := fun l : L ↦ (fun x ↦ x + (l : Fin 2 → ℝ)) '' K)
      (fun A ↦ volume (A ∩ euclidDisk r)) (hinj.comp Subtype.val_injective)]
  congr 1
  exact tsum_congr fun l ↦ by rw [inter_comm]

/-- **Theorem 2.1.3** (Fejes Tóth; `thm:fejes-toth-packing`, equation `eqn:fejes-toth`). If
`K ⊂ ℝ²` is a centrally symmetric convex disk, then `δ(K) = δ_L(K)`.

The book cites Fejes Tóth (`External.fejes_toth`, whose `δ` and `δ_L` are suprema of upper
densities) and Definition 2.1.2's formula `δ(K, L) = area(K)/det(L)` (`definition2_1_2`). The
book's `δ(K)` is at most the source's `δ(K)` (a packing whose density exists has upper density
equal to its density, and every packing ratio is at most `1`); the source's `δ(K)` is its `δ_L(K)`;
the source's `δ_L(K)` is at most the book's `δ_L(K)`, since each lattice packing has upper density
`area(K)/det(L)`; and the book's `δ_L(K)` is at most its `δ(K)`, since a lattice packing `K + L`
is a packing of congruent copies of `K` whose density exists. -/
theorem theorem2_1_3 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) :
    greatestPackingDensity K = greatestLatticePackingDensity K := by
  obtain ⟨hconv, hcomp, hint, hsymm⟩ := hK
  have hKd : IsConvexDisk K := ⟨hconv, hcomp, hint⟩
  have hinj := dens_translate_injective hcomp (hint.mono interior_subset)
  have hU : ∀ L, upperDensity (External.FejesToth.translates K L) = upperLatticeDensity K L :=
    fun L ↦ by rw [upperDensity, upperLatticeDensity, dens_packingRatio_translates hinj]
  have hLo : ∀ L, lowerDensity (External.FejesToth.translates K L) = lowerLatticeDensity K L :=
    fun L ↦ by rw [lowerDensity, lowerLatticeDensity, dens_packingRatio_translates hinj]
  -- The source's `δ(K)` is at most `1`.
  have hle1 : External.FejesToth.packingDensity K ≤ 1 := by
    refine iSup₂_le fun 𝒜 h𝒜 ↦ iSup_le fun hcong ↦ dens_upperDensity_le_one ?_ h𝒜
    intro A hA
    obtain ⟨M, -, v, rfl⟩ := hcong A hA
    exact dens_convex_image hconv M v
  -- The book's `δ(K)` is at most the source's `δ(K)`.
  have h1 : greatestPackingDensity K ≤ (External.FejesToth.packingDensity K).toReal := by
    refine Real.sSup_le ?_ ENNReal.toReal_nonneg
    rintro _ ⟨P, ⟨hP, hcop⟩, -, rfl⟩
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hle1)
      (le_iSup₂_of_le P hP.2 (le_iSup_of_le hcop le_rfl))
  -- The source's `δ_L(K)` is at most the book's `δ_L(K)`.
  have hbddL : BddAbove
      {d | ∃ L, IsPlaneLattice L ∧ IsLatticePacking K L ∧ latticePackingDensity K L = d} := by
    refine ⟨1, ?_⟩
    rintro _ ⟨L, -, hKL, rfl⟩
    have : upperLatticeDensity K L ≤ 1 := by
      rw [← hU L]
      refine dens_upperDensity_le_one ?_ ((dens_isPacking_translates_iff hinj L).mpr hKL)
      rintro _ ⟨l, rfl⟩
      exact (dens_isConvexDisk_translate hKd l).1
    exact (ENNReal.toReal_mono ENNReal.one_ne_top this).trans_eq ENNReal.toReal_one
  have h2 : (External.FejesToth.latticePackingDensity K).toReal ≤
      greatestLatticePackingDensity K := by
    refine ENNReal.toReal_le_of_le_ofReal
      (Real.sSup_nonneg fun _ ⟨_, _, _, hd⟩ ↦ hd ▸ ENNReal.toReal_nonneg) ?_
    refine iSup₂_le fun L hL ↦ iSup_le fun hP ↦ ?_
    have hKL : IsLatticePacking K L := (dens_isPacking_translates_iff hinj L).mp hP
    change upperDensity (External.FejesToth.translates K L) ≤ _
    rw [hU, (definition2_1_2 hKd hL hKL).1]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← ch2_latticePackingDensity_eq hKd hL hKL]
    exact le_csSup hbddL ⟨L, hL, hKL, rfl⟩
  -- The book's `δ_L(K)` is at most its `δ(K)`: lattice packings are packings of congruent copies.
  have h3 : greatestLatticePackingDensity K ≤ greatestPackingDensity K := by
    have hbddP : BddAbove
        {d | ∃ P, IsPackingOfCopies K P ∧ HasDensity P ∧ packingDensity P = d} := by
      refine ⟨1, ?_⟩
      rintro _ ⟨P, ⟨hP, -⟩, -, rfl⟩
      exact (ENNReal.toReal_mono ENNReal.one_ne_top (dens_upperDensity_le_one
        (fun A hA ↦ (hP.1 A hA).1) hP.2)).trans_eq ENNReal.toReal_one
    refine Real.sSup_le ?_ (Real.sSup_nonneg fun _ ⟨_, _, _, hd⟩ ↦ hd ▸ ENNReal.toReal_nonneg)
    rintro _ ⟨L, hL, hKL, rfl⟩
    obtain ⟨hu, hl⟩ := definition2_1_2 hKd hL hKL
    refine le_csSup hbddP ⟨External.FejesToth.translates K L, ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · rintro _ ⟨l, rfl⟩
      exact dens_isConvexDisk_translate hKd l
    · exact (dens_isPacking_translates_iff hinj L).mpr hKL
    · rintro _ ⟨l, rfl⟩
      exact ⟨1, one_mem _, l, by simp only [Matrix.one_mulVec]⟩
    · exact ⟨by rw [hU, hu]; exact ENNReal.ofReal_ne_top, by rw [hU, hLo, hu, hl]⟩
    · rw [packingDensity, latticePackingDensity, hU]
  rw [External.fejes_toth ⟨hconv, hcomp, hint⟩ hsymm] at h1
  exact le_antisymm (h1.trans h2) h3

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
