module

public import SmoothedPolygons.Ch2.Reinhardt
public import External.Mahler1947
public import External.MinkowskiMahler

/-!
# Mahler's approach (§2.3)

Admissible and critical lattices, the minimal determinant `Δ(K)` and irreducible disks
(Definitions 2.3.1–2.3.5), the theorems of Minkowski and Mahler on critical lattices and
circumscribed hexagons (Theorems 2.3.6 and 2.3.7, cited), Mahler's critical hexagons
(Definition 2.3.8), and their relation to Reinhardt's (Theorem 2.3.9, Corollary 2.3.10).

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

/-- **Theorem 2.3.9** (`thm:min-critical`). Let `K ∈ 𝔎_ccs`. Let `H_K` be a centrally symmetric
hexagon of least area circumscribing `K`. Then `H_K` is a critical hexagon in the sense of
Definition 2.3.8. -/
theorem theorem2_3_9 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {v : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) : IsCriticalHexagon K (hexagonOf v) := by
  sorry

/-- **Corollary 2.3.10**. Let `K = K_min` have worst greatest packing density. Then `K` is
irreducible. -/
theorem corollary2_3_10 {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) : IsIrreducible K := by
  sorry

end SmoothedPolygons
