module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Convex.Measure
public import Basic.Analysis.Convex.CircumscribedPolygon
public import Basic.Analysis.Convex.HexagonLattice

/-!
# Fejes Tóth's theorem: lattice packings are densest for centrally symmetric disks

Cited as Theorem 2.1.3 of Hales–Vajjha, *Packings of Smoothed Polygons*, from L. Fejes Tóth,
*Some packing and covering theorems*, Acta Sci. Math. Szeged 12(A) (1950), 62–67, and
*Lagerungen in der Ebene auf der Kugel und im Raum*, Springer, 1953 (3rd edition with G. Fejes
Tóth and W. Kuperberg, 2023): if `K` is a centrally symmetric convex disk, then the greatest
density of a packing of congruent copies of `K` equals the greatest density of a lattice packing
of translates of `K`, `δ(K) = δ_L(K)`.

Definitions, in the terms of the source. The plane is `Fin 2 → ℝ` with Lebesgue measure. A
*packing* is a family of sets with pairwise disjoint interiors. The *upper density* of a family
`𝒜` is `limsup_{r → ∞} Σ_{A ∈ 𝒜} area(A ∩ D_r) / area(D_r)`, where `D_r` is the circular disk of
radius `r` about the origin. `δ(K)` is the supremum of the upper densities of the packings of
congruent copies of `K` (images under Euclidean motions `x ↦ A x + b`, `A` orthogonal), and
`δ_L(K)` the supremum of the upper densities of the lattice packings `{K + l | l ∈ L}`, `L` a
lattice (a discrete subgroup of `ℝ²` spanning `ℝ²`). Taking suprema of upper densities gives the
strongest form of the statement (no packing of congruent copies is denser, even in the sense of
upper density, than the best lattice packing). Densities take values in `[0, ∞]`.

Status: `fejes_toth` is proved from Fejes Tóth's cell lemma `FejesToth.ft_cell_decomposition`,
which is left as `sorry` (the planar-topology core; its docstring gives the argument). The lattice
half `|K| / t_K(6) ≤ δ_L(K)` and everything else are proved; see the section *Proof* below.
-/

@[expose] public section

namespace External

open MeasureTheory Filter Set Matrix
open scoped ENNReal

namespace FejesToth

/-- The circular disk `D_r = {x | x₀² + x₁² ≤ r²}`. -/
def disk (r : ℝ) : Set (Fin 2 → ℝ) := {x | x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2}

/-- A convex disk (convex domain): a compact convex set with nonempty interior. -/
def IsConvexDisk (K : Set (Fin 2 → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- `K` is centrally symmetric (about the origin). -/
def IsCentrallySymmetric (K : Set (Fin 2 → ℝ)) : Prop := ∀ x ∈ K, -x ∈ K

/-- `K'` is congruent to `K`: `K' = {A x + b | x ∈ K}` with `A` orthogonal. -/
def IsCongruent (K K' : Set (Fin 2 → ℝ)) : Prop :=
  ∃ A ∈ Matrix.orthogonalGroup (Fin 2) ℝ, ∃ b : Fin 2 → ℝ, K' = (fun x ↦ A *ᵥ x + b) '' K

/-- A packing: a family of sets with pairwise disjoint interiors. -/
def IsPacking (𝒜 : Set (Set (Fin 2 → ℝ))) : Prop :=
  𝒜.Pairwise fun A B ↦ Disjoint (interior A) (interior B)

/-- The upper density `limsup_{r → ∞} Σ_{A ∈ 𝒜} area(A ∩ D_r) / area(D_r)` of a family. -/
noncomputable def upperDensity (𝒜 : Set (Set (Fin 2 → ℝ))) : ℝ≥0∞ :=
  limsup (fun r ↦ (∑' A : 𝒜, volume ((A : Set (Fin 2 → ℝ)) ∩ disk r)) / volume (disk r)) atTop

/-- The greatest packing density `δ(K)`: the supremum of the upper densities of the packings of
congruent copies of `K`. -/
noncomputable def packingDensity (K : Set (Fin 2 → ℝ)) : ℝ≥0∞ :=
  ⨆ (𝒜 : Set (Set (Fin 2 → ℝ))) (_ : IsPacking 𝒜) (_ : ∀ A ∈ 𝒜, IsCongruent K A),
    upperDensity 𝒜

/-- A lattice: a discrete subgroup of `ℝ²` that spans `ℝ²`. -/
def IsLattice (L : Submodule ℤ (Fin 2 → ℝ)) : Prop :=
  DiscreteTopology L ∧ Submodule.span ℝ (L : Set (Fin 2 → ℝ)) = ⊤

/-- The family of translates `{K + l | l ∈ L}`. -/
def translates (K : Set (Fin 2 → ℝ)) (L : Submodule ℤ (Fin 2 → ℝ)) : Set (Set (Fin 2 → ℝ)) :=
  range fun l : L ↦ (fun x ↦ x + (l : Fin 2 → ℝ)) '' K

/-- The greatest lattice packing density `δ_L(K)`: the supremum of the upper densities of the
lattice packings of `K`. -/
noncomputable def latticePackingDensity (K : Set (Fin 2 → ℝ)) : ℝ≥0∞ :=
  ⨆ (L : Submodule ℤ (Fin 2 → ℝ)) (_ : IsLattice L) (_ : IsPacking (translates K L)),
    upperDensity (translates K L)


/-! ## Proof

The proof follows L. Fejes Tóth (1950) in the form of K. Böröczky Jr., *Finite packing and
covering by congruent convex domains*, Discrete Comput. Geom. 30 (2003), 185–193 (Lemma 5, §3),
and of J. Pach and P. K. Agarwal, *Combinatorial Geometry*, Ch. 3. Write `t_K(k)` for the least
area of a polygon with at most `k` sides containing `K` (`PlaneConvex.minCircumscribedArea`, the
infimum over `k` closed half-planes containing `K` of the area of their intersection).

1. `δ_L(K) ≤ δ(K)` (`ft_latticePackingDensity_le_packingDensity`): a lattice packing is a packing
   of congruent copies (`A = 1`).
2. **Dowker's theorem** (`PlaneConvex.minCircumscribedArea_add_le`, in `Basic`): if `m + n = 2k`
   then `2 t_K(k) ≤ t_K(m) + t_K(n)`. Proof without the area formula of Dowker's paper: merge the
   normal angles of a circumscribed `m`-gon `P` and `n`-gon `Q` (support lines of `K`) in cyclic
   order and give them alternately to two `k`-gons `X, Y`; then `X ∩ Y = P ∩ Q` and
   `X ∪ Y ⊆ P ∪ Q`, since the normals of the support lines violated by a point form an arc of
   length `< π` (`PlaneConvex.violates_of_le_of_le`: the support function is sublinear), so a point
   of `X` violates at most one constraint of `Y`. Measure additivity
   (`MeasureTheory.measure_union_add_inter`) gives `|X| + |Y| ≤ |P| + |Q|`. Sorting uses
   `Tuple.sort`, angles mod `2π` use `toIcoMod`.
   Consequences: `t_K(k) < ∞` for `k ≥ 4`, `t_K` is antitone, and the supporting line at `6`:
   `t_K(6) + 6d ≤ t_K(s) + s d` for `s ≥ 3`, `d = t_K(6) - t_K(7)`
   (`PlaneConvex.minCircumscribedArea_six_add_le`); `t_K` is invariant under Euclidean motions
   (`PlaneConvex.minCircumscribedArea_image_motion`, via `Measure.addHaar_image_linearMap`).
3. **Fejes Tóth's cell lemma** (`ft_cell_decomposition`, **the only `sorry`**): `n ≥ 1`
   non-overlapping convex disks in a bounded convex polygon `Q` cut out by `m` half-planes lie in
   non-overlapping convex polygons `C_i ⊆ Q`, `C_i` cut out by `s_i ≥ 3` half-planes, with
   `∑ s_i ≤ 6n + m - 6`. See its docstring for the argument and the infrastructure it needs.
4. **Fejes Tóth's inequality** (`ft_card_mul_le_volume`): `n` congruent copies of `K` packed in a
   convex polygon `Q` with `m ≤ 6` sides satisfy `n t_K(6) ≤ |Q|`:
   `|Q| ≥ ∑ |C_i|` (non-overlapping convex sets, `Convex.addHaar_frontier`), `|C_i| ≥ t_K(s_i)`
   (2, motion invariance), `∑ t_K(s_i) ≥ n t_K(6) - d (∑ s_i - 6n) ≥ n t_K(6)` (2 and 3).
5. **Densities** (`ft_upperDensity_le`): every packing of congruent copies of `K` has upper
   density at most `|K| / t_K(6)`. Cover `D_r` by the half-open grid squares of side `L = √r`
   (`ft_cell`) meeting it; these lie in `D_{r+2L}`, so there are at most `|D_{r+2L}| / L²` of
   them (`measure_biUnion_finset`); the copies meeting a square lie in the square enlarged by the
   diameter `D` of `K` (`ft_exists_diam_bound`), a rectangle, so by 4 at most
   `(L + 2D)² / t_K(6)` of them; hence the density in `D_r` is at most
   `((r + 2L)/r)² ((L + 2D)/L)² |K| / t_K(6) → |K| / t_K(6)` (`|D_ρ| = ρ² |D_1|`,
   `Measure.addHaar_smul`; `Filter.limsup_le_limsup`, `Filter.Tendsto.limsup_eq`).
6. **Dowker, symmetric case** (`PlaneConvex.exists_symm_le`, in `Basic`): for `K = -K`, merging a
   circumscribed hexagon `P` with `-P` gives two centrally symmetric hexagons with
   `|X| + |Y| ≤ 2|P|`; so `t_K(6)` is the infimum of the areas of the centrally symmetric
   circumscribed hexagons `{x | |⟨u_i, x⟩| ≤ h_K(u_i), i < 3}`
   (`ft_minCircumscribedArea_six_eq_iInf_symm`).
7. **Lattice tiling by a symmetric hexagon** (`ft_hexagon_lattice`, from
   `Basic/Analysis/Convex/HexagonLattice.lean`): such a hexagon of finite area is, in normal form,
   `{|⟨u, x⟩|, |⟨v, x⟩|, |⟨αu + βv, x⟩| ≤ 1}` (`PlaneConvex.circPolygon_symm_eq_symmHexagon`; a
   degenerate one is a slab of infinite area), and is a fundamental domain of a lattice
   `ℤ w₁ + ℤ w₂` (`PlaneConvex.exists_lattice_symmHexagon`: a parallelogram, or a genuine hexagon
   whose covering property is the Voronoi argument for a positive definite quadratic form); the
   lattice is discrete and spanning (`Module.Basis`, `ZSpan`), and `K + L` is a packing.
8. **Lattice densities** (`ft_le_upperDensity_translates`): if `P ⊇ K` is bounded and `P + L`
   covers the plane, the upper density of `K + L` is at least `|K| / |P|` (count the lattice
   points of `D_{r-R}`, finitely many by `Metric.finite_isBounded_inter_isClosed`).
9. **Conclusion** (`ft_div_le_latticePackingDensity`, `fejes_toth`):
   `δ(K) ≤ |K| / t_K(6) = sup_P |K| / |P| ≤ δ_L(K)` (5, 6, 7, 8; `ENNReal.inv_iInf`).

On the planar topology. Steps 1–2 and 4–9 use no planar topology beyond the cyclic order of normal
angles. All of it is concentrated in the cell lemma 3, which needs (a) the existence of the cells
and (b) the count `∑ s_i ≤ 6n + m - 6`. Neither can be had cheaply: a binary space partition
(recursive cuts along lines avoiding the disks), which would give (b) by an easy induction (even
`∑ s_i ≤ 4n + m - 4`), does not exist in general (a pinwheel of long congruent rectangles has no
free cut, and the hexagonal packing of discs has none), and cells of the form
`{x | f_i(x) = max_j f_j(x)}`, `f_i` affine (power diagrams), which tile automatically, cannot
separate a pinwheel either. The least topology we know for (b) is the angle-sum count recalled in
the cell lemma's docstring: in the normal-angle representation the interior angles of a convex
`s`-gon sum to `(s - 2)π` for free, so (b) reduces to the local fact that the corner angles of
non-overlapping cells at a point sum to at most `2π` (`π` at a point interior to a side of a cell
or on a side of `Q`), an area computation in small disks, plus the structure of the holes; it
avoids Euler's formula and the Jordan curve theorem.
-/

open PlaneConvex
open scoped Real Pointwise

/-! ### Congruent copies -/

theorem ft_volume_of_congruent {K A : Set (Fin 2 → ℝ)} (h : IsCongruent K A) :
    volume A = volume K := by
  obtain ⟨M, hM, b, rfl⟩ := h
  exact volume_image_motion hM b K

theorem ft_minCircumscribedArea_of_congruent {K A : Set (Fin 2 → ℝ)} (h : IsCongruent K A)
    (k : ℕ) : minCircumscribedArea A k = minCircumscribedArea K k := by
  obtain ⟨M, hM, b, rfl⟩ := h
  exact minCircumscribedArea_image_motion hM b k

theorem ft_continuous_motion (M : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) :
    Continuous fun x : Fin 2 → ℝ ↦ M *ᵥ x + b :=
  (Continuous.matrix_mulVec continuous_const continuous_id).add continuous_const

/-- A convex set of positive area has nonempty interior. -/
theorem ft_interior_nonempty_of_convex {A : Set (Fin 2 → ℝ)} (hA : Convex ℝ A)
    (hpos : volume A ≠ 0) : (interior A).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  apply hpos
  refine measure_mono_null (subset_closure.trans ?_) (Convex.addHaar_frontier volume hA)
  rw [closure_eq_interior_union_frontier, h, empty_union]

theorem ft_isConvexDisk_of_congruent {K A : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K)
    (h : IsCongruent K A) : IsConvexDisk A := by
  have hvol := ft_volume_of_congruent h
  obtain ⟨M, hM, b, rfl⟩ := h
  have hconv : Convex ℝ ((fun x ↦ M *ᵥ x + b) '' K) := by
    have : (fun x ↦ M *ᵥ x + b) '' K = (fun x ↦ b + x) '' (Matrix.toLin' M '' K) := by
      rw [image_image]
      congr 1
      ext x
      simp [add_comm]
    rw [this]
    exact (hK.1.linear_image _).translate b
  refine ⟨hconv, hK.2.1.image (ft_continuous_motion M b), ?_⟩
  apply ft_interior_nonempty_of_convex hconv
  rw [hvol]
  obtain ⟨x, hx⟩ := hK.2.2
  exact (Measure.measure_pos_of_nonempty_interior _ ⟨x, hx⟩).ne'

/-! ### Fejes Tóth's cell lemma -/

/-- **Fejes Tóth's cell lemma** (L. Fejes Tóth 1950; Böröczky 2003, Lemma 5). Let
`Q = ⋂_{j < m} {⟨b j, x⟩ ≤ d j}` be a bounded convex polygon and `K₀, …, K_{n-1}`, `n ≥ 1`,
pairwise non-overlapping convex disks in `Q`. Then there are convex polygons
`C i = ⋂_{l < s i} {⟨a i l, x⟩ ≤ c i l}` with `K i ⊆ C i ⊆ Q`, pairwise non-overlapping, such that
`∑ s i ≤ 6n + m - 6`.

This is left as `sorry`: it is the planar-topology core of Fejes Tóth's theorem. The argument, as
three lemmas to be formalized:

(A) *A maximal family of cells.* For `i ≠ j` let `H_ij ⊇ K_i`, `H_ji ⊇ K_j` be the two closed
half-planes of a line separating `K_i` and `K_j` (Hahn–Banach, `geometric_hahn_banach_open_open`
on the interiors, then closures), and `P_i = Q ∩ ⋂_{j ≠ i} H_ij`; the `P_i` are non-overlapping
convex polygons, and every family of non-overlapping convex sets `K_i ⊆ Φ_i ⊆ Q` is dominated by one
of this form. The lines range over a compact set and `∑ |P_i|` is continuous in them (dominated
convergence: the indicators converge off the lines), so a family of maximal total area exists.

(B) *Holes are pinwheels* (Böröczky's Lemma 5). At a maximum, the closure of each component of
`Q \ ⋃ P_i` is a convex polygon `R` in the interior of `Q`, each side of which lies on a side of a
cell, and each corner `v` of which is a corner of the cell carrying the next side and lies in the
relative interior of the side of the cell carrying the previous one; otherwise the line carrying
a side of `R` could be rotated or moved about an endpoint so as to enlarge a cell, contradicting
maximality. In particular the cells cover `∂Q`.

(C) *The count* `∑ s_i ≤ 6n + m - 6`, by Euler's formula for the cell complex obtained by
shrinking each hole to a point (Böröczky's Proposition 4), or, avoiding Euler's formula, by angles:
the interior angles of a convex `s`-gon sum to `(s - 2)π` (with the normals sorted by angle, the
exterior angles are the gaps between consecutive normals, which sum to `2π`), so
`∑_i (s_i - 2)π = ∑_p A_p` where `A_p` is the sum of the angles of the cell corners at the point
`p`, `c_p` their number. Locally (`area (C ∩ B(p, ε)) = θ_p(C) ε²/2` for small `ε`, and the cells
do not overlap) `A_p = 2π` with `c_p ≥ 3`, or `A_p = π` with `c_p ≥ 2` (when `p` is interior to a
side of a cell or of `Q`), or `A_p` is the angle of `Q` at its corner `p`, except at the corners
of holes, where (B) gives a total of `2π` over at least three cell corners per hole. Hence
`A_p ≤ (2/3)π c_p` outside the corners of `Q` (grouping the corners of each hole) and
`∑ (s_i - 2)π ≤ (2/3)π (∑ s_i - m) + (m - 2)π`, which is the claim.

Infrastructure: separation of convex bodies; compactness and continuity for (A); the local
structure of convex polygons at a point (sectors) and the angle sum for (C); a perturbation
argument for (B). Estimated size: (A) about 600 lines, (B) about 1500, (C) about 1500. -/
theorem ft_cell_decomposition {m n : ℕ} (hn : 1 ≤ n) (b : Fin m → Fin 2 → ℝ) (d : Fin m → ℝ)
    (hQ : Bornology.IsBounded (halfPlanesInter b d)) (Ks : Fin n → Set (Fin 2 → ℝ))
    (hKs : ∀ i, IsConvexDisk (Ks i)) (hsub : ∀ i, Ks i ⊆ halfPlanesInter b d)
    (hdisj : Pairwise fun i j ↦ Disjoint (interior (Ks i)) (interior (Ks j))) :
    ∃ (s : Fin n → ℕ) (a : ∀ i, Fin (s i) → Fin 2 → ℝ) (c : ∀ i, Fin (s i) → ℝ),
      (∀ i, 3 ≤ s i) ∧ (∀ i, Ks i ⊆ halfPlanesInter (a i) (c i)) ∧
      (∀ i, halfPlanesInter (a i) (c i) ⊆ halfPlanesInter b d) ∧
      (Pairwise fun i j ↦ Disjoint (interior (halfPlanesInter (a i) (c i)))
        (interior (halfPlanesInter (a j) (c j)))) ∧
      ∑ i, s i + 6 ≤ 6 * n + m := by
  sorry

/-! ### Fejes Tóth's inequality -/

/-- **Fejes Tóth's inequality.** If `n` congruent copies of a convex disk `K` are packed in a
convex polygon `Q` with at most six sides, then `n · t_K(6) ≤ |Q|`. -/
theorem ft_card_mul_le_volume {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K) {m : ℕ} (hm : m ≤ 6)
    (b : Fin m → Fin 2 → ℝ) (d : Fin m → ℝ) (hQ : Bornology.IsBounded (halfPlanesInter b d))
    (F : Finset (Set (Fin 2 → ℝ))) (hF : ∀ A ∈ F, IsCongruent K A)
    (hpack : IsPacking (F : Set (Set (Fin 2 → ℝ)))) (hFQ : ∀ A ∈ F, A ⊆ halfPlanesInter b d) :
    (F.card : ℝ≥0∞) * minCircumscribedArea K 6 ≤ volume (halfPlanesInter b d) := by
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · simp
  have hne : K.Nonempty := hK.2.2.mono interior_subset
  set n := F.card with hn_def
  have hn : 1 ≤ n := Finset.card_pos.2 hFne
  let e : Fin n ≃ F := F.equivFin.symm
  let Ks : Fin n → Set (Fin 2 → ℝ) := fun i ↦ (e i : Set (Fin 2 → ℝ))
  have hKs : ∀ i, IsConvexDisk (Ks i) := fun i ↦ ft_isConvexDisk_of_congruent hK (hF _ (e i).2)
  have hsub : ∀ i, Ks i ⊆ halfPlanesInter b d := fun i ↦ hFQ _ (e i).2
  have hdisj : Pairwise fun i j ↦ Disjoint (interior (Ks i)) (interior (Ks j)) := by
    intro i j hij
    refine hpack (e i).2 (e j).2 fun h ↦ hij (e.injective (Subtype.ext h))
  obtain ⟨s, a, c, hs3, hKC, hCQ, hCdisj, hcount⟩ :=
    ft_cell_decomposition hn b d hQ Ks hKs hsub hdisj
  have harea : ∀ i, minCircumscribedArea K (s i) ≤ volume (halfPlanesInter (a i) (c i)) := by
    intro i
    rw [← ft_minCircumscribedArea_of_congruent (hF _ (e i).2)]
    exact minCircumscribedArea_le (hKC i)
  have hsum : ∑ i, volume (halfPlanesInter (a i) (c i)) ≤ volume (halfPlanesInter b d) :=
    sum_volume_le_of_pairwise_disjoint_interior _ (fun i ↦ convex_halfPlanesInter _ _) hCdisj
      hCQ
  set t := minCircumscribedArea K
  set dd := t 6 - t 7
  have hdd : dd ≠ ∞ :=
    ne_top_of_le_ne_top (minCircumscribedArea_lt_top hK.2.1 (by norm_num)).ne tsub_le_self
  have hline : ∑ i, (t 6 + 6 * dd) ≤ ∑ i, (t (s i) + (s i : ℝ≥0∞) * dd) :=
    Finset.sum_le_sum fun i _ ↦ minCircumscribedArea_six_add_le hK.2.1 hne (hs3 i)
  have hL : ∑ _i : Fin n, (t 6 + 6 * dd) = n * (t 6 + 6 * dd) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hR : ∑ i, (t (s i) + (s i : ℝ≥0∞) * dd) =
      ∑ i, t (s i) + (∑ i, (s i : ℝ≥0∞)) * dd := by
    rw [Finset.sum_add_distrib, Finset.sum_mul]
  rw [hL, hR] at hline
  have hS : (∑ i, (s i : ℝ≥0∞)) ≤ 6 * n := by
    have : ∑ i, s i ≤ 6 * n := by omega
    exact_mod_cast this
  have h6 : (n : ℝ≥0∞) * (6 * dd) ≠ ∞ := ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top
    (by simp) hdd)
  have key : (n : ℝ≥0∞) * t 6 + n * (6 * dd) ≤ ∑ i, t (s i) + n * (6 * dd) := by
    calc (n : ℝ≥0∞) * t 6 + n * (6 * dd) = n * (t 6 + 6 * dd) := by ring
      _ ≤ ∑ i, t (s i) + (∑ i, (s i : ℝ≥0∞)) * dd := hline
      _ ≤ ∑ i, t (s i) + 6 * n * dd := by gcongr
      _ = ∑ i, t (s i) + n * (6 * dd) := by ring
  calc (n : ℝ≥0∞) * t 6 ≤ ∑ i, t (s i) := ENNReal.le_of_add_le_add_right h6 key
    _ ≤ ∑ i, volume (halfPlanesInter (a i) (c i)) := Finset.sum_le_sum fun i _ ↦ harea i
    _ ≤ _ := hsum

/-! ### Disks, diameters, grids -/

theorem ft_disk_eq_smul {ρ : ℝ} (hρ : 0 < ρ) : disk ρ = ρ • disk 1 := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hρ.ne']
  simp only [disk, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, one_pow, mul_pow, ← mul_add,
    inv_pow]
  rw [inv_mul_le_iff₀ (by positivity), mul_one]

theorem ft_volume_disk {ρ : ℝ} (hρ : 0 < ρ) :
    volume (disk ρ) = ENNReal.ofReal (ρ ^ 2) * volume (disk 1) := by
  rw [ft_disk_eq_smul hρ, Measure.addHaar_smul, Module.finrank_fin_fun,
    abs_of_nonneg (by positivity)]

theorem ft_volume_disk_one_ne_zero : volume (disk 1) ≠ 0 := by
  have hsub : Icc (fun _ ↦ -(1 / 2 : ℝ)) (fun _ ↦ 1 / 2) ⊆ disk 1 := by
    intro x hx
    have h0 : -(1 / 2 : ℝ) ≤ x 0 := hx.1 0
    have h1 : x 0 ≤ 1 / 2 := hx.2 0
    have h2 : -(1 / 2 : ℝ) ≤ x 1 := hx.1 1
    have h3 : x 1 ≤ 1 / 2 := hx.2 1
    simp only [disk, mem_ofPred_eq]
    nlinarith
  rw [← pos_iff_ne_zero]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Icc_pi]
  norm_num

theorem ft_volume_disk_one_ne_top : volume (disk 1) ≠ ∞ := by
  have hsub : disk 1 ⊆ Icc (fun _ ↦ (-1 : ℝ)) (fun _ ↦ 1) := by
    intro x hx
    simp only [disk, mem_ofPred_eq, one_pow] at hx
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;> fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0),
      sq_nonneg (x 1)]
  exact ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono hsub)

/-- The congruent copies of a compact set have uniformly bounded diameters. -/
theorem ft_exists_diam_bound {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ A, IsCongruent K A → ∀ x ∈ A, ∀ y ∈ A, ∀ i, |x i - y i| ≤ D := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨3 * max R 0, by positivity, ?_⟩
  rintro A ⟨M, hM, b, rfl⟩ _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ i
  set R' := max R 0
  have hR' : 0 ≤ R' := le_max_right _ _
  have hxb : ∀ j, |x j| ≤ R' := fun j ↦ (norm_le_pi_norm x j).trans
    ((mem_closedBall_zero_iff.1 (hR hx)).trans (le_max_left _ _))
  have hyb : ∀ j, |y j| ≤ R' := fun j ↦ (norm_le_pi_norm y j).trans
    ((mem_closedBall_zero_iff.1 (hR hy)).trans (le_max_left _ _))
  have hv := orthogonal_dotProduct_mulVec hM (x - y) (x - y)
  have hdiff : (M *ᵥ x + b) i - (M *ᵥ y + b) i = (M *ᵥ (x - y)) i := by
    simp [Matrix.mulVec_sub]
  rw [hdiff]
  set v := M *ᵥ (x - y)
  have hsq : v i ^ 2 ≤ v ⬝ᵥ v := by
    simp only [dotProduct, Fin.sum_univ_two]
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  rw [hv] at hsq
  have h8 : (x - y) ⬝ᵥ (x - y) ≤ 8 * R' ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_two, Pi.sub_apply]
    have h0 := abs_le.1 (hxb 0)
    have h1 := abs_le.1 (hxb 1)
    have h2 := abs_le.1 (hyb 0)
    have h3 := abs_le.1 (hyb 1)
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- The half-open grid square `∏ [z_i L, (z_i + 1) L)`. -/
def ft_cell (L : ℝ) (z : Fin 2 → ℤ) : Set (Fin 2 → ℝ) :=
  Set.pi univ fun i ↦ Ico (z i * L) ((z i + 1) * L)

theorem ft_mem_cell_floor {L : ℝ} (hL : 0 < L) (x : Fin 2 → ℝ) :
    x ∈ ft_cell L (fun i ↦ ⌊x i / L⌋) := by
  intro i _
  constructor
  · have := Int.floor_le (x i / L)
    rwa [le_div_iff₀ hL] at this
  · have := Int.lt_floor_add_one (x i / L)
    rwa [div_lt_iff₀ hL] at this

theorem ft_cell_disjoint {L : ℝ} (hL : 0 < L) {z z' : Fin 2 → ℤ} (h : z ≠ z') :
    Disjoint (ft_cell L z) (ft_cell L z') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  apply h
  funext i
  have h1 := hx i (mem_univ _)
  have h2 := hx' i (mem_univ _)
  have a1 : (z i : ℝ) < z' i + 1 := by
    have := lt_of_le_of_lt h1.1 h2.2
    exact (mul_lt_mul_iff_left₀ hL).1 this
  have a2 : (z' i : ℝ) < z i + 1 := by
    have := lt_of_le_of_lt h2.1 h1.2
    exact (mul_lt_mul_iff_left₀ hL).1 this
  have b1 : z i < z' i + 1 := by exact_mod_cast a1
  have b2 : z' i < z i + 1 := by exact_mod_cast a2
  omega

theorem ft_volume_cell {L : ℝ} (hL : 0 < L) (z : Fin 2 → ℤ) :
    volume (ft_cell L z) = ENNReal.ofReal (L ^ 2) := by
  rw [ft_cell, Real.volume_pi_Ico, Fin.prod_univ_two, ← ENNReal.ofReal_mul (by nlinarith)]
  congr 1
  ring

theorem ft_measurableSet_cell (L : ℝ) (z : Fin 2 → ℤ) : MeasurableSet (ft_cell L z) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico

/-- A grid square meeting `D_r` lies in `D_{r + 2L}`. -/
theorem ft_cell_subset_disk {L r : ℝ} (hL : 0 < L) (hr : 0 ≤ r) {z : Fin 2 → ℤ}
    (h : (ft_cell L z ∩ disk r).Nonempty) : ft_cell L z ⊆ disk (r + 2 * L) := by
  obtain ⟨y, hy, hyr⟩ := h
  intro x hx
  simp only [disk, mem_ofPred_eq] at hyr ⊢
  have hd : ∀ i, |x i - y i| ≤ L := by
    intro i
    have h1 := hx i (mem_univ _)
    have h2 := hy i (mem_univ _)
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  set δ0 := x 0 - y 0
  set δ1 := x 1 - y 1
  have hδ0 := abs_le.1 (hd 0)
  have hδ1 := abs_le.1 (hd 1)
  have hx0 : x 0 = y 0 + δ0 := by ring
  have hx1 : x 1 = y 1 + δ1 := by ring
  rw [hx0, hx1]
  have hδ : δ0 ^ 2 + δ1 ^ 2 ≤ 2 * L ^ 2 := by nlinarith
  have hcs : (y 0 * δ0 + y 1 * δ1) ^ 2 ≤ (y 0 ^ 2 + y 1 ^ 2) * (δ0 ^ 2 + δ1 ^ 2) := by
    nlinarith [sq_nonneg (y 0 * δ1 - y 1 * δ0)]
  have hdot : y 0 * δ0 + y 1 * δ1 ≤ 2 * r * L := by
    by_contra hcon
    push Not at hcon
    have : (2 * r * L) ^ 2 < (y 0 * δ0 + y 1 * δ1) ^ 2 := by
      have : 0 ≤ 2 * r * L := by positivity
      nlinarith
    nlinarith [mul_le_mul hyr hδ (by positivity) (by positivity)]
  nlinarith

/-- An axis-parallel rectangle as an intersection of four half-planes. -/
theorem ft_Icc_eq_halfPlanesInter (lo hi : Fin 2 → ℝ) :
    Icc lo hi = halfPlanesInter (![![1, 0], ![0, 1], ![-1, 0], ![0, -1]] : Fin 4 → Fin 2 → ℝ)
      ![hi 0, hi 1, -lo 0, -lo 1] := by
  ext x
  simp only [mem_Icc, halfPlanesInter, mem_ofPred_eq, Fin.forall_fin_succ]
  simp [dotProduct, Fin.sum_univ_two, Pi.le_def, Fin.forall_fin_two, neg_le_neg_iff]
  tauto

/-- Fejes Tóth's inequality for a rectangle. -/
theorem ft_card_mul_le_volume_Icc {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K)
    (lo hi : Fin 2 → ℝ) (F : Finset (Set (Fin 2 → ℝ))) (hF : ∀ A ∈ F, IsCongruent K A)
    (hpack : IsPacking (F : Set (Set (Fin 2 → ℝ)))) (hFQ : ∀ A ∈ F, A ⊆ Icc lo hi) :
    (F.card : ℝ≥0∞) * minCircumscribedArea K 6 ≤ volume (Icc lo hi) := by
  rw [ft_Icc_eq_halfPlanesInter] at hFQ ⊢
  exact ft_card_mul_le_volume hK (by norm_num) _ _
    (by rw [← ft_Icc_eq_halfPlanesInter]; exact Metric.isBounded_Icc lo hi) F hF hpack hFQ

/-! ### From finite packings to densities -/

/-- Every packing of congruent copies of `K` has upper density at most `|K| / t_K(6)`. -/
theorem ft_upperDensity_le {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K)
    {𝒜 : Set (Set (Fin 2 → ℝ))} (hpack : IsPacking 𝒜) (hcong : ∀ A ∈ 𝒜, IsCongruent K A) :
    upperDensity 𝒜 ≤ volume K / minCircumscribedArea K 6 := by
  classical
  have hK' := hK
  obtain ⟨hconv, hcpt, hint⟩ := hK
  obtain ⟨D, hD0, hD⟩ := ft_exists_diam_bound hcpt
  set t6 := minCircumscribedArea K 6
  have hvolK : volume K ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ hint).ne'
  have ht6 : t6 ≠ 0 := fun h ↦ hvolK (le_antisymm (h ▸ volume_le_minCircumscribedArea 6) bot_le)
  have ht6' : t6 ≠ ∞ := (minCircumscribedArea_lt_top hcpt (by norm_num)).ne
  set c := volume K / t6
  have hc : volume K = t6 * c := (ENNReal.mul_div_cancel ht6 ht6').symm
  set v1 := (volume (disk 1)).toReal
  have hv1 : volume (disk 1) = ENNReal.ofReal v1 :=
    (ENNReal.ofReal_toReal ft_volume_disk_one_ne_top).symm
  have hv1pos : 0 < v1 := ENNReal.toReal_pos ft_volume_disk_one_ne_zero ft_volume_disk_one_ne_top
  set G : ℝ → ℝ := fun r ↦ (r + 2 * √r) ^ 2 * (√r + 2 * D) ^ 2 / ((√r) ^ 2 * r ^ 2) with hG
  have key : ∀ r : ℝ, 1 ≤ r → (∑' A : 𝒜, volume ((A : Set (Fin 2 → ℝ)) ∩ disk r)) /
      volume (disk r) ≤ ENNReal.ofReal (G r) * c := by
    intro r hr
    have hr0 : 0 < r := by linarith
    have hL : 0 < √r := Real.sqrt_pos.2 hr0
    set L := √r with hLdef
    -- the grid squares meeting `D_r`
    set n0 : ℤ := ⌈r / L⌉ + 1
    set Z : Finset (Fin 2 → ℤ) := (Fintype.piFinset fun _ : Fin 2 ↦ Finset.Icc (-n0) n0).filter
      fun z ↦ ft_cell L z ⊆ disk (r + 2 * L)
    have hcover : ∀ x ∈ disk r, ∃ z ∈ Z, x ∈ ft_cell L z := by
      intro x hx
      refine ⟨fun i ↦ ⌊x i / L⌋, ?_, ft_mem_cell_floor hL x⟩
      rw [Finset.mem_filter]
      refine ⟨?_, ft_cell_subset_disk hL hr0.le ⟨x, ft_mem_cell_floor hL x, hx⟩⟩
      simp only [disk, mem_ofPred_eq] at hx
      have hxi : ∀ i, |x i| ≤ r := by
        intro i
        rw [abs_le]
        fin_cases i <;> simp <;> constructor <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
      have hc1 : r / L ≤ ⌈r / L⌉ := Int.le_ceil _
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      constructor
      · have h1 : -r / L ≤ x i / L := div_le_div_of_nonneg_right (abs_le.1 (hxi i)).1 hL.le
        have h2 := Int.lt_floor_add_one (x i / L)
        have h3 : (-n0 : ℝ) < ⌊x i / L⌋ + 1 := by
          simp only [n0]; push_cast
          rw [neg_div] at h1
          linarith
        have : -n0 < ⌊x i / L⌋ + 1 := by exact_mod_cast h3
        change -n0 ≤ ⌊x i / L⌋
        omega
      · have h1 : x i / L ≤ r / L := div_le_div_of_nonneg_right (abs_le.1 (hxi i)).2 hL.le
        have h2 := Int.floor_le (x i / L)
        have h3 : (⌊x i / L⌋ : ℝ) ≤ n0 := by
          simp only [n0]; push_cast
          linarith
        change ⌊x i / L⌋ ≤ n0
        exact_mod_cast h3
    have hZcard : (Z.card : ℝ) * L ^ 2 ≤ (r + 2 * L) ^ 2 * v1 := by
      have h1 : ∑ z ∈ Z, volume (ft_cell L z) ≤ volume (disk (r + 2 * L)) := by
        rw [← measure_biUnion_finset (fun z _ z' _ hzz' ↦ ft_cell_disjoint hL hzz')
          (fun z _ ↦ ft_measurableSet_cell L z)]
        exact measure_mono (iUnion₂_subset fun z hz ↦ (Finset.mem_filter.1 hz).2)
      rw [Finset.sum_congr rfl (fun z _ ↦ ft_volume_cell hL z), Finset.sum_const, nsmul_eq_mul,
        ft_volume_disk (by positivity), hv1, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h1
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
    -- the packing estimate in one grid square
    have hsq : ∀ z (S : Finset 𝒜), ∑ A ∈ S, volume ((A : Set (Fin 2 → ℝ)) ∩ ft_cell L z) ≤
        ENNReal.ofReal ((L + 2 * D) ^ 2) * c := by
      intro z S
      set Sz := S.filter fun A : 𝒜 ↦ ((A : Set (Fin 2 → ℝ)) ∩ ft_cell L z).Nonempty
      have h1 : ∑ A ∈ S, volume ((A : Set (Fin 2 → ℝ)) ∩ ft_cell L z) ≤ ∑ _A ∈ Sz, volume K := by
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum fun A _ ↦ ?_
        split_ifs with h
        · rw [← ft_volume_of_congruent (hcong A A.2)]
          exact measure_mono inter_subset_left
        · rw [Set.not_nonempty_iff_eq_empty.1 h, measure_empty]
      have h2 : (Sz.card : ℝ≥0∞) * t6 ≤ ENNReal.ofReal ((L + 2 * D) ^ 2) := by
        have := ft_card_mul_le_volume_Icc hK' (fun i ↦ z i * L - D) (fun i ↦ (z i + 1) * L + D)
          (Sz.map (Function.Embedding.subtype (· ∈ 𝒜))) ?_ ?_ ?_
        · rw [Finset.card_map] at this
          refine this.trans (le_of_eq ?_)
          rw [Real.volume_Icc_pi, Fin.prod_univ_two, ← ENNReal.ofReal_mul (by nlinarith)]
          congr 1
          ring
        · intro A hA
          obtain ⟨A', _, rfl⟩ := Finset.mem_map.1 hA
          exact hcong _ A'.2
        · intro A hA B hB hAB
          obtain ⟨A', _, rfl⟩ := Finset.mem_map.1 hA
          obtain ⟨B', _, rfl⟩ := Finset.mem_map.1 hB
          exact hpack A'.2 B'.2 hAB
        · intro A hA x hx
          obtain ⟨A', hA', rfl⟩ := Finset.mem_map.1 hA
          obtain ⟨y, hyA, hyc⟩ := (Finset.mem_filter.1 hA').2
          have hxy := hD _ (hcong _ A'.2) x hx y hyA
          refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
          · have h1 := hyc i (mem_univ _)
            have h2 := abs_le.1 (hxy i)
            simp only
            linarith [h1.1, h1.2]
          · have h1 := hyc i (mem_univ _)
            have h2 := abs_le.1 (hxy i)
            simp only
            linarith [h1.1, h1.2]
      calc ∑ A ∈ S, volume ((A : Set (Fin 2 → ℝ)) ∩ ft_cell L z) ≤ ∑ _A ∈ Sz, volume K := h1
        _ = (Sz.card * t6) * c := by rw [Finset.sum_const, nsmul_eq_mul, hc, mul_assoc]
        _ ≤ ENNReal.ofReal ((L + 2 * D) ^ 2) * c := by gcongr
    -- the estimate for the disk
    have htsum : ∑' A : 𝒜, volume ((A : Set (Fin 2 → ℝ)) ∩ disk r) ≤
        ENNReal.ofReal (Z.card * (L + 2 * D) ^ 2) * c := by
      rw [tsum_eq_iSup_sum]
      refine iSup_le fun S ↦ ?_
      calc ∑ A ∈ S, volume ((A : Set (Fin 2 → ℝ)) ∩ disk r)
          ≤ ∑ A ∈ S, ∑ z ∈ Z, volume ((A : Set (Fin 2 → ℝ)) ∩ ft_cell L z) := by
            refine Finset.sum_le_sum fun A _ ↦ ?_
            refine (measure_mono ?_).trans (measure_biUnion_finset_le Z _)
            rintro x ⟨hxA, hxr⟩
            obtain ⟨z, hz, hxz⟩ := hcover x hxr
            exact mem_iUnion₂.2 ⟨z, hz, hxA, hxz⟩
        _ = ∑ z ∈ Z, ∑ A ∈ S, volume ((A : Set (Fin 2 → ℝ)) ∩ ft_cell L z) := Finset.sum_comm
        _ ≤ ∑ _z ∈ Z, ENNReal.ofReal ((L + 2 * D) ^ 2) * c :=
            Finset.sum_le_sum fun z _ ↦ hsq z S
        _ = ENNReal.ofReal (Z.card * (L + 2 * D) ^ 2) * c := by
            rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.div_le_of_le_mul
    refine htsum.trans ?_
    rw [ft_volume_disk hr0, hv1, ← ENNReal.ofReal_mul (by positivity), mul_right_comm,
      ← ENNReal.ofReal_mul (by simp only [G]; positivity)]
    gcongr ENNReal.ofReal ?_ * _
    have hGr : G r * (r ^ 2 * v1) = (r + 2 * L) ^ 2 * v1 * (L + 2 * D) ^ 2 / L ^ 2 := by
      simp only [G, ← hLdef]
      field_simp
    rw [hGr, le_div_iff₀ (by positivity)]
    calc (Z.card : ℝ) * (L + 2 * D) ^ 2 * L ^ 2 = (Z.card * L ^ 2) * (L + 2 * D) ^ 2 := by ring
      _ ≤ (r + 2 * L) ^ 2 * v1 * (L + 2 * D) ^ 2 :=
          mul_le_mul_of_nonneg_right hZcard (sq_nonneg _)
  -- `G r → 1`
  have hGlim : Tendsto G atTop (nhds 1) := by
    have hinv : Tendsto (fun r : ℝ ↦ (√r)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    have h1 : Tendsto (fun r : ℝ ↦ (1 + 2 * (√r)⁻¹) ^ 2 * (1 + 2 * D * (√r)⁻¹) ^ 2) atTop
        (nhds ((1 + 2 * 0) ^ 2 * (1 + 2 * D * 0) ^ 2)) :=
      ((tendsto_const_nhds.add (hinv.const_mul 2)).pow 2).mul
        ((tendsto_const_nhds.add (hinv.const_mul (2 * D))).pow 2)
    simp only [mul_zero, add_zero, one_pow, mul_one] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    obtain ⟨u, hu, rfl⟩ : ∃ u : ℝ, 0 < u ∧ r = u ^ 2 :=
      ⟨√r, Real.sqrt_pos.2 hr, (Real.sq_sqrt hr.le).symm⟩
    simp only [G, Real.sqrt_sq hu.le]
    field_simp
  have hT : Tendsto (fun r ↦ ENNReal.ofReal (G r) * c) atTop (nhds c) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hGlim) (b := c)
      (Or.inl (by simp))
    simpa using this
  calc upperDensity 𝒜 ≤ limsup (fun r ↦ ENNReal.ofReal (G r) * c) atTop :=
        Filter.limsup_le_limsup ((eventually_ge_atTop 1).mono key)
    _ = c := hT.limsup_eq

/-! ### Lattice packings from centrally symmetric hexagons -/

/-- For `K = -K`, `t_K(6)` is the infimum of the areas of the centrally symmetric circumscribed
hexagons (Dowker). -/
theorem ft_minCircumscribedArea_six_eq_iInf_symm {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K)
    (hsymm : IsCentrallySymmetric K) :
    minCircumscribedArea K 6 =
      ⨅ c : Fin 3 → ℝ, volume (circPolygon K (Sum.elim c fun i ↦ c i + π)) := by
  obtain ⟨hconv, hcpt, hint⟩ := hK
  have hne : K.Nonempty := hint.mono interior_subset
  apply le_antisymm
  · refine le_iInf fun c ↦ ?_
    have hre : circPolygon K ((Sum.elim c fun i ↦ c i + π) ∘ finSumFinEquiv.symm) =
        circPolygon K (Sum.elim c fun i ↦ c i + π) := by
      ext x
      simp only [mem_circPolygon_iff, Function.comp_apply]
      constructor
      · intro h i
        simpa using h (finSumFinEquiv i)
      · intro h i
        exact h _
    rw [← hre]
    exact minCircumscribedArea_le_circPolygon hcpt (k := 3 + 3) _
  · rw [minCircumscribedArea_eq_iInf hcpt hne]
    refine le_iInf fun θ ↦ ?_
    obtain ⟨c, hc⟩ := exists_symm_le hcpt hne hsymm (j := 3) θ
    exact iInf_le_of_le c hc

/-- A centrally symmetric hexagon `P ⊇ K` of finite area is a fundamental domain of a lattice. -/
theorem ft_hexagon_lattice {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K)
    (hsymm : IsCentrallySymmetric K) (c : Fin 3 → ℝ)
    (hfin : volume (circPolygon K (Sum.elim c fun i ↦ c i + π)) ≠ ∞) :
    ∃ L : Submodule ℤ (Fin 2 → ℝ), IsLattice L ∧ IsPacking (translates K L) ∧
      Bornology.IsBounded (circPolygon K (Sum.elim c fun i ↦ c i + π)) ∧
      ∀ x, ∃ l ∈ L, x - l ∈ circPolygon K (Sum.elim c fun i ↦ c i + π) := by
  obtain ⟨hconv, hcpt, hint⟩ := hK
  have hKP := subset_circPolygon hcpt (Sum.elim c fun i ↦ c i + π)
  obtain ⟨u, v, α, β, huv, hα, hβ, hP⟩ :=
    circPolygon_symm_eq_symmHexagon hcpt hint hsymm c hfin
  rw [hP] at hKP ⊢
  obtain ⟨w₁, w₂, hli, hcov, hpk⟩ := exists_lattice_symmHexagon huv hα hβ
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ (Fin 2 → ℝ) := by simp
  set b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ⇑b = ![w₁, w₂] := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  set L := Submodule.span ℤ (Set.range b)
  have hmem : ∀ l, l ∈ L ↔ ∃ m n : ℤ, l = (m : ℝ) • w₁ + (n : ℝ) • w₂ := by
    intro l
    rw [Submodule.mem_span_range_iff_exists_fun, hb]
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨f 0, f 1, ?_⟩
      simp [Fin.sum_univ_two, Int.cast_smul_eq_zsmul]
    · rintro ⟨m, n, rfl⟩
      refine ⟨![m, n], ?_⟩
      simp [Fin.sum_univ_two, Int.cast_smul_eq_zsmul]
  refine ⟨L, ⟨inferInstance, ?_⟩, ?_, isBounded_symmHexagon huv α β, fun x ↦ ?_⟩
  · rw [Submodule.span_span_of_tower, b.span_eq]
  · -- the translates of `K` do not overlap
    rintro _ ⟨l, rfl⟩ _ ⟨l', rfl⟩ hne
    rw [Set.disjoint_left]
    intro z hz hz'
    apply hne
    have himg : ∀ a : Fin 2 → ℝ, (fun x ↦ x + a) '' interior K =
        interior ((fun x ↦ x + a) '' K) := fun a ↦ (Homeomorph.addRight a).image_interior K
    simp only at hz hz'
    rw [← himg] at hz hz'
    obtain ⟨k, hk, rfl⟩ := hz
    obtain ⟨k', hk', hkk'⟩ := hz'
    have hint' := interior_mono hKP
    obtain ⟨a1, a2, a3⟩ := interior_symmHexagon_subset u v α β (hint' hk)
    obtain ⟨b1, b2, b3⟩ := interior_symmHexagon_subset u v α β (hint' hk')
    have hd : (l' : Fin 2 → ℝ) - l ∈ L := sub_mem l'.2 l.2
    obtain ⟨m, n, hmn⟩ := (hmem _).1 hd
    have hdk : (l' : Fin 2 → ℝ) - l = k - k' := by
      simp only at hkk'
      rw [sub_eq_sub_iff_add_eq_add, add_comm]
      exact hkk'
    by_contra hll
    have hne' : m ≠ 0 ∨ n ≠ 0 := by
      by_contra hcon
      simp only [not_or, not_not] at hcon
      apply hll
      have : (l' : Fin 2 → ℝ) - l = 0 := by rw [hmn, hcon.1, hcon.2]; simp
      have hl : l = l' := Subtype.ext (sub_eq_zero.1 this).symm
      rw [hl]
    have hpk' := hpk m n hne'
    rw [← hmn, hdk] at hpk'
    have c1 : |u ⬝ᵥ (k - k')| < 2 := by
      rw [dotProduct_sub]
      exact (abs_sub _ _).trans_lt (by linarith)
    have c2 : |v ⬝ᵥ (k - k')| < 2 := by
      rw [dotProduct_sub]
      exact (abs_sub _ _).trans_lt (by linarith)
    have c3 : |(α • u + β • v) ⬝ᵥ (k - k')| < 2 := by
      rw [dotProduct_sub]
      exact (abs_sub _ _).trans_lt (by linarith)
    rcases hpk' with h | h | h <;> linarith
  · -- the translates of the hexagon cover the plane
    obtain ⟨m, n, hx⟩ := hcov x
    exact ⟨_, (hmem _).2 ⟨m, n, rfl⟩, hx⟩

theorem ft_finite_inter {L : Submodule ℤ (Fin 2 → ℝ)} (hL : DiscreteTopology L)
    {s : Set (Fin 2 → ℝ)} (hs : Bornology.IsBounded s) : (s ∩ (L : Set (Fin 2 → ℝ))).Finite := by
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hs ?_
  rw [← Submodule.coe_toAddSubgroup]
  have : DiscreteTopology L.toAddSubgroup := hL
  exact AddSubgroup.isClosed_of_discreteTopology

theorem ft_neg_mem_disk {x : Fin 2 → ℝ} {a : ℝ} (hx : x ∈ disk a) : -x ∈ disk a := by
  simpa [disk] using hx

/-- Minkowski's inequality for the Euclidean disks. -/
theorem ft_add_mem_disk {x y : Fin 2 → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : x ∈ disk a)
    (hy : y ∈ disk b) : x + y ∈ disk (a + b) := by
  simp only [disk, mem_ofPred_eq, Pi.add_apply] at hx hy ⊢
  have hcs : (x 0 * y 0 + x 1 * y 1) ^ 2 ≤ (x 0 ^ 2 + x 1 ^ 2) * (y 0 ^ 2 + y 1 ^ 2) := by
    nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0)]
  have hdot : x 0 * y 0 + x 1 * y 1 ≤ a * b := by
    by_contra hcon
    push Not at hcon
    have : (a * b) ^ 2 < (x 0 * y 0 + x 1 * y 1) ^ 2 := by
      have : 0 ≤ a * b := by positivity
      nlinarith
    nlinarith [mul_le_mul hx hy (by positivity) (by positivity)]
  nlinarith

/-- Distinct translates of a nonempty compact set are distinct. -/
theorem ft_translate_injective {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hne : K.Nonempty) :
    Function.Injective fun l : Fin 2 → ℝ ↦ (fun x ↦ x + l) '' K := by
  intro l l' h
  set v := l - l'
  have hcont : Continuous fun x : Fin 2 → ℝ ↦ v ⬝ᵥ x := by fun_prop
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne hcont.continuousOn
  have : y + l ∈ (fun x ↦ x + l') '' K := by
    rw [← show (fun x ↦ x + l) '' K = (fun x ↦ x + l') '' K from h]
    exact ⟨y, hy, rfl⟩
  obtain ⟨y', hy', hyy'⟩ := this
  simp only at hyy'
  have hy'eq : y' = y + v := by
    rw [show y' = y' + l' - l' from (add_sub_cancel_right y' l').symm, hyy']
    simp only [v]
    rw [add_sub_assoc]
  have := hmax hy'
  simp only [mem_ofPred_eq, hy'eq, dotProduct_add] at this
  have hvv : v ⬝ᵥ v = 0 := by
    have : v ⬝ᵥ v ≤ 0 := by linarith
    have h0 : 0 ≤ v ⬝ᵥ v := by
      simp only [dotProduct, Fin.sum_univ_two]
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    linarith
  have hv : v = 0 := by
    simp only [dotProduct, Fin.sum_univ_two] at hvv
    ext i
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  exact sub_eq_zero.1 hv

/-- If the translates `P + L` cover the plane and `K ⊆ P`, the upper density of `K + L` is at least
`|K| / |P|`. -/
theorem ft_le_upperDensity_translates {K P : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K)
    (hKP : K ⊆ P) (hP : Bornology.IsBounded P) {L : Submodule ℤ (Fin 2 → ℝ)} (hL : IsLattice L)
    (hcover : ∀ x, ∃ l ∈ L, x - l ∈ P) :
    volume K / volume P ≤ upperDensity (translates K L) := by
  classical
  obtain ⟨hconv, hcpt, hint⟩ := hK
  have hne : K.Nonempty := hint.mono interior_subset
  have hvolK : volume K ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ hint).ne'
  have hvolP0 : volume P ≠ 0 := fun h ↦ hvolK (measure_mono_null hKP h)
  have hvolPtop : volume P ≠ ∞ := hP.measure_lt_top.ne
  set c' := volume K / volume P
  have hc' : volume P * c' = volume K := ENNReal.mul_div_cancel hvolP0 hvolPtop
  -- `P` lies in a disk
  obtain ⟨R0, hR0⟩ := hP.subset_closedBall 0
  set R := 2 * max R0 0
  have hR : 0 ≤ R := by positivity
  have hPR : P ⊆ disk R := by
    intro p hp
    have hb : ∀ i, |p i| ≤ max R0 0 := fun i ↦ (norm_le_pi_norm p i).trans
      ((mem_closedBall_zero_iff.1 (hR0 hp)).trans (le_max_left _ _))
    have h0 := abs_le.1 (hb 0)
    have h1 := abs_le.1 (hb 1)
    have : 0 ≤ max R0 0 := le_max_right _ _
    simp only [disk, mem_ofPred_eq, R]
    nlinarith
  set v1 := (volume (disk 1)).toReal
  have hv1 : volume (disk 1) = ENNReal.ofReal v1 :=
    (ENNReal.ofReal_toReal ft_volume_disk_one_ne_top).symm
  have hv1pos : 0 < v1 := ENNReal.toReal_pos ft_volume_disk_one_ne_zero ft_volume_disk_one_ne_top
  have key : ∀ r : ℝ, 2 * R + 1 ≤ r → ENNReal.ofReal (((r - 2 * R) / r) ^ 2) * c' ≤
      (∑' A : translates K L, volume ((A : Set (Fin 2 → ℝ)) ∩ disk r)) / volume (disk r) := by
    intro r hr
    have hr0 : 0 < r := by linarith
    have hr2 : 0 < r - 2 * R := by linarith
    -- the lattice points in `D_{r - R}`
    have hfin : (disk (r - R) ∩ (L : Set (Fin 2 → ℝ))).Finite := ft_finite_inter hL.1
      (Metric.isBounded_Icc (fun _ ↦ -(r - R)) (fun _ ↦ r - R) |>.subset fun x hx ↦ by
        simp only [disk, mem_ofPred_eq] at hx
        refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;> fin_cases i <;> simp <;>
          nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)])
    set G := hfin.toFinset
    have hcov : disk (r - 2 * R) ⊆ ⋃ l ∈ G, (fun x ↦ x + l) '' P := by
      intro x hx
      obtain ⟨l, hl, hxl⟩ := hcover x
      have hlr : l ∈ disk (r - R) := by
        have := ft_add_mem_disk hr2.le hR hx (ft_neg_mem_disk (hPR hxl))
        rwa [show x + -(x - l) = l by rw [neg_sub, add_sub_cancel],
          show r - 2 * R + R = r - R by ring] at this
      exact mem_iUnion₂.2 ⟨l, hfin.mem_toFinset.2 ⟨hlr, hl⟩, x - l, hxl, sub_add_cancel x l⟩
    have hG1 : volume (disk (r - 2 * R)) ≤ G.card * volume P := by
      refine (measure_mono hcov).trans ((measure_biUnion_finset_le G _).trans (le_of_eq ?_))
      rw [Finset.sum_congr rfl fun l _ ↦ by rw [image_add_right, measure_preimage_add_right],
        Finset.sum_const, nsmul_eq_mul]
    have hG2 : (G.card : ℝ≥0∞) * volume K ≤
        ∑' A : translates K L, volume ((A : Set (Fin 2 → ℝ)) ∩ disk r) := by
      let φ : L → translates K L := fun l ↦ ⟨(fun x ↦ x + (l : Fin 2 → ℝ)) '' K, l, rfl⟩
      have hφ : Function.Injective φ := fun l l' h ↦
        Subtype.ext (ft_translate_injective hcpt hne (congrArg Subtype.val h))
      have hGL : ∀ l ∈ G, l ∈ L := fun l hl ↦ (hfin.mem_toFinset.1 hl).2
      have hin : ∀ l ∈ G, (fun x ↦ x + l) '' K ⊆ disk r := by
        intro l hl
        rintro _ ⟨x, hx, rfl⟩
        have := ft_add_mem_disk hR (by linarith) (hPR (hKP hx)) (hfin.mem_toFinset.1 hl).1
        rwa [show R + (r - R) = r by ring] at this
      calc (G.card : ℝ≥0∞) * volume K
          = ∑ l ∈ G.subtype (· ∈ L), volume ((φ l : Set (Fin 2 → ℝ)) ∩ disk r) := by
            rw [Finset.sum_congr rfl fun l hl ↦ by
              rw [inter_eq_left.2 (hin _ (Finset.mem_subtype.1 hl)), image_add_right,
                measure_preimage_add_right],
              Finset.sum_const, nsmul_eq_mul, Finset.card_subtype,
              Finset.filter_true_of_mem hGL]
        _ ≤ ∑' l : L, volume ((φ l : Set (Fin 2 → ℝ)) ∩ disk r) := sum_le_tsum _
        _ ≤ ∑' A : translates K L, volume ((A : Set (Fin 2 → ℝ)) ∩ disk r) :=
            tsum_comp_le_tsum_of_injective hφ
              (fun A : translates K L ↦ volume ((A : Set (Fin 2 → ℝ)) ∩ disk r))
    have hV0 : volume (disk r) ≠ 0 := by
      rw [ft_volume_disk hr0]
      exact mul_ne_zero (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)
        ft_volume_disk_one_ne_zero
    have hVtop : volume (disk r) ≠ ∞ := by
      rw [ft_volume_disk hr0]
      exact ENNReal.mul_ne_top (by simp) ft_volume_disk_one_ne_top
    rw [ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVtop)]
    refine le_trans (le_of_eq ?_) (le_trans (mul_le_mul_left hG1 c') ?_)
    · rw [ft_volume_disk hr0, ft_volume_disk hr2]
      calc ENNReal.ofReal (((r - 2 * R) / r) ^ 2) * c' * (ENNReal.ofReal (r ^ 2) * volume (disk 1))
          = ENNReal.ofReal (r ^ 2 * ((r - 2 * R) / r) ^ 2) * volume (disk 1) * c' := by
            rw [ENNReal.ofReal_mul (by positivity)]
            ring
        _ = _ := by
            congr 3
            field_simp
    · rw [mul_assoc, hc']
      exact hG2
  have hT : Tendsto (fun r ↦ ENNReal.ofReal (((r - 2 * R) / r) ^ 2) * c') atTop (nhds c') := by
    have h1 : Tendsto (fun r : ℝ ↦ ((r - 2 * R) / r) ^ 2) atTop (nhds 1) := by
      have : Tendsto (fun r : ℝ ↦ (1 - 2 * R * r⁻¹) ^ 2) atTop (nhds ((1 - 2 * R * 0) ^ 2)) :=
        ((tendsto_const_nhds.sub (tendsto_inv_atTop_zero.const_mul (2 * R))).pow 2)
      simp only [mul_zero, sub_zero, one_pow] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with r hr
      field_simp
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (b := c') (Or.inl (by simp))
    simpa using this
  calc c' = limsup (fun r ↦ ENNReal.ofReal (((r - 2 * R) / r) ^ 2) * c') atTop :=
        hT.limsup_eq.symm
    _ ≤ upperDensity (translates K L) :=
        Filter.limsup_le_limsup ((eventually_ge_atTop (2 * R + 1)).mono key)

theorem ft_div_le_latticePackingDensity {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K)
    (hsymm : IsCentrallySymmetric K) :
    volume K / minCircumscribedArea K 6 ≤ latticePackingDensity K := by
  rw [ft_minCircumscribedArea_six_eq_iInf_symm hK hsymm, ENNReal.div_eq_inv_mul,
    ENNReal.inv_iInf, ENNReal.iSup_mul]
  refine iSup_le fun c ↦ ?_
  rw [← ENNReal.div_eq_inv_mul]
  by_cases hfin : volume (circPolygon K (Sum.elim c fun i ↦ c i + π)) = ∞
  · simp [hfin]
  obtain ⟨L, hL, hpack, hbdd, hcover⟩ := ft_hexagon_lattice hK hsymm c hfin
  exact (ft_le_upperDensity_translates hK (subset_circPolygon hK.2.1 _) hbdd hL hcover).trans
    (le_iSup_of_le L (le_iSup_of_le hL (le_iSup_of_le hpack le_rfl)))

theorem ft_latticePackingDensity_le_packingDensity (K : Set (Fin 2 → ℝ)) :
    latticePackingDensity K ≤ packingDensity K := by
  refine iSup_le fun L ↦ iSup_le fun _ ↦ iSup_le fun hpack ↦ ?_
  refine le_iSup_of_le (translates K L) (le_iSup_of_le hpack (le_iSup_of_le ?_ le_rfl))
  rintro _ ⟨l, rfl⟩
  refine ⟨1, one_mem _, l, ?_⟩
  simp

end FejesToth

open FejesToth in
/-- **Fejes Tóth (1950).** For a centrally symmetric convex disk `K`, the greatest packing density
of `K` equals its greatest lattice packing density: `δ(K) = δ_L(K)`. -/
theorem fejes_toth {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K) (hsymm : IsCentrallySymmetric K) :
    packingDensity K = latticePackingDensity K := by
  refine le_antisymm (iSup_le fun 𝒜 ↦ iSup_le fun hpack ↦ iSup_le fun hcong ↦ ?_)
    (ft_latticePackingDensity_le_packingDensity K)
  exact (ft_upperDensity_le hK hpack hcong).trans (ft_div_le_latticePackingDensity hK hsymm)

end External
