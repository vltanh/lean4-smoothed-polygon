module

public import External.MahlerIrreducible

/-!
# Mahler 1946, Theorems D and E, and Lemma 12 of paper A

K. Mahler, *Lattice points in n-dimensional star bodies II. Reducibility theorems I*,
Proc. Kon. Ned. Akad. Wet. 49 (1946), 331–343 (scan: Mahler's collected works, CARMA archive,
item 088), §4 "A sufficient condition for irreducibility": Definition B (pp. 338–339), Theorem D
(p. 340) and Theorem E (p. 341); and Lemma 12 of K. Mahler, *On irreducible convex domains*,
Proc. Kon. Ned. Akad. Wet. 50 (1947), 98–107 ("paper A", p. 104), which quotes it from
Theorems D and E (its footnote 7).

## Readings

Mahler works with star bodies `F(X) ≤ 1` of `ℝⁿ` (`F` a continuous distance function), calls `K`
*reducible* if there is a star body `H ⊊ K` with `Δ(H) = Δ(K)` (Definition A, p. 334), and an
*inner point* of `K` a point with `F(X) < 1`. We specialize to the plane and to symmetric convex
domains (`IsSymmetricConvexDomain`; inner points are interior points, `C` is `frontier K`), and to
irreducibility against symmetric convex subdomains (`MahlerIrreducible.IsIrreducible`; paper A's
Lemma 13 shows that for convex `K` the two notions agree). Mahler's Euclidean `|X - Q|` is replaced
by the sup norm of `Fin 2 → ℝ` (only neighbourhoods matter).

*Definition B* (`IsFree`). Mahler fixes a reduced basis `Y₁, Y₂` of the critical lattice `Λ`; a
lattice `Λ*` lies in an `ε`-neighbourhood of `Λ` if it has a basis `Y₁*, Y₂*` with
`|Y_g* - Y_g| < ε`, and then `P* = u₁ Y₁* + u₂ Y₂*` corresponds to `P = u₁ Y₁ + u₂ Y₂`. `Λ` is
*free* if for every point `P` of `Λ` on `C` and every `ε > 0` there is such a `Λ*` with
`d(Λ*) < d(Λ)` having no inner points of `K` except `O` and `±P*`. We ask this for some basis of
`Λ` (any fixed basis gives the same notion; a reduced basis is one of them), and prove Theorem E
for every basis (`m46e_free_at`).

## Proofs, following Mahler

* **Theorem D** (`theoremD`): a dense set `Σ ⊆ C` of points on free lattices makes `K`
  irreducible. Mahler's proof: if `H ⊊ K` had `Δ(H) = Δ(K)`, take `Q ∈ C` outside `H`
  (`ml3_exists_frontier_notMem`) with a neighbourhood `|X - Q| ≤ ε` outside `H`, `P ∈ Σ` with
  `|P - Q| ≤ ε / 2` and `Λ*` as in Definition B with `|P* - P| ≤ ε / 2` (Mahler leaves the passage
  from (a) to this bound to the reader); `Λ*` is `H`-admissible, so
  `Δ(H) ≤ d(Λ*) < d(Λ) = Δ(K)`.
* **Theorem E** (`theoremE`): a critical lattice with just six points on `C` is free. Mahler's
  proof: by (A) (Minkowski; `minkowski_mahler`) the six points are `±A, ±B, ±(A + B)` for a basis
  `A, B` of `Λ`, and the chosen point may be taken to be `A + B` (`m46e_hex_neg`, `m46e_hex_rot`,
  `m46e_hex_rot'`); a line `L` separates it from the other five (Mahler infers its existence from
  "no three of the six points are collinear"; we write it down: `φ = 3/2`, `φ(sA + tB) = s + t`);
  `K* = K ∩ {|φ| ≤ 3/2}` is a symmetric convex domain (`MahlerIrreducible.irr_cut`) with only the
  four points `±A, ±B` of `Λ` on its boundary; a neighbouring `K*`-admissible lattice `Λ*` of
  smaller determinant exists; and it satisfies Definition B (`m46e_hex_deform`).
  - *Gap in Mahler 1946* (filled): "since only four points of `Λ` lie on the boundary of `K*`,
    there exists a neighbouring lattice `Λ*` which is `K*`-admissible and of determinant
    `d(Λ*) < d(Λ)`" is asserted without argument (it is a local form of (A); (A) itself only
    gives a `K*`-admissible lattice of smaller determinant somewhere, not a neighbouring one). We
    fill it with the deformation by which (A) is proved in `External.MinkowskiMahler`
    (`mm_add_or_sub_mem`): turn `A` and `B` along support lines `f = 1`, `g = 1` of `K*`,
    `A(t) = (1 - τ t f(B)) A + τ t B`, `B(t) = τ t A + (1 - τ t g(A)) B` (`τ = ±1`), whose
    determinant is `(1 - t |f(B) + g(A)| + t² (f(B) g(A) - 1)) det(A, B)`, smaller in absolute
    value than `det(A, B)` for small `t > 0` (`m46e_turn`).
  - Mahler's statement in §4 that "the points `P_k*` are then the only points of `Λ*` which lie on,
    or near to, the boundary `C` of `K`, if `ε` sufficiently small" is given there without proof;
    we prove it in the form used (`m46e_near`), and use it both for `K*` (admissibility of `Λ*`)
    and for `K` (condition (c) of Definition B).
* **Lemma 12 of paper A** (`m46e_lemma12`): if every point of `C` lies on a critical lattice, `K`
  is irreducible. Paper A quotes it from Theorems D and E. *Gap in paper A* (filled from paper A
  itself): Theorem E applies only to critical lattices with just six points on `C`, and Theorem D
  needs a dense set of points on such lattices; this does not follow from `Π = C` alone. Paper A
  supplies it: if `K` is not a parallelogram, every critical lattice has just six points on `C`
  (Corollary to Lemma 5, `ml5_lemma5_cor_six`; `m46e_cor_ncard`), so Theorems E and D apply with
  `Σ = C`; a parallelogram is irreducible by Lemma 1 (`ml5_lemma1`), the way paper A sets
  parallelograms aside before Lemma 5. (The 1946 paper treats the square by Theorems D and E
  directly, Example (a) on p. 342, using the six-point critical lattices through the boundary
  points other than the vertices and the midpoints of the sides.)
-/

@[expose] public section

namespace External

namespace Mahler1946

open Set Filter Topology MinkowskiMahler MahlerIrreducible

variable {K : Set (Fin 2 → ℝ)}

/-! ### Neighbouring lattices (§4) -/

/-- **The points of a neighbouring lattice in `K`** (Mahler 1946, §4: "The points `P_k*` … are
then the only points of `Λ*` which lie on, or near to, the boundary `C` of `K`, if `ε` sufficiently
small", stated there without proof). Let `u, v` be a basis of a lattice and `A i → u`, `B i → v`.
Eventually, a point `m A i + n B i` lies in `K` only if `m u + n v` does: the coefficients of the
points in `K` are bounded (Cramer's rule), and for each of the finitely many pairs `(m, n)` with
`m u + n v ∉ K`, the point `m A i + n B i` eventually stays outside the closed set `K`. -/
lemma m46e_near (hK : IsSymmetricConvexDomain K) {u v : Fin 2 → ℝ} (huv : cross u v ≠ 0)
    {ι : Type*} {l : Filter ι} {A B : ι → Fin 2 → ℝ}
    (hA : Tendsto A l (𝓝 u)) (hB : Tendsto B l (𝓝 v)) :
    ∀ᶠ i in l, ∀ m n : ℤ, (m : ℝ) • A i + (n : ℝ) • B i ∈ K → (m : ℝ) • u + (n : ℝ) • v ∈ K := by
  obtain ⟨R, hR⟩ : ∃ R, ∀ x ∈ K, ‖x‖ ≤ R := hK.2.1.isBounded.exists_norm_le
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0 (interior_subset (mm_zero_mem_interior hK)))
  set c := |cross u v| with hc
  have hcpos : 0 < c := abs_pos.2 huv
  have hcross : Tendsto (fun i ↦ cross (A i) (B i)) l (𝓝 (cross u v)) := by
    have hA0 := tendsto_pi_nhds.1 hA 0
    have hA1 := tendsto_pi_nhds.1 hA 1
    have hB0 := tendsto_pi_nhds.1 hB 0
    have hB1 := tendsto_pi_nhds.1 hB 1
    exact (hA0.mul hB1).sub (hA1.mul hB0)
  have hev1 : ∀ᶠ i in l, c / 2 < |cross (A i) (B i)| :=
    hcross.abs.eventually (lt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ i in l, ‖A i‖ < ‖u‖ + 1 := hA.norm.eventually (gt_mem_nhds (by linarith))
  have hev3 : ∀ᶠ i in l, ‖B i‖ < ‖v‖ + 1 := hB.norm.eventually (gt_mem_nhds (by linarith))
  set N : ℕ := ⌈4 * R * (‖u‖ + ‖v‖ + 2) / c⌉₊ with hN
  have hNge : 4 * R * (‖u‖ + ‖v‖ + 2) / c ≤ N := Nat.le_ceil _
  -- the coefficients of the lattice points in `K` are bounded by `N`
  have hbound : ∀ i, c / 2 < |cross (A i) (B i)| → ‖A i‖ < ‖u‖ + 1 → ‖B i‖ < ‖v‖ + 1 →
      ∀ m n : ℤ, (m : ℝ) • A i + (n : ℝ) • B i ∈ K → |(m : ℝ)| ≤ N ∧ |(n : ℝ)| ≤ N := by
    intro i h1 h2 h3 m n hmem
    have hx := hR _ hmem
    have e1 : cross ((m : ℝ) • A i + (n : ℝ) • B i) (B i) = m * cross (A i) (B i) := by
      rw [mm_cross_smul_add, mm_cross_self]; ring
    have e2 : cross (A i) ((m : ℝ) • A i + (n : ℝ) • B i) = n * cross (A i) (B i) := by
      rw [mm_cross_add_smul, mm_cross_self]; ring
    have b1 := mm_abs_cross_le ((m : ℝ) • A i + (n : ℝ) • B i) (B i)
    have b2 := mm_abs_cross_le (A i) ((m : ℝ) • A i + (n : ℝ) • B i)
    rw [e1, abs_mul] at b1
    rw [e2, abs_mul] at b2
    have hnu := norm_nonneg u
    have hnv := norm_nonneg v
    have hnA := norm_nonneg (A i)
    have hnB := norm_nonneg (B i)
    have hm0 := abs_nonneg (m : ℝ)
    have hn0 := abs_nonneg (n : ℝ)
    constructor
    · refine le_trans ?_ hNge
      rw [le_div_iff₀ hcpos]
      have : |(m : ℝ)| * (c / 2) ≤ 2 * R * (‖v‖ + 1) := by
        calc |(m : ℝ)| * (c / 2) ≤ |(m : ℝ)| * |cross (A i) (B i)| := by gcongr
          _ ≤ 2 * ‖(m : ℝ) • A i + (n : ℝ) • B i‖ * ‖B i‖ := b1
          _ ≤ 2 * R * (‖v‖ + 1) := by gcongr
      nlinarith
    · refine le_trans ?_ hNge
      rw [le_div_iff₀ hcpos]
      have : |(n : ℝ)| * (c / 2) ≤ 2 * (‖u‖ + 1) * R := by
        calc |(n : ℝ)| * (c / 2) ≤ |(n : ℝ)| * |cross (A i) (B i)| := by gcongr
          _ ≤ 2 * ‖A i‖ * ‖(m : ℝ) • A i + (n : ℝ) • B i‖ := b2
          _ ≤ 2 * (‖u‖ + 1) * R := by gcongr
      nlinarith
  -- in the finite box of coefficients, the points off `K` eventually stay off `K`
  set S : Finset (ℤ × ℤ) := Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N
  have hevS : ∀ᶠ i in l, ∀ p ∈ S, (p.1 : ℝ) • A i + (p.2 : ℝ) • B i ∈ K →
      (p.1 : ℝ) • u + (p.2 : ℝ) • v ∈ K := by
    rw [Filter.eventually_all_finset]
    intro p _
    by_cases hK' : (p.1 : ℝ) • u + (p.2 : ℝ) • v ∈ K
    · exact Eventually.of_forall fun i _ ↦ hK'
    · have hT : Tendsto (fun i ↦ (p.1 : ℝ) • A i + (p.2 : ℝ) • B i) l
          (𝓝 ((p.1 : ℝ) • u + (p.2 : ℝ) • v)) := (hA.const_smul _).add (hB.const_smul _)
      exact (hT.eventually ((mm_isClosed hK).isOpen_compl.mem_nhds hK')).mono
        fun i hi hmem ↦ absurd hmem hi
  filter_upwards [hev1, hev2, hev3, hevS] with i h1 h2 h3 h5
  intro m n hmem
  obtain ⟨hm, hn⟩ := hbound i h1 h2 h3 m n hmem
  have hm' := abs_le.1 hm
  have hn' := abs_le.1 hn
  refine h5 (m, n) ?_ hmem
  simp only [S, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have : (-(N : ℝ)) ≤ m := hm'.1
    exact_mod_cast this
  · have : (m : ℝ) ≤ N := hm'.2
    exact_mod_cast this
  · have : (-(N : ℝ)) ≤ n := hn'.1
    exact_mod_cast this
  · have : (n : ℝ) ≤ N := hn'.2
    exact_mod_cast this

/-- Coefficients in a basis `u, v` are unique. -/
lemma m46e_coeff {u v X : Fin 2 → ℝ} (huv : cross u v ≠ 0) {m n : ℤ} (m' n' : ℤ)
    (h : (m : ℝ) • u + (n : ℝ) • v = X) (hX : X = (m' : ℝ) • u + (n' : ℝ) • v) :
    m = m' ∧ n = n' := by
  by_contra hne
  have hmn : m - m' ≠ 0 ∨ n - n' ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hne ⟨by omega, by omega⟩
  apply mm_comb_ne_zero huv hmn
  have h0 : (m : ℝ) • u + (n : ℝ) • v - ((m' : ℝ) • u + (n' : ℝ) • v) = 0 := by
    rw [h, hX, sub_self]
  rw [← h0]
  push_cast
  module

/-! ### Definition B and Theorem D -/

/-- **Definition B** (Mahler 1946, pp. 338–339), in the plane: the critical lattice `Λ` of `K` is
*free* if, for a basis `Y₁, Y₂` of `Λ` (Mahler: a reduced basis), to every point
`P = u₁ Y₁ + u₂ Y₂` of `Λ` on the boundary `C` of `K` and to every `ε > 0` there is a lattice
`Λ*` with (a) a basis `Y₁*, Y₂*` such that `|Y_g* - Y_g| < ε` ("`Λ*` lies in an `ε`-neighbourhood
of `Λ`"), (b) `d(Λ*) < d(Λ)`, and (c) no inner points of `K` except `O` and `±P*`, where
`P* = u₁ Y₁* + u₂ Y₂*` is the point of `Λ*` corresponding to `P`. -/
def IsFree (K : Set (Fin 2 → ℝ)) (Λ : Submodule ℤ (Fin 2 → ℝ)) : Prop :=
  IsCritical K Λ ∧ ∃ Y₁ Y₂ : Fin 2 → ℝ, IsBasis Λ Y₁ Y₂ ∧
    ∀ u₁ u₂ : ℤ, (u₁ : ℝ) • Y₁ + (u₂ : ℝ) • Y₂ ∈ frontier K → ∀ ε > 0,
      ∃ Y₁' Y₂' : Fin 2 → ℝ, ‖Y₁' - Y₁‖ < ε ∧ ‖Y₂' - Y₂‖ < ε ∧ cross Y₁' Y₂' ≠ 0 ∧
        det (Submodule.span ℤ {Y₁', Y₂'}) < det Λ ∧
        ∀ X ∈ Submodule.span ℤ {Y₁', Y₂'}, X ∈ interior K →
          X = 0 ∨ X = (u₁ : ℝ) • Y₁' + (u₂ : ℝ) • Y₂' ∨ X = -((u₁ : ℝ) • Y₁' + (u₂ : ℝ) • Y₂')

/-- **Mahler (1946), Theorem D**, for symmetric convex domains in the plane: *Let `K` be a bounded
star body, and `Σ` a set of points on its boundary `C` which is everywhere dense. If further `P` is
any point of `Σ`, let there be a free lattice of `K` containing `P`. Then `K` is irreducible.*

Mahler's proof. Assume `H ⊊ K` with `Δ(H) = Δ(K)`. There is a point `Q` on `C` outside `H`, and
`ε > 0` such that all `X` with `|X - Q| ≤ ε` lie outside `H`. Take `P ∈ Σ` with `|P - Q| ≤ ε / 2`
and the free lattice `Λ` through `P`; by Definition B there is a lattice `Λ*` with
`d(Λ*) < d(Λ)` containing no inner points of `K` except `O` and `±P*`, `|P* - P| ≤ ε / 2`, so that
`|P* - Q| ≤ ε`. Hence `Λ*` is `H`-admissible and `Δ(H) ≤ d(Λ*) < d(Λ) = Δ(K)`. -/
theorem theoremD (hK : IsSymmetricConvexDomain K) {S : Set (Fin 2 → ℝ)} (hS : S ⊆ frontier K)
    (hdense : frontier K ⊆ closure S) (hfree : ∀ P ∈ S, ∃ Λ, IsFree K Λ ∧ P ∈ Λ) :
    MahlerIrreducible.IsIrreducible K := by
  refine ⟨hK, fun H hH hsub hne ↦ lt_of_le_of_ne (ml3_minDet_mono hK hsub) fun hEq ↦ ?_⟩
  -- a point `Q` of `C` outside `H`, and a neighbourhood `|X - Q| ≤ ε` outside `H`
  obtain ⟨Q, hQ, hQH⟩ := ml3_exists_frontier_notMem hK hH hsub hne
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hH.2.1.isClosed.isOpen_compl Q hQH
  set ε := δ / 2 with hεdef
  have hε : 0 < ε := by positivity
  have hout : ∀ X, dist X Q ≤ ε → X ∉ H := fun X hX ↦ hball (Metric.mem_ball.2 (by linarith))
  -- a point `P ∈ Σ` with `|P - Q| ≤ ε / 2`, on a free lattice `Λ`
  obtain ⟨P, hPS, hPQ⟩ := Metric.mem_closure_iff.1 (hdense hQ) (ε / 2) (by positivity)
  obtain ⟨Λ, ⟨hΛ, Y₁, Y₂, hY, hfr⟩, hPΛ⟩ := hfree P hPS
  rw [← hY.2] at hPΛ
  obtain ⟨u₁, u₂, rfl⟩ := mm_mem_span_pair.1 hPΛ
  set M : ℝ := |(u₁ : ℝ)| + |(u₂ : ℝ)| + 1 with hMdef
  have hM : 0 < M := by positivity
  -- the lattice `Λ*` of Definition B, with `|Y_g* - Y_g| < ε / (2M)`
  obtain ⟨Y₁', Y₂', h1, h2, hcr, hdet, hc⟩ :=
    hfr u₁ u₂ (hS hPS) (ε / 2 / M) (by positivity)
  set P' := (u₁ : ℝ) • Y₁' + (u₂ : ℝ) • Y₂' with hP'def
  have hPP : dist P' ((u₁ : ℝ) • Y₁ + (u₂ : ℝ) • Y₂) ≤ ε / 2 := by
    rw [dist_eq_norm]
    have e : P' - ((u₁ : ℝ) • Y₁ + (u₂ : ℝ) • Y₂) =
        (u₁ : ℝ) • (Y₁' - Y₁) + (u₂ : ℝ) • (Y₂' - Y₂) := by
      rw [hP'def]; module
    rw [e]
    have hu₁ := abs_nonneg (u₁ : ℝ)
    have hu₂ := abs_nonneg (u₂ : ℝ)
    calc ‖(u₁ : ℝ) • (Y₁' - Y₁) + (u₂ : ℝ) • (Y₂' - Y₂)‖
        ≤ ‖(u₁ : ℝ) • (Y₁' - Y₁)‖ + ‖(u₂ : ℝ) • (Y₂' - Y₂)‖ := norm_add_le _ _
      _ = |(u₁ : ℝ)| * ‖Y₁' - Y₁‖ + |(u₂ : ℝ)| * ‖Y₂' - Y₂‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |(u₁ : ℝ)| * (ε / 2 / M) + |(u₂ : ℝ)| * (ε / 2 / M) := by gcongr
      _ ≤ M * (ε / 2 / M) := by
        rw [← add_mul]; gcongr; linarith
      _ = ε / 2 := by field_simp
  have hP'Q : dist P' Q ≤ ε := by
    have := dist_triangle P' ((u₁ : ℝ) • Y₁ + (u₂ : ℝ) • Y₂) Q
    rw [dist_comm ((u₁ : ℝ) • Y₁ + (u₂ : ℝ) • Y₂) Q] at this
    linarith
  have hP'H : P' ∉ H := hout _ hP'Q
  have hnP'H : -P' ∉ H := fun h ↦ hP'H (by simpa using hH.2.2.2 _ h)
  -- `Λ*` is `H`-admissible
  have hadm : IsAdmissible H (Submodule.span ℤ {Y₁', Y₂'}) := fun X hX hXi ↦ by
    rcases hc X hX (interior_mono hsub hXi) with h | h | h
    · exact h
    · exact absurd (h ▸ interior_subset hXi) hP'H
    · exact absurd (h ▸ interior_subset hXi) hnP'H
  have hle := mm_minimalDeterminant_le (mm_isLattice_span hcr) hadm
  have hΔ := hΛ.2.2
  linarith

/-! ### Theorem E -/

/-- The six points `±A, ±B, ±(A + B)` of Minkowski's theorem (A) as the only points of `Λ` on `C`:
`A, B, A + B` lie on `C`, `A, B` is a basis of `Λ`, and the points of `Λ` in `K` are
`O, ±A, ±B, ±(A + B)`. -/
def m46e_IsHex (K : Set (Fin 2 → ℝ)) (Λ : Submodule ℤ (Fin 2 → ℝ)) (A B : Fin 2 → ℝ) : Prop :=
  A ∈ frontier K ∧ B ∈ frontier K ∧ A + B ∈ frontier K ∧ Submodule.span ℤ {A, B} = Λ ∧
    ∀ X ∈ Λ, X ∈ K → X = 0 ∨ X = A ∨ X = -A ∨ X = B ∨ X = -B ∨ X = A + B ∨ X = -(A + B)

section Hex

variable {Λ : Submodule ℤ (Fin 2 → ℝ)} {A B : Fin 2 → ℝ}

/-- The point `-(A + B)` of the hexagon as the sum of `-A, -B`. -/
lemma m46e_hex_neg (hK : IsSymmetricConvexDomain K) (h : m46e_IsHex K Λ A B) :
    m46e_IsHex K Λ (-A) (-B) := by
  obtain ⟨hA, hB, hAB, hspan, hpts⟩ := h
  have hab := mm_cross_ne_zero hK hA hB hAB
  refine ⟨mm_neg_mem_frontier hK hA, mm_neg_mem_frontier hK hB,
    by rw [← neg_add]; exact mm_neg_mem_frontier hK hAB, ?_, fun X hX hXK ↦ ?_⟩
  · rw [← hspan]
    refine mm_span_eq hab (mm_mem_span_pair.2 ⟨-1, 0, by simp⟩)
      (mm_mem_span_pair.2 ⟨0, -1, by simp⟩) ?_
    congr 1; simp only [cross, Pi.neg_apply]; ring
  · rcases hpts X hX hXK with h | h | h | h | h | h | h
    · exact Or.inl h
    · iterate 2 right
      left; rw [h, neg_neg]
    · right; left; exact h
    · iterate 4 right
      left; rw [h, neg_neg]
    · iterate 3 right
      left; exact h
    · iterate 6 right
      rw [h]; abel
    · iterate 5 right
      left; rw [h]; abel

/-- The point `B` of the hexagon as the sum of `A + B, -A`. -/
lemma m46e_hex_rot (hK : IsSymmetricConvexDomain K) (h : m46e_IsHex K Λ A B) :
    m46e_IsHex K Λ (A + B) (-A) := by
  obtain ⟨hA, hB, hAB, hspan, hpts⟩ := h
  have hab := mm_cross_ne_zero hK hA hB hAB
  refine ⟨hAB, mm_neg_mem_frontier hK hA, by rw [show A + B + -A = B by abel]; exact hB, ?_,
    fun X hX hXK ↦ ?_⟩
  · rw [← hspan]
    refine mm_span_eq hab (mm_mem_span_pair.2 ⟨1, 1, by simp⟩)
      (mm_mem_span_pair.2 ⟨-1, 0, by simp⟩) ?_
    congr 1; simp only [cross, Pi.neg_apply, Pi.add_apply]; ring
  · rcases hpts X hX hXK with h | h | h | h | h | h | h
    · exact Or.inl h
    · iterate 4 right
      left; rw [h, neg_neg]
    · iterate 3 right
      left; exact h
    · iterate 5 right
      left; rw [h]; abel
    · iterate 6 right
      rw [h]; abel
    · right; left; exact h
    · iterate 2 right
      left; exact h

/-- The point `A` of the hexagon as the sum of `-B, A + B`. -/
lemma m46e_hex_rot' (hK : IsSymmetricConvexDomain K) (h : m46e_IsHex K Λ A B) :
    m46e_IsHex K Λ (-B) (A + B) := by
  obtain ⟨hA, hB, hAB, hspan, hpts⟩ := h
  have hab := mm_cross_ne_zero hK hA hB hAB
  refine ⟨mm_neg_mem_frontier hK hB, hAB, by rw [show -B + (A + B) = A by abel]; exact hA, ?_,
    fun X hX hXK ↦ ?_⟩
  · rw [← hspan]
    refine mm_span_eq hab (mm_mem_span_pair.2 ⟨0, -1, by simp⟩)
      (mm_mem_span_pair.2 ⟨1, 1, by simp⟩) ?_
    congr 1; simp only [cross, Pi.neg_apply, Pi.add_apply]; ring
  · rcases hpts X hX hXK with h | h | h | h | h | h | h
    · exact Or.inl h
    · iterate 5 right
      left; rw [h]; abel
    · iterate 6 right
      rw [h]; abel
    · iterate 2 right
      left; rw [h, neg_neg]
    · right; left; exact h
    · iterate 3 right
      left; exact h
    · iterate 4 right
      left; exact h

end Hex

/-- **The neighbouring lattice of smaller determinant** (filling the gap in Mahler's proof of
Theorem E). Let `A, B` be boundary points of a symmetric convex domain `K'` (Mahler's `K*`),
independent, such that the only points of the lattice with basis `A, B` in `K'` are `O, ±A, ±B`.
Turning `A` and `B` along support lines `f = 1`, `g = 1` of `K'`,
`A(t) = (1 - τ t p) A + τ t B`, `B(t) = τ t A + (1 - τ t q) B` (`p = f(B)`, `q = g(A)`,
`τ = ±1` the sign of `p + q`), gives lattices tending to the given one, of determinant
`(1 - t |p + q| + t² (p q - 1)) |det(A, B)| < |det(A, B)|`, and `K'`-admissible for small `t > 0`:
by `m46e_near` their only possible points in `K'` are `O, ±A(t), ±B(t)`, which are not inner points
since `f(A(t)) = g(B(t)) = 1`. This is the deformation of `mm_add_or_sub_mem` (the proof of
Minkowski's theorem (A) in `External.MinkowskiMahler`). -/
lemma m46e_turn {K' : Set (Fin 2 → ℝ)} (hK : IsSymmetricConvexDomain K') {A B : Fin 2 → ℝ}
    (hab : cross A B ≠ 0) (hA : A ∈ frontier K') (hB : B ∈ frontier K')
    (hpts : ∀ X ∈ Submodule.span ℤ {A, B}, X ∈ K' → X = 0 ∨ X = A ∨ X = -A ∨ X = B ∨ X = -B) :
    ∃ A' B' : ℝ → Fin 2 → ℝ, Tendsto A' (𝓝[>] 0) (𝓝 A) ∧ Tendsto B' (𝓝[>] 0) (𝓝 B) ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), cross (A' t) (B' t) ≠ 0 ∧ |cross (A' t) (B' t)| < |cross A B| ∧
        IsAdmissible K' (Submodule.span ℤ {A' t, B' t}) := by
  have haK := mm_mem_of_frontier hK hA
  have hbK := mm_mem_of_frontier hK hB
  have hnaK := hK.2.2.2 A haK
  have hnbK := hK.2.2.2 B hbK
  obtain ⟨f, hf1, hf2, hf3⟩ := mm_support hK hA
  obtain ⟨g, hg1, hg2, hg3⟩ := mm_support hK hB
  set p := f B with hpdef
  set q := g A with hqdef
  have hp1 : |p| ≤ 1 := by
    have h1 := hf2 B hbK
    have h2 := hf2 (-B) hnbK
    rw [map_neg] at h2
    exact abs_le.2 ⟨by linarith, h1⟩
  have hq1 : |q| ≤ 1 := by
    have h1 := hg2 A haK
    have h2 := hg2 (-A) hnaK
    rw [map_neg] at h2
    exact abs_le.2 ⟨by linarith, h1⟩
  set τ : ℝ := if 0 ≤ p + q then 1 else -1 with hτdef
  have hτ : τ * (p + q) = |p + q| ∧ τ * τ = 1 := by
    by_cases h : 0 ≤ p + q
    · simp [hτdef, h, abs_of_nonneg h]
    · push Not at h; simp [hτdef, h.not_ge, abs_of_neg h]
  set A' : ℝ → Fin 2 → ℝ := fun t ↦ (1 - τ * t * p) • A + (τ * t) • B with hA'def
  set B' : ℝ → Fin 2 → ℝ := fun t ↦ (τ * t) • A + (1 - τ * t * q) • B with hB'def
  have hfA : ∀ t, f (A' t) = 1 := by
    intro t; simp only [hA'def, map_add, map_smul, smul_eq_mul, hf1, ← hpdef]; ring
  have hgB : ∀ t, g (B' t) = 1 := by
    intro t; simp only [hB'def, map_add, map_smul, smul_eq_mul, hg1, ← hqdef]; ring
  have tA : Tendsto A' (𝓝[>] 0) (𝓝 A) := by
    simpa [hA'def] using mm_tendsto_zero (f := A') (by rw [hA'def]; fun_prop)
  have tB : Tendsto B' (𝓝[>] 0) (𝓝 B) := by
    simpa [hB'def] using mm_tendsto_zero (f := B') (by rw [hB'def]; fun_prop)
  refine ⟨A', B', tA, tB, ?_⟩
  have hdet : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < |cross (A' t) (B' t)| ∧
      |cross (A' t) (B' t)| < |cross A B| := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hφ : cross (A' t) (B' t) = (1 - t * |p + q| + t ^ 2 * (p * q - 1)) * cross A B := by
      rw [hA'def, hB'def, mm_cross_comb, ← hτ.1]
      linear_combination (t ^ 2 * (p * q - 1) * cross A B) * hτ.2
    have hpq : |p * q| ≤ 1 := by rw [abs_mul]; nlinarith [abs_nonneg p, abs_nonneg q]
    have hpq' := abs_le.1 hpq
    have hs := abs_nonneg (p + q)
    have hs2 : |p + q| ≤ 2 := (abs_add_le p q).trans (by linarith)
    have hφpos : 0 < 1 - t * |p + q| + t ^ 2 * (p * q - 1) := by nlinarith
    have hφlt : 1 - t * |p + q| + t ^ 2 * (p * q - 1) < 1 := by
      rcases hs.lt_or_eq with h | h
      · nlinarith
      · have hq' : q = -p := by
          have := abs_eq_zero.1 h.symm; linarith
        have : p * q - 1 < 0 := by rw [hq']; nlinarith [sq_nonneg p]
        have : t ^ 2 * (p * q - 1) < 0 := mul_neg_of_pos_of_neg (by positivity) this
        rw [← h]; linarith
    rw [hφ, abs_mul, abs_of_pos hφpos]
    have := abs_pos.2 hab
    constructor <;> nlinarith
  filter_upwards [hdet, m46e_near hK hab tA tB] with t ⟨hpos, hlt⟩ hn
  refine ⟨fun h ↦ by rw [h, abs_zero] at hpos; exact lt_irrefl _ hpos, hlt, fun X hX hXi ↦ ?_⟩
  obtain ⟨m, n, rfl⟩ := mm_mem_span_pair.1 hX
  rcases hpts _ (mm_mem_span_pair.2 ⟨m, n, rfl⟩) (hn m n (interior_subset hXi)) with
    h | h | h | h | h
  · obtain ⟨rfl, rfl⟩ := m46e_coeff hab 0 0 h (by simp)
    simp
  · obtain ⟨rfl, rfl⟩ := m46e_coeff hab 1 0 h (by simp)
    have := hf3 _ (by simpa using hXi)
    rw [hfA] at this; exact absurd this (lt_irrefl _)
  · obtain ⟨rfl, rfl⟩ := m46e_coeff hab (-1) 0 h (by simp)
    have := hf3 _ (by simpa using mm_neg_mem_interior hK hXi)
    rw [hfA] at this; exact absurd this (lt_irrefl _)
  · obtain ⟨rfl, rfl⟩ := m46e_coeff hab 0 1 h (by simp)
    have := hg3 _ (by simpa using hXi)
    rw [hgB] at this; exact absurd this (lt_irrefl _)
  · obtain ⟨rfl, rfl⟩ := m46e_coeff hab 0 (-1) h (by simp)
    have := hg3 _ (by simpa using mm_neg_mem_interior hK hXi)
    rw [hgB] at this; exact absurd this (lt_irrefl _)

/-- **Mahler's construction in the proof of Theorem E**, for the chosen point `A + B` of a critical
lattice whose points on `C` are just `±A, ±B, ±(A + B)`. The line `L : φ = 3/2`, where
`φ(s A + t B) = s + t`, separates `A + B` from the five other points; the points of `K` not
separated from `O` by `L` or `-L` form the symmetric convex domain `K* = K ∩ {|φ| ≤ 3/2}`, on whose
boundary `Λ` has only the four points `±A, ±B`. A neighbouring `K*`-admissible lattice `Λ*` of
smaller determinant (`m46e_turn`, filling Mahler's gap) has no inner points of `K` except `O` and
`±(A* + B*)`: its points in `K` are `O, ±A*, ±B*, ±(A* + B*)` (`m46e_near`), and `±A*, ±B*` lie
strictly between `L` and `-L`, where `K` and `K*` have the same inner points. -/
lemma m46e_hex_deform (hK : IsSymmetricConvexDomain K) {Λ : Submodule ℤ (Fin 2 → ℝ)}
    {A B : Fin 2 → ℝ} (h : m46e_IsHex K Λ A B) :
    ∃ A' B' : ℝ → Fin 2 → ℝ, Tendsto A' (𝓝[>] 0) (𝓝 A) ∧ Tendsto B' (𝓝[>] 0) (𝓝 B) ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), cross (A' t) (B' t) ≠ 0 ∧ |cross (A' t) (B' t)| < |cross A B| ∧
        ∀ X ∈ Submodule.span ℤ {A' t, B' t}, X ∈ interior K →
          X = 0 ∨ X = A' t + B' t ∨ X = -(A' t + B' t) := by
  obtain ⟨hA, hB, hAB, hspan, hpts⟩ := h
  have hab := mm_cross_ne_zero hK hA hB hAB
  -- the line `L : φ = 3/2`, `φ(s A + t B) = s + t`
  set a : Fin 2 → ℝ := ![(B 1 - A 1) / cross A B, (A 0 - B 0) / cross A B] with hadef
  have hφ : ∀ X, a ⬝ᵥ X = (cross A X - cross B X) / cross A B := by
    intro X
    simp only [hadef, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      cross]
    field_simp
    ring
  have hφA : a ⬝ᵥ A = 1 := by
    rw [hφ, mm_cross_self, mm_cross_swap A B, zero_sub, neg_neg, div_self hab]
  have hφB : a ⬝ᵥ B = 1 := by rw [hφ, mm_cross_self, sub_zero, div_self hab]
  have hφAB : a ⬝ᵥ (A + B) = 2 := by rw [dotProduct_add, hφA, hφB]; norm_num
  -- the domain `K*`
  set Ks := K ∩ {X | |a ⬝ᵥ X| ≤ 3 / 2} with hKsdef
  have hKs : IsSymmetricConvexDomain Ks := irr_cut hK a (by norm_num)
  have hint : interior K ∩ {X | |a ⬝ᵥ X| < 3 / 2} ⊆ interior Ks :=
    interior_maximal (fun X hX ↦ ⟨interior_subset hX.1, show |a ⬝ᵥ X| ≤ 3 / 2 from hX.2.le⟩)
      (isOpen_interior.inter (isOpen_lt (irr_continuous_abs_dot a) continuous_const))
  have hAs : A ∈ frontier Ks := mm_mem_frontier hKs
    ⟨mm_mem_of_frontier hK hA, by rw [mem_ofPred_eq, hφA]; norm_num⟩
    fun hi ↦ hA.2 (interior_mono inter_subset_left hi)
  have hBs : B ∈ frontier Ks := mm_mem_frontier hKs
    ⟨mm_mem_of_frontier hK hB, by rw [mem_ofPred_eq, hφB]; norm_num⟩
    fun hi ↦ hB.2 (interior_mono inter_subset_left hi)
  -- the points of `Λ` in `K*` are `O, ±A, ±B`
  have hptss : ∀ X ∈ Submodule.span ℤ {A, B}, X ∈ Ks →
      X = 0 ∨ X = A ∨ X = -A ∨ X = B ∨ X = -B := by
    intro X hX hXs
    have hXs2 : |a ⬝ᵥ X| ≤ 3 / 2 := hXs.2
    rcases hpts X (hspan ▸ hX) hXs.1 with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · rw [h, hφAB] at hXs2; norm_num at hXs2
    · rw [h, dotProduct_neg, hφAB] at hXs2; norm_num at hXs2
  -- the neighbouring `K*`-admissible lattice
  obtain ⟨A', B', tA, tB, hev⟩ := m46e_turn hKs hab hAs hBs hptss
  have hφA' : ∀ᶠ t in 𝓝[>] (0 : ℝ), |a ⬝ᵥ A' t| < 3 / 2 :=
    (((irr_continuous_dot a).tendsto A).comp tA).abs.eventually
      (gt_mem_nhds (by rw [hφA]; norm_num))
  have hφB' : ∀ᶠ t in 𝓝[>] (0 : ℝ), |a ⬝ᵥ B' t| < 3 / 2 :=
    (((irr_continuous_dot a).tendsto B).comp tB).abs.eventually
      (gt_mem_nhds (by rw [hφB]; norm_num))
  refine ⟨A', B', tA, tB, ?_⟩
  filter_upwards [hev, m46e_near hK hab tA tB, hφA', hφB'] with t ⟨hcr, hlt, hadm⟩ hn hta htb
  refine ⟨hcr, hlt, fun X hX hXi ↦ ?_⟩
  -- an inner point of `K` in `Λ*`: inside `K*` it is `O`; otherwise it is `±(A* + B*)`
  by_cases hXs : X ∈ interior Ks
  · exact Or.inl (hadm X hX hXs)
  obtain ⟨m, n, rfl⟩ := mm_mem_span_pair.1 hX
  have hmn : (m : ℝ) • A + (n : ℝ) • B ∈ Λ := by
    rw [← hspan]; exact mm_mem_span_pair.2 ⟨m, n, rfl⟩
  rcases hpts _ hmn (hn m n (interior_subset hXi)) with h | h | h | h | h | h | h
  · obtain ⟨rfl, rfl⟩ := m46e_coeff hab 0 0 h (by simp)
    simp
  · obtain ⟨rfl, rfl⟩ := m46e_coeff hab 1 0 h (by simp)
    exact absurd (hint ⟨hXi, by simpa using hta⟩) hXs
  · obtain ⟨rfl, rfl⟩ := m46e_coeff hab (-1) 0 h (by simp)
    have e : ((-1 : ℤ) : ℝ) • A' t + ((0 : ℤ) : ℝ) • B' t = -A' t := by simp
    rw [e] at hXi hXs
    exact absurd (hint ⟨hXi, show |a ⬝ᵥ -A' t| < 3 / 2 by rwa [dotProduct_neg, abs_neg]⟩) hXs
  · obtain ⟨rfl, rfl⟩ := m46e_coeff hab 0 1 h (by simp)
    exact absurd (hint ⟨hXi, by simpa using htb⟩) hXs
  · obtain ⟨rfl, rfl⟩ := m46e_coeff hab 0 (-1) h (by simp)
    have e : ((0 : ℤ) : ℝ) • A' t + ((-1 : ℤ) : ℝ) • B' t = -B' t := by simp
    rw [e] at hXi hXs
    exact absurd (hint ⟨hXi, show |a ⬝ᵥ -B' t| < 3 / 2 by rwa [dotProduct_neg, abs_neg]⟩) hXs
  · obtain ⟨rfl, rfl⟩ := m46e_coeff hab 1 1 h (by simp)
    right; left; simp
  · obtain ⟨rfl, rfl⟩ := m46e_coeff hab (-1) (-1) h (by push_cast; module)
    right; right; push_cast; module

/-- **Definition B for the chosen point `A + B`, in any basis.** Let `Λ` have just the six points
`±A, ±B, ±(A + B)` on `C`, let `Y₁, Y₂` be any basis of `Λ`, and `A + B = u₁ Y₁ + u₂ Y₂`. For
`ε > 0` there is a lattice `Λ*` with a basis `Y₁*, Y₂*`, `|Y_g* - Y_g| < ε`, `d(Λ*) < d(Λ)`, and no
inner points of `K` except `O` and `±(u₁ Y₁* + u₂ Y₂*)`: the image of `Λ` under the linear map
`A ↦ A*`, `B ↦ B*` of `m46e_hex_deform`. -/
lemma m46e_free_at (hK : IsSymmetricConvexDomain K) {Λ : Submodule ℤ (Fin 2 → ℝ)}
    {A B : Fin 2 → ℝ} (h : m46e_IsHex K Λ A B) {Y₁ Y₂ : Fin 2 → ℝ} (hY : IsBasis Λ Y₁ Y₂)
    {u₁ u₂ : ℤ} (hP : (u₁ : ℝ) • Y₁ + (u₂ : ℝ) • Y₂ = A + B) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y₁' Y₂' : Fin 2 → ℝ, ‖Y₁' - Y₁‖ < ε ∧ ‖Y₂' - Y₂‖ < ε ∧ cross Y₁' Y₂' ≠ 0 ∧
      det (Submodule.span ℤ {Y₁', Y₂'}) < det Λ ∧
      ∀ X ∈ Submodule.span ℤ {Y₁', Y₂'}, X ∈ interior K →
        X = 0 ∨ X = (u₁ : ℝ) • Y₁' + (u₂ : ℝ) • Y₂' ∨
          X = -((u₁ : ℝ) • Y₁' + (u₂ : ℝ) • Y₂') := by
  have hspan := h.2.2.2.1
  have hab := mm_cross_ne_zero hK h.1 h.2.1 h.2.2.1
  obtain ⟨A', B', tA, tB, hev⟩ := m46e_hex_deform hK h
  -- the coordinates of `Y₁, Y₂` in the basis `A, B`
  have hY₁ : Y₁ ∈ Submodule.span ℤ {A, B} := by
    rw [hspan, ← hY.2]; exact Submodule.subset_span (by simp)
  have hY₂ : Y₂ ∈ Submodule.span ℤ {A, B} := by
    rw [hspan, ← hY.2]; exact Submodule.subset_span (by simp)
  obtain ⟨a₁, b₁, e₁⟩ := mm_mem_span_pair.1 hY₁
  obtain ⟨a₂, b₂, e₂⟩ := mm_mem_span_pair.1 hY₂
  have hdetΛ : det Λ = |cross A B| := by rw [← hspan]; exact mm_det_span hab
  -- the change of basis is unimodular
  have hk : |(a₁ : ℝ) * b₂ - b₁ * a₂| = 1 := by
    have h1 := mm_det_eq (hspan ▸ mm_isLattice_span hab) hY
    rw [hdetΛ, ← e₁, ← e₂, mm_cross_comb, abs_mul] at h1
    exact mul_right_cancel₀ (abs_pos.2 hab).ne' (h1.symm.trans (one_mul _).symm)
  -- the coordinates of `P = A + B` in the basis `Y₁, Y₂`
  have hc : u₁ * a₁ + u₂ * a₂ = 1 ∧ u₁ * b₁ + u₂ * b₂ = 1 := by
    refine m46e_coeff (m := u₁ * a₁ + u₂ * a₂) (n := u₁ * b₁ + u₂ * b₂) (X := A + B) hab 1 1
      ?_ (by simp)
    rw [← hP, ← e₁, ← e₂]; push_cast; module
  have t₁ : Tendsto (fun t ↦ (a₁ : ℝ) • A' t + (b₁ : ℝ) • B' t) (𝓝[>] 0) (𝓝 Y₁) := by
    rw [← e₁]; exact (tA.const_smul _).add (tB.const_smul _)
  have t₂ : Tendsto (fun t ↦ (a₂ : ℝ) • A' t + (b₂ : ℝ) • B' t) (𝓝[>] 0) (𝓝 Y₂) := by
    rw [← e₂]; exact (tA.const_smul _).add (tB.const_smul _)
  obtain ⟨t, ⟨hcr, hlt, hpts'⟩, h₁, h₂⟩ :=
    (hev.and ((Metric.tendsto_nhds.1 t₁ ε hε).and (Metric.tendsto_nhds.1 t₂ ε hε))).exists
  have hcross : cross ((a₁ : ℝ) • A' t + (b₁ : ℝ) • B' t) ((a₂ : ℝ) • A' t + (b₂ : ℝ) • B' t) =
      ((a₁ : ℝ) * b₂ - b₁ * a₂) * cross (A' t) (B' t) := mm_cross_comb _ _ _ _ _ _
  have hcr' :
      cross ((a₁ : ℝ) • A' t + (b₁ : ℝ) • B' t) ((a₂ : ℝ) • A' t + (b₂ : ℝ) • B' t) ≠ 0 := by
    rw [hcross]
    refine mul_ne_zero (fun h0 ↦ ?_) hcr
    rw [h0, abs_zero] at hk; norm_num at hk
  refine ⟨_, _, by rwa [← dist_eq_norm], by rwa [← dist_eq_norm], hcr', ?_, fun X hX hXi ↦ ?_⟩
  · rw [mm_det_span hcr', hcross, abs_mul, hk, one_mul, hdetΛ]; exact hlt
  · have hsub : Submodule.span ℤ {(a₁ : ℝ) • A' t + (b₁ : ℝ) • B' t,
        (a₂ : ℝ) • A' t + (b₂ : ℝ) • B' t} ≤ Submodule.span ℤ {A' t, B' t} := by
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨mm_mem_span_pair.2 ⟨a₁, b₁, rfl⟩, mm_mem_span_pair.2 ⟨a₂, b₂, rfl⟩⟩
    have hPt : (u₁ : ℝ) • ((a₁ : ℝ) • A' t + (b₁ : ℝ) • B' t) +
        (u₂ : ℝ) • ((a₂ : ℝ) • A' t + (b₂ : ℝ) • B' t) = A' t + B' t := by
      have e : (u₁ : ℝ) • ((a₁ : ℝ) • A' t + (b₁ : ℝ) • B' t) +
          (u₂ : ℝ) • ((a₂ : ℝ) • A' t + (b₂ : ℝ) • B' t) =
          ((u₁ * a₁ + u₂ * a₂ : ℤ) : ℝ) • A' t + ((u₁ * b₁ + u₂ * b₂ : ℤ) : ℝ) • B' t := by
        push_cast; module
      rw [e, hc.1, hc.2]; simp
    rw [hPt]
    exact hpts' X (hsub hX) hXi

/-- The six points `±A, ±B, ±(A + B)` are distinct. -/
lemma m46e_ncard_six {A B : Fin 2 → ℝ} (hab : cross A B ≠ 0) :
    ({A, -A, B, -B, A + B, -(A + B)} : Set (Fin 2 → ℝ)).ncard = 6 := by
  have hne : ∀ x y : Fin 2 → ℝ, ∀ m n : ℤ, (m ≠ 0 ∨ n ≠ 0) →
      x - y = (m : ℝ) • A + (n : ℝ) • B → x ≠ y := by
    intro x y m n hmn hxy h
    exact mm_comb_ne_zero hab hmn (by rw [← hxy, h, sub_self])
  have h1 : A ∉ ({-A, B, -B, A + B, -(A + B)} : Set (Fin 2 → ℝ)) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hne _ _ 2 0 (by norm_num) (by push_cast; module),
      hne _ _ 1 (-1) (by norm_num) (by push_cast; module),
      hne _ _ 1 1 (by norm_num) (by push_cast; module),
      hne _ _ 0 (-1) (by norm_num) (by push_cast; module),
      hne _ _ 2 1 (by norm_num) (by push_cast; module)⟩
  have h2 : -A ∉ ({B, -B, A + B, -(A + B)} : Set (Fin 2 → ℝ)) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hne _ _ (-1) (-1) (by norm_num) (by push_cast; module),
      hne _ _ (-1) 1 (by norm_num) (by push_cast; module),
      hne _ _ (-2) (-1) (by norm_num) (by push_cast; module),
      hne _ _ 0 1 (by norm_num) (by push_cast; module)⟩
  have h3 : B ∉ ({-B, A + B, -(A + B)} : Set (Fin 2 → ℝ)) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hne _ _ 0 2 (by norm_num) (by push_cast; module),
      hne _ _ (-1) 0 (by norm_num) (by push_cast; module),
      hne _ _ 1 2 (by norm_num) (by push_cast; module)⟩
  have h4 : -B ∉ ({A + B, -(A + B)} : Set (Fin 2 → ℝ)) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hne _ _ (-1) (-2) (by norm_num) (by push_cast; module),
      hne _ _ 1 0 (by norm_num) (by push_cast; module)⟩
  have h5 : A + B ∉ ({-(A + B)} : Set (Fin 2 → ℝ)) := by
    simp only [mem_singleton_iff]
    exact hne _ _ 2 2 (by norm_num) (by push_cast; module)
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_insert_of_notMem h3,
    Set.ncard_insert_of_notMem h4, Set.ncard_insert_of_notMem h5, Set.ncard_singleton]

/-- **"Just six points on `C`"** for a critical lattice with basis `A, B` and `A, B, A + B` on `C`:
`Λ ∩ C` has six elements exactly when the points of `Λ` in `K` are `O, ±A, ±B, ±(A + B)`. -/
lemma m46e_ncard_six_iff (hK : IsSymmetricConvexDomain K) {Λ : Submodule ℤ (Fin 2 → ℝ)}
    (hΛ : IsCritical K Λ) {A B : Fin 2 → ℝ} (hA : A ∈ frontier K) (hB : B ∈ frontier K)
    (hAB : A + B ∈ frontier K) (hspan : Submodule.span ℤ {A, B} = Λ) :
    ((Λ : Set (Fin 2 → ℝ)) ∩ frontier K).ncard = 6 ↔ m46e_IsHex K Λ A B := by
  have hab := mm_cross_ne_zero hK hA hB hAB
  have mem : ∀ m n : ℤ, (m : ℝ) • A + (n : ℝ) • B ∈ (Λ : Set (Fin 2 → ℝ)) := fun m n ↦ by
    rw [SetLike.mem_coe, ← hspan]; exact mm_mem_span_pair.2 ⟨m, n, rfl⟩
  have hsub : ({A, -A, B, -B, A + B, -(A + B)} : Set (Fin 2 → ℝ)) ⊆
      (Λ : Set (Fin 2 → ℝ)) ∩ frontier K := by
    intro X hX
    simp only [mem_insert_iff, mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by simpa using mem 1 0, hA⟩
    · exact ⟨by simpa using mem (-1) 0, mm_neg_mem_frontier hK hA⟩
    · exact ⟨by simpa using mem 0 1, hB⟩
    · exact ⟨by simpa using mem 0 (-1), mm_neg_mem_frontier hK hB⟩
    · exact ⟨by simpa using mem 1 1, hAB⟩
    · refine ⟨?_, mm_neg_mem_frontier hK hAB⟩
      convert mem (-1) (-1) using 1; push_cast; module
  have hfr : ∀ X ∈ Λ, X ∈ K → X ≠ 0 → X ∈ frontier K := fun X hX hXK hX0 ↦
    mm_mem_frontier hK hXK fun hi ↦ hX0 (hΛ.2.1 X hX hi)
  constructor
  · intro hsix
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hsix, m46e_ncard_six hab])
      (Set.finite_of_ncard_ne_zero (by rw [hsix]; norm_num))
    refine ⟨hA, hB, hAB, hspan, fun X hX hXK ↦ ?_⟩
    by_cases hX0 : X = 0
    · exact Or.inl hX0
    have hX6 : X ∈ ({A, -A, B, -B, A + B, -(A + B)} : Set (Fin 2 → ℝ)) := by
      rw [heq]; exact ⟨hX, hfr X hX hXK hX0⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hX6
    tauto
  · intro hhex
    have heq : (Λ : Set (Fin 2 → ℝ)) ∩ frontier K = {A, -A, B, -B, A + B, -(A + B)} := by
      refine Subset.antisymm (fun X ⟨hX, hXF⟩ ↦ ?_) hsub
      have h7 := hhex.2.2.2.2 X hX (mm_mem_of_frontier hK hXF)
      have hX0 := mm_ne_zero_of_frontier hK hXF
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    rw [heq, m46e_ncard_six hab]

/-- **Mahler (1946), Theorem E**, for symmetric convex domains: *Let `K` be a convex star domain in
`R₂`, and `Λ` a critical lattice of `K` with just six points on `C`. Then `Λ` is a free lattice.*

Mahler's proof. By (A) (`minkowski_mahler`) the six points are `±P₀, ±P₂, ±(P₀ + P₂)` for a basis
`P₀, P₂` of `Λ`; no three of them are collinear, so a line `L` separates any chosen one of them from
the five others; with `K*` the set of points of `K` not separated from `O` by `L` or `-L`, a convex
star domain with only four points of `Λ` on its boundary, there is a neighbouring `K*`-admissible
lattice `Λ*` with `d(Λ*) < d(Λ)`, and it satisfies the conditions of Definition B. Here the chosen
point is written `A + B` for a relabelling `(A, B)` of the hexagon, and the construction is
`m46e_hex_deform` (see the module docstring for the gap filled there). -/
theorem theoremE (hK : IsSymmetricConvexDomain K) {Λ : Submodule ℤ (Fin 2 → ℝ)}
    (hΛ : IsCritical K Λ) (hsix : ((Λ : Set (Fin 2 → ℝ)) ∩ frontier K).ncard = 6) :
    IsFree K Λ := by
  obtain ⟨P₀, P₁, P₂, -, -, -, h0F, h1F, h2F, hB, h012, -, -⟩ := (minkowski_mahler hK).1 Λ hΛ
  subst h012
  have hc := mm_cross_ne_zero hK h0F h2F h1F
  have hspan : Submodule.span ℤ {P₀, P₂} = Λ := by
    rw [← hB.2]
    refine (mm_span_eq hc (mm_mem_span_pair.2 ⟨1, 0, by simp⟩)
      (mm_mem_span_pair.2 ⟨1, 1, by simp⟩) ?_).symm
    congr 1; simp only [cross, Pi.add_apply]; ring
  have hhex : m46e_IsHex K Λ P₀ P₂ := (m46e_ncard_six_iff hK hΛ h0F h2F h1F hspan).1 hsix
  refine ⟨hΛ, P₀, P₀ + P₂, hB, fun u₁ u₂ hP ε hε ↦ ?_⟩
  have hPΛ : (u₁ : ℝ) • P₀ + (u₂ : ℝ) • (P₀ + P₂) ∈ Λ := by
    rw [← hB.2]; exact mm_mem_span_pair.2 ⟨u₁, u₂, rfl⟩
  rcases hhex.2.2.2.2 _ hPΛ (mm_mem_of_frontier hK hP) with h | h | h | h | h | h | h
  · exact absurd h (mm_ne_zero_of_frontier hK hP)
  · exact m46e_free_at hK (m46e_hex_rot' hK hhex) hB (by rw [h]; abel) hε
  · exact m46e_free_at hK (m46e_hex_neg hK (m46e_hex_rot' hK hhex)) hB (by rw [h]; abel) hε
  · exact m46e_free_at hK (m46e_hex_rot hK hhex) hB (by rw [h]; abel) hε
  · exact m46e_free_at hK (m46e_hex_neg hK (m46e_hex_rot hK hhex)) hB (by rw [h]; abel) hε
  · exact m46e_free_at hK hhex hB h hε
  · exact m46e_free_at hK (m46e_hex_neg hK hhex) hB (by rw [h]; abel) hε

/-! ### Lemma 12 of paper A -/

/-- **Corollary to Lemma 5 of paper A, as "just six points"**: if `K` is not a parallelogram,
every critical lattice of `K` has just six points on `C` (`ml5_lemma5_cor_six`, for the
positively oriented configuration of basis points given by Lemma 3). -/
lemma m46e_cor_ncard (hK : IsSymmetricConvexDomain K) (hpar : ¬IsParallelogram K)
    {Λ : Submodule ℤ (Fin 2 → ℝ)} (hΛ : IsCritical K Λ) :
    ((Λ : Set (Fin 2 → ℝ)) ∩ frontier K).ncard = 6 := by
  obtain ⟨P₀, P₁, P₂, -, -, -, h0F, h1F, h2F, hB, h012, -, hdet⟩ := (minkowski_mahler hK).1 Λ hΛ
  subst h012
  have hc := mm_cross_ne_zero hK h0F h2F h1F
  have hspan : Submodule.span ℤ {P₀, P₂} = Λ := by
    rw [← hB.2]
    refine (mm_span_eq hc (mm_mem_span_pair.2 ⟨1, 0, by simp⟩)
      (mm_mem_span_pair.2 ⟨1, 1, by simp⟩) ?_).symm
    congr 1; simp only [cross, Pi.add_apply]; ring
  refine (m46e_ncard_six_iff hK hΛ h0F h2F h1F hspan).2 ⟨h0F, h2F, h1F, hspan, fun X hX hXK ↦ ?_⟩
  by_cases hX0 : X = 0
  · exact Or.inl hX0
  have hXF : X ∈ frontier K := mm_mem_frontier hK hXK fun hi ↦ hX0 (hΛ.2.1 X hX hi)
  rcases (abs_eq (irr_minimalDeterminant_pos hK).le).1 hdet with e | e
  · have hR : ml5_IsConf K P₀ (P₀ + P₂) :=
      ⟨h0F, h1F, by rw [add_sub_cancel_left]; exact h2F, e⟩
    have := ml5_lemma5_cor_six hK hpar hR hXF (by rw [hB.2]; exact hX)
    rw [add_sub_cancel_left] at this
    tauto
  · have hR : ml5_IsConf K (P₀ + P₂) P₀ :=
      ⟨h1F, h0F, by rw [sub_add_cancel_left]; exact mm_neg_mem_frontier hK h2F,
        by rw [mm_cross_swap, e, neg_neg]⟩
    have := ml5_lemma5_cor_six hK hpar hR hXF (by rw [Set.pair_comm, hB.2]; exact hX)
    rw [sub_add_cancel_left, neg_neg] at this
    tauto

/-- **Mahler, paper A, Lemma 12** (for convex subdomains; the "if" half of Mahler 1947, Lemma 3):
*If `K` is a convex domain, and if every point of `C` belongs to `Π`, then `K` is irreducible*
(`Π`: the points of `C` on critical lattices). Paper A quotes it from Theorems D and E of the 1946
paper. A parallelogram is irreducible by Lemma 1 of paper A (`ml5_lemma1`). Otherwise every
critical lattice has just six points on `C` (Corollary to Lemma 5, `m46e_cor_ncard`), hence is free
(Theorem E), and every point of `C` lies on one; so `K` is irreducible by Theorem D with `Σ = C`.
Gap in paper A (filled): Theorems D and E alone do not give the lemma from `Π = C`; the Corollary
to Lemma 5 and Lemma 1, both proved in paper A before Lemma 12, supply the dense set of points on
six-point critical lattices. -/
theorem m46e_lemma12 (hK : IsSymmetricConvexDomain K)
    (hall : ∀ u ∈ frontier K, ∃ Λ, IsCritical K Λ ∧ u ∈ Λ) :
    MahlerIrreducible.IsIrreducible K := by
  by_cases hpar : IsParallelogram K
  · exact ml5_lemma1 hpar
  refine theoremD hK subset_rfl subset_closure fun P hP ↦ ?_
  obtain ⟨Λ, hΛ, hPΛ⟩ := hall P hP
  exact ⟨Λ, theoremE hK hΛ (m46e_cor_ncard hK hpar hΛ), hPΛ⟩

end Mahler1946

end External
