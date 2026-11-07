module

public import External.Mahler1947
public import Basic.Algebra.Module.ZLattice.PlaneCritical
public import Basic.Analysis.Convex.BoundaryArc
public import Mathlib.Analysis.Convex.Extreme

/-!
# Irreducible convex domains (Mahler)

Cited in the remark after Definition 2.3.5 of Hales–Vajjha, *Packings of Smoothed Polygons*, from
K. Mahler, *On the minimum determinant and the circumscribed hexagons of a convex domain*,
Proc. Kon. Ned. Akad. Wet. 50 (1947), 692–703, Lemma 3 (stated there without proof; its footnote 3
reads "See Lemmas 8 and 12 of paper A", paper A being Mahler, *On irreducible convex domains*,
Proc. Kon. Ned. Akad. Wet. 50 (1947), 98–107): *the convex domain `K` is irreducible if and only if
every boundary point of `K` belongs to a critical lattice of `K`.*

Definitions, in the terms of the source; symmetric convex domains, lattices, `Δ(K)` and critical
lattices are those of `External.MinkowskiMahler`, tac-lines those of `External.Mahler1947`. A
symmetric convex domain `K` is irreducible (`IsIrreducible`) if every symmetric convex domain
`K' ⊆ K` other than `K` has a smaller minimal determinant, `Δ(K') < Δ(K)`.

## What is proved

`mahler_irreducible_iff`: Lemma 3 in full. On the way, the lemmas of paper A that its proof uses:
Lemma 1 (`MahlerIrreducible.ml5_lemma1`, parallelograms are irreducible; `Δ` of a parallelogram,
`ml5_par_minDet`), Lemma 2 (`ml3_width_eq`), Lemma 5 and its Corollary (`ml5_lemma5`,
`ml5_lemma5_partner`, `ml5_lemma5_unique`, `ml5_lemma5_cor_six`, `ml5_lemma5_cor_arcs`), Lemma 6
(`ml5_lemma6`), Lemma 7 (`ml5_lemma7`), Lemma 11 for convex domains (`ml3_isClosed`) and the
class-A case of Lemma 13 (`ml5_classA`); further `mahler_irreducible` (if `K` is irreducible,
every tac-line `ℓ` of `K` passes through a point of a critical lattice `Λ` of `K`, one of the six
points `±P₀, ±P₁, ±P₂` of a configuration of Mahler's Lemma 2 (Minkowski: `P₀, P₁` a basis of `Λ`,
`P₁ = P₀ + P₂`, the three points on the boundary of `K`)), `mahler_irreducible_exposed` (exposed
points), `ml3_extreme` (extreme points), `ml3_onlyIf` (all boundary points) and
`ml3_irreducible_of_forall` (the converse). The facts about the boundary curve that Mahler uses
"by the convexity of `C`" (arcs, the radial parametrization and the intermediate value theorem on
arcs, chords, arcs without extreme points) are in `Basic.Analysis.Convex.BoundaryArc`.

## Sources, and departures from them

Mahler 1947 states Lemma 3 without proof. Paper A was not among the sources supplied with the
book; for this proof we read a scan of it (Mahler's collected works, CARMA archive, item 094).
In paper A a domain is *irreducible* if every *star domain* `H ⊊ K` has `Δ(H) < Δ(K)`;
`IsIrreducible` asks this only of symmetric convex subdomains (paper A's Lemma 13 shows that for a
convex `K` the two notions agree, so Lemma 3 holds for either). Paper A quotes its Lemma 8
(irreducible star domain: every boundary point on a critical lattice), Lemmas 10, 11 and Lemma 12
(convex `K` with every boundary point on a critical lattice is irreducible) from Mahler, *Lattice
points in n-dimensional star bodies II. Reducibility theorems I*, Proc. Kon. Ned. Akad. Wet. 49
(1946), 331–343, Theorems B–E; it proves Lemmas 1, 2, 5–7 and 13 itself. Our proofs:

* **Following paper A.** The "only if" half follows the proof of Lemma 13, which splits the
  boundary points off critical lattices into class B (extreme points) and class A (inner points
  of boundary segments), with paper A's own lemmas proved by Mahler's arguments:
  - Lemma 1 (`ml5_lemma1`), in the coordinates of the parallelogram instead of after an affine
    map to the square. `Δ(K₀) = 1`, which Mahler takes from Minkowski's theorem on linear forms
    (not available), is obtained from Mahler's own example in §2 (`A(P₁) = 1` for every boundary
    point of the square) with Lemmas 2 and 3 (`ml5_par_minDet`). Gaps in paper A, filled: the
    reduction to `P₀ = (ξ, 1)`, `0 < ξ < 1`, is left to the reader; and `±θP₀` are not the only
    points of `Λ₀` inside the square when `θ < 1/2` (all of them are multiples of `θP₀`, which
    are not inner points of `H`; `ml5_lemma1_core`).
  - Lemma 2 (`ml3_width_eq`): Mahler's strip argument (this replaces an earlier proof by support
    functionals).
  - Lemma 5 (`ml5_lemma5`, `ml5_lemma5_partner`, `ml5_lemma5_unique`), Mahler's proof; slip in
    paper A: "an inner point of `P₂P₃` lies on `L**`" should read "lies on `C`". Its Corollary
    (`ml5_lemma5_cor_six`, `ml5_lemma5_cor_arcs`) has no proof in paper A; we supply one
    (`ml3_eight` and the uniqueness of the configuration at a point).
  - Lemma 6 (`ml5_lemma6`), Mahler's proof: the triangle `P₁, P₁ + P₂, P₂` (`ml5_triangle`), the
    line `{P₁*, X} = Δ` meeting the arcs `A₂, A₃` (intermediate value theorem on arcs), Lemma 5.
    Stated for one step (a point inside `A₁` has its next points inside `A₂, A₃`), from which
    Mahler's "just one point on each arc" follows by rotating the configuration.
  - Lemma 7 (`ml5_lemma7_step`, `ml5_lemma7`), Mahler's argument via Lemma 6.
  - Class A (`ml5_classA`, used in `ml3_onlyIf`), as written: the largest segment `Γ₁` around the
    point with ends on critical lattices and inner points off them; `P'₁` inside `A₁` (Mahler's
    "without loss of generality" is our naming of the ends by orientation); `P'₂, P'₃` inside
    `A₂, A₃` (Lemma 6); the inner points of `Γ₂, Γ₃` off critical lattices (Lemma 7, used with
    the indices shifted cyclically and the roles of the lattices exchanged, `ml5_lemma7_back`),
    hence not extreme, hence `Γ₂, Γ₃` are segments; `{Q₁, Q₃} > 0` from the positions of
    `P'₁, P'₃` in the triangles; Mahler's quadratic (`ml3_quadratic`). Gaps in paper A, filled:
    the sign of `{P₁*, P₃*}` (Lemma 3 bounds its absolute value; the sign follows by continuity),
    and the step "the inner points of `Γ_l` are of class A, so `Γ_l` is a segment"
    (`BoundaryArc.midpoint_mem_frontier_of_forall_not_mem_extremePoints`). Mahler excludes
    parallelograms by Lemma 1 (a reducible domain is not a parallelogram); since we argue by
    contradiction from an irreducible `K` with a boundary point off `Π`, we exclude them by
    Mahler's example in §3 instead (for a parallelogram `Π = C`, `ml5_par_pi`).
* **Departures that remain** (the 1946 paper's proofs were not at hand when these were written;
  the paper has since been located in the same archive, item 088, and following it is left for a
  later round):
  - Class B (`ml3_extreme`). Mahler uses Lemma 10 (from the proof of Theorem C of the 1946 paper,
    for star domains) and a cut by a line. We use the shaving argument of `mahler_irreducible` on
    support lines tilted towards the extreme point, and the closedness of the set `Π` of boundary
    points on critical lattices (Lemma 11, a special case of Theorem B of the 1946 paper;
    `ml3_isClosed`, by compactness of the critical lattices).
  - "If" (Lemma 12 = Theorems D and E of the 1946 paper, for convex subdomains;
    `ml3_irreducible_of_forall`). Our argument: if `K' ⊊ K` had `Δ(K') = Δ(K)`, a critical
    lattice `Λ` of `K` through a boundary point `p ∉ K'` would be `K'`-critical, so (Lemma 2 for
    `K'`) it has points `Q₀, Q₂, Q₀ + Q₂` on the boundary of `K'`, hence of `K`. Admissibility
    then forces `p = ±(2Q₀ + Q₂), ±(Q₀ + 2Q₂), ±(Q₀ - Q₂)` (`ml3_eight`), i.e. `p = A + B` with
    `A, B, A ± B` on the boundary; then `K` lies in the parallelogram `|f| ≤ 1, |g| ≤ 1` (`f, g`
    support functionals at `A, B`) of vertex `p`, and `p` is an extreme point of `K`
    (`ml3_square_extreme`). The nearby boundary points `A + (1 - ε)B`, also outside `K'`, are not
    extreme.

## Proof of `mahler_irreducible`

Let `ℓ = {x | a · x = M}` with `a · x ≤ M` on `K`; then `M > 0` and `|a · x| ≤ M` on `K`, with
`|a · x| < M` on the interior. Shave `K` symmetrically along `±ℓ`: the domains
`K_n = K ∩ {|a · x| ≤ c_n}`, `c_n ↑ M`, are symmetric convex domains properly contained in `K`
(`irr_cut`), so `Δ(K_n) < Δ(K)` by irreducibility. Let `Λ_n` be a critical lattice of `K_n`
(`irr_exists_critical`, Mahler's compactness theorem) with points `P₀ⁿ, P₁ⁿ = P₀ⁿ + P₂ⁿ, P₂ⁿ` on
the boundary of `K_n` (Lemma 2, `External.minkowski_mahler`). Not all three lie on the boundary of
`K`: otherwise `Λ_n` would be `K`-admissible (Lemma 1), with `d(Λ_n) = Δ(K_n) < Δ(K)`. A point of
the boundary of `K_n` inside `K` lies on the cut, so one of the three has `|a · Pⁿ| ≥ c_n`. All
these points lie in `K`, so a subsequence of `(P₀ⁿ, P₂ⁿ)` converges to some `(P₀, P₂)`. The lattice
`Λ` with basis `P₀, P₁ = P₀ + P₂` is `K`-admissible: a nonzero point `m P₀ + k P₁` inside `K` would
be the limit of the points `m P₀ⁿ + k P₁ⁿ` of `Λ_n`, which for large `n` lie inside `K` with
`|a · x| < c_n`, hence inside `K_n`. So `P₀, P₁, P₂` are boundary points of `K` (they are not `0`:
the points `Pⁿ` stay outside a fixed neighbourhood of `0`), `det(P₀, P₂) ≠ 0`, and
`d(Λ) = |det(P₀, P₁)| = lim Δ(K_n) ≤ Δ(K)`: `Λ` is critical. Finally `|a · P| ≥ M` for one of the
`P = P₀, P₁, P₂`, so `P` or `-P` lies on `ℓ`.
-/

@[expose] public section

namespace External

namespace MahlerIrreducible

open Set Filter Topology MinkowskiMahler

/-- An irreducible convex domain (Mahler): a symmetric convex domain `K` such that every symmetric
convex domain `K' ⊆ K` with `K' ≠ K` has a smaller minimal determinant, `Δ(K') < Δ(K)`. -/
def IsIrreducible (K : Set (Fin 2 → ℝ)) : Prop :=
  IsSymmetricConvexDomain K ∧ ∀ K', IsSymmetricConvexDomain K' → K' ⊆ K → K' ≠ K →
    minimalDeterminant K' < minimalDeterminant K

/-! ## Proof -/

section Proof

variable {K : Set (Fin 2 → ℝ)}

lemma irr_continuous_dot (a : Fin 2 → ℝ) : Continuous fun x : Fin 2 → ℝ ↦ a ⬝ᵥ x := by
  simp only [dotProduct, Fin.sum_univ_two]
  fun_prop

lemma irr_continuous_abs_dot (a : Fin 2 → ℝ) : Continuous fun x : Fin 2 → ℝ ↦ |a ⬝ᵥ x| :=
  (irr_continuous_dot a).abs

lemma irr_dot_self_pos {a : Fin 2 → ℝ} (ha : a ≠ 0) : 0 < a ⬝ᵥ a := by
  simp only [dotProduct, Fin.sum_univ_two]
  by_contra hneg
  apply ha
  ext i; fin_cases i <;> simp <;> nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]

/-- A linear functional `a · x` bounded by `M` on `K` is `< M` on the interior of `K`. -/
lemma irr_dot_lt {a : Fin 2 → ℝ} (ha : a ≠ 0) {M : ℝ} (haK : ∀ x ∈ K, a ⬝ᵥ x ≤ M)
    {x : Fin 2 → ℝ} (hx : x ∈ interior K) : a ⬝ᵥ x < M := by
  have hc : Continuous fun t : ℝ ↦ x + t • a := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • a ∈ K :=
    hc.continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 hx)
  obtain ⟨t, htK, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have h1 := haK _ htK
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h1
  have h2 := irr_dot_self_pos ha
  have h3 : (0 : ℝ) < t := ht
  nlinarith

/-- **Existence of critical lattices** (Mahler's compactness theorem in the plane,
`PlaneLattice.exists_admissible_covolume_le`, for the open set `interior K`; the lattice `R ℤ²`
is admissible when `K` lies in the square `|x₀|, |x₁| < R`). -/
lemma irr_exists_critical (hK : IsSymmetricConvexDomain K) : ∃ Λ, IsCritical K Λ := by
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
  have hadm₀ : ∀ x ∈ Submodule.span ℤ {(![R, 0] : Fin 2 → ℝ), ![0, R]}, x ∈ interior K →
      x = 0 := by
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
  obtain ⟨L, hLd, hLs, hLadm, hLmin⟩ := PlaneLattice.exists_admissible_covolume_le
    isOpen_interior (mm_zero_mem_interior hK) hd₀ hs₀ hadm₀
  refine ⟨L, ⟨hLd, hLs⟩, hLadm, ?_⟩
  unfold minimalDeterminant
  refine Eq.symm (IsLeast.csInf_eq ⟨⟨L, ⟨hLd, hLs⟩, hLadm, rfl⟩, ?_⟩)
  rintro d ⟨L', ⟨hL'd, hL's⟩, hL'adm, rfl⟩
  exact hLmin L' hL'd hL's hL'adm

/-- The minimal determinant of a symmetric convex domain is positive. -/
lemma irr_minimalDeterminant_pos (hK : IsSymmetricConvexDomain K) : 0 < minimalDeterminant K := by
  obtain ⟨Λ, ⟨hd, hs⟩, -, hdet⟩ := irr_exists_critical hK
  have : IsZLattice ℝ Λ := ⟨hs⟩
  rw [← hdet]
  exact ZLattice.covolume_pos Λ

/-- **Shaving.** Cutting a symmetric convex domain by the strip `|a · x| ≤ c`, `c > 0`, gives a
symmetric convex domain. -/
lemma irr_cut (hK : IsSymmetricConvexDomain K) (a : Fin 2 → ℝ) {c : ℝ} (hc : 0 < c) :
    IsSymmetricConvexDomain (K ∩ {x | |a ⬝ᵥ x| ≤ c}) := by
  have hcont := irr_continuous_abs_dot a
  refine ⟨hK.1.inter ?_, hK.2.1.inter_right (isClosed_le hcont continuous_const), ⟨0, ?_⟩, ?_⟩
  · intro x hx y hy s t hs ht hst
    simp only [mem_ofPred_eq] at hx hy ⊢
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    calc |s * (a ⬝ᵥ x) + t * (a ⬝ᵥ y)| ≤ |s * (a ⬝ᵥ x)| + |t * (a ⬝ᵥ y)| := abs_add_le _ _
      _ = s * |a ⬝ᵥ x| + t * |a ⬝ᵥ y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * c + t * c := by gcongr
      _ = c := by rw [← add_mul, hst, one_mul]
  · rw [interior_inter]
    refine ⟨mm_zero_mem_interior hK, interior_maximal (t := {x | |a ⬝ᵥ x| < c})
      (fun x (hx : |a ⬝ᵥ x| < c) ↦ show |a ⬝ᵥ x| ≤ c from hx.le)
      (isOpen_lt hcont continuous_const) ?_⟩
    simpa using hc
  · rintro x ⟨hx, hxc⟩
    refine ⟨hK.2.2.2 x hx, ?_⟩
    change |a ⬝ᵥ -x| ≤ c
    rw [dotProduct_neg, abs_neg]
    exact hxc

end Proof

end MahlerIrreducible

open Set Filter Topology MahlerIrreducible Mahler1947 MinkowskiMahler

/-- **Mahler (1947), Lemma 3, weak form of the "only if" half** (a critical-lattice point on each
support line). Let `K` be an irreducible symmetric convex domain and `ℓ` a tac-line of `K`. Then a
critical lattice `Λ` of `K` has a point on `ℓ`: there are points `P₀, P₁, P₂` of `Λ` on the
boundary of `K` with `P₁ = P₀ + P₂` such that `P₀, P₁` is a basis of `Λ` (Mahler's Lemma 2), and
one of the six points `±P₀, ±P₁, ±P₂` lies on `ℓ`.

This is the basic step of our proof of the "only if" half of Lemma 3 (`mahler_irreducible_iff`),
proved by shaving `K` along `±ℓ` (see the module docstring); Mahler states Lemma 3 without proof,
referring to Lemmas 8 and 12 of his paper A. For a boundary point that is the only point of `K` on
a tac-line it is the corresponding case of Lemma 3 (`mahler_irreducible_exposed`). -/
theorem mahler_irreducible {K : Set (Fin 2 → ℝ)} (hK : MahlerIrreducible.IsIrreducible K)
    {ℓ : Set (Fin 2 → ℝ)} (hℓ : IsTacLine K ℓ) :
    ∃ (Λ : Submodule ℤ (Fin 2 → ℝ)) (P₀ P₁ P₂ : Fin 2 → ℝ), MinkowskiMahler.IsCritical K Λ ∧
      P₀ ∈ Λ ∧ P₁ ∈ Λ ∧ P₂ ∈ Λ ∧ P₀ ∈ frontier K ∧ P₁ ∈ frontier K ∧ P₂ ∈ frontier K ∧
      MinkowskiMahler.IsBasis Λ P₀ P₁ ∧ P₁ = P₀ + P₂ ∧
      (P₀ ∈ ℓ ∨ -P₀ ∈ ℓ ∨ P₁ ∈ ℓ ∨ -P₁ ∈ ℓ ∨ P₂ ∈ ℓ ∨ -P₂ ∈ ℓ) := by
  obtain ⟨hKd, hirr⟩ := hK
  obtain ⟨⟨a, ha, M, rfl, haK⟩, ⟨u, hu, huK⟩⟩ := hℓ
  simp only [mem_ofPred_eq] at hu
  -- `|a · x| ≤ M` on `K` and `|a · x| < M` on its interior
  have habs : ∀ x ∈ K, |a ⬝ᵥ x| ≤ M := by
    intro x hx
    have := haK (-x) (hKd.2.2.2 x hx)
    rw [dotProduct_neg] at this
    exact abs_le.2 ⟨by linarith, haK x hx⟩
  have hlt : ∀ x ∈ interior K, |a ⬝ᵥ x| < M := by
    intro x hx
    have h1 := irr_dot_lt ha haK hx
    have h2 := irr_dot_lt ha haK (mm_neg_mem_interior hKd hx)
    rw [dotProduct_neg] at h2
    exact abs_lt.2 ⟨by linarith, h1⟩
  have hM : 0 < M := by simpa using hlt 0 (mm_zero_mem_interior hKd)
  -- the cuts `c_n ↑ M`
  set c : ℕ → ℝ := fun n ↦ M - M / 2 * (1 / ((n : ℝ) + 1)) with hcdef
  have hinv : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) ≤ 1 := fun n ↦
    ⟨by positivity,
      (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])⟩
  have hc0 : ∀ n, M / 2 ≤ c n := fun n ↦ by
    have := hinv n
    simp only [hcdef]; nlinarith
  have hcM : ∀ n, c n < M := fun n ↦ by
    have := hinv n
    simp only [hcdef]; nlinarith
  have hcpos : ∀ n, 0 < c n := fun n ↦ lt_of_lt_of_le (half_pos hM) (hc0 n)
  have hctend : Tendsto c atTop (𝓝 M) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (M / 2)
    have h2 := h.const_sub M
    rw [mul_zero, sub_zero] at h2
    exact h2
  -- the shaved domains `K_n`
  set Kn : ℕ → Set (Fin 2 → ℝ) := fun n ↦ K ∩ {x | |a ⬝ᵥ x| ≤ c n} with hKndef
  have hKn : ∀ n, IsSymmetricConvexDomain (Kn n) := fun n ↦ irr_cut hKd a (hcpos n)
  have hKnK : ∀ n, Kn n ⊆ K := fun n ↦ inter_subset_left
  have hKnne : ∀ n, Kn n ≠ K := by
    intro n h
    have h2 : u ∈ Kn n := h ▸ huK
    have h3 : |a ⬝ᵥ u| ≤ c n := h2.2
    rw [hu, abs_of_pos hM] at h3
    linarith [hcM n]
  have hΔ : ∀ n, minimalDeterminant (Kn n) < minimalDeterminant K :=
    fun n ↦ hirr _ (hKn n) (hKnK n) (hKnne n)
  have hint : ∀ n x, x ∈ interior K → |a ⬝ᵥ x| < c n → x ∈ interior (Kn n) := by
    intro n x hx hxc
    rw [interior_inter]
    exact ⟨hx, interior_maximal (t := {x | |a ⬝ᵥ x| < c n})
      (fun y (hy : |a ⬝ᵥ y| < c n) ↦ show |a ⬝ᵥ y| ≤ c n from hy.le)
      (isOpen_lt (irr_continuous_abs_dot a) continuous_const) hxc⟩
  -- critical lattices of the `K_n` and their configurations of Lemma 2
  choose Λ hΛ using fun n ↦ irr_exists_critical (hKn n)
  have hconf := fun n ↦ (minkowski_mahler (hKn n)).1 (Λ n) (hΛ n)
  choose P₀ P₁ P₂ h0Λ h1Λ h2Λ h0F h1F h2F hB h012 hdetΛ hdetΔ using hconf
  -- one of the three points lies in the cut-off part
  have hcap : ∀ n, c n ≤ |a ⬝ᵥ P₀ n| ∨ c n ≤ |a ⬝ᵥ P₁ n| ∨ c n ≤ |a ⬝ᵥ P₂ n| := by
    intro n
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have hfr : ∀ x, x ∈ frontier (Kn n) → |a ⬝ᵥ x| < c n → x ∈ frontier K := fun x hx hxc ↦
      mm_mem_frontier hKd (hKnK n (mm_mem_of_frontier (hKn n) hx))
        (fun hxi ↦ hx.2 (hint n x hxi hxc))
    have hadm := mm_isAdmissible hKd (hfr _ (h0F n) g0) (hfr _ (h2F n) g2)
      (by rw [← h012 n]; exact hfr _ (h1F n) g1)
    rw [← h012 n, (hB n).2] at hadm
    have h1 := mm_minimalDeterminant_le (hΛ n).1 hadm
    rw [(hΛ n).2.2] at h1
    linarith [hΔ n]
  -- the points stay outside a fixed neighbourhood `W` of `0`
  set W : Set (Fin 2 → ℝ) := interior K ∩ {x | |a ⬝ᵥ x| < M / 2} with hW
  have hWo : IsOpen W := isOpen_interior.inter (isOpen_lt (irr_continuous_abs_dot a)
    continuous_const)
  have hW0 : (0 : Fin 2 → ℝ) ∈ W := ⟨mm_zero_mem_interior hKd, by simpa using half_pos hM⟩
  have hWn : ∀ n x, x ∈ frontier (Kn n) → x ∉ W := fun n x hx hxW ↦
    hx.2 (hint n x hxW.1 (lt_of_lt_of_le hxW.2 (hc0 n)))
  -- a convergent subsequence
  have hmemK : ∀ n, (P₀ n, P₂ n) ∈ K ×ˢ K := fun n ↦
    ⟨hKnK n (mm_mem_of_frontier (hKn n) (h0F n)), hKnK n (mm_mem_of_frontier (hKn n) (h2F n))⟩
  obtain ⟨⟨Q₀, Q₂⟩, ⟨hQ₀K, hQ₂K⟩, φ, hφ, hlim⟩ := (hKd.2.1.prod hKd.2.1).tendsto_subseq hmemK
  have t0 : Tendsto (fun n ↦ P₀ (φ n)) atTop (𝓝 Q₀) := hlim.fst_nhds
  have t2 : Tendsto (fun n ↦ P₂ (φ n)) atTop (𝓝 Q₂) := hlim.snd_nhds
  have t1 : Tendsto (fun n ↦ P₁ (φ n)) atTop (𝓝 (Q₀ + Q₂)) := by
    simp only [h012]; exact t0.add t2
  have tc : Tendsto (fun n ↦ c (φ n)) atTop (𝓝 M) := hctend.comp hφ.tendsto_atTop
  -- the limit lattice is `K`-admissible
  have hadm : ∀ m k : ℤ, (m : ℝ) • Q₀ + (k : ℝ) • (Q₀ + Q₂) ∈ interior K →
      (m : ℝ) • Q₀ + (k : ℝ) • (Q₀ + Q₂) = 0 := by
    intro m k hy
    have ty : Tendsto (fun n ↦ (m : ℝ) • P₀ (φ n) + (k : ℝ) • P₁ (φ n)) atTop
        (𝓝 ((m : ℝ) • Q₀ + (k : ℝ) • (Q₀ + Q₂))) :=
      (t0.const_smul _).add (t1.const_smul _)
    have e1 : ∀ᶠ n in atTop, (m : ℝ) • P₀ (φ n) + (k : ℝ) • P₁ (φ n) ∈ interior K :=
      ty (isOpen_interior.mem_nhds hy)
    have tdot : Tendsto (fun n ↦ |a ⬝ᵥ ((m : ℝ) • P₀ (φ n) + (k : ℝ) • P₁ (φ n))|) atTop
        (𝓝 |a ⬝ᵥ ((m : ℝ) • Q₀ + (k : ℝ) • (Q₀ + Q₂))|) :=
      ((irr_continuous_abs_dot a).tendsto _).comp ty
    have e2 := tdot.eventually_lt tc (hlt _ hy)
    have e3 : ∀ᶠ n in atTop, (m : ℝ) • P₀ (φ n) + (k : ℝ) • P₁ (φ n) = 0 := by
      filter_upwards [e1, e2] with n h1 h2
      have hmem : (m : ℝ) • P₀ (φ n) + (k : ℝ) • P₁ (φ n) ∈ Λ (φ n) := by
        rw [← (hB (φ n)).2]; exact mm_mem_span_pair.2 ⟨m, k, rfl⟩
      exact (hΛ (φ n)).2.1 _ hmem (hint _ _ h1 h2)
    exact tendsto_nhds_unique ty
      ((tendsto_const_nhds (x := (0 : Fin 2 → ℝ))).congr' (e3.mono fun n h ↦ h.symm))
  -- the limit points are nonzero boundary points of `K`
  have hnW : ∀ {f : ℕ → Fin 2 → ℝ} {q : Fin 2 → ℝ}, Tendsto f atTop (𝓝 q) → (∀ n, f n ∉ W) →
      q ≠ 0 := by
    intro f q hf hfW hq
    obtain ⟨n, hn⟩ := (hf.eventually_mem (hWo.mem_nhds (hq ▸ hW0))).exists
    exact hfW n hn
  have hQ0 := hnW t0 (fun n ↦ hWn _ _ (h0F (φ n)))
  have hQ1 := hnW t1 (fun n ↦ hWn _ _ (h1F (φ n)))
  have hQ2 := hnW t2 (fun n ↦ hWn _ _ (h2F (φ n)))
  have hQ₁K : Q₀ + Q₂ ∈ K := hKd.2.1.isClosed.mem_of_tendsto t1
    (Eventually.of_forall fun n ↦ hKnK _ (mm_mem_of_frontier (hKn _) (h1F (φ n))))
  have hF0 : Q₀ ∈ frontier K := mm_mem_frontier hKd hQ₀K fun hi ↦ hQ0 (by
    have := hadm 1 0 (by simpa using hi)
    simpa using this)
  have hF1 : Q₀ + Q₂ ∈ frontier K := mm_mem_frontier hKd hQ₁K fun hi ↦ hQ1 (by
    have := hadm 0 1 (by simpa using hi)
    simpa using this)
  have e2 : ((-1 : ℤ) : ℝ) • Q₀ + ((1 : ℤ) : ℝ) • (Q₀ + Q₂) = Q₂ := by
    push_cast; module
  have hF2 : Q₂ ∈ frontier K := mm_mem_frontier hKd hQ₂K fun hi ↦ hQ2 (by
    have := hadm (-1) 1 (by rw [e2]; exact hi)
    rwa [e2] at this)
  -- the limit lattice is critical
  have hcr : cross Q₀ (Q₀ + Q₂) ≠ 0 := by
    have : cross Q₀ (Q₀ + Q₂) = cross Q₀ Q₂ := by simp only [cross, Pi.add_apply]; ring
    rw [this]; exact mm_cross_ne_zero hKd hF0 hF2 hF1
  have hlat := mm_isLattice_span hcr
  have hadm' : IsAdmissible K (Submodule.span ℤ {Q₀, Q₀ + Q₂}) := by
    intro x hx hxK
    obtain ⟨m, k, rfl⟩ := mm_mem_span_pair.1 hx
    exact hadm m k hxK
  have hcrit : IsCritical K (Submodule.span ℤ {Q₀, Q₀ + Q₂}) := by
    refine ⟨hlat, hadm', le_antisymm ?_ (mm_minimalDeterminant_le hlat hadm')⟩
    rw [mm_det_span hcr]
    have hcc : Continuous fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) ↦ |cross p.1 p.2| := by
      simp only [cross]; fun_prop
    have tcr : Tendsto (fun n ↦ |cross (P₀ (φ n)) (P₁ (φ n))|) atTop
        (𝓝 |cross Q₀ (Q₀ + Q₂)|) := (hcc.tendsto _).comp (t0.prodMk_nhds t1)
    refine le_of_tendsto tcr (Eventually.of_forall fun n ↦ ?_)
    rw [hdetΔ (φ n)]
    exact (hΔ (φ n)).le
  -- one of the limit points lies on `±ℓ`
  have hon : M ≤ |a ⬝ᵥ Q₀| ∨ M ≤ |a ⬝ᵥ (Q₀ + Q₂)| ∨ M ≤ |a ⬝ᵥ Q₂| := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f0 := (((irr_continuous_abs_dot a).tendsto _).comp t0).eventually_lt tc g0
    have f1 := (((irr_continuous_abs_dot a).tendsto _).comp t1).eventually_lt tc g1
    have f2 := (((irr_continuous_abs_dot a).tendsto _).comp t2).eventually_lt tc g2
    obtain ⟨n, i0, i1, i2⟩ := (f0.and (f1.and f2)).exists
    simp only [Function.comp_apply] at i0 i1 i2
    rcases hcap (φ n) with h | h | h <;> linarith
  have hside : ∀ q ∈ K, M ≤ |a ⬝ᵥ q| → q ∈ {x | a ⬝ᵥ x = M} ∨ -q ∈ {x | a ⬝ᵥ x = M} := by
    intro q hq hMq
    have := le_antisymm (habs q hq) hMq
    rcases (abs_eq hM.le).1 this with h | h
    · exact Or.inl h
    · right; change a ⬝ᵥ -q = M; rw [dotProduct_neg, h, neg_neg]
  have m0 : Q₀ ∈ Submodule.span ℤ {Q₀, Q₀ + Q₂} := Submodule.subset_span (by simp)
  have m1 : Q₀ + Q₂ ∈ Submodule.span ℤ {Q₀, Q₀ + Q₂} := Submodule.subset_span (by simp)
  have m2 : Q₂ ∈ Submodule.span ℤ {Q₀, Q₀ + Q₂} := by
    have := Submodule.sub_mem _ m1 m0
    rwa [add_sub_cancel_left] at this
  refine ⟨_, Q₀, Q₀ + Q₂, Q₂, hcrit, m0, m1, m2, hF0, hF1, hF2, mm_isBasis_span hcr, rfl, ?_⟩
  rcases hon with h | h | h
  · rcases hside _ hQ₀K h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases hside _ hQ₁K h with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
  · rcases hside _ hQ₂K h with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))

/-- **Mahler (1947), Lemma 3, at exposed points.** If `K` is irreducible, every boundary point
`u` that is the only point of `K` on some tac-line belongs to a critical lattice of `K`. -/
theorem mahler_irreducible_exposed {K : Set (Fin 2 → ℝ)}
    (hK : MahlerIrreducible.IsIrreducible K)
    {ℓ : Set (Fin 2 → ℝ)} (hℓ : IsTacLine K ℓ) {u : Fin 2 → ℝ} (hu : ℓ ∩ K = {u}) :
    ∃ Λ, MinkowskiMahler.IsCritical K Λ ∧ u ∈ Λ := by
  obtain ⟨Λ, P₀, P₁, P₂, hΛ, h0, h1, h2, f0, f1, f2, -, -, hon⟩ := mahler_irreducible hK hℓ
  have hKd := hK.1
  have key : ∀ P ∈ Λ, P ∈ frontier K → P ∈ ℓ ∨ -P ∈ ℓ → u ∈ Λ := by
    intro P hP hPF hPℓ
    have hPK := mm_mem_of_frontier hKd hPF
    rcases hPℓ with h | h
    · have : P ∈ ℓ ∩ K := ⟨h, hPK⟩
      rw [hu] at this
      rw [← this]; exact hP
    · have : -P ∈ ℓ ∩ K := ⟨h, hKd.2.2.2 P hPK⟩
      rw [hu] at this
      rw [← this]; exact Λ.neg_mem hP
  refine ⟨Λ, hΛ, ?_⟩
  rcases hon with h | h | h | h | h | h
  · exact key _ h0 f0 (Or.inl h)
  · exact key _ h0 f0 (Or.inr h)
  · exact key _ h1 f1 (Or.inl h)
  · exact key _ h1 f1 (Or.inr h)
  · exact key _ h2 f2 (Or.inl h)
  · exact key _ h2 f2 (Or.inr h)

namespace MahlerIrreducible

open Set Filter Topology MinkowskiMahler Mahler1947 BoundaryArc

section Lemma3

variable {K : Set (Fin 2 → ℝ)}

/-! ### Linear algebra in the plane -/

/-- A vector `w` with `det(X, w) = 0` is a multiple of `X ≠ 0`. -/
lemma ml3_parallel {X w : Fin 2 → ℝ} (h : cross X w = 0) (hX : X ≠ 0) : ∃ τ : ℝ, w = τ • X := by
  simp only [cross] at h
  by_cases h0 : X 0 = 0
  · have h1 : X 1 ≠ 0 := by
      intro h1; apply hX; ext i; fin_cases i <;> simp [h0, h1]
    refine ⟨w 1 / X 1, ?_⟩
    ext i; fin_cases i
    · have : w 0 * X 1 = 0 := by rw [h0] at h; linarith
      have hw0 : w 0 = 0 := (mul_eq_zero.1 this).resolve_right h1
      simp [h0, hw0]
    · simp; field_simp
  · refine ⟨w 0 / X 0, ?_⟩
    ext i; fin_cases i
    · simp; field_simp
    · simp; field_simp; linarith

/-- A continuous linear functional on the plane is a dot product. -/
lemma ml3_dual_vec (f : StrongDual ℝ (Fin 2 → ℝ)) :
    ∃ a : Fin 2 → ℝ, ∀ x, a ⬝ᵥ x = f x := by
  refine ⟨![f (Pi.single 0 1), f (Pi.single 1 1)], fun x ↦ ?_⟩
  have hx : x = x 0 • (Pi.single 0 1 : Fin 2 → ℝ) + x 1 • (Pi.single 1 1 : Fin 2 → ℝ) := by
    ext i; fin_cases i <;> simp
  conv_rhs => rw [hx]
  simp only [map_add, map_smul, smul_eq_mul, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- Two vectors annihilated by the same nonzero functional are parallel. -/
lemma ml3_cross_eq_zero_of_dot {a v w : Fin 2 → ℝ} (ha : a ≠ 0) (hv : a ⬝ᵥ v = 0)
    (hw : a ⬝ᵥ w = 0) : cross v w = 0 := by
  simp only [dotProduct, Fin.sum_univ_two] at hv hw
  simp only [cross]
  have h0 : a 0 * (v 0 * w 1 - v 1 * w 0) = 0 := by linear_combination w 1 * hv - v 1 * hw
  have h1 : a 1 * (v 0 * w 1 - v 1 * w 0) = 0 := by linear_combination v 0 * hw - w 0 * hv
  by_contra hne
  apply ha
  ext i; fin_cases i
  · exact (mul_eq_zero.1 h0).resolve_right hne
  · exact (mul_eq_zero.1 h1).resolve_right hne

/-! ### Arcs in determinant form -/

lemma ml5_cross_smul_right (c : ℝ) (u v : Fin 2 → ℝ) : cross u (c • v) = c * cross u v := by
  simp only [cross, Pi.smul_apply, smul_eq_mul]; ring

lemma ml5_continuous_cross_left (b : Fin 2 → ℝ) : Continuous fun x : Fin 2 → ℝ ↦ cross x b := by
  simp only [cross]; fun_prop

lemma ml5_continuous_cross_right (a : Fin 2 → ℝ) : Continuous fun x : Fin 2 → ℝ ↦ cross a x := by
  simp only [cross]; fun_prop

/-- `0` is not on the segment `[R, S]` when `det(R, S) ≠ 0`. -/
lemma ml5_zero_notMem_segment {R S : Fin 2 → ℝ} (h : cross R S ≠ 0) :
    (0 : Fin 2 → ℝ) ∉ segment ℝ R S := by
  rintro ⟨a, b, ha, hb, hab, h0⟩
  have h1 := congrArg (fun x ↦ cross R x) h0
  have h2 := congrArg (fun x ↦ cross x S) h0
  simp only [mm_cross_add_smul, mm_cross_smul_add, mm_cross_self] at h1 h2
  simp only [cross, Pi.zero_apply, mul_zero, zero_mul, sub_zero] at h1 h2
  have e1 : b * cross R S = 0 := by simp only [cross]; linarith
  have e2 : a * cross R S = 0 := by simp only [cross]; linarith
  have := (mul_eq_zero.1 e1).resolve_right h
  have := (mul_eq_zero.1 e2).resolve_right h
  linarith

/-- The inner points of the arc between `R` and `S` (`det(R, S) > 0`) are the boundary points `X`
with `det(R, X) > 0` and `det(X, S) > 0`. -/
lemma ml5_mem_openArc_iff {R S X : Fin 2 → ℝ} (h : 0 < cross R S) :
    X ∈ openArc K R S ↔ X ∈ frontier K ∧ 0 < cross R X ∧ 0 < cross X S := by
  constructor
  · rintro ⟨hX, a, b, ha, hb, rfl⟩
    refine ⟨hX, ?_, ?_⟩
    · rw [mm_cross_add_smul, mm_cross_self]; nlinarith
    · rw [mm_cross_smul_add, mm_cross_self]; nlinarith
  · rintro ⟨hX, h1, h2⟩
    exact ⟨hX, _, _, div_pos h2 h, div_pos h1 h, mm_eq_comb h.ne' X⟩

/-- The points of the arc between `R` and `S` (`det(R, S) > 0`) are the boundary points `X` with
`det(R, X) ≥ 0` and `det(X, S) ≥ 0`. -/
lemma ml5_mem_arc_iff {R S X : Fin 2 → ℝ} (h : 0 < cross R S) :
    X ∈ arc K R S ↔ X ∈ frontier K ∧ 0 ≤ cross R X ∧ 0 ≤ cross X S := by
  constructor
  · rintro ⟨hX, a, b, ha, hb, rfl⟩
    refine ⟨hX, ?_, ?_⟩
    · rw [mm_cross_add_smul, mm_cross_self]; nlinarith
    · rw [mm_cross_smul_add, mm_cross_self]; nlinarith
  · rintro ⟨hX, h1, h2⟩
    exact ⟨hX, _, _, div_nonneg h2 h.le, div_nonneg h1 h.le, mm_eq_comb h.ne' X⟩

/-- **The part of `K` beyond a chord lies in the cone of its ends** (`BoundaryArc.add_le_one_of_neg`
in determinant form): for boundary points `R, S` with `det(R, S) > 0` and `X ∈ K` outside the
cone of `R, S`, `X` lies on the side of the chord `RS` of the origin. -/
lemma ml5_chord (hK : IsSymmetricConvexDomain K) {R S X : Fin 2 → ℝ} (hR : R ∈ frontier K)
    (hS : S ∈ frontier K) (hRS : 0 < cross R S) (hX : X ∈ K)
    (h : cross R X < 0 ∨ cross X S < 0) : cross X S + cross R X ≤ cross R S := by
  have hdec := mm_eq_comb hRS.ne' X
  have h0 := mm_zero_mem_interior hK
  have key : cross X S / cross R S + cross R X / cross R S ≤ 1 := by
    rcases h with h | h
    · exact add_le_one_of_neg hK.1 h0 hR.2 (mm_mem_of_frontier hK hS)
        (by rw [← hdec]; exact hX) (div_neg_of_neg_of_pos h hRS)
    · have := add_le_one_of_neg hK.1 h0 hS.2 (mm_mem_of_frontier hK hR)
        (a := cross R X / cross R S) (b := cross X S / cross R S)
        (by rw [add_comm, ← hdec]; exact hX) (div_neg_of_neg_of_pos h hRS)
      linarith
  rwa [← add_div, div_le_one hRS] at key

/-- **Boundary points in the cone of a chord lie beyond it** (`BoundaryArc.one_le_add` in
determinant form). -/
lemma ml5_beyond (hK : IsSymmetricConvexDomain K) {R S X : Fin 2 → ℝ} (hR : R ∈ K) (hS : S ∈ K)
    (hRS : 0 < cross R S) (hX : X ∈ frontier K) (h1 : 0 ≤ cross R X) (h2 : 0 ≤ cross X S) :
    cross R S ≤ cross X S + cross R X := by
  have := one_le_add hK.1 (mm_zero_mem_interior hK) hR hS (div_nonneg h2 hRS.le)
    (div_nonneg h1 hRS.le) (by rw [← mm_eq_comb hRS.ne' X]; exact hX.2)
  rwa [← add_div, le_div_iff₀ hRS, one_mul] at this

/-- A ray from `O` meets the boundary once. -/
lemma ml5_ray (hK : IsSymmetricConvexDomain K) {X : Fin 2 → ℝ} (hX : X ∈ frontier K) {c : ℝ}
    (hc : 0 < c) (hcX : c • X ∈ frontier K) : c = 1 := by
  have h1 := mm_le_one_of_smul_mem hK hX hc.le (mm_mem_of_frontier hK hcX)
  have h2 := mm_le_one_of_smul_mem hK hcX (inv_nonneg.2 hc.le)
    (by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]; exact mm_mem_of_frontier hK hX)
  have : 1 ≤ c := by
    by_contra h; push Not at h
    have := one_lt_inv_iff₀.2 ⟨hc, h⟩
    linarith
  linarith

/-- Two boundary points on the same ray from `O` (`det(X, Y) = 0`, both on the positive side of
some `R`) coincide. -/
lemma ml5_eq_of_cross_eq_zero (hK : IsSymmetricConvexDomain K) {R X Y : Fin 2 → ℝ}
    (hX : X ∈ frontier K) (hY : Y ∈ frontier K) (hXY : cross X Y = 0) (hRX : 0 < cross R X)
    (hRY : 0 < cross R Y) : X = Y := by
  obtain ⟨τ, hτ⟩ := ml3_parallel hXY (mm_ne_zero_of_frontier hK hX)
  have e : cross R Y = τ * cross R X := by rw [hτ, ml5_cross_smul_right]
  have hτ0 : 0 < τ := by
    by_contra h; push Not at h; nlinarith
  rw [hτ, ml5_ray hK hX hτ0 (hτ ▸ hY), one_smul]

/-! ### Mahler's Lemma 2 of paper A -/

/-- **Mahler, paper A, Lemma 2**: all points of `I₂(P₁)` lie at the same distance from the line
`L₁ = OP₁`: two pairs `P₂', P₃' = P₂' - P₁` and `P₂'', P₃'' = P₂'' - P₁` of boundary points on
the positive side of `L₁` have `det(P₁, P₂') = det(P₁, P₂'')`.

Mahler's proof. Let `δ' = det(P₁, P₂') < δ'' = det(P₁, P₂'')`. Since `C₊` is a convex arc, `P₂''`
and `P₃''` lie on the arc of `C₊` bounded by `P₂'` and `P₃'` (they lie beyond the chord `P₂'P₃'`,
hence in the cone of its ends, `ml5_chord`), in the order `P₂', P₂'', P₃'', P₃'`. The lines `L₂`
through `P₂', P₂''` and `L₃` through `P₃', P₃''` are parallel, and by the convexity of `C`
(`ml5_chord` for the chords `P₂'P₂''` and `P₃''P₃'`) `P₁` and `-P₁` lie in the strip between them.
This is impossible: the segment from `-P₁` to `P₁` is parallel to, but twice as long as, the
segment from `P₃'` to `P₂'`. -/
lemma ml3_width_eq (hK : IsSymmetricConvexDomain K) {X U V : Fin 2 → ℝ} (hX : X ∈ K)
    (hU : U ∈ frontier K) (hUX : U - X ∈ frontier K) (hV : V ∈ frontier K)
    (hVX : V - X ∈ frontier K) (hU0 : 0 < cross X U) (hV0 : 0 < cross X V) :
    cross X U = cross X V := by
  -- the case `δ' < δ''`
  have key : ∀ U V : Fin 2 → ℝ, U ∈ frontier K → U - X ∈ frontier K → V ∈ frontier K →
      V - X ∈ frontier K → 0 < cross X U → cross X U < cross X V → False := by
    intro U V hU hUX hV hVX hU0 hlt
    have hUK := mm_mem_of_frontier hK hU
    have hVK := mm_mem_of_frontier hK hV
    have hUXK := mm_mem_of_frontier hK hUX
    have hVXK := mm_mem_of_frontier hK hVX
    -- `det(P₂', P₃') = δ'`
    have c23 : cross U (U - X) = cross X U := by simp only [cross, Pi.sub_apply]; ring
    -- `P₂''` and `P₃''` lie beyond the chord `P₂'P₃'`, hence on the arc between `P₂'` and `P₃'`
    have hsum : ∀ Y, cross Y (U - X) + cross U Y = cross X Y := fun Y ↦ by
      simp only [cross, Pi.sub_apply]; ring
    have hon : ∀ Y ∈ K, cross X U < cross X Y → 0 ≤ cross U Y ∧ 0 ≤ cross Y (U - X) := by
      intro Y hY hY'
      by_contra h
      rw [not_and_or, not_le, not_le] at h
      have := ml5_chord hK hU hUX (by rw [c23]; exact hU0) hY h
      rw [hsum, c23] at this
      linarith
    obtain ⟨h1, -⟩ := hon V hVK hlt
    obtain ⟨-, h2⟩ := hon (V - X) hVXK (by
      rw [show cross X (V - X) = cross X V by simp only [cross, Pi.sub_apply]; ring]; exact hlt)
    -- strictly: `P₂''` is not on the ray of `P₂'`, nor `P₃''` on the ray of `P₃'`
    have hstrict : ∀ W Y : Fin 2 → ℝ, W ∈ frontier K → Y ∈ frontier K → 0 < cross X W →
        cross X W < cross X Y → cross W Y ≠ 0 := by
      intro W Y hW hY hW0 hWY h0
      obtain ⟨τ, hτ⟩ := ml3_parallel h0 (mm_ne_zero_of_frontier hK hW)
      have e : cross X Y = τ * cross X W := by rw [hτ, ml5_cross_smul_right]
      have hτ1 : 1 < τ := by
        by_contra h; push Not at h; nlinarith
      have := ml5_ray hK hW (by linarith) (hτ ▸ hY)
      linarith
    have h1' : 0 < cross U V := lt_of_le_of_ne h1 (hstrict U V hU hV hU0 hlt).symm
    have h2' : 0 < cross (V - X) (U - X) := by
      refine lt_of_le_of_ne h2 fun h ↦ hstrict (U - X) (V - X) hUX hVX
        (by rw [show cross X (U - X) = cross X U by simp only [cross, Pi.sub_apply]; ring]
            exact hU0)
        (by rw [show cross X (U - X) = cross X U by simp only [cross, Pi.sub_apply]; ring,
              show cross X (V - X) = cross X V by simp only [cross, Pi.sub_apply]; ring]
            exact hlt) ?_
      rw [mm_cross_swap, ← h, neg_zero]
    -- `P₁` lies on the side of `L₂` of the origin, `-P₁` on the side of `L₃` of the origin
    have s1 := ml5_chord hK hU hV h1' hX (Or.inl (by rw [mm_cross_swap]; linarith))
    have e0 : cross (-X) (U - X) = -cross X U := by
      simp only [cross, Pi.sub_apply, Pi.neg_apply]; ring
    have s2 := ml5_chord hK hVX hUX h2' (hK.2.2.2 X hX) (Or.inr (by rw [e0]; linarith))
    -- the strip is narrower than the segment `[-P₁, P₁]`
    have e1 : cross X V + cross U X = cross X V - cross X U := by rw [mm_cross_swap U X]; ring
    have e2 : cross (-X) (U - X) + cross (V - X) (-X) = cross X V - cross X U := by
      simp only [cross, Pi.sub_apply, Pi.neg_apply]; ring
    have e3 : cross (V - X) (U - X) = cross X V - cross X U - cross U V := by
      simp only [cross, Pi.sub_apply]; ring
    rw [e1] at s1
    rw [e2, e3] at s2
    linarith
  rcases lt_trichotomy (cross X U) (cross X V) with h | h | h
  · exact (key U V hU hUX hV hVX hU0 h).elim
  · exact h
  · exact (key V U hV hVX hU hUX hV0 h).elim

/-- Uniqueness of `A(X)` with absolute values (`ml3_width_eq` after reorienting the pairs). -/
lemma ml3_width_abs (hK : IsSymmetricConvexDomain K) {X U V : Fin 2 → ℝ} (hX : X ∈ K)
    (hU : U ∈ frontier K) (hUX : U - X ∈ frontier K) (hV : V ∈ frontier K)
    (hVX : V - X ∈ frontier K) (hU0 : cross X U ≠ 0) (hV0 : cross X V ≠ 0) :
    |cross X U| = |cross X V| := by
  have flip : ∀ W, W ∈ frontier K → W - X ∈ frontier K → cross X W ≠ 0 →
      ∃ W', W' ∈ frontier K ∧ W' - X ∈ frontier K ∧ 0 < cross X W' ∧
        |cross X W| = cross X W' := by
    intro W hW hWX hW0
    rcases hW0.lt_or_gt with h | h
    · refine ⟨X - W, by rw [← neg_sub]; exact mm_neg_mem_frontier hK hWX,
        by rw [show X - W - X = -W by abel]; exact mm_neg_mem_frontier hK hW, ?_, ?_⟩
      · have : cross X (X - W) = -cross X W := by simp only [cross, Pi.sub_apply]; ring
        rw [this]; linarith
      · have : cross X (X - W) = -cross X W := by simp only [cross, Pi.sub_apply]; ring
        rw [this, abs_of_neg h]
    · exact ⟨W, hW, hWX, h, abs_of_pos h⟩
  obtain ⟨U', hU'F, hU'X, hU'0, hU'eq⟩ := flip U hU hUX hU0
  obtain ⟨V', hV'F, hV'X, hV'0, hV'eq⟩ := flip V hV hVX hV0
  rw [hU'eq, hV'eq]
  exact ml3_width_eq hK hX hU'F hU'X hV'F hV'X hU'0 hV'0

/-! ### The set of boundary points on critical lattices is closed -/

/-- **Mahler, paper A, Lemma 11** (in the plane, for convex domains): the set `Π` of boundary
points of `K` that lie on a critical lattice of `K` is closed. A limit of such points lies on the
limit of a convergent subsequence of the critical lattices (Lemma 2 bases on the boundary). -/
lemma ml3_isClosed (hK : IsSymmetricConvexDomain K) :
    IsClosed {x | x ∈ frontier K ∧ ∃ Λ, IsCritical K Λ ∧ x ∈ Λ} := by
  refine IsSeqClosed.isClosed fun {xs x} hxs hlim ↦ ?_
  choose hF Λ hΛ hxΛ using hxs
  have hconf := fun n ↦ (minkowski_mahler hK).1 (Λ n) (hΛ n)
  choose P₀ P₁ P₂ h0Λ h1Λ h2Λ h0F h1F h2F hB h012 hdetΛ hdetΔ using hconf
  have hmemK : ∀ n, (P₀ n, P₁ n) ∈ K ×ˢ K :=
    fun n ↦ ⟨mm_mem_of_frontier hK (h0F n), mm_mem_of_frontier hK (h1F n)⟩
  obtain ⟨⟨Q₀, Q₁⟩, -, φ, hφ, hlim'⟩ := (hK.2.1.prod hK.2.1).tendsto_subseq hmemK
  have t0 : Tendsto (fun n ↦ P₀ (φ n)) atTop (𝓝 Q₀) := hlim'.fst_nhds
  have t1 : Tendsto (fun n ↦ P₁ (φ n)) atTop (𝓝 Q₁) := hlim'.snd_nhds
  have tx : Tendsto (fun n ↦ xs (φ n)) atTop (𝓝 x) := hlim.comp hφ.tendsto_atTop
  have hΔ := irr_minimalDeterminant_pos hK
  have hcc : Continuous fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) ↦ cross p.1 p.2 := by
    simp only [cross]; fun_prop
  have tcr : Tendsto (fun n ↦ cross (P₀ (φ n)) (P₁ (φ n))) atTop (𝓝 (cross Q₀ Q₁)) :=
    (hcc.tendsto _).comp (t0.prodMk_nhds t1)
  have habs : |cross Q₀ Q₁| = minimalDeterminant K :=
    tendsto_nhds_unique tcr.abs (tendsto_const_nhds.congr fun n ↦ (hdetΔ (φ n)).symm)
  have hcr : cross Q₀ Q₁ ≠ 0 := by intro h; rw [h, abs_zero] at habs; linarith
  have hcrn : ∀ n, cross (P₀ n) (P₁ n) ≠ 0 := fun n h ↦ by
    have := hdetΔ n; rw [h, abs_zero] at this; linarith
  -- the limit lattice is `K`-admissible
  have hadm : IsAdmissible K (Submodule.span ℤ {Q₀, Q₁}) := by
    intro y hy hyK
    obtain ⟨m, k, rfl⟩ := mm_mem_span_pair.1 hy
    have ty : Tendsto (fun n ↦ (m : ℝ) • P₀ (φ n) + (k : ℝ) • P₁ (φ n)) atTop
        (𝓝 ((m : ℝ) • Q₀ + (k : ℝ) • Q₁)) := (t0.const_smul _).add (t1.const_smul _)
    have e1 : ∀ᶠ n in atTop, (m : ℝ) • P₀ (φ n) + (k : ℝ) • P₁ (φ n) ∈ interior K :=
      ty (isOpen_interior.mem_nhds hyK)
    have e3 : ∀ᶠ n in atTop, (m : ℝ) • P₀ (φ n) + (k : ℝ) • P₁ (φ n) = 0 := by
      filter_upwards [e1] with n h1
      have hmem : (m : ℝ) • P₀ (φ n) + (k : ℝ) • P₁ (φ n) ∈ Λ (φ n) := by
        rw [← (hB (φ n)).2]; exact mm_mem_span_pair.2 ⟨m, k, rfl⟩
      exact (hΛ (φ n)).2.1 _ hmem h1
    exact tendsto_nhds_unique ty
      ((tendsto_const_nhds (x := (0 : Fin 2 → ℝ))).congr' (e3.mono fun n h ↦ h.symm))
  have hcrit : IsCritical K (Submodule.span ℤ {Q₀, Q₁}) :=
    ⟨mm_isLattice_span hcr, hadm, by rw [mm_det_span hcr, habs]⟩
  -- integer coordinates of `x`
  have hcoef : ∀ n, ∃ m k : ℤ, cross (xs n) (P₁ n) / cross (P₀ n) (P₁ n) = m ∧
      cross (P₀ n) (xs n) / cross (P₀ n) (P₁ n) = k := by
    intro n
    have hx := hxΛ n
    rw [← (hB n).2] at hx
    obtain ⟨m, k, hmk⟩ := mm_mem_span_pair.1 hx
    refine ⟨m, k, ?_, ?_⟩
    · rw [← hmk, mm_cross_smul_add, mm_cross_self]; field_simp [hcrn n]; ring
    · rw [← hmk, mm_cross_add_smul, mm_cross_self]; field_simp [hcrn n]; ring
  choose m k hm hk using hcoef
  have ta : Tendsto (fun n ↦ cross (xs (φ n)) (P₁ (φ n)) / cross (P₀ (φ n)) (P₁ (φ n))) atTop
      (𝓝 (cross x Q₁ / cross Q₀ Q₁)) :=
    (((hcc.tendsto _).comp (tx.prodMk_nhds t1))).div tcr hcr
  have tb : Tendsto (fun n ↦ cross (P₀ (φ n)) (xs (φ n)) / cross (P₀ (φ n)) (P₁ (φ n))) atTop
      (𝓝 (cross Q₀ x / cross Q₀ Q₁)) :=
    (((hcc.tendsto _).comp (t0.prodMk_nhds tx))).div tcr hcr
  have ha : cross x Q₁ / cross Q₀ Q₁ ∈ range ((↑) : ℤ → ℝ) :=
    Real.isClosed_range_intCast.mem_of_tendsto ta
      (Eventually.of_forall fun n ↦ ⟨m (φ n), (hm (φ n)).symm⟩)
  have hb : cross Q₀ x / cross Q₀ Q₁ ∈ range ((↑) : ℤ → ℝ) :=
    Real.isClosed_range_intCast.mem_of_tendsto tb
      (Eventually.of_forall fun n ↦ ⟨k (φ n), (hk (φ n)).symm⟩)
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  refine ⟨isClosed_frontier.mem_of_tendsto tx (Eventually.of_forall fun n ↦ hF _), _, hcrit, ?_⟩
  rw [mm_eq_comb hcr x, ← ha, ← hb]
  exact mm_mem_span_pair.2 ⟨a, b, rfl⟩

/-- A point of a critical lattice on a tac-line (`mahler_irreducible`, in the form used below). -/
lemma ml3_tac_point (hK : IsIrreducible K) {ℓ : Set (Fin 2 → ℝ)} (hℓ : IsTacLine K ℓ) :
    ∃ Z ∈ ℓ, Z ∈ frontier K ∧ ∃ Λ, IsCritical K Λ ∧ Z ∈ Λ := by
  obtain ⟨Λ, P₀, P₁, P₂, hΛ, h0, h1, h2, f0, f1, f2, -, -, hon⟩ := mahler_irreducible hK hℓ
  have key : ∀ P ∈ Λ, P ∈ frontier K → P ∈ ℓ ∨ -P ∈ ℓ →
      ∃ Z ∈ ℓ, Z ∈ frontier K ∧ ∃ Λ, IsCritical K Λ ∧ Z ∈ Λ := by
    intro P hP hPF hPℓ
    rcases hPℓ with h | h
    · exact ⟨P, h, hPF, Λ, hΛ, hP⟩
    · exact ⟨-P, h, mm_neg_mem_frontier hK.1 hPF, Λ, hΛ, Λ.neg_mem hP⟩
  rcases hon with h | h | h | h | h | h
  · exact key _ h0 f0 (Or.inl h)
  · exact key _ h0 f0 (Or.inr h)
  · exact key _ h1 f1 (Or.inl h)
  · exact key _ h1 f1 (Or.inr h)
  · exact key _ h2 f2 (Or.inl h)
  · exact key _ h2 f2 (Or.inr h)

/-- The tac-line `{x | a · x = M}` where `M` is the maximum of `a · x` on `K`. -/
lemma ml3_tacLine_max (hK : IsSymmetricConvexDomain K) {a : Fin 2 → ℝ} (ha : a ≠ 0) :
    ∃ M, (∀ x ∈ K, a ⬝ᵥ x ≤ M) ∧ IsTacLine K {x | a ⬝ᵥ x = M} := by
  obtain ⟨z, hz, hmax⟩ := hK.2.1.exists_isMaxOn ⟨0, interior_subset (mm_zero_mem_interior hK)⟩
    (irr_continuous_dot a).continuousOn
  exact ⟨a ⬝ᵥ z, fun x hx ↦ hmax hx, ⟨a, ha, _, rfl, fun x hx ↦ hmax hx⟩, ⟨z, rfl, hz⟩⟩

/-- An extreme point of `K` lies on its boundary. -/
lemma ml3_extreme_frontier (hK : IsSymmetricConvexDomain K) {e : Fin 2 → ℝ}
    (he : e ∈ K.extremePoints ℝ) : e ∈ frontier K := by
  refine mm_mem_frontier hK he.1 fun hi ↦ ?_
  set v : Fin 2 → ℝ := ![1, 0]
  have hv : v ≠ 0 := fun h ↦ by simpa [v] using congrFun h 0
  have hc : Continuous fun t : ℝ ↦ e + t • v := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), e + t • v ∈ K :=
    hc.continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 hi)
  have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), e + (-t) • v ∈ K :=
    (continuous_neg.tendsto' (0 : ℝ) 0 neg_zero).eventually hev
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ := (((hev.and hev').filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hseg : e ∈ openSegment ℝ (e + t • v) (e + (-t) • v) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
  have := he.2 h1 h2 hseg
  have ht0 : (t : ℝ) ≠ 0 := (show (0 : ℝ) < t from ht).ne'
  apply hv
  have h3 : t • v = 0 := by
    have := congrArg (· - e) this; simpa using this
  exact (smul_eq_zero.1 h3).resolve_left ht0

/-- **Every extreme point of an irreducible domain lies on a critical lattice.** At an exposed
point this is `mahler_irreducible_exposed`. Otherwise the support line at `e` meets `K` in a
segment `[e, b]`; tilting it, the tac-lines `{x | (a - s(b - e)) · x = M_s}` carry points of
critical lattices (`mahler_irreducible`) which tend to `e` as `s → 0⁺`, and `Π` is closed
(`ml3_isClosed`). -/
lemma ml3_extreme (hK : IsIrreducible K) {e : Fin 2 → ℝ} (he : e ∈ K.extremePoints ℝ) :
    ∃ Λ, IsCritical K Λ ∧ e ∈ Λ := by
  have hKd := hK.1
  have heF := ml3_extreme_frontier hKd he
  obtain ⟨f, hf1, hf2, hf3⟩ := mm_support hKd heF
  obtain ⟨a, ha⟩ := ml3_dual_vec f
  have ha0 : a ≠ 0 := by rintro rfl; have := ha e; simp [hf1] at this
  by_cases hface : ∃ b ∈ K, f b = 1 ∧ b ≠ e
  · obtain ⟨b, hbK, hfb, hbe⟩ := hface
    set w := b - e with hw
    have hw0 : w ≠ 0 := sub_ne_zero.2 hbe
    have hww : 0 < w ⬝ᵥ w := irr_dot_self_pos hw0
    have haw : a ⬝ᵥ w = 0 := by rw [hw, dotProduct_sub, ha, ha, hfb, hf1, sub_self]
    set s : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hs
    have hs0 : ∀ n, 0 < s n := fun n ↦ by positivity
    have hstend : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hg0 : ∀ n, a - s n • w ≠ 0 := by
      intro n h
      have : a ⬝ᵥ w = s n * (w ⬝ᵥ w) := by
        rw [sub_eq_zero.1 h, smul_dotProduct, smul_eq_mul]
      rw [haw] at this
      have := mul_pos (hs0 n) hww
      linarith
    have hpt : ∀ n, ∃ Z, (∀ x ∈ K, (a - s n • w) ⬝ᵥ x ≤ (a - s n • w) ⬝ᵥ Z) ∧
        Z ∈ frontier K ∧ ∃ Λ, IsCritical K Λ ∧ Z ∈ Λ := by
      intro n
      obtain ⟨M, hM, hℓ⟩ := ml3_tacLine_max hKd (hg0 n)
      obtain ⟨Z, hZℓ, hZF, hZΛ⟩ := ml3_tac_point hK hℓ
      exact ⟨Z, fun x hx ↦ (hM x hx).trans_eq hZℓ.symm, hZF, hZΛ⟩
    choose Z hZmax hZF hZΛ using hpt
    have hZK : ∀ n, Z n ∈ K := fun n ↦ mm_mem_of_frontier hKd (hZF n)
    obtain ⟨z, hzK, φ, hφ, tz⟩ := hKd.2.1.tendsto_subseq hZK
    -- `w · Z_n ≤ w · e` and `f(Z_n) ≥ 1 + s_n (w · Z_n - w · e)`
    have hineq : ∀ n, w ⬝ᵥ Z n ≤ w ⬝ᵥ e ∧ 1 + s n * (w ⬝ᵥ Z n - w ⬝ᵥ e) ≤ a ⬝ᵥ Z n := by
      intro n
      have h1 := hZmax n e (mm_mem_of_frontier hKd heF)
      have h2 := hf2 _ (hZK n)
      rw [← ha] at h2
      simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, ha e, hf1] at h1
      constructor
      · by_contra hc; push Not at hc
        nlinarith [mul_pos (hs0 n) (sub_pos.2 hc)]
      · linarith
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, ∀ x ∈ K, m₀ ≤ w ⬝ᵥ x := by
      obtain ⟨y, -, hy⟩ := hKd.2.1.exists_isMinOn ⟨e, mm_mem_of_frontier hKd heF⟩
        (irr_continuous_dot w).continuousOn
      exact ⟨w ⬝ᵥ y, fun x hx ↦ hy hx⟩
    have tdot : ∀ c : Fin 2 → ℝ, Tendsto (fun n ↦ c ⬝ᵥ Z (φ n)) atTop (𝓝 (c ⬝ᵥ z)) :=
      fun c ↦ ((irr_continuous_dot c).tendsto _).comp tz
    -- `f(z) = 1`
    have hfz : a ⬝ᵥ z = 1 := by
      refine le_antisymm ((ha z).trans_le (hf2 z hzK)) ?_
      have tl : Tendsto (fun n ↦ 1 + s (φ n) * (m₀ - w ⬝ᵥ e)) atTop (𝓝 1) := by
        have := ((hstend.comp hφ.tendsto_atTop).mul_const (m₀ - w ⬝ᵥ e)).const_add 1
        simpa using this
      refine le_of_tendsto_of_tendsto tl (tdot a) (Eventually.of_forall fun n ↦ ?_)
      have := (hineq (φ n)).2
      have h3 := hm₀ _ (hZK (φ n))
      have := hs0 (φ n)
      nlinarith
    have hwz : w ⬝ᵥ z ≤ w ⬝ᵥ e :=
      le_of_tendsto_of_tendsto (tdot w) tendsto_const_nhds
        (Eventually.of_forall fun n ↦ (hineq (φ n)).1)
    -- `z = e`
    have hcr : cross w (z - e) = 0 :=
      ml3_cross_eq_zero_of_dot ha0 haw (by rw [dotProduct_sub, hfz, ha, hf1, sub_self])
    obtain ⟨τ, hτ⟩ := ml3_parallel hcr hw0
    have hτ0 : τ ≤ 0 := by
      have : w ⬝ᵥ z = w ⬝ᵥ e + τ * (w ⬝ᵥ w) := by
        rw [show z = e + τ • w by rw [← hτ]; abel, dotProduct_add, dotProduct_smul,
          smul_eq_mul]
      nlinarith
    have hze : z = e := by
      rcases hτ0.lt_or_eq with hlt | heq
      · have h1τ : 1 - τ ≠ 0 := by linarith
        have hseg : e ∈ openSegment ℝ z b := by
          refine ⟨1 / (1 - τ), -τ / (1 - τ), by apply div_pos <;> linarith,
            by apply div_pos <;> linarith, by rw [← add_div, div_eq_one_iff_eq h1τ]; ring,
            ?_⟩
          rw [show z = e + τ • w by rw [← hτ]; abel, hw]
          ext i
          simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          field_simp
          ring
        exact he.2 hzK hbK hseg
      · rw [show z = e + τ • w by rw [← hτ]; abel, heq, zero_smul, add_zero]
    rw [hze] at tz
    obtain ⟨-, hΛ⟩ := (ml3_isClosed hKd).mem_of_tendsto tz
      (Eventually.of_forall fun n ↦ ⟨hZF (φ n), hZΛ (φ n)⟩)
    exact hΛ
  · push Not at hface
    refine mahler_irreducible_exposed hK (ℓ := {x | a ⬝ᵥ x = 1})
      ⟨⟨a, ha0, 1, rfl, fun x hx ↦ (ha x).trans_le (hf2 x hx)⟩, ⟨e, by simp [ha, hf1], he.1⟩⟩ ?_
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff, ha]
    constructor
    · rintro ⟨h1, h2⟩; exact hface x h2 h1
    · rintro rfl; exact ⟨hf1, he.1⟩

/-! ### The "if" half (Mahler, paper A, Lemma 12, for convex subdomains) -/

/-- `Δ(K') ≤ Δ(K)` for `K' ⊆ K`: a critical lattice of `K` is `K'`-admissible. -/
lemma ml3_minDet_mono (hK : IsSymmetricConvexDomain K) {K' : Set (Fin 2 → ℝ)} (hsub : K' ⊆ K) :
    minimalDeterminant K' ≤ minimalDeterminant K := by
  obtain ⟨Λ, hlat, hadm, hdet⟩ := irr_exists_critical hK
  rw [← hdet]
  exact mm_minimalDeterminant_le hlat fun x hx hxi ↦ hadm x hx (interior_mono hsub hxi)

/-- A proper symmetric convex subdomain `K'` of `K` misses a boundary point of `K` (the maximum on
`K` of a functional separating a point of `K \ K'` from `K'`). -/
lemma ml3_exists_frontier_notMem (hK : IsSymmetricConvexDomain K) {K' : Set (Fin 2 → ℝ)}
    (hK' : IsSymmetricConvexDomain K') (hsub : K' ⊆ K) (hne : K' ≠ K) :
    ∃ u ∈ frontier K, u ∉ K' := by
  obtain ⟨x, hxK, hxK'⟩ : ∃ x ∈ K, x ∉ K' := by
    by_contra h; push Not at h; exact hne (Subset.antisymm hsub h)
  obtain ⟨f, c, hf, hc⟩ := geometric_hahn_banach_closed_point hK'.1 hK'.2.1.isClosed hxK'
  obtain ⟨a, ha⟩ := ml3_dual_vec f
  have h0 := hf 0 (interior_subset (mm_zero_mem_interior hK'))
  rw [map_zero] at h0
  have ha0 : a ≠ 0 := by
    rintro rfl; have := ha x; simp only [zero_dotProduct] at this; linarith
  obtain ⟨u, huK, hmax⟩ := hK.2.1.exists_isMaxOn ⟨x, hxK⟩ (irr_continuous_dot a).continuousOn
  refine ⟨u, mm_mem_frontier hK huK fun hi ↦ ?_, fun huK' ↦ ?_⟩
  · have := irr_dot_lt ha0 (M := a ⬝ᵥ u) (fun y hy ↦ hmax hy) hi
    linarith
  · have h1 := hf u huK'
    have h2 : a ⬝ᵥ x ≤ a ⬝ᵥ u := hmax hxK
    rw [ha, ha] at h2
    linarith

/-- In a square configuration (`A + B, A - B ∈ K`) a support functional at `A` vanishes at `B`. -/
lemma ml3_square_supp {A B : Fin 2 → ℝ} (hAB : A + B ∈ K) (hAB' : A - B ∈ K)
    (f : StrongDual ℝ (Fin 2 → ℝ)) (hf1 : f A = 1) (hf2 : ∀ y ∈ K, f y ≤ 1) : f B = 0 := by
  have h1 := hf2 _ hAB
  have h2 := hf2 _ hAB'
  rw [map_add, hf1] at h1
  rw [map_sub, hf1] at h2
  linarith

/-- **`A + B` is an extreme point of `K` in a square configuration**: if `A, B, A + B, A - B` are
boundary points, `K` lies in the parallelogram `|f| ≤ 1, |g| ≤ 1` (`f, g` support functionals at
`A, B`), of which `A + B` is a vertex. -/
lemma ml3_square_extreme (hK : IsSymmetricConvexDomain K) {A B : Fin 2 → ℝ}
    (hA : A ∈ frontier K) (hB : B ∈ frontier K) (hAB : A + B ∈ frontier K)
    (hAB' : A - B ∈ frontier K) {x y : Fin 2 → ℝ} (hx : x ∈ K) (hy : y ∈ K)
    (hxy : x + y = (2 : ℝ) • (A + B)) : x = A + B := by
  obtain ⟨f, hf1, hf2, -⟩ := mm_support hK hA
  obtain ⟨g, hg1, hg2, -⟩ := mm_support hK hB
  have hfB := ml3_square_supp (mm_mem_of_frontier hK hAB) (mm_mem_of_frontier hK hAB') f hf1 hf2
  have hgA : g A = 0 := ml3_square_supp (A := B) (B := A)
    (by rw [add_comm]; exact mm_mem_of_frontier hK hAB)
    (by have := hK.2.2.2 _ (mm_mem_of_frontier hK hAB'); rwa [neg_sub] at this) g hg1 hg2
  have hcr := mm_cross_ne_zero hK hA hB hAB
  have hfx := hf2 x hx
  have hfy := hf2 y hy
  have hgx := hg2 x hx
  have hgy := hg2 y hy
  have hf' : f x + f y = 2 := by
    have := congrArg f hxy
    simp only [map_add, map_smul, smul_eq_mul, hf1, hfB] at this; linarith
  have hg' : g x + g y = 2 := by
    have := congrArg g hxy
    simp only [map_add, map_smul, smul_eq_mul, hg1, hgA] at this; linarith
  have hd := mm_eq_comb hcr x
  have hfx' : f x = cross x B / cross A B := by
    conv_lhs => rw [hd]
    simp [hf1, hfB]
  have hgx' : g x = cross A x / cross A B := by
    conv_lhs => rw [hd]
    simp [hg1, hgA]
  rw [hd, show cross x B / cross A B = 1 by linarith, show cross A x / cross A B = 1 by linarith,
    one_smul, one_smul]

/-- The integer case analysis of `ml3_eight`. -/
lemma ml3_int_cases (a b : ℤ) (hpos : 0 < a ∨ (a = 0 ∧ 0 < b)) (h10 : ¬ (a = 1 ∧ b = 0))
    (h01 : ¬ (a = 0 ∧ b = 1)) (h11 : ¬ (a = 1 ∧ b = 1)) :
    (b = 0 ∧ 2 ≤ a) ∨ (a = 0 ∧ 2 ≤ b) ∨ (2 ≤ b ∧ b ≤ a) ∨ (2 ≤ a ∧ a ≤ b) ∨
      (b = 1 ∧ 3 ≤ a) ∨ (a = 1 ∧ 3 ≤ b) ∨ (b < 0 ∧ 2 ≤ a) ∨ (a = 1 ∧ b ≤ -2) ∨
      (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = -1) := by
  rcases hpos with ha | ⟨ha, hb⟩
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · by_cases ha2 : 2 ≤ a
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hb, ha2⟩
      · have ha1 : a = 1 := by omega
        by_cases hb1 : b = -1
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inr <| Or.inr ⟨ha1, hb1⟩
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
            ⟨ha1, by omega⟩
    · exact Or.inl ⟨hb, by omega⟩
    · by_cases hb1 : b = 1
      · by_cases ha2 : a = 2
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inl ⟨ha2, hb1⟩
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hb1, by omega⟩
      · by_cases ha1 : a = 1
        · by_cases hb2 : b = 2
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inr <| Or.inr <| Or.inl ⟨ha1, hb2⟩
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨ha1, by omega⟩
        · rcases le_total b a with hab | hab
          · exact Or.inr <| Or.inr <| Or.inl ⟨by omega, hab⟩
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨by omega, hab⟩
  · exact Or.inr <| Or.inl ⟨ha, by omega⟩

/-- **Lattice points of `K` beyond Minkowski's hexagon.** Let `Q₀, Q₂, Q₀ + Q₂` be boundary points
(so the lattice `Λ` with basis `Q₀, Q₀ + Q₂` is `K`-admissible, Mahler's Lemma 1), and `u` a point
of `Λ ∩ K` other than `0, ±Q₀, ±Q₂, ±(Q₀ + Q₂)`. Then `u = A + B` for a square configuration:
`A, B, A + B, A - B` are boundary points (`u = ±(2Q₀ + Q₂), ±(Q₀ + 2Q₂), ±(Q₀ - Q₂)`; any other
`u` would put a nonzero lattice point in the interior of `K`). -/
lemma ml3_eight (hK : IsSymmetricConvexDomain K) {Q₀ Q₂ u : Fin 2 → ℝ} (h0 : Q₀ ∈ frontier K)
    (h2 : Q₂ ∈ frontier K) (h1 : Q₀ + Q₂ ∈ frontier K) (hu : u ∈ K)
    (huΛ : u ∈ Submodule.span ℤ {Q₀, Q₀ + Q₂})
    (hne : u ≠ 0 ∧ u ≠ Q₀ ∧ u ≠ -Q₀ ∧ u ≠ Q₂ ∧ u ≠ -Q₂ ∧ u ≠ Q₀ + Q₂ ∧ u ≠ -(Q₀ + Q₂)) :
    ∃ A B, A ∈ frontier K ∧ B ∈ frontier K ∧ A + B ∈ frontier K ∧ A - B ∈ frontier K ∧
      u = A + B ∧ |cross A B| = |cross Q₀ Q₂| := by
  have hadm := mm_isAdmissible hK h0 h2 h1
  have hcr : cross Q₀ Q₂ ≠ 0 := mm_cross_ne_zero hK h0 h2 h1
  have hL : ∀ m k : ℤ, (m : ℝ) • Q₀ + (k : ℝ) • Q₂ ∈ Submodule.span ℤ {Q₀, Q₀ + Q₂} :=
    fun m k ↦ mm_mem_span_pair.2 ⟨m - k, k, by push_cast; module⟩
  have hK0 := mm_mem_of_frontier hK h0
  have hK2 := mm_mem_of_frontier hK h2
  have hK1 := mm_mem_of_frontier hK h1
  have hKn0 := hK.2.2.2 _ hK0
  have hKn2 := hK.2.2.2 _ hK2
  have hKn1 := hK.2.2.2 _ hK1
  -- a nonzero lattice point `m Q₀ + k Q₂` cannot be `α x + β y` with `x, y ∈ K`, `α + β < 1`
  have comb : ∀ (x y : Fin 2 → ℝ) (α β : ℝ), x ∈ K → y ∈ K → 0 ≤ α → 0 ≤ β → α + β < 1 →
      ∀ m k : ℤ, (m ≠ 0 ∨ k ≠ 0) → α • x + β • y = (m : ℝ) • Q₀ + (k : ℝ) • Q₂ → False :=
    fun x y α β hx hy hα hβ hαβ m k hmk heq ↦
      mm_comb_ne_zero hcr hmk (hadm _ (hL m k) (heq ▸ mm_comb_mem_interior hK hx hy hα hβ hαβ))
  have core : ∀ (v : Fin 2 → ℝ) (a b : ℤ), v ∈ K → v = (a : ℝ) • Q₀ + (b : ℝ) • Q₂ →
      (0 < a ∨ (a = 0 ∧ 0 < b)) → ¬ (a = 1 ∧ b = 0) → ¬ (a = 0 ∧ b = 1) →
      ¬ (a = 1 ∧ b = 1) → (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = -1) := by
    intro v a b hv hvab hpos h10 h01 h11
    have hcases := ml3_int_cases a b hpos h10 h01 h11
    subst hvab
    rcases hcases with ⟨hb, ha⟩ | ⟨ha, hb⟩ | ⟨hb, hab⟩ | ⟨ha, hab⟩ | ⟨hb, ha⟩ | ⟨ha, hb⟩ |
        ⟨hb, ha⟩ | ⟨ha, hb⟩ | h | h | h
    · have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
      refine (comb _ _ (1 / a) 0 hv hK0 (by positivity) le_rfl (by
        rw [add_zero, div_lt_one (by linarith)]; linarith) 1 0 (by norm_num) ?_).elim
      subst hb; ext i; simp; field_simp
    · have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
      refine (comb _ _ (1 / b) 0 hv hK0 (by positivity) le_rfl (by
        rw [add_zero, div_lt_one (by linarith)]; linarith) 0 1 (by norm_num) ?_).elim
      subst ha; ext i; simp; field_simp
    · have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
      have hab' : (b : ℝ) ≤ a := by exact_mod_cast hab
      have ha0 : (0 : ℝ) < a := by linarith
      refine (comb _ _ (1 / a) (1 - b / a) hv hK2 (by positivity)
        (by rw [sub_nonneg, div_le_one ha0]; exact hab') (by
          have : (1 / a : ℝ) + (1 - b / a) = 1 - (b - 1) / a := by field_simp; ring
          rw [this]; have : 0 < ((b : ℝ) - 1) / a := div_pos (by linarith) ha0
          linarith) 1 1 (by norm_num) ?_).elim
      ext i; simp; field_simp; ring
    · have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
      have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
      have hb0 : (0 : ℝ) < b := by linarith
      refine (comb _ _ (1 / b) (1 - a / b) hv hK0 (by positivity)
        (by rw [sub_nonneg, div_le_one hb0]; exact hab') (by
          have : (1 / b : ℝ) + (1 - a / b) = 1 - (a - 1) / b := by field_simp; ring
          rw [this]; have : 0 < ((a : ℝ) - 1) / b := div_pos (by linarith) hb0
          linarith) 1 1 (by norm_num) ?_).elim
      ext i; simp; field_simp; ring
    · have ha' : (3 : ℝ) ≤ a := by exact_mod_cast ha
      subst hb
      refine (comb _ _ (1 / a) (1 / a) hv hKn2 (by positivity) (by positivity) (by
        rw [← add_div, div_lt_one (by linarith)]; linarith) 1 0 (by norm_num) ?_).elim
      ext i; simp; field_simp
    · have hb' : (3 : ℝ) ≤ b := by exact_mod_cast hb
      subst ha
      refine (comb _ _ (1 / b) (1 / b) hv hKn0 (by positivity) (by positivity) (by
        rw [← add_div, div_lt_one (by linarith)]; linarith) 0 1 (by norm_num) ?_).elim
      ext i; simp; field_simp
    · have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
      have hb' : (b : ℝ) < 0 := by exact_mod_cast hb
      have hd : (0 : ℝ) < a - b := by linarith
      refine (comb _ _ (1 / (a - b)) (-b / (a - b)) hv hK1 (by positivity)
        (div_nonneg (by linarith) hd.le) (by
          rw [← add_div, div_lt_one hd]; linarith) 1 0 (by norm_num) ?_).elim
      ext i; simp; field_simp; ring
    · have hb' : (b : ℝ) ≤ -2 := by exact_mod_cast hb
      subst ha
      have hd : (0 : ℝ) < 1 - b := by linarith
      refine (comb _ _ (1 / (1 - b)) (1 / (1 - b)) hv hKn1 (by positivity) (by positivity) (by
        rw [← add_div, div_lt_one hd]; linarith) 0 (-1) (by norm_num) ?_).elim
      ext i; simp; field_simp; ring
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨m, k, hmk⟩ := mm_mem_span_pair.1 huΛ
  obtain ⟨hn0, hn1, hn2, hn3, hn4, hn5, hn6⟩ := hne
  have huF : u ∈ frontier K := mm_mem_frontier hK hu fun hi ↦ hn0 (hadm _ huΛ hi)
  obtain ⟨a, ha_def⟩ : ∃ a : ℤ, a = m + k := ⟨_, rfl⟩
  have hu' : u = (a : ℝ) • Q₀ + (k : ℝ) • Q₂ := by rw [← hmk, ha_def]; push_cast; module
  have hval : ∀ a' b' : ℤ, a = a' → k = b' → u = (a' : ℝ) • Q₀ + (b' : ℝ) • Q₂ := by
    rintro a' b' rfl rfl; exact hu'
  have e10 : ¬ (a = 1 ∧ k = 0) := fun h ↦ hn1 (by rw [hval 1 0 h.1 h.2]; simp)
  have e01 : ¬ (a = 0 ∧ k = 1) := fun h ↦ hn3 (by rw [hval 0 1 h.1 h.2]; simp)
  have e11 : ¬ (a = 1 ∧ k = 1) := fun h ↦ hn5 (by rw [hval 1 1 h.1 h.2]; simp)
  have f10 : ¬ (a = -1 ∧ k = 0) := fun h ↦ hn2 (by rw [hval (-1) 0 h.1 h.2]; simp)
  have f01 : ¬ (a = 0 ∧ k = -1) := fun h ↦ hn4 (by rw [hval 0 (-1) h.1 h.2]; simp)
  have f11 : ¬ (a = -1 ∧ k = -1) := fun h ↦ hn6 (by
    rw [hval (-1) (-1) h.1 h.2]; push_cast; module)
  have f00 : ¬ (a = 0 ∧ k = 0) := fun h ↦ hn0 (by rw [hval 0 0 h.1 h.2]; simp)
  have hsix : (a = 2 ∧ k = 1) ∨ (a = 1 ∧ k = 2) ∨ (a = 1 ∧ k = -1) ∨ (a = -2 ∧ k = -1) ∨
      (a = -1 ∧ k = -2) ∨ (a = -1 ∧ k = 1) := by
    by_cases hp : 0 < a ∨ (a = 0 ∧ 0 < k)
    · rcases core u a k hu hu' hp e10 e01 e11 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · have hv : -u = ((-a : ℤ) : ℝ) • Q₀ + ((-k : ℤ) : ℝ) • Q₂ := by
        rw [hu']; push_cast; module
      have hp' : 0 < -a ∨ (-a = 0 ∧ 0 < -k) := by omega
      have g10 : ¬ (-a = 1 ∧ -k = 0) := by omega
      have g01 : ¬ (-a = 0 ∧ -k = 1) := by omega
      have g11 : ¬ (-a = 1 ∧ -k = 1) := by omega
      rcases core (-u) (-a) (-k) (hK.2.2.2 u hu) hv hp' g10 g01 g11 with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))
  have hF1 : -(Q₀ + Q₂) ∈ frontier K := mm_neg_mem_frontier hK h1
  have hF0 := mm_neg_mem_frontier hK h0
  have hF2 := mm_neg_mem_frontier hK h2
  rcases hsix with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have hu2 : u = (Q₀ + Q₂) + Q₀ := by rw [hval 2 1 h₁ h₂]; push_cast; module
    refine ⟨Q₀ + Q₂, Q₀, h1, h0, hu2 ▸ huF, by convert h2 using 1; module, hu2, ?_⟩
    rw [show cross (Q₀ + Q₂) Q₀ = -cross Q₀ Q₂ by simp only [cross, Pi.add_apply]; ring, abs_neg]
  · have hu2 : u = (Q₀ + Q₂) + Q₂ := by rw [hval 1 2 h₁ h₂]; push_cast; module
    refine ⟨Q₀ + Q₂, Q₂, h1, h2, hu2 ▸ huF, by convert h0 using 1; module, hu2, ?_⟩
    rw [show cross (Q₀ + Q₂) Q₂ = cross Q₀ Q₂ by simp only [cross, Pi.add_apply]; ring]
  · have hu2 : u = Q₀ + -Q₂ := by rw [hval 1 (-1) h₁ h₂]; push_cast; module
    refine ⟨Q₀, -Q₂, h0, hF2, hu2 ▸ huF, by convert h1 using 1; module, hu2, ?_⟩
    rw [show cross Q₀ (-Q₂) = -cross Q₀ Q₂ by simp only [cross, Pi.neg_apply]; ring, abs_neg]
  · have hu2 : u = -(Q₀ + Q₂) + -Q₀ := by rw [hval (-2) (-1) h₁ h₂]; push_cast; module
    refine ⟨-(Q₀ + Q₂), -Q₀, hF1, hF0, hu2 ▸ huF, by convert hF2 using 1; module, hu2, ?_⟩
    rw [show cross (-(Q₀ + Q₂)) (-Q₀) = -cross Q₀ Q₂ by
      simp only [cross, Pi.add_apply, Pi.neg_apply]; ring, abs_neg]
  · have hu2 : u = -(Q₀ + Q₂) + -Q₂ := by rw [hval (-1) (-2) h₁ h₂]; push_cast; module
    refine ⟨-(Q₀ + Q₂), -Q₂, hF1, hF2, hu2 ▸ huF, by convert hF0 using 1; module, hu2, ?_⟩
    rw [show cross (-(Q₀ + Q₂)) (-Q₂) = cross Q₀ Q₂ by
      simp only [cross, Pi.add_apply, Pi.neg_apply]; ring]
  · have hu2 : u = -Q₀ + Q₂ := by rw [hval (-1) 1 h₁ h₂]; push_cast; module
    refine ⟨-Q₀, Q₂, hF0, h2, hu2 ▸ huF, by convert hF1 using 1; module, hu2, ?_⟩
    rw [show cross (-Q₀) Q₂ = -cross Q₀ Q₂ by simp only [cross, Pi.neg_apply]; ring, abs_neg]

/-- **Mahler, paper A, Lemma 12, for convex subdomains** (the "if" half of Lemma 3): if every
boundary point of `K` lies on a critical lattice of `K`, then `K` is irreducible. Let `K' ⊊ K`
have `Δ(K') = Δ(K)`. A critical lattice `Λ` of `K` through a boundary point `p ∉ K'` is
`K'`-critical, so (Lemma 2 for `K'`) it has points `Q₀, Q₂, Q₀ + Q₂` on the boundary of `K'`,
hence of `K`; then `p` is a vertex `A + B` of a square configuration (`ml3_eight`), an extreme
point of `K` (`ml3_square_extreme`). But the boundary points `A + (1 - ε)B` near `A + B` are also
outside `K'` and are not extreme. -/
lemma ml3_irreducible_of_forall (hK : IsSymmetricConvexDomain K)
    (hall : ∀ u ∈ frontier K, ∃ Λ, IsCritical K Λ ∧ u ∈ Λ) : IsIrreducible K := by
  refine ⟨hK, fun K' hK' hsub hne ↦ lt_of_le_of_ne (ml3_minDet_mono hK hsub) fun hEq ↦ ?_⟩
  have key : ∀ p ∈ frontier K, p ∉ K' → ∃ A B, A ∈ frontier K ∧ B ∈ frontier K ∧
      A + B ∈ frontier K ∧ A - B ∈ frontier K ∧ p = A + B := by
    intro p hp hpK'
    obtain ⟨Λ, hΛ, hpΛ⟩ := hall p hp
    have hΛ' : IsCritical K' Λ :=
      ⟨hΛ.1, fun x hx hxi ↦ hΛ.2.1 x hx (interior_mono hsub hxi), hΛ.2.2.trans hEq.symm⟩
    obtain ⟨Q₀, Q₁, Q₂, h0Λ, h1Λ, h2Λ, h0F, h1F, h2F, hB, h012, -, -⟩ :=
      (minkowski_mahler hK').1 Λ hΛ'
    have toF : ∀ Q ∈ Λ, Q ∈ frontier K' → Q ∈ frontier K := fun Q hQ hQF ↦
      mm_mem_frontier hK (hsub (mm_mem_of_frontier hK' hQF))
        fun hi ↦ mm_ne_zero_of_frontier hK' hQF (hΛ.2.1 Q hQ hi)
    have hK'0 := interior_subset (mm_zero_mem_interior hK')
    have mem : ∀ Q, Q ∈ frontier K' → Q ∈ K' ∧ -Q ∈ K' := fun Q hQ ↦
      ⟨mm_mem_of_frontier hK' hQ, hK'.2.2.2 _ (mm_mem_of_frontier hK' hQ)⟩
    subst h012
    have hne : p ≠ 0 ∧ p ≠ Q₀ ∧ p ≠ -Q₀ ∧ p ≠ Q₂ ∧ p ≠ -Q₂ ∧ p ≠ Q₀ + Q₂ ∧
        p ≠ -(Q₀ + Q₂) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
      · exact hpK' hK'0
      · exact hpK' (mem _ h0F).1
      · exact hpK' (mem _ h0F).2
      · exact hpK' (mem _ h2F).1
      · exact hpK' (mem _ h2F).2
      · exact hpK' (mem _ h1F).1
      · exact hpK' (mem _ h1F).2
    obtain ⟨A, B, h₁, h₂, h₃, h₄, h₅, -⟩ := ml3_eight hK (toF _ h0Λ h0F) (toF _ h2Λ h2F)
      (toF _ h1Λ h1F) (mm_mem_of_frontier hK hp) (by rw [hB.2]; exact hpΛ) hne
    exact ⟨A, B, h₁, h₂, h₃, h₄, h₅⟩
  obtain ⟨u, huF, huK'⟩ := ml3_exists_frontier_notMem hK hK' hsub hne
  obtain ⟨A, B, hA, hB, hAB, hAB', rfl⟩ := key u huF huK'
  have hc : Continuous fun ε : ℝ ↦ A + (1 - ε) • B := by fun_prop
  have hev₀ : (fun ε : ℝ ↦ A + (1 - ε) • B) ⁻¹' K'ᶜ ∈ 𝓝 (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by
      rw [sub_zero, one_smul]; exact hK'.2.1.isClosed.isOpen_compl.mem_nhds huK')
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), A + (1 - ε) • B ∉ K' := hev₀
  obtain ⟨ε, ⟨hεK', hε1⟩, hε0⟩ := (((hev.and (Iio_mem_nhds one_pos)).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hε0' : (0 : ℝ) < ε := hε0
  have hε1' : ε < 1 := hε1
  have hABK := mm_mem_of_frontier hK hAB
  have hABK' := mm_mem_of_frontier hK hAB'
  obtain ⟨f, hf1, hf2, hf3⟩ := mm_support hK hA
  have hfB := ml3_square_supp hABK hABK' f hf1 hf2
  have hpK : A + (1 - ε) • B ∈ K := by
    have := hK.1 hABK hABK' (show (0 : ℝ) ≤ 1 - ε / 2 by linarith)
      (show (0 : ℝ) ≤ ε / 2 by linarith) (by ring)
    convert this using 1; module
  have hpF : A + (1 - ε) • B ∈ frontier K := mm_mem_frontier hK hpK fun hi ↦ by
    have := hf3 _ hi
    simp only [map_add, map_smul, hf1, hfB, smul_eq_mul, mul_zero, add_zero] at this
    exact lt_irrefl _ this
  obtain ⟨A', B', hA', hB', hAB₁, hAB₁', hp⟩ := key _ hpF hεK'
  have hyK : A + (1 - 2 * ε) • B ∈ K := by
    have := hK.1 hABK hABK' (show (0 : ℝ) ≤ 1 - ε by linarith) hε0'.le (by ring)
    convert this using 1; module
  have hx := ml3_square_extreme hK hA' hB' hAB₁ hAB₁' hABK hyK (by rw [← hp]; module)
  rw [← hp] at hx
  have : ε • B = 0 := by
    rw [show ε • B = (A + B) - (A + (1 - ε) • B) by module, hx, sub_self]
  exact mm_ne_zero_of_frontier hK hB ((smul_eq_zero.1 this).resolve_left hε0'.ne')

/-! ### Functionals and partners -/

/-- The functional `x ↦ det(v, x)`. -/
noncomputable def ml3_crossL (v : Fin 2 → ℝ) : StrongDual ℝ (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ cross v x
      map_add' := fun x y ↦ by simp only [cross, Pi.add_apply]; ring
      map_smul' := fun c x ↦ by
        simp only [cross, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

lemma ml3_crossL_apply (v x : Fin 2 → ℝ) : ml3_crossL v x = cross v x := rfl

/-- A nonzero functional `≤ c` on `K` is `< c` on the interior of `K`. -/
lemma ml3_lt_of_interior (ψ : StrongDual ℝ (Fin 2 → ℝ)) {c : ℝ} (hψ : ∀ y ∈ K, ψ y ≤ c)
    {v : Fin 2 → ℝ} (hv : ψ v ≠ 0) {y : Fin 2 → ℝ} (hy : y ∈ interior K) : ψ y < c := by
  obtain ⟨a, ha⟩ := ml3_dual_vec ψ
  have ha0 : a ≠ 0 := by rintro rfl; apply hv; rw [← ha]; simp
  have := irr_dot_lt ha0 (M := c) (fun x hx ↦ (ha x).trans_le (hψ x hx)) hy
  rwa [ha] at this

/-- The critical lattice through a boundary point `Z` gives a pair `W, W - Z` of boundary points
with `|det(Z, W)| = Δ(K)` (Mahler's Lemma 2 and `ml3_eight`). -/
lemma ml3_pair (hK : IsSymmetricConvexDomain K) {Λ : Submodule ℤ (Fin 2 → ℝ)}
    (hΛ : IsCritical K Λ) {Z : Fin 2 → ℝ} (hZ : Z ∈ Λ) (hZF : Z ∈ frontier K) :
    ∃ W, W ∈ frontier K ∧ W - Z ∈ frontier K ∧ |cross Z W| = minimalDeterminant K := by
  obtain ⟨P₀, P₁, P₂, h0Λ, h1Λ, h2Λ, h0F, h1F, h2F, hB, h012, -, hdet⟩ :=
    (minkowski_mahler hK).1 Λ hΛ
  subst h012
  have c1 : |cross P₀ P₂| = minimalDeterminant K := by
    rw [← hdet]; congr 1; simp only [cross, Pi.add_apply]; ring
  have n0 := mm_neg_mem_frontier hK h0F
  have n1 := mm_neg_mem_frontier hK h1F
  have n2 := mm_neg_mem_frontier hK h2F
  have ab : ∀ x y : Fin 2 → ℝ, cross x y = cross P₀ P₂ ∨ cross x y = -cross P₀ P₂ →
      |cross x y| = minimalDeterminant K := by
    rintro x y (h | h) <;> rw [h] <;> simp [c1]
  by_cases e0 : Z = P₀
  · rw [e0]
    exact ⟨_, h1F, by simpa using h2F, ab _ _ (Or.inl (by simp only [cross, Pi.add_apply]; ring))⟩
  by_cases e1 : Z = -P₀
  · rw [e1]
    exact ⟨-(P₀ + P₂), n1, by convert n2 using 1; abel,
      ab _ _ (Or.inl (by simp only [cross, Pi.add_apply, Pi.neg_apply]; ring))⟩
  by_cases e2 : Z = P₀ + P₂
  · rw [e2]
    exact ⟨P₀, h0F, by convert n2 using 1; abel,
      ab _ _ (Or.inr (by simp only [cross, Pi.add_apply]; ring))⟩
  by_cases e3 : Z = -(P₀ + P₂)
  · rw [e3]
    exact ⟨-P₀, n0, by convert h2F using 1; abel,
      ab _ _ (Or.inr (by simp only [cross, Pi.add_apply, Pi.neg_apply]; ring))⟩
  by_cases e4 : Z = P₂
  · rw [e4]
    exact ⟨P₀ + P₂, h1F, by convert h0F using 1; abel,
      ab _ _ (Or.inr (by simp only [cross, Pi.add_apply]; ring))⟩
  by_cases e5 : Z = -P₂
  · rw [e5]
    exact ⟨-(P₀ + P₂), n1, by convert n0 using 1; abel,
      ab _ _ (Or.inr (by simp only [cross, Pi.add_apply, Pi.neg_apply]; ring))⟩
  have hZ0 : Z ≠ 0 := mm_ne_zero_of_frontier hK hZF
  obtain ⟨A, B, hA, hB', hAB, hAB', hZAB, hcr⟩ := ml3_eight hK h0F h2F h1F
    (mm_mem_of_frontier hK hZF) (by rw [hB.2]; exact hZ) ⟨hZ0, e0, e1, e4, e5, e2, e3⟩
  refine ⟨A, hA, ?_, ?_⟩
  · rw [hZAB, show A - (A + B) = -B by abel]; exact mm_neg_mem_frontier hK hB'
  · rw [hZAB, ← c1, ← hcr, show cross (A + B) A = -cross A B by
      simp only [cross, Pi.add_apply]; ring, abs_neg]


/-! ### Parallelograms (Mahler, paper A, §1) -/

/-- A parallelogram with centre `O`: the points `s a + t b`, `|s|, |t| ≤ 1`, for linearly
independent `a, b` (its vertices are `±a ± b`). -/
def IsParallelogram (K : Set (Fin 2 → ℝ)) : Prop :=
  ∃ a b : Fin 2 → ℝ, cross a b ≠ 0 ∧ K = {x | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • a + t • b}

/-- The parallelogram with vertices `±a ± b` in coordinates:
`|det(x, b)|, |det(a, x)| ≤ |det(a, b)|`. -/
lemma ml5_par_mem {a b : Fin 2 → ℝ} (h : cross a b ≠ 0) (x : Fin 2 → ℝ) :
    (∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • a + t • b) ↔
      |cross x b| ≤ |cross a b| ∧ |cross a x| ≤ |cross a b| := by
  have hab : 0 < |cross a b| := abs_pos.2 h
  constructor
  · rintro ⟨s, t, hs, ht, rfl⟩
    rw [mm_cross_smul_add, mm_cross_add_smul, mm_cross_self, mm_cross_self, mul_zero, add_zero,
      mul_zero, zero_add, abs_mul, abs_mul]
    exact ⟨mul_le_of_le_one_left hab.le hs, mul_le_of_le_one_left hab.le ht⟩
  · rintro ⟨h1, h2⟩
    refine ⟨_, _, ?_, ?_, mm_eq_comb h x⟩
    · rw [abs_div, div_le_one hab]; exact h1
    · rw [abs_div, div_le_one hab]; exact h2

lemma ml5_cross_neg_left (u v : Fin 2 → ℝ) : cross (-u) v = -cross u v := by
  simp only [cross, Pi.neg_apply]; ring

lemma ml5_cross_neg_right (u v : Fin 2 → ℝ) : cross u (-v) = -cross u v := by
  simp only [cross, Pi.neg_apply]; ring

/-- A nonzero functional `x ↦ det(x, b)` bounded by `D` on `K` is `< D` on the interior. -/
lemma ml5_cross_lt_of_interior {b : Fin 2 → ℝ} {D : ℝ} (hb : b ≠ 0)
    (hK : ∀ y ∈ K, cross y b ≤ D) {x : Fin 2 → ℝ} (hx : x ∈ interior K) : cross x b < D := by
  have hv : ∃ v, cross v b ≠ 0 := by
    by_contra h; push Not at h
    apply hb; ext i
    have h0 := h (Pi.single 0 1)
    have h1 := h (Pi.single 1 1)
    simp [cross] at h0 h1
    fin_cases i <;> simp [h0, h1]
  obtain ⟨v, hv⟩ := hv
  have := ml3_lt_of_interior (-ml3_crossL b) (c := D)
    (fun y hy ↦ by simpa [ml3_crossL_apply, mm_cross_swap b y] using hK y hy) (v := v)
    (by simpa [ml3_crossL_apply, mm_cross_swap b v] using hv) hx
  simpa [ml3_crossL_apply, mm_cross_swap b x] using this

section Par

variable {a b : Fin 2 → ℝ}

/-- Interior points of the parallelogram have both coordinates of absolute value `< 1`. -/
lemma ml5_par_interior (hab : cross a b ≠ 0)
    (hmem : ∀ x, x ∈ K ↔ |cross x b| ≤ |cross a b| ∧ |cross a x| ≤ |cross a b|) {x : Fin 2 → ℝ}
    (hx : x ∈ interior K) : |cross x b| < |cross a b| ∧ |cross a x| < |cross a b| := by
  have hb : b ≠ 0 := by rintro rfl; simp [cross] at hab
  have ha : a ≠ 0 := by rintro rfl; simp [cross] at hab
  have hb' : -b ≠ 0 := neg_ne_zero.2 hb
  have ha' : a ≠ 0 := ha
  -- the functionals `±det(·, b)` and `±det(a, ·) = ∓det(·, a)`
  have h1 := ml5_cross_lt_of_interior hb (D := |cross a b|)
    (fun y hy ↦ (le_abs_self _).trans ((hmem y).1 hy).1) hx
  have h2 := ml5_cross_lt_of_interior hb' (D := |cross a b|)
    (fun y hy ↦ by rw [ml5_cross_neg_right]; exact (neg_le_abs _).trans ((hmem y).1 hy).1) hx
  have h3 := ml5_cross_lt_of_interior (b := a) ha (D := |cross a b|)
    (fun y hy ↦ by rw [mm_cross_swap]; exact (neg_le_abs _).trans ((hmem y).1 hy).2) hx
  have h4 := ml5_cross_lt_of_interior (b := -a) (neg_ne_zero.2 ha) (D := |cross a b|)
    (fun y hy ↦ by
      rw [ml5_cross_neg_right, mm_cross_swap, neg_neg]
      exact (le_abs_self _).trans ((hmem y).1 hy).2) hx
  rw [ml5_cross_neg_right] at h2
  rw [ml5_cross_neg_right, mm_cross_swap, neg_neg] at h4
  rw [mm_cross_swap] at h3
  exact ⟨abs_lt.2 ⟨by linarith, h1⟩, abs_lt.2 ⟨by linarith, h4⟩⟩

/-- A boundary point of the parallelogram lies on a side. -/
lemma ml5_par_frontier (hmem : ∀ x, x ∈ K ↔ |cross x b| ≤ |cross a b| ∧ |cross a x| ≤ |cross a b|)
    {x : Fin 2 → ℝ} (hx : x ∈ frontier K) :
    |cross x b| = |cross a b| ∨ |cross a x| = |cross a b| := by
  by_contra h
  push Not at h
  apply hx.2
  have hcl : x ∈ K := by
    have := frontier_subset_closure hx
    have hc : IsClosed K := by
      have : K = {x | |cross x b| ≤ |cross a b| ∧ |cross a x| ≤ |cross a b|} := Set.ext hmem
      rw [this]
      exact (isClosed_le (ml5_continuous_cross_left b).abs continuous_const).inter
        (isClosed_le (ml5_continuous_cross_right a).abs continuous_const)
    exact hc.closure_subset this
  obtain ⟨h1, h2⟩ := (hmem x).1 hcl
  refine interior_maximal (t := {y | |cross y b| < |cross a b| ∧ |cross a y| < |cross a b|})
    (fun y hy ↦ (hmem y).2 ⟨hy.1.le, hy.2.le⟩)
    ((isOpen_lt (ml5_continuous_cross_left b).abs continuous_const).inter
      (isOpen_lt (ml5_continuous_cross_right a).abs continuous_const))
    ⟨lt_of_le_of_ne h1 h.1, lt_of_le_of_ne h2 h.2⟩

/-- A point of the parallelogram on a side is a boundary point. -/
lemma ml5_par_mem_frontier (hKd : IsSymmetricConvexDomain K) (hab : cross a b ≠ 0)
    (hmem : ∀ x, x ∈ K ↔ |cross x b| ≤ |cross a b| ∧ |cross a x| ≤ |cross a b|) {x : Fin 2 → ℝ}
    (hx : x ∈ K) (h : |cross x b| = |cross a b| ∨ |cross a x| = |cross a b|) : x ∈ frontier K :=
  mm_mem_frontier hKd hx fun hi ↦ by
    have := ml5_par_interior hab hmem hi
    rcases h with h | h <;> linarith [this.1, this.2]

/-- The coordinate description is invariant under the symmetries `(a, b) ↦ (-a, -b), (b, -a)`. -/
lemma ml5_par_mem_neg (hmem : ∀ x, x ∈ K ↔ |cross x b| ≤ |cross a b| ∧ |cross a x| ≤ |cross a b|)
    (x : Fin 2 → ℝ) :
    x ∈ K ↔ |cross x (-b)| ≤ |cross (-a) (-b)| ∧ |cross (-a) x| ≤ |cross (-a) (-b)| := by
  rw [ml5_cross_neg_right, ml5_cross_neg_left, ml5_cross_neg_right, ml5_cross_neg_left, neg_neg,
    abs_neg, abs_neg, hmem]

lemma ml5_par_mem_rot (hmem : ∀ x, x ∈ K ↔ |cross x b| ≤ |cross a b| ∧ |cross a x| ≤ |cross a b|)
    (x : Fin 2 → ℝ) : x ∈ K ↔ |cross x (-a)| ≤ |cross b (-a)| ∧ |cross b x| ≤ |cross b (-a)| := by
  have e1 : |cross x (-a)| = |cross a x| := by rw [ml5_cross_neg_right, mm_cross_swap a x, neg_neg]
  have e2 : |cross b (-a)| = |cross a b| := by rw [ml5_cross_neg_right, mm_cross_swap a b, neg_neg]
  have e3 : |cross b x| = |cross x b| := by rw [mm_cross_swap x b, abs_neg]
  rw [e1, e2, e3, hmem, and_comm]

/-- **Mahler's example, paper A, §2** (one side of the parallelogram): the boundary point
`P₁ = a + t b`, `|t| ≤ 1`, has the partner `P₂ = b` if `t ≥ 0` and `P₂ = a + (1 + t) b` if `t ≤ 0`
(`P₂, P₂ - P₁` boundary points, `det(P₁, P₂) = det(a, b)`). -/
lemma ml5_par_partner_side (hKd : IsSymmetricConvexDomain K) (hab : cross a b ≠ 0)
    (hmem : ∀ x, x ∈ K ↔ |cross x b| ≤ |cross a b| ∧ |cross a x| ≤ |cross a b|) {t : ℝ}
    (ht : |t| ≤ 1) : ∃ W, W ∈ frontier K ∧ W - (a + t • b) ∈ frontier K ∧
      cross (a + t • b) W = cross a b := by
  have hD : 0 < |cross a b| := abs_pos.2 hab
  have fr : ∀ {x : Fin 2 → ℝ}, x ∈ K → (|cross x b| = |cross a b| ∨ |cross a x| = |cross a b|) →
      x ∈ frontier K := fun hx h ↦ ml5_par_mem_frontier hKd hab hmem hx h
  have c1 : ∀ c d : ℝ, cross (c • a + d • b) b = c * cross a b := fun c d ↦ by
    rw [mm_cross_smul_add, mm_cross_self]; ring
  have c2 : ∀ c d : ℝ, cross a (c • a + d • b) = d * cross a b := fun c d ↦ by
    rw [mm_cross_add_smul, mm_cross_self]; ring
  have mem : ∀ c d : ℝ, |c| ≤ 1 → |d| ≤ 1 → c • a + d • b ∈ K := fun c d hc hd ↦ by
    rw [hmem, c1, c2, abs_mul, abs_mul]
    exact ⟨mul_le_of_le_one_left hD.le hc, mul_le_of_le_one_left hD.le hd⟩
  rcases le_total 0 t with h0 | h0
  · refine ⟨(0 : ℝ) • a + (1 : ℝ) • b, fr (mem 0 1 (by simp) (by simp))
      (Or.inr (by rw [c2, one_mul])), ?_, ?_⟩
    · have e : (0 : ℝ) • a + (1 : ℝ) • b - (a + t • b) = (-1 : ℝ) • a + (1 - t) • b := by module
      rw [e]
      refine fr (mem _ _ (by simp) (by rw [abs_le] at ht ⊢; constructor <;> linarith))
        (Or.inl (by rw [c1, abs_mul]; simp))
    · rw [show a + t • b = (1 : ℝ) • a + t • b by rw [one_smul], mm_cross_comb]; ring
  · refine ⟨(1 : ℝ) • a + (1 + t) • b, fr (mem 1 _ (by simp)
      (by rw [abs_le] at ht ⊢; constructor <;> linarith)) (Or.inl (by rw [c1, one_mul])), ?_, ?_⟩
    · have e : (1 : ℝ) • a + (1 + t) • b - (a + t • b) = (0 : ℝ) • a + (1 : ℝ) • b := by module
      rw [e]
      exact fr (mem 0 1 (by simp) (by simp)) (Or.inr (by rw [c2, one_mul]))
    · rw [show a + t • b = (1 : ℝ) • a + t • b by rw [one_smul], mm_cross_comb]; ring

/-- **Mahler's example, paper A, §2**: every boundary point `P₁` of a parallelogram has a partner
`P₂` (`P₂, P₂ - P₁` boundary points) with `|det(P₁, P₂)| = |det(a, b)|`. -/
lemma ml5_par_partner (hKd : IsSymmetricConvexDomain K) (hab : cross a b ≠ 0)
    (hmem : ∀ x, x ∈ K ↔ |cross x b| ≤ |cross a b| ∧ |cross a x| ≤ |cross a b|) {u : Fin 2 → ℝ}
    (hu : u ∈ frontier K) :
    ∃ W, W ∈ frontier K ∧ W - u ∈ frontier K ∧ |cross u W| = |cross a b| := by
  have hD : 0 < |cross a b| := abs_pos.2 hab
  obtain ⟨hs, ht⟩ := (hmem u).1 (mm_mem_of_frontier hKd hu)
  have hdec := mm_eq_comb hab u
  set s := cross u b / cross a b with hsdef
  set t := cross a u / cross a b with htdef
  have hs1 : |s| ≤ 1 := by rw [hsdef, abs_div, div_le_one hD]; exact hs
  have ht1 : |t| ≤ 1 := by rw [htdef, abs_div, div_le_one hD]; exact ht
  have hab' : cross a b ≠ 0 := hab
  rcases ml5_par_frontier hmem hu with h | h
  · have hs' : |s| = 1 := by rw [hsdef, abs_div, h, div_self hD.ne']
    rcases (abs_eq zero_le_one).1 hs' with e | e
    · -- the side `a + t b`
      obtain ⟨W, h1, h2, h3⟩ := ml5_par_partner_side hKd hab hmem ht1
      refine ⟨W, h1, ?_, ?_⟩ <;> rw [hdec, e, one_smul]
      · exact h2
      · rw [h3]
    · -- the side `-a - t b = (-a) + t (-b)`
      have hab2 : cross (-a) (-b) ≠ 0 := by
        rw [ml5_cross_neg_left, ml5_cross_neg_right, neg_neg]; exact hab
      obtain ⟨W, h1, h2, h3⟩ := ml5_par_partner_side (t := -t) hKd hab2 (ml5_par_mem_neg hmem)
        (by rw [abs_neg]; exact ht1)
      have eu : u = -a + (-t) • (-b) := by rw [hdec, e]; module
      refine ⟨W, h1, by rw [eu]; exact h2, ?_⟩
      rw [eu, h3, ml5_cross_neg_left, ml5_cross_neg_right, neg_neg]
  · have ht' : |t| = 1 := by rw [htdef, abs_div, h, div_self hD.ne']
    have hab2 : cross b (-a) ≠ 0 := by rw [ml5_cross_neg_right, mm_cross_swap, neg_neg]; exact hab
    have hrot := ml5_par_mem_rot hmem
    rcases (abs_eq zero_le_one).1 ht' with e | e
    · -- the side `b + s a = b + (-s) (-a)`
      obtain ⟨W, h1, h2, h3⟩ := ml5_par_partner_side (t := -s) hKd hab2 hrot
        (by rw [abs_neg]; exact hs1)
      have eu : u = b + (-s) • (-a) := by rw [hdec, e]; module
      refine ⟨W, h1, by rw [eu]; exact h2, ?_⟩
      rw [eu, h3, ml5_cross_neg_right, mm_cross_swap, neg_neg]
    · -- the side `-b + s a`, by symmetry from `b - s a`
      obtain ⟨W, h1, h2, h3⟩ := ml5_par_partner_side (t := s) hKd hab2 hrot hs1
      have eu : u = -(b + s • (-a)) := by rw [hdec, e]; module
      refine ⟨-W, mm_neg_mem_frontier hKd h1, ?_, ?_⟩
      · rw [eu, show -W - -(b + s • (-a)) = -(W - (b + s • (-a))) by abel]
        exact mm_neg_mem_frontier hKd h2
      · rw [eu, ml5_cross_neg_left, ml5_cross_neg_right, neg_neg, h3, ml5_cross_neg_right,
          mm_cross_swap, neg_neg]

/-- A parallelogram is a symmetric convex domain. -/
lemma ml5_par_domain (hpar : IsParallelogram K) : IsSymmetricConvexDomain K := by
  obtain ⟨a, b, hab, rfl⟩ := hpar
  have hD : 0 < |cross a b| := abs_pos.2 hab
  have hset : {x | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • a + t • b} =
      (fun p : ℝ × ℝ ↦ p.1 • a + p.2 • b) '' (Icc (-1) 1 ×ˢ Icc (-1) 1) := by
    ext x
    simp only [mem_ofPred_eq, mem_image, mem_prod, mem_Icc, Prod.exists, abs_le]
    constructor
    · rintro ⟨s, t, hs, ht, rfl⟩; exact ⟨s, t, ⟨hs, ht⟩, rfl⟩
    · rintro ⟨s, t, ⟨hs, ht⟩, rfl⟩; exact ⟨s, t, hs, ht, rfl⟩
  have hdet : {x | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • a + t • b} =
      {x | |cross x b| ≤ |cross a b| ∧ |cross a x| ≤ |cross a b|} := Set.ext (ml5_par_mem hab)
  refine ⟨?_, ?_, ⟨0, ?_⟩, ?_⟩
  · rw [hdet]
    intro x hx y hy p q hp hq hpq
    simp only [mem_ofPred_eq] at hx hy ⊢
    rw [mm_cross_smul_add, mm_cross_add_smul]
    constructor
    · calc |p * cross x b + q * cross y b| ≤ p * |cross x b| + q * |cross y b| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
        _ ≤ p * |cross a b| + q * |cross a b| :=
          add_le_add (mul_le_mul_of_nonneg_left hx.1 hp) (mul_le_mul_of_nonneg_left hy.1 hq)
        _ = |cross a b| := by rw [← add_mul, hpq, one_mul]
    · calc |p * cross a x + q * cross a y| ≤ p * |cross a x| + q * |cross a y| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
        _ ≤ p * |cross a b| + q * |cross a b| :=
          add_le_add (mul_le_mul_of_nonneg_left hx.2 hp) (mul_le_mul_of_nonneg_left hy.2 hq)
        _ = |cross a b| := by rw [← add_mul, hpq, one_mul]
  · rw [hset]
    exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  · rw [hdet]
    refine interior_maximal (t := {y | |cross y b| < |cross a b| ∧ |cross a y| < |cross a b|})
      (fun y hy ↦ by simp only [mem_ofPred_eq] at hy ⊢; exact ⟨hy.1.le, hy.2.le⟩)
      ((isOpen_lt (ml5_continuous_cross_left b).abs continuous_const).inter
        (isOpen_lt (ml5_continuous_cross_right a).abs continuous_const)) ?_
    simp only [mem_ofPred_eq, cross, Pi.zero_apply, zero_mul, mul_zero, sub_zero, abs_zero]
    exact ⟨hD, hD⟩
  · rintro x ⟨s, t, hs, ht, rfl⟩
    exact ⟨-s, -t, by rwa [abs_neg], by rwa [abs_neg], by module⟩

/-- **`Δ` of a parallelogram** (paper A, §1: "by Minkowski's theorem on linear forms,
`Δ(K₀) = 1`"): the minimal determinant of the parallelogram with vertices `±a ± b` is
`|det(a, b)|`. We obtain it, instead of from Minkowski's theorem, from Mahler's own example in §2
and Lemma 3: a critical lattice has three boundary points `P₀, P₂, P₀ + P₂` with
`|det(P₀, P₀ + P₂)| = Δ`, and `A(P₀) = |det(a, b)|` for every boundary point `P₀`
(`ml5_par_partner`, and Lemma 2, `ml3_width_abs`). -/
lemma ml5_par_minDet (hKd : IsSymmetricConvexDomain K) (hab : cross a b ≠ 0)
    (hmem : ∀ x, x ∈ K ↔ |cross x b| ≤ |cross a b| ∧ |cross a x| ≤ |cross a b|) :
    minimalDeterminant K = |cross a b| := by
  have hD : 0 < |cross a b| := abs_pos.2 hab
  have fr : ∀ {x : Fin 2 → ℝ}, x ∈ K → (|cross x b| = |cross a b| ∨ |cross a x| = |cross a b|) →
      x ∈ frontier K := fun hx h ↦ ml5_par_mem_frontier hKd hab hmem hx h
  have c1 : ∀ c d : ℝ, cross (c • a + d • b) b = c * cross a b := fun c d ↦ by
    rw [mm_cross_smul_add, mm_cross_self]; ring
  have c2 : ∀ c d : ℝ, cross a (c • a + d • b) = d * cross a b := fun c d ↦ by
    rw [mm_cross_add_smul, mm_cross_self]; ring
  have mem : ∀ c d : ℝ, |c| ≤ 1 → |d| ≤ 1 → c • a + d • b ∈ K := fun c d hc hd ↦ by
    rw [hmem, c1, c2, abs_mul, abs_mul]
    exact ⟨mul_le_of_le_one_left hD.le hc, mul_le_of_le_one_left hD.le hd⟩
  have ea : a = (1 : ℝ) • a + (0 : ℝ) • b := by module
  have eb : b = (0 : ℝ) • a + (1 : ℝ) • b := by module
  have eab : a + b = (1 : ℝ) • a + (1 : ℝ) • b := by module
  have haF : a ∈ frontier K := by
    rw [ea]; exact fr (mem 1 0 (by simp) (by simp)) (Or.inl (by rw [c1, one_mul]))
  have hbF : b ∈ frontier K := by
    rw [eb]; exact fr (mem 0 1 (by simp) (by simp)) (Or.inr (by rw [c2, one_mul]))
  have habF : a + b ∈ frontier K := by
    rw [eab]; exact fr (mem 1 1 (by simp) (by simp)) (Or.inl (by rw [c1, one_mul]))
  refine le_antisymm ?_ ?_
  · obtain ⟨hle, -⟩ := (minkowski_mahler hKd).2 a (a + b) b haF habF hbF rfl
    have hc : cross a (a + b) = cross a b := by
      rw [show a + b = (1 : ℝ) • a + (1 : ℝ) • b by module, c2, one_mul]
    rw [hc] at hle
    exact hle
  · obtain ⟨Λ, hΛ⟩ := irr_exists_critical hKd
    obtain ⟨P₀, P₁, P₂, -, -, -, h0F, h1F, h2F, -, h012, -, hdet⟩ := (minkowski_mahler hKd).1 Λ hΛ
    have hΔ := irr_minimalDeterminant_pos hKd
    obtain ⟨W, hW, hWu, hWabs⟩ := ml5_par_partner hKd hab hmem h0F
    have h1 : cross P₀ P₁ ≠ 0 := by intro h; rw [h, abs_zero] at hdet; linarith
    have h2 : cross P₀ W ≠ 0 := by intro h; rw [h, abs_zero] at hWabs; linarith
    have heq := ml3_width_abs hKd (mm_mem_of_frontier hKd h0F) h1F
      (by rw [h012, add_sub_cancel_left]; exact h2F) hW hWu h1 h2
    rw [← hdet, heq, hWabs]

end Par

/-- **Mahler's example, paper A, §3** (with Lemma 4): for a parallelogram `Π = C`, every boundary
point lies on a critical lattice. -/
lemma ml5_par_pi (hpar : IsParallelogram K) {u : Fin 2 → ℝ} (hu : u ∈ frontier K) :
    ∃ Λ, IsCritical K Λ ∧ u ∈ Λ := by
  have hKd := ml5_par_domain hpar
  obtain ⟨a, b, hab, hK⟩ := hpar
  have hmem : ∀ x, x ∈ K ↔ |cross x b| ≤ |cross a b| ∧ |cross a x| ≤ |cross a b| := fun x ↦ by
    rw [hK]; exact ml5_par_mem hab x
  obtain ⟨W, hW, hWu, hWabs⟩ := ml5_par_partner hKd hab hmem hu
  obtain ⟨-, h⟩ := (minkowski_mahler hKd).2 (W - u) W u hWu hW hu (by abel)
  have hc : |cross (W - u) W| = minimalDeterminant K := by
    rw [ml5_par_minDet hKd hab hmem, ← hWabs, show cross (W - u) W = -cross u W by
      simp only [cross, Pi.sub_apply]; ring, abs_neg]
  refine ⟨_, h.1 hc, ?_⟩
  rw [show u = W - (W - u) by abel]
  exact Submodule.sub_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))

/-! ### Mahler's Lemma 1 of paper A -/

/-- The integer step of Lemma 1: with `0 < θ, ξ < 1`, a point `m P₁ + k P₂` of the lattice of
basis `P₁ = (θξ, θ)`, `P₂ = (1, θ - 1)` inside the square has `k = 0`. -/
lemma ml5_lemma1_int {θ ξ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (m k : ℤ)
    (h1 : |(m : ℝ) * θ * ξ + k| < 1) (h2 : |(m : ℝ) * θ + k * (θ - 1)| < 1) : k = 0 := by
  have key : ∀ m k : ℤ, 1 ≤ k → |(m : ℝ) * θ * ξ + k| < 1 →
      |(m : ℝ) * θ + k * (θ - 1)| < 1 → False := by
    intro m k hk h1 h2
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [abs_lt] at h1 h2
    rcases le_or_gt (m + k) 0 with h | h
    · have h' : ((m : ℝ) + k) ≤ 0 := by exact_mod_cast h
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hθ0.le h']
    · have h' : (1 : ℝ) - k ≤ m := by
        have : 1 - k ≤ m := by omega
        exact_mod_cast this
      have hθξ : θ * ξ ≤ 1 := by nlinarith
      have e1 : (1 - (k : ℝ)) * (θ * ξ) ≤ (m : ℝ) * (θ * ξ) :=
        mul_le_mul_of_nonneg_right h' (by positivity)
      have e2 : (1 - (k : ℝ)) ≤ (1 - (k : ℝ)) * (θ * ξ) := by nlinarith
      nlinarith
  rcases lt_trichotomy k 0 with hk | hk | hk
  · exact (key (-m) (-k) (by omega)
      (by push_cast; rw [show -(m : ℝ) * θ * ξ + -k = -((m : ℝ) * θ * ξ + k) by ring, abs_neg]
          exact h1)
      (by push_cast; rw [show -(m : ℝ) * θ + -(k : ℝ) * (θ - 1) = -((m : ℝ) * θ + k * (θ - 1)) by
            ring, abs_neg]
          exact h2)).elim
  · exact hk
  · exact (key m k (by omega) h1 h2).elim

/-- **Mahler's proof of Lemma 1**, in the coordinates `x = s a + t b` of the parallelogram
`K₀ = {|s|, |t| ≤ 1}` (instead of reducing to the unit square by an affine map). Let `H` be a
symmetric convex domain in `K₀` (`hint`: its inner points are inner points of `K₀`) missing the
boundary point `P₀ = ξ a + b`, `0 < ξ < 1`. Let `θ P₀` (`0 < θ < 1`) be the boundary point of `H`
on the ray of `P₀`, and `Λ₀` the lattice of basis `P₁ = θ P₀`, `P₂ = a + (θ - 1) b`, of
determinant `(1 - (1 - θ)(1 - θξ)) |det(a, b)| < |det(a, b)|`. Then `Λ₀` is `H`-admissible, so
`Δ(H) < |det(a, b)|`.

Gap in paper A (filled here): Mahler says that `±θ P₀` are the only points of `Λ₀` which are inner
points of `K₀`. This holds only for `θ ≥ 1/2`: for `θ < 1/2` the multiples `m θ P₀`,
`2 ≤ |m| < 1/θ`, are inner points of `K₀` too. The argument survives: the points of `Λ₀` inside
`K₀` are the multiples of `θ P₀` (`ml5_lemma1_int`), and those other than `O` are not inner points
of `H`, since `θ P₀` is a boundary point of the convex domain `H`. -/
lemma ml5_lemma1_core {H : Set (Fin 2 → ℝ)} (hH : IsSymmetricConvexDomain H) {a b : Fin 2 → ℝ}
    (hab : cross a b ≠ 0)
    (hint : ∀ x ∈ interior H, |cross x b| < |cross a b| ∧ |cross a x| < |cross a b|)
    {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hP : ξ • a + b ∉ H) :
    minimalDeterminant H < |cross a b| := by
  have hD : 0 < |cross a b| := abs_pos.2 hab
  set P₀ := ξ • a + b with hP₀
  have hcl := hH.2.1.isClosed
  have h0 := mm_zero_mem_interior hH
  -- `θ`: `θ P₀` is the boundary point of `H` on the ray of `P₀`
  set T := {τ : ℝ | τ ∈ Icc (0 : ℝ) 1 ∧ τ • P₀ ∈ H} with hT
  have hc : Continuous fun τ : ℝ ↦ τ • P₀ := by fun_prop
  have hTc : IsClosed T := isClosed_Icc.inter (hcl.preimage hc)
  have hT0 : (0 : ℝ) ∈ T := ⟨⟨le_rfl, zero_le_one⟩, by rw [zero_smul]; exact interior_subset h0⟩
  have hTb : BddAbove T := ⟨1, fun τ hτ ↦ hτ.1.2⟩
  set θ := sSup T with hθ
  have hθT : θ ∈ T := hTc.csSup_mem ⟨0, hT0⟩ hTb
  have hθ1 : θ < 1 := lt_of_le_of_ne hθT.1.2 fun h ↦ hP (by
    have := hθT.2; rwa [h, one_smul] at this)
  have hθ0 : 0 < θ := by
    have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), τ • P₀ ∈ H := hc.continuousAt.preimage_mem_nhds
      (by rw [zero_smul]; exact mem_interior_iff_mem_nhds.1 h0)
    obtain ⟨τ, ⟨hτH, hτ1⟩, hτ0⟩ := (((hev.and (Iio_mem_nhds one_pos)).filter_mono
      nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
    exact lt_of_lt_of_le hτ0 (le_csSup hTb ⟨⟨le_of_lt hτ0, le_of_lt hτ1⟩, hτH⟩)
  have hθi : θ • P₀ ∉ interior H := by
    intro hi
    have hev : ∀ᶠ τ in 𝓝 θ, τ • P₀ ∈ H :=
      hc.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.1 hi)
    obtain ⟨τ, ⟨hτH, hτ1⟩, hτθ⟩ := (((hev.and (Iio_mem_nhds hθ1)).filter_mono
      nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Ioi θ ∈ 𝓝[>] θ)).exists
    have hτθ' : θ < τ := hτθ
    have := le_csSup hTb ⟨⟨by linarith, le_of_lt hτ1⟩, hτH⟩
    linarith
  -- the multiples `m θ P₀`, `m ≠ 0`, are not inner points of `H`
  have hmult : ∀ m : ℤ, m ≠ 0 → ((m : ℝ) * θ) • P₀ ∉ interior H := by
    have pos : ∀ m : ℤ, 1 ≤ m → ((m : ℝ) * θ) • P₀ ∉ interior H := by
      intro m hm hi
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      apply hθi
      rcases hm'.lt_or_eq with h | h
      · have := mm_smul_mem_interior hH (interior_subset hi) (t := 1 / m) (by positivity)
          (by rw [div_lt_one (by linarith)]; exact h)
        rwa [smul_smul, show 1 / (m : ℝ) * (m * θ) = θ by field_simp] at this
      · rwa [← h, one_mul] at hi
    intro m hm hi
    rcases lt_or_gt_of_ne hm with h | h
    · refine pos (-m) (by omega) ?_
      have := mm_neg_mem_interior hH hi
      convert this using 1
      push_cast; rw [neg_mul, neg_smul]
    · exact pos m (by omega) hi
  -- the lattice `Λ₀` with basis `P₁ = θ P₀`, `P₂ = a + (θ - 1) b`
  set P₁ := θ • P₀ with hP₁
  set P₂ := a + (θ - 1) • b with hP₂
  have hcr : cross P₁ P₂ = (θ * ξ * (θ - 1) - θ) * cross a b := by
    simp only [hP₁, hP₂, hP₀, cross, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hcoef : θ * ξ * (θ - 1) - θ < 0 := by nlinarith [mul_pos hθ0 hξ0]
  have hne : cross P₁ P₂ ≠ 0 := by rw [hcr]; exact mul_ne_zero hcoef.ne hab
  have hadm : IsAdmissible H (Submodule.span ℤ {P₁, P₂}) := by
    intro x hx hxi
    obtain ⟨m, k, rfl⟩ := mm_mem_span_pair.1 hx
    obtain ⟨h1, h2⟩ := hint _ hxi
    have e1 : cross ((m : ℝ) • P₁ + (k : ℝ) • P₂) b = ((m : ℝ) * θ * ξ + k) * cross a b := by
      simp only [hP₁, hP₂, hP₀, cross, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have e2 : cross a ((m : ℝ) • P₁ + (k : ℝ) • P₂) =
        ((m : ℝ) * θ + k * (θ - 1)) * cross a b := by
      simp only [hP₁, hP₂, hP₀, cross, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, abs_mul, mul_lt_iff_lt_one_left hD] at h1
    rw [e2, abs_mul, mul_lt_iff_lt_one_left hD] at h2
    obtain rfl := ml5_lemma1_int hθ0 hθ1 hξ0 hξ1 m k h1 h2
    by_cases hm : m = 0
    · subst hm; simp
    · exfalso
      apply hmult m hm
      convert hxi using 1
      rw [hP₁, smul_smul]; simp
  have hθξ : θ * ξ < 1 := by nlinarith
  have hlt : |cross P₁ P₂| < |cross a b| := by
    rw [hcr, abs_mul, abs_of_neg hcoef]
    have : -(θ * ξ * (θ - 1) - θ) < 1 := by
      nlinarith [mul_pos (sub_pos.2 hθ1) (sub_pos.2 hθξ)]
    nlinarith
  calc minimalDeterminant H ≤ det (Submodule.span ℤ {P₁, P₂}) :=
        mm_minimalDeterminant_le (mm_isLattice_span hne) hadm
    _ = |cross P₁ P₂| := mm_det_span hne
    _ < |cross a b| := hlt

/-- **Mahler, paper A, Lemma 1**: every parallelogram with centre at `O` is irreducible.

Mahler's proof: `Δ(K₀) = |det(a, b)|` (Minkowski's theorem on linear forms; here `ml5_par_minDet`,
from Mahler's §2 example and Lemma 3); a proper subdomain `H` misses a boundary point `P₀` of
`K₀`, and then `Δ(H) < Δ(K₀)` (`ml5_lemma1_core`). Gap in paper A (filled here): "without loss of
generality, `P₀ = (ξ, 1)`, `0 < ξ < 1`" is left to the reader: a symmetry `(a, b) ↦ (±a, ±b)`,
`(±b, ±a)` of the parallelogram puts `P₀` on the side `{ξ a + b | 0 ≤ ξ ≤ 1}`, and since `H` is
closed a neighbouring point of that side with `0 < ξ < 1` also lies outside `H`. -/
theorem ml5_lemma1 (hpar : IsParallelogram K) : IsIrreducible K := by
  have hKd := ml5_par_domain hpar
  obtain ⟨a, b, hab, hK⟩ := hpar
  have hmem : ∀ x, x ∈ K ↔ |cross x b| ≤ |cross a b| ∧ |cross a x| ≤ |cross a b| := fun x ↦ by
    rw [hK]; exact ml5_par_mem hab x
  have hD : 0 < |cross a b| := abs_pos.2 hab
  refine ⟨hKd, fun H hH hsub hne ↦ ?_⟩
  rw [ml5_par_minDet hKd hab hmem]
  obtain ⟨P, hPF, hPH⟩ := ml3_exists_frontier_notMem hKd hH hsub hne
  have hintK : ∀ x ∈ interior H, |cross x b| < |cross a b| ∧ |cross a x| < |cross a b| :=
    fun x hx ↦ ml5_par_interior hab hmem (interior_mono hsub hx)
  -- the reduction to `P₀ = ξ a' + b'`, `0 < ξ < 1`, for a symmetry `(a', b')`
  have red : ∀ a' b' : Fin 2 → ℝ, |cross a' b'| = |cross a b| →
      (∀ x ∈ interior H, |cross x b'| < |cross a b| ∧ |cross a' x| < |cross a b|) →
      ∀ σ : ℝ, |σ| ≤ 1 → σ • a' + b' ∉ H → minimalDeterminant H < |cross a b| := by
    intro a' b' hD' hint' σ hσ hσH
    have hab' : cross a' b' ≠ 0 := by intro h; rw [h, abs_zero] at hD'; linarith
    have hopen : {y | y ∉ H} ∈ 𝓝 (σ • a' + b') := hH.2.1.isClosed.isOpen_compl.mem_nhds hσH
    rcases le_total 0 σ with h | h
    · have hcl : σ ∈ closure (Ioo (0 : ℝ) 1) := by
        rw [closure_Ioo zero_ne_one]; exact ⟨h, (abs_le.1 hσ).2⟩
      have hev : {ξ : ℝ | ξ • a' + b' ∉ H} ∈ 𝓝 σ :=
        (show Continuous fun ξ : ℝ ↦ ξ • a' + b' by fun_prop).continuousAt.preimage_mem_nhds hopen
      obtain ⟨ξ, hξH, hξ⟩ := mem_closure_iff_nhds.1 hcl _ hev
      rw [← hD']
      exact ml5_lemma1_core hH hab' (by rw [hD']; exact hint') hξ.1 hξ.2 hξH
    · have hab'' : cross (-a') b' ≠ 0 := by rw [ml5_cross_neg_left]; exact neg_ne_zero.2 hab'
      have hD'' : |cross (-a') b'| = |cross a b| := by rw [ml5_cross_neg_left, abs_neg, hD']
      have hcl : -σ ∈ closure (Ioo (0 : ℝ) 1) := by
        rw [closure_Ioo zero_ne_one]; exact ⟨by linarith, by linarith [(abs_le.1 hσ).1]⟩
      have hev : {ξ : ℝ | ξ • (-a') + b' ∉ H} ∈ 𝓝 (-σ) :=
        (show Continuous fun ξ : ℝ ↦ ξ • (-a') + b' by fun_prop).continuousAt.preimage_mem_nhds
          (by rw [smul_neg, neg_smul, neg_neg]; exact hopen)
      obtain ⟨ξ, hξH, hξ⟩ := mem_closure_iff_nhds.1 hcl _ hev
      rw [← hD'']
      refine ml5_lemma1_core hH hab'' (fun x hx ↦ ?_) hξ.1 hξ.2 hξH
      rw [hD'', ml5_cross_neg_left, abs_neg]; exact hint' x hx
  -- the four sides
  have hdec := mm_eq_comb hab P
  set s := cross P b / cross a b with hs
  set t := cross a P / cross a b with ht
  obtain ⟨hs1, ht1⟩ := (hmem P).1 (mm_mem_of_frontier hKd hPF)
  have hs1' : |s| ≤ 1 := by rw [hs, abs_div, div_le_one hD]; exact hs1
  have ht1' : |t| ≤ 1 := by rw [ht, abs_div, div_le_one hD]; exact ht1
  have sw : ∀ x y : Fin 2 → ℝ, |cross y x| = |cross x y| := fun x y ↦ by
    rw [mm_cross_swap, abs_neg]
  have nr : ∀ x y : Fin 2 → ℝ, |cross x (-y)| = |cross x y| := fun x y ↦ by
    rw [ml5_cross_neg_right, abs_neg]
  rcases ml5_par_frontier hmem hPF with h | h
  · have hs' : |s| = 1 := by rw [hs, abs_div, h, div_self hD.ne']
    rcases (abs_eq zero_le_one).1 hs' with e | e
    · refine red b a (sw a b) (fun x hx ↦ ?_) t ht1' ?_
      · rw [sw a x, sw x b]; exact (hintK x hx).symm
      · have : t • b + a = P := by rw [hdec, e]; module
        rw [this]; exact hPH
    · refine red b (-a) (by rw [nr, sw a b]) (fun x hx ↦ ?_) t ht1' ?_
      · rw [nr, sw a x, sw x b]; exact (hintK x hx).symm
      · have : t • b + -a = P := by rw [hdec, e]; module
        rw [this]; exact hPH
  · have ht' : |t| = 1 := by rw [ht, abs_div, h, div_self hD.ne']
    rcases (abs_eq zero_le_one).1 ht' with e | e
    · refine red a b rfl hintK s hs1' ?_
      have : s • a + b = P := by rw [hdec, e]; module
      rw [this]; exact hPH
    · refine red a (-b) (nr a b) (fun x hx ↦ ?_) s hs1' ?_
      · rw [nr]; exact hintK x hx
      · have : s • a + -b = P := by rw [hdec, e]; module
        rw [this]; exact hPH

/-! ### Critical configurations and Mahler's Lemmas 5–7 of paper A -/

/-- A positively oriented critical configuration `O P₁ P₂ P₃` (paper A, Lemma 3): `P₁, P₂` and
`P₃ = P₂ - P₁` are boundary points and `det(P₁, P₂) = Δ(K)`. The lattice of basis `P₁, P₂` is then
critical (`ml5_pi_of_conf`), and its points `P₁, P₂, P₃, -P₁, -P₂, -P₃` on `C` follow one another
in the positive sense; `(P₂, P₃)` and `(P₁ - P₂, P₁)` are configurations of the same lattice
(`ml5_conf_next`, `ml5_conf_prev`). -/
def ml5_IsConf (K : Set (Fin 2 → ℝ)) (P₁ P₂ : Fin 2 → ℝ) : Prop :=
  P₁ ∈ frontier K ∧ P₂ ∈ frontier K ∧ P₂ - P₁ ∈ frontier K ∧ cross P₁ P₂ = minimalDeterminant K

section Conf

variable {P₁ P₂ : Fin 2 → ℝ}

lemma ml5_conf_next (hK : IsSymmetricConvexDomain K) (h : ml5_IsConf K P₁ P₂) :
    ml5_IsConf K P₂ (P₂ - P₁) :=
  ⟨h.2.1, h.2.2.1, by rw [sub_sub_cancel_left]; exact mm_neg_mem_frontier hK h.1,
    by rw [← h.2.2.2]; simp only [cross, Pi.sub_apply]; ring⟩

lemma ml5_conf_prev (hK : IsSymmetricConvexDomain K) (h : ml5_IsConf K P₁ P₂) :
    ml5_IsConf K (P₁ - P₂) P₁ :=
  ⟨by rw [← neg_sub]; exact mm_neg_mem_frontier hK h.2.2.1, h.1,
    by rw [sub_sub_cancel]; exact h.2.1, by rw [← h.2.2.2]; simp only [cross, Pi.sub_apply]; ring⟩

lemma ml5_conf_pos (hK : IsSymmetricConvexDomain K) (h : ml5_IsConf K P₁ P₂) :
    0 < cross P₁ P₂ := h.2.2.2 ▸ irr_minimalDeterminant_pos hK

/-- A boundary point on a critical lattice is the first point of a configuration (Lemma 3). -/
lemma ml5_conf_of_pi (hK : IsSymmetricConvexDomain K) {P : Fin 2 → ℝ} (hP : P ∈ frontier K)
    (hΛ : ∃ Λ, IsCritical K Λ ∧ P ∈ Λ) : ∃ W, ml5_IsConf K P W := by
  obtain ⟨Λ, hΛ, hPΛ⟩ := hΛ
  obtain ⟨W, hW, hWP, habs⟩ := ml3_pair hK hΛ hPΛ hP
  rcases (abs_eq (irr_minimalDeterminant_pos hK).le).1 habs with h | h
  · exact ⟨W, hP, hW, hWP, h⟩
  · refine ⟨P - W, hP, by rw [← neg_sub]; exact mm_neg_mem_frontier hK hWP,
      by rw [sub_sub_cancel_left]; exact mm_neg_mem_frontier hK hW, ?_⟩
    rw [show cross P (P - W) = -cross P W by simp only [cross, Pi.sub_apply]; ring, h, neg_neg]

/-- The first point of a configuration lies on a critical lattice (Lemma 3, converse part). -/
lemma ml5_pi_of_conf (hK : IsSymmetricConvexDomain K) (h : ml5_IsConf K P₁ P₂) :
    ∃ Λ, IsCritical K Λ ∧ P₁ ∈ Λ := by
  obtain ⟨-, h2⟩ := (minkowski_mahler hK).2 (P₂ - P₁) P₂ P₁ h.2.2.1 h.2.1 h.1 (by abel)
  refine ⟨_, h2.1 ?_, ?_⟩
  · rw [show cross (P₂ - P₁) P₂ = -cross P₁ P₂ by simp only [cross, Pi.sub_apply]; ring, abs_neg,
      h.2.2.2, abs_of_pos (irr_minimalDeterminant_pos hK)]
  · rw [show P₁ = P₂ - (P₂ - P₁) by abel]
    exact Submodule.sub_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))

end Conf

/-- The Plücker relation `det(A, B) det(X, Y) = det(X, B) det(A, Y) + det(A, X) det(B, Y)`. -/
lemma ml5_plucker (A B X Y : Fin 2 → ℝ) :
    cross A B * cross X Y = cross X B * cross A Y + cross A X * cross B Y := by
  simp only [cross]; ring

lemma ml5_neg_mem_openArc (hK : IsSymmetricConvexDomain K) {R S X : Fin 2 → ℝ}
    (h : X ∈ openArc K R S) : -X ∈ openArc K (-R) (-S) := by
  obtain ⟨hX, a, b, ha, hb, rfl⟩ := h
  exact ⟨mm_neg_mem_frontier hK hX, a, b, ha, hb, by module⟩

/-- A point of an arc other than its ends is an inner point of the arc. -/
lemma ml5_openArc_of_arc (hK : IsSymmetricConvexDomain K) {R S Z : Fin 2 → ℝ}
    (hR : R ∈ frontier K) (hS : S ∈ frontier K) (hZ : Z ∈ arc K R S) (hZR : Z ≠ R) (hZS : Z ≠ S) :
    Z ∈ openArc K R S := by
  obtain ⟨hZF, a, b, ha, hb, rfl⟩ := hZ
  have hZ0 := mm_ne_zero_of_frontier hK hZF
  refine ⟨hZF, a, b, lt_of_le_of_ne ha fun h ↦ ?_, lt_of_le_of_ne hb fun h ↦ ?_, rfl⟩
  · subst h
    rw [zero_smul, zero_add] at hZF hZ0 hZS
    have hb0 : 0 < b := lt_of_le_of_ne hb fun h ↦ hZ0 (by rw [← h, zero_smul])
    exact hZS (by rw [ml5_ray hK hS hb0 hZF, one_smul])
  · subst h
    rw [zero_smul, add_zero] at hZF hZ0 hZR
    have ha0 : 0 < a := lt_of_le_of_ne ha fun h ↦ hZ0 (by rw [← h, zero_smul])
    exact hZR (by rw [ml5_ray hK hR ha0 hZF, one_smul])

/-- **Mahler, paper A, Lemma 5.** Let `K` be a convex domain which is not a parallelogram, and
`O P₁ P₂ P₃` a critical configuration. Then all points of the segment `P₂P₃` other than `P₂, P₃`
are inner points of `K`.

Mahler's proof: let `L*` be a tac-line at `P₁`, `L**` the line `P₂P₃`, and `K*` the parallelogram
bounded by `±L*, ±L**`. If an inner point of `P₂P₃` lies on `C`, `L**` is a tac-line and
`K ⊆ K*`; the lattice of basis `P₁, P₂` is `K*`-admissible (its points `P₁, P₂, P₃` lie on the
boundary of `K*`), hence `Δ(K*) = Δ(K)`, and by Lemma 1 (`ml5_lemma1`) `K = K*`, a contradiction.
(Slip in paper A: Mahler writes "if at least one inner point of the segment `P₂P₃` lies on `L**`",
meaning "on `C`".) -/
theorem ml5_lemma5 (hK : IsSymmetricConvexDomain K) (hpar : ¬IsParallelogram K)
    {P₁ P₂ : Fin 2 → ℝ} (h : ml5_IsConf K P₁ P₂) :
    ∀ t ∈ Ioo (0 : ℝ) 1, (1 - t) • P₂ + t • (P₂ - P₁) ∈ interior K := by
  intro t ht
  by_contra hY
  obtain ⟨h1, h2, h3, hdet⟩ := h
  have mem : ∀ {x : Fin 2 → ℝ}, x ∈ frontier K → x ∈ K := fun hx ↦ mm_mem_of_frontier hK hx
  have hYK : (1 - t) • P₂ + t • (P₂ - P₁) ∈ K :=
    hK.1 (mem h2) (mem h3) (by linarith [ht.2]) ht.1.le (by ring)
  -- `L**` is a tac-line: a support functional `ψ` at the inner point is `1` at `P₂, P₃`
  obtain ⟨ψ, hψ1, hψ2, -⟩ := mm_support hK (mm_mem_frontier hK hYK hY)
  have e2 := hψ2 P₂ (mem h2)
  have e3 := hψ2 _ (mem h3)
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hψ1
  have hψ2' : ψ P₂ = 1 := by nlinarith [ht.1, ht.2]
  have hψ3' : ψ (P₂ - P₁) = 1 := by nlinarith [ht.1, ht.2]
  have hψ1' : ψ P₁ = 0 := by rw [map_sub] at hψ3'; linarith
  -- `L*`: a support functional `φ` at `P₁`
  obtain ⟨φ, hφ1, hφ2, -⟩ := mm_support hK h1
  -- the parallelogram `K* = {|φ| ≤ 1, |ψ| ≤ 1}`, with vertices `±a ± b`
  set a : Fin 2 → ℝ := P₁ with ha
  set b : Fin 2 → ℝ := P₂ - (φ P₂) • P₁ with hb
  have hφb : φ b = 0 := by rw [hb, map_sub, map_smul, hφ1, smul_eq_mul, mul_one, sub_self]
  have hψb : ψ b = 1 := by rw [hb, map_sub, map_smul, hψ1', smul_zero, sub_zero, hψ2']
  have hcr : cross a b ≠ 0 := by
    intro hc
    obtain ⟨τ, hτ⟩ := ml3_parallel hc (mm_ne_zero_of_frontier hK h1)
    have := congrArg ψ hτ
    rw [map_smul, hψb, hψ1', smul_zero] at this
    exact one_ne_zero this
  have hdec : ∀ x, x = φ x • a + ψ x • b := by
    intro x
    have hd := mm_eq_comb hcr x
    have hφx : φ x = cross x b / cross a b := by
      conv_lhs => rw [hd]
      simp [hφ1, hφb]
    have hψx : ψ x = cross a x / cross a b := by
      conv_lhs => rw [hd]
      simp [hψ1', hψb]
    rw [hφx, hψx]; exact hd
  set Kst := {x | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • a + t • b} with hKst
  have hpar' : IsParallelogram Kst := ⟨a, b, hcr, rfl⟩
  have hKstd := ml5_par_domain hpar'
  have habs : ∀ f : StrongDual ℝ (Fin 2 → ℝ), (∀ y ∈ K, f y ≤ 1) → ∀ y ∈ K, |f y| ≤ 1 := by
    intro f hf y hy
    have := hf _ (hK.2.2.2 y hy)
    rw [map_neg] at this
    exact abs_le.2 ⟨by linarith, hf y hy⟩
  have hsub : K ⊆ Kst := fun x hx ↦ ⟨φ x, ψ x, habs φ hφ2 x hx, habs ψ hψ2 x hx, hdec x⟩
  have hne : K ≠ Kst := fun h ↦ hpar (h ▸ hpar')
  have hlt := (ml5_lemma1 hpar').2 K hK hsub hne
  -- `φ, ψ ≤ 1` on `K*`
  have hKφ : ∀ y ∈ Kst, φ y ≤ 1 := by
    rintro y ⟨s, t, hs, -, rfl⟩
    simp only [map_add, map_smul, smul_eq_mul, hφ1, hφb, mul_one, mul_zero, add_zero]
    exact (le_abs_self s).trans hs
  have hKψ : ∀ y ∈ Kst, ψ y ≤ 1 := by
    rintro y ⟨s, t, -, ht, rfl⟩
    simp only [map_add, map_smul, smul_eq_mul, hψ1', hψb, mul_one, mul_zero, zero_add]
    exact (le_abs_self t).trans ht
  have fr : ∀ (f : StrongDual ℝ (Fin 2 → ℝ)), (∀ y ∈ Kst, f y ≤ 1) → ∀ y, y ∈ K → f y = 1 →
      y ∈ frontier Kst := by
    intro f hf y hy hfy
    refine mm_mem_frontier hKstd (hsub hy) fun hi ↦ ?_
    have := ml3_lt_of_interior f hf (v := y) (by rw [hfy]; norm_num) hi
    linarith
  have f1 := fr φ hKφ P₁ (mem h1) hφ1
  have f2 := fr ψ hKψ P₂ (mem h2) hψ2'
  have f3 := fr ψ hKψ _ (mem h3) hψ3'
  -- the lattice of basis `P₃, P₂` is `K*`-admissible, so `Δ(K*) ≤ Δ(K)`
  obtain ⟨hle, -⟩ := (minkowski_mahler hKstd).2 (P₂ - P₁) P₂ P₁ f3 f2 f1 (by abel)
  rw [show cross (P₂ - P₁) P₂ = -cross P₁ P₂ by simp only [cross, Pi.sub_apply]; ring, abs_neg,
    hdet, abs_of_pos (irr_minimalDeterminant_pos hK)] at hle
  linarith

/-- **The line `L**` meets `C` only at `P₂` and `P₃`** (from Lemma 5 and the convexity of `C`,
`BoundaryArc.eq_zero_or_eq_one_of_collinear`). -/
lemma ml5_lemma5_line (hK : IsSymmetricConvexDomain K) (hpar : ¬IsParallelogram K)
    {P₁ P₂ : Fin 2 → ℝ} (h : ml5_IsConf K P₁ P₂) {X : Fin 2 → ℝ} (hX : X ∈ frontier K)
    (hXc : cross P₁ X = cross P₁ P₂) : X = P₂ ∨ X = P₂ - P₁ := by
  have hc : cross P₁ (X - P₂) = 0 := by simp only [cross, Pi.sub_apply] at hXc ⊢; linarith
  obtain ⟨σ, hσ⟩ := ml3_parallel hc (mm_ne_zero_of_frontier hK h.1)
  have hXe : X = (1 - -σ) • P₂ + (-σ) • (P₂ - P₁) := by
    rw [show X = P₂ + σ • P₁ by rw [← hσ]; abel]; module
  rcases eq_zero_or_eq_one_of_collinear hK.1 h.2.1.2 h.2.2.1.2 (ml5_lemma5 hK hpar h)
    (t := -σ) (by rw [← hXe]; exact mm_mem_of_frontier hK hX) (by rw [← hXe]; exact hX.2)
    with h0 | h1
  · left; rw [hXe, h0]; simp
  · right; rw [hXe, h1]; simp

/-- **Lemma 5, second part** ("`I₂(P₁)` reduces to the single point `P₂`"): the configuration
starting at `P₁` is unique. -/
theorem ml5_lemma5_partner (hK : IsSymmetricConvexDomain K) (hpar : ¬IsParallelogram K)
    {P₁ P₂ P₂' : Fin 2 → ℝ} (h : ml5_IsConf K P₁ P₂) (h' : ml5_IsConf K P₁ P₂') : P₂' = P₂ := by
  have hP0 := mm_ne_zero_of_frontier hK h.1
  rcases ml5_lemma5_line hK hpar h h'.2.1 (by rw [h'.2.2.2, h.2.2.2]) with e | e
  · exact e
  · exfalso
    have hc : cross P₁ (P₂' - P₁) = cross P₁ P₂ := by
      rw [e]; simp only [cross, Pi.sub_apply]; ring
    rcases ml5_lemma5_line hK hpar h h'.2.2.1 hc with e' | e' <;> rw [e] at e'
    · apply hP0
      have : (2 : ℝ) • P₁ = 0 := by rw [two_smul]; linear_combination (exp := 1) -e'
      exact (smul_eq_zero.1 this).resolve_left two_ne_zero
    · exact hP0 (by linear_combination (exp := 1) -e')

/-- **Corollary to Lemma 5**, first part: a critical lattice of a convex domain which is not a
parallelogram has just six points `±P₁, ±P₂, ±P₃` on `C`. Gap in paper A (filled here): the
corollary is stated without proof. A further point `u` of the lattice on `C` would be `A + B` with
`A, B, A ± B` on `C` and `|det(A, B)| = Δ(K)` (`ml3_eight`), so that `A + B` and `B` (or `A + B`
and `A`) would be two partners of `A` (or of `B`), against `ml5_lemma5_partner`. -/
theorem ml5_lemma5_cor_six (hK : IsSymmetricConvexDomain K) (hpar : ¬IsParallelogram K)
    {P₁ P₂ : Fin 2 → ℝ} (h : ml5_IsConf K P₁ P₂) {u : Fin 2 → ℝ} (hu : u ∈ frontier K)
    (huΛ : u ∈ Submodule.span ℤ {P₁, P₂}) :
    u = P₁ ∨ u = P₂ ∨ u = P₂ - P₁ ∨ u = -P₁ ∨ u = -P₂ ∨ u = -(P₂ - P₁) := by
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hne
  have e : P₁ + (P₂ - P₁) = P₂ := by abel
  obtain ⟨A, B, hA, hB, hAB, hAB', hu', habs⟩ := ml3_eight hK h.1 h.2.2.1 (by rw [e]; exact h.2.1)
    (mm_mem_of_frontier hK hu) (by rw [e]; exact huΛ)
    ⟨mm_ne_zero_of_frontier hK hu, n1, n4, n3, n6, by rw [e]; exact n2, by rw [e]; exact n5⟩
  have hΔ : |cross P₁ (P₂ - P₁)| = minimalDeterminant K := by
    rw [show cross P₁ (P₂ - P₁) = cross P₁ P₂ by simp only [cross, Pi.sub_apply]; ring, h.2.2.2,
      abs_of_pos (irr_minimalDeterminant_pos hK)]
  rw [hΔ] at habs
  have hBA : B - A ∈ frontier K := by rw [← neg_sub]; exact mm_neg_mem_frontier hK hAB'
  rcases (abs_eq (irr_minimalDeterminant_pos hK).le).1 habs with hc | hc
  · -- `A + B` and `B` are partners of `A`
    have c1 : ml5_IsConf K A (A + B) := ⟨hA, hAB, by rw [add_sub_cancel_left]; exact hB,
      by rw [show cross A (A + B) = cross A B by simp only [cross, Pi.add_apply]; ring, hc]⟩
    have c2 : ml5_IsConf K A B := ⟨hA, hB, hBA, hc⟩
    have := ml5_lemma5_partner hK hpar c2 c1
    exact mm_ne_zero_of_frontier hK hA (by linear_combination (exp := 1) this)
  · -- `A + B` and `A` are partners of `B`
    have hc' : cross B A = minimalDeterminant K := by rw [mm_cross_swap, hc, neg_neg]
    have c1 : ml5_IsConf K B (A + B) := ⟨hB, hAB, by rw [add_sub_cancel_right]; exact hA,
      by rw [show cross B (A + B) = cross B A by simp only [cross, Pi.add_apply]; ring, hc']⟩
    have c2 : ml5_IsConf K B A := ⟨hB, hA, hAB', hc'⟩
    have := ml5_lemma5_partner hK hpar c2 c1
    exact mm_ne_zero_of_frontier hK hB (by linear_combination (exp := 1) this)

/-- **Lemma 5, last part**: `Λ` is the only critical lattice of `K` containing `P₁` (Mahler: "the
second part also holds since `I₂(P₁)` reduces to the single point `P₂`"). A critical lattice `Λ'`
through `P₁` has a configuration `(R₁, R₂)` of basis points (Lemma 3); by the Corollary `P₁` is one
of its six points on `C`, so a rotation or reflection of `(R₁, R₂)` is a configuration `(P₁, W)`
with `W ∈ Λ'`; then `W = P₂` (`ml5_lemma5_partner`), and `P₁, P₂` is a basis of `Λ'`. -/
theorem ml5_lemma5_unique (hK : IsSymmetricConvexDomain K) (hpar : ¬IsParallelogram K)
    {P₁ P₂ : Fin 2 → ℝ} (h : ml5_IsConf K P₁ P₂) {Λ : Submodule ℤ (Fin 2 → ℝ)}
    (hΛ : IsCritical K Λ) (hP : P₁ ∈ Λ) : Λ = Submodule.span ℤ {P₁, P₂} := by
  obtain ⟨Q₀, Q₁, Q₂, -, -, -, h0F, h1F, h2F, hB, h012, -, hdet⟩ :=
    (minkowski_mahler hK).1 Λ hΛ
  -- a positively oriented configuration `(R₁, R₂)` of basis points
  obtain ⟨R₁, R₂, hR, hRΛ⟩ : ∃ R₁ R₂, ml5_IsConf K R₁ R₂ ∧ Λ = Submodule.span ℤ {R₁, R₂} := by
    rcases (abs_eq (irr_minimalDeterminant_pos hK).le).1 hdet with e | e
    · exact ⟨Q₀, Q₁, ⟨h0F, h1F, by rw [h012, add_sub_cancel_left]; exact h2F, e⟩, hB.2.symm⟩
    · refine ⟨Q₁, Q₀, ⟨h1F, h0F, ?_, by rw [mm_cross_swap, e, neg_neg]⟩, ?_⟩
      · rw [h012, sub_add_cancel_left]; exact mm_neg_mem_frontier hK h2F
      rw [← hB.2, Set.pair_comm]
  have m1 : R₁ ∈ Λ := by rw [hRΛ]; exact Submodule.subset_span (by simp)
  have m2 : R₂ ∈ Λ := by rw [hRΛ]; exact Submodule.subset_span (by simp)
  have cneg : ∀ {S₁ S₂ : Fin 2 → ℝ}, ml5_IsConf K S₁ S₂ → ml5_IsConf K (-S₁) (-S₂) :=
    fun {S₁ S₂} hS ↦ ⟨mm_neg_mem_frontier hK hS.1, mm_neg_mem_frontier hK hS.2.1,
      by rw [show -S₂ - -S₁ = -(S₂ - S₁) by abel]; exact mm_neg_mem_frontier hK hS.2.2.1,
      by rw [ml5_cross_neg_left, ml5_cross_neg_right, neg_neg]; exact hS.2.2.2⟩
  have six := ml5_lemma5_cor_six hK hpar hR h.1 (by rw [← hRΛ]; exact hP)
  -- the partner `W ∈ Λ` of `P₁` in `Λ`
  obtain ⟨W, hWΛ, hW⟩ : ∃ W ∈ Λ, ml5_IsConf K P₁ W := by
    rcases six with e | e | e | e | e | e <;> rw [e]
    · exact ⟨R₂, m2, hR⟩
    · exact ⟨R₂ - R₁, Λ.sub_mem m2 m1, ml5_conf_next hK hR⟩
    · refine ⟨-R₁, Λ.neg_mem m1, ?_⟩
      have := ml5_conf_next hK (ml5_conf_next hK hR); rwa [sub_sub_cancel_left] at this
    · exact ⟨-R₂, Λ.neg_mem m2, cneg hR⟩
    · exact ⟨-(R₂ - R₁), Λ.neg_mem (Λ.sub_mem m2 m1), cneg (ml5_conf_next hK hR)⟩
    · refine ⟨R₁, m1, ?_⟩
      have := ml5_conf_prev hK hR; rwa [show R₁ - R₂ = -(R₂ - R₁) by abel] at this
  rw [ml5_lemma5_partner hK hpar h hW] at hWΛ
  rw [hRΛ] at hP hWΛ ⊢
  refine (mm_span_eq (ml5_conf_pos hK hR).ne' hP hWΛ ?_).symm
  rw [h.2.2.2, hR.2.2.2]

/-- **Corollary to Lemma 5**, second part: none of the arcs `A₁ = P₁P₂`, `A₂ = P₂P₃`,
`A₃ = P₃(-P₁)` (nor, by symmetry, `A₄, A₅, A₆`) is a line segment: the inner points of the chords
are inner points of `K` (Lemma 5 for the configurations `(P₁ - P₂, P₁)`, `(P₁, P₂)`,
`(P₂, P₃)`). -/
theorem ml5_lemma5_cor_arcs (hK : IsSymmetricConvexDomain K) (hpar : ¬IsParallelogram K)
    {P₁ P₂ : Fin 2 → ℝ} (h : ml5_IsConf K P₁ P₂) :
    (∀ t ∈ Ioo (0 : ℝ) 1, (1 - t) • P₁ + t • P₂ ∈ interior K) ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, (1 - t) • P₂ + t • (P₂ - P₁) ∈ interior K) ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, (1 - t) • (P₂ - P₁) + t • (-P₁) ∈ interior K) := by
  refine ⟨fun t ht ↦ ?_, ml5_lemma5 hK hpar h, fun t ht ↦ ?_⟩
  · have := ml5_lemma5 hK hpar (ml5_conf_prev hK h) t ht
    rwa [sub_sub_cancel] at this
  · have := ml5_lemma5 hK hpar (ml5_conf_next hK h) t ht
    rwa [sub_sub_cancel_left] at this

section Lemma67

variable {P₁ P₂ : Fin 2 → ℝ}

lemma ml5_cross_P₃ (P₁ P₂ : Fin 2 → ℝ) : cross P₂ (P₂ - P₁) = cross P₁ P₂ := by
  simp only [cross, Pi.sub_apply]; ring

lemma ml5_cross_P₄ (P₁ P₂ : Fin 2 → ℝ) : cross (P₂ - P₁) (-P₁) = cross P₁ P₂ := by
  simp only [cross, Pi.sub_apply, Pi.neg_apply]; ring

/-- **Lemma 6, first step** ("none of the three arcs `A₆, A₁, A₂` is a line segment; hence, by the
convexity of `C`, `P₁*` is an inner point of the triangle with vertices `P₁, P₁ + P₂, P₂`"): an
inner point `X = s P₁ + t P₂` of the arc `A₁` has `0 < s, t < 1 < s + t`, where
`s Δ = det(X, P₂)`, `t Δ = det(P₁, X)`. The bounds `s, t ≤ 1 ≤ s + t` come from the chords
`P₆P₁`, `P₂P₃` and `P₁P₂` (`ml5_chord`, `ml5_beyond`); equality would put `X`, `P₁` or `P₂` inside
a segment of `C` containing a chord of the Corollary to Lemma 5. -/
lemma ml5_triangle (hK : IsSymmetricConvexDomain K) (hpar : ¬IsParallelogram K)
    {X : Fin 2 → ℝ} (h : ml5_IsConf K P₁ P₂) (hX : X ∈ openArc K P₁ P₂) :
    0 < cross X P₂ ∧ cross X P₂ < cross P₁ P₂ ∧ 0 < cross P₁ X ∧ cross P₁ X < cross P₁ P₂ ∧
      cross P₁ P₂ < cross X P₂ + cross P₁ X := by
  have hΔ := ml5_conf_pos hK h
  obtain ⟨hXF, h1, h2⟩ := (ml5_mem_openArc_iff hΔ).1 hX
  obtain ⟨c1, c2, -⟩ := ml5_lemma5_cor_arcs hK hpar h
  obtain ⟨c6, -, -⟩ := ml5_lemma5_cor_arcs hK hpar (ml5_conf_prev hK h)
  have hXK := mm_mem_of_frontier hK hXF
  have hdec := mm_eq_comb hΔ.ne' X
  set Δ := cross P₁ P₂ with hΔdef
  set s := cross X P₂ / Δ with hs
  set t := cross P₁ X / Δ with ht
  have hs0 : 0 < s := div_pos h2 hΔ
  have ht0 : 0 < t := div_pos h1 hΔ
  have hsΔ : cross X P₂ = s * Δ := by rw [hs]; field_simp
  have htΔ : cross P₁ X = t * Δ := by rw [ht]; field_simp
  have mid : ∀ U V : Fin 2 → ℝ, U ∈ K → V ∈ K → ∀ Y ∈ openSegment ℝ U V, Y ∉ interior K →
      ∀ Z ∈ segment ℝ U V, Z ∉ interior K := fun U V hU hV Y hY hYi Z hZ ↦
    not_mem_interior_of_mem_segment hK.1 hK.2.2.1 hU hV hY hYi hZ
  -- `s + t > 1`
  have hb := ml5_beyond hK (mm_mem_of_frontier hK h.1) (mm_mem_of_frontier hK h.2.1) hΔ hXF
    h1.le h2.le
  have hst : Δ < cross X P₂ + cross P₁ X := by
    refine lt_of_le_of_ne hb fun he ↦ hXF.2 ?_
    have hst1 : s + t = 1 := by
      rw [hsΔ, htΔ, ← add_mul] at he
      exact (mul_eq_right₀ hΔ.ne').1 he.symm
    have := c1 t ⟨ht0, by linarith⟩
    rwa [show 1 - t = s by linarith, ← hdec] at this
  -- `t < 1`: the chord `P₂P₃`
  have ct := ml5_chord hK h.2.1 h.2.2.1 (by rw [ml5_cross_P₃]; exact hΔ) hXK
    (Or.inl (by rw [mm_cross_swap]; linarith))
  rw [show cross X (P₂ - P₁) + cross P₂ X = cross P₁ X by simp only [cross, Pi.sub_apply]; ring,
    ml5_cross_P₃] at ct
  have ht1 : cross P₁ X < Δ := by
    refine lt_of_le_of_ne ct fun he ↦ ?_
    have ht' : t = 1 := by rw [ht, he, div_self hΔ.ne']
    -- `P₂` is an inner point of the segment from `X` to `P₃`
    have hX' : X = s • P₁ + P₂ := by rw [hdec, ht', one_smul]
    have hseg : P₂ ∈ openSegment ℝ X (P₂ - P₁) :=
      ⟨1 / (1 + s), s / (1 + s), by positivity, by positivity, by field_simp, by
        rw [hX']; ext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        field_simp; ring⟩
    have hmid : (1 - 1 / 2 : ℝ) • P₂ + (1 / 2 : ℝ) • (P₂ - P₁) ∈ segment ℝ X (P₂ - P₁) :=
      ⟨1 / (2 * (1 + s)), 1 - 1 / (2 * (1 + s)), by positivity, by
        rw [sub_nonneg, div_le_one (by positivity)]; linarith, by ring, by
        rw [hX']; ext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        field_simp; ring⟩
    exact mid _ _ hXK (mm_mem_of_frontier hK h.2.2.1) _ hseg h.2.1.2 _ hmid
      (c2 (1 / 2) ⟨by norm_num, by norm_num⟩)
  -- `s < 1`: the chord `P₆P₁`
  have cs := ml5_chord hK (ml5_conf_prev hK h).1 h.1 (ml5_conf_pos hK (ml5_conf_prev hK h)) hXK
    (Or.inr (by rw [mm_cross_swap]; linarith))
  rw [show cross X P₁ + cross (P₁ - P₂) X = cross X P₂ by simp only [cross, Pi.sub_apply]; ring,
    show cross (P₁ - P₂) P₁ = Δ by simp only [hΔdef, cross, Pi.sub_apply]; ring] at cs
  have hs1 : cross X P₂ < Δ := by
    refine lt_of_le_of_ne cs fun he ↦ ?_
    have hs' : s = 1 := by rw [hs, he, div_self hΔ.ne']
    -- `P₁` is an inner point of the segment from `P₆ = P₁ - P₂` to `X`
    have hX' : X = P₁ + t • P₂ := by rw [hdec, hs', one_smul]
    have hseg : P₁ ∈ openSegment ℝ (P₁ - P₂) X :=
      ⟨t / (1 + t), 1 / (1 + t), by positivity, by positivity, by field_simp; ring, by
        rw [hX']; ext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        field_simp; ring⟩
    have hmid : (1 - 1 / 2 : ℝ) • (P₁ - P₂) + (1 / 2 : ℝ) • P₁ ∈ segment ℝ (P₁ - P₂) X :=
      ⟨1 - 1 / (2 * (1 + t)), 1 / (2 * (1 + t)), by
        rw [sub_nonneg, div_le_one (by positivity)]; linarith, by positivity, by ring, by
        rw [hX']; ext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        field_simp; ring⟩
    exact mid _ _ (mm_mem_of_frontier hK (ml5_conf_prev hK h).1) hXK _ hseg h.1.2 _ hmid
      (c6 (1 / 2) ⟨by norm_num, by norm_num⟩)
  exact ⟨h2, hs1, h1, ht1, hst⟩

/-- **Mahler, paper A, Lemma 6.** Let `K` be a convex domain which is not a parallelogram,
`O P₁ P₂ P₃` a critical configuration of the critical lattice `Λ`, and `Λ*` a critical lattice
with a point `P₁*` inside the arc `A₁ = P₁P₂`, with configuration `O P₁* P₂* P₃*`. Then `P₂*` and
`P₃*` are inner points of the arcs `A₂ = P₂P₃` and `A₃ = P₃(-P₁)`. (Applied to the rotated
configurations `(P₂, P₃)`, `(P₃, -P₁)`, … and with `Λ*` symmetric, this is Mahler's statement that
`Λ*` has just one point on each arc `A_l`.)

Mahler's proof: `P₁* = s P₁ + t P₂` with `0 < s, t < 1 < s + t` (`ml5_triangle`), so
`0 < {P₁*, P₂} = sΔ < Δ`, `{P₁*, P₃} = (s + t)Δ > Δ` and `0 < {P₁*, P₄} = tΔ < Δ`. Hence the
line `{P₁*, X} = Δ` meets `C` at an inner point of `A₂` and at an inner point of `A₃`
(intermediate value theorem on arcs, `BoundaryArc.exists_mem_arc_eq`). By Lemma 5 its only points
on `C` are `P₂*` and `P₃*` (`ml5_lemma5_line`); the one on `A₂` comes after the one on `A₃` in the
direction of `P₁*`, so it is `P₂* = P₃* + P₁*`. -/
theorem ml5_lemma6 (hK : IsSymmetricConvexDomain K) (hpar : ¬IsParallelogram K)
    {X Y : Fin 2 → ℝ} (h : ml5_IsConf K P₁ P₂) (h' : ml5_IsConf K X Y)
    (hX : X ∈ openArc K P₁ P₂) :
    Y ∈ openArc K P₂ (P₂ - P₁) ∧ Y - X ∈ openArc K (P₂ - P₁) (-P₁) := by
  have hΔ := ml5_conf_pos hK h
  obtain ⟨-, s1, -, t1, st⟩ := ml5_triangle hK hpar h hX
  have hXY : cross X Y = cross P₁ P₂ := by rw [h'.2.2.2, h.2.2.2]
  have hP₃ : 0 < cross P₂ (P₂ - P₁) := by rw [ml5_cross_P₃]; exact hΔ
  have hP₄ : 0 < cross (P₂ - P₁) (-P₁) := by rw [ml5_cross_P₄]; exact hΔ
  have f3 : cross P₁ P₂ < cross X (P₂ - P₁) := by
    rw [show cross X (P₂ - P₁) = cross X P₂ + cross P₁ X by simp only [cross, Pi.sub_apply]; ring]
    exact st
  have f4 : cross X (-P₁) < cross P₁ P₂ := by
    rw [ml5_cross_neg_right, mm_cross_swap, neg_neg]; exact t1
  have h0 := mm_zero_mem_interior hK
  have hnP₁ := mm_neg_mem_frontier hK h.1
  -- the line `{P₁*, X} = Δ` meets the arcs `A₂` and `A₃`
  obtain ⟨Z, hZ, hZc⟩ := exists_mem_arc_eq hK.1 h0 hK.2.1.isBounded h.2.1 h.2.2.1
    (ml5_zero_notMem_segment hP₃.ne') (ml5_continuous_cross_right X) s1.le f3.le
  obtain ⟨Z', hZ', hZc'⟩ := exists_mem_arc_eq hK.1 h0 hK.2.1.isBounded h.2.2.1 hnP₁
    (ml5_zero_notMem_segment hP₄.ne') (f := fun W ↦ -cross X W)
    (ml5_continuous_cross_right X).neg (c := -cross P₁ P₂) (by linarith) (by linarith)
  simp only [neg_inj] at hZc'
  have hZo : Z ∈ openArc K P₂ (P₂ - P₁) := ml5_openArc_of_arc hK h.2.1 h.2.2.1 hZ
    (by rintro rfl; linarith) (by rintro rfl; linarith)
  have hZo' : Z' ∈ openArc K (P₂ - P₁) (-P₁) := ml5_openArc_of_arc hK h.2.2.1 hnP₁ hZ'
    (by rintro rfl; linarith) (by rintro rfl; linarith)
  -- by Lemma 5 these points are `P₂*` and `P₃*`
  have l1 := ml5_lemma5_line hK hpar h' hZo.1 (by rw [hZc, hXY])
  have l2 := ml5_lemma5_line hK hpar h' hZo'.1 (by rw [hZc', hXY])
  obtain ⟨-, -, a2⟩ := (ml5_mem_openArc_iff hP₃).1 hZo
  obtain ⟨-, b1, -⟩ := (ml5_mem_openArc_iff hP₄).1 hZo'
  have sw := mm_cross_swap (P₂ - P₁)
  rcases l1 with e1 | e1 <;> rcases l2 with e2 | e2
  · rw [e1] at a2; rw [e2] at b1; linarith [sw Y]
  · rw [e1] at hZo; rw [e2] at hZo'; exact ⟨hZo, hZo'⟩
  · -- `Z = P₃*`, `Z' = P₂*`: then `det(P₃, P₁*) > 0`, impossible
    rw [e1] at a2; rw [e2] at b1
    have : cross (P₂ - P₁) X = cross (P₂ - P₁) Y + cross (Y - X) (P₂ - P₁) := by
      simp only [cross, Pi.sub_apply]; ring
    linarith [sw X]
  · rw [e1] at a2; rw [e2] at b1; linarith [sw (Y - X)]

/-- **Mahler, paper A, Lemma 7** (one step). Let `Λ, Λ*, Λ**` be critical lattices of a convex
domain which is not a parallelogram, with configurations `(P₁, P₂)`, `(P₁*, P₂*)`, `(P₁**, P₂**)`,
`P₁*, P₁**` inside the arc `A₁ = P₁P₂`. If `P₁*` separates `P₁` from `P₁**` on `A₁`, then `P₂*`
separates `P₂` from `P₂**` on `A₂`.

Mahler's proof (for the smallest index at which the separation fails): otherwise the arc of `C`
between the consecutive points `P₁**`, `P₂**` of `Λ**` would contain no point of `Λ*`, against
Lemma 6. Indeed, `P₁*` lies inside the arc `A₆** = P₆**P₁**` of `Λ**` (`P₆** = P₁** - P₂**` lies
inside `A₆`), so by Lemma 6 for `Λ**` the next point `P₂*` of `Λ*` lies inside
`A₁** = P₁**P₂**`. -/
theorem ml5_lemma7_step (hK : IsSymmetricConvexDomain K) (hpar : ¬IsParallelogram K)
    {X₁ X₂ Y₁ Y₂ : Fin 2 → ℝ} (h : ml5_IsConf K P₁ P₂) (hX : ml5_IsConf K X₁ X₂)
    (hY : ml5_IsConf K Y₁ Y₂) (hX₁ : X₁ ∈ openArc K P₁ P₂) (hY₁ : Y₁ ∈ openArc K P₁ P₂)
    (hsep : X₁ ∈ openArc K P₁ Y₁) : X₂ ∈ openArc K P₂ Y₂ := by
  have hΔ := ml5_conf_pos hK h
  obtain ⟨hY₂, hY₃⟩ := ml5_lemma6 hK hpar h hY hY₁
  obtain ⟨hX₂, -⟩ := ml5_lemma6 hK hpar h hX hX₁
  have hP₃ : 0 < cross P₂ (P₂ - P₁) := by rw [ml5_cross_P₃]; exact hΔ
  have hP₄ : 0 < cross (P₂ - P₁) (-P₁) := by rw [ml5_cross_P₄]; exact hΔ
  obtain ⟨-, x1, x2⟩ := (ml5_mem_openArc_iff hΔ).1 hX₁
  obtain ⟨-, y1, -⟩ := (ml5_mem_openArc_iff hΔ).1 hY₁
  obtain ⟨-, -, s2⟩ := (ml5_mem_openArc_iff y1).1 hsep
  obtain ⟨-, w1, w2⟩ := (ml5_mem_openArc_iff hP₄).1 hY₃
  obtain ⟨-, z1, -⟩ := (ml5_mem_openArc_iff hP₃).1 hY₂
  obtain ⟨hX₂F, v1, -⟩ := (ml5_mem_openArc_iff hP₃).1 hX₂
  -- `P₁*` lies inside the arc `A₆**` between `P₆** = P₁** - P₂**` and `P₁**`
  have hcY : 0 < cross (Y₁ - Y₂) Y₁ := ml5_conf_pos hK (ml5_conf_prev hK hY)
  have k : 0 < cross (Y₁ - Y₂) X₁ := by
    have pl := ml5_plucker P₁ P₂ X₁ (Y₂ - Y₁)
    have e1 : cross P₁ (Y₂ - Y₁) = cross (Y₂ - Y₁) (-P₁) := by
      simp only [cross, Pi.sub_apply, Pi.neg_apply]; ring
    have e2 : cross P₂ (Y₂ - Y₁) = cross P₁ (Y₂ - Y₁) + cross (P₂ - P₁) (Y₂ - Y₁) := by
      simp only [cross, Pi.sub_apply]; ring
    have e3 : cross (Y₁ - Y₂) X₁ = cross X₁ (Y₂ - Y₁) := by
      simp only [cross, Pi.sub_apply]; ring
    rw [e3]
    have q1 : 0 < cross P₁ (Y₂ - Y₁) := by rw [e1]; exact w2
    have q2 : 0 < cross P₂ (Y₂ - Y₁) := by rw [e2]; linarith
    by_contra hc
    push Not at hc
    nlinarith [mul_pos x2 q1, mul_pos x1 q2, mul_nonpos_of_nonneg_of_nonpos hΔ.le hc]
  have hX₁' : X₁ ∈ openArc K (Y₁ - Y₂) Y₁ := (ml5_mem_openArc_iff hcY).2 ⟨hX₁.1, k, s2⟩
  have := (ml5_lemma6 hK hpar (ml5_conf_prev hK hY) hX hX₁').1
  rw [sub_sub_cancel] at this
  obtain ⟨-, -, u2⟩ := (ml5_mem_openArc_iff (ml5_conf_pos hK hY)).1 this
  exact (ml5_mem_openArc_iff z1).2 ⟨hX₂F, v1, u2⟩

/-- **Mahler, paper A, Lemma 7.** In the situation of `ml5_lemma7_step`, if `P₁*` separates `P₁`
from `P₁**` on `A₁`, then `P_l*` separates `P_l` from `P_l**` on `A_l` for `l = 2, …, 6`
(`P₃ = P₂ - P₁`, `P_{l+3} = -P_l`): the step applied to the configurations `(P₁, P₂)` and
`(P₂, P₃)`, and the symmetry in `O`. -/
theorem ml5_lemma7 (hK : IsSymmetricConvexDomain K) (hpar : ¬IsParallelogram K)
    {X₁ X₂ Y₁ Y₂ : Fin 2 → ℝ} (h : ml5_IsConf K P₁ P₂) (hX : ml5_IsConf K X₁ X₂)
    (hY : ml5_IsConf K Y₁ Y₂) (hX₁ : X₁ ∈ openArc K P₁ P₂) (hY₁ : Y₁ ∈ openArc K P₁ P₂)
    (hsep : X₁ ∈ openArc K P₁ Y₁) :
    X₂ ∈ openArc K P₂ Y₂ ∧ X₂ - X₁ ∈ openArc K (P₂ - P₁) (Y₂ - Y₁) ∧
      -X₁ ∈ openArc K (-P₁) (-Y₁) ∧ -X₂ ∈ openArc K (-P₂) (-Y₂) ∧
      -(X₂ - X₁) ∈ openArc K (-(P₂ - P₁)) (-(Y₂ - Y₁)) := by
  have l2 := ml5_lemma7_step hK hpar h hX hY hX₁ hY₁ hsep
  have l3 := ml5_lemma7_step hK hpar (ml5_conf_next hK h) (ml5_conf_next hK hX)
    (ml5_conf_next hK hY) (ml5_lemma6 hK hpar h hX hX₁).1 (ml5_lemma6 hK hpar h hY hY₁).1 l2
  exact ⟨l2, l3, ml5_neg_mem_openArc hK hsep, ml5_neg_mem_openArc hK l2,
    ml5_neg_mem_openArc hK l3⟩

/-- **Lemma 7 with the roles of `Λ*` and `Λ**` exchanged and the step taken backwards** (as Mahler
uses it in the proof of Lemma 13): if `P₂*` separates `P₂` from `P₂**`, then `P₁*` separates `P₁`
from `P₁**`. Otherwise `P₁** ` would separate `P₁` from `P₁*` (`P₁* ≠ P₁**`, since by Lemma 5 the
configuration at a point is unique), and by Lemma 7 `P₂**` would separate `P₂` from `P₂*`. -/
lemma ml5_lemma7_back (hK : IsSymmetricConvexDomain K) (hpar : ¬IsParallelogram K)
    {X₁ X₂ Y₁ Y₂ : Fin 2 → ℝ} (h : ml5_IsConf K P₁ P₂) (hX : ml5_IsConf K X₁ X₂)
    (hY : ml5_IsConf K Y₁ Y₂) (hX₁ : X₁ ∈ openArc K P₁ P₂) (hY₁ : Y₁ ∈ openArc K P₁ P₂)
    (hsep : X₂ ∈ openArc K P₂ Y₂) : X₁ ∈ openArc K P₁ Y₁ := by
  have hΔ := ml5_conf_pos hK h
  have hP₃ : 0 < cross P₂ (P₂ - P₁) := by rw [ml5_cross_P₃]; exact hΔ
  obtain ⟨hX₁F, x1, -⟩ := (ml5_mem_openArc_iff hΔ).1 hX₁
  obtain ⟨hY₁F, y1, -⟩ := (ml5_mem_openArc_iff hΔ).1 hY₁
  obtain ⟨-, z1, -⟩ := (ml5_mem_openArc_iff hP₃).1 (ml5_lemma6 hK hpar h hY hY₁).1
  obtain ⟨-, z1', -⟩ := (ml5_mem_openArc_iff hP₃).1 (ml5_lemma6 hK hpar h hX hX₁).1
  obtain ⟨-, -, q⟩ := (ml5_mem_openArc_iff z1).1 hsep
  rcases lt_trichotomy (cross X₁ Y₁) 0 with c | c | c
  · exfalso
    have hs : Y₁ ∈ openArc K P₁ X₁ :=
      (ml5_mem_openArc_iff x1).2 ⟨hY₁F, y1, by rw [mm_cross_swap]; linarith⟩
    obtain ⟨-, -, q'⟩ := (ml5_mem_openArc_iff z1').1 (ml5_lemma7_step hK hpar h hY hX hY₁ hX₁ hs)
    rw [mm_cross_swap] at q'
    linarith
  · exfalso
    obtain rfl := ml5_eq_of_cross_eq_zero hK hX₁F hY₁F c x1 y1
    rw [ml5_lemma5_partner hK hpar hX hY, mm_cross_self] at q
    exact lt_irrefl _ q
  · exact (ml5_mem_openArc_iff y1).2 ⟨hX₁F, x1, c⟩

end Lemma67

/-! ### Mahler's quadratic and the "only if" half -/

/-- If the midpoint of two points of `K` is a boundary point, so is the whole segment. -/
lemma ml3_seg_frontier (hK : IsSymmetricConvexDomain K) {P Q : Fin 2 → ℝ} (hP : P ∈ K)
    (hQ : Q ∈ K) (hM : (1 / 2 : ℝ) • (P + Q) ∈ frontier K) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : (1 - t) • P + t • Q ∈ frontier K := by
  obtain ⟨f, hf1, hf2, hf3⟩ := mm_support hK hM
  have h1 := hf2 P hP
  have h2 := hf2 Q hQ
  rw [map_smul, map_add, smul_eq_mul] at hf1
  refine mm_mem_frontier hK (hK.1 hP hQ (by linarith) ht0 (by ring)) fun hi ↦ ?_
  have := hf3 _ hi
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
  have hP1 : f P = 1 := by linarith
  have hQ1 : f Q = 1 := by linarith
  rw [hP1, hQ1] at this
  linarith

/-! ### Mahler's Lemma 13 of paper A, class A -/

/-- **Mahler's quadratic** (paper A, end of the proof of Lemma 13). Let `(P₁, P₂)` and
`(P₁', P₂')` be critical configurations (`P₃ = P₂ - P₁`, `P₃' = P₂' - P₁'`) such that the arcs
`Γ_l` from `P_l` to `P_l'` (`l = 1, 2, 3`) are segments of `C`, and let `Q_l = P_l' - P_l`, with
`c = {Q₁, Q₃} > 0`. The points `P_l* = P_l + t Q_l` lie on `C` and `P₁* + P₃* = P₂*`, so by Lemma 3
`|f(t)| ≥ Δ(K)` for `f(t) = {P₁*, P₃*} = a + bt + ct²`. Since `f(0) = f(1) = Δ(K)` and
`f'' = 2c > 0`, `f(1/2) = Δ(K) - c/4 < Δ(K)`, a contradiction. Gap in paper A (filled here):
Mahler takes `{P₁*, P₃*} > Δ(K)` with its sign; Lemma 3 bounds `|f(t)|`, and `f(t) ≥ Δ(K)` follows
since the continuous `f` starts at `f(0) = Δ(K)` and never takes values in `(-Δ(K), Δ(K))`. -/
lemma ml3_quadratic (hK : IsSymmetricConvexDomain K) {P₁ P₂ Q Q₂ : Fin 2 → ℝ}
    (h : ml5_IsConf K P₁ P₂) (h' : ml5_IsConf K Q Q₂)
    (hs1 : (1 / 2 : ℝ) • (P₁ + Q) ∈ frontier K) (hs2 : (1 / 2 : ℝ) • (P₂ + Q₂) ∈ frontier K)
    (hs3 : (1 / 2 : ℝ) • ((P₂ - P₁) + (Q₂ - Q)) ∈ frontier K)
    (hc : 0 < cross (Q - P₁) ((Q₂ - Q) - (P₂ - P₁))) : False := by
  have hΔ := irr_minimalDeterminant_pos hK
  have mem : ∀ {x : Fin 2 → ℝ}, x ∈ frontier K → x ∈ K := fun hx ↦ mm_mem_of_frontier hK hx
  set Δ := minimalDeterminant K with hΔdef
  set c := cross (Q - P₁) ((Q₂ - Q) - (P₂ - P₁)) with hcdef
  set f : ℝ → ℝ := fun τ ↦ Δ - c * τ * (1 - τ) with hfdef
  -- Lemma 3 for the parallelograms `O P₁* P₂* P₃*`
  have hf : ∀ τ ∈ Icc (0 : ℝ) 1, Δ ≤ |f τ| := by
    intro τ hτ
    have g1 := ml3_seg_frontier hK (mem h.1) (mem h'.1) hs1 hτ.1 hτ.2
    have g2 := ml3_seg_frontier hK (mem h.2.1) (mem h'.2.1) hs2 hτ.1 hτ.2
    have g3 := ml3_seg_frontier hK (mem h.2.2.1) (mem h'.2.2.1) hs3 hτ.1 hτ.2
    obtain ⟨hle, -⟩ := (minkowski_mahler hK).2 _ _ _ g1 g2 g3 (by module)
    have key : cross ((1 - τ) • P₁ + τ • Q) ((1 - τ) • P₂ + τ • Q₂) =
        (1 - τ) ^ 2 * cross P₁ P₂ + τ ^ 2 * cross Q Q₂ +
          τ * (1 - τ) * (cross P₁ P₂ + cross Q Q₂ - c) := by
      simp only [hcdef, cross, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    rw [key, h.2.2.2, h'.2.2.2] at hle
    convert hle using 2
    simp only [hfdef]; ring
  -- `f ≥ Δ(K)` at `t = 1/2` (the sign, by continuity)
  have hhalf : Δ ≤ f (1 / 2) := by
    by_contra hlt
    push Not at hlt
    have h1 := hf (1 / 2) ⟨by norm_num, by norm_num⟩
    have hneg : f (1 / 2) < 0 := by
      by_contra h0; push Not at h0; rw [abs_of_nonneg h0] at h1; linarith
    have hcont : ContinuousOn f (Icc 0 (1 / 2)) := by
      simp only [hfdef]; fun_prop
    obtain ⟨τ, hτ, hτ0⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1 / 2) hcont
      ⟨hneg.le, by simp only [hfdef]; linarith⟩
    have := hf τ ⟨hτ.1, by linarith [hτ.2]⟩
    rw [hτ0, abs_zero] at this
    linarith
  simp only [hfdef] at hhalf
  nlinarith

/-- The inner points of an arc which is a segment of `C` are the inner points of the segment. -/
lemma ml5_openArc_seg (hK : IsSymmetricConvexDomain K) {A B X : Fin 2 → ℝ} (hA : A ∈ frontier K)
    (hB : B ∈ frontier K) (hM : (1 / 2 : ℝ) • (A + B) ∈ frontier K) (hX : X ∈ openArc K A B) :
    ∃ t ∈ Ioo (0 : ℝ) 1, X = A + t • (B - A) := by
  obtain ⟨hXF, a, b, ha, hb, rfl⟩ := hX
  obtain ⟨ψ, hψ1, hψ2, -⟩ := mm_support hK hM
  have e1 := hψ2 A (mm_mem_of_frontier hK hA)
  have e2 := hψ2 B (mm_mem_of_frontier hK hB)
  rw [map_smul, map_add, smul_eq_mul] at hψ1
  have hψA : ψ A = 1 := by linarith
  have hψB : ψ B = 1 := by linarith
  have e3 := hψ2 _ (mm_mem_of_frontier hK hXF)
  rw [map_add, map_smul, map_smul, hψA, hψB, smul_eq_mul, smul_eq_mul] at e3
  have e4 := one_le_add hK.1 (mm_zero_mem_interior hK) (mm_mem_of_frontier hK hA)
    (mm_mem_of_frontier hK hB) ha.le hb.le hXF.2
  refine ⟨b, ⟨hb, by linarith⟩, ?_⟩
  rw [show a = 1 - b by linarith]
  module

/-- **Mahler, paper A, Lemma 13, class A** (the second case of its proof). Let `K` be a convex
domain which is not a parallelogram whose extreme points (class B) all lie on critical lattices,
and let `Γ₁ = P₁P₁'` be a segment of `C` whose ends lie on critical lattices and whose inner points
do not (`det(P₁, P₁') > 0`). This is impossible.

Mahler's proof. Let `(P₁, P₂)`, `(P₁', P₂')` be the configurations of the critical lattices `Λ, Λ'`
at `P₁, P₁'` (unique, Lemma 5). By the hypothesis about `Γ₁`, `P₁'` is an inner point of the arc
`A₁ = P₁P₂` (the gap left there, "`P₁'` belongs to `A₁` or `A₆`", is filled by our naming of the
ends: otherwise `P₂` would lie on `Γ₁`, and `A₁` would be the segment `Γ₁` if `P₂ = P₁'`), and by
Lemma 6 `P₂', P₃'` are inner points of `A₂, A₃`. By Lemma 7 the inner points of the arcs
`Γ₂ = P₂P₂'` and `Γ₃ = P₃P₃'` lie on no critical lattice, as those of `Γ₁` do not (Mahler: "it is
immediately clear from Lemma 7"; here Lemma 7 is applied with the indices shifted cyclically and
the roles of `Λ*, Λ**` exchanged, `ml5_lemma7_back`). Hence they are of class A (not extreme), and
`Γ₂, Γ₃` are segments (`BoundaryArc.midpoint_mem_frontier_of_forall_not_mem_extremePoints`).
As in the proof of Lemma 6, `P₁', P₃'` lie inside the triangles `P₁, P₁ + P₂, P₂` and
`P₃, -P₁ + P₃, -P₁` (`ml5_triangle`), so `Q₁ = P₁' - P₁` and `Q₃ = P₃' - P₃` lie inside the
triangles `O, P₂, P₃` and `O, -P₁, -P₂`, and `{Q₁, Q₃} > 0`. Mahler's quadratic (`ml3_quadratic`)
gives the contradiction. (Only `Γ₁, Γ₂, Γ₃` are needed; `Γ₄, Γ₅, Γ₆` are their reflections.) -/
theorem ml5_classA (hK : IsSymmetricConvexDomain K) (hpar : ¬IsParallelogram K)
    (hext : ∀ e ∈ K.extremePoints ℝ, ∃ Λ, IsCritical K Λ ∧ e ∈ Λ) {P₁ Q : Fin 2 → ℝ}
    (hP₁ : P₁ ∈ frontier K) (hQ : Q ∈ frontier K) (hP₁c : ∃ Λ, IsCritical K Λ ∧ P₁ ∈ Λ)
    (hQc : ∃ Λ, IsCritical K Λ ∧ Q ∈ Λ) (hor : 0 < cross P₁ Q)
    (hseg : (1 / 2 : ℝ) • (P₁ + Q) ∈ frontier K)
    (hgap : ∀ X ∈ openArc K P₁ Q, ¬∃ Λ, IsCritical K Λ ∧ X ∈ Λ) : False := by
  obtain ⟨P₂, h⟩ := ml5_conf_of_pi hK hP₁ hP₁c
  obtain ⟨Q₂, h'⟩ := ml5_conf_of_pi hK hQ hQc
  have hΔ := ml5_conf_pos hK h
  have hP₃ : 0 < cross P₂ (P₂ - P₁) := by rw [ml5_cross_P₃]; exact hΔ
  have hP₄ : 0 < cross (P₂ - P₁) (-P₁) := by rw [ml5_cross_P₄]; exact hΔ
  -- `P₁'` is an inner point of `A₁`
  have hQA₁ : Q ∈ openArc K P₁ P₂ := by
    refine (ml5_mem_openArc_iff hΔ).2 ⟨hQ, hor, ?_⟩
    by_contra hc
    push Not at hc
    have hP₂arc : P₂ ∈ arc K P₁ Q :=
      (ml5_mem_arc_iff hor).2 ⟨h.2.1, hΔ.le, by rw [mm_cross_swap]; linarith⟩
    by_cases hPQ : P₂ = Q
    · -- `A₁` would be the segment `Γ₁`
      subst hPQ
      apply hseg.2
      have := (ml5_lemma5_cor_arcs hK hpar h).1 (1 / 2) ⟨by norm_num, by norm_num⟩
      convert this using 1; module
    · have hne : P₂ ≠ P₁ := fun e ↦ by rw [e, mm_cross_self] at hΔ; exact lt_irrefl _ hΔ
      exact hgap P₂ (ml5_openArc_of_arc hK hP₁ hQ hP₂arc hne hPQ)
        (ml5_pi_of_conf hK (ml5_conf_next hK h))
  -- Lemma 6: `P₂'`, `P₃'` are inner points of `A₂`, `A₃`
  obtain ⟨hQ₂, hQ₃⟩ := ml5_lemma6 hK hpar h h' hQA₁
  obtain ⟨-, q21, q22⟩ := (ml5_mem_openArc_iff hP₃).1 hQ₂
  obtain ⟨-, q31, q32⟩ := (ml5_mem_openArc_iff hP₄).1 hQ₃
  -- Lemma 7: the inner points of `Γ₂` are not on critical lattices
  have gap2 : ∀ X ∈ openArc K P₂ Q₂, ¬∃ Λ, IsCritical K Λ ∧ X ∈ Λ := by
    intro X hX hXc
    obtain ⟨hXF, x1, x2⟩ := (ml5_mem_openArc_iff q21).1 hX
    have hXA₂ : X ∈ openArc K P₂ (P₂ - P₁) := by
      refine (ml5_mem_openArc_iff hP₃).2 ⟨hXF, x1, ?_⟩
      have pl := ml5_plucker P₂ Q₂ X (P₂ - P₁)
      by_contra hc; push Not at hc
      nlinarith [mul_pos x2 hP₃, mul_pos x1 q22, mul_nonpos_of_nonneg_of_nonpos q21.le hc]
    obtain ⟨Y, hXY⟩ := ml5_conf_of_pi hK hXF hXc
    have h6 := (ml5_lemma6 hK hpar (ml5_conf_next hK h) hXY hXA₂).2
    have hZ : X - Y ∈ openArc K P₁ P₂ := by
      have := ml5_neg_mem_openArc hK h6
      rwa [neg_sub Y X, show -(P₂ - P₁ - P₂) = P₁ by abel, neg_neg] at this
    exact hgap _ (ml5_lemma7_back hK hpar h (ml5_conf_prev hK hXY) h' hZ hQA₁ hX)
      (ml5_pi_of_conf hK (ml5_conf_prev hK hXY))
  -- Lemma 7: the inner points of `Γ₃` are not on critical lattices
  have hc3 : ml5_IsConf K (P₂ - P₁) (-P₁) := by
    have := ml5_conf_next hK (ml5_conf_next hK h); rwa [sub_sub_cancel_left] at this
  have gap3 : ∀ X ∈ openArc K (P₂ - P₁) (Q₂ - Q), ¬∃ Λ, IsCritical K Λ ∧ X ∈ Λ := by
    intro X hX hXc
    obtain ⟨hXF, x1, x2⟩ := (ml5_mem_openArc_iff q31).1 hX
    have hXA₃ : X ∈ openArc K (P₂ - P₁) (-P₁) := by
      refine (ml5_mem_openArc_iff hP₄).2 ⟨hXF, x1, ?_⟩
      have pl := ml5_plucker (P₂ - P₁) (Q₂ - Q) X (-P₁)
      by_contra hc; push Not at hc
      nlinarith [mul_pos x2 hP₄, mul_pos x1 q32, mul_nonpos_of_nonneg_of_nonpos q31.le hc]
    obtain ⟨Y, hXY⟩ := ml5_conf_of_pi hK hXF hXc
    have h6 := (ml5_lemma6 hK hpar hc3 hXY hXA₃).2
    have hZ : X - Y ∈ openArc K P₂ (P₂ - P₁) := by
      have := ml5_neg_mem_openArc hK h6
      rwa [neg_sub Y X, show -(-P₁ - (P₂ - P₁)) = P₂ by abel, neg_neg] at this
    exact gap2 _ (ml5_lemma7_back hK hpar (ml5_conf_next hK h) (ml5_conf_prev hK hXY)
      (ml5_conf_next hK h') hZ hQ₂ hX) (ml5_pi_of_conf hK (ml5_conf_prev hK hXY))
  -- the arcs `Γ₂`, `Γ₃` are segments
  have hfin : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  have seg2 := midpoint_mem_frontier_of_forall_not_mem_extremePoints hfin hK.1 hK.2.1
    (mm_zero_mem_interior hK) h.2.1 h'.2.1 (mm_linearIndependent_real q21.ne')
    fun X hX he ↦ gap2 X hX (hext X he)
  have seg3 := midpoint_mem_frontier_of_forall_not_mem_extremePoints hfin hK.1 hK.2.1
    (mm_zero_mem_interior hK) h.2.2.1 h'.2.2.1 (mm_linearIndependent_real q31.ne')
    fun X hX he ↦ gap3 X hX (hext X he)
  -- the positions of `P₁'`, `P₃'`, and `{Q₁, Q₃} > 0`
  obtain ⟨u1, u1', v1, -, -⟩ := ml5_triangle hK hpar h hQA₁
  obtain ⟨u3, u3', v3, -, w3⟩ := ml5_triangle hK hpar hc3 hQ₃
  rw [ml5_cross_P₄] at u3' w3
  have hcQ : 0 < cross (Q - P₁) ((Q₂ - Q) - (P₂ - P₁)) := by
    have key : cross P₁ P₂ * cross (Q - P₁) ((Q₂ - Q) - (P₂ - P₁)) =
        (cross Q P₂ - cross P₁ P₂) * (cross (Q₂ - Q) (-P₁) - cross P₁ P₂) +
          cross P₁ Q * (cross (Q₂ - Q) (-P₁) + cross (P₂ - P₁) (Q₂ - Q) - cross P₁ P₂) := by
      simp only [cross, Pi.sub_apply, Pi.neg_apply]; ring
    by_contra hc; push Not at hc
    nlinarith [mul_pos_of_neg_of_neg (sub_neg.2 u1') (sub_neg.2 u3'), mul_pos v1 (sub_pos.2 w3),
      mul_nonpos_of_nonneg_of_nonpos hΔ.le hc]
  exact ml3_quadratic hK h h' hseg seg2 seg3 hcQ

/-- **Mahler, paper A, Lemma 8 and Lemma 13, for convex subdomains** (the "only if" half of
Lemma 3): every boundary point of an irreducible domain lies on a critical lattice. A
parallelogram has `Π = C` (`ml5_par_pi`, Mahler's example in §3). Otherwise we follow the proof of
Lemma 13: extreme points (class B) lie on critical lattices (`ml3_extreme`); a point `u` of class A
lies inside a boundary segment `{f = 1} ∩ K` whose ends are extreme, hence on critical lattices,
the critical-lattice points of the segment form a closed set (Lemma 11, `ml3_isClosed`), and `u`
lies in a largest sub-segment `Γ₁ = [A, B]` whose ends are on critical lattices and whose inner
points are not; this contradicts `ml5_classA` (Lemmas 5–7 and Mahler's quadratic). -/
lemma ml3_onlyIf (hirr : IsIrreducible K) {u : Fin 2 → ℝ} (hu : u ∈ frontier K) :
    ∃ Λ, IsCritical K Λ ∧ u ∈ Λ := by
  have hK := hirr.1
  by_cases hnpar : IsParallelogram K
  · exact ml5_par_pi hnpar hu
  by_contra hnot
  have huK := mm_mem_of_frontier hK hu
  have hnext : u ∉ K.extremePoints ℝ := fun he ↦ hnot (ml3_extreme hirr he)
  obtain ⟨x₁, hx₁, x₂, hx₂, hseg, hne⟩ :
      ∃ x₁ ∈ K, ∃ x₂ ∈ K, u ∈ openSegment ℝ x₁ x₂ ∧ x₁ ≠ u := by
    by_contra h; push Not at h
    exact hnext ⟨huK, fun x₁ hx₁ x₂ hx₂ hs ↦ h x₁ hx₁ x₂ hx₂ hs⟩
  obtain ⟨a₁, a₂, ha₁, ha₂, ha12, hu12⟩ := hseg
  set d := x₂ - x₁ with hd
  have hd0 : d ≠ 0 := by
    intro h; apply hne
    have h2 : x₂ = x₁ := sub_eq_zero.1 h
    rw [← hu12, h2, ← add_smul, ha12, one_smul]
  obtain ⟨f, hf1, hf2, hf3⟩ := mm_support hK hu
  have hfx : f x₁ = 1 ∧ f x₂ = 1 := by
    have h1 := hf2 _ hx₁
    have h2 := hf2 _ hx₂
    have := congrArg f hu12
    rw [map_add, map_smul, map_smul, hf1, smul_eq_mul, smul_eq_mul] at this
    constructor <;> nlinarith
  have hfd : f d = 0 := by rw [hd, map_sub, hfx.1, hfx.2, sub_self]
  -- the face `p t = u + t d`
  set p : ℝ → Fin 2 → ℝ := fun t ↦ u + t • d with hp
  have hpc : Continuous p := by fun_prop
  have hfp : ∀ t, f (p t) = 1 := fun t ↦ by simp [hp, hf1, hfd]
  have hpF : ∀ t, p t ∈ K → p t ∈ frontier K := fun t ht ↦
    mm_mem_frontier hK ht fun hi ↦ by have := hf3 _ hi; rw [hfp] at this; exact lt_irrefl _ this
  set T := {t : ℝ | p t ∈ K} with hT
  have hTc : IsClosed T := hK.2.1.isClosed.preimage hpc
  have hx₁T : -a₂ ∈ T := by
    change u + (-a₂) • d ∈ K
    convert hx₁ using 1; rw [← hu12, hd]; rw [show a₁ = 1 - a₂ by linarith]; module
  have hx₂T : a₁ ∈ T := by
    change u + a₁ • d ∈ K
    convert hx₂ using 1; rw [← hu12, hd]; rw [show a₂ = 1 - a₁ by linarith]; module
  obtain ⟨R, hR⟩ := hK.2.1.isBounded.subset_closedBall 0
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd0
  have hTbd : ∀ t ∈ T, |t| ≤ (R + ‖u‖) / ‖d‖ := by
    intro t ht
    have h1 := hR ht
    rw [mem_closedBall_zero_iff] at h1
    rw [le_div_iff₀ hdn]
    have h2 : ‖t • d‖ ≤ ‖u + t • d‖ + ‖u‖ := by
      have := norm_sub_le (u + t • d) u
      rwa [add_sub_cancel_left] at this
    rw [norm_smul, Real.norm_eq_abs] at h2
    linarith
  have hTa : BddAbove T := ⟨_, fun t ht ↦ (le_abs_self t).trans (hTbd t ht)⟩
  have hTbb : BddBelow T := ⟨-((R + ‖u‖) / ‖d‖), fun t ht ↦ by
    have := neg_abs_le t; linarith [hTbd t ht]⟩
  set tlo := sInf T with htlo
  set thi := sSup T with hthi
  have htloT : tlo ∈ T := hTc.csInf_mem ⟨_, hx₁T⟩ hTbb
  have hthiT : thi ∈ T := hTc.csSup_mem ⟨_, hx₁T⟩ hTa
  have htlo0 : tlo < 0 := lt_of_le_of_lt (csInf_le hTbb hx₁T) (by linarith)
  have hthi0 : 0 < thi := lt_of_lt_of_le ha₁ (le_csSup hTa hx₂T)
  have hpK : ∀ r ∈ Icc tlo thi, p r ∈ K := by
    rintro r ⟨hr1, hr2⟩
    have hlen : 0 < thi - tlo := by linarith
    have := hK.1 htloT hthiT
      (show 0 ≤ (thi - r) / (thi - tlo) from div_nonneg (by linarith) hlen.le)
      (show 0 ≤ (r - tlo) / (thi - tlo) from div_nonneg (by linarith) hlen.le)
      (by field_simp; ring)
    convert this using 1
    simp only [hp]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  -- the ends of the face are extreme points
  have hpar : ∀ y, f y = 1 → ∃ τ, y = p τ := by
    intro y hy
    obtain ⟨a, ha⟩ := ml3_dual_vec f
    have ha0 : a ≠ 0 := by rintro rfl; have := ha u; simp [hf1] at this
    have hcr := ml3_cross_eq_zero_of_dot ha0 (show a ⬝ᵥ d = 0 by rw [ha, hfd])
      (show a ⬝ᵥ (y - u) = 0 by rw [ha, map_sub, hy, hf1, sub_self])
    obtain ⟨τ, hτ⟩ := ml3_parallel hcr hd0
    exact ⟨τ, by simp only [hp]; rw [← hτ]; abel⟩
  have hext : ∀ t₀ ∈ T, ((∀ t ∈ T, t₀ ≤ t) ∨ (∀ t ∈ T, t ≤ t₀)) →
      p t₀ ∈ K.extremePoints ℝ := by
    intro t₀ ht₀ hmin
    refine ⟨ht₀, fun y₁ hy₁ y₂ hy₂ hs ↦ ?_⟩
    obtain ⟨b₁, b₂, hb₁, hb₂, hb12, hy12⟩ := hs
    have h1 := hf2 _ hy₁
    have h2 := hf2 _ hy₂
    have := congrArg f hy12
    rw [map_add, map_smul, map_smul, hfp, smul_eq_mul, smul_eq_mul] at this
    obtain ⟨τ₁, rfl⟩ := hpar y₁ (by nlinarith)
    obtain ⟨τ₂, rfl⟩ := hpar y₂ (by nlinarith)
    have hτ : t₀ = b₁ * τ₁ + b₂ * τ₂ := by
      have hv : (t₀ - (b₁ * τ₁ + b₂ * τ₂)) • d = p t₀ - (b₁ • p τ₁ + b₂ • p τ₂) := by
        simp only [hp]; rw [show b₂ = 1 - b₁ by linarith]; module
      rw [hy12, sub_self] at hv
      exact sub_eq_zero.1 ((smul_eq_zero.1 hv).resolve_right hd0)
    have hid : b₁ * (τ₁ - t₀) + b₂ * (τ₂ - t₀) = 0 := by
      rw [hτ]; linear_combination (-(b₁ * τ₁ + b₂ * τ₂)) * hb12
    rcases hmin with h | h
    · have e1 := h τ₁ hy₁
      have e2 := h τ₂ hy₂
      have : b₁ * (τ₁ - t₀) = 0 := by
        linarith [mul_nonneg hb₁.le (sub_nonneg.2 e1), mul_nonneg hb₂.le (sub_nonneg.2 e2)]
      rw [show τ₁ = t₀ by
        have := (mul_eq_zero.1 this).resolve_left hb₁.ne'; linarith]
    · have e1 := h τ₁ hy₁
      have e2 := h τ₂ hy₂
      have : b₁ * (t₀ - τ₁) = 0 := by
        linarith [mul_nonneg hb₁.le (sub_nonneg.2 e1), mul_nonneg hb₂.le (sub_nonneg.2 e2)]
      rw [show τ₁ = t₀ by
        have := (mul_eq_zero.1 this).resolve_left hb₁.ne'; linarith]
  set Pk := {x | x ∈ frontier K ∧ ∃ Λ, IsCritical K Λ ∧ x ∈ Λ} with hPi
  have hPic : IsClosed Pk := ml3_isClosed hK
  have hpPi : ∀ t, p t ∈ Pk ↔ p t ∈ frontier K ∧ ∃ Λ, IsCritical K Λ ∧ p t ∈ Λ := fun t ↦ Iff.rfl
  have hplo : p tlo ∈ Pk := ⟨hpF _ htloT, ml3_extreme hirr (hext _ htloT (Or.inl fun t ht ↦
    csInf_le hTbb ht))⟩
  have hphi : p thi ∈ Pk := ⟨hpF _ hthiT, ml3_extreme hirr (hext _ hthiT (Or.inr fun t ht ↦
    le_csSup hTa ht))⟩
  have hp0 : p 0 ∉ Pk := fun h ↦ hnot (by simpa [hp] using h.2)
  -- the gap `(t_A, t_B)` around `0`
  set S₁ := {t : ℝ | t ∈ Icc tlo 0 ∧ p t ∈ Pk} with hS₁
  set S₂ := {t : ℝ | t ∈ Icc 0 thi ∧ p t ∈ Pk} with hS₂
  have hS₁c : IsClosed S₁ := isClosed_Icc.inter (hPic.preimage hpc)
  have hS₂c : IsClosed S₂ := isClosed_Icc.inter (hPic.preimage hpc)
  have hS₁a : BddAbove S₁ := ⟨0, fun t ht ↦ ht.1.2⟩
  have hS₂b : BddBelow S₂ := ⟨0, fun t ht ↦ ht.1.1⟩
  have hS₁n : tlo ∈ S₁ := ⟨⟨le_rfl, htlo0.le⟩, hplo⟩
  have hS₂n : thi ∈ S₂ := ⟨⟨hthi0.le, le_rfl⟩, hphi⟩
  set tA := sSup S₁ with htA
  set tB := sInf S₂ with htB
  have htAS : tA ∈ S₁ := hS₁c.csSup_mem ⟨_, hS₁n⟩ hS₁a
  have htBS : tB ∈ S₂ := hS₂c.csInf_mem ⟨_, hS₂n⟩ hS₂b
  have htA0 : tA < 0 := lt_of_le_of_ne htAS.1.2 fun h ↦ hp0 (h ▸ htAS.2)
  have htB0 : 0 < tB := lt_of_le_of_ne htBS.1.1 fun h ↦ hp0 (h.symm ▸ htBS.2)
  have hgap0 : ∀ r, tA < r → r < tB → p r ∉ Pk := by
    intro r hr1 hr2 hr
    rcases le_total r 0 with h | h
    · have := le_csSup hS₁a ⟨⟨by linarith [htAS.1.1], h⟩, hr⟩; linarith
    · have := csInf_le hS₂b ⟨⟨h, by linarith [htBS.1.2]⟩, hr⟩; linarith
  set A := p tA with hA
  set B := p tB with hB
  have hAF : A ∈ frontier K := htAS.2.1
  have hBF : B ∈ frontier K := htBS.2.1
  have hBA : B - A = (tB - tA) • d := by simp only [hA, hB, hp]; module
  have hgap : ∀ t : ℝ, 0 < t → t < 1 → ¬ ∃ Λ, IsCritical K Λ ∧ A + t • (B - A) ∈ Λ := by
    intro t ht0 ht1 hΛ
    have heq : A + t • (B - A) = p (tA + t * (tB - tA)) := by
      rw [hBA]; simp only [hA, hp]; module
    have hr1 : tA < tA + t * (tB - tA) := by nlinarith
    have hr2 : tA + t * (tB - tA) < tB := by nlinarith
    refine hgap0 _ hr1 hr2 ⟨hpF _ (hpK _ ⟨by linarith [htAS.1.1], by linarith [htBS.1.2]⟩), ?_⟩
    rw [← heq]; exact hΛ
  -- the segment `Γ₁ = [A, B]`: ends on critical lattices, inner points off them
  have hfA : f A = 1 := hfp tA
  have hfB : f B = 1 := hfp tB
  have hcAB : cross A B ≠ 0 := by
    intro h
    obtain ⟨τ, hτ⟩ := ml3_parallel h (mm_ne_zero_of_frontier hK hAF)
    have h1 := congrArg f hτ
    rw [map_smul, hfA, hfB, smul_eq_mul, mul_one] at h1
    rw [← h1, one_smul] at hτ
    have : (tB - tA) • d = 0 := by rw [← hBA, hτ, sub_self]
    exact smul_ne_zero (sub_pos.2 (htA0.trans htB0)).ne' hd0 this
  have hmid : (1 / 2 : ℝ) • (A + B) ∈ frontier K := by
    have e : (1 / 2 : ℝ) • (A + B) = p ((tA + tB) / 2) := by simp only [hA, hB, hp]; module
    rw [e]
    exact hpF _ (hpK _ ⟨by linarith [htAS.1.1], by linarith [htBS.1.2]⟩)
  have hgapArc : ∀ X ∈ openArc K A B, ¬∃ Λ, IsCritical K Λ ∧ X ∈ Λ := by
    intro X hX hΛ
    obtain ⟨t, ht, rfl⟩ := ml5_openArc_seg hK hAF hBF hmid hX
    exact hgap t ht.1 ht.2 hΛ
  have hext : ∀ e ∈ K.extremePoints ℝ, ∃ Λ, IsCritical K Λ ∧ e ∈ Λ :=
    fun e he ↦ ml3_extreme hirr he
  -- Lemma 13, class A, with the ends named so that `det(P₁, P₁') > 0`
  rcases lt_or_gt_of_ne hcAB with hneg | hpos
  · refine ml5_classA hK hnpar hext hBF hAF htBS.2.2 htAS.2.2 (by rw [mm_cross_swap]; linarith)
      (by rw [add_comm]; exact hmid) fun X hX ↦ hgapArc X ?_
    obtain ⟨hXF, a, b, ha, hb, rfl⟩ := hX
    exact ⟨hXF, b, a, hb, ha, add_comm _ _⟩
  · exact ml5_classA hK hnpar hext hAF hBF htAS.2.2 htBS.2.2 hpos hmid hgapArc

end Lemma3

end MahlerIrreducible

/-- **Mahler (1947), Lemma 3.** The (symmetric) convex domain `K` is irreducible if and only if
every boundary point of `K` belongs to a critical lattice of `K`.

Mahler states the lemma without proof (footnote 3: "See Lemmas 8 and 12 of paper A", Mahler, *On
irreducible convex domains*, Proc. Kon. Ned. Akad. Wet. 50 (1947), 98–107). All domains of the
paper are symmetric in the origin; irreducibility is `MahlerIrreducible.IsIrreducible` (no proper
symmetric convex subdomain has the same minimal determinant).

Proof. "If" (paper A, Lemma 12, for convex subdomains): `ml3_irreducible_of_forall`. "Only if"
(paper A, Lemma 8 together with Lemma 13, which passes from convex to star subdomains):
`ml3_onlyIf`; see the module docstring for the arguments and the departures from paper A. -/
theorem mahler_irreducible_iff {K : Set (Fin 2 → ℝ)} (hK : IsSymmetricConvexDomain K) :
    MahlerIrreducible.IsIrreducible K ↔
      ∀ u ∈ frontier K, ∃ Λ, MinkowskiMahler.IsCritical K Λ ∧ u ∈ Λ :=
  ⟨fun h _ hu ↦ ml3_onlyIf h hu, ml3_irreducible_of_forall hK⟩

end External
