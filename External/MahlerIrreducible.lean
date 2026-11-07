module

public import External.MinkowskiMahler
public import Basic.Algebra.Module.ZLattice.PlaneCritical
public import Basic.Analysis.Convex.BoundaryArc
public import Mathlib.Analysis.Convex.Extreme

/-!
# Irreducible convex domains (Mahler, paper A)

Cited in the remark after Definition 2.3.5 of Hales–Vajjha, *Packings of Smoothed Polygons*, from
K. Mahler, *On the minimum determinant and the circumscribed hexagons of a convex domain*,
Proc. Kon. Ned. Akad. Wet. 50 (1947), 692–703, Lemma 3 (stated there without proof; its footnote 3
reads "See Lemmas 8 and 12 of paper A", paper A being Mahler, *On irreducible convex domains*,
Proc. Kon. Ned. Akad. Wet. 50 (1947), 98–107): *the convex domain `K` is irreducible if and only if
every boundary point of `K` belongs to a critical lattice of `K`.*

This file has the definition of irreducibility and the lemmas of paper A that the proof of
Lemma 3 uses. Paper A quotes its Lemmas 8, 10, 11 and 12 from K. Mahler, *Lattice points in
n-dimensional star bodies II. Reducibility theorems I*, Proc. Kon. Ned. Akad. Wet. 49 (1946),
331–343, Theorems B–E; these are in `External.Mahler1946.TheoremC` and
`External.Mahler1946.TheoremE`, which import this file. Lemma 3 itself (`mahler_irreducible_iff`,
and the weak form `mahler_irreducible` that Lemma 2.2.5 uses) is assembled in
`External.MahlerIrreducible.Lemma3`, whose docstring says which part of the proof follows which
source and collects the errors and gaps of the three sources.

Definitions, in the terms of the source; symmetric convex domains, lattices, `Δ(K)` and critical
lattices are those of `External.MinkowskiMahler`. A symmetric convex domain `K` is irreducible
(`IsIrreducible`) if every symmetric convex domain `K' ⊆ K` other than `K` has a smaller minimal
determinant, `Δ(K') < Δ(K)`.

## What is proved

Paper A's own lemmas, by Mahler's arguments: Lemma 1 (`MahlerIrreducible.ml5_lemma1`,
parallelograms are irreducible; `Δ` of a parallelogram, `ml5_par_minDet`; Mahler's example in §3,
`Π = C` for a parallelogram, `ml5_par_pi`), Lemma 2 (`ml3_width_eq`), Lemmas 3 and 4 in the form
used (critical configurations `ml5_IsConf`, `ml5_conf_of_pi`, `ml5_pi_of_conf`; Lemma 3 is
Minkowski's theorem, `External.minkowski_mahler`), Lemma 5 and its Corollary (`ml5_lemma5`,
`ml5_lemma5_partner`, `ml5_lemma5_unique`, `ml5_lemma5_cor_six`, `ml5_lemma5_cor_arcs`), Lemma 6
(`ml5_lemma6`), Lemma 7 (`ml5_lemma7`) and the class-A case of Lemma 13 (`ml5_classA`, with
Mahler's quadratic `ml3_quadratic`). On the way, facts that the 1946 files use too: the existence
of critical lattices (`irr_exists_critical`, Mahler's compactness theorem in the plane), the cut
of `K` by a strip `|a · x| ≤ c` (`irr_cut`), `Δ(K') ≤ Δ(K)` for `K' ⊆ K` (`ml3_minDet_mono`), a
boundary point of `K` outside a proper subdomain (`ml3_exists_frontier_notMem`), and the lattice
points of `K` beyond Minkowski's hexagon (`ml3_eight`). The facts about the boundary curve that
Mahler uses "by the convexity of `C`" (arcs, the radial parametrization and the intermediate
value theorem on arcs, chords, arcs without extreme points) are in
`Basic.Analysis.Convex.BoundaryArc`.

## Sources, and departures from them

Mahler 1947 states Lemma 3 without proof. Paper A was not among the sources supplied with the
book; we read a scan of it (Mahler's collected works, CARMA archive, item 094), and of the 1946
paper (item 088; the book's bibliography entry `mahler1946lattice` is this paper). Reading: in
paper A and in the 1946 paper a domain is *irreducible* if every *star domain* `H ⊊ K` has
`Δ(H) < Δ(K)`; `IsIrreducible` asks this only of symmetric convex subdomains. Paper A's Lemma 13
(a reducible convex domain has a convex proper subdomain with the same `Δ`) is the bridge: for a
convex `K` the two notions agree, and the "only if" half of Lemma 3 for `IsIrreducible` is the
proof of Lemma 13 (`MahlerIrreducible.ml3_onlyIf`). The lemmas of this file follow paper A:

* Lemma 1 (`ml5_lemma1`), Mahler's proof. *Departure from paper A:* `Δ(K₀) = 1`, which Mahler
  takes from Minkowski's theorem on linear forms, is obtained from Mahler's own example in §2
  (`A(P₁) = 1` for every boundary point of the square) with Lemmas 2 and 3 (`ml5_par_minDet`);
  and the proof is written in the coordinates of the parallelogram instead of after an affine map
  to the square. *Gap in paper A*, filled: the reduction to `P₀ = (ξ, 1)`, `0 < ξ < 1`, is left to
  the reader. *Error in paper A*, harmless: `±θP₀` are not the only points of `Λ₀` inside the
  square when `θ < 1/2`; all of them are multiples of `θP₀`, which are not inner points of `H`
  (`ml5_lemma1_core`).
* Lemma 2 (`ml3_width_eq`): Mahler's strip argument.
* Lemma 5 (`ml5_lemma5`, `ml5_lemma5_partner`, `ml5_lemma5_unique`), Mahler's proof. *Slip in
  paper A:* "an inner point of `P₂P₃` lies on `L**`" should read "lies on `C`". *Gap in paper A*,
  filled: its Corollary (`ml5_lemma5_cor_six`, `ml5_lemma5_cor_arcs`) has no proof; we supply one
  (`ml3_eight` and the uniqueness of the configuration at a point).
* Lemma 6 (`ml5_lemma6`), Mahler's proof: the triangle `P₁, P₁ + P₂, P₂` (`ml5_triangle`), the
  line `{P₁*, X} = Δ` meeting the arcs `A₂, A₃` (intermediate value theorem on arcs), Lemma 5.
  Stated for one step (a point inside `A₁` has its next points inside `A₂, A₃`), from which
  Mahler's "just one point on each arc" follows by rotating the configuration.
* Lemma 7 (`ml5_lemma7_step`, `ml5_lemma7`), Mahler's argument via Lemma 6.
* Class A of Lemma 13 (`ml5_classA`), as written: the largest segment `Γ₁` around the point with
  ends on critical lattices and inner points off them; `P'₁` inside `A₁`; `P'₂, P'₃` inside
  `A₂, A₃` (Lemma 6); the inner points of `Γ₂, Γ₃` off critical lattices (Lemma 7, used with the
  indices shifted cyclically and the roles of the lattices exchanged, `ml5_lemma7_back`), hence
  not extreme, hence `Γ₂, Γ₃` are segments; `{Q₁, Q₃} > 0` from the positions of `P'₁, P'₃` in
  the triangles; Mahler's quadratic (`ml3_quadratic`). *Gaps in paper A*, filled: Mahler's
  "without loss of generality, `P'₁` lies on `A₁`" (our naming of the ends by orientation); the
  sign of `{P₁*, P₃*}` (Lemma 3 bounds its absolute value; the sign follows by continuity); and
  the step "the inner points of `Γ_l` are of class A, so `Γ_l` is a segment"
  (`BoundaryArc.midpoint_mem_frontier_of_forall_not_mem_extremePoints`).

Class B of Lemma 13 (with Lemma 10), the closedness of `Π` (Lemma 11) and Lemma 12 are in the
1946 files, by Mahler's proofs of Theorems B–E; the assembly, and the weak form
`mahler_irreducible` derived from Lemma 3, are in `External.MahlerIrreducible.Lemma3`.
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

open Set Filter Topology MinkowskiMahler BoundaryArc

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

/-! ### Extreme points and subdomains -/

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

/-! ### Lattice points beyond Minkowski's hexagon -/

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

/-! ### Segments of the boundary -/

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

end Lemma3

end MahlerIrreducible

end External
