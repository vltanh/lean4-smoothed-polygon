module

public import External.Mahler1947
public import Basic.Algebra.Module.ZLattice.PlaneCritical
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

`mahler_irreducible_iff`: Lemma 3 in full. On the way: `mahler_irreducible` (if `K` is
irreducible, every tac-line `ℓ` of `K` passes through a point of a critical lattice `Λ` of `K`,
one of the six points `±P₀, ±P₁, ±P₂` of a configuration of Mahler's Lemma 2 (Minkowski: `P₀, P₁`
a basis of `Λ`, `P₁ = P₀ + P₂`, the three points on the boundary of `K`));
`mahler_irreducible_exposed` (exposed points); `MahlerIrreducible.ml3_extreme` (extreme points);
`MahlerIrreducible.ml3_onlyIf` (all boundary points); `MahlerIrreducible.ml3_irreducible_of_forall`
(the converse).

## Sources, and departures from them

Mahler 1947 states Lemma 3 without proof. Paper A was not among the sources supplied with the
book; for this proof we read a scan of it (Mahler's collected works, CARMA archive, item 094).
In paper A a domain is *irreducible* if every *star domain* `H ⊊ K` has `Δ(H) < Δ(K)`;
`IsIrreducible` asks this only of symmetric convex subdomains (paper A's Lemma 13 shows that for a
convex `K` the two notions agree, so Lemma 3 holds for either). Paper A quotes its Lemma 8
(irreducible star domain: every boundary point on a critical lattice), Lemmas 10, 11 and Lemma 12
(convex `K` with every boundary point on a critical lattice is irreducible) from Mahler, Proc.
Kon. Ned. Akad. Wet. 49 (1946), 331–343, Theorems B–E, which we do not have; it proves Lemma 13 (a
reducible convex domain contains a proper convex subdomain with the same `Δ`). Our proofs:

* "If" (Lemma 12, for convex subdomains; `ml3_irreducible_of_forall`). Not Mahler's (unavailable)
  proof, but the following argument. If `K' ⊊ K` had `Δ(K') = Δ(K)`, a critical lattice `Λ` of
  `K` through a boundary point `p ∉ K'` would be `K'`-critical, so (Lemma 2 for `K'`) it has
  points `Q₀, Q₂, Q₀ + Q₂` on the boundary of `K'`, hence of `K`. Admissibility then forces
  `p = ±(2Q₀ + Q₂), ±(Q₀ + 2Q₂), ±(Q₀ - Q₂)` (`ml3_eight`), i.e. `p = A + B` with `A, B, A ± B` on
  the boundary; then `K` lies in the parallelogram `|f| ≤ 1, |g| ≤ 1` (`f, g` support functionals
  at `A, B`) of vertex `p`, and `p` is an extreme point of `K` (`ml3_square_extreme`). The nearby
  boundary points `A + (1 - ε)B`, also outside `K'`, are not extreme. This covers parallelograms
  (paper A, Lemma 1) without Minkowski's theorem.
* "Only if" (Lemma 8 with Lemma 13). We follow the proof of Lemma 13, which splits the boundary
  points off critical lattices into class B (not inside a boundary segment, i.e. extreme points)
  and class A (inside a boundary segment).
  - Class B (`ml3_extreme`). Mahler uses Lemma 10 (from the 1946 paper, for star domains) and a
    cut by a line. We use the shaving argument of `mahler_irreducible` on support lines tilted
    towards the extreme point, and the closedness of the set `Π` of boundary points on critical
    lattices (paper A, Lemma 11; `ml3_isClosed`, by compactness of the critical lattices).
  - Class A (`ml3_onlyIf`). As in Lemma 13: a maximal segment `Γ₁ = [A, B]` of the boundary
    around the point whose inner points are off `Π`, with `A, B ∈ Π`; the critical lattices at
    `A, B` with points `P_l, P'_l`; the points `P_l + t(P'_l - P_l)`; and the quadratic
    `f(t) = det` with `f(0) = f(1) = Δ(K)` and `f'' > 0`, which gives an admissible lattice of
    determinant `< Δ(K)` (`ml3_quadratic`). Departure from the paper: Mahler shows that the arcs
    `Γ₂, Γ₃` from `P₂` to `P'₂` and from `P₃` to `P'₃` are segments, and that `f'' > 0`, from his
    Lemmas 5–7 (uniqueness and interlacing of critical lattices of a non-parallelogram). We
    choose the extreme partners `U, V` of `A, B` and prove `f'' > 0` by convexity in
    coordinates adapted to `[A, B]` (`ml3_n_lt`), and that the chords `[U, V]`,
    `[U - A, V - B]` lie on the boundary (`ml3_chord`) from `mahler_irreducible` applied to the
    cap beyond the chord, Lemma 2 of paper A (uniqueness of the area `A(P₁)`, `ml3_width`), and
    convexity. Only `Γ₁, Γ₂, Γ₃` are needed (the other three arcs are their reflections). The
    degenerate case where a partner lies on the support line of `Γ₁` or on its parallel through
    `O` is settled by sliding the lattice along `Γ₁` (`ml3_slide`; Mahler's example of the square
    in §2 of paper A).

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

open Set Filter Topology MinkowskiMahler Mahler1947

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

/-- A functional that is `< 1` on the interior of a symmetric convex domain is `> -1` there. -/
lemma ml3_abs_lt_of_interior (hK : IsSymmetricConvexDomain K) (f : StrongDual ℝ (Fin 2 → ℝ))
    (hf : ∀ y ∈ interior K, f y < 1) {y : Fin 2 → ℝ} (hy : y ∈ interior K) :
    -1 < f y ∧ f y < 1 := by
  have := hf _ (mm_neg_mem_interior hK hy)
  rw [map_neg] at this
  exact ⟨by linarith, hf y hy⟩

/-! ### Mahler's Lemma 2 of paper A: the area `A(X)` -/

/-- **Mahler, paper A, Lemma 2** (the chord of `K` parallel to `X` of length `|X|` with both ends
on the boundary is the farthest one from the line `OX`): if `U, U - X` are boundary points with
`det(X, U) > 0`, and `V, V - X` are points of `K`, then `det(X, V) ≤ det(X, U)`. -/
lemma ml3_width (hK : IsSymmetricConvexDomain K) {X U V : Fin 2 → ℝ} (hX : X ∈ K)
    (hU : U ∈ frontier K) (hUX : U - X ∈ frontier K) (hV : V ∈ K) (hVX : V - X ∈ K)
    (h0 : 0 < cross X U) : cross X V ≤ cross X U := by
  by_contra hlt
  push Not at hlt
  have hXV : 0 < cross X V := h0.trans hlt
  set s := cross X U / cross X V with hs
  have hs0 : 0 < s := div_pos h0 hXV
  have hs1 : s < 1 := (div_lt_one hXV).2 hlt
  have hX0 : X ≠ 0 := by rintro rfl; simp [cross] at h0
  have hY₁ : (1 - s) • X + s • V ∈ K := hK.1 hX hV (by linarith) hs0.le (by ring)
  have hcr : cross X ((1 - s) • X + s • V - U) = 0 := by
    have : cross X ((1 - s) • X + s • V - U) = s * cross X V - cross X U := by
      simp only [cross, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, hs, div_mul_cancel₀ _ hXV.ne']; ring
  obtain ⟨τ, hτ⟩ := ml3_parallel hcr hX0
  rcases lt_or_ge 0 τ with hτ0 | hτ0
  · obtain ⟨f, hf1, hf2, -⟩ := mm_support hK hU
    have e1 := hf2 _ (mm_mem_of_frontier hK hUX)
    have e2 := hf2 _ hY₁
    have e3 := hf2 _ hV
    have hY : (1 - s) • X + s • V = U + τ • X := by rw [← hτ]; abel
    have e4 : f ((1 - s) • X + s • V) = (1 - s) * f X + s * f V := by simp
    rw [hY] at e2
    rw [hY] at e4
    simp only [map_add, map_smul, smul_eq_mul, map_sub] at e1 e2 e4
    have hfX0 : 0 ≤ f X := by linarith
    have hm : τ * f X = 0 := by nlinarith
    have hfX : f X = 0 := (mul_eq_zero.1 hm).resolve_left hτ0.ne'
    rw [hfX, hf1] at e4
    nlinarith [mul_le_mul_of_nonneg_left e3 hs0.le]
  · obtain ⟨g, hg1, hg2, -⟩ := mm_support hK hUX
    have hY₂ : (1 - s) • (-X) + s • (V - X) ∈ K :=
      hK.1 (hK.2.2.2 X hX) hVX (by linarith) hs0.le (by ring)
    have e1 := hg2 _ (mm_mem_of_frontier hK hU)
    have e2 := hg2 _ hY₂
    have e3 := hg2 _ hV
    have hY : (1 - s) • (-X) + s • (V - X) = U + (τ - 2 + s) • X := by
      rw [show U + (τ - 2 + s) • X = (U + τ • X) - (2 - s) • X by module, ← hτ]; module
    have e4 : g ((1 - s) • (-X) + s • (V - X)) = s * g V - g X := by
      simp only [map_add, map_smul, map_neg, map_sub, smul_eq_mul]; ring
    rw [hY] at e2 e4
    simp only [map_add, map_smul, smul_eq_mul, map_sub] at hg1 e1 e2 e4
    have hgX0 : g X ≤ 0 := by linarith
    have hm : (τ - 1 + s) * g X = 0 := by nlinarith
    have hgX : g X = 0 := (mul_eq_zero.1 hm).resolve_left (by linarith)
    rw [hgX] at e4 hg1
    nlinarith [mul_le_mul_of_nonneg_left e3 hs0.le]

/-- **Uniqueness of `A(X)`** (Mahler, paper A, Lemma 2): two pairs `U, U - X` and `V, V - X` of
boundary points with `det(X, U), det(X, V) > 0` have `det(X, U) = det(X, V)`. -/
lemma ml3_width_eq (hK : IsSymmetricConvexDomain K) {X U V : Fin 2 → ℝ} (hX : X ∈ K)
    (hU : U ∈ frontier K) (hUX : U - X ∈ frontier K) (hV : V ∈ frontier K)
    (hVX : V - X ∈ frontier K) (hU0 : 0 < cross X U) (hV0 : 0 < cross X V) :
    cross X U = cross X V :=
  le_antisymm (ml3_width hK hX hV hVX (mm_mem_of_frontier hK hU) (mm_mem_of_frontier hK hUX) hV0)
    (ml3_width hK hX hU hUX (mm_mem_of_frontier hK hV) (mm_mem_of_frontier hK hVX) hU0)

/-- **The chords parallel to `X` have length at least `|X|` below the level `det(X, U)`**: if
`U, U - X ∈ K` with `det(X, U) ≠ 0`, and `Z ∈ K` is the end in direction `X` of its chord (a
support functional `ψ` at `Z` has `ψ(X) > 0`), with `0 ≤ det(X, Z) / det(X, U) ≤ 1`, then
`Z - X ∈ K` (the chord through `Z` contains a convex combination of `[-X, X]` and
`[U - X, U]`, of length at least `|X|`). -/
lemma ml3_sub_mem (hK : IsSymmetricConvexDomain K) {X U Z : Fin 2 → ℝ} (hX : X ∈ K)
    (hU : U ∈ K) (hUX : U - X ∈ K) (h0 : cross X U ≠ 0) (hZ : Z ∈ K)
    (ψ : StrongDual ℝ (Fin 2 → ℝ)) (hψZ : ψ Z = 1) (hψ : ∀ y ∈ K, ψ y ≤ 1) (hψX : 0 < ψ X)
    (hc0 : 0 ≤ cross X Z / cross X U) (hc1 : cross X Z / cross X U ≤ 1) : Z - X ∈ K := by
  have hX0 : X ≠ 0 := by rintro rfl; simp [cross] at h0
  set l := cross X Z / cross X U with hl
  have hl0 : 0 ≤ l := hc0
  have hl1 : l ≤ 1 := hc1
  have hW : l • U + (1 - l) • X ∈ K := hK.1 hU hX hl0 (by linarith) (by ring)
  have hcr : cross X (Z - (l • U + (1 - l) • X)) = 0 := by
    have : cross X (Z - (l • U + (1 - l) • X)) = cross X Z - l * cross X U := by
      simp only [cross, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, hl, div_mul_cancel₀ _ h0]; ring
  obtain ⟨τ, hτ⟩ := ml3_parallel hcr hX0
  -- `τ ≥ 0` since `Z` is the end of its chord
  have hτ0 : 0 ≤ τ := by
    have e := hψ _ hW
    have : l • U + (1 - l) • X = Z - τ • X := by rw [← hτ]; abel
    rw [this, map_sub, map_smul, hψZ, smul_eq_mul] at e
    nlinarith
  have hlX : l • (U - X) + (1 - l) • (-X) ∈ K :=
    hK.1 hUX (hK.2.2.2 X hX) hl0 (by linarith) (by ring)
  set θ := 1 / (2 - l + τ) with hθ
  have hpos : 0 < 2 - l + τ := by linarith
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hpos]; linarith
  have hmem := hK.1 hlX hZ hθ0 (by linarith : 0 ≤ 1 - θ) (by ring)
  convert hmem using 1
  have hZ' : Z = l • U + (1 - l) • X + τ • X := by rw [← hτ]; abel
  have hθ' : θ * (2 - l + τ) = 1 := by rw [hθ]; field_simp
  rw [hZ']
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  linear_combination (X i) * hθ'

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

/-! ### Coordinates adapted to a boundary segment -/

/-- The functional `x ↦ det(v, x)`. -/
noncomputable def ml3_crossL (v : Fin 2 → ℝ) : StrongDual ℝ (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ cross v x
      map_add' := fun x y ↦ by simp only [cross, Pi.add_apply]; ring
      map_smul' := fun c x ↦ by
        simp only [cross, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

lemma ml3_crossL_apply (v x : Fin 2 → ℝ) : ml3_crossL v x = cross v x := rfl

/-- Coordinates adapted to a segment `[A, B]` with `det(B - A, A) ≠ 0`:
`x = s(x) (B - A) + n(x) A`, so that `A = (0, 1)` and `B = (1, 1)`. -/
lemma ml3_frame {A B : Fin 2 → ℝ} (hκ : cross (B - A) A ≠ 0) :
    ∃ s n : StrongDual ℝ (Fin 2 → ℝ), (∀ x, x = s x • (B - A) + n x • A) ∧
      s A = 0 ∧ n A = 1 ∧ s B = 1 ∧ n B = 1 := by
  set κ := cross (B - A) A
  refine ⟨(-κ⁻¹) • ml3_crossL A, κ⁻¹ • ml3_crossL (B - A), fun x ↦ ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [smul_apply, ml3_crossL_apply, smul_eq_mul]
  · have h1 : -κ⁻¹ * cross A x = cross x A / κ := by rw [mm_cross_swap A x]; ring
    have h2 : κ⁻¹ * cross (B - A) x = cross (B - A) x / κ := by ring
    rw [h1, h2]; exact mm_eq_comb hκ x
  · rw [mm_cross_self]; ring
  · exact inv_mul_cancel₀ hκ
  · have : cross A B = -κ := by simp only [κ, cross, Pi.sub_apply]; ring
    rw [this]; field_simp
  · have : cross (B - A) B = κ := by simp only [κ, cross, Pi.sub_apply]; ring
    rw [this]; field_simp

lemma ml3_frame_dual {A e : Fin 2 → ℝ} {s n : StrongDual ℝ (Fin 2 → ℝ)}
    (hdec : ∀ x, x = s x • e + n x • A) (ψ : StrongDual ℝ (Fin 2 → ℝ)) (x : Fin 2 → ℝ) :
    ψ x = s x * ψ e + n x * ψ A := by
  conv_lhs => rw [hdec x]
  simp

lemma ml3_frame_cross {A e : Fin 2 → ℝ} {s n : StrongDual ℝ (Fin 2 → ℝ)}
    (hdec : ∀ x, x = s x • e + n x • A) (x y : Fin 2 → ℝ) :
    cross x y = (s x * n y - n x * s y) * cross e A := by
  conv_lhs => rw [hdec x, hdec y]
  exact mm_cross_comb _ _ _ _ _ _

lemma ml3_frame_ext {A e : Fin 2 → ℝ} {s n : StrongDual ℝ (Fin 2 → ℝ)}
    (hdec : ∀ x, x = s x • e + n x • A) {x y : Fin 2 → ℝ} (hs : s x = s y) (hn : n x = n y) :
    x = y := by
  rw [hdec x, hdec y, hs, hn]

/-- A nonzero functional `≤ c` on `K` is `< c` on the interior of `K`. -/
lemma ml3_lt_of_interior (ψ : StrongDual ℝ (Fin 2 → ℝ)) {c : ℝ} (hψ : ∀ y ∈ K, ψ y ≤ c)
    {v : Fin 2 → ℝ} (hv : ψ v ≠ 0) {y : Fin 2 → ℝ} (hy : y ∈ interior K) : ψ y < c := by
  obtain ⟨a, ha⟩ := ml3_dual_vec ψ
  have ha0 : a ≠ 0 := by rintro rfl; apply hv; rw [← ha]; simp
  have := irr_dot_lt ha0 (M := c) (fun x hx ↦ (ha x).trans_le (hψ x hx)) hy
  rwa [ha] at this

/-- **Which side of the boundary.** In the coordinates of a segment `[A, B]` on a tac-line
`n = 1`, let `X` be a point with `n(X) = 1` and `U, U - X` points of `K` with `0 < n(U) < 1` and
positive determinant (`U` lies to the left). Then a support functional at `U` or at `U - X` is
decreasing in the direction `B - A`. -/
lemma ml3_left (hK : IsSymmetricConvexDomain K) {A e X U : Fin 2 → ℝ}
    {s n : StrongDual ℝ (Fin 2 → ℝ)} (hdec : ∀ x, x = s x • e + n x • A) (hse : s e = 1)
    (hne : n e = 0) (hX : X ∈ K) (hU : U ∈ K) (hnX : n X = 1)
    (hD : 0 < s X * n U - s U) (hn0 : 0 < n U) (hn1 : n U < 1)
    (ψ : StrongDual ℝ (Fin 2 → ℝ)) (hψ : ∀ y ∈ K, ψ y ≤ 1) (hP : ψ U = 1 ∨ ψ (U - X) = 1) :
    ψ e < 0 := by
  have hvec : (s X * n U - s U) • e = n U • X - U := by
    apply ml3_frame_ext hdec
    · simp only [map_smul, map_sub, smul_eq_mul, hse]; ring
    · simp only [map_smul, map_sub, smul_eq_mul, hne, hnX]; ring
  have key : (s X * n U - s U) * ψ e = n U * ψ X - ψ U := by
    have := congrArg ψ hvec; simpa using this
  have hXK := hψ X hX
  rcases hP with h | h
  · rw [h] at key
    have : n U * ψ X ≤ n U := by nlinarith
    nlinarith
  · have h1 := hψ U hU
    have h2 := hψ (-X) (hK.2.2.2 X hX)
    rw [map_sub] at h
    rw [map_neg] at h2
    nlinarith

/-- **A sign lemma.** Let `φ = 1` at `P, Q` and `φ(Z) > 1`, and let `χ` be a support functional at
`P` with `χ(Q) < 1`, `χ(Z) ≤ 1`, both decreasing in the direction `e`. Then `Z` and `Q` lie on the
same side of `P` in height `n`. -/
lemma ml3_sign {A e P Q Z : Fin 2 → ℝ} {s n : StrongDual ℝ (Fin 2 → ℝ)}
    (hdec : ∀ x, x = s x • e + n x • A) (φ χ : StrongDual ℝ (Fin 2 → ℝ)) (hφe : φ e < 0)
    (hχe : χ e < 0) (hφP : φ P = 1) (hφQ : φ Q = 1) (hφZ : 1 < φ Z) (hχP : χ P = 1)
    (hχQ : χ Q < 1) (hχZ : χ Z ≤ 1) : 0 < (n Z - n P) * (n Q - n P) := by
  have d := ml3_frame_dual hdec
  set k := χ A * φ e - χ e * φ A with hk
  have iden : ∀ x, (n x - n P) * k = φ e * (χ x - χ P) - χ e * (φ x - φ P) := by
    intro x; rw [d φ x, d φ P, d χ x, d χ P, hk]; ring
  have hw : 0 < (n Q - n P) * k := by
    rw [iden Q, hφQ, hφP, hχP, sub_self, mul_zero, sub_zero]
    exact mul_pos_of_neg_of_neg hφe (by linarith)
  have hz : 0 < (n Z - n P) * k := by
    rw [iden Z, hφP, hχP]
    have h1 : 0 ≤ φ e * (χ Z - 1) := mul_nonneg_of_nonpos_of_nonpos hφe.le (by linarith)
    have h2 : 0 < -χ e * (φ Z - 1) := mul_pos (by linarith) (by linarith)
    linarith
  have h := mul_pos hz hw
  by_contra hc
  push Not at hc
  nlinarith [sq_nonneg k]

/-- **Heights of partners increase along the segment** (Mahler's "`P₂*` and `P₃*` describe the
arcs in the same sense", from the convexity of the boundary). In the coordinates of a boundary
segment `[A, B]`, let `U, U - A` and `V, V - B` be pairs of boundary points with positive
determinants and heights in `(0, 1)`. Then `n(U) < n(V)`. -/
lemma ml3_n_lt (hK : IsSymmetricConvexDomain K) {A B U V : Fin 2 → ℝ}
    {s n : StrongDual ℝ (Fin 2 → ℝ)} (hdec : ∀ x, x = s x • (B - A) + n x • A) (hsA : s A = 0)
    (hnA : n A = 1) (hsB : s B = 1) (hnB : n B = 1) (hA : A ∈ K) (hB : B ∈ K)
    (hU : U ∈ frontier K) (hUA : U - A ∈ frontier K) (hV : V ∈ frontier K)
    (hVB : V - B ∈ frontier K) (hDU : 0 < -s U) (hDV : 0 < n V - s V)
    (hnU : 0 < n U ∧ n U < 1) (hnV : 0 < n V ∧ n V < 1) : n U < n V := by
  have hse : s (B - A) = 1 := by rw [map_sub, hsA, hsB, sub_zero]
  have hne : n (B - A) = 0 := by rw [map_sub, hnA, hnB, sub_self]
  have hUK := mm_mem_of_frontier hK hU
  have hUAK := mm_mem_of_frontier hK hUA
  have hVK := mm_mem_of_frontier hK hV
  have hVBK := mm_mem_of_frontier hK hVB
  obtain ⟨ψ, hψ1, hψ2, -⟩ := mm_support hK hUA
  obtain ⟨χ, hχ1, hχ2, -⟩ := mm_support hK hV
  have hψe := ml3_left hK hdec hse hne hA hUK hnA (by rw [hsA]; linarith) hnU.1 hnU.2
    ψ hψ2 (Or.inr hψ1)
  have hχe := ml3_left hK hdec hse hne hB hVK hnB (by rw [hsB]; linarith) hnV.1 hnV.2
    χ hχ2 (Or.inl hχ1)
  by_contra hc
  push Not at hc
  set l := n U - n V with hl
  have hl0 : 0 ≤ l := by linarith
  have hl1 : l < 1 := by linarith [hnU.2, hnV.1]
  have hY : V - (1 - l) • B ∈ K := by
    have := hK.1 hVK hVBK hl0 (by linarith : (0 : ℝ) ≤ 1 - l) (by ring)
    convert this using 1; module
  have hY' : U - l • A ∈ K := by
    have := hK.1 hUAK hUK hl0 (by linarith : (0 : ℝ) ≤ 1 - l) (by ring)
    convert this using 1; module
  have d := ml3_frame_dual hdec
  have sY : s (V - (1 - l) • B) = s V - (1 - l) := by simp [hsB]
  have nY : n (V - (1 - l) • B) = n V - (1 - l) := by simp [hnB]
  have sY' : s (U - l • A) = s U := by simp [hsA]
  have nY' : n (U - l • A) = n U - l := by simp [hnA]
  have sUA : s (U - A) = s U := by simp [hsA]
  have nUA : n (U - A) = n U - 1 := by simp [hnA]
  have e1 := hψ2 _ hY
  rw [d ψ, sY, nY] at e1
  have e1' := d ψ (U - A)
  rw [hψ1, sUA, nUA] at e1'
  have e2 := hχ2 _ hY'
  rw [d χ, sY', nY'] at e2
  have e2' := d χ V
  rw [hχ1] at e2'
  have f1 : (s V - (1 - l) - s U) * ψ (B - A) ≤ 0 := by rw [hl] at e1; nlinarith
  have f2 : (s U - s V) * χ (B - A) ≤ 0 := by rw [hl] at e2; nlinarith
  have g1 : 0 ≤ s V - (1 - l) - s U := by
    by_contra h; push Not at h; nlinarith
  have g2 : 0 ≤ s U - s V := by
    by_contra h; push Not at h; nlinarith
  linarith

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

/-- **Partners of a point of a critical lattice.** If `Z` lies on a critical lattice and
`X, Z - X` are boundary points, then `X` lies on a critical lattice (uniqueness of `A(Z)`,
`ml3_width_abs`, and the converse half of Lemma 2). -/
lemma ml3_partner_crit (hK : IsSymmetricConvexDomain K) {Z X : Fin 2 → ℝ}
    (hZF : Z ∈ frontier K) (hZΛ : ∃ Λ, IsCritical K Λ ∧ Z ∈ Λ) (hX : X ∈ frontier K)
    (hZX : Z - X ∈ frontier K) : ∃ Λ, IsCritical K Λ ∧ X ∈ Λ := by
  obtain ⟨Λ, hΛ, hZ⟩ := hZΛ
  obtain ⟨W, hW, hWZ, hWabs⟩ := ml3_pair hK hΛ hZ hZF
  have hΔ := irr_minimalDeterminant_pos hK
  have hW0 : cross Z W ≠ 0 := by intro h; rw [h, abs_zero] at hWabs; linarith
  have hZsum : Z - X + X = Z := sub_add_cancel Z X
  have hcZX : cross (Z - X) X = cross Z X := by simp only [cross, Pi.sub_apply]; ring
  have hX0 : cross Z X ≠ 0 := hcZX ▸ mm_cross_ne_zero hK hZX hX (by rw [hZsum]; exact hZF)
  have hXZ : X - Z ∈ frontier K := by rw [← neg_sub]; exact mm_neg_mem_frontier hK hZX
  have heq := ml3_width_abs hK (mm_mem_of_frontier hK hZF) hW hWZ hX hXZ hW0 hX0
  obtain ⟨-, h2⟩ := (minkowski_mahler hK).2 (Z - X) Z X hZX hZF hX hZsum.symm
  have hc : |cross (Z - X) Z| = minimalDeterminant K := by
    rw [show cross (Z - X) Z = cross Z X by simp only [cross, Pi.sub_apply]; ring, ← heq, hWabs]
  refine ⟨_, h2.1 hc, ?_⟩
  have : X = Z - (Z - X) := by abel
  rw [this]
  exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
    (Submodule.subset_span (by simp))

/-- **Sliding along a segment** (Mahler's example of the square). Let `f ≤ 1` be a support
functional of `K`, `X₀, x` points with `f = 1`, and `V₀` a boundary point with `f(V₀) = 0` and
`|det(X₀, V₀)| = Δ(K)`. Then the lattice with basis `x, V₀` is critical: its points lie on the
lines `f = m` (`m ∈ ℤ`), the points on `f = 0` are the multiples of `V₀`. -/
lemma ml3_slide (hK : IsSymmetricConvexDomain K) (f : StrongDual ℝ (Fin 2 → ℝ))
    (hf3 : ∀ y ∈ interior K, f y < 1) {X₀ V₀ x : Fin 2 → ℝ} (hfX : f X₀ = 1) (hfx : f x = 1)
    (hfV : f V₀ = 0) (hV₀ : V₀ ∈ frontier K) (hcr : |cross X₀ V₀| = minimalDeterminant K) :
    ∃ Λ, IsCritical K Λ ∧ x ∈ Λ := by
  obtain ⟨a, ha⟩ := ml3_dual_vec f
  have ha0 : a ≠ 0 := by rintro rfl; have := ha x; simp [hfx] at this
  have hpar : cross (x - X₀) V₀ = 0 :=
    ml3_cross_eq_zero_of_dot ha0 (by rw [ha, map_sub, hfx, hfX, sub_self]) (by rw [ha, hfV])
  have hxV : cross x V₀ = cross X₀ V₀ := by
    have : cross (x - X₀) V₀ = cross x V₀ - cross X₀ V₀ := by
      simp only [cross, Pi.sub_apply]; ring
    linarith
  have hΔ := irr_minimalDeterminant_pos hK
  have hne : cross x V₀ ≠ 0 := by intro h; rw [hxV] at h; rw [h, abs_zero] at hcr; linarith
  obtain ⟨g, hg1, -, hg3⟩ := mm_support hK hV₀
  refine ⟨_, ⟨mm_isLattice_span hne, ?_, by rw [mm_det_span hne, hxV, hcr]⟩,
    Submodule.subset_span (by simp)⟩
  intro y hy hyi
  obtain ⟨m, k, rfl⟩ := mm_mem_span_pair.1 hy
  have h1 := ml3_abs_lt_of_interior hK f hf3 hyi
  simp only [map_add, map_smul, hfx, hfV, smul_eq_mul, mul_one, mul_zero, add_zero] at h1
  have hm : m = 0 := by
    have : |(m : ℝ)| < 1 := abs_lt.2 h1
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast this)
  subst hm
  have h2 := ml3_abs_lt_of_interior hK g hg3 hyi
  simp only [Int.cast_zero, zero_smul, zero_add, map_smul, hg1, smul_eq_mul, mul_one] at h2
  have hk : k = 0 := by
    have : |(k : ℝ)| < 1 := abs_lt.2 h2
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast this)
  simp [hk]

/-! ### The arcs between partners are segments -/

/-- **The arcs between partners are segments** (Mahler, paper A, proof of Lemma 13: "the inner
points of all arcs `Γ_l` are of class A, and so all six arcs `Γ_l` are line segments"). Let
`[A, B]` be a segment of the boundary on the tac-line `n = 1` whose inner points lie on no
critical lattice (`hgap`), and let `U, U - A` and `V, V - B` be pairs of boundary points with
`det = Δ(K)`, chosen with `U` highest and `V` lowest among such pairs. Then the chord `[U, V]`
lies on the boundary of `K`.

Mahler obtains this from the interlacing of critical lattices (his Lemmas 5–7) and the fact that
the points of the arc, being on no critical lattice, are not extreme. We argue directly: if the
chord were not on the boundary, the cap of `K` beyond it would have a tac-line `{φ = max}`
carrying a point `Z` of a critical lattice (`mahler_irreducible`); by convexity `Z` lies between
`U` and `V` (`ml3_sign`) and has a partner `X` on `[A, B]` with `Z - X` on the boundary (`Z - A ∈
K` by `ml3_sub_mem`, `Z - B ∉ int K` by a four-point convexity argument); `X = A` or `X = B`
contradicts the choice of `U` or `V` (uniqueness of `A(X)`, `ml3_width_abs`), and an inner `X`
would lie on a critical lattice (`ml3_partner_crit`). -/
lemma ml3_chord (hirr : IsIrreducible K) {A B U V : Fin 2 → ℝ}
    {s n : StrongDual ℝ (Fin 2 → ℝ)} (hκ : cross (B - A) A ≠ 0)
    (hdec : ∀ x, x = s x • (B - A) + n x • A) (hsA : s A = 0) (hnA : n A = 1) (hsB : s B = 1)
    (hnB : n B = 1) (hA : A ∈ frontier K) (hB : B ∈ frontier K) (hn : ∀ x ∈ K, n x ≤ 1)
    (hU : U ∈ frontier K) (hUA : U - A ∈ frontier K) (hV : V ∈ frontier K)
    (hVB : V - B ∈ frontier K) {D : ℝ} (hD : 0 < D) (hDU : -s U = D) (hDV : n V - s V = D)
    (hnU : 0 < n U ∧ n U < 1) (hnV : 0 < n V ∧ n V < 1)
    (hUmax : ∀ W ∈ frontier K, W - A ∈ frontier K → -s W = D → n W ≤ n U)
    (hVmin : ∀ W ∈ frontier K, W - B ∈ frontier K → n W - s W = D → n V ≤ n W)
    (hgap : ∀ t : ℝ, 0 < t → t < 1 → ¬ ∃ Λ, IsCritical K Λ ∧ A + t • (B - A) ∈ Λ) :
    (1 / 2 : ℝ) • (U + V) ∈ frontier K := by
  have hK := hirr.1
  have hse : s (B - A) = 1 := by rw [map_sub, hsA, hsB, sub_zero]
  have hne : n (B - A) = 0 := by rw [map_sub, hnA, hnB, sub_self]
  have d := ml3_frame_dual hdec
  have dc := ml3_frame_cross hdec
  have hUK := mm_mem_of_frontier hK hU
  have hUAK := mm_mem_of_frontier hK hUA
  have hVK := mm_mem_of_frontier hK hV
  have hVBK := mm_mem_of_frontier hK hVB
  have hAK := mm_mem_of_frontier hK hA
  have hBK := mm_mem_of_frontier hK hB
  have hlt : n U < n V := ml3_n_lt hK hdec hsA hnA hsB hnB hAK hBK hU hUA hV hVB (by linarith)
    (by linarith) hnU hnV
  by_contra hmid
  have hMK : (1 / 2 : ℝ) • (U + V) ∈ K := by
    have := hK.1 hUK hVK (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (by norm_num)
    convert this using 1; module
  have hMi : (1 / 2 : ℝ) • (U + V) ∈ interior K := by
    by_contra h; exact hmid (mm_mem_frontier hK hMK h)
  -- the functional `φ` with `φ(U) = φ(V) = 1`
  have hcUV : cross U V ≠ 0 := by
    rw [dc U V]
    refine mul_ne_zero ?_ hκ
    have : s U * n V - n U * s V = -(D * (n V - n U)) - n U * n V := by
      rw [show s U = -D by linarith, show s V = n V - D by linarith]; ring
    rw [this]
    have := mul_pos hD (sub_pos.2 hlt)
    have := mul_pos hnU.1 hnV.1
    linarith
  set φ : StrongDual ℝ (Fin 2 → ℝ) := (cross U V)⁻¹ • (ml3_crossL U - ml3_crossL V) with hφdef
  have hφ : ∀ x, φ x = (cross U V)⁻¹ * (cross U x - cross V x) := fun x ↦ by
    simp [hφdef, ml3_crossL_apply]
  have hφU : φ U = 1 := by
    rw [hφ, mm_cross_self, mm_cross_swap U V, zero_sub, neg_neg, inv_mul_cancel₀ hcUV]
  have hφV : φ V = 1 := by rw [hφ, mm_cross_self, sub_zero, inv_mul_cancel₀ hcUV]
  have hφM : φ ((1 / 2 : ℝ) • (U + V)) = 1 := by
    rw [map_smul, map_add, hφU, hφV, smul_eq_mul]; norm_num
  have hbig : ∃ y ∈ K, 1 < φ y := by
    by_contra h
    push Not at h
    have := ml3_lt_of_interior φ h (v := U) (by rw [hφU]; norm_num) hMi
    linarith
  obtain ⟨y₀, hy₀K, hy₀⟩ := hbig
  obtain ⟨a, ha⟩ := ml3_dual_vec φ
  have ha0 : a ≠ 0 := by rintro rfl; have := ha U; simp [hφU] at this
  obtain ⟨M, hM, hℓ⟩ := ml3_tacLine_max hK ha0
  obtain ⟨Z, hZℓ, hZF, hZΛ⟩ := ml3_tac_point hirr hℓ
  have hZK := mm_mem_of_frontier hK hZF
  simp only [mem_ofPred_eq, ha] at hZℓ
  have hφmax : ∀ x ∈ K, φ x ≤ φ Z := fun x hx ↦ by rw [hZℓ, ← ha]; exact hM x hx
  have hφZ : 1 < φ Z := lt_of_lt_of_le hy₀ (hφmax y₀ hy₀K)
  -- frame values of `φ`
  set q := φ (B - A) with hq
  set p := φ A with hp
  have eU := d φ U
  have eV := d φ V
  rw [hφU] at eU
  rw [hφV] at eV
  have hsU : s U = -D := by linarith
  have hsV : s V = n V - D := by linarith
  rw [hsU] at eU
  rw [hsV] at eV
  have hpq : (n V - n U) * p = -(n V * q) := by linarith
  have hq0 : q < 0 := by
    by_contra h
    push Not at h
    have h1 : (n V - n U) * p ≤ 0 := by rw [hpq]; linarith [mul_nonneg hnV.1.le h]
    have h2 : p ≤ 0 := by
      by_contra h3; push Not at h3; linarith [mul_pos (sub_pos.2 hlt) h3]
    linarith [mul_nonneg hD.le h, mul_nonpos_of_nonneg_of_nonpos hnU.1.le h2]
  have hp0 : 0 < p := by
    have : 0 < (n V - n U) * p := by rw [hpq]; linarith [mul_neg_of_pos_of_neg hnV.1 hq0]
    by_contra h; push Not at h
    linarith [mul_nonpos_of_nonneg_of_nonpos (sub_pos.2 hlt).le h]
  -- support functionals at `U` and `V` are decreasing along `B - A`
  obtain ⟨χU, hχU1, hχU2, hχU3⟩ := mm_support hK hU
  obtain ⟨χV, hχV1, hχV2, hχV3⟩ := mm_support hK hV
  have hχUe := ml3_left hK hdec hse hne hAK hUK hnA (by rw [hsA]; linarith) hnU.1 hnU.2 χU hχU2
    (Or.inl hχU1)
  have hχVe := ml3_left hK hdec hse hne hBK hVK hnB (by rw [hsB]; linarith) hnV.1 hnV.2 χV hχV2
    (Or.inl hχV1)
  have hχUV : χU V < 1 := by
    have := hχU3 _ hMi
    rw [map_smul, map_add, hχU1, smul_eq_mul] at this; linarith
  have hχVU : χV U < 1 := by
    have := hχV3 _ hMi
    rw [map_smul, map_add, hχV1, smul_eq_mul] at this; linarith
  -- `n(U) < n(Z) < n(V)`
  have hZU : n U < n Z := by
    have := ml3_sign hdec φ χU hq0 hχUe hφU hφV hφZ hχU1 hχUV (hχU2 Z hZK)
    by_contra h; push Not at h
    linarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 h) (sub_pos.2 hlt).le]
  have hZV : n Z < n V := by
    have := ml3_sign hdec φ χV hq0 hχVe hφV hφU hφZ hχV1 hχVU (hχV2 Z hZK)
    by_contra h; push Not at h
    linarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 h) (sub_neg.2 hlt).le]
  -- `s(V) < 0` and `s(Z) < 0`
  have hsV0 : s V < 0 := by
    have e1 := d χV V
    have e2 := hχV2 A hAK
    rw [d χV A, hsA, hnA, zero_mul, zero_add, one_mul] at e2
    rw [hχV1] at e1
    have h3 : n V * χV A ≤ n V := mul_le_of_le_one_right hnV.1.le e2
    by_contra h; push Not at h
    linarith [mul_nonpos_of_nonneg_of_nonpos h hχVe.le]
  have eZ := d φ Z
  have hsZ0 : s Z < 0 := by
    have key : (φ Z - 1) * (n V - n U) =
        q * ((s Z - s U) * (n V - n U) - (n Z - n U) * n V) := by
      linear_combination (n V - n U) * eZ - (n V - n U) * eU + q * (n V - n U) * hsU +
        (n Z - n U) * hpq
    have h1 : 0 < (φ Z - 1) * (n V - n U) := mul_pos (by linarith) (sub_pos.2 hlt)
    have h2 : (s Z - s U) * (n V - n U) - (n Z - n U) * n V < 0 := by
      by_contra h; push Not at h
      linarith [mul_nonpos_of_nonpos_of_nonneg hq0.le h]
    have h3 : (n Z - n U) * n V < (n V - n U) * n V :=
      mul_lt_mul_of_pos_right (by linarith) hnV.1
    have h4 : s Z * (n V - n U) < (n V - n U) * s V := by
      rw [hsU] at h2; rw [hsV]; nlinarith
    have h5 : (n V - n U) * s V < 0 := mul_neg_of_pos_of_neg (sub_pos.2 hlt) hsV0
    by_contra h; push Not at h
    linarith [mul_nonneg h (sub_pos.2 hlt).le]
  -- `s(Z) ≥ s(U)`: `U` lies left of the chord from `U - A` to `Z`
  have hsZU : s U ≤ s Z := by
    set μ := 1 / (n Z - n U + 1) with hμ
    have hμ0 : 0 < μ := by rw [hμ]; apply div_pos one_pos; linarith
    have hμ1 : μ ≤ 1 := by rw [hμ, div_le_one (by linarith)]; linarith
    have hμ' : μ * (n Z - n U + 1) = 1 := by rw [hμ]; field_simp
    have hY : (1 - μ) • (U - A) + μ • Z ∈ K := hK.1 hUAK hZK (by linarith) hμ0.le (by ring)
    have e1 := hχU2 _ hY
    rw [d χU] at e1
    have e0 := d χU U
    rw [hχU1] at e0
    have sY : s ((1 - μ) • (U - A) + μ • Z) = (1 - μ) * s U + μ * s Z := by simp [hsA]
    have nY : n ((1 - μ) • (U - A) + μ • Z) = n U := by
      simp only [map_add, map_smul, map_sub, smul_eq_mul, hnA]; linear_combination hμ'
    rw [sY, nY] at e1
    have h5 : μ * ((s Z - s U) * χU (B - A)) ≤ 0 := by linarith
    by_contra h; push Not at h
    linarith [mul_pos hμ0 (mul_pos_of_neg_of_neg (sub_neg.2 h) hχUe)]
  -- `Z - A ∈ K`
  have hZA : Z - A ∈ K := by
    have hcAU : cross A U = D * cross (B - A) A := by rw [dc, hsA, hnA, hsU]; ring
    have hcAZ : cross A Z = -s Z * cross (B - A) A := by rw [dc, hsA, hnA]; ring
    have hD' : D ≠ 0 := hD.ne'
    have hrat : cross A Z / cross A U = -s Z / D := by
      rw [hcAU, hcAZ]; field_simp
    refine ml3_sub_mem hK hAK hUK hUAK (by rw [hcAU]; exact mul_ne_zero hD.ne' hκ) hZK
      ((φ Z)⁻¹ • φ) (by simp only [smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ (by linarith))
      (fun x hx ↦ by
        simp only [smul_apply, smul_eq_mul]
        rw [inv_mul_le_iff₀ (lt_trans one_pos hφZ), mul_one]; exact hφmax x hx)
      (by simp only [smul_apply, smul_eq_mul]; exact mul_pos (inv_pos.2 (by linarith)) hp0)
      (by rw [hrat]; exact div_nonneg (by linarith) hD.le)
      (by rw [hrat, div_le_one hD]; linarith)
  -- the partner `X = A + t* (B - A)` of `Z`
  set T := {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ Z - (A + t • (B - A)) ∈ K} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (hK.2.1.isClosed.preimage (by fun_prop))
  have hT0 : (0 : ℝ) ∈ T := ⟨⟨le_rfl, zero_le_one⟩, by simpa using hZA⟩
  have hTb : BddAbove T := ⟨1, fun t ht ↦ ht.1.2⟩
  set t₀ := sSup T with ht₀
  have ht₀T : t₀ ∈ T := hTc.csSup_mem ⟨0, hT0⟩ hTb
  have hXK : A + t₀ • (B - A) ∈ K := by
    have := hK.1 hAK hBK (show 0 ≤ 1 - t₀ by linarith [ht₀T.1.2]) ht₀T.1.1 (by ring)
    convert this using 1; module
  have hXF : A + t₀ • (B - A) ∈ frontier K := mm_mem_frontier hK hXK fun hi ↦ by
    have := ml3_lt_of_interior n hn (v := A) (by rw [hnA]; norm_num) hi
    rw [map_add, map_smul, hnA, hne, smul_eq_mul, mul_zero, add_zero] at this
    exact lt_irrefl _ this
  have hZXF : Z - (A + t₀ • (B - A)) ∈ frontier K := by
    refine mm_mem_frontier hK ht₀T.2 fun hi ↦ ?_
    rcases (ht₀T.1.2).lt_or_eq with h1 | h1
    · -- push `t` a little beyond `t₀`
      have hc : Continuous fun t : ℝ ↦ Z - (A + t • (B - A)) := by fun_prop
      have hev : (fun t : ℝ ↦ Z - (A + t • (B - A))) ⁻¹' interior K ∈ 𝓝 t₀ :=
        hc.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hi)
      have hev2 : ∀ᶠ t in 𝓝[>] t₀, Z - (A + t • (B - A)) ∈ interior K ∧ t < 1 :=
        nhdsWithin_le_nhds (Filter.inter_mem hev (Iio_mem_nhds h1))
      obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ :=
        (hev2.and (self_mem_nhdsWithin : Ioi t₀ ∈ 𝓝[>] t₀)).exists
      have htT : t ∈ T := ⟨⟨by linarith [ht₀T.1.1, show t₀ < t from ht3], le_of_lt ht2⟩,
        interior_subset ht1⟩
      have := le_csSup hTb htT
      linarith [show t₀ < t from ht3]
    · -- `t₀ = 1`: `Z - B` is not interior (four-point argument)
      rw [h1, one_smul, add_sub_cancel] at hi
      set l := n V - n Z with hl
      have hl0 : 0 < l := by linarith
      have hl1 : l < 1 := by linarith [hnV.2, hZU, hnU.1]
      have hY : (1 - l) • (Z - B) + l • Z ∈ interior K :=
        hK.1.combo_interior_self_mem_interior hi hZK (by linarith) hl0.le (by ring)
      obtain ⟨χ₂, hχ₂1, hχ₂2, hχ₂3⟩ := mm_support hK hVB
      have hχ₂e := ml3_left hK hdec hse hne hBK hVK hnB (by rw [hsB]; linarith) hnV.1 hnV.2
        χ₂ hχ₂2 (Or.inr hχ₂1)
      have e1 := hχ₂3 _ hY
      have hY' : l • (V - B) + (1 - l) • V ∈ K := hK.1 hVBK hVK hl0.le (by linarith) (by ring)
      have e2 := hφmax _ hY'
      rw [d χ₂] at e1 hχ₂1
      rw [d φ] at e2
      have sY : s ((1 - l) • (Z - B) + l • Z) = s Z - 1 + l := by simp [hsB]; ring
      have nY : n ((1 - l) • (Z - B) + l • Z) = n V - 1 := by
        simp only [map_add, map_smul, map_sub, smul_eq_mul, hnB]; rw [hl]; ring
      have sY' : s (l • (V - B) + (1 - l) • V) = s V - l := by simp [hsB]; ring
      have nY' : n (l • (V - B) + (1 - l) • V) = n Z := by
        simp only [map_add, map_smul, map_sub, smul_eq_mul, hnB]; rw [hl]; ring
      have sVB : s (V - B) = s V - 1 := by simp [hsB]
      have nVB : n (V - B) = n V - 1 := by simp [hnB]
      rw [sY, nY] at e1
      rw [sY', nY'] at e2
      rw [sVB, nVB] at hχ₂1
      have f1 : (s Z + l - s V) * χ₂ (B - A) < 0 := by linarith
      have f2 : (s V - l - s Z) * q ≤ 0 := by linarith
      have g1 : 0 < s Z + l - s V := by
        by_contra h; push Not at h
        linarith [mul_nonneg_of_nonpos_of_nonpos h hχ₂e.le]
      have g2 : 0 ≤ s V - l - s Z := by
        by_contra h; push Not at h
        linarith [mul_pos_of_neg_of_neg h hq0]
      linarith
  -- the three cases for `t₀`
  have hZ0 : 0 < n Z := by linarith [hnU.1]
  rcases (ht₀T.1.1).lt_or_eq with h0 | h0
  · rcases (ht₀T.1.2).lt_or_eq with h1 | h1
    · exact hgap t₀ h0 h1 (ml3_partner_crit hK hZF hZΛ hXF hZXF)
    · -- `X = B`
      rw [h1, one_smul, add_sub_cancel] at hZXF
      have hcBV : cross B V = D * cross (B - A) A := by rw [dc, hsB, hnB, hsV]; ring
      have hcBZ : cross B Z = (n Z - s Z) * cross (B - A) A := by rw [dc, hsB, hnB]; ring
      have heq := ml3_width_abs hK hBK hV hVB hZF hZXF
        (by rw [hcBV]; exact mul_ne_zero hD.ne' hκ)
        (by rw [hcBZ]; exact mul_ne_zero (by linarith) hκ)
      rw [hcBV, hcBZ, abs_mul, abs_mul, abs_of_pos hD, abs_of_pos (by linarith : 0 < n Z - s Z)]
        at heq
      have := hVmin Z hZF hZXF (mul_right_cancel₀ (abs_ne_zero.2 hκ) heq).symm
      linarith
  · -- `X = A`
    rw [← h0, zero_smul, add_zero] at hZXF
    have hcAU : cross A U = D * cross (B - A) A := by rw [dc, hsA, hnA, hsU]; ring
    have hcAZ : cross A Z = -s Z * cross (B - A) A := by rw [dc, hsA, hnA]; ring
    have heq := ml3_width_abs hK hAK hU hUA hZF hZXF
      (by rw [hcAU]; exact mul_ne_zero hD.ne' hκ)
      (by rw [hcAZ]; exact mul_ne_zero (by linarith) hκ)
    rw [hcAU, hcAZ, abs_mul, abs_mul, abs_of_pos hD, abs_of_pos (by linarith : 0 < -s Z)] at heq
    have := hUmax Z hZF hZXF (mul_right_cancel₀ (abs_ne_zero.2 hκ) heq).symm
    linarith

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

/-- **Mahler's quadratic** (paper A, end of the proof of Lemma 13). If the chords `[U, V]` and
`[U - A, V - B]` lie on the boundary of `K`, then for `0 ≤ t ≤ 1` the points `A_t = A + t(B - A)`,
`U_t = U + t(V - U)` and `U_t - A_t` are boundary points, so the lattice with basis `A_t, U_t` is
admissible (Lemma 1); but its determinant is `(D - t(1 - t)(n(V) - n(U))) |κ| < D |κ| = Δ(K)` for
small `t > 0` (`f(t) = a + bt + ct²` with `f(0) = f(1) = Δ(K)`, `f'' > 0`). -/
lemma ml3_quadratic (hK : IsSymmetricConvexDomain K) {A B U V : Fin 2 → ℝ}
    {s n : StrongDual ℝ (Fin 2 → ℝ)} (hκ : cross (B - A) A ≠ 0)
    (hdec : ∀ x, x = s x • (B - A) + n x • A) (hsA : s A = 0) (hnA : n A = 1) (hsB : s B = 1)
    (hnB : n B = 1) (hA : A ∈ frontier K) (hB : B ∈ frontier K) (hn : ∀ x ∈ K, n x ≤ 1)
    (hU : U ∈ frontier K) (hUA : U - A ∈ frontier K) (hV : V ∈ frontier K)
    (hVB : V - B ∈ frontier K) {D : ℝ} (hD : 0 < D) (hDU : -s U = D) (hDV : n V - s V = D)
    (hlt : n U < n V) (hΔ : |cross A U| = minimalDeterminant K)
    (hM2 : (1 / 2 : ℝ) • (U + V) ∈ frontier K)
    (hM3 : (1 / 2 : ℝ) • ((U - A) + (V - B)) ∈ frontier K) : False := by
  have dc := ml3_frame_cross hdec
  have hne : n (B - A) = 0 := by rw [map_sub, hnA, hnB, sub_self]
  set δ := n V - n U with hδ
  have hδ0 : 0 < δ := by linarith
  set t := D / (2 * (D + δ)) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ (by positivity)]; linarith
  have hprod : 0 < t * (1 - t) * δ := by
    have : 0 < 1 - t := by linarith
    positivity
  have hprod' : t * (1 - t) * δ < D := by
    have h1 : t * (1 - t) * δ ≤ t * δ := by
      have : t * (1 - t) * δ = t * δ - t * t * δ := by ring
      rw [this]; have : 0 ≤ t * t * δ := by positivity
      linarith
    have h2 : t * δ = D * δ / (2 * (D + δ)) := by rw [ht]; ring
    have h3 : D * δ / (2 * (D + δ)) < D := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have hAK := mm_mem_of_frontier hK hA
  have hBK := mm_mem_of_frontier hK hB
  -- the three boundary points
  have hX : (1 - t) • A + t • B ∈ frontier K := by
    refine mm_mem_frontier hK (hK.1 hAK hBK (by linarith) ht0.le (by ring)) fun hi ↦ ?_
    have := ml3_lt_of_interior n hn (v := A) (by rw [hnA]; norm_num) hi
    rw [map_add, map_smul, map_smul, hnA, hnB, smul_eq_mul, smul_eq_mul] at this
    linarith
  have hUt : (1 - t) • U + t • V ∈ frontier K :=
    ml3_seg_frontier hK (mm_mem_of_frontier hK hU) (mm_mem_of_frontier hK hV) hM2 ht0.le
      (by linarith)
  have hWt : (1 - t) • (U - A) + t • (V - B) ∈ frontier K :=
    ml3_seg_frontier hK (mm_mem_of_frontier hK hUA) (mm_mem_of_frontier hK hVB) hM3 ht0.le
      (by linarith)
  have hsum : (1 - t) • U + t • V = ((1 - t) • (U - A) + t • (V - B)) + ((1 - t) • A + t • B) := by
    module
  obtain ⟨hle, -⟩ := (minkowski_mahler hK).2 _ _ _ hWt hUt hX hsum
  -- the determinant
  have hcr : cross ((1 - t) • (U - A) + t • (V - B)) ((1 - t) • U + t • V) =
      -((D - t * (1 - t) * δ) * cross (B - A) A) := by
    rw [show (1 - t) • (U - A) + t • (V - B) = ((1 - t) • U + t • V) - ((1 - t) • A + t • B) by
      module]
    rw [show cross (((1 - t) • U + t • V) - ((1 - t) • A + t • B)) ((1 - t) • U + t • V) =
      -cross ((1 - t) • A + t • B) ((1 - t) • U + t • V) by simp only [cross, Pi.sub_apply]; ring]
    rw [dc]
    simp only [map_add, map_smul, smul_eq_mul, hsA, hnA, hsB, hnB]
    rw [show s U = -D by linarith, show s V = n V - D by linarith, hδ]
    ring
  have hcAU : cross A U = D * cross (B - A) A := by
    rw [dc, hsA, hnA, show s U = -D by linarith]; ring
  rw [hcr, abs_neg, abs_mul, abs_of_pos (by linarith : 0 < D - t * (1 - t) * δ)] at hle
  rw [hcAU, abs_mul, abs_of_pos hD] at hΔ
  have hκ' : 0 < |cross (B - A) A| := abs_pos.2 hκ
  rw [← hΔ] at hle
  nlinarith

/-- **Mahler, paper A, Lemma 8 and Lemma 13, for convex subdomains** (the "only if" half of
Lemma 3): every boundary point of an irreducible domain lies on a critical lattice. Extreme
points: `ml3_extreme`. Otherwise the point `u` lies inside a boundary segment `{f = 1} ∩ K`,
whose ends are extreme and so lie on critical lattices; the critical-lattice points of the
segment form a closed set (`ml3_isClosed`), and `u` lies in a gap `(A, B)` between two of them.
The pairs of the critical lattices at `A` and `B` (`ml3_pair`) are normalized (orientation, and
the extreme ones `U`, `V` chosen); they are not on the lines `f = 0, 1` (`ml3_slide`); the chords
`[U, V]` and `[U - A, V - B]` lie on the boundary (`ml3_chord`, the second one applied to the
reflected pairs `B - V, A - U`), and Mahler's quadratic (`ml3_quadratic`) gives a contradiction. -/
lemma ml3_onlyIf (hirr : IsIrreducible K) {u : Fin 2 → ℝ} (hu : u ∈ frontier K) :
    ∃ Λ, IsCritical K Λ ∧ u ∈ Λ := by
  have hK := hirr.1
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
  -- the frame of `[A, B]`
  have hfA : f A = 1 := hfp tA
  have hfBA : f (B - A) = 0 := by rw [hBA, map_smul, hfd, smul_zero]
  have hBA0 : B - A ≠ 0 := by
    rw [hBA]; exact smul_ne_zero (by linarith) hd0
  have hκ : cross (B - A) A ≠ 0 := by
    intro h
    obtain ⟨τ, hτ⟩ := ml3_parallel h hBA0
    have := congrArg f hτ
    rw [map_smul, hfBA, smul_zero, hfA] at this
    exact one_ne_zero this
  obtain ⟨s, n, hdec, hsA, hnA, hsB, hnB⟩ := ml3_frame hκ
  have hnf : ∀ x, n x = f x := fun x ↦ by
    rw [ml3_frame_dual hdec f x, hfBA, hfA]; ring
  have hn : ∀ x ∈ K, n x ≤ 1 := fun x hx ↦ (hnf x).trans_le (hf2 x hx)
  have dc := ml3_frame_cross hdec
  set κ := cross (B - A) A with hκdef
  have hκ0 : 0 < |κ| := abs_pos.2 hκ
  have hΔ := irr_minimalDeterminant_pos hK
  set D := minimalDeterminant K / |κ| with hDdef
  have hD : 0 < D := div_pos hΔ hκ0
  have hDκ : D * |κ| = minimalDeterminant K := by rw [hDdef]; field_simp
  have hAK := mm_mem_of_frontier hK hAF
  have hBK := mm_mem_of_frontier hK hBF
  -- pairs at `A` and at `B`, normalized
  obtain ⟨ΛA, hΛA, hAΛ⟩ := htAS.2.2
  obtain ⟨ΛB, hΛB, hBΛ⟩ := htBS.2.2
  obtain ⟨WA, hWA, hWAA, hWAabs⟩ := ml3_pair hK hΛA hAΛ hAF
  obtain ⟨WB, hWB, hWBB, hWBabs⟩ := ml3_pair hK hΛB hBΛ hBF
  have hcA : ∀ W, cross A W = -s W * κ := fun W ↦ by rw [dc, hsA, hnA]; ring
  have hcB : ∀ W, cross B W = (n W - s W) * κ := fun W ↦ by rw [dc, hsB, hnB]; ring
  rw [hcA, abs_mul, ← hDκ] at hWAabs
  rw [hcB, abs_mul, ← hDκ] at hWBabs
  have hWAabs' := mul_right_cancel₀ hκ0.ne' hWAabs
  have hWBabs' := mul_right_cancel₀ hκ0.ne' hWBabs
  set PA := {W | W ∈ frontier K ∧ W - A ∈ frontier K ∧ -s W = D} with hPA
  set PB := {W | W ∈ frontier K ∧ W - B ∈ frontier K ∧ n W - s W = D} with hPB
  have hPAne : PA.Nonempty := by
    rcases abs_eq hD.le |>.1 hWAabs' with h | h
    · exact ⟨WA, hWA, hWAA, h⟩
    · refine ⟨A - WA, by rw [← neg_sub]; exact mm_neg_mem_frontier hK hWAA,
        by rw [show A - WA - A = -WA by abel]; exact mm_neg_mem_frontier hK hWA, ?_⟩
      rw [map_sub, hsA]; linarith
  have hPBne : PB.Nonempty := by
    rcases abs_eq hD.le |>.1 hWBabs' with h | h
    · exact ⟨WB, hWB, hWBB, h⟩
    · refine ⟨B - WB, by rw [← neg_sub]; exact mm_neg_mem_frontier hK hWBB,
        by rw [show B - WB - B = -WB by abel]; exact mm_neg_mem_frontier hK hWB, ?_⟩
      rw [map_sub, map_sub, hsB, hnB]; linarith
  have hsc : Continuous fun x ↦ s x := s.continuous
  have hnc : Continuous fun x ↦ n x := n.continuous
  have hPAc : IsCompact PA := hK.2.1.of_isClosed_subset
    (isClosed_frontier.inter ((isClosed_frontier.preimage (by fun_prop)).inter
      (isClosed_eq (by fun_prop) continuous_const))) fun W hW ↦ mm_mem_of_frontier hK hW.1
  have hPBc : IsCompact PB := hK.2.1.of_isClosed_subset
    (isClosed_frontier.inter ((isClosed_frontier.preimage (by fun_prop)).inter
      (isClosed_eq (by fun_prop) continuous_const))) fun W hW ↦ mm_mem_of_frontier hK hW.1
  obtain ⟨U, ⟨hU, hUA, hDU⟩, hUmax⟩ := hPAc.exists_isMaxOn hPAne hnc.continuousOn
  obtain ⟨V, ⟨hV, hVB, hDV⟩, hVmin⟩ := hPBc.exists_isMinOn hPBne hnc.continuousOn
  have hUmax' : ∀ W ∈ frontier K, W - A ∈ frontier K → -s W = D → n W ≤ n U :=
    fun W h1 h2 h3 ↦ hUmax ⟨h1, h2, h3⟩
  have hVmin' : ∀ W ∈ frontier K, W - B ∈ frontier K → n W - s W = D → n V ≤ n W :=
    fun W h1 h2 h3 ↦ hVmin ⟨h1, h2, h3⟩
  have hUK := mm_mem_of_frontier hK hU
  have hUAK := mm_mem_of_frontier hK hUA
  have hVK := mm_mem_of_frontier hK hV
  have hVBK := mm_mem_of_frontier hK hVB
  have hΔU : |cross A U| = minimalDeterminant K := by
    rw [hcA, abs_mul, ← hDκ, ← hDU, abs_of_pos (by linarith)]
  have hΔV : |cross B V| = minimalDeterminant K := by
    rw [hcB, abs_mul, ← hDκ, hDV, abs_of_pos hD]
  -- heights strictly between `0` and `1` (`ml3_slide`)
  have hnU : 0 < n U ∧ n U < 1 := by
    have h1 := hn U hUK
    have h2 := hn _ (hK.2.2.2 _ hUAK)
    rw [map_neg, map_sub, hnA] at h2
    refine ⟨lt_of_le_of_ne (by linarith) fun h ↦ hnot ?_, lt_of_le_of_ne h1 fun h ↦ hnot ?_⟩
    · exact ml3_slide hK f hf3 hfA hf1 (by rw [← hnf, ← h]) hU hΔU
    · refine ml3_slide hK f hf3 hfA hf1 (by rw [← hnf, map_sub, h, hnA, sub_self]) hUA ?_
      rw [show cross A (U - A) = cross A U by simp only [cross, Pi.sub_apply]; ring, hΔU]
  have hfB : f B = 1 := hfp tB
  have hnV : 0 < n V ∧ n V < 1 := by
    have h1 := hn V hVK
    have h2 := hn _ (hK.2.2.2 _ hVBK)
    rw [map_neg, map_sub, hnB] at h2
    refine ⟨lt_of_le_of_ne (by linarith) fun h ↦ hnot ?_, lt_of_le_of_ne h1 fun h ↦ hnot ?_⟩
    · exact ml3_slide hK f hf3 hfB hf1 (by rw [← hnf, ← h]) hV hΔV
    · refine ml3_slide hK f hf3 hfB hf1 (by rw [← hnf, map_sub, h, hnB, sub_self]) hVB ?_
      rw [show cross B (V - B) = cross B V by simp only [cross, Pi.sub_apply]; ring, hΔV]
  have hlt := ml3_n_lt hK hdec hsA hnA hsB hnB hAK hBK hU hUA hV hVB (by linarith) (by linarith)
    hnU hnV
  -- the chord `[U, V]`
  have hM2 := ml3_chord hirr hκ hdec hsA hnA hsB hnB hAF hBF hn hU hUA hV hVB hD hDU hDV hnU hnV
    hUmax' hVmin' hgap
  -- the chord `[U - A, V - B]`: the reflected pairs `B - V, A - U` in the frame of `[B, A]`
  have hκ' : cross (A - B) B ≠ 0 := by
    rw [show cross (A - B) B = -cross (B - A) A by simp only [cross, Pi.sub_apply]; ring]
    exact neg_ne_zero.2 hκ
  have hdec' : ∀ x, x = (n - s) x • (A - B) + n x • B := fun x ↦ by
    conv_lhs => rw [hdec x]
    simp only [sub_apply]
    module
  have hU'F : B - V ∈ frontier K := by rw [← neg_sub]; exact mm_neg_mem_frontier hK hVB
  have hU'B : B - V - B ∈ frontier K := by
    rw [show B - V - B = -V by abel]; exact mm_neg_mem_frontier hK hV
  have hV'F : A - U ∈ frontier K := by rw [← neg_sub]; exact mm_neg_mem_frontier hK hUA
  have hV'A : A - U - A ∈ frontier K := by
    rw [show A - U - A = -U by abel]; exact mm_neg_mem_frontier hK hU
  have hM3' := ml3_chord hirr (A := B) (B := A) (U := B - V) (V := A - U) (s := n - s) (n := n)
    hκ' hdec' (by simp [hsB, hnB]) hnB (by simp [hsA, hnA]) hnA hBF hAF hn hU'F hU'B hV'F hV'A hD
    (by simp only [sub_apply, map_sub, hsB, hnB]; linarith)
    (by simp only [sub_apply, map_sub, hsA, hnA]; linarith)
    ⟨by rw [map_sub, hnB]; linarith [hnV.2], by rw [map_sub, hnB]; linarith [hnV.1]⟩
    ⟨by rw [map_sub, hnA]; linarith [hnU.2], by rw [map_sub, hnA]; linarith [hnU.1]⟩
    (fun W h1 h2 h3 ↦ by
      have := hVmin' (B - W) (by rw [← neg_sub]; exact mm_neg_mem_frontier hK h2)
        (by rw [show B - W - B = -W by abel]; exact mm_neg_mem_frontier hK h1)
        (by simp only [sub_apply] at h3
            rw [map_sub, map_sub, hsB, hnB]; linarith)
      rw [map_sub, hnB] at this; rw [map_sub, hnB]; linarith)
    (fun W h1 h2 h3 ↦ by
      have := hUmax' (A - W) (by rw [← neg_sub]; exact mm_neg_mem_frontier hK h2)
        (by rw [show A - W - A = -W by abel]; exact mm_neg_mem_frontier hK h1)
        (by simp only [sub_apply] at h3
            rw [map_sub, hsA]; linarith)
      rw [map_sub, hnA] at this; rw [map_sub, hnA]; linarith)
    (fun t ht0 ht1 hΛ ↦ hgap (1 - t) (by linarith) (by linarith)
      (by rw [show A + (1 - t) • (B - A) = B + t • (A - B) by module]; exact hΛ))
  have hM3 : (1 / 2 : ℝ) • ((U - A) + (V - B)) ∈ frontier K := by
    have := mm_neg_mem_frontier hK hM3'
    convert this using 1; module
  exact ml3_quadratic hK hκ hdec hsA hnA hsB hnB hAF hBF hn hU hUA hV hVB hD hDU hDV hlt hΔU
    hM2 hM3

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
