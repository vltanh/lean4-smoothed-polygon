module

public import External.Mahler1947
public import Basic.Algebra.Module.ZLattice.PlaneCritical

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

A weak form of the "only if" half of Lemma 3 (a critical-lattice point on each support line).
`mahler_irreducible`: if `K` is irreducible, then every tac-line `ℓ` of `K` passes through a point
of a critical lattice `Λ` of `K`; the point is one of the six points `±P₀, ±P₁, ±P₂` of a
configuration of Mahler's Lemma 2 (Minkowski: `P₀, P₁` a basis of `Λ`, `P₁ = P₀ + P₂`, the three
points on the boundary of `K`). `mahler_irreducible_exposed`: in particular, a boundary point that
is the only point of `K` on some tac-line (an exposed point) belongs to a critical lattice of `K`;
this is the "only if" half of Lemma 3 at the exposed points. When `ℓ ∩ K` is a segment, the
theorem gives a point of a critical lattice on the segment, which need not be a given point of it.

Departure from the source: Mahler 1947 states Lemma 3 without proof, referring to Lemmas 8 and 12
of his paper A, whose proofs we do not have. We prove the statement above by the classical
shaving argument. Shaving `K` along a tac-line `ℓ` only shows that `ℓ ∩ K` contains a point of a
critical lattice; when `ℓ ∩ K` is a segment this does not reach every point of the segment, so the
half "only if" is proved only at the exposed points (the other points lie on segments of the
boundary, possibly as endpoints). The half "if" is not proved; it is not used.

## Proof

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

Departure from the source: Mahler states Lemma 3 (irreducible iff every boundary point belongs to
a critical lattice) without proof, referring to Lemmas 8 and 12 of his paper A. We prove, by
shaving `K` along `±ℓ`, that `ℓ ∩ K` contains a point of a critical lattice; for a boundary point
that is the only point of `K` on a tac-line this is the corresponding case of Lemma 3
(`mahler_irreducible_exposed`). The other boundary points (on segments of the boundary) and the
converse are not treated. -/
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

end External
