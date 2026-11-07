module

public import External.MahlerIrreducible

/-!
# Mahler 1946, Theorems B and C; paper A, Lemmas 10, 11 and class B of Lemma 13

K. Mahler, *Lattice points in n-dimensional star bodies II. Reducibility theorems I*, Proc. Kon.
Ned. Akad. Wet. 49 (1946), 331–343 (scan: Mahler's collected works, CARMA archive, item 088),
Theorems B (p. 334, proof pp. 335–336) and C (pp. 336–338), and their use in K. Mahler, *On
irreducible convex domains*, Proc. Kon. Ned. Akad. Wet. 50 (1947), 98–107 ("paper A"): Lemma 10
("proof of Theorem C"), Lemma 11 ("special case of Theorem B"), both p. 104, and the first case
("class B") of the proof of Lemma 13, pp. 104–105. The proof of Mahler 1947, Lemma 3
(`External.MahlerIrreducible.Lemma3`, `MahlerIrreducible.ml3_onlyIf`) uses `lemma11` and
`m46c_classB`.

## Mahler's setting, and how it is specialized

In the 1946 paper (p. 332) a *distance function* `F` on `Rₙ` satisfies `F(X) ≥ 0`, `F(O) = 0`,
`F(tX) = |t| F(X)` for all real `t`, and is continuous; `K : F(X) ≤ 1` is a *star body*
(`m46c_IsDistanceFunction`, `m46c_IsStarBody`; so star bodies are symmetric in `O`). A lattice is
`K`-admissible if `O` is its only point inside `K`, `Δ(K)` is the lower bound of `d(Λ)` over these,
and a critical lattice is an admissible one with `d(Λ) = Δ(K)`: these are `IsAdmissible`,
`minimalDeterminant`, `IsCritical` of `External.MinkowskiMahler`, which make sense for any set.
`H < K` means that `H` is a proper subset of `K`, and `H ≺ K` that moreover `Δ(H) = Δ(K)`
(pp. 333–334); Definition A (p. 334): `K` is *reducible* if a star body `H ≺ K` exists
(`m46c_IsReducible`), *irreducible* otherwise.

Readings. Everything is in the plane (`n = 2`), and the body `K` of Theorems B and C is a symmetric
convex domain (`IsSymmetricConvexDomain`), whose distance function is its gauge `gauge K`
(`m46c_isStarBody`); this is all that paper A needs (it applies Theorems B and C to convex
domains). The auxiliary body `H` of Theorem C is a star body that is in general not convex; we keep
it a star body (`lemma10`) and make it convex afterwards by paper A's cut by a line
(`m46c_classB`), as Mahler does. Mahler's `|X|` is the Euclidean length; in the direction
`|X|⁻¹X` (`m46c_dir`) we use the norm of `Fin 2 → ℝ` (the sup norm), since only the continuity of
`X ↦ |X|⁻¹X` off `O`, its invariance under `X ↦ tX` (`t > 0`), and the fact that it determines
the ray of `X` are used. The two results of Part I (Proc. Roy. Soc.) that the proofs quote are
proved in the plane: Theorem 2, the selection theorem (`m46c_theorem2`, by Lagrange–Gauss reduced
bases, `PlaneLattice.exists_reduced_basis`), and Theorem 8, the existence of critical lattices
(`m46c_theorem8`, from `PlaneLattice.exists_admissible_covolume_le`).

## What is proved

* `theoremB` (Theorem B) by Mahler's proof: Theorem 2 gives a convergent subsequence of the
  lattices with convergent reduced bases; the integer coordinates of `P_r` (Cramer's rule)
  converge to integers, so `P` lies on the limit lattice, which is admissible and critical.
* `lemma11` (paper A, Lemma 11): the set `Π` of boundary points on critical lattices is closed, as
  the special case of Theorem B with critical lattices.
* `lemma10` (paper A, Lemma 10, i.e. the proof of Theorem C) and `theoremC` (Theorem C) by
  Mahler's proof: a cone `S` around `P` meeting no critical lattice (`m46c_step1`, by Theorem B);
  a determinant gap `d(Λ) ≥ (1 + δ)² Δ(K)` for admissible lattices through `S` (`m46c_step2`, by
  Theorem B); the body `H : G ≤ 1` with `Δ(H) = Δ(K)` (the end of `lemma10`).
* `m46c_classB` (paper A, Lemma 13, class B): by Lemma 10 and the cut of `K` by a line `L` and its
  mirror image `-L`.

## Errors and gaps, and their repair

* **Error in Mahler 1946** (proof of Theorem C, p. 337): the function
  `G(X) = F(X){1 + (δ/σ) max(0, σ - ||X|⁻¹X - |P|⁻¹P|)}` is not a distance function, since it is
  not even: `G(P) = (1 + δ) F(P)` but `G(-P) = F(P)` (for `σ ≤ 2`), so `H : G ≤ 1` contains `-P`
  but not `P` and is not a star body (`m46c_mahlerG_not_distanceFunction`), whereas paper A's
  Lemma 10 asserts that `H` omits both points `±P`. Repair: measure the distance from `|X|⁻¹X` to
  the nearer of the two directions `±|P|⁻¹P` (`m46c_ω`, `m46c_G`). The rest of the proof is
  unchanged, except that in its last step one of the two points `±λQ_s` (instead of `λQ_s`) lies
  in `S`; both lie on `Λ*`.
* **Gap in paper A** (proof of Lemma 13, class B): the existence of a line `L'` through `P` with no
  point in common with `H'` is not shown (it fails for points of class A, which is why the classes
  are distinguished). We fill it along Mahler's lines (`m46c_line`): a support line at the extreme
  point `P`, tilted slightly about `P`, misses the compact set `H' ∌ P`. Mahler also asks that `L'`
  not be a tac-line of `C` at `P`; this is not used (`H ≠ K` because `P` lies beyond `L`), and our
  `L'` may be one.
* Paper A's Lemma 10 assumes `K` reducible; the hypothesis is not used, and `lemma10` omits it.
-/

@[expose] public section

namespace External

namespace Mahler1946

open Set Filter Topology MinkowskiMahler MahlerIrreducible

variable {K : Set (Fin 2 → ℝ)}

/-! ### Theorem 2 of Part I (the selection theorem), in the plane -/

/-- `‖x‖² ≤ x₀² + x₁²` for the sup norm. -/
lemma m46c_norm_sq_le (x : Fin 2 → ℝ) : ‖x‖ ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2 := by
  have hs : 0 ≤ Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := Real.sqrt_nonneg _
  have hle : ‖x‖ ≤ Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg hs).2 fun i ↦ ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  calc ‖x‖ ^ 2 ≤ Real.sqrt (x 0 ^ 2 + x 1 ^ 2) ^ 2 := by gcongr
    _ = x 0 ^ 2 + x 1 ^ 2 := Real.sq_sqrt (by positivity)

lemma m46c_norm_le_of_sq {x : Fin 2 → ℝ} {B : ℝ} (h : x 0 ^ 2 + x 1 ^ 2 ≤ B) :
    ‖x‖ ≤ B + 1 := by
  have h1 := m46c_norm_sq_le x
  nlinarith [norm_nonneg x]

/-- **Mahler 1946, Part I, Theorem 2** (quoted on p. 332 of Part II), in the plane: *every bounded
infinite sequence of lattices contains a convergent infinite subsequence (i.e., reduced bases of
its elements tend to a basis of the limiting lattice)*. A sequence `Λ_r` is *bounded* if
`d(Λ_r) ≤ D` and `|X| ≥ ρ > 0` for every point `X ≠ O` of every `Λ_r`. The reduced bases are
those of Lagrange–Gauss (`PlaneLattice.exists_reduced_basis`): `|u|² ≥ ρ²`, `|u| ≤ |v|` and
`2|u · v| ≤ |u|²`, so `det(u, v)² ≥ ¾|u|²|v|²` (Lagrange's identity) bounds `|v|² ≤ 4D²/(3ρ²)` and
keeps `det(u, v)² ≥ ¾ρ⁴`. -/
theorem m46c_theorem2 {Λ : ℕ → Submodule ℤ (Fin 2 → ℝ)} (hlat : ∀ r, IsLattice (Λ r))
    {D ρ : ℝ} (hρ : 0 < ρ) (hD : ∀ r, det (Λ r) ≤ D)
    (hmin : ∀ r, ∀ x ∈ Λ r, x ≠ 0 → ρ ≤ ‖x‖) :
    ∃ (u v : ℕ → Fin 2 → ℝ) (u₀ v₀ : Fin 2 → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ r, IsBasis (Λ r) (u r) (v r) ∧ cross (u r) (v r) ≠ 0) ∧
      Tendsto (fun r ↦ u (φ r)) atTop (𝓝 u₀) ∧ Tendsto (fun r ↦ v (φ r)) atTop (𝓝 v₀) ∧
      cross u₀ v₀ ≠ 0 := by
  set B : ℝ := 4 / 3 * D ^ 2 / ρ ^ 2 with hB
  have hred : ∀ r, ∃ u v : Fin 2 → ℝ, (IsBasis (Λ r) u v ∧ cross u v ≠ 0) ∧
      ‖u‖ ≤ B + 1 ∧ ‖v‖ ≤ B + 1 ∧ 3 / 4 * ρ ^ 4 ≤ cross u v ^ 2 := by
    intro r
    obtain ⟨hd, hs⟩ := hlat r
    have := hd
    have : IsZLattice ℝ (Λ r) := ⟨hs⟩
    obtain ⟨u, v, hspan, hcr, -, huv, hip⟩ := PlaneLattice.exists_reduced_basis (Λ r)
    have hcr' : cross u v ≠ 0 := hcr
    have hbas : IsBasis (Λ r) u v := ⟨mm_linearIndependent hcr', hspan⟩
    have hdet := mm_det_eq (hlat r) hbas
    have huΛ : u ∈ Λ r := hspan ▸ Submodule.subset_span (by simp)
    have hu0 : u ≠ 0 := by rintro rfl; simp [cross] at hcr'
    have hρu := hmin r u huΛ hu0
    have hρu2 : ρ ^ 2 ≤ u 0 ^ 2 + u 1 ^ 2 :=
      (pow_le_pow_left₀ hρ.le hρu 2).trans (m46c_norm_sq_le u)
    have hcrD : cross u v ^ 2 ≤ D ^ 2 := by
      have h1 : |cross u v| ≤ D := hdet ▸ hD r
      have h2 : 0 ≤ |cross u v| := abs_nonneg _
      calc cross u v ^ 2 = |cross u v| ^ 2 := (sq_abs _).symm
        _ ≤ D ^ 2 := by gcongr
    -- Lagrange's identity
    have hlag : cross u v ^ 2 + (u 0 * v 0 + u 1 * v 1) ^ 2 =
        (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by simp only [cross]; ring
    have hip2 : (u 0 * v 0 + u 1 * v 1) ^ 2 ≤
        (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) / 4 := by
      have h1 : 4 * (u 0 * v 0 + u 1 * v 1) ^ 2 ≤ (u 0 ^ 2 + u 1 ^ 2) ^ 2 := by
        have := sq_abs (u 0 * v 0 + u 1 * v 1)
        nlinarith [abs_nonneg (u 0 * v 0 + u 1 * v 1)]
      nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    have hv2 : v 0 ^ 2 + v 1 ^ 2 ≤ B := by
      rw [hB, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have hlow : 3 / 4 * ρ ^ 4 ≤ cross u v ^ 2 := by
      have h1 : ρ ^ 2 * ρ ^ 2 ≤ (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) :=
        mul_le_mul hρu2 (hρu2.trans huv) (by positivity) (by positivity)
      nlinarith
    exact ⟨u, v, ⟨hbas, hcr'⟩, m46c_norm_le_of_sq (huv.trans hv2), m46c_norm_le_of_sq hv2,
      hlow⟩
  choose u v huv hu hv hlow using hred
  have hmem : ∀ r, (u r, v r) ∈ Metric.closedBall (0 : Fin 2 → ℝ) (B + 1) ×ˢ
      Metric.closedBall (0 : Fin 2 → ℝ) (B + 1) :=
    fun r ↦ ⟨mem_closedBall_zero_iff.2 (hu r), mem_closedBall_zero_iff.2 (hv r)⟩
  obtain ⟨⟨u₀, v₀⟩, -, φ, hφ, hlim⟩ :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).tendsto_subseq hmem
  have tu : Tendsto (fun r ↦ u (φ r)) atTop (𝓝 u₀) := hlim.fst_nhds
  have tv : Tendsto (fun r ↦ v (φ r)) atTop (𝓝 v₀) := hlim.snd_nhds
  have hcc : Continuous fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) ↦ cross p.1 p.2 := by
    simp only [cross]; fun_prop
  have tcr : Tendsto (fun r ↦ cross (u (φ r)) (v (φ r)) ^ 2) atTop (𝓝 (cross u₀ v₀ ^ 2)) :=
    ((hcc.tendsto _).comp (tu.prodMk_nhds tv)).pow 2
  have h0 : 3 / 4 * ρ ^ 4 ≤ cross u₀ v₀ ^ 2 :=
    ge_of_tendsto tcr (Eventually.of_forall fun r ↦ hlow (φ r))
  refine ⟨u, v, u₀, v₀, φ, hφ, huv, tu, tv, fun h ↦ ?_⟩
  rw [h] at h0
  have : 0 < ρ ^ 4 := by positivity
  linarith

/-! ### Theorem B -/

/-- **Mahler 1946, Theorem B** (p. 334), for a symmetric convex domain `K` in the plane: *let
`Λ₁, Λ₂, Λ₃, …` be an infinite sequence of `K`-admissible lattices with the following properties:
(a) `lim d(Λ_r) = Δ(K)`; (b) every lattice `Λ_r` contains a point `P_r` on the boundary `C` of
`K`; (c) the points `P₁, P₂, P₃, …` tend to a limit point `P`. Then `P` lies on `C`, and there
exists a critical lattice `Λ` of `K` containing `P`.*

Mahler's proof (pp. 335–336): the sequence of lattices is bounded, so by Theorem 2
(`m46c_theorem2`) a subsequence converges, with reduced bases `Y₁⁽ʳ⁾, Y₂⁽ʳ⁾` tending to a basis
`Y₁, Y₂` of the limit lattice `Λ`. The coordinates `u_g⁽ʳ⁾` of `P⁽ʳ⁾` in these bases are integers,
given by Cramer's rule, so they converge to the coordinates of `P` in `Y₁, Y₂`, which are therefore
integers: `P` is a point of `Λ`. "As in earlier proofs", `Λ` is `K`-admissible, and so critical. -/
theorem theoremB (hK : IsSymmetricConvexDomain K) {Λ : ℕ → Submodule ℤ (Fin 2 → ℝ)}
    (hlat : ∀ r, IsLattice (Λ r)) (hadm : ∀ r, IsAdmissible K (Λ r))
    (hdet : Tendsto (fun r ↦ det (Λ r)) atTop (𝓝 (minimalDeterminant K)))
    {P : ℕ → Fin 2 → ℝ} (hPΛ : ∀ r, P r ∈ Λ r) (hPC : ∀ r, P r ∈ frontier K)
    {P₀ : Fin 2 → ℝ} (hP : Tendsto P atTop (𝓝 P₀)) :
    P₀ ∈ frontier K ∧ ∃ L, IsCritical K L ∧ P₀ ∈ L := by
  refine ⟨isClosed_frontier.mem_of_tendsto hP (Eventually.of_forall hPC), ?_⟩
  -- the sequence of lattices is bounded
  obtain ⟨D, hD⟩ := hdet.bddAbove_range
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior 0 (mm_zero_mem_interior hK)
  have hmin : ∀ r, ∀ x ∈ Λ r, x ≠ 0 → ε ≤ ‖x‖ := by
    intro r x hx hx0
    by_contra h
    push Not at h
    exact hx0 (hadm r x hx (hball (mem_ball_zero_iff.2 h)))
  -- Theorem 2: a convergent subsequence
  obtain ⟨u, v, u₀, v₀, φ, hφ, hB, tu, tv, hcr⟩ :=
    m46c_theorem2 hlat hε (fun r ↦ hD ⟨r, rfl⟩) hmin
  have hcc : Continuous fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) ↦ cross p.1 p.2 := by
    simp only [cross]; fun_prop
  have tcr : Tendsto (fun r ↦ cross (u (φ r)) (v (φ r))) atTop (𝓝 (cross u₀ v₀)) :=
    (hcc.tendsto _).comp (tu.prodMk_nhds tv)
  have hdetφ : Tendsto (fun r ↦ det (Λ (φ r))) atTop (𝓝 (minimalDeterminant K)) :=
    hdet.comp hφ.tendsto_atTop
  have habs : |cross u₀ v₀| = minimalDeterminant K :=
    tendsto_nhds_unique tcr.abs
      (hdetφ.congr fun r ↦ mm_det_eq (hlat (φ r)) (hB (φ r)).1)
  -- the limit lattice is `K`-admissible
  have hadm₀ : IsAdmissible K (Submodule.span ℤ {u₀, v₀}) := by
    intro y hy hyK
    obtain ⟨m, k, rfl⟩ := mm_mem_span_pair.1 hy
    have ty : Tendsto (fun r ↦ (m : ℝ) • u (φ r) + (k : ℝ) • v (φ r)) atTop
        (𝓝 ((m : ℝ) • u₀ + (k : ℝ) • v₀)) := (tu.const_smul _).add (tv.const_smul _)
    have e1 : ∀ᶠ r in atTop, (m : ℝ) • u (φ r) + (k : ℝ) • v (φ r) ∈ interior K :=
      ty (isOpen_interior.mem_nhds hyK)
    have e3 : ∀ᶠ r in atTop, (m : ℝ) • u (φ r) + (k : ℝ) • v (φ r) = 0 := by
      filter_upwards [e1] with r h1
      have hmem : (m : ℝ) • u (φ r) + (k : ℝ) • v (φ r) ∈ Λ (φ r) := by
        rw [← (hB (φ r)).1.2]; exact mm_mem_span_pair.2 ⟨m, k, rfl⟩
      exact hadm (φ r) _ hmem h1
    exact tendsto_nhds_unique ty
      ((tendsto_const_nhds (x := (0 : Fin 2 → ℝ))).congr' (e3.mono fun r h ↦ h.symm))
  have hcrit : IsCritical K (Submodule.span ℤ {u₀, v₀}) :=
    ⟨mm_isLattice_span hcr, hadm₀, by rw [mm_det_span hcr, habs]⟩
  -- the coordinates of `P_r` are integers (Cramer's rule), and so are their limits
  have hcoef : ∀ r, ∃ m k : ℤ, cross (P r) (v r) / cross (u r) (v r) = m ∧
      cross (u r) (P r) / cross (u r) (v r) = k := by
    intro r
    have hx := hPΛ r
    rw [← (hB r).1.2] at hx
    obtain ⟨m, k, hmk⟩ := mm_mem_span_pair.1 hx
    refine ⟨m, k, ?_, ?_⟩
    · rw [← hmk, mm_cross_smul_add, mm_cross_self]; field_simp [(hB r).2]; ring
    · rw [← hmk, mm_cross_add_smul, mm_cross_self]; field_simp [(hB r).2]; ring
  choose m k hm hk using hcoef
  have tP : Tendsto (fun r ↦ P (φ r)) atTop (𝓝 P₀) := hP.comp hφ.tendsto_atTop
  have ta : Tendsto (fun r ↦ cross (P (φ r)) (v (φ r)) / cross (u (φ r)) (v (φ r))) atTop
      (𝓝 (cross P₀ v₀ / cross u₀ v₀)) :=
    (((hcc.tendsto _).comp (tP.prodMk_nhds tv))).div tcr hcr
  have tb : Tendsto (fun r ↦ cross (u (φ r)) (P (φ r)) / cross (u (φ r)) (v (φ r))) atTop
      (𝓝 (cross u₀ P₀ / cross u₀ v₀)) :=
    (((hcc.tendsto _).comp (tu.prodMk_nhds tP))).div tcr hcr
  have ha : cross P₀ v₀ / cross u₀ v₀ ∈ range ((↑) : ℤ → ℝ) :=
    Real.isClosed_range_intCast.mem_of_tendsto ta
      (Eventually.of_forall fun r ↦ ⟨m (φ r), (hm (φ r)).symm⟩)
  have hb : cross u₀ P₀ / cross u₀ v₀ ∈ range ((↑) : ℤ → ℝ) :=
    Real.isClosed_range_intCast.mem_of_tendsto tb
      (Eventually.of_forall fun r ↦ ⟨k (φ r), (hk (φ r)).symm⟩)
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  refine ⟨_, hcrit, ?_⟩
  rw [mm_eq_comb hcr P₀, ← ha, ← hb]
  exact mm_mem_span_pair.2 ⟨a, b, rfl⟩

/-- **Mahler, paper A, Lemma 11** (p. 104; "special case of Theorem B" of the 1946 paper), for a
symmetric convex domain `K`: *let `Π` be the set of all points on `C` which belong to at least one
critical lattice of `K`. Then `Π` is a closed set.* A limit of points of `Π` on critical lattices
`Λ_r` is, by Theorem B (`d(Λ_r) = Δ(K)` for all `r`), on a critical lattice. -/
theorem lemma11 (hK : IsSymmetricConvexDomain K) :
    IsClosed {x | x ∈ frontier K ∧ ∃ Λ, IsCritical K Λ ∧ x ∈ Λ} := by
  refine IsSeqClosed.isClosed fun {xs x} hxs hlim ↦ ?_
  choose hF Λ hΛ hxΛ using hxs
  exact theoremB hK (fun r ↦ (hΛ r).1) (fun r ↦ (hΛ r).2.1)
    (tendsto_const_nhds.congr fun r ↦ (hΛ r).2.2.symm) hxΛ hF hlim

/-! ### Star bodies -/

/-- A *distance function* (Mahler 1946, p. 332, in the plane): `F(X) ≥ 0`, `F(tX) = |t| F(X)` for
all real `t` (so `F(O) = 0`), and `F` is continuous. -/
def m46c_IsDistanceFunction (F : (Fin 2 → ℝ) → ℝ) : Prop :=
  (∀ x, 0 ≤ F x) ∧ (∀ (t : ℝ) x, F (t • x) = |t| * F x) ∧ Continuous F

/-- A *star body* `K : F(X) ≤ 1` (Mahler 1946, p. 332), `F` a distance function. -/
def m46c_IsStarBody (H : Set (Fin 2 → ℝ)) : Prop :=
  ∃ F, m46c_IsDistanceFunction F ∧ H = {x | F x ≤ 1}

/-- **Mahler 1946, Definition A** (p. 334): *the star body `K` is called reducible if there exists
a star body `H` such that `H ≺ K`*, i.e. `H` is a proper subset of `K` with `Δ(H) = Δ(K)`; it is
*irreducible* otherwise. -/
def m46c_IsReducible (K : Set (Fin 2 → ℝ)) : Prop :=
  ∃ H, m46c_IsStarBody H ∧ H ⊆ K ∧ H ≠ K ∧ minimalDeterminant H = minimalDeterminant K

/-- A star body is symmetric in `O` ("contains, and is symmetrical in, the origin", p. 332). -/
lemma m46c_starBody_neg {H : Set (Fin 2 → ℝ)} (hH : m46c_IsStarBody H) {x : Fin 2 → ℝ}
    (hx : x ∈ H) : -x ∈ H := by
  obtain ⟨F, ⟨-, hF, -⟩, rfl⟩ := hH
  have := hF (-1) x
  simp only [neg_smul, one_smul, abs_neg, abs_one, one_mul] at this
  simpa [this] using hx

/-- `O` is an inner point of a star body. -/
lemma m46c_starBody_zero {H : Set (Fin 2 → ℝ)} (hH : m46c_IsStarBody H) :
    (0 : Fin 2 → ℝ) ∈ interior H := by
  obtain ⟨F, ⟨-, hF, hc⟩, rfl⟩ := hH
  have h0 : F 0 = 0 := by simpa using hF 0 0
  exact interior_maximal (t := {x | F x < 1}) (fun x (hx : F x < 1) ↦ show F x ≤ 1 from hx.le)
    (isOpen_lt hc continuous_const) (show F 0 < 1 by rw [h0]; norm_num)

/-! ### The distance function `F` of a symmetric convex domain: its gauge -/

lemma m46c_nhds (hK : IsSymmetricConvexDomain K) : K ∈ 𝓝 (0 : Fin 2 → ℝ) :=
  mem_interior_iff_mem_nhds.1 (mm_zero_mem_interior hK)

lemma m46c_gauge_continuous (hK : IsSymmetricConvexDomain K) : Continuous (gauge K) :=
  continuous_gauge hK.1 (m46c_nhds hK)

lemma m46c_gauge_smul (hK : IsSymmetricConvexDomain K) (t : ℝ) (x : Fin 2 → ℝ) :
    gauge K (t • x) = |t| * gauge K x := by
  rcases le_or_gt 0 t with ht | ht
  · rw [gauge_smul_of_nonneg ht, abs_of_nonneg ht, smul_eq_mul]
  · rw [show t • x = (-t) • (-x) by rw [neg_smul_neg], gauge_smul_of_nonneg (by linarith),
      gauge_neg hK.2.2.2, abs_of_neg ht, smul_eq_mul]

lemma m46c_gauge_lt_one (hK : IsSymmetricConvexDomain K) {x : Fin 2 → ℝ} :
    gauge K x < 1 ↔ x ∈ interior K :=
  gauge_lt_one_iff_mem_interior hK.1 (m46c_nhds hK)

lemma m46c_gauge_le_one (hK : IsSymmetricConvexDomain K) {x : Fin 2 → ℝ} :
    gauge K x ≤ 1 ↔ x ∈ K := by
  rw [gauge_le_one_iff_mem_closure hK.1 (m46c_nhds hK), (mm_isClosed hK).closure_eq]

lemma m46c_gauge_eq_one (hK : IsSymmetricConvexDomain K) {x : Fin 2 → ℝ} :
    gauge K x = 1 ↔ x ∈ frontier K :=
  gauge_eq_one_iff_mem_frontier hK.1 (m46c_nhds hK)

lemma m46c_gauge_pos (hK : IsSymmetricConvexDomain K) {x : Fin 2 → ℝ} (hx : x ≠ 0) :
    0 < gauge K x :=
  (gauge_pos (absorbent_nhds_zero (m46c_nhds hK))
    ((NormedSpace.isVonNBounded_iff ℝ).2 hK.2.1.isBounded)).2 hx

/-- A symmetric convex domain is a star body, `K : F(X) ≤ 1` with `F` its gauge. -/
lemma m46c_isStarBody (hK : IsSymmetricConvexDomain K) : m46c_IsStarBody K :=
  ⟨gauge K, ⟨gauge_nonneg, m46c_gauge_smul hK, m46c_gauge_continuous hK⟩,
    by ext x; exact (m46c_gauge_le_one hK).symm⟩

/-! ### Directions -/

/-- The direction `|X|⁻¹ X` of a point `X` (`|·|` the norm of `Fin 2 → ℝ`; `O` for `X = O`). -/
noncomputable def m46c_dir (x : Fin 2 → ℝ) : Fin 2 → ℝ := ‖x‖⁻¹ • x

lemma m46c_dir_smul {t : ℝ} (ht : 0 < t) (x : Fin 2 → ℝ) : m46c_dir (t • x) = m46c_dir x := by
  simp only [m46c_dir, norm_smul, Real.norm_eq_abs, abs_of_pos ht, smul_smul, mul_inv]
  rcases eq_or_ne ‖x‖ 0 with h | h
  · rw [norm_eq_zero.1 h]; simp
  · congr 1; field_simp

lemma m46c_dir_neg (x : Fin 2 → ℝ) : m46c_dir (-x) = -m46c_dir x := by
  simp [m46c_dir]

lemma m46c_dir_continuousAt {x : Fin 2 → ℝ} (hx : x ≠ 0) : ContinuousAt m46c_dir x :=
  ((continuous_norm.continuousAt).inv₀ (norm_ne_zero_iff.2 hx)).smul continuousAt_id

lemma m46c_eq_smul_dir (x : Fin 2 → ℝ) : x = ‖x‖ • m46c_dir x := by
  rcases eq_or_ne x 0 with rfl | h
  · simp
  · rw [m46c_dir, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_smul]

lemma m46c_norm_dir {x : Fin 2 → ℝ} (hx : x ≠ 0) : ‖m46c_dir x‖ = 1 := by
  rw [m46c_dir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]

/-- Every ray from `O` meets `C` only once. -/
lemma m46c_eq_of_dir (hK : IsSymmetricConvexDomain K) {x y : Fin 2 → ℝ} (hx : x ∈ frontier K)
    (hy : y ∈ frontier K) (h : m46c_dir x = m46c_dir y) : x = y := by
  have hxy : y = (‖y‖ / ‖x‖) • x :=
    calc y = ‖y‖ • m46c_dir y := m46c_eq_smul_dir y
      _ = ‖y‖ • (‖x‖⁻¹ • x) := by rw [← h]; rfl
      _ = (‖y‖ / ‖x‖) • x := by rw [smul_smul, div_eq_mul_inv]
  have h1 := (m46c_gauge_eq_one hK).2 hy
  rw [hxy, m46c_gauge_smul hK, (m46c_gauge_eq_one hK).2 hx, mul_one,
    abs_of_nonneg (by positivity)] at h1
  rw [hxy, h1, one_smul]

/-! ### Mahler's body `H : G(X) ≤ 1`, corrected -/

/-- **Mahler's function `G`, as printed** (1946, p. 337), with `F` the gauge of `K`:
`G(X) = F(X){1 + (δ/σ) max(0, σ - ||X|⁻¹X - |P|⁻¹P|)}`. It is not a distance function
(`m46c_mahlerG_not_distanceFunction`); we use `m46c_G` instead. -/
noncomputable def m46c_mahlerG (K : Set (Fin 2 → ℝ)) (P : Fin 2 → ℝ) (σ δ : ℝ)
    (x : Fin 2 → ℝ) : ℝ :=
  gauge K x * (1 + δ / σ * max 0 (σ - ‖m46c_dir x - m46c_dir P‖))

/-- **Error in Mahler 1946** (proof of Theorem C, p. 337: "so that `G(X)` is a distance
function"): Mahler's `G` is not even, `G(P) = 1 + δ` but `G(-P) = 1` (for `0 < σ ≤ 2`, `δ > 0`), so
it is not a distance function and `H : G ≤ 1` is not a star body (it contains `-P` but not `P`). -/
lemma m46c_mahlerG_not_distanceFunction (hK : IsSymmetricConvexDomain K) {P : Fin 2 → ℝ}
    (hP : P ∈ frontier K) {σ δ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2) (hδ : 0 < δ) :
    ¬ m46c_IsDistanceFunction (m46c_mahlerG K P σ δ) := by
  rintro ⟨-, hG, -⟩
  have h := hG (-1) P
  have hP0 := mm_ne_zero_of_frontier hK hP
  have h2 : ‖m46c_dir (-P) - m46c_dir P‖ = 2 := by
    rw [m46c_dir_neg, show -m46c_dir P - m46c_dir P = (-2 : ℝ) • m46c_dir P by module,
      norm_smul, m46c_norm_dir hP0]
    norm_num
  have hF : gauge K P = 1 := (m46c_gauge_eq_one hK).2 hP
  simp only [m46c_mahlerG, neg_smul, one_smul, abs_neg, abs_one, one_mul, gauge_neg hK.2.2.2, hF,
    h2, sub_self, norm_zero, sub_zero, max_eq_left (by linarith : σ - 2 ≤ 0), max_eq_right hσ.le,
    div_mul_cancel₀ _ hσ.ne', mul_zero] at h
  linarith

/-- The distance `ω(X) = min(||X|⁻¹X - p|, ||X|⁻¹X + p|)` from the direction of `X` to the
nearer of the two directions `±p` (repair of Mahler's `||X|⁻¹X - |P|⁻¹P|`, with `p = |P|⁻¹P`). -/
noncomputable def m46c_ω (p x : Fin 2 → ℝ) : ℝ := min ‖m46c_dir x - p‖ ‖m46c_dir x + p‖

/-- The factor `1 + (δ/σ) max(0, σ - ω(X))` of Mahler's `G`, corrected. -/
noncomputable def m46c_c (p : Fin 2 → ℝ) (σ δ : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  1 + δ / σ * max 0 (σ - m46c_ω p x)

/-- **Mahler's distance function `G`, corrected**: `G(X) = F(X){1 + (δ/σ) max(0, σ - ω(X))}`, with
`F` the gauge of `K` and `ω` the distance of the direction of `X` from `±p`. -/
noncomputable def m46c_G (K : Set (Fin 2 → ℝ)) (p : Fin 2 → ℝ) (σ δ : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  gauge K x * m46c_c p σ δ x

section Body

variable {p : Fin 2 → ℝ} {σ δ : ℝ}

lemma m46c_ω_neg (x : Fin 2 → ℝ) : m46c_ω p (-x) = m46c_ω p x := by
  simp only [m46c_ω, m46c_dir_neg]
  rw [show -m46c_dir x - p = -(m46c_dir x + p) by abel,
    show -m46c_dir x + p = -(m46c_dir x - p) by abel, norm_neg, norm_neg, min_comm]

lemma m46c_c_smul {t : ℝ} (ht : t ≠ 0) (x : Fin 2 → ℝ) :
    m46c_c p σ δ (t • x) = m46c_c p σ δ x := by
  rcases ht.lt_or_gt with ht | ht
  · rw [show t • x = -((-t) • x) by rw [neg_smul, neg_neg], m46c_c, m46c_c, m46c_ω_neg]
    simp only [m46c_ω, m46c_dir_smul (neg_pos.2 ht)]
  · simp only [m46c_c, m46c_ω, m46c_dir_smul ht]

lemma m46c_c_ge (hσ : 0 < σ) (hδ : 0 ≤ δ) (x : Fin 2 → ℝ) : 1 ≤ m46c_c p σ δ x := by
  have : 0 ≤ δ / σ * max 0 (σ - m46c_ω p x) := by positivity
  simp only [m46c_c]; linarith

lemma m46c_c_le (hσ : 0 < σ) (hδ : 0 ≤ δ) (x : Fin 2 → ℝ) : m46c_c p σ δ x ≤ 1 + δ := by
  have hω : 0 ≤ m46c_ω p x := le_min (norm_nonneg _) (norm_nonneg _)
  have hm : max 0 (σ - m46c_ω p x) ≤ σ := max_le hσ.le (by linarith)
  have : δ / σ * max 0 (σ - m46c_ω p x) ≤ δ := by
    calc δ / σ * max 0 (σ - m46c_ω p x) ≤ δ / σ * σ := by gcongr
      _ = δ := div_mul_cancel₀ _ hσ.ne'
  simp only [m46c_c]; linarith

/-- `G(X) > F(X)` only if `ω(X) < σ`. -/
lemma m46c_ω_lt {x : Fin 2 → ℝ} (h : 1 < m46c_c p σ δ x) : m46c_ω p x < σ := by
  by_contra hc
  push Not at hc
  simp only [m46c_c, max_eq_left (by linarith : σ - m46c_ω p x ≤ 0), mul_zero, add_zero] at h
  exact lt_irrefl _ h

lemma m46c_c_continuousAt {x : Fin 2 → ℝ} (hx : x ≠ 0) : ContinuousAt (m46c_c p σ δ) x := by
  have hd := m46c_dir_continuousAt hx
  have hω : ContinuousAt (m46c_ω p) x :=
    ((continuous_norm.continuousAt.comp (hd.sub continuousAt_const)).min
      (continuous_norm.continuousAt.comp (hd.add continuousAt_const)))
  exact continuousAt_const.add (continuousAt_const.mul
    (continuousAt_const.max (continuousAt_const.sub hω)))

lemma m46c_c_self {P : Fin 2 → ℝ} : m46c_c (m46c_dir P) σ δ P = 1 + δ / σ * max 0 σ := by
  simp [m46c_c, m46c_ω]

/-- The corrected `G` is a distance function (Mahler: "so that `G(X)` is a distance function").
Continuity at `O` from `0 ≤ G ≤ (1 + δ) F`. -/
lemma m46c_G_isDistanceFunction (hK : IsSymmetricConvexDomain K) (hσ : 0 < σ) (hδ : 0 ≤ δ) :
    m46c_IsDistanceFunction (m46c_G K p σ δ) := by
  refine ⟨fun x ↦ mul_nonneg (gauge_nonneg x) (by linarith [m46c_c_ge (p := p) hσ hδ x]),
    fun t x ↦ ?_, continuous_iff_continuousAt.2 fun x ↦ ?_⟩
  · rcases eq_or_ne t 0 with rfl | ht
    · simp [m46c_G]
    · simp only [m46c_G, m46c_gauge_smul hK, m46c_c_smul ht]; ring
  · rcases eq_or_ne x 0 with rfl | hx
    · have hG0 : m46c_G K p σ δ 0 = 0 := by simp [m46c_G]
      rw [ContinuousAt, hG0]
      have t1 : Tendsto (fun y ↦ (1 + δ) * gauge K y) (𝓝 0) (𝓝 0) := by
        have := ((m46c_gauge_continuous hK).tendsto 0).const_mul (1 + δ)
        simpa using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds t1 (fun y ↦ ?_)
        (fun y ↦ ?_)
      · exact mul_nonneg (gauge_nonneg y) (by linarith [m46c_c_ge (p := p) hσ hδ y])
      · simp only [m46c_G]
        rw [mul_comm (1 + δ)]
        exact mul_le_mul_of_nonneg_left (m46c_c_le hσ hδ y) (gauge_nonneg y)
    · exact (m46c_gauge_continuous hK).continuousAt.mul (m46c_c_continuousAt hx)

end Body

/-! ### Theorem C -/

/-- Points `X_n` of `C` with `||X_n|⁻¹X_n - p| ≤ s_n` have a subsequence tending to a point `Q`
of `C` with `||Q|⁻¹Q - p| ≤ lim s_n` (`C` is compact, and `X ↦ |X|⁻¹X` continuous on it). -/
lemma m46c_subseq (hK : IsSymmetricConvexDomain K) {X : ℕ → Fin 2 → ℝ}
    (hX : ∀ n, X n ∈ frontier K) {p : Fin 2 → ℝ} {s : ℕ → ℝ} {s₀ : ℝ}
    (hs : Tendsto s atTop (𝓝 s₀)) (hXs : ∀ n, ‖m46c_dir (X n) - p‖ ≤ s n) :
    ∃ (Q : Fin 2 → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (fun n ↦ X (φ n)) atTop (𝓝 Q) ∧
      Q ∈ frontier K ∧ ‖m46c_dir Q - p‖ ≤ s₀ := by
  obtain ⟨Q, -, φ, hφ, tX⟩ := hK.2.1.tendsto_subseq fun n ↦ mm_mem_of_frontier hK (hX n)
  have hQ : Q ∈ frontier K :=
    isClosed_frontier.mem_of_tendsto tX (Eventually.of_forall fun n ↦ hX _)
  have td : Tendsto (fun n ↦ ‖m46c_dir (X (φ n)) - p‖) atTop (𝓝 ‖m46c_dir Q - p‖) :=
    (((m46c_dir_continuousAt (mm_ne_zero_of_frontier hK hQ)).tendsto.comp tX).sub_const p).norm
  exact ⟨Q, φ, hφ, tX, hQ, le_of_tendsto_of_tendsto td (hs.comp hφ.tendsto_atTop)
    (Eventually.of_forall fun n ↦ hXs _)⟩

/-- **Theorem C, first assertion** (p. 336): if no critical lattice of `K` passes through `P ∈ C`,
*a positive number `σ` exists such that no critical lattice of `K` passes through a point of the
set `S` consisting of all points `X` on `C` for which `||X|⁻¹X - |P|⁻¹P| ≤ σ`*. Otherwise critical
lattices `Λ_r` would contain points `P_r ∈ C` tending to `P` (a subsequence tends to a point of
`C` on the ray of `P`, i.e. to `P`), and Theorem B would give a critical lattice through `P`. -/
lemma m46c_step1 (hK : IsSymmetricConvexDomain K) {P : Fin 2 → ℝ} (hP : P ∈ frontier K)
    (hno : ∀ Λ, IsCritical K Λ → P ∉ Λ) :
    ∃ σ > 0, ∀ X ∈ frontier K, ‖m46c_dir X - m46c_dir P‖ ≤ σ →
      ∀ Λ, IsCritical K Λ → X ∉ Λ := by
  by_contra hcon
  push Not at hcon
  have := fun n : ℕ ↦ hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose X hXF hXd Λ hΛ hXΛ using this
  obtain ⟨Q, φ, hφ, tX, hQ, hQd⟩ :=
    m46c_subseq hK hXF tendsto_one_div_add_atTop_nhds_zero_nat hXd
  have hQP : Q = P := m46c_eq_of_dir hK hQ hP (sub_eq_zero.1 (norm_le_zero_iff.1 hQd))
  subst hQP
  obtain ⟨-, L, hL, hQL⟩ := theoremB hK (fun n ↦ (hΛ (φ n)).1) (fun n ↦ (hΛ (φ n)).2.1)
    (tendsto_const_nhds.congr fun n ↦ (hΛ (φ n)).2.2.symm) (fun n ↦ hXΛ (φ n))
    (fun n ↦ hXF (φ n)) tX
  exact hno L hL hQL

/-- **Theorem C, second assertion** (p. 336): *there is a positive number `δ` such that
`d(Λ) ≥ (1 + δ)ⁿ Δ(K)` for every `K`-admissible lattice which contains a point of `S`*
(`n = 2`). Otherwise admissible lattices `Λ_r` with `d(Λ_r) → Δ(K)` would contain points of `S`;
`S` being bounded and closed, a subsequence of these tends to a point `P*` of `S`, and Theorem B
gives a critical lattice through `P*`, contrary to the first assertion. -/
lemma m46c_step2 (hK : IsSymmetricConvexDomain K) {p : Fin 2 → ℝ} {σ : ℝ}
    (hS : ∀ X ∈ frontier K, ‖m46c_dir X - p‖ ≤ σ → ∀ Λ, IsCritical K Λ → X ∉ Λ) :
    ∃ δ > 0, ∀ Λ, IsLattice Λ → IsAdmissible K Λ → ∀ X ∈ Λ, X ∈ frontier K →
      ‖m46c_dir X - p‖ ≤ σ → (1 + δ) ^ 2 * minimalDeterminant K ≤ det Λ := by
  by_contra hcon
  push Not at hcon
  have := fun n : ℕ ↦ hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose Λ hlat hadm X hXΛ hXF hXd hdet using this
  have hle : ∀ n, minimalDeterminant K ≤ det (Λ n) :=
    fun n ↦ mm_minimalDeterminant_le (hlat n) (hadm n)
  have tup : Tendsto (fun n : ℕ ↦ (1 + 1 / ((n : ℝ) + 1)) ^ 2 * minimalDeterminant K) atTop
      (𝓝 (minimalDeterminant K)) := by
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat.const_add 1).pow 2).mul_const
      (minimalDeterminant K)
    simpa using this
  have tdet : Tendsto (fun n ↦ det (Λ n)) atTop (𝓝 (minimalDeterminant K)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tup hle (fun n ↦ (hdet n).le)
  obtain ⟨Q, φ, hφ, tX, hQ, hQd⟩ := m46c_subseq hK hXF (s := fun _ ↦ σ) tendsto_const_nhds hXd
  obtain ⟨-, L, hL, hQL⟩ := theoremB hK (fun n ↦ hlat (φ n)) (fun n ↦ hadm (φ n))
    (tdet.comp hφ.tendsto_atTop) (fun n ↦ hXΛ (φ n)) (fun n ↦ hXF (φ n)) tX
  exact hS Q hQ hQd L hL hQL

/-- **Mahler 1946, Part I, Theorem 8** (quoted on p. 332), in the plane, for any set `H` with `O`
an inner point that has an admissible lattice: *`H` possesses at least one critical lattice*
(from Mahler's compactness theorem, `PlaneLattice.exists_admissible_covolume_le`). -/
theorem m46c_theorem8 {H : Set (Fin 2 → ℝ)} (h0 : (0 : Fin 2 → ℝ) ∈ interior H)
    {L₀ : Submodule ℤ (Fin 2 → ℝ)} (hL₀ : IsLattice L₀) (hadm : IsAdmissible H L₀) :
    ∃ Λ, IsCritical H Λ := by
  obtain ⟨L, hLd, hLs, hLadm, hLmin⟩ := PlaneLattice.exists_admissible_covolume_le
    isOpen_interior h0 hL₀.1 hL₀.2 hadm
  refine ⟨L, ⟨hLd, hLs⟩, hLadm, ?_⟩
  unfold minimalDeterminant
  refine Eq.symm (IsLeast.csInf_eq ⟨⟨L, ⟨hLd, hLs⟩, hLadm, rfl⟩, ?_⟩)
  rintro d ⟨L', ⟨hL'd, hL's⟩, hL'adm, rfl⟩
  exact hLmin L' hL'd hL's hL'adm

/-- **Mahler, paper A, Lemma 10** (p. 104; "proof of Theorem C" of the 1946 paper), for a symmetric
convex domain `K`: *let `P` be a point on `C` such that no critical lattice of `K` contains `P`.
Then there exists a star domain `H` contained in `K`, but not containing the two points `±P`, for
which `Δ(H) = Δ(K)`.* (Paper A also assumes `K` reducible, which is not used.) `H` is a compact
star body, i.e. a star domain in the sense of paper A.

Mahler's proof of Theorem C (pp. 336–338): `σ` from the first assertion (`m46c_step1`), `δ` from
the second (`m46c_step2`), and `H : G(X) ≤ 1` with `G` the corrected distance function `m46c_G`
(see the module docstring for the error), so `F ≤ G ≤ (1 + δ) F` and `H < K`. If `Δ(H) < Δ(K)`,
a critical lattice `Λ` of `H` (Theorem 8) is not `K`-admissible, and the set `Σ` of its points
`Q_s ≠ O` inside `K` is finite and not empty. Each satisfies `F(Q_s) < 1 ≤ G(Q_s)`; with
`min F(Q_s) = 1/λ`, `1 < λ ≤ 1 + δ`, the lattice `Λ* = λΛ` is `K`-admissible and one of the points
`±λQ_s` lies in `S`, so `λ² Δ(H) = d(Λ*) ≥ (1 + δ)² Δ(K)`, whence `Δ(H) ≥ Δ(K)`: a
contradiction. -/
theorem lemma10 (hK : IsSymmetricConvexDomain K) {P : Fin 2 → ℝ} (hP : P ∈ frontier K)
    (hno : ∀ Λ, IsCritical K Λ → P ∉ Λ) :
    ∃ H, m46c_IsStarBody H ∧ IsCompact H ∧ H ⊆ K ∧ P ∉ H ∧ -P ∉ H ∧
      minimalDeterminant H = minimalDeterminant K := by
  set p := m46c_dir P with hp
  obtain ⟨σ, hσ, hS⟩ := m46c_step1 hK hP hno
  obtain ⟨δ, hδ, hgap⟩ := m46c_step2 hK hS
  set G := m46c_G K p σ δ with hG
  have hGd : m46c_IsDistanceFunction G := m46c_G_isDistanceFunction hK hσ hδ.le
  set H := {x | G x ≤ 1} with hH
  have hstar : m46c_IsStarBody H := ⟨G, hGd, rfl⟩
  have hsub : H ⊆ K := fun x (hx : G x ≤ 1) ↦ (m46c_gauge_le_one hK).1
    ((le_mul_of_one_le_right (gauge_nonneg x) (m46c_c_ge hσ hδ.le x)).trans hx)
  have hcpt : IsCompact H :=
    hK.2.1.of_isClosed_subset (isClosed_le hGd.2.2 continuous_const) hsub
  have hGP : G P = 1 + δ := by
    simp only [hG, m46c_G, (m46c_gauge_eq_one hK).2 hP, one_mul, hp, m46c_c_self,
      max_eq_right hσ.le, div_mul_cancel₀ _ hσ.ne']
  have hPH : P ∉ H := fun h ↦ by
    have : G P ≤ 1 := h
    linarith
  have hnPH : -P ∉ H := fun h ↦ hPH (by simpa using m46c_starBody_neg hstar h)
  refine ⟨H, hstar, hcpt, hsub, hPH, hnPH, le_antisymm (ml3_minDet_mono hK hsub) ?_⟩
  -- `Δ(H) < Δ(K)` is impossible
  by_contra hlt
  push Not at hlt
  obtain ⟨ΛK, hΛK⟩ := irr_exists_critical hK
  obtain ⟨Λ, hΛ⟩ := m46c_theorem8 (m46c_starBody_zero hstar) hΛK.1
    (fun x hx hxH ↦ hΛK.2.1 x hx (interior_mono hsub hxH))
  have hnadm : ¬ IsAdmissible K Λ := fun h ↦ by
    have := mm_minimalDeterminant_le hΛ.1 h
    rw [hΛ.2.2] at this
    linarith
  -- the set `Σ` of the points `Q_s ≠ O` of `Λ` inside `K`
  set Sig := {Q | Q ∈ Λ ∧ Q ∈ interior K ∧ Q ≠ 0} with hSig
  have hne : Sig.Nonempty := by
    unfold IsAdmissible at hnadm
    push Not at hnadm
    obtain ⟨Q, hQΛ, hQK, hQ0⟩ := hnadm
    exact ⟨Q, hQΛ, hQK, hQ0⟩
  have hfin : Sig.Finite := by
    have hdisc : IsDiscrete (Λ : Set (Fin 2 → ℝ)) := isDiscrete_iff_discreteTopology.mpr hΛ.1.1
    have hcl : IsClosed (Λ : Set (Fin 2 → ℝ)) :=
      AddSubgroup.isClosed_of_isDiscrete Λ.toAddSubgroup hdisc
    exact (Metric.finite_isBounded_inter_isClosed hdisc hK.2.1.isBounded hcl).subset
      fun Q hQ ↦ ⟨interior_subset hQ.2.1, hQ.1⟩
  obtain ⟨Q₀, ⟨hQ₀Λ, hQ₀K, hQ₀0⟩, hQ₀min⟩ := Set.exists_min_image Sig (gauge K) hfin hne
  set F₀ := gauge K Q₀ with hF₀
  have hF0 : 0 < F₀ := m46c_gauge_pos hK hQ₀0
  have hF1 : F₀ < 1 := (m46c_gauge_lt_one hK).2 hQ₀K
  have hGQ : 1 ≤ G Q₀ := by
    by_contra h
    push Not at h
    have : Q₀ ∈ interior H := interior_maximal (t := {x | G x < 1})
      (fun x (hx : G x < 1) ↦ show G x ≤ 1 from hx.le) (isOpen_lt hGd.2.2 continuous_const) h
    exact hQ₀0 (hΛ.2.1 Q₀ hQ₀Λ this)
  -- `min F(Q_s) = 1/λ`, `1 < λ ≤ 1 + δ`
  set lam := F₀⁻¹ with hlam
  have hlam1 : 1 < lam := (one_lt_inv₀ hF0).2 hF1
  have hcQ : lam ≤ m46c_c p σ δ Q₀ := by
    rw [hlam, inv_le_iff_one_le_mul₀ hF0, mul_comm]
    exact hGQ
  have hlamδ : lam ≤ 1 + δ := hcQ.trans (m46c_c_le hσ hδ.le Q₀)
  have hωQ : m46c_ω p Q₀ < σ := m46c_ω_lt (hlam1.trans_le hcQ)
  -- the lattice `Λ* = λΛ` is `K`-admissible
  obtain ⟨u, v, hbas, huv⟩ := mm_exists_basis hΛ.1
  have hcrl : cross (lam • u) (lam • v) = lam ^ 2 * cross u v := by
    simp only [cross, Pi.smul_apply, smul_eq_mul]; ring
  have huv' : cross (lam • u) (lam • v) ≠ 0 := by
    rw [hcrl]; exact mul_ne_zero (by positivity) huv
  have hadm' : IsAdmissible K (Submodule.span ℤ {lam • u, lam • v}) := by
    intro y hy hyK
    obtain ⟨m, k, rfl⟩ := mm_mem_span_pair.1 hy
    have hYΛ : (m : ℝ) • u + (k : ℝ) • v ∈ Λ := by
      rw [← hbas.2]; exact mm_mem_span_pair.2 ⟨m, k, rfl⟩
    have hy' : (m : ℝ) • (lam • u) + (k : ℝ) • (lam • v) =
        lam • ((m : ℝ) • u + (k : ℝ) • v) := by
      rw [smul_add, smul_comm lam (m : ℝ) u, smul_comm lam (k : ℝ) v]
    rw [hy'] at hyK ⊢
    have h1 : lam * gauge K ((m : ℝ) • u + (k : ℝ) • v) < 1 := by
      have := (m46c_gauge_lt_one hK).2 hyK
      rwa [m46c_gauge_smul hK, abs_of_pos (by linarith)] at this
    by_contra hY0
    have hY0' : (m : ℝ) • u + (k : ℝ) • v ≠ 0 := fun h ↦ hY0 (by rw [h, smul_zero])
    have hYlt : gauge K ((m : ℝ) • u + (k : ℝ) • v) < F₀ := by
      rw [hlam, inv_mul_lt_iff₀ hF0, mul_one] at h1
      exact h1
    have hYK : (m : ℝ) • u + (k : ℝ) • v ∈ interior K :=
      (m46c_gauge_lt_one hK).1 (hYlt.trans hF1)
    have := hQ₀min _ ⟨hYΛ, hYK, hY0'⟩
    linarith
  -- one of the points `±λQ₀` of `Λ*` lies in `S`
  have hQ₀mem : lam • Q₀ ∈ Submodule.span ℤ {lam • u, lam • v} := by
    have := hQ₀Λ
    rw [← hbas.2] at this
    obtain ⟨m, k, hmk⟩ := mm_mem_span_pair.1 this
    exact mm_mem_span_pair.2 ⟨m, k, by
      rw [← hmk, smul_add, smul_comm lam (m : ℝ) u, smul_comm lam (k : ℝ) v]⟩
  have hlQF : lam • Q₀ ∈ frontier K := by
    rw [← m46c_gauge_eq_one hK, m46c_gauge_smul hK, abs_of_pos (by linarith), hlam,
      inv_mul_cancel₀ hF0.ne']
  have hdet' : det (Submodule.span ℤ {lam • u, lam • v}) = lam ^ 2 * minimalDeterminant H := by
    rw [mm_det_span huv', hcrl, abs_mul, abs_of_nonneg (sq_nonneg _), ← mm_det_eq hΛ.1 hbas,
      hΛ.2.2]
  have hgap' : (1 + δ) ^ 2 * minimalDeterminant K ≤
      det (Submodule.span ℤ {lam • u, lam • v}) := by
    rcases min_lt_iff.1 hωQ with h | h
    · refine hgap _ (mm_isLattice_span huv') hadm' _ hQ₀mem hlQF ?_
      rw [m46c_dir_smul (by linarith)]
      exact h.le
    · refine hgap _ (mm_isLattice_span huv') hadm' _ (Submodule.neg_mem _ hQ₀mem)
        (mm_neg_mem_frontier hK hlQF) ?_
      rw [m46c_dir_neg, m46c_dir_smul (by linarith),
        show -m46c_dir Q₀ - p = -(m46c_dir Q₀ + p) by abel, norm_neg]
      exact h.le
  -- `Δ(H) = λ⁻² d(Λ*) ≥ ((1 + δ)/λ)² Δ(K) ≥ Δ(K)`
  have hΔK := irr_minimalDeterminant_pos hK
  have h1 : lam ^ 2 * minimalDeterminant H < lam ^ 2 * minimalDeterminant K := by
    have : 0 < lam ^ 2 := by positivity
    exact mul_lt_mul_of_pos_left hlt this
  have h2 : lam ^ 2 * minimalDeterminant K ≤ (1 + δ) ^ 2 * minimalDeterminant K := by
    have : lam ^ 2 ≤ (1 + δ) ^ 2 := pow_le_pow_left₀ (by linarith) hlamδ 2
    exact mul_le_mul_of_nonneg_right this hΔK.le
  linarith

/-- **Mahler 1946, Theorem C** (p. 336), for a symmetric convex domain `K` in the plane: *let
`K : F(X) ≤ 1` be an irreducible star body of the finite type, and let `P` be any finite point on
the boundary `C` of `K`. Then there exists at least one critical lattice of `K` containing `P`.*
Irreducible in the sense of Definition A (`m46c_IsReducible`: against all star bodies). Mahler's
proof: if no critical lattice contains `P`, the star body `H` of `lemma10` has `H ≺ K`. -/
theorem theoremC (hK : IsSymmetricConvexDomain K) (hirr : ¬ m46c_IsReducible K)
    {P : Fin 2 → ℝ} (hP : P ∈ frontier K) : ∃ Λ, IsCritical K Λ ∧ P ∈ Λ := by
  by_contra h
  push Not at h
  obtain ⟨H, hH, -, hsub, hPH, -, hΔ⟩ := lemma10 hK hP h
  exact hirr ⟨H, hH, hsub, fun hHK ↦ hPH (hHK ▸ mm_mem_of_frontier hK hP), hΔ⟩

/-! ### Class B of paper A's Lemma 13 -/

/-- **The line `L'`** (paper A, proof of Lemma 13, class B: "draw a line `L'` through `P` which has
no point in common with `H'`"). Gap in paper A, filled: if `e` is an extreme point of `K` and `A`
a compact subset of `K` not containing `e`, a line `a · x = a · e` through `e` has `A` strictly on
the side of `O`. Take a support line `a₀ · x = 1` at `e`; if it meets `K` in a segment `[e, b]`,
tilt it about `e` towards `b`: the lines `((1 + s(w · e)) a₀ - s w) · x = 1`, `w = b - e`, `s → 0⁺`.
Were each of them met by a point `x_s` of `A`, a limit point `z ∈ A` of the `x_s` would satisfy
`a₀ · z = 1` and `w · z ≤ w · e`, so `z = e` (`e` is an endpoint of `[e, b]`). -/
lemma m46c_line (hK : IsSymmetricConvexDomain K) {e : Fin 2 → ℝ} (he : e ∈ K.extremePoints ℝ)
    {A : Set (Fin 2 → ℝ)} (hA : IsCompact A) (hAK : A ⊆ K) (heA : e ∉ A) :
    ∃ a : Fin 2 → ℝ, ∀ x ∈ A, a ⬝ᵥ x < a ⬝ᵥ e := by
  have heF := ml3_extreme_frontier hK he
  obtain ⟨f, hf1, hf2, -⟩ := mm_support hK heF
  obtain ⟨a₀, ha₀⟩ := ml3_dual_vec f
  have ha₀e : a₀ ⬝ᵥ e = 1 := by rw [ha₀, hf1]
  have ha₀K : ∀ x ∈ K, a₀ ⬝ᵥ x ≤ 1 := fun x hx ↦ by rw [ha₀]; exact hf2 x hx
  have ha₀0 : a₀ ≠ 0 := by rintro rfl; simp at ha₀e
  -- the direction `w` of the tilt (`w = 0` if the support line meets `K` only at `e`)
  obtain ⟨w, hw⟩ : ∃ w : Fin 2 → ℝ, ∀ x ∈ K, a₀ ⬝ᵥ x = 1 → w ⬝ᵥ x ≤ w ⬝ᵥ e → x = e := by
    by_cases hface : ∃ b ∈ K, a₀ ⬝ᵥ b = 1 ∧ b ≠ e
    · obtain ⟨b, hbK, hb1, hbe⟩ := hface
      refine ⟨b - e, fun x hxK hx1 hxw ↦ ?_⟩
      have hw0 : b - e ≠ 0 := sub_ne_zero.2 hbe
      have haw : a₀ ⬝ᵥ (b - e) = 0 := by rw [dotProduct_sub, hb1, ha₀e, sub_self]
      have hcr : cross (b - e) (x - e) = 0 :=
        ml3_cross_eq_zero_of_dot ha₀0 haw (by rw [dotProduct_sub, hx1, ha₀e, sub_self])
      obtain ⟨τ, hτ⟩ := ml3_parallel hcr hw0
      have hx : x = e + τ • (b - e) := by rw [← hτ]; abel
      have hww := irr_dot_self_pos hw0
      have hτ0 : τ ≤ 0 := by
        have : (b - e) ⬝ᵥ x = (b - e) ⬝ᵥ e + τ * ((b - e) ⬝ᵥ (b - e)) := by
          rw [hx, dotProduct_add, dotProduct_smul, smul_eq_mul]
        nlinarith
      rcases hτ0.lt_or_eq with hlt | heq
      · have h1τ : 1 - τ ≠ 0 := by linarith
        have hseg : e ∈ openSegment ℝ x b := by
          refine ⟨1 / (1 - τ), -τ / (1 - τ), by apply div_pos <;> linarith,
            by apply div_pos <;> linarith, by rw [← add_div, div_eq_one_iff_eq h1τ]; ring, ?_⟩
          rw [hx]
          ext i
          simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          field_simp
          ring
        exact he.2 hxK hbK hseg
      · rw [hx, heq, zero_smul, add_zero]
    · push Not at hface
      exact ⟨0, fun x hxK hx1 _ ↦ hface x hxK hx1⟩
  by_contra hcon
  push Not at hcon
  set s : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hs
  have hs0 : ∀ n, 0 < s n := fun n ↦ by positivity
  have hstend : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose x hxA hx using fun n ↦ hcon ((1 + s n * (w ⬝ᵥ e)) • a₀ - s n • w)
  have hxK : ∀ n, x n ∈ K := fun n ↦ hAK (hxA n)
  have hineq : ∀ n, 1 ≤ a₀ ⬝ᵥ x n + s n * ((w ⬝ᵥ e) * (a₀ ⬝ᵥ x n) - w ⬝ᵥ x n) := by
    intro n
    have := hx n
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, ha₀e] at this
    linarith
  have hpos : ∀ n, 0 ≤ (w ⬝ᵥ e) * (a₀ ⬝ᵥ x n) - w ⬝ᵥ x n := by
    intro n
    have h1 := hineq n
    have h2 := ha₀K _ (hxK n)
    have h3 := hs0 n
    by_contra hneg
    push Not at hneg
    nlinarith
  obtain ⟨z, hzA, φ, hφ, tz⟩ := hA.tendsto_subseq hxA
  have tdot : ∀ c : Fin 2 → ℝ, Tendsto (fun n ↦ c ⬝ᵥ x (φ n)) atTop (𝓝 (c ⬝ᵥ z)) :=
    fun c ↦ ((irr_continuous_dot c).tendsto _).comp tz
  have tsφ : Tendsto (fun n ↦ s (φ n)) atTop (𝓝 0) := hstend.comp hφ.tendsto_atTop
  have tq : Tendsto (fun n ↦ (w ⬝ᵥ e) * (a₀ ⬝ᵥ x (φ n)) - w ⬝ᵥ x (φ n)) atTop
      (𝓝 ((w ⬝ᵥ e) * (a₀ ⬝ᵥ z) - w ⬝ᵥ z)) :=
    ((tdot a₀).const_mul _).sub (tdot w)
  have hz1 : a₀ ⬝ᵥ z = 1 := by
    refine le_antisymm (ha₀K z (hAK hzA)) ?_
    have tl := (tdot a₀).add (tsφ.mul tq)
    rw [zero_mul, add_zero] at tl
    exact ge_of_tendsto tl (Eventually.of_forall fun n ↦ hineq (φ n))
  have hzw : w ⬝ᵥ z ≤ w ⬝ᵥ e := by
    have := ge_of_tendsto tq (Eventually.of_forall fun n ↦ hpos (φ n))
    rw [hz1, mul_one] at this
    linarith
  exact heA (hw z (hAK hzA) hz1 hzw ▸ hzA)

/-- **Mahler, paper A, Lemma 13, class B** (first case of the proof, pp. 104–105), for convex
subdomains: *every extreme point `e` of an irreducible convex domain `K` lies on a critical lattice
of `K`.* (Paper A's class B: the points of `C` that are not inner points of a segment in `C`, i.e.
the extreme points of `K`.)

Mahler's proof: otherwise, *by Lemma 10, there exists a star domain `H'` contained in `K`, but not
containing the two points `±P`, such that `Δ(H') = Δ(K)`. Draw a line `L'` through `P` which has no
point in common with `H'` [`m46c_line`]. Then a line `L` parallel to `L'`, separating `L'` from
`O`, can be chosen which also has no points in common with `H'`; denote by `-L` the line
symmetrical to `L` in `O`, and by `H` the part of `K` between `L` and `-L`. Then `H` is a convex
domain containing `H'`, and is itself a proper subset of `K`. Evidently
`Δ(H') ≤ Δ(H) ≤ Δ(K)`, whence `Δ(H) = Δ(K)`*, contradicting the irreducibility of `K`. -/
theorem m46c_classB (hK : MahlerIrreducible.IsIrreducible K) {e : Fin 2 → ℝ}
    (he : e ∈ K.extremePoints ℝ) : ∃ Λ, IsCritical K Λ ∧ e ∈ Λ := by
  have hKd := hK.1
  have heF := ml3_extreme_frontier hKd he
  by_contra hno
  push Not at hno
  -- Lemma 10: the star domain `H'`
  obtain ⟨H', hstar, hcpt, hsub, heH, -, hΔ⟩ := lemma10 hKd heF hno
  -- the line `L' : a · x = a · e`
  obtain ⟨a, ha⟩ := m46c_line hKd he hcpt hsub heH
  have h0 : (0 : Fin 2 → ℝ) ∈ H' := interior_subset (m46c_starBody_zero hstar)
  obtain ⟨m, hmH, hmax⟩ := hcpt.exists_isMaxOn ⟨0, h0⟩ (irr_continuous_dot a).continuousOn
  have hM : a ⬝ᵥ m < a ⬝ᵥ e := ha m hmH
  have hM0 : 0 ≤ a ⬝ᵥ m := by simpa using hmax h0
  -- the line `L : a · x = c` between `H'` and `L'`, and the part `H` of `K` between `±L`
  set c := (a ⬝ᵥ m + a ⬝ᵥ e) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  set H := K ∩ {x | |a ⬝ᵥ x| ≤ c} with hH
  have hHd : IsSymmetricConvexDomain H := irr_cut hKd a hc0
  have hHK : H ⊆ K := inter_subset_left
  have hne : H ≠ K := by
    intro h
    have heH' : e ∈ H := h ▸ he.1
    have h1 : |a ⬝ᵥ e| ≤ c := heH'.2
    have := le_abs_self (a ⬝ᵥ e)
    linarith
  have hH'H : H' ⊆ H := by
    intro x hx
    refine ⟨hsub hx, ?_⟩
    have h1 : a ⬝ᵥ x ≤ a ⬝ᵥ m := hmax hx
    have h2 : a ⬝ᵥ (-x) ≤ a ⬝ᵥ m := hmax (m46c_starBody_neg hstar hx)
    rw [dotProduct_neg] at h2
    change |a ⬝ᵥ x| ≤ c
    rw [abs_le]
    constructor <;> linarith
  -- `Δ(H') ≤ Δ(H) < Δ(K) = Δ(H')`
  have hlt := hK.2 H hHd hHK hne
  have hle := ml3_minDet_mono hHd hH'H
  linarith

end Mahler1946

end External
