module

public import External.Mahler1947
public import External.Mahler1946.TheoremC
public import External.Mahler1946.TheoremE

/-!
# Mahler 1947, Lemma 3

Cited in the remark after Definition 2.3.5 of Hales–Vajjha, *Packings of Smoothed Polygons*, from
K. Mahler, *On the minimum determinant and the circumscribed hexagons of a convex domain*,
Proc. Kon. Ned. Akad. Wet. 50 (1947), 692–703, Lemma 3: *the convex domain `K` is irreducible if
and only if every boundary point of `K` belongs to a critical lattice of `K`*
(`mahler_irreducible_iff`). From it we derive the weak form that the proof of Lemma 2.2.5 uses
(`mahler_irreducible`: every tac-line of an irreducible `K` passes through a point of a critical
lattice, one of the six points of a configuration of Mahler's Lemma 2).

This module assembles the proof from `External.MahlerIrreducible` (the definitions and paper A's
own lemmas) and `External.Mahler1946.TheoremC`, `External.Mahler1946.TheoremE` (the theorems of
the 1946 paper that paper A quotes), which both import `External.MahlerIrreducible`; hence a
module of its own, named after the lemma it proves and placed under the file it completes.

## Sources

* **Mahler 1947** states Lemma 3 without proof; its footnote 3 reads "See Lemmas 8 and 12 of
  paper A".
* **Paper A**: K. Mahler, *On irreducible convex domains*, Proc. Kon. Ned. Akad. Wet. 50 (1947),
  98–107 (not among the sources supplied with the book; we read a scan from Mahler's collected
  works, CARMA archive, item 094). It proves Lemmas 1, 2, 5, 6, 7 and 13 itself (Lemma 3 is
  Minkowski's theorem, `External.minkowski_mahler`; Lemmas 4 and 9 are immediate consequences),
  and quotes Lemmas 8, 10, 11 and 12 from the 1946 paper.
* **Mahler 1946**: K. Mahler, *Lattice points in n-dimensional star bodies II. Reducibility
  theorems I*, Proc. Kon. Ned. Akad. Wet. 49 (1946), 331–343 (scan: CARMA item 088; the book's
  bibliography entry `mahler1946lattice` is this paper). Paper A's Lemma 8 is its Theorem C,
  Lemma 10 the proof of Theorem C, Lemma 11 a special case of Theorem B, and Lemma 12 its
  Theorems D and E. Its proofs quote two theorems of Part I (Proc. Roy. Soc. A): the selection
  theorem (Theorem 2) and the existence of critical lattices (Theorem 8).

## What follows which source

The proof follows Mahler throughout: Mahler 1947 → paper A → Mahler 1946.

* **"Only if"** (`MahlerIrreducible.ml3_onlyIf`): the proof of paper A's Lemma 13 from "`Π*` is
  not the null set" on (`Π`: the points of `C` on critical lattices; `Π*`: the others), argued by
  contradiction from a point of `Π*`. The points of `C` are of class B (extreme points of `K`) or
  of class A (inner points of a segment in `C`).
  - Class B (`Mahler1946.m46c_classB`): paper A's Lemma 10 (`Mahler1946.lemma10`, the proof of
    Theorem C of Mahler 1946: a cone around `P` meeting no critical lattice, a determinant gap for
    the admissible lattices through the cone, and the star body `G(X) ≤ 1`) gives a star domain
    `H' ⊆ K` missing `±P` with `Δ(H') = Δ(K)`; the part of `K` between a line `L` separating `P`
    from `H'` and its mirror image `-L` is a convex `H ⊊ K` with `Δ(H) = Δ(K)`.
  - Class A (`MahlerIrreducible.ml5_classA`): the largest segment `Γ₁` around the point whose ends
    lie in `Π` and whose inner points lie in `Π*` (it exists since `Π` is closed, paper A's
    Lemma 11, `Mahler1946.lemma11`, from Theorem B of Mahler 1946 (`Mahler1946.theoremB`), and
    since the ends of the boundary segment are of class B); then paper A's Lemmas 5–7 and Mahler's
    quadratic.
  - Parallelograms: Mahler sets them aside by Lemma 1 (a reducible domain is not a
    parallelogram); since we argue from an irreducible `K`, we use instead Mahler's example in §3
    of paper A (`Π = C` for a parallelogram, `MahlerIrreducible.ml5_par_pi`).
  Mahler 1947 cites Lemma 8 (an irreducible star domain has `Π = C`: Theorem C of Mahler 1946,
  formalized as `Mahler1946.theoremC`). For irreducibility against convex subdomains, the notion
  of `MahlerIrreducible.IsIrreducible`, it is the proof of Lemma 13 that gives `Π = C`, with
  Lemma 10 in place of Lemma 8.
* **"If"** (`Mahler1946.m46e_lemma12`): paper A's Lemma 12, from Theorem D of Mahler 1946
  (`Mahler1946.theoremD`: a dense set of points of `C` on free lattices makes `K` irreducible) and
  Theorem E (`Mahler1946.theoremE`: a critical lattice with just six points on `C` is free), with
  the Corollary to Lemma 5 and Lemma 1 of paper A.
* **The weak form** (`mahler_irreducible`): the tac-line meets `K` in a boundary point `u`, which
  lies on a critical lattice by the "only if" half; then (paper A, Lemmas 3 and 4,
  `MahlerIrreducible.ml5_conf_of_pi`) there are points `P₂, P₂ - u` on `C` with
  `det(u, P₂) = Δ(K)`, and the lattice of basis `u, P₂` is critical (Lemma 3, converse part). This
  replaces our earlier proof by shaving `K` along the tac-line, which was not Mahler's.

## Readings

* Everything is in the plane, and the domains of Lemma 3 are symmetric convex domains
  (`MinkowskiMahler.IsSymmetricConvexDomain`). Mahler 1946 states Theorems B–D for star bodies
  `F(X) ≤ 1` in `n` dimensions (Theorem E for convex star domains in the plane); we prove them for
  symmetric convex domains `K`, whose distance function is the gauge `gauge K`
  (`Mahler1946.m46c_isStarBody`). The auxiliary body `G(X) ≤ 1` of Theorem C is a star body that
  is not convex in general; it stays a star body (`Mahler1946.m46c_IsStarBody`), and paper A's cut
  by a line replaces it by a convex domain.
* Mahler's Euclidean length `|X|` is replaced by the norm of `Fin 2 → ℝ` (the sup norm) in the
  direction `|X|⁻¹X` of Theorem C and in the neighbourhoods `|X - Q| ≤ ε` of §4 of Mahler 1946:
  only the continuity and homogeneity of `X ↦ |X|⁻¹X` and the neighbourhoods are used.
* Irreducibility (`MahlerIrreducible.IsIrreducible`) is tested against symmetric convex
  subdomains; paper A and Mahler 1946 (Definition A, `Mahler1946.m46c_IsReducible`) test it
  against all star domains. Paper A's Lemma 13 (a reducible convex domain has a convex proper
  subdomain with the same `Δ`) is the bridge: for convex `K` the two notions agree.
* Definition B of Mahler 1946 (free lattices, `Mahler1946.IsFree`) is asked for some basis of the
  lattice instead of a reduced one (any fixed basis gives the same notion).

## Errors and gaps of the sources, repaired

Mahler 1946:
* *Error* (proof of Theorem C, p. 337): `G(X) = F(X){1 + (δ/σ) max(0, σ - ||X|⁻¹X - |P|⁻¹P|)}` is
  not even (`G(P) = (1 + δ)F(P)` but `G(-P) = F(P)`), so `H : G ≤ 1` is not a star body and
  contains `-P`, whereas paper A's Lemma 10 asserts that `H` omits `±P`
  (`Mahler1946.m46c_mahlerG_not_distanceFunction`). Repaired by measuring the distance from
  `|X|⁻¹X` to the nearer of the two directions `±|P|⁻¹P` (`Mahler1946.m46c_G`); in the last step
  one of the points `±λQ_s` (instead of `λQ_s`) lies in the cone.
* *Gap* (proof of Theorem E): "since only four points of `Λ` lie on the boundary of `K*`, there
  exists a neighbouring lattice `Λ*` which is `K*`-admissible and of determinant `d(Λ*) < d(Λ)`"
  is asserted without argument ((A) gives such a lattice, but not a neighbouring one). Filled with
  the deformation by which (A) is proved (`Mahler1946.m46e_turn`).
* *Gap* (§4): "the points `P_k*` are then the only points of `Λ*` which lie on, or near to, the
  boundary `C` of `K`, if `ε` sufficiently small" is stated without proof; proved
  (`Mahler1946.m46e_near`).
* Details left to the reader, written out: in Theorem D the passage from `|Y_g* - Y_g| < ε` to
  `|P* - P| ≤ ε/2`; in Theorem E a line separating the chosen point from the five others (Mahler
  infers it from "no three of the six points are collinear").

Paper A:
* *Error* (proof of Lemma 1): "`±θP₀` are its only points which are inner points of `K₀`" fails
  for `θ < 1/2` (the multiples `mθP₀`, `2 ≤ |m| < 1/θ`, are inner points too); the argument
  survives, since the points of the lattice inside `K₀` are multiples of `θP₀`, none of them an
  inner point of `H` (`MahlerIrreducible.ml5_lemma1_core`).
* *Slip* (proof of Lemma 5): "an inner point of the segment `P₂P₃` lies on `L**`" should read
  "lies on `C`".
* *Gaps*, filled: in Lemma 1 the reduction to `P₀ = (ξ, 1)`, `0 < ξ < 1`
  (`MahlerIrreducible.ml5_lemma1`); the Corollary to Lemma 5 has no proof
  (`MahlerIrreducible.ml5_lemma5_cor_six`); in Lemma 13, class A, the sign of `{P₁*, P₃*}`
  (Lemma 3 bounds its absolute value; the sign follows by continuity,
  `MahlerIrreducible.ml3_quadratic`), the step "the inner points of `Γ_l` are of class A, so
  `Γ_l` is a segment" (`BoundaryArc.midpoint_mem_frontier_of_forall_not_mem_extremePoints`) and
  "without loss of generality `P'₁` lies on `A₁`" (our naming of the ends by orientation); in
  Lemma 13, class B, the existence of a line `L'` through `P` missing `H'`
  (`Mahler1946.m46c_line`: a support line at the extreme point `P`, tilted slightly; Mahler's
  further condition that `L'` is not a tac-line at `P` is not needed); Lemma 12 does not follow
  from Theorems D and E alone, which need a dense set of points of `C` on critical lattices with
  just six points on `C`: the Corollary to Lemma 5 supplies them when `K` is not a parallelogram,
  and Lemma 1 settles parallelograms (`Mahler1946.m46e_lemma12`).
* Lemma 10 assumes `K` reducible; the hypothesis is not used, and `Mahler1946.lemma10` omits it.

## Departures that remain

* `Δ(K₀) = 1` for the square (proof of Lemma 1), which Mahler takes from Minkowski's theorem on
  linear forms, is derived from Mahler's own example in §2 of paper A (`A(P₁) = 1` for every
  boundary point `P₁`) with Lemmas 2 and 3 (`MahlerIrreducible.ml5_par_minDet`); and Lemma 1 is
  proved in the coordinates of the parallelogram instead of after an affine map to the square.
* Theorems 2 and 8 of Part I, which Mahler 1946 quotes, are proved in the plane by standard
  arguments rather than quoted: Theorem 2 by Lagrange–Gauss reduced bases
  (`Mahler1946.m46c_theorem2`), Theorem 8 from Mahler's compactness theorem in the plane
  (`Mahler1946.m46c_theorem8`, by `PlaneLattice.exists_admissible_covolume_le`).
-/

@[expose] public section

namespace External

namespace MahlerIrreducible

open Set Filter Topology MinkowskiMahler BoundaryArc Mahler1946

variable {K : Set (Fin 2 → ℝ)}

/-- **Mahler, paper A, Lemma 13, for convex subdomains** (the "only if" half of Mahler 1947,
Lemma 3): every boundary point of an irreducible domain lies on a critical lattice. A
parallelogram has `Π = C` (`ml5_par_pi`, Mahler's example in §3 of paper A). Otherwise we follow
the proof of Lemma 13 from "`Π*` is not the null set" on, by contradiction from a point `u ∈ Π*`.
The points of class B (extreme points of `K`) lie on critical lattices (`m46c_classB`: Lemma 10,
from the proof of Theorem C of Mahler 1946, and the cut by a line), so `u` is of class A: an inner
point of the boundary segment `{f = 1} ∩ K`, whose ends are extreme, hence in `Π`. Since `Π` is
closed (Lemma 11, `lemma11`, from Theorem B of Mahler 1946), `u` lies in a largest sub-segment
`Γ₁ = [A, B]` whose ends lie in `Π` and whose inner points do not; this contradicts `ml5_classA`
(Lemmas 5–7 and Mahler's quadratic). -/
lemma ml3_onlyIf (hirr : IsIrreducible K) {u : Fin 2 → ℝ} (hu : u ∈ frontier K) :
    ∃ Λ, IsCritical K Λ ∧ u ∈ Λ := by
  have hK := hirr.1
  by_cases hnpar : IsParallelogram K
  · exact ml5_par_pi hnpar hu
  by_contra hnot
  have huK := mm_mem_of_frontier hK hu
  have hnext : u ∉ K.extremePoints ℝ := fun he ↦ hnot (m46c_classB hirr he)
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
  have hPic : IsClosed Pk := lemma11 hK
  have hpPi : ∀ t, p t ∈ Pk ↔ p t ∈ frontier K ∧ ∃ Λ, IsCritical K Λ ∧ p t ∈ Λ := fun t ↦ Iff.rfl
  have hplo : p tlo ∈ Pk := ⟨hpF _ htloT, m46c_classB hirr (hext _ htloT (Or.inl fun t ht ↦
    csInf_le hTbb ht))⟩
  have hphi : p thi ∈ Pk := ⟨hpF _ hthiT, m46c_classB hirr (hext _ hthiT (Or.inr fun t ht ↦
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
    fun e he ↦ m46c_classB hirr he
  -- Lemma 13, class A, with the ends named so that `det(P₁, P₁') > 0`
  rcases lt_or_gt_of_ne hcAB with hneg | hpos
  · refine ml5_classA hK hnpar hext hBF hAF htBS.2.2 htAS.2.2 (by rw [mm_cross_swap]; linarith)
      (by rw [add_comm]; exact hmid) fun X hX ↦ hgapArc X ?_
    obtain ⟨hXF, a, b, ha, hb, rfl⟩ := hX
    exact ⟨hXF, b, a, hb, ha, add_comm _ _⟩
  · exact ml5_classA hK hnpar hext hAF hBF htAS.2.2 htBS.2.2 hpos hmid hgapArc

end MahlerIrreducible

open Set MahlerIrreducible Mahler1947 MinkowskiMahler

/-- **Mahler (1947), Lemma 3.** The (symmetric) convex domain `K` is irreducible if and only if
every boundary point of `K` belongs to a critical lattice of `K`.

Mahler states the lemma without proof (footnote 3: "See Lemmas 8 and 12 of paper A", Mahler, *On
irreducible convex domains*, Proc. Kon. Ned. Akad. Wet. 50 (1947), 98–107). All domains of the
paper are symmetric in the origin; irreducibility is `MahlerIrreducible.IsIrreducible` (no proper
symmetric convex subdomain has the same minimal determinant).

Proof. "Only if": `ml3_onlyIf`, the proof of paper A's Lemma 13 (with its Lemmas 10 and 11, from
Theorems C and B of Mahler 1946). "If": paper A's Lemma 12 (`Mahler1946.m46e_lemma12`, from
Theorems D and E of Mahler 1946). See the module docstring for the sources, the readings, and the
errors and gaps repaired. -/
theorem mahler_irreducible_iff {K : Set (Fin 2 → ℝ)} (hK : IsSymmetricConvexDomain K) :
    MahlerIrreducible.IsIrreducible K ↔
      ∀ u ∈ frontier K, ∃ Λ, MinkowskiMahler.IsCritical K Λ ∧ u ∈ Λ :=
  ⟨fun h _ hu ↦ ml3_onlyIf h hu, Mahler1946.m46e_lemma12 hK⟩

/-- **Mahler (1947), Lemma 3, weak form of the "only if" half** (a critical-lattice point on each
support line). Let `K` be an irreducible symmetric convex domain and `ℓ` a tac-line of `K`. Then a
critical lattice `Λ` of `K` has a point on `ℓ`: there are points `P₀, P₁, P₂` of `Λ` on the
boundary of `K` with `P₁ = P₀ + P₂` such that `P₀, P₁` is a basis of `Λ` (Mahler's Lemma 2), and
one of the six points `±P₀, ±P₁, ±P₂` lies on `ℓ`.

Derived from Lemma 3 (`mahler_irreducible_iff`). A point `u` of `K` on `ℓ` is a boundary point
of `K`, so by the "only if" half it lies on a critical lattice. By paper A's Lemmas 3 and 4
(`ml5_conf_of_pi`) there are boundary points `W, W - u` with `det(u, W) = Δ(K)`, and the lattice
of basis `u, W` is critical (Mahler 1947's Lemma 2, i.e. paper A's Lemma 3, converse part,
`External.minkowski_mahler`). Take `P₀ = u`, `P₁ = W`, `P₂ = W - u`. -/
theorem mahler_irreducible {K : Set (Fin 2 → ℝ)} (hK : MahlerIrreducible.IsIrreducible K)
    {ℓ : Set (Fin 2 → ℝ)} (hℓ : IsTacLine K ℓ) :
    ∃ (Λ : Submodule ℤ (Fin 2 → ℝ)) (P₀ P₁ P₂ : Fin 2 → ℝ), MinkowskiMahler.IsCritical K Λ ∧
      P₀ ∈ Λ ∧ P₁ ∈ Λ ∧ P₂ ∈ Λ ∧ P₀ ∈ frontier K ∧ P₁ ∈ frontier K ∧ P₂ ∈ frontier K ∧
      MinkowskiMahler.IsBasis Λ P₀ P₁ ∧ P₁ = P₀ + P₂ ∧
      (P₀ ∈ ℓ ∨ -P₀ ∈ ℓ ∨ P₁ ∈ ℓ ∨ -P₁ ∈ ℓ ∨ P₂ ∈ ℓ ∨ -P₂ ∈ ℓ) := by
  have hKd := hK.1
  obtain ⟨⟨a, ha, M, rfl, haK⟩, ⟨u, hu, huK⟩⟩ := hℓ
  have hu' : a ⬝ᵥ u = M := hu
  -- the point `u` of `K` on `ℓ` is a boundary point, on a critical lattice (Lemma 3)
  have huF : u ∈ frontier K :=
    mm_mem_frontier hKd huK fun hi ↦ (irr_dot_lt ha haK hi).ne hu'
  -- its configuration `u, W, W - u` (paper A, Lemmas 3 and 4)
  obtain ⟨W, hconf⟩ := ml5_conf_of_pi hKd huF ((mahler_irreducible_iff hKd).1 hK u huF)
  have hΔ := irr_minimalDeterminant_pos hKd
  have hcr : cross u W ≠ 0 := by rw [hconf.2.2.2]; exact hΔ.ne'
  have hcrit : IsCritical K (Submodule.span ℤ {u, W}) :=
    ((minkowski_mahler hKd).2 u W (W - u) huF hconf.2.1 hconf.2.2.1 (by abel)).2.1
      (by rw [hconf.2.2.2, abs_of_pos hΔ])
  have m0 : u ∈ Submodule.span ℤ {u, W} := Submodule.subset_span (by simp)
  have m1 : W ∈ Submodule.span ℤ {u, W} := Submodule.subset_span (by simp)
  exact ⟨_, u, W, W - u, hcrit, m0, m1, Submodule.sub_mem _ m1 m0, huF, hconf.2.1, hconf.2.2.1,
    mm_isBasis_span hcr, by abel, Or.inl hu⟩

end External
