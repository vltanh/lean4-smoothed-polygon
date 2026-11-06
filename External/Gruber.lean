module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The density of a lattice packing

Cited in Definition 2.1.2 of Hales–Vajjha, *Packings of Smoothed Polygons*, from P. M. Gruber,
*Convex and Discrete Geometry*, Grundlehren 336, Springer, 2007, Corollary 30.1: if `C` is a convex
body and `L` a lattice such that the translates `C + l`, `l ∈ L`, have pairwise disjoint
interiors, then the upper and lower densities of the lattice packing `{C + l | l ∈ L}` coincide
and are equal to `V(C)/d(L)`.

Definitions, in the terms of the source. Space is `E^d = ι → ℝ` with Lebesgue measure `V`. A
convex body is a compact convex set, here with nonempty interior. A lattice is
`L = {z₁ b₁ + ⋯ + z_d b_d | zᵢ ∈ ℤ}` for a basis `b₁, …, b_d` of `E^d`, and `d(L) = |det(b₁, …,
b_d)|`. The upper and lower densities of the lattice packing are
`limsup` and `liminf`, as `λ → ∞`, of `Σ_{l ∈ L} V((C + l) ∩ λB^d) / V(λB^d)`, where
`λB^d = {x | Σ xᵢ² ≤ λ²}` is the solid Euclidean ball of radius `λ` about the origin. Densities
take values in `[0, ∞]`.
-/

@[expose] public section

namespace External

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Gruber

variable {ι : Type*} [Fintype ι]

/-- The solid Euclidean ball `λB^d = {x | Σ xᵢ² ≤ λ²}` of radius `λ` about the origin. -/
def ball (r : ℝ) : Set (ι → ℝ) := {x | ∑ i, x i ^ 2 ≤ r ^ 2}

/-- A (proper) convex body: a compact convex set with nonempty interior. -/
def IsConvexBody (C : Set (ι → ℝ)) : Prop :=
  Convex ℝ C ∧ IsCompact C ∧ (interior C).Nonempty

/-- The lattice `L = ℤ b₁ + ⋯ + ℤ b_d` with basis `b`. -/
noncomputable def lattice (b : Module.Basis ι ℝ (ι → ℝ)) : Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ (range b)

/-- The determinant `d(L) = |det(b₁, …, b_d)|` of the lattice with basis `b`. -/
noncomputable def latticeDet [DecidableEq ι] (b : Module.Basis ι ℝ (ι → ℝ)) : ℝ :=
  |(Matrix.of fun i j ↦ b i j).det|

/-- `{C + l | l ∈ L}` is a packing: the translates have pairwise disjoint interiors. -/
def IsLatticePacking (C : Set (ι → ℝ)) (b : Module.Basis ι ℝ (ι → ℝ)) : Prop :=
  ∀ l ∈ lattice b, ∀ l' ∈ lattice b, l ≠ l' →
    Disjoint (interior ((fun x ↦ x + l) '' C)) (interior ((fun x ↦ x + l') '' C))

/-- The ratio `Σ_{l ∈ L} V((C + l) ∩ λB^d) / V(λB^d)`. -/
noncomputable def densityRatio (C : Set (ι → ℝ)) (b : Module.Basis ι ℝ (ι → ℝ)) (r : ℝ) :
    ℝ≥0∞ :=
  (∑' l : lattice b, volume ((fun x ↦ x + (l : ι → ℝ)) '' C ∩ ball r)) / volume (ball (ι := ι) r)

/-- The upper density of the lattice packing `{C + l | l ∈ L}`. -/
noncomputable def upperDensity (C : Set (ι → ℝ)) (b : Module.Basis ι ℝ (ι → ℝ)) : ℝ≥0∞ :=
  limsup (densityRatio C b) atTop

/-- The lower density of the lattice packing `{C + l | l ∈ L}`. -/
noncomputable def lowerDensity (C : Set (ι → ℝ)) (b : Module.Basis ι ℝ (ι → ℝ)) : ℝ≥0∞ :=
  liminf (densityRatio C b) atTop

/-! ### Proof of Corollary 30.1

The standard lattice-point count. Let `R` bound the Euclidean norms of the points of `C`. A
translate `C + l` meeting `λB^d` has `|l| ≤ λ + R`, and `C + l ⊆ λB^d` when `|l| ≤ λ - R`, so
`N(λ - R) V(C) ≤ Σ_{l ∈ L} V((C + l) ∩ λB^d) ≤ N(λ + R) V(C)`, where `N(ρ)` is the number of
lattice points in `ρB^d`. Since `N(ρ) / V(ρB^d) → 1/d(L)` (Mathlib's lattice-point count
`ZLattice.covolume.tendsto_card_le_div`), both bounds divided by `V(λB^d)` tend to `V(C)/d(L)`.
-/

open scoped Pointwise

/-- The Euclidean norm `(Σ xᵢ²)^{1/2}`. -/
private noncomputable def dens_euclNorm (x : ι → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖

private lemma dens_euclNorm_sq (x : ι → ℝ) : dens_euclNorm x ^ 2 = ∑ i, x i ^ 2 := by
  rw [dens_euclNorm, EuclideanSpace.norm_sq_eq]
  simp

private lemma dens_euclNorm_nonneg (x : ι → ℝ) : 0 ≤ dens_euclNorm x := norm_nonneg _

private lemma dens_euclNorm_add (x y : ι → ℝ) :
    dens_euclNorm (x + y) ≤ dens_euclNorm x + dens_euclNorm y := by
  simp only [dens_euclNorm, WithLp.toLp_add]
  exact norm_add_le _ _

private lemma dens_euclNorm_neg (x : ι → ℝ) : dens_euclNorm (-x) = dens_euclNorm x := by
  simp only [dens_euclNorm, WithLp.toLp_neg, norm_neg]

private lemma dens_euclNorm_smul (c : ℝ) (x : ι → ℝ) :
    dens_euclNorm (c • x) = |c| * dens_euclNorm x := by
  simp only [dens_euclNorm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

private lemma dens_continuous_euclNorm : Continuous (dens_euclNorm (ι := ι)) :=
  continuous_norm.comp (PiLp.continuous_toLp 2 _)

private lemma dens_mem_ball {r : ℝ} (hr : 0 ≤ r) {x : ι → ℝ} :
    x ∈ ball r ↔ dens_euclNorm x ≤ r := by
  rw [ball, mem_ofPred_eq, ← dens_euclNorm_sq,
    pow_le_pow_iff_left₀ (dens_euclNorm_nonneg x) hr two_ne_zero]

private lemma dens_isClosed_ball (r : ℝ) : IsClosed (ball (ι := ι) r) :=
  isClosed_le (by fun_prop) continuous_const

private lemma dens_isBounded_ball (r : ℝ) : Bornology.IsBounded (ball (ι := ι) r) := by
  refine (Metric.isBounded_closedBall (x := (0 : ι → ℝ)) (r := |r|)).subset fun x hx ↦ ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg r)]
  intro i
  rw [Real.norm_eq_abs]
  exact sq_le_sq.mp ((Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j))
    (Finset.mem_univ i)).trans hx)

private lemma dens_isCompact_ball (r : ℝ) : IsCompact (ball (ι := ι) r) :=
  Metric.isCompact_of_isClosed_isBounded (dens_isClosed_ball r) (dens_isBounded_ball r)

private lemma dens_convex_ball {r : ℝ} (hr : 0 ≤ r) : Convex ℝ (ball (ι := ι) r) := by
  intro x hx y hy a c ha hc hac
  rw [dens_mem_ball hr] at hx hy ⊢
  calc dens_euclNorm (a • x + c • y) ≤ dens_euclNorm (a • x) + dens_euclNorm (c • y) :=
        dens_euclNorm_add _ _
    _ = a * dens_euclNorm x + c * dens_euclNorm y := by
        rw [dens_euclNorm_smul, dens_euclNorm_smul, abs_of_nonneg ha, abs_of_nonneg hc]
    _ ≤ a * r + c * r := by gcongr
    _ = r := by rw [← add_mul, hac, one_mul]

private lemma dens_ball_eq_smul {r : ℝ} (hr : 0 < r) : ball (ι := ι) r = r • ball 1 := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne', dens_mem_ball hr.le, dens_mem_ball zero_le_one,
    dens_euclNorm_smul, abs_of_pos (inv_pos.mpr hr), inv_mul_le_iff₀ hr, mul_one]

private lemma dens_volume_ball {r : ℝ} (hr : 0 < r) :
    volume (ball (ι := ι) r) = ENNReal.ofReal (r ^ Fintype.card ι) * volume (ball (ι := ι) 1) := by
  rw [dens_ball_eq_smul hr, Measure.addHaar_smul, Module.finrank_fintype_fun_eq_card,
    abs_of_pos (pow_pos hr _)]

private lemma dens_volume_ball_one_pos : 0 < volume (ball (ι := ι) 1) := by
  have hU : IsOpen {x : ι → ℝ | ∑ i, x i ^ 2 < 1} := isOpen_lt (by fun_prop) continuous_const
  refine lt_of_lt_of_le (hU.measure_pos volume ⟨0, by simp⟩) (measure_mono fun x hx ↦ ?_)
  simp only [ball, mem_ofPred_eq, one_pow] at hx ⊢
  exact hx.le

private lemma dens_volume_ball_ne_zero {r : ℝ} (hr : 0 < r) : volume (ball (ι := ι) r) ≠ 0 := by
  rw [dens_volume_ball hr]
  exact mul_ne_zero (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne' dens_volume_ball_one_pos.ne'

private lemma dens_volume_ball_ne_top (r : ℝ) : volume (ball (ι := ι) r) ≠ ⊤ :=
  (dens_isCompact_ball r).measure_lt_top.ne

private lemma dens_volumeReal_ball_one_pos : 0 < volume.real (ball (ι := ι) 1) :=
  ENNReal.toReal_pos dens_volume_ball_one_pos.ne' (dens_volume_ball_ne_top 1)

private lemma dens_volumeReal_ball {r : ℝ} (hr : 0 < r) :
    volume.real (ball (ι := ι) r) = r ^ Fintype.card ι * volume.real (ball (ι := ι) 1) := by
  rw [measureReal_def, dens_volume_ball hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _), measureReal_def]

/-- The points of `L` in `s`, as a subtype of `s` or of `L`. -/
private def dens_equiv (L : Submodule ℤ (ι → ℝ)) (s : Set (ι → ℝ)) :
    (s ∩ (L : Set (ι → ℝ)) : Set (ι → ℝ)) ≃ {l : L // (l : ι → ℝ) ∈ s} where
  toFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  invFun l := ⟨l.1.1, l.2, l.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The number `N(ρ)` of lattice points in the ball `ρB^d`. -/
private noncomputable def dens_count (b : Module.Basis ι ℝ (ι → ℝ)) (ρ : ℝ) : ℕ :=
  Nat.card {l : Submodule.span ℤ (range b) // (l : ι → ℝ) ∈ ball ρ}

private lemma dens_finite (b : Module.Basis ι ℝ (ι → ℝ)) (ρ : ℝ) :
    Finite {l : Submodule.span ℤ (range b) // (l : ι → ℝ) ∈ ball ρ} := by
  have := (ZSpan.setFinite_inter b (dens_isBounded_ball ρ)).to_subtype
  exact Finite.of_equiv _ (dens_equiv _ _)

/-- `N(ρ) / ρ^d → V(B^d)/d(L)`: Mathlib's lattice-point count. -/
private lemma dens_tendsto_count [Nonempty ι] (b : Module.Basis ι ℝ (ι → ℝ)) :
    Tendsto (fun ρ : ℝ ↦ (dens_count b ρ : ℝ) / ρ ^ Fintype.card ι) atTop
      (𝓝 (volume.real (ball (ι := ι) 1) / ZLattice.covolume (Submodule.span ℤ (range b)))) := by
  have hd : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hF : ∀ ρ : ℝ, 0 ≤ ρ →
      {x : ι → ℝ | x ∈ univ ∧ dens_euclNorm x ^ Fintype.card ι ≤ ρ ^ Fintype.card ι} =
        ball ρ := by
    intro ρ hρ
    ext x
    rw [mem_ofPred_eq, dens_mem_ball hρ,
      pow_le_pow_iff_left₀ (dens_euclNorm_nonneg x) hρ hd]
    simp
  have hF1 : {x : ι → ℝ | x ∈ univ ∧ dens_euclNorm x ^ Fintype.card ι ≤ 1} = ball 1 := by
    simpa using hF 1 zero_le_one
  have h₁ : ∀ (x : ι → ℝ) ⦃r : ℝ⦄, 0 ≤ r → dens_euclNorm (r • x) ^ Fintype.card ι =
      r ^ Fintype.card ι * dens_euclNorm x ^ Fintype.card ι := by
    intro x r hr
    rw [dens_euclNorm_smul, abs_of_nonneg hr, mul_pow]
  have h₂ := hF1 ▸ dens_isBounded_ball (ι := ι) 1
  have h₃ := hF1 ▸ (dens_isClosed_ball (ι := ι) 1).measurableSet
  have h₄ := hF1 ▸ Convex.addHaar_frontier (volume : Measure (ι → ℝ))
    (dens_convex_ball (ι := ι) zero_le_one)
  have hX : ∀ ⦃x : ι → ℝ⦄ ⦃r : ℝ⦄, x ∈ univ → 0 < r → r • x ∈ univ := fun _ _ _ _ ↦ mem_univ _
  have h := ZLattice.covolume.tendsto_card_le_div (Submodule.span ℤ (range b)) hX h₁ h₂ h₃ h₄
  rw [hF1] at h
  refine (h.comp (tendsto_pow_atTop hd)).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with ρ hρ
  simp only [Function.comp_apply]
  rw [hF ρ hρ, Nat.card_congr (dens_equiv _ _)]
  rfl

/-- `N(ρ) / V(ρB^d) → 1/d(L)`. -/
private lemma dens_tendsto_count_div [Nonempty ι] (b : Module.Basis ι ℝ (ι → ℝ)) :
    Tendsto (fun ρ : ℝ ↦ (dens_count b ρ : ℝ) / volume.real (ball (ι := ι) ρ)) atTop
      (𝓝 (1 / ZLattice.covolume (Submodule.span ℤ (range b)))) := by
  have hv := dens_volumeReal_ball_one_pos (ι := ι)
  have h := (dens_tendsto_count b).div_const (volume.real (ball (ι := ι) 1))
  rw [div_div_cancel_left' hv.ne', ← one_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ρ hρ
  rw [dens_volumeReal_ball hρ, div_div]

/-- `N(ρ + a) / V(ρB^d) → 1/d(L)` for every fixed `a`. -/
private lemma dens_tendsto_count_shift [Nonempty ι] (b : Module.Basis ι ℝ (ι → ℝ)) (a : ℝ) :
    Tendsto (fun ρ : ℝ ↦ (dens_count b (ρ + a) : ℝ) / volume.real (ball (ι := ι) ρ)) atTop
      (𝓝 (1 / ZLattice.covolume (Submodule.span ℤ (range b)))) := by
  have h1 := (dens_tendsto_count_div b).comp (tendsto_atTop_add_const_right atTop a tendsto_id)
  have h2 : Tendsto (fun ρ : ℝ ↦ (1 + a / ρ) ^ Fintype.card ι) atTop (𝓝 1) := by
    have : Tendsto (fun ρ : ℝ ↦ 1 + a / ρ) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    rw [add_zero] at this
    simpa using this.pow (Fintype.card ι)
  have h := h1.mul h2
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (max 0 (-a))] with ρ hρ
  have hρ0 : 0 < ρ := lt_of_le_of_lt (le_max_left _ _) hρ
  have hρa : 0 < ρ + a := by linarith [le_max_right 0 (-a)]
  have hv := dens_volumeReal_ball_one_pos (ι := ι)
  simp only [Function.comp_apply, id]
  rw [dens_volumeReal_ball hρa, dens_volumeReal_ball hρ0,
    show 1 + a / ρ = (ρ + a) / ρ by field_simp, div_pow]
  field_simp

/-- The translates meeting `λB^d` have `|l| ≤ λ + R`, so the sum is at most `N(λ + R) V(C)`. -/
private lemma dens_tsum_le (b : Module.Basis ι ℝ (ι → ℝ)) {C : Set (ι → ℝ)} {R : ℝ}
    (hCR : ∀ x ∈ C, dens_euclNorm x ≤ R) (hR : 0 ≤ R) {r : ℝ} (hr : 0 ≤ r) :
    ∑' l : Submodule.span ℤ (range b), volume ((fun x ↦ x + (l : ι → ℝ)) '' C ∩ ball r) ≤
      dens_count b (r + R) * volume C := by
  set S : Set (Submodule.span ℤ (range b)) := {l | (l : ι → ℝ) ∈ ball (r + R)}
  calc ∑' l : Submodule.span ℤ (range b), volume ((fun x ↦ x + (l : ι → ℝ)) '' C ∩ ball r)
      ≤ ∑' l : Submodule.span ℤ (range b), S.indicator (fun _ ↦ volume C) l := by
        refine tsum_le_tsum fun l ↦ ?_
        by_cases hl : l ∈ S
        · rw [indicator_of_mem hl]
          calc volume ((fun x ↦ x + (l : ι → ℝ)) '' C ∩ ball r)
              ≤ volume ((fun x ↦ x + (l : ι → ℝ)) '' C) := measure_mono inter_subset_left
            _ = volume C := by rw [image_add_right, measure_preimage_add_right]
        · rw [indicator_of_notMem hl]
          have : (fun x ↦ x + (l : ι → ℝ)) '' C ∩ ball r = ∅ := by
            refine eq_empty_of_forall_notMem ?_
            rintro _ ⟨⟨x, hx, rfl⟩, hxr⟩
            apply hl
            change (l : ι → ℝ) ∈ ball (r + R)
            rw [dens_mem_ball (add_nonneg hr hR)]
            rw [dens_mem_ball hr] at hxr
            calc dens_euclNorm (l : ι → ℝ) = dens_euclNorm ((x + (l : ι → ℝ)) + (-x)) := by
                  congr 1; abel
              _ ≤ dens_euclNorm (x + (l : ι → ℝ)) + dens_euclNorm (-x) := dens_euclNorm_add _ _
              _ ≤ r + R := by rw [dens_euclNorm_neg]; linarith [hCR x hx]
          rw [this, measure_empty]
    _ = ∑' _ : S, volume C := (tsum_subtype S fun _ ↦ volume C).symm
    _ = dens_count b (r + R) * volume C := by
        have : Finite S := dens_finite b (r + R)
        rw [ENNReal.tsum_const, ENat.card_eq_coe_natCard, ENat.toENNReal_coe]
        rfl

/-- The translates `C + l` with `|l| ≤ λ - R` lie in `λB^d`, so the sum is at least
`N(λ - R) V(C)`. -/
private lemma dens_le_tsum (b : Module.Basis ι ℝ (ι → ℝ)) {C : Set (ι → ℝ)} {R : ℝ}
    (hCR : ∀ x ∈ C, dens_euclNorm x ≤ R) (hR : 0 ≤ R) {r : ℝ} (hr : R ≤ r) :
    dens_count b (r - R) * volume C ≤
      ∑' l : Submodule.span ℤ (range b), volume ((fun x ↦ x + (l : ι → ℝ)) '' C ∩ ball r) := by
  set S : Set (Submodule.span ℤ (range b)) := {l | (l : ι → ℝ) ∈ ball (r - R)}
  calc (dens_count b (r - R) : ℝ≥0∞) * volume C = ∑' _ : S, volume C := by
        have : Finite S := dens_finite b (r - R)
        rw [ENNReal.tsum_const, ENat.card_eq_coe_natCard, ENat.toENNReal_coe]
        rfl
    _ = ∑' l : Submodule.span ℤ (range b), S.indicator (fun _ ↦ volume C) l :=
        tsum_subtype S fun _ ↦ volume C
    _ ≤ _ := by
        refine tsum_le_tsum fun l ↦ ?_
        by_cases hl : l ∈ S
        · rw [indicator_of_mem hl]
          have hsub : (fun x ↦ x + (l : ι → ℝ)) '' C ⊆ ball r := by
            rintro _ ⟨x, hx, rfl⟩
            have hl' : (l : ι → ℝ) ∈ ball (r - R) := hl
            rw [dens_mem_ball (hR.trans hr)]
            rw [dens_mem_ball (sub_nonneg.mpr hr)] at hl'
            calc dens_euclNorm (x + (l : ι → ℝ)) ≤ dens_euclNorm x + dens_euclNorm (l : ι → ℝ) :=
                  dens_euclNorm_add _ _
              _ ≤ R + (r - R) := add_le_add (hCR x hx) hl'
              _ = r := by ring
          rw [inter_eq_left.mpr hsub, image_add_right, measure_preimage_add_right]
        · rw [indicator_of_notMem hl]
          exact zero_le

end Gruber

open Gruber in
/-- **Gruber, *Convex and Discrete Geometry*, Corollary 30.1.** If `C` is a convex body and `L` a
lattice such that `{C + l | l ∈ L}` is a packing, then its upper and lower densities are both
equal to `V(C)/d(L)`. -/
theorem gruber_corollary_30_1 {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Set (ι → ℝ)}
    (hC : IsConvexBody C) {b : Module.Basis ι ℝ (ι → ℝ)} (hCb : IsLatticePacking C b) :
    upperDensity C b = ENNReal.ofReal (volume.real C / latticeDet b) ∧
      lowerDensity C b = ENNReal.ofReal (volume.real C / latticeDet b) := by
  -- The count below uses only that `C` is compact with nonempty interior: the sums count the
  -- translates with multiplicity, so the disjointness of their interiors is not needed.
  obtain ⟨-, hcomp, hint⟩ := hC
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- `E^0` is a point: every ratio is `1`, and `V(C) = d(L) = 1`.
    have hne : C.Nonempty := hint.mono interior_subset
    have hCu : C = univ := Set.Nonempty.eq_univ (α := ι → ℝ) hne
    have hvol : volume (univ : Set (ι → ℝ)) = 1 := by simp [volume_pi]
    have hdet : latticeDet b = 1 := by simp [latticeDet, Matrix.det_isEmpty]
    have hratio : densityRatio C b = fun _ ↦ 1 := by
      funext r
      have hball : ball (ι := ι) r = univ := by
        ext x
        simp [ball, sq_nonneg]
      have hS : ∀ l : lattice b, (fun x ↦ x + (l : ι → ℝ)) '' C ∩ ball r = univ := fun l ↦ by
        rw [hball, inter_univ]
        exact Set.Nonempty.eq_univ (α := ι → ℝ) (hne.image _)
      have : Unique (lattice b) := { default := 0, uniq := fun _ ↦ Subsingleton.elim _ _ }
      rw [densityRatio, (hasSum_unique _).tsum_eq, hS, hball, hvol,
        ENNReal.div_self one_ne_zero ENNReal.one_ne_top]
    have hval : ENNReal.ofReal (volume.real C / latticeDet b) = 1 := by
      rw [hdet, div_one, measureReal_def, hCu, hvol, ENNReal.toReal_one, ENNReal.ofReal_one]
    rw [upperDensity, lowerDensity, hratio, hval, limsup_const, liminf_const]
    exact ⟨rfl, rfl⟩
  obtain ⟨R₀, hR₀⟩ := hcomp.exists_bound_of_continuousOn dens_continuous_euclNorm.continuousOn
  set R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hCR : ∀ x ∈ C, dens_euclNorm x ≤ R := fun x hx ↦ by
    have := hR₀ x hx
    rw [Real.norm_of_nonneg (dens_euclNorm_nonneg x)] at this
    exact this.trans (le_max_left _ _)
  have hCtop : volume C ≠ ⊤ := hcomp.measure_lt_top.ne
  have hdet : ZLattice.covolume (Submodule.span ℤ (range b)) = latticeDet b := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (ZSpan.isAddFundamentalDomain b volume), ZSpan.volume_real_fundamentalDomain]
    rfl
  have hconv : ∀ (n : ℕ) {r : ℝ}, 0 < r → (n : ℝ≥0∞) * volume C / volume (ball (ι := ι) r) =
      ENNReal.ofReal (n * volume.real C / volume.real (ball (ι := ι) r)) := by
    intro n r hr
    rw [← ENNReal.ofReal_toReal (ENNReal.div_ne_top (ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top n) hCtop) (dens_volume_ball_ne_zero hr)), ENNReal.toReal_div,
      ENNReal.toReal_mul, ENNReal.toReal_natCast]
    rfl
  have key : ∀ a : ℝ, Tendsto (fun r ↦ ENNReal.ofReal ((dens_count b (r + a) : ℝ) *
      volume.real C / volume.real (ball (ι := ι) r))) atTop
        (𝓝 (ENNReal.ofReal (volume.real C / latticeDet b))) := by
    intro a
    refine ENNReal.tendsto_ofReal ?_
    have h := (dens_tendsto_count_shift b a).mul_const (volume.real C)
    rw [hdet, one_div_mul_eq_div] at h
    refine h.congr fun r ↦ ?_
    rw [mul_div_right_comm]
  have hlim : Tendsto (densityRatio C b) atTop
      (𝓝 (ENNReal.ofReal (volume.real C / latticeDet b))) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (key (-R)) (key R) ?_ ?_
    · filter_upwards [eventually_ge_atTop (R + 1)] with r hr
      have hr0 : 0 < r := by linarith
      rw [← sub_eq_add_neg, ← hconv _ hr0]
      exact ENNReal.div_le_div_right (dens_le_tsum b hCR hR (by linarith)) _
    · filter_upwards [eventually_ge_atTop (R + 1)] with r hr
      have hr0 : 0 < r := by linarith
      rw [← hconv _ hr0]
      exact ENNReal.div_le_div_right (dens_tsum_le b hCR hR hr0.le) _
  exact ⟨hlim.limsup_eq, hlim.liminf_eq⟩

end External
