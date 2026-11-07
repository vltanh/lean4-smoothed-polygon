module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The inverse of a function with positive derivative and periodic increments

A function `ℓ : ℝ → ℝ` with a positive derivative everywhere is strictly increasing; if moreover
its increments over a period are constant, `ℓ(θ + p) = ℓ(θ) + L` with `p > 0` (as for the
arclength of a periodic curve, or the lift of a degree-one circle map), it is a bijection of `ℝ`,
and its inverse is differentiable with the reciprocal derivative and has the inverse increments
`Θ(t + L) = Θ(t) + p`.

## Main statement

* `exists_inverse_of_hasDerivAt_pos`.
-/

@[expose] public section

open Filter

/-- **The inverse of a function with positive derivative and periodic increments.** If `ℓ` has a
positive derivative `n` everywhere, `ℓ(0) = 0` and `ℓ(θ + p) = ℓ(θ) + L` with `p > 0`, then
`L > 0` and `ℓ` is a bijection of `ℝ`; its inverse `Θ` is continuous, strictly increasing, has
derivative `1/n(Θ(t))`, and `Θ(t + L) = Θ(t) + p`. -/
theorem exists_inverse_of_hasDerivAt_pos {ℓ n : ℝ → ℝ} (hℓ : ∀ θ, HasDerivAt ℓ (n θ) θ)
    (hpos : ∀ θ, 0 < n θ) (h0 : ℓ 0 = 0) {p L : ℝ} (hp : 0 < p)
    (hL : ∀ θ, ℓ (θ + p) = ℓ θ + L) :
    0 < L ∧ ∃ Θ : ℝ → ℝ, Continuous Θ ∧ StrictMono Θ ∧ Θ 0 = 0 ∧ (∀ t, ℓ (Θ t) = t) ∧
      (∀ θ, Θ (ℓ θ) = θ) ∧ (∀ t, Θ (t + L) = Θ t + p) ∧ ∀ t, HasDerivAt Θ (n (Θ t))⁻¹ t := by
  have hmono : StrictMono ℓ := strictMono_of_deriv_pos fun θ ↦ by
    rw [(hℓ θ).deriv]; exact hpos θ
  have hcont : Continuous ℓ := continuous_iff_continuousAt.2 fun θ ↦ (hℓ θ).continuousAt
  have hLpos : 0 < L := by
    have h1 := hL 0
    rw [zero_add, h0] at h1
    have h2 := hmono hp
    rw [h0] at h2
    linarith
  have hk : ∀ (k : ℕ) θ, ℓ (θ + k * p) = ℓ θ + k * L := by
    intro k
    induction k with
    | zero => intro θ; simp
    | succ k ih =>
      intro θ
      push_cast
      rw [show θ + (k + 1) * p = (θ + k * p) + p by ring, hL, ih]
      ring
  have hsurj : Function.Surjective ℓ := by
    refine hcont.surjective (tendsto_atTop_atTop_of_monotone hmono.monotone fun b ↦ ?_)
      (tendsto_atBot_atBot_of_monotone hmono.monotone fun b ↦ ?_)
    · obtain ⟨k, hk'⟩ := exists_nat_ge (b / L)
      refine ⟨0 + k * p, ?_⟩
      rw [hk, h0]
      have := (div_le_iff₀ hLpos).1 hk'
      linarith
    · obtain ⟨k, hk'⟩ := exists_nat_ge (-b / L)
      refine ⟨-(k * p), ?_⟩
      have h1 := hk k (-(k * p))
      rw [neg_add_cancel, h0] at h1
      have := (div_le_iff₀ hLpos).1 hk'
      linarith
  set e := StrictMono.orderIsoOfSurjective ℓ hmono hsurj
  have he1 : ∀ t, ℓ (e.symm t) = t := fun t ↦
    StrictMono.orderIsoOfSurjective_self_symm_apply ℓ hmono hsurj t
  have he2 : ∀ θ, e.symm (ℓ θ) = θ := fun θ ↦
    StrictMono.orderIsoOfSurjective_symm_apply_self ℓ hmono hsurj θ
  refine ⟨hLpos, e.symm, e.symm.continuous, e.symm.strictMono, by have := he2 0; rwa [h0] at this,
    he1, he2,
    fun t ↦ ?_, fun t ↦ ?_⟩
  · conv_lhs => rw [← he1 t]
    rw [← hL, he2]
  · exact HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt (hℓ _) (hpos _).ne'
      (Eventually.of_forall he1)
