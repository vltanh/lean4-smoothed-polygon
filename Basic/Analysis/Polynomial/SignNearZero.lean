module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic.LinearCombination

/-!
# The sign of a real cubic near `0⁺`

For small `t > 0`, the sign of `a + b t + c t² + d t³` is the sign of its first nonzero
coefficient (`exists_forall_Ioc_cubic_pos`).
-/

@[expose] public section

open Set

/-- A continuous function positive at `0` is positive on some `(0, ε]`. -/
private lemma l4n_pos_near_zero {q : ℝ → ℝ} (hq : Continuous q) (h0 : 0 < q 0) :
    ∃ ε > 0, ∀ t ∈ Ioc 0 ε, 0 < q t := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 (hq.continuousAt.eventually (lt_mem_nhds h0))
  refine ⟨ε / 2, by positivity, fun t ht ↦ h ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
  linarith [ht.2]

/-- **The sign of a cubic near `0⁺`**: if the first nonzero coefficient of
`a + b t + c t² + d t³` is positive, the cubic is positive on some `(0, ε]`. -/
theorem exists_forall_Ioc_cubic_pos {a b c d : ℝ}
    (h : 0 < a ∨ (a = 0 ∧ 0 < b) ∨ (a = 0 ∧ b = 0 ∧ 0 < c) ∨ (a = 0 ∧ b = 0 ∧ c = 0 ∧ 0 < d)) :
    ∃ ε > 0, ∀ t ∈ Ioc 0 ε, 0 < a + b * t + c * t ^ 2 + d * t ^ 3 := by
  rcases h with ha | ⟨rfl, hb⟩ | ⟨rfl, rfl, hc⟩ | ⟨rfl, rfl, rfl, hd⟩
  · exact l4n_pos_near_zero (by fun_prop) (by simpa using ha)
  · obtain ⟨ε, hε, h⟩ := l4n_pos_near_zero (q := fun t ↦ b + c * t + d * t ^ 2) (by fun_prop)
      (by simpa using hb)
    refine ⟨ε, hε, fun t ht ↦ ?_⟩
    have := mul_pos ht.1 (h t ht)
    linear_combination this
  · obtain ⟨ε, hε, h⟩ := l4n_pos_near_zero (q := fun t ↦ c + d * t) (by fun_prop)
      (by simpa using hc)
    refine ⟨ε, hε, fun t ht ↦ ?_⟩
    have := mul_pos (pow_pos ht.1 2) (h t ht)
    linear_combination this
  · exact ⟨1, one_pos, fun t ht ↦ by have := pow_pos ht.1 3; nlinarith⟩
