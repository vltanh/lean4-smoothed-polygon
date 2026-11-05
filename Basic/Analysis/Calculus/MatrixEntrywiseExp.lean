module

public import Basic.Analysis.Calculus.MatrixEntrywise
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Entrywise derivative of the matrix exponential

For a square matrix `A` over `𝕜 = ℝ` or `ℂ` (any `RCLike` field), the curve
`t ↦ exp (t • A)` (with `NormedSpace.exp`, which takes no field argument) has entrywise derivative
`exp (t • A) * A = A * exp (t • A)`. The proofs choose the operator norm on matrices locally
(`open scoped Matrix.Norms.Operator`) and transfer Mathlib's `hasDerivAt_exp_smul_const`; the
statements do not depend on a norm.

## API

Derivatives (the unprimed versions put `A` on the right, as Mathlib's `hasDerivAt_exp_smul_const`):
* `Matrix.hasDerivAtEntrywise_exp_smul_const`: `(exp (t • A))' = exp (t • A) * A`;
* `Matrix.hasDerivAtEntrywise_exp_smul_const'`: `(exp (t • A))' = A * exp (t • A)`;
* `Matrix.hasDerivAtEntrywise_exp_neg_smul_const`: `(exp (-t • A))' = -(exp (-t • A) * A)`;
* `Matrix.hasDerivAtEntrywise_exp_neg_smul_const'`: `(exp (-t • A))' = -(A * exp (-t • A))`.

Algebraic identities for the one-parameter group `t ↦ exp (t • A)` (no norm involved):
* `Matrix.exp_zero_smul`: `exp ((0 : ℝ) • A) = 1`;
* `Matrix.exp_add_smul`: `exp ((s + t) • A) = exp (s • A) * exp (t • A)`;
* `Matrix.exp_smul_mul_exp_neg_smul`: `exp (t • A) * exp (-t • A) = 1`;
* `Matrix.exp_neg_smul_mul_exp_smul`: `exp (-t • A) * exp (t • A) = 1`;
* `Matrix.exp_neg_smul`: `exp (-t • A) = (exp (t • A))⁻¹`;
* `Matrix.commute_exp_smul`: `Commute A (exp (t • A))`, i.e. `A * exp (t • A) = exp (t • A) * A`.

See also Mathlib's `Matrix.exp_add_of_commute`, `Matrix.exp_neg`, `Matrix.isUnit_exp` and the
generic `NormedSpace.exp_zero`.
-/

@[expose] public section

namespace Matrix

variable {m 𝕜 : Type*} [Fintype m] [DecidableEq m] [RCLike 𝕜]

/-! ### Derivatives -/

/-- The derivative of `t ↦ exp (t • A)` is `exp (t • A) * A`, entry by entry. -/
theorem hasDerivAtEntrywise_exp_smul_const (A : Matrix m m 𝕜) (t : ℝ) :
    HasDerivAtEntrywise (fun s : ℝ ↦ NormedSpace.exp (s • A)) (NormedSpace.exp (t • A) * A) t := by
  open scoped Matrix.Norms.Operator in
  -- the uniform structure of the operator norm is the product one, but only up to unfolding
  have : @CompleteSpace (Matrix m m 𝕜) PseudoMetricSpace.toUniformSpace := by
    exact inferInstanceAs (CompleteSpace (Matrix m m 𝕜))
  exact (hasDerivAt_exp_smul_const (𝕂 := ℝ) A t).hasDerivAtEntrywise

/-- The derivative of `t ↦ exp (t • A)` is `A * exp (t • A)`, entry by entry. -/
theorem hasDerivAtEntrywise_exp_smul_const' (A : Matrix m m 𝕜) (t : ℝ) :
    HasDerivAtEntrywise (fun s : ℝ ↦ NormedSpace.exp (s • A)) (A * NormedSpace.exp (t • A)) t := by
  open scoped Matrix.Norms.Operator in
  have : @CompleteSpace (Matrix m m 𝕜) PseudoMetricSpace.toUniformSpace := by
    exact inferInstanceAs (CompleteSpace (Matrix m m 𝕜))
  exact (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t).hasDerivAtEntrywise

/-- The derivative of `t ↦ exp (-t • A)` is `-(exp (-t • A) * A)`, entry by entry. -/
theorem hasDerivAtEntrywise_exp_neg_smul_const (A : Matrix m m 𝕜) (t : ℝ) :
    HasDerivAtEntrywise (fun s : ℝ ↦ NormedSpace.exp (-s • A))
      (-(NormedSpace.exp (-t • A) * A)) t := by
  simpa using (hasDerivAtEntrywise_exp_smul_const A (-t)).scomp (hasDerivAt_neg t)

/-- The derivative of `t ↦ exp (-t • A)` is `-(A * exp (-t • A))`, entry by entry. -/
theorem hasDerivAtEntrywise_exp_neg_smul_const' (A : Matrix m m 𝕜) (t : ℝ) :
    HasDerivAtEntrywise (fun s : ℝ ↦ NormedSpace.exp (-s • A))
      (-(A * NormedSpace.exp (-t • A))) t := by
  simpa using (hasDerivAtEntrywise_exp_smul_const' A (-t)).scomp (hasDerivAt_neg t)

/-! ### The one-parameter group `t ↦ exp (t • A)` -/

theorem exp_zero_smul (A : Matrix m m 𝕜) : NormedSpace.exp ((0 : ℝ) • A) = 1 := by
  rw [zero_smul, NormedSpace.exp_zero]

theorem commute_exp_smul (A : Matrix m m 𝕜) (t : ℝ) : Commute A (NormedSpace.exp (t • A)) :=
  ((Commute.refl A).smul_right t).exp_right

theorem exp_add_smul (A : Matrix m m 𝕜) (s t : ℝ) :
    NormedSpace.exp ((s + t) • A) = NormedSpace.exp (s • A) * NormedSpace.exp (t • A) := by
  rw [add_smul, exp_add_of_commute _ _ (((Commute.refl A).smul_left s).smul_right t)]

theorem exp_smul_mul_exp_neg_smul (A : Matrix m m 𝕜) (t : ℝ) :
    NormedSpace.exp (t • A) * NormedSpace.exp (-t • A) = 1 := by
  rw [← exp_add_smul, add_neg_cancel, exp_zero_smul]

theorem exp_neg_smul_mul_exp_smul (A : Matrix m m 𝕜) (t : ℝ) :
    NormedSpace.exp (-t • A) * NormedSpace.exp (t • A) = 1 := by
  rw [← exp_add_smul, neg_add_cancel, exp_zero_smul]

theorem exp_neg_smul (A : Matrix m m 𝕜) (t : ℝ) :
    NormedSpace.exp (-t • A) = (NormedSpace.exp (t • A))⁻¹ := by
  rw [neg_smul, exp_neg]

end Matrix
