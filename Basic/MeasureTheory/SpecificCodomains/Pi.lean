module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Interval integrals of functions with values in `ι → ℝ`

`intervalIntegral.eval_integral`: the components of an interval integral of a function with
values in `ι → ℝ`, `ι` finite, are the interval integrals of its components (the interval-integral
form of `MeasureTheory.eval_integral`).
-/

@[expose] public section

open MeasureTheory

namespace intervalIntegral

/-- The component `i` of the interval integral of an interval integrable `f : ℝ → ι → ℝ` is the
interval integral of the component `i` of `f`. -/
theorem eval_integral {ι : Type*} [Fintype ι] {f : ℝ → ι → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (i : ι) :
    (∫ s in a..b, f s) i = ∫ s in a..b, f s i := by
  have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).intervalIntegral_comp_comm hf
  simpa using this.symm

end intervalIntegral
