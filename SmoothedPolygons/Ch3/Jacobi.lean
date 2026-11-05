module

public import Basic.Analysis.Calculus.MatrixEntrywise
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Jacobi's formula (Lemma 3.1.12)
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- **Lemma 3.1.12** (`lem:Jacobi`, Jacobi's formula). If `A` is a differentiable function of a
real variable with values in `GL_n(ℂ)`, then `det(A)' = det(A) tr(A⁻¹A')`. -/
theorem lemma3_1_12 {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (A' : Matrix (Fin n) (Fin n) ℂ)
    (t : ℝ) (hA : HasDerivAtEntrywise A A' t) (hinv : IsUnit (A t).det) :
    HasDerivAt (fun s ↦ (A s).det) ((A t).det * ((A t)⁻¹ * A').trace) t := by
  sorry

/-- **Lemma 3.1.12** (`lem:Jacobi`), the parenthetical form: without the assumption that `A` is
invertible, `det(A)' = tr(adj(A) A')`, where `adj(A)` is the adjugate of `A`. -/
theorem lemma3_1_12_adjugate {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (A' : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (hA : HasDerivAtEntrywise A A' t) :
    HasDerivAt (fun s ↦ (A s).det) ((A t).adjugate * A').trace t := by
  sorry

end SmoothedPolygons
