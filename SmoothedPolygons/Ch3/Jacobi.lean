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

/-- **Lemma 3.1.12** (`lem:Jacobi`), the parenthetical form: without the assumption that `A` is
invertible, `det(A)' = tr(adj(A) A')`, where `adj(A)` is the adjugate of `A`.

Departure from the paper: the book verifies the polynomial identity on the dense set of matrices
with distinct nonzero eigenvalues, through a differentiable diagonalization `A = L⁻¹DL`. Mathlib
has neither a differentiable eigen-decomposition nor that density fact, so the formula is proved
instead by differentiating the Leibniz expansion of `det` (product rule) and recognizing
`∑ᵢ det(A with column i replaced by that of A') = tr(adj(A) A')` through Cramer's rule. The user
approved this departure. -/
theorem lemma3_1_12_adjugate {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (A' : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (hA : HasDerivAtEntrywise A A' t) :
    HasDerivAt (fun s ↦ (A s).det) ((A t).adjugate * A').trace t := by
  -- Leibniz expansion and the product rule
  have h : HasDerivAt
      (fun s ↦ ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A s (σ i) i)
      (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, A t (σ j) j) • A' (σ i) i) t :=
    HasDerivAt.fun_sum fun σ _ ↦ (HasDerivAt.fun_finsetProd fun i _ ↦ hA (σ i) i).const_mul _
  convert h using 1
  · funext s
    rw [Matrix.det_apply']
  -- `tr(adj(A) A') = ∑ᵢ det(A with column i replaced by column i of A')`
  · have hcol : ∀ i, ((A t).adjugate * A') i i =
        ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ((∏ j ∈ Finset.univ.erase i, A t (σ j) j) * A' (σ i) i) := by
      intro i
      have h1 : ((A t).adjugate * A') i i = cramer (A t) (fun k ↦ A' k i) i := by
        rw [cramer_eq_adjugate_mulVec]; rfl
      rw [h1, cramer_apply, det_apply']
      refine Finset.sum_congr rfl fun σ _ ↦ ?_
      congr 1
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), updateCol_self, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun j hj ↦ ?_
      rw [updateCol_ne (Finset.ne_of_mem_erase hj)]
    rw [Matrix.trace]
    simp only [diag_apply, hcol, smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]

/-- **Lemma 3.1.12** (`lem:Jacobi`, Jacobi's formula). If `A` is a differentiable function of a
real variable with values in `GL_n(ℂ)`, then `det(A)' = det(A) tr(A⁻¹A')`.

Proof: the parenthetical form `lemma3_1_12_adjugate`, with `det(A) A⁻¹ = adj(A)`.

Departure from the paper: the book verifies the polynomial identity on the dense set of matrices
with distinct nonzero eigenvalues, through a differentiable diagonalization `A = L⁻¹DL`. Mathlib
has neither a differentiable eigen-decomposition nor that density fact, so the formula is proved
instead by differentiating the Leibniz expansion of `det` (product rule) and recognizing
`∑ᵢ det(A with column i replaced by that of A') = tr(adj(A) A')` through Cramer's rule. The user
approved this departure. -/
theorem lemma3_1_12 {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (A' : Matrix (Fin n) (Fin n) ℂ)
    (t : ℝ) (hA : HasDerivAtEntrywise A A' t) (hinv : IsUnit (A t).det) :
    HasDerivAt (fun s ↦ (A s).det) ((A t).det * ((A t)⁻¹ * A').trace) t := by
  convert lemma3_1_12_adjugate A A' t hA using 1
  rw [← smul_eq_mul, ← trace_smul, ← Matrix.smul_mul, inv_def, smul_smul, Ring.inverse_eq_inv',
    mul_inv_cancel₀ hinv.ne_zero, one_smul]

end SmoothedPolygons
