module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Analysis.Complex.Basic

/-!
# Entrywise calculus for matrix-valued functions of a real variable

Mathlib puts no canonical norm on `Matrix m n 𝕜`: several norms are available as local instances
(`Matrix.Norms.Elementwise`, `Matrix.Norms.Frobenius`, `Matrix.Norms.Operator`), all equivalent in
finite dimension. To state results about derivatives and Lipschitz continuity of matrix-valued
curves without choosing a norm, we phrase them entry by entry. For finite index types these
notions agree with the corresponding notions for any norm on the matrices.
-/

@[expose] public section

namespace Matrix

variable {m n : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]

/-- The matrix-valued function `f` has derivative `f'` at `t`, entry by entry. -/
def HasDerivAtEntrywise (f : ℝ → Matrix m n 𝕜) (f' : Matrix m n 𝕜) (t : ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun s ↦ f s i j) (f' i j) t

/-- The matrix-valued function `f` has derivative `f'` at `t` within the set `s`, entry by
entry. -/
def HasDerivWithinAtEntrywise (f : ℝ → Matrix m n 𝕜) (f' : Matrix m n 𝕜) (s : Set ℝ) (t : ℝ) :
    Prop :=
  ∀ i j, HasDerivWithinAt (fun s ↦ f s i j) (f' i j) s t

/-- The entrywise derivative of a matrix-valued function (zero in the entries where the entry is
not differentiable, as for `deriv`). -/
noncomputable def derivEntrywise (f : ℝ → Matrix m n 𝕜) (t : ℝ) : Matrix m n 𝕜 :=
  Matrix.of fun i j ↦ deriv (fun s ↦ f s i j) t

/-- Every entry of the real matrix-valued function `f` is Lipschitz on `s`. -/
def LipschitzOnEntrywise (f : ℝ → Matrix m n ℝ) (s : Set ℝ) : Prop :=
  ∀ i j, ∃ C, LipschitzOnWith C (fun t ↦ f t i j) s

end Matrix
