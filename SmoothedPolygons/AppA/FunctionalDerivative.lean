module

public import SmoothedPolygons.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The functional derivative (Definition A.2.1)

For a function `F` on `𝔰𝔩₂(ℝ)`, the functional derivative `δF/δX ∈ 𝔰𝔩₂(ℝ)*` is defined through the
directional derivatives, `F'(X; W) = ⟨W, δF/δX⟩_*` (Definition A.2.1). Throughout the book
`𝔰𝔩₂(ℝ)*` is identified with `𝔰𝔩₂(ℝ)` by the trace form (§6.2, Appendix A.8), so `δF/δX` is the
traceless matrix `D` with `F'(X; W) = ⟨W, D⟩` for every traceless `W`; it is unique because the
trace form is nondegenerate on `𝔰𝔩₂(ℝ)`.
-/

@[expose] public section

namespace SmoothedPolygons

/-- **Definition A.2.1** (`eqn:functional-derivative`), on `V = 𝔰𝔩₂(ℝ)` with `V* ≅ V` by the trace
form: `D ∈ 𝔰𝔩₂(ℝ)` is the functional derivative of `F` at `X` if the directional derivative of `F`
at `X` in every traceless direction `W` exists and equals `⟨W, D⟩`. -/
def HasFunctionalDerivative (F : Mat2 → ℝ) (X D : Mat2) : Prop :=
  D.trace = 0 ∧ ∀ W : Mat2, W.trace = 0 → HasDerivAt (fun s : ℝ ↦ F (X + s • W)) (traceForm W D) 0

end SmoothedPolygons
