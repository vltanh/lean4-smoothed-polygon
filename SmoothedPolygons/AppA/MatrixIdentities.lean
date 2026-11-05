module

public import SmoothedPolygons.Defs
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.Basic

/-!
# Matrix identities (Appendix A.6)

Identities for matrices in `𝔰𝔩₂(ℂ)` (Propositions A.6.1–A.6.3) and the matrix exponential of an
element of `𝔰𝔩₂(ℝ)` (Lemma A.6.4).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- **Proposition A.6.1** (`prop:brack-brack`). For `X, Y ∈ 𝔰𝔩₂(ℂ)`,
`ad_X² Y = [[Y, X], X] = -2 det(X) Y - 2XYX = 2⟨X, X⟩Y - 2⟨X, Y⟩X`. -/
theorem propositionA_6_1 (X Y : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.trace = 0) (hY : Y.trace = 0) :
    X * (X * Y - Y * X) - (X * Y - Y * X) * X = (Y * X - X * Y) * X - X * (Y * X - X * Y) ∧
      (Y * X - X * Y) * X - X * (Y * X - X * Y) = (-2 * X.det) • Y - (2 : ℂ) • (X * Y * X) ∧
      (Y * X - X * Y) * X - X * (Y * X - X * Y) =
        (2 * (X * X).trace) • Y - (2 * (X * Y).trace) • X := by
  sorry

/-- **Proposition A.6.2** (`prop:trace-quotient-sub`). For `X, Y, Z, W ∈ 𝔰𝔩₂(ℂ)`,
`⟨X, Z⟩⟨Y, W⟩ - ⟨Y, Z⟩⟨X, W⟩ = -(1/2)⟨[X, Y], [Z, W]⟩`. -/
theorem propositionA_6_2 (X Y Z W : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.trace = 0)
    (hY : Y.trace = 0) (hZ : Z.trace = 0) (hW : W.trace = 0) :
    (X * Z).trace * (Y * W).trace - (Y * Z).trace * (X * W).trace =
      -(1 / 2) * ((X * Y - Y * X) * (Z * W - W * Z)).trace := by
  sorry

/-- **Proposition A.6.3** (`prop:brack-brack-inner-prod`). For `X, Y, Z, W ∈ 𝔰𝔩₂(ℂ)` with
`⟨Y, Z⟩ = 0`, `⟨[X, Y], [Z, W]⟩ = -2⟨X, Z⟩⟨Y, W⟩`. -/
theorem propositionA_6_3 (X Y Z W : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.trace = 0)
    (hY : Y.trace = 0) (hZ : Z.trace = 0) (hW : W.trace = 0) (hYZ : (Y * Z).trace = 0) :
    ((X * Y - Y * X) * (Z * W - W * Z)).trace = -2 * (X * Z).trace * (Y * W).trace := by
  sorry

/-- **Lemma A.6.4** (`lem:exp-of-sl2`). If `X ∈ 𝔰𝔩₂(ℝ)` and `d = det X`, then `exp(X) ∈ SL₂(ℝ)`, and
`exp(tX) = cosh(t√(-d)) I₂ + sinh(t√(-d))/√(-d) X` if `d < 0`,
`exp(tX) = cos(t√d) I₂ + sin(t√d)/√d X` if `d > 0`, and `exp(tX) = I₂ + tX` if `d = 0`. -/
theorem lemmaA_6_4 (X : Matrix (Fin 2) (Fin 2) ℝ) (hX : X.trace = 0) :
    (NormedSpace.exp X).det = 1 ∧
      ∀ t : ℝ,
        (X.det < 0 → NormedSpace.exp (t • X) =
          Real.cosh (t * √(-X.det)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
            (Real.sinh (t * √(-X.det)) / √(-X.det)) • X) ∧
        (0 < X.det → NormedSpace.exp (t • X) =
          Real.cos (t * √X.det) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
            (Real.sin (t * √X.det) / √X.det) • X) ∧
        (X.det = 0 → NormedSpace.exp (t • X) = 1 + t • X) := by
  sorry

end SmoothedPolygons
