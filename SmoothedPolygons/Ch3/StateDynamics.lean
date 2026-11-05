module

public import SmoothedPolygons.Ch2.MultiCurve
public import Basic.Analysis.Calculus.MatrixEntrywise
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# State dynamics in the Lie group (§3.1)

A multi-curve `σ` determines a curve `g` in `SL₂(ℝ)` with `σ_j(t) = g(t) s_j` (Theorem 3.1.1), and
the curve `X = g⁻¹g'` in `𝔰𝔩₂(ℝ)` (Definition 3.1.3, Theorem 3.1.4). For balanced disks, `X`
satisfies the star inequalities (Corollary 3.1.6), and a reparameterization makes `det X = 1`
(Proposition 3.1.9, Corollaries 3.1.10, 3.1.11).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Matrix

/-- **Theorem 3.1.1** (`thm:defn-g`, Mahler, Hales). A `C^k` multi-curve `σ` on `[0, t_f]` and a
multi-point `s` determine a `C^k` curve `g : [0, t_f] → SL₂(ℝ)` by the conditions
`σ_j(t) = g(t) s_j` for all `j` and `t`; the curve is unique on `[0, t_f]`.
(`C^k` for a matrix-valued curve means that every entry is `C^k`.) -/
theorem theorem3_1_1 (k : ℕ) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ) (hσ : IsMultiCurve k σ tf)
    (s : ZMod 6 → Fin 2 → ℝ) (hs : IsMultiPoint s) :
    ∃ g : ℝ → Mat2, (∀ i j, ContDiffOn ℝ k (fun t ↦ g t i j) (Set.Icc 0 tf)) ∧
      (∀ t ∈ Set.Icc 0 tf, (g t).det = 1 ∧ ∀ j, σ j t = g t *ᵥ s j) ∧
      ∀ g' : ℝ → Mat2, (∀ t ∈ Set.Icc 0 tf, ∀ j, σ j t = g' t *ᵥ s j) →
        Set.EqOn g' g (Set.Icc 0 tf) := by
  sorry

/-- The derivative `g'` of a matrix-valued curve on `[0, t_f]`, entry by entry, within the
interval. -/
noncomputable def curveDeriv (g : ℝ → Mat2) (tf t : ℝ) : Mat2 :=
  Matrix.of fun i j ↦ derivWithin (fun s ↦ g s i j) (Set.Icc 0 tf) t

/-- **Definition 3.1.3** (`def:X-defn`). For a `C¹` curve `g : [0, t_f] → SL₂(ℝ)`, the curve
`X = g⁻¹ g'` (defined by `g' = gX`). -/
noncomputable def curveX (g : ℝ → Mat2) (tf t : ℝ) : Mat2 := (g t)⁻¹ * curveDeriv g tf t

/-- **Theorem 3.1.4** (`thm:defn-X`), parts (1) and (2). Let `K` be a convex disk whose boundary
is parameterized by a regular `C¹` multi-curve `σ`, let `g` be the curve induced by a multi-point
`s` (`σ_j(t) = g(t) s_j`, Theorem 3.1.1), and let `X = g⁻¹g'`. Then `X(t) ∈ 𝔰𝔩₂(ℝ)` and
`σ_j'(t) = Ad_{g(t)}(X(t)) σ_j(t)` for all `j`. Part (3) is `theorem3_1_4_lipschitz`. -/
theorem theorem3_1_4 (K : Set (Fin 2 → ℝ)) (hK : IsConvexDisk K) (σ : ZMod 6 → ℝ → Fin 2 → ℝ)
    (tf : ℝ) (htf : 0 < tf) (hσ : IsMultiCurve 1 σ tf)
    (hreg : ∀ j, ∀ t ∈ Set.Icc 0 tf, derivWithin (σ j) (Set.Icc 0 tf) t ≠ 0)
    (hbd : (⋃ j, σ j '' Set.Icc 0 tf) = frontier K)
    (s : ZMod 6 → Fin 2 → ℝ) (hs : IsMultiPoint s) (g : ℝ → Mat2)
    (hg : ∀ t ∈ Set.Icc 0 tf, (g t).det = 1 ∧ ∀ j, σ j t = g t *ᵥ s j) :
    ∀ t ∈ Set.Icc 0 tf, (curveX g tf t).trace = 0 ∧
      ∀ j, derivWithin (σ j) (Set.Icc 0 tf) t = (g t * curveX g tf t * (g t)⁻¹) *ᵥ σ j t := by
  sorry

/-- **Theorem 3.1.4** (`thm:defn-X`), part (3): `X` is Lipschitz.

The printed statement asks only for a convex disk with a regular `C¹` multi-curve; part (3) is
false in that generality (the unit disk with `σ_j(t) = Rot(θ(t)) s_j*`, `θ(t) = t + t^{3/2}`, gives
`X = θ' J`, which is not Lipschitz). The proof cites Lemma 2.4.3 (`lem:tangents-lipschitz`), which
gives Lipschitz tangents `σ_j'` for the minimizer `K_min` parameterized by arclength (the standing
assumption of §2.4); Chapter 2 is outside the scope of this formalization, so its conclusion is a
hypothesis here. It holds for balanced disks (Definition 2.4.7, item 2). -/
theorem theorem3_1_4_lipschitz (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ) (htf : 0 < tf)
    (hσ : IsMultiCurve 1 σ tf)
    (hLip : ∀ j, ∃ C, LipschitzOnWith C (derivWithin (σ j) (Set.Icc 0 tf)) (Set.Icc 0 tf))
    (s : ZMod 6 → Fin 2 → ℝ) (hs : IsMultiPoint s) (g : ℝ → Mat2)
    (hg : ∀ t ∈ Set.Icc 0 tf, (g t).det = 1 ∧ ∀ j, σ j t = g t *ᵥ s j) :
    LipschitzOnEntrywise (curveX g tf) (Set.Icc 0 tf) := by
  sorry

/-- **Definition 3.1.5** (`eqn:R`). `R = exp(Jπ/3)` is the counterclockwise rotation by `π/3`;
the shared definitions write `R` out, and this is the bridge to the definition by the matrix
exponential. -/
theorem definition3_1_5 : R = NormedSpace.exp ((Real.pi / 3) • J) := by
  sorry

/-- **Corollary 3.1.6** (`cor:X-props`). For a balanced disk `K` with boundary parameterization
`σ_j(t) = g(t) s_j*`, the curve `X = g⁻¹g'` satisfies the star inequalities `ρᵢ(X) > 0`; in
particular `√3 |a| < c`, `3b + c < 0`, `0 < c`, `tr(JX) = b - c < 0` for `X = [[a, b], [c, -a]]`,
and `det X > 0`. -/
theorem corollary3_1_6 (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ)
    (hKσ : IsBalancedPair K σ tf) (g : ℝ → Mat2) (hg : ∀ t j, σ j t = g t *ᵥ sixthRoot j) (t : ℝ) :
    0 < ρ₀ ((g t)⁻¹ * derivEntrywise g t) ∧ 0 < ρ₁ ((g t)⁻¹ * derivEntrywise g t) ∧
      0 < ρ₂ ((g t)⁻¹ * derivEntrywise g t) ∧
      √3 * |((g t)⁻¹ * derivEntrywise g t) 0 0| < ((g t)⁻¹ * derivEntrywise g t) 1 0 ∧
      3 * ((g t)⁻¹ * derivEntrywise g t) 0 1 + ((g t)⁻¹ * derivEntrywise g t) 1 0 < 0 ∧
      0 < ((g t)⁻¹ * derivEntrywise g t) 1 0 ∧
      (J * ((g t)⁻¹ * derivEntrywise g t)).trace < 0 ∧
      0 < ((g t)⁻¹ * derivEntrywise g t).det := by
  sorry

/-- **Proposition 3.1.9** (`prop:reparam-lipschitz`). Let `(K, σ)` be a balanced pair with
`σ_0` parameterized by arclength, `σ_j = g s_j*`, `X = g⁻¹g'`, and let `t ↦ s(t)` be a
reparameterization (`s' > 0`) such that `X̃(t) = X(s(t)) s'(t)` has `det X̃ = 1`. Then `X̃` is
Lipschitz. -/
theorem proposition3_1_9 (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ)
    (hKσ : IsBalancedPair K σ tf)
    (harc : ∀ t, deriv (σ 0) t 0 ^ 2 + deriv (σ 0) t 1 ^ 2 = 1)
    (g : ℝ → Mat2) (hg : ∀ t j, σ j t = g t *ᵥ sixthRoot j)
    (s s' : ℝ → ℝ) (hs : ∀ t, HasDerivAt s (s' t) t) (hs' : ∀ t, 0 < s' t)
    (hdet : ∀ t, (s' t • ((g (s t))⁻¹ * derivEntrywise g (s t))).det = 1) :
    LipschitzOnEntrywise (fun t ↦ s' t • ((g (s t))⁻¹ * derivEntrywise g (s t))) Set.univ := by
  sorry

/-- **Corollary 3.1.10** (`cor:X-diff-ae`). In the parameterization of Proposition 3.1.9 with
`det X̃ = 1`, the curve `X̃` is differentiable almost everywhere (Rademacher's theorem). -/
theorem corollary3_1_10 (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ)
    (hKσ : IsBalancedPair K σ tf)
    (harc : ∀ t, deriv (σ 0) t 0 ^ 2 + deriv (σ 0) t 1 ^ 2 = 1)
    (g : ℝ → Mat2) (hg : ∀ t j, σ j t = g t *ᵥ sixthRoot j)
    (s s' : ℝ → ℝ) (hs : ∀ t, HasDerivAt s (s' t) t) (hs' : ∀ t, 0 < s' t)
    (hdet : ∀ t, (s' t • ((g (s t))⁻¹ * derivEntrywise g (s t))).det = 1) :
    ∀ᵐ t, ∀ i j, DifferentiableAt ℝ
      (fun t ↦ (s' t • ((g (s t))⁻¹ * derivEntrywise g (s t))) i j) t := by
  sorry

/-- **Corollary 3.1.11** (`cor:param-equiv`). For a Lipschitz curve `X` in `𝔰𝔩₂(ℝ)` with
`det X ≠ 0` on `[a, b]` (the setting of Proposition 3.1.9), `det X` is constant if and only if
`X + X⁻¹X' ∈ 𝔰𝔩₂(ℝ)` almost everywhere. -/
theorem corollary3_1_11 (X : ℝ → Mat2) (a b : ℝ) (hab : a ≤ b)
    (htr : ∀ t ∈ Set.Icc a b, (X t).trace = 0) (hdet : ∀ t ∈ Set.Icc a b, (X t).det ≠ 0)
    (hLip : LipschitzOnEntrywise X (Set.Icc a b)) :
    (∃ c, ∀ t ∈ Set.Icc a b, (X t).det = c) ↔
      ∀ᵐ t, t ∈ Set.Ioo a b → (X t + (X t)⁻¹ * derivEntrywise X t).trace = 0 := by
  sorry

end SmoothedPolygons
