module

public import SmoothedPolygons.Ch8.Defs
public import SmoothedPolygons.Ch3.LieAlgebraDynamics
public import SmoothedPolygons.Ch3.ControlProblem

/-!
# A circular arc is not a local minimizer (second variation, proof of Theorem 8.2.7)

The proof of Theorem 8.2.7 (`thm:no-singular-arcs`, TeX 7320–7391) shows by a second variation
that a trajectory of the Reinhardt problem containing a circular arc (`X ≡ J` on an interval) is
not a minimizer; the book cites Mahler's second-variation proof that the circle is not a local
minimizer (`mahler1947area`) as background and gives its own computation (MCA:1049350).

The deformation (TeX 7334–7342): with compactly supported smooth `ψ₁, ψ₂` on `(t₁, t₂)` and
`S(t) = [[ψ₁, ψ₂], [ψ₂, -ψ₁]]`, `g_s(t) = g(t₁) exp(-J t₁) Ψ_s(t) exp(Jt)`, `Ψ_s = exp(s S)`
(the book takes `g₀ = I`; the cost is left invariant). The cost is the parametrization-invariant
`-(3/2) ∫ ⟨J, g⁻¹ dg⟩` (Cartan–Maurer form, eqn `eqn:cost` / (4.3.1)), and
`⟨J, g_s⁻¹ g_s'⟩ = ⟨J, J⟩ + ⟨J, Ψ_s⁻¹ Ψ_s'⟩`, whence (checked with sympy)
`cost(g_s) = cost(g₀) - 3 s² ∫ (ψ₁' ψ₂ - ψ₁ ψ₂') dt + O(s³)` (TeX 7363–7373; the book's
`cost(g₀) = π` holds only on `[0, π/3]`, on `(t₁, t₂)` the cost is `3(t₂ - t₁)`, gap G8).
Choosing `ψ₁, ψ₂` with `∫ (ψ₁'ψ₂ - ψ₁ψ₂') > 0` makes the `s²` term negative. (The book's choice
"`ψ₁' > 0` and `ψ₂' < 0` on their common support" is impossible at the ends of a support of a
compactly supported function and is read on the interior of the overlap; e.g. `ψ₂(t) = ψ₁(t + δ)`
(so `ψ₂` lies to the left of `ψ₁`, as in the book's choice and Remark 8.2.8) for a bump `ψ₁` and
small `δ > 0` gives `∫ (ψ₁'ψ₂ - ψ₁ψ₂') = 2 ∫ ψ₁'(τ) ψ₁(τ + δ) dτ ≈ 2δ ∫ ψ₁'² > 0`; the choice
`ψ₂(t) = ψ₁(t - δ)` gives the opposite sign and raises the cost.)
For small `s` the curvatures of `σ_i = g_s s_i*` stay positive, uniformly close to the circle's
(TeX 7384–7390); the deformed curve, reparametrized to `det X = 1`, is the trajectory of an
admissible control (§3.3–§3.4).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- **A circular arc is not a local minimizer** (the second-variation argument in the proof of
Theorem 8.2.7, TeX 7327–7391; Mahler 1947). If an admissible trajectory of Problem 3.6.2 has
`X ≡ J` on an interval `[t₁, t₂] ⊆ [0, T]` with `t₁ < t₂` (a circular arc: `g = g₀ exp(Jt)`
there), then some admissible trajectory has strictly smaller cost.

Proof (the book's):
1. On `[t₁, t₂]`, `g(t) = g(t₁) exp(J(t - t₁))` (`g' = gJ`).
2. The deformation `g_s = g(t₁) exp(-Jt₁) Ψ_s exp(Jt)` on `[t₁, t₂]` with `Ψ_s = exp(sS)`,
   `S = [[ψ₁, ψ₂], [ψ₂, -ψ₁]]`, `ψᵢ` smooth with compact support in `(t₁, t₂)`; `g_s = g` near the
   ends, `det g_s = 1` (`tr S = 0`). Explicitly `exp(sS) = cosh(s r) I + (sinh(s r)/r) S`,
   `r = √(ψ₁² + ψ₂²)` (`S² = r² I`), smooth in `(s, t)`.
3. The cost `-(3/2) ∫ ⟨J, g⁻¹g'⟩` does not depend on the parametrization of `g`, and
   `cost(g_s) = cost(g) - 3s² ∫ (ψ₁'ψ₂ - ψ₁ψ₂') + O(s³)` (Taylor expansion of the integrand
   `3 + 3s²(ψ₁ψ₂' - ψ₂ψ₁') + O(s³)`, uniformly in `t`).
4. Choose `ψ₁, ψ₂` with `∫ (ψ₁'ψ₂ - ψ₁ψ₂') > 0`; for small `s > 0`, `cost(g_s) < cost(g)`.
5. For small `s`, `X_s = g_s⁻¹ g_s'` is uniformly close to `J`, so it satisfies the star
   inequalities and has positive state-dependent curvatures `κ_j` (Lemma 3.3.1); reparametrize
   by `τ = ∫ √(det X_s)` so that `det X = 1` (the cost is unchanged), and take the control
   `u_j = κ_j / Σ κ` (Definition 3.3.2), which lies in `U_T` and drives `X` (Theorem 3.4.2,
   `theorem3_4_2`). The spliced trajectory (the original outside `[t₁, t₂]`, the reparametrized
   deformation inside, the rest shifted in time) satisfies the boundary conditions of
   Problem 3.6.2 (`g` and `X` agree with the original near `t₁` and `t₂`).
Expected size: 600–1000 lines. -/
theorem l3st_exists_lt_cost_of_circleArc {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁) (h₁₂ : t₁ < t₂) (h₂ : t₂ ≤ T)
    (hX : ∀ t ∈ Icc t₁ t₂, X t = J) :
    ∃ (T' : ℝ) (u' : ℝ → Fin 3 → ℝ) (g' X' : ℝ → Mat2),
      IsReinhardtAdmissible T' u' g' X' ∧ reinhardtCost T' X' < reinhardtCost T X := by
  sorry

end SmoothedPolygons
