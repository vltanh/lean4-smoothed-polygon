module

public import SmoothedPolygons.Ch8.Defs
public import SmoothedPolygons.Ch7.ConstantControl

/-!
# Constant vertex control does not meet the singular locus (Lemma 8.3.4)

Lemma 8.3.4 (`lem:constant-not-singular`, TeX 7619–7670): an extremal trajectory with constant
control at a vertex of `U_T` does not meet the singular locus. ("This lemma does not rule out the
possibility of a chattering arc converging to the singular locus", TeX 7627–7629: that is the
subject of Part "Mahler" and of the hypothesis `NoChatteringIntoSingularLocus` of
Theorem 16.3.1.)

The book's proof expands the switching functions at a point of `𝒮_sing` to third order. Two slips
(gap G6, checked with sympy): `Λ_R'''(0) = +6 λ_cost [J, P₃]`, not `-6 λ_cost [J, P₃]` (TeX 7648),
and the display TeX 7657–7660 lacks an `=` and the factor `λ_cost`. With
`P_i = Z_{e_i}/⟨J, Z_{e_i}⟩`:
`[J, P₃] ⊥ J, P₃`, `P₁ + P₂ + P₃ = -(3/2) J`, `⟨[J, P₃], P₁⟩ = -2√3 = -⟨[J, P₃], P₂⟩`, and the
control term `-⟨Λ_R(t), P_i⟩` has leading coefficients `(2√3 λ_cost, -2√3 λ_cost, 0) t³` for
`i = 1, 2, 3`. The conclusion is unaffected, and the argument works on either side of the meeting
time separately, which covers a meeting time at an end of the interval (the form in which
Theorem 16.3.1 uses the lemma: "A trajectory cannot reach the singular locus with finitely many
switches", TeX 12818–12819).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- **Lemma 8.3.4** (`lem:constant-not-singular`). An extremal lifted trajectory on `[a, b]` whose
control is constant (almost everywhere) at a vertex of `U_T` does not meet the singular locus at
any time of `[a, b]`.

Proof (the book's, TeX 7632–7670, with the sign of G6 corrected): suppose the lift is in `𝒮_sing`
at `t₀ ∈ [a, b]`, say with control `e₃` (the other vertices by the rotation `edgeFrame`). Then
`λ_cost ≠ 0`, `X(t₀) = J`, `Λ₁(t₀) = (3/2) λ_cost J`, `Λ_R(t₀) = 0`
(`l3st_mem_singularLocus_iff`). With constant control, `P` is constant (Lemma 7.1.1,
`lemma7_1_1`) and the state and costate are explicit analytic functions (§7.1:
`X(t) = exp((t - t₀)P) J exp(-(t - t₀)P)`, `Λ₁(t) = g(t)⁻¹ Λ₁(t₀) g(t)` up to the base point, and
the linear equation for `Λ_R`); only `C³` with a Taylor expansion is needed. One computes
`Λ_{1,cost}'(t₀) = 0`, `Λ_R'(t₀) = Λ_R''(t₀) = 0` and `Λ_R'''(t₀) = 6 λ_cost [J, P₃]`, so the
control-dependent term at `e_i` is
`-⟨Λ_R(t), P_i⟩ = -(t - t₀)³ λ_cost ⟨[J, P₃], P_i⟩ + O((t - t₀)⁴)`,
with `⟨[J, P₃], P₁⟩ = -⟨[J, P₃], P₂⟩ = -2√3` and `⟨[J, P₃], P₃⟩ = 0`. For `t ≠ t₀` near `t₀` on
either side, one of `e₁, e₂` gives a strictly larger Hamiltonian than `e₃`, against the maximum
condition for the control `e₃` (which holds almost everywhere). Expected size: 300–500 lines. -/
theorem lemma8_3_4 {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) {i : Fin 3}
    (hu : ∀ᵐ t, t ∈ Ioo a b → u t = vertex i) :
    ∀ t ∈ Icc a b, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus := by
  sorry

end SmoothedPolygons
