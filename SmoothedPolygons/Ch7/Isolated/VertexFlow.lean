module

public import SmoothedPolygons.Ch7.Isolated.Defs

/-!
# Theorem 7.7.1, steps 0–1: normalization, time shift and the vertex flow

Step 0: the conditions of a Pontryagin extremal are homogeneous in the costate (`iso_smul`), and
an extremal can be restarted at any time `s ≥ 0` of its twisted-periodic continuation
(`iso_shift`). Step 1: the closed-form flow `iso_vertexFlow` solves the state–costate equations
with a vertex control (`iso_vertexFlow_solution`), an extremal arc with a vertex control is this
flow (`iso_arc_eq_vertexFlow`), and from `q_fix(y₀)` it is the strong lift of Theorem 7.5.1
(`iso_vertexFlow_qFix`).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### Step 0: normalization and time shift -/

/-- The conditions of a Pontryagin extremal are homogeneous in the costate: `(Λ₁, Λ_R, λ_cost)`
may be multiplied by any `c > 0`. -/
theorem iso_smul {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {c : ℝ} (hc : 0 < c) :
    IsPontryaginExtremal T u g X (fun t ↦ c • Λ₁ t) (fun t ↦ c • ΛR t) (c * lam) := by
  obtain ⟨hst, hg0, hgT, hXT, h1T, hRT, hlam, hpt, hI1, hIR, hmax⟩ := h
  have hc0 : c ≠ 0 := hc.ne'
  have hT : 0 ≤ T := hst.1.le
  -- scaling an integral curve
  have hsc : ∀ {f v : ℝ → Mat2}, IsIntegralCurve f v T →
      IsIntegralCurve (fun t ↦ c • f t) (fun t ↦ c • v t) T := fun {f v} hI i j ↦ by
    obtain ⟨hint, heq⟩ := hI i j
    refine ⟨hint.const_mul c, fun t ht ↦ ?_⟩
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [heq t ht, intervalIntegral.integral_const_mul]
    ring
  have hJ : (3 / 2 * (c * lam)) • J = c • ((3 / 2 * lam) • J) := by rw [smul_smul]; ring_nf
  have htf : ∀ A B : Mat2, traceForm (c • A) B = c * traceForm A B := fun A B ↦ by
    simp [traceForm, Matrix.trace_smul]
  refine ⟨hst, hg0, hgT, hXT, ?_, ?_, mul_nonpos_of_nonneg_of_nonpos hc.le hlam, fun t ht ↦ ?_,
    ?_, ?_, ?_⟩
  · simp only [h1T, Matrix.smul_mul, Matrix.mul_smul]
  · simp only [hRT, Matrix.smul_mul, Matrix.mul_smul]
  · obtain ⟨h1, h2, h3, h4⟩ := hpt t ht
    refine ⟨by rw [Matrix.trace_smul, h1, smul_zero], by rw [Matrix.trace_smul, h2, smul_zero],
      by rw [htf, h3, mul_zero], ?_⟩
    rcases h4 with h | h | h
    · exact Or.inl (mul_ne_zero hc0 h)
    · exact Or.inr (Or.inl (smul_ne_zero hc0 h))
    · exact Or.inr (Or.inr (smul_ne_zero hc0 h))
  · refine poly_isIntegralCurve_congr (hsc hI1) hT fun t _ ↦ ?_
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  · refine poly_isIntegralCurve_congr (hsc hIR) hT fun t _ ↦ ?_
    rw [htf, hJ]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, neg_mul,
      mul_neg]
    module
  · filter_upwards [hmax] with t ht hmem
    obtain ⟨hH, hle⟩ := ht hmem
    have hscale : ∀ v, hamiltonian (c * lam) (c • Λ₁ t) (c • ΛR t) (X t) v =
        c * hamiltonian lam (Λ₁ t) (ΛR t) (X t) v := fun v ↦ by
      simp only [hamiltonian, hJ, ← smul_sub, htf]
      ring
    refine ⟨by rw [hscale, hH, mul_zero], fun v hv ↦ ?_⟩
    rw [hscale, hscale]
    exact mul_le_mul_of_nonneg_left (hle v hv) hc.le

/-- Restarting an extremal at a time `s ≥ 0`: by the transversality conditions the extremal
continues twisted-periodically (`X(t + T) = R⁻¹X(t)R`, `Λ(t + T) = R⁻¹Λ(t)R`,
`g(t + T) = g(t)R`), and the continuation started at `s`, with `g` renormalized to `g(0) = I₂`, is
again an extremal on `[0, T]`. (Not in the book; needed because an extremal near the octagon need
not start on the Poincaré section.) -/
theorem iso_shift {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {s : ℝ} (hs : 0 ≤ s) :
    IsPontryaginExtremal T (fun t ↦ iso_extControl T u (s + t))
      (fun t ↦ (poly_pw 1 R T g s)⁻¹ * poly_pw 1 R T g (s + t))
      (fun t ↦ poly_pw R⁻¹ R T X (s + t)) (fun t ↦ poly_pw R⁻¹ R T Λ₁ (s + t))
      (fun t ↦ poly_pw R⁻¹ R T ΛR (s + t)) lam := by
  sorry

/-! ### Step 1: the extremal flow with a vertex control -/

/-- `iso_vertexFlow` solves the state–costate equations with control `e_m` and `λ_cost = -1`, from
`q` at time `0`. -/
theorem iso_vertexFlow_solution (m : Fin 3) (q : iso_PhasePt)
    (hZ : traceForm (controlMatrix (vertex m)) q.1 ≠ 0) (t : ℝ) :
    HasDerivAtEntrywise (fun s ↦ (iso_vertexFlow m q s).1)
        (controlP (vertex m) (iso_vertexFlow m q t).1 * (iso_vertexFlow m q t).1 -
          (iso_vertexFlow m q t).1 * controlP (vertex m) (iso_vertexFlow m q t).1) t ∧
      HasDerivAtEntrywise (fun s ↦ (iso_vertexFlow m q s).2.1)
        ((iso_vertexFlow m q t).2.1 * (iso_vertexFlow m q t).1 -
          (iso_vertexFlow m q t).1 * (iso_vertexFlow m q t).2.1) t ∧
      HasDerivAtEntrywise (fun s ↦ (iso_vertexFlow m q s).2.2)
        (costateRHS (-1) (iso_vertexFlow m q t).2.1 (iso_vertexFlow m q t).2.2
          (iso_vertexFlow m q t).1 (vertex m)) t ∧
      iso_vertexFlow m q 0 = q := by
  sorry

/-- On an arc where the control is the vertex `e_m` almost everywhere, a normalized extremal is
the vertex flow from its value at the start of the arc (uniqueness for the linear equations,
Grönwall, as in `poly_trajectory_unique` and `str_costateΛR_unique`). -/
theorem iso_arc_eq_vertexFlow {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR (-1)) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ T) (m : Fin 3) (hu : ∀ᵐ t, t ∈ Ioo a b → u t = vertex m) :
    ∀ t ∈ Icc a b, (X t, Λ₁ t, ΛR t) = iso_vertexFlow m (X a, Λ₁ a, ΛR a) (t - a) := by
  sorry

/-- From `q_fix(y₀)` the `e₃`-flow is the explicit lift of Theorem 7.5.1. -/
theorem iso_vertexFlow_qFix (y0 : ℝ) (hy0 : 1 / √3 < y0) (t : ℝ) :
    iso_vertexFlow 2 (iso_qFix y0) t = (segX y0 t, strongΛ₁ y0 t, strongΛR y0 t) := by
  sorry

end SmoothedPolygons
