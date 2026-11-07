module

public import SmoothedPolygons.Ch3.ControlProblem
public import SmoothedPolygons.Ch7.SmoothedPolygon

/-!
# The terminal time of the global minimizer (Lemma 4.3.1)

The cost in half-plane coordinates is `(3/2) ∫ (x² + y² + 1)/y dt` (`eqn:cost-upper-half-plane`).
Lemma 4.3.1 bounds the terminal time of a global minimizer. Its proof uses that the minimizer has
area less than `π`, which the book does not justify at that point; it follows from the smoothed
octagon (Example before Theorem 7.5.6), which is why this file comes after Chapter 7. Its other
step, that the cost density is at least `3` on star states, needs no minimality: it is stated for
every state trajectory (`three_mul_le_reinhardtCost`), as §6.1 uses it for every competitor.
-/

@[expose] public section

namespace SmoothedPolygons

/-- The cost density in half-plane coordinates: `-(3/2)⟨J, Φ(x + iy)⟩ = (3/2)(x² + y² + 1)/y`
(`eqn:cost-upper-half-plane`). -/
theorem cost_density_halfPlane (x y : ℝ) (hy : 0 < y) :
    -(3 / 2) * traceForm J (Φ x y) = 3 / 2 * ((x ^ 2 + y ^ 2 + 1) / y) := by
  rw [poly_traceForm_J_Φ x y hy]
  ring

/-- A star state `X` has `⟨J, X⟩ < 0`: with `X = [[a, b], [c, -a]]`, the star inequalities
`ρ₀, ρ₁ > 0` give `c > 0`, and `det X = -a² - bc = 1` gives `b < 0`, so `⟨J, X⟩ = b - c < 0`. -/
lemma poly_traceForm_J_neg {X : Mat2} (hX : IsStarState X) : traceForm J X < 0 := by
  obtain ⟨htr, hdet, h0, h1, -⟩ := hX
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  unfold ρ₀ at h0
  unfold ρ₁ at h1
  have h3 : 0 < √3 := by positivity
  have hc : 0 < X 1 0 := by
    have h0' := (div_pos_iff_of_pos_right h3).1 h0
    have h1' := (div_pos_iff_of_pos_right h3).1 h1
    linarith
  have hd : X 1 1 = -X 0 0 := by linarith
  rw [hd] at hdet
  have hb : X 0 1 < 0 := by nlinarith [sq_nonneg (X 0 0)]
  have hJX : traceForm J X = X 0 1 - X 1 0 := by
    simp [traceForm, J, Matrix.trace_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  rw [hJX]
  linarith

/-- The cost density `-(3/2)⟨J, X⟩ = (3/2)(x² + y² + 1)/y ≥ y + 1/y ≥ 2 · (3/2) = 3` on star
states, with `X = Φ(x + iy)` by Lemmas 4.1.1 and 4.2.1 (a star state has `det X = 1` and
`⟨J, X⟩ < 0`). -/
private lemma l2c_three_le_costDensity {X : Mat2} (hX : IsStarState X) :
    3 ≤ -(3 / 2) * traceForm J X := by
  have hmem : X ∈ adjointOrbit J := by
    rw [← lemma4_1_1]
    exact ⟨hX.1, hX.2.1, poly_traceForm_J_neg hX⟩
  obtain ⟨z, -, hz⟩ := lemma4_2_1.surjOn hmem
  have hy := z.im_pos
  rw [← hz, ΦH, cost_density_halfPlane _ _ hy]
  have h2 : 2 ≤ (z.re ^ 2 + z.im ^ 2 + 1) / z.im := by
    rw [le_div_iff₀ hy]
    nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 1)]
  linarith

/-- **The cost is at least three times the terminal time**: the cost density
`-(3/2)⟨J, X⟩ = (3/2)(x² + y² + 1)/y` (`eqn:cost-upper-half-plane`) is at least `3` on star states,
so the cost of every state trajectory on `[0, T]` is at least `3T`. This is the argument of the
proof of Lemma 4.3.1, which needs no minimality; §6.1 uses it to bound the terminal time of every
competitor cheaper than the smoothed octagon (`SmoothedPolygons/Ch6/Existence.lean`). -/
theorem three_mul_le_reinhardtCost {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) : 3 * T ≤ reinhardtCost T X := by
  obtain ⟨hT, -, -, hstar, -, hXI⟩ := h
  have hXc : ContinuousOn X (Set.Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  have hJc : ContinuousOn (fun t ↦ traceForm J (X t)) (Set.Icc 0 T) :=
    (continuous_const.matrix_mul continuous_id).matrix_trace.comp_continuousOn hXc
  have hbound : ∀ t ∈ Set.Icc 0 T, 3 ≤ -(3 / 2) * traceForm J (X t) := fun t ht ↦
    l2c_three_le_costDensity (hstar t ht).2
  have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hT.le
    intervalIntegrable_const ((hJc.intervalIntegrable_of_Icc hT.le).const_mul (-(3 / 2))) hbound
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at this
  simpa [reinhardtCost, smul_eq_mul, mul_comm] using this

/-- **Lemma 4.3.1** (`lem:tf-pi3`). The global minimizer of the Reinhardt control problem has
terminal time `t_f < π/3`.

The book's proof: `area(K_min) < π`, and `(x² + y² + 1)/y ≥ y + 1/y ≥ 2`, so
`π > area(K_min) = (3/2) ∫₀^{t_f} (x² + y² + 1)/y dt ≥ 3 t_f`. Here `X = Φ(x + iy)` by
Lemmas 4.1.1 and 4.2.1 (a star state has `det X = 1` and `⟨J, X⟩ < 0`).

Departure from the paper (a gap the book leaves): the book compares the minimizer with the unit
disk, whose trajectory (`X ≡ J`, constant control `(1/3, 1/3, 1/3)`, `t_f = π/3`) is admissible
with cost `π`; minimality gives only `area(K_min) ≤ π`, and the book does not say why the
inequality is strict. The repair compares with the smoothed octagon instead: its trajectory is
admissible (Theorem 7.5.6 with `k = 1`; a Pontryagin extremal satisfies the boundary conditions)
and its cost is `≈ 3.126 < π` (the example before Theorem 7.5.6). -/
theorem lemma4_3_1 (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2) (h : IsReinhardtMinimizer T u g X) :
    T < Real.pi / 3 := by
  obtain ⟨⟨hst, -, -, -⟩, hmin⟩ := h
  -- the minimizer costs less than the smoothed octagon, whose cost is `< π`
  obtain ⟨⟨g', X', hst', hg0', hX0'⟩, hext⟩ := theorem7_5_6 1 le_rfl
  obtain ⟨-, Λ₁, ΛR, lam, hP⟩ := hext g' X' hst' hg0' hX0'
  have hadm : IsReinhardtAdmissible (tf 1) (polygonControl 1) g' X' :=
    ⟨hst', hg0', hP.2.2.1, hP.2.2.2.1⟩
  have hoct := (example7_5_smoothedOctagon.2.2.2.2 g' X' hst' hg0' hX0').2.2.1
  have hlt : reinhardtCost T X < Real.pi := (hmin _ _ _ _ hadm).trans_lt hoct
  -- `-(3/2)⟨J, X⟩ = (3/2)(x² + y² + 1)/y ≥ 3`, so the cost is at least `3 t_f`
  have hge := three_mul_le_reinhardtCost hst
  linarith [Real.pi_pos]

end SmoothedPolygons
