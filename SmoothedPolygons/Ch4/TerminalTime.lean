module

public import SmoothedPolygons.Ch3.ControlProblem
public import SmoothedPolygons.Ch7.SmoothedPolygon

/-!
# The terminal time of the global minimizer (Lemma 4.3.1)

The cost in half-plane coordinates is `(3/2) ∫ (x² + y² + 1)/y dt` (`eqn:cost-upper-half-plane`).
Lemma 4.3.1 bounds the terminal time of a global minimizer. Its proof uses that the minimizer has
area less than `π`, which the book does not justify at that point; it follows from the smoothed
octagon (Example before Theorem 7.5.6), which is why this file comes after Chapter 7.
-/

@[expose] public section

namespace SmoothedPolygons

/-- The cost density in half-plane coordinates: `-(3/2)⟨J, Φ(x + iy)⟩ = (3/2)(x² + y² + 1)/y`
(`eqn:cost-upper-half-plane`). -/
theorem cost_density_halfPlane (x y : ℝ) (hy : 0 < y) :
    -(3 / 2) * traceForm J (Φ x y) = 3 / 2 * ((x ^ 2 + y ^ 2 + 1) / y) := by
  sorry

/-- **Lemma 4.3.1** (`lem:tf-pi3`). The global minimizer of the Reinhardt control problem has
terminal time `t_f < π/3`. -/
theorem lemma4_3_1 (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2) (h : IsReinhardtMinimizer T u g X) :
    T < Real.pi / 3 := by
  sorry

end SmoothedPolygons
