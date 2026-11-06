module

public import SmoothedPolygons.Ch7.Isolated.Defs

/-!
# Theorem 7.7.1, step 3: the switching structure of nearby extremals

An extremal near the octagon's crosses the Poincaré section and, restarted there, returns to its
initial point after four applications of the Poincaré map, following the octagon's switching
sequence (eqn:fp).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### Step 3: the switching structure of nearby extremals -/

/-- An extremal whose initial condition is near the octagon's and whose terminal time is near
`t_f` crosses the section `χ₂₃ = 0` near `t = 0` or near `t = T`: some restart of its
twisted-periodic continuation starts on the section, as close to `q_oct` as wanted. (Transversal
crossing by `iso_chi32_hasDerivAt`; the step the book omits.) -/
theorem iso_section_crossing (V : Set iso_PhasePt) (hV : V ∈ 𝓝 (iso_qFix (y₀ 1))) :
    ∃ U ∈ 𝓝 (iso_qFix (y₀ 1)), ∃ ε > 0, ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2),
      IsPontryaginExtremal T u g X Λ₁ ΛR (-1) → |T - tf 1| < ε → (X 0, Λ₁ 0, ΛR 0) ∈ U →
      ∃ s ∈ Ico 0 T,
        (poly_pw R⁻¹ R T X s, poly_pw R⁻¹ R T Λ₁ s, poly_pw R⁻¹ R T ΛR s) ∈ V ∧
          iso_IsSectionPt (poly_pw R⁻¹ R T X s, poly_pw R⁻¹ R T Λ₁ s, poly_pw R⁻¹ R T ΛR s) := by
  sorry

/-- The return map (eqn:fp): a normalized extremal starting on the section near `q_oct`, with
terminal time near `t_f`, is the concatenation of four vertex arcs `e₃, e₁, e₂, e₃` whose
switching times are given by the Poincaré time, `T = t₄`, and `f⁴ q₀ = q₀`. This is where the
strict inequalities of Lemma 7.5.3 (away from the switching times), `iso_chi32_hasDerivAt` and
`iso_edge_slope` (near them), and Grönwall's inequality for the extremal dynamics enter: they
show that the extremal is bang-bang with the octagon's switching sequence. -/
theorem iso_return :
    ∃ V ∈ 𝓝 (iso_qFix (y₀ 1)), ∃ ε > 0, ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2),
      IsPontryaginExtremal T u g X Λ₁ ΛR (-1) → |T - tf 1| < ε → (X 0, Λ₁ 0, ΛR 0) ∈ V →
      iso_IsSectionPt (X 0, Λ₁ 0, ΛR 0) →
      iso_poincareMap^[4] (X 0, Λ₁ 0, ΛR 0) = (X 0, Λ₁ 0, ΛR 0) ∧
        T = iso_poincareSwitchTimes (X 0, Λ₁ 0, ΛR 0) 4 ∧
        ∀ i < 4, ∀ t ∈ Icc (iso_poincareSwitchTimes (X 0, Λ₁ 0, ΛR 0) i)
            (iso_poincareSwitchTimes (X 0, Λ₁ 0, ΛR 0) (i + 1)),
          (X t, Λ₁ t, ΛR t) = iso_adRinvPow i
            (iso_vertexFlow 2 (iso_poincareMap^[i] (X 0, Λ₁ 0, ΛR 0))
              (t - iso_poincareSwitchTimes (X 0, Λ₁ 0, ΛR 0) i)) := by
  sorry

end SmoothedPolygons
