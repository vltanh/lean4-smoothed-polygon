module

public import SmoothedPolygons.Ch7.Isolated.VertexFlow
public import SmoothedPolygons.Ch7.Isolated.Switching
public import SmoothedPolygons.Ch7.Isolated.Return
public import SmoothedPolygons.Ch7.Isolated.Poincare
public import SmoothedPolygons.Ch7.Isolated.Hyperbolic
public import SmoothedPolygons.Ch7.Isolated.FixedPoints

/-!
# The smoothed octagon is an isolated extremal (Theorem 7.7.1)

**Theorem 7.7.1** (`thm:oct-isolated`): "The lifted trajectory of the smoothed octagon is an
isolated extremal. That is, in some neighborhood of the set of initial conditions in the cotangent
space, the only extremal trajectory satisfying the transversality conditions at the endpoints is
that of the smoothed octagon." The book gives a proof sketch (E32 of the audit). This file states
the theorem; the sketch is made into a sequence of lemmas, the elementary ones proved and the
analytic ones left with `sorry`, in the modules

* `SmoothedPolygons.Ch7.Isolated.Defs`: all definitions (the statement's vocabulary and the plan's);
* `SmoothedPolygons.Ch7.Isolated.VertexFlow`: steps 0–1;
* `SmoothedPolygons.Ch7.Isolated.Switching`: step 2;
* `SmoothedPolygons.Ch7.Isolated.Return`: step 3;
* `SmoothedPolygons.Ch7.Isolated.Poincare`: step 4;
* `SmoothedPolygons.Ch7.Isolated.Hyperbolic`: step 5;
* `SmoothedPolygons.Ch7.Isolated.FixedPoints`: steps 6–7;

and this file assembles them.

## How the statement reads the book

* *Initial conditions in the cotangent space.* With `g(0) = I₂` (a transversality condition), an
  extremal is determined by `(X(0), Λ₁(0), Λ_R(0), λ_cost)` and its control. The costate
  `(Λ₁, Λ_R, λ_cost)` is only determined up to a positive factor (the conditions of
  `IsPontryaginExtremal` are invariant under `(Λ₁, Λ_R, λ_cost) ↦ c(Λ₁, Λ_R, λ_cost)`,
  `c > 0`), so a neighborhood of the octagon's initial condition is a *conic* one: some positive
  multiple of the costate, together with `X(0)`, lies in a neighborhood `U` of the octagon's
  normalized initial condition `(Φ(i y₀), Λ₁(0), Λ_R(0), -1)` (`InitialConditionMem`). This
  excludes abnormal (`λ_cost = 0`) extremals automatically, and with the nontriviality condition of
  `IsPontryaginExtremal` on the reduced costate (E21) the degenerate lift `Λ₂ = X` does not arise.
* *Up to time translation.* Starting the octagon's lifted trajectory at time `s` instead of `0`
  (with `g(t) = g_oct(s)⁻¹ g_oct(s + t)`) gives again an extremal satisfying all transversality
  conditions (the conditions are invariant under the twisted-periodic continuation
  `q(t + T) = Ad(R⁻¹) q(t)`, `g(t + T) = g(t) R`), whose initial condition tends to the octagon's
  as `s → 0`. So no neighborhood contains only the octagon's initial condition, and the theorem
  must be read up to time translation: the extremal is the octagon's, started at some time `s`
  (`IsOctagonLiftFrom`). The book's proof does the same by working on a Poincaré section.
* *Terminal time near `t_f`.* The octagon's lift on `[0, 28 t_sw]` (seven turns) also satisfies all
  transversality conditions, with the same initial condition. The book's proof (`f⁴ q₀ = q₀`,
  eqn:fp) only treats extremals with four switching intervals, i.e. terminal time near
  `t_f = 4 t_sw`; for long terminal times, periodic orbits of the Poincaré map passing near a
  hyperbolic fixed point are not excluded by its argument. The statement therefore also asks
  `|T - t_f| < ε`; the conclusion then gives `T = t_f`.

The statement is not vacuous: the octagon's own lift satisfies the hypotheses for every `U` and
`ε`, and the conclusion with `s = 0` (`theorem7_7_1_octagon`).

## The proof (the book's sketch, made precise)

Write `q = (X, Λ₁, Λ_R) ∈ 𝔰𝔩₂(ℝ)³` and normalize `λ_cost = -1`. The steps, each a lemma below:

0. *Normalization and time shift* (`iso_smul`, `iso_shift`). Rescale the costate so that
   `λ_cost = -1`; continue the extremal twisted-periodically and restart it at a time `s`.
1. *The extremal flow with a vertex control* (`iso_vertexFlow`, `iso_vertexFlow_solution`,
   `iso_arc_eq_vertexFlow`, `iso_vertexFlow_qFix`). For the control `e_m` the flow is explicit
   from any `q`: `X(t) = Ad(e^{tP})X₀`, `Λ₁(t) = g(t)⁻¹Λ₁(0)g(t)`, and `Λ_R` by variation of
   constants in the frame `e^{-tP} Λ_R e^{tP}` (§7.1). On an arc where the control is `e_m` almost
   everywhere the extremal is this flow (Grönwall). From `q_fix(y₀) = (Φ(iy₀), Λ₁(0), Λ_R(0))` it
   is the explicit lift of Theorem 7.5.1.
2. *Transversality of switching times* (`iso_chi32_hasDerivAt`, `iso_chi32Slope_pos`,
   `iso_chi31_hasDerivAt`, `iso_edge_slope`). The remark after Lemma 7.5.3: `χ₃₂` vanishes at `0`
   with slope `2√3(4 - Y - Y ln(4/Y))/(3y₀²) > 0`, `Y = 1 + 3y₀²`; by the symmetry of Lemma 7.5.3,
   `χ₃₁` vanishes at `t_sw` with the opposite slope. On the switching surface `χ₂₃ = 0` the
   derivative of `χ₃₂` along the state–costate vector field is the same for every control on the
   edge `[e₂, e₃]` of `U_T` (it is the Poisson bracket `{H₃, H₂}`), so near the octagon's switching
   points no singular arc and no chattering can occur.
3. *Same switching structure* (`iso_section_crossing`, `iso_return`). An extremal whose initial
   condition is near the octagon's and whose terminal time is near `t_f` stays near the octagon's
   trajectory (Grönwall, together with the strict inequalities of Lemma 7.5.3 away from the
   switching times and step 2 near them), is bang-bang with controls `e₃, e₁, e₂, e₃` (up to the
   shift), crosses the section `χ₂₃ = 0` near `t = 0` (or near `t = T`), and, restarted there,
   returns to its initial point after four applications of the Poincaré map `f` (eqn:fp).
4. *The Poincaré map* (`iso_poincareTime`, `iso_poincareMap`, `iso_poincareMap_qFix`,
   `iso_poincareMapCoords_hasStrictFDerivAt`). `f(q) = Ad(R) q(t_sw(q), q)`, with `t_sw(q)` the
   first positive zero of `χ₃₁` along the `e₃`-flow; by step 2 and the implicit function theorem it
   is `C¹` near `q_oct`. Every `q_fix(y₀)`, `y₀ ∈ (1/√3, 1)`, is a fixed point (Theorem 7.5.1,
   Lemma 7.5.3).
5. *The direct calculation* (`iso_sectionMatrix`, `iso_sectionBasis`, `iso_fderiv_basis`,
   `iso_sectionMatrix_charpoly`, `iso_octagon_bounds`, `iso_sectionMatrix_octagon_hyperbolic`,
   `iso_hyperbolic`). On the tangent space of the four-dimensional section `N_d` at
   `q_fix(y₀)` the derivative of `f` has, in the basis `iso_sectionBasis`, the explicit matrix
   `iso_sectionMatrix (y₀²) ℓ`, `ℓ = ln(4/(3y₀² + 1))`, whose characteristic polynomial is the
   reciprocal polynomial `z⁴ - e₁z³ + e₂z² - e₁z + 1` (`f` is symplectic). For the octagon
   (`Y = 2√2`, `ℓ = ln 2/2`) the multipliers are `-7.74641, -2.11221, -0.47344, -0.12909`; with
   `w = z + 1/z` the polynomial becomes `z² p(w)`, `p(w) = w² - e₁w + e₂ - 2`, and `p > 0` on
   `[-2, 2]` because `-e₁ > 4` and `p(-2) = 2 + 2e₁ + e₂ > 0`; these two inequalities reduce to
   `(4√2 + 1) ln 2 + 50 - 38√2 > 0` and `10 ln 2 + 52 - 42√2 < 0` (`iso_octagon_bounds`, proved).
   So no multiplier has modulus `1`: the fixed point is hyperbolic.
6. *Implicit function theorem* (`iso_fixedPoints`). On the five-dimensional manifold
   `N = ⋃_d N_d`, `f⁴ - id` has at `q_oct` a derivative of rank four (it is `A⁴ - I` on
   `T N_{d_oct}`, invertible by step 5); its kernel is spanned by the tangent of the family
   `y₀ ↦ q_fix(y₀)`. So near `q_oct` the fixed points of `f⁴` on the section are exactly the
   `q_fix(y₀)` (Mathlib: `HasStrictFDerivAt.implicitFunctionOfProdDomain` in coordinates
   `(d, ξ)`, or the inverse function theorem).
7. *Final transversality* (`iso_trace_sq_of_pow_four`, `iso_y0_of_closing`). For the extremal
   from `q_fix(y₀)` with four switching intervals, `g(t_f) = (g_sw R⁻¹)⁴ R⁴`, so `g(t_f) = R` means
   `(g_sw R⁻¹)⁴ = -I`, hence `(tr(g_sw R⁻¹))² = 2`, `4/(1 + 3y₀²) = √2` and `y₀ = y_oct` (proved).
   This is eqn:theta-k for `k = 1`, used in the converse direction of Lemma 7.5.5.

## Gaps of the book's sketch

* The statement must be read up to time translation and with the terminal time near `t_f` (see
  above); the costate normalization is implicit.
* An extremal near the octagon need not start on the section; the restart at the crossing time
  (step 0, step 3) is not mentioned.
* That nearby extremals are bang-bang with the octagon's switching sequence is not argued: the
  book cites transversality of the first switching time only. One also needs the strict
  inequality at the third vertex (Lemma 7.5.3: `χ₃₁(0) > 0`), the exclusion of singular arcs and
  chattering at the switching points (step 2: the slope of `χ₃₂` on the switching surface does
  not depend on the control on the edge), and a continuous-dependence argument for the
  discontinuous extremal dynamics (step 3).
* The remark after Lemma 7.5.3 gives the slope only for `χ₃₂` at `0`; the Poincaré time needs
  the slope of `χ₃₁` at `t_sw`, which follows by the symmetry `χ₃₁(t_sw - t) = χ₃₂(t)`.
* "Direct calculation shows that the fixed point `q_oct` is hyperbolic" is not given; step 5
  supplies it, with the Jacobian in closed form.
* The book applies the inverse function theorem to `f_d⁴ - I` for each `d` separately; the
  neighborhoods must be uniform in `d`, which the implicit function theorem with parameter `d`
  (step 6) provides. The book's `y₀(d)` uses the monotonicity of `d(y₀)` (Remark 7.5.2, not proved
  in the book); step 6 does not need it (hyperbolicity forces `d'(y_oct) ≠ 0`).
* "The only fixed point `q_fix(d)` satisfying (eqn:theta-k) is `q_oct`" uses Lemma 7.5.5 in the
  converse direction (`g(t_f) = R` implies the trace condition), which step 7 proves.

## The direct calculation in closed form

With `u = y₀²`, `Y = 1 + 3u`, `ℓ = ln(4/Y)` and `D = Yℓ + Y - 4 < 0`, the coefficients of the
characteristic polynomial of the section map at `q_fix(y₀)` are
`e₁ = 8(ℓY(2Y - 3) + (Y - 4)(Y² - 3Y + 1))/(Y²D)` and
`e₂ = -2(ℓ(Y⁴ + 16Y³ - 72Y² + 64) + 9Y⁴ - 60Y³ + 40Y² + 304Y - 320)/(Y³D)`, with
`χ(-1) = 32(ℓ(3Y² - 4) + 4Y² - 21Y + 20)/(Y³D)`; for the octagon `e₁ ≈ -10.46115`,
`e₂ ≈ 22.36330`, `χ(-1) ≈ 3.44100`, `χ(1) ≈ 45.28561`. The slope of `χ₃₁` at `t_sw` is
`2√3 D/(3u) = -iso_chi32Slope y₀`. These were obtained by differentiating the closed-form flow
symbolically and are exact identities in `(y₀, ℓ)` (`ℓ` treated as an independent symbol).

What is proved here: `theorem7_7_1_octagon` (non-vacuity), `iso_smul`, `iso_chi32Slope_pos`,
`iso_qFix_isSectionPt`, `iso_poincareTime_qFix` and `iso_poincareMap_qFix` (from
`iso_vertexFlow_qFix`), `iso_octagon_bounds`, `iso_det_quadratic`,
`iso_sectionMatrix_octagon_hyperbolic` (from `iso_sectionMatrix_charpoly`),
`iso_trace_sq_of_pow_four`, `iso_y0_of_closing`.
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-- **Theorem 7.7.1** (`thm:oct-isolated`). The lifted trajectory of the smoothed octagon is an
isolated extremal: there are a neighborhood `U` of its normalized initial condition in the
cotangent space and `ε > 0` such that every Pontryagin extremal with terminal time
`|T - t_f| < ε` whose initial condition lies in the cone over `U` is the octagon's lifted
trajectory, started at some time `s ∈ [0, 3t_sw)` (the period of `(X, Λ₁, Λ_R)`), with costate
`-λ_cost` times the octagon's; in particular `T = t_f` and `λ_cost < 0`.

The reading (conic neighborhood, up to time translation, terminal time near `t_f`) is explained
in the module docstring; the proof plan is the sequence of lemmas below. -/
theorem theorem7_7_1 :
    ∃ U ∈ 𝓝 octInitialCondition, ∃ ε > 0,
      ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ),
        IsPontryaginExtremal T u g X Λ₁ ΛR lam → |T - tf 1| < ε →
        InitialConditionMem U X Λ₁ ΛR lam →
        T = tf 1 ∧ lam < 0 ∧ ∃ s ∈ Ico 0 (3 * tsw 1), IsOctagonLiftFrom s T u g X Λ₁ ΛR lam := by
  sorry

/-- The statement of Theorem 7.7.1 is not vacuous: the smoothed octagon's own lift is a Pontryagin
extremal with terminal time `t_f`, its initial condition lies in every neighborhood `U` of
`octInitialCondition` (with `c = 1`), and it satisfies the conclusion with `s = 0`. -/
theorem theorem7_7_1_octagon (U : Set (Mat2 × Mat2 × Mat2 × ℝ)) (hU : U ∈ 𝓝 octInitialCondition) :
    IsPontryaginExtremal (tf 1) (polygonControl 1) (polygonG (y₀ 1) (tsw 1))
        (polygonX (y₀ 1) (tsw 1)) octΛ₁ octΛR (-1) ∧
      InitialConditionMem U (polygonX (y₀ 1) (tsw 1)) octΛ₁ octΛR (-1) ∧
      IsOctagonLiftFrom 0 (tf 1) (polygonControl 1) (polygonG (y₀ 1) (tsw 1))
        (polygonX (y₀ 1) (tsw 1)) octΛ₁ octΛR (-1) := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  obtain ⟨hst, hg0, hX0⟩ := poly_isStateTrajectory (y₀ 1) hy0 hy1 4 (by norm_num)
  have hT : ((4 : ℕ) : ℝ) * switchTime (y₀ 1) = (3 * ((1 : ℕ) : ℝ) + 1) * switchTime (y₀ 1) := by
    norm_num
  rw [hT] at hst
  have hext := poly_isPontryaginExtremal 1 le_rfl (y₀ 1) hy0 hy1 (poly_y₀_trace le_rfl) _ _ hst
    hg0 hX0
  have hstart : ∀ f0 : ℝ → Mat2, poly_pw R⁻¹ R (tsw 1) f0 0 = f0 0 := fun f0 ↦ by
    simp [poly_pw]
  refine ⟨hext, ⟨1, one_pos, ?_⟩, fun t _ ↦ ?_, Filter.Eventually.of_forall fun t _ ↦ ?_⟩
  · have hX0' : polygonX (y₀ 1) (tsw 1) 0 = Φ 0 (y₀ 1) := hX0
    simp only [one_smul, one_mul, octΛ₁, octΛR, hstart, hX0']
    exact mem_of_mem_nhds hU
  · have hg0' : polygonG (y₀ 1) (tsw 1) 0 = 1 := hg0
    simp [hg0', octΛ₁, octΛR]
  · simp [polygonControl]

/-! ### Assembly

`theorem7_7_1` follows: given an extremal as in the statement, rescale it (`iso_smul`), restart
it on the section near `q_oct` (`iso_section_crossing`, `iso_shift`), apply `iso_return` to get
`f⁴ q₀ = q₀` and the four arcs, `iso_fixedPoints` to get `q₀ = q_fix(y₀)`, `iso_arc_eq_vertexFlow`
and `iso_vertexFlow_qFix` to identify the arcs with the spline of `y₀`, and `iso_y0_of_closing` with
`g(T) = R` to get `y₀ = y_oct`; then `T = 4 t_sw = t_f`, and undoing the restart gives the shift
`s` (reduced mod `3 t_sw`, the period of `(X, Λ₁, Λ_R)`; `g` is unchanged by this reduction since
`R³ = -I`). -/

end SmoothedPolygons
