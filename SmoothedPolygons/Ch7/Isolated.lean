module

public import SmoothedPolygons.Ch7.SmoothedPolygon
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The smoothed octagon is an isolated extremal (Theorem 7.7.1)

**Theorem 7.7.1** (`thm:oct-isolated`): "The lifted trajectory of the smoothed octagon is an
isolated extremal. That is, in some neighborhood of the set of initial conditions in the cotangent
space, the only extremal trajectory satisfying the transversality conditions at the endpoints is
that of the smoothed octagon." The book gives a proof sketch (E32 of the audit). This file states
the theorem, makes the sketch into a sequence of lemmas, and proves the elementary ones; the
analytic steps are left with `sorry`.

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

/-! ### The statement -/

/-- The costate `Λ₁` of the smoothed octagon's lift (normalized by `λ_cost = -1`) on `[0, ∞)`: on
the `i`-th switching interval `[iτ, (i+1)τ)`, `τ = t_sw`, the `R⁻ⁱ`-conjugate of the strong lift
of Theorem 7.5.1, as in `poly_isPontryaginExtremal` for `k = 1`. -/
noncomputable def octΛ₁ : ℝ → Mat2 := poly_pw R⁻¹ R (tsw 1) (strongΛ₁ (y₀ 1))

/-- The costate `Λ_R` of the smoothed octagon's lift (normalized by `λ_cost = -1`) on `[0, ∞)`. -/
noncomputable def octΛR : ℝ → Mat2 := poly_pw R⁻¹ R (tsw 1) (strongΛR (y₀ 1))

/-- The initial condition `(X(0), Λ₁(0), Λ_R(0), λ_cost)` of the smoothed octagon's lift in the
cotangent space, normalized by `λ_cost = -1` (`g(0) = I₂` is fixed by transversality). -/
noncomputable def octInitialCondition : Mat2 × Mat2 × Mat2 × ℝ :=
  (Φ 0 (y₀ 1), strongΛ₁ (y₀ 1) 0, strongΛR (y₀ 1) 0, -1)

/-- The initial condition of a lifted trajectory lies in the cone over `U`: the costate is only
determined up to a positive factor, so some positive multiple of `(Λ₁(0), Λ_R(0), λ_cost)`,
together with `X(0)`, lies in `U`. -/
def InitialConditionMem (U : Set (Mat2 × Mat2 × Mat2 × ℝ)) (X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) :
    Prop :=
  ∃ c : ℝ, 0 < c ∧ (X 0, c • Λ₁ 0, c • ΛR 0, c * lam) ∈ U

/-- On `[0, T]`, `(u, g, X, Λ₁, Λ_R, λ_cost)` is the lifted smoothed octagon started at time `s`:
`X(t) = X_oct(s + t)`, `g(t) = g_oct(s)⁻¹ g_oct(s + t)`, the costates are `-λ_cost` times the
octagon's (normalized) costates at `s + t`, and the control is the octagon's control at `s + t`
almost everywhere. -/
def IsOctagonLiftFrom (s T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) : Prop :=
  (∀ t ∈ Icc 0 T, X t = polygonX (y₀ 1) (tsw 1) (s + t) ∧
      g t = (polygonG (y₀ 1) (tsw 1) s)⁻¹ * polygonG (y₀ 1) (tsw 1) (s + t) ∧
      Λ₁ t = (-lam) • octΛ₁ (s + t) ∧ ΛR t = (-lam) • octΛR (s + t)) ∧
    ∀ᵐ t, t ∈ Ioo 0 T → u t = polygonControl 1 (s + t)

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

/-- The relabelling of the controls under conjugation by `R⁻ⁿ`:
`R⁻ⁿ Z_u Rⁿ = Z_{iso_rotControl n u}` (for the vertices this is `poly_conj_pow_vertex`,
`R⁻¹ Z_{e_m} R = Z_{e_{m+1}}`). -/
def iso_rotControl (n : ℕ) (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i ↦ u (i - ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩)

/-- The twisted-periodic continuation to `[0, ∞)` of a control on `[0, T]`: on `[nT, (n+1)T)` it
is `u(t - nT)` relabelled by `R⁻ⁿ`. The states and costates continue as `poly_pw R⁻¹ R T X`,
`poly_pw R⁻¹ R T Λ`, and `g` as `poly_pw 1 R T g` (`g(t + T) = g(t) R`). -/
noncomputable def iso_extControl (T : ℝ) (u : ℝ → Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  iso_rotControl ⌊t / T⌋₊ (u (t - ⌊t / T⌋₊ * T))

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

/-! ### Step 1: the extremal flow with a vertex control

The reduced phase space is `𝔰𝔩₂(ℝ)³ ∋ q = (X, Λ₁, Λ_R)`, `λ_cost = -1`; `g` is recovered from `X`
and `g(0) = I₂`. For the constant control `e_m`, with `P = Z_{e_m}/⟨Z_{e_m}, X₀⟩` (constant along
the arc, Lemma 7.1.1) and `Λ̃ = e^{-tP} Λ_R e^{tP}`, the costate equation `eqn:lamR` becomes
`Λ̃' = -⟨Λ̃, P⟩[P, X₀] - [M, X₀]` with `M(s) = e^{-sP}(Λ₁(s) + (3/2)J)e^{sP}`, and
`c = ⟨Λ̃, P⟩` satisfies `c' = -⟨M, [X₀, P]⟩`; both are solved by quadrature. -/

/-- A point `(X, Λ₁, Λ_R)` of the reduced phase space. -/
abbrev iso_PhasePt : Type := Mat2 × Mat2 × Mat2

/-- `Ad(R)` acting componentwise. -/
noncomputable def iso_adR (q : iso_PhasePt) : iso_PhasePt :=
  (R * q.1 * R⁻¹, R * q.2.1 * R⁻¹, R * q.2.2 * R⁻¹)

/-- `Ad(R⁻ⁿ)` acting componentwise. -/
noncomputable def iso_adRinvPow (n : ℕ) (q : iso_PhasePt) : iso_PhasePt :=
  (R⁻¹ ^ n * q.1 * R ^ n, R⁻¹ ^ n * q.2.1 * R ^ n, R⁻¹ ^ n * q.2.2 * R ^ n)

/-- `P = Z_{e_m}/⟨Z_{e_m}, X₀⟩` at the initial point. -/
noncomputable def iso_vfP (m : Fin 3) (q : iso_PhasePt) : Mat2 := controlP (vertex m) q.1

/-- `g(t) = e^{t(X₀ + P)} e^{-tP}` (`eqn:const-control-g`). -/
noncomputable def iso_vfG (m : Fin 3) (q : iso_PhasePt) (t : ℝ) : Mat2 :=
  constControlG q.1 (iso_vfP m q) t

/-- `X(t) = e^{tP} X₀ e^{-tP}` (`eqn:const-control-z-X`). -/
noncomputable def iso_vfX (m : Fin 3) (q : iso_PhasePt) (t : ℝ) : Mat2 :=
  constControlX q.1 (iso_vfP m q) t

/-- `Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)` (Corollary 6.5.3). -/
noncomputable def iso_vfΛ₁ (m : Fin 3) (q : iso_PhasePt) (t : ℝ) : Mat2 :=
  (iso_vfG m q t)⁻¹ * q.2.1 * iso_vfG m q t

/-- `M(s) = e^{-sP} (Λ₁(s) + (3/2) J) e^{sP}`. -/
noncomputable def iso_vfM (m : Fin 3) (q : iso_PhasePt) (s : ℝ) : Mat2 :=
  NormedSpace.exp (-s • iso_vfP m q) * (iso_vfΛ₁ m q s + (3 / 2 : ℝ) • J) *
    NormedSpace.exp (s • iso_vfP m q)

/-- `c(σ) = ⟨Λ_R(σ), P⟩ = ⟨Λ_R(0), P⟩ - ∫₀^σ ⟨M, [X₀, P]⟩`. -/
noncomputable def iso_vfC (m : Fin 3) (q : iso_PhasePt) (σ : ℝ) : ℝ :=
  traceForm q.2.2 (iso_vfP m q) -
    ∫ s in (0 : ℝ)..σ, traceForm (iso_vfM m q s) (q.1 * iso_vfP m q - iso_vfP m q * q.1)

/-- `Λ_R(t) = e^{tP} (Λ_R(0) - (∫₀ᵗ c) [P, X₀] - ∫₀ᵗ [M, X₀]) e^{-tP}`. -/
noncomputable def iso_vfΛR (m : Fin 3) (q : iso_PhasePt) (t : ℝ) : Mat2 :=
  NormedSpace.exp (t • iso_vfP m q) *
    (q.2.2 - (∫ σ in (0 : ℝ)..t, iso_vfC m q σ) • (iso_vfP m q * q.1 - q.1 * iso_vfP m q) -
      Matrix.of fun i j ↦ ∫ s in (0 : ℝ)..t, (iso_vfM m q s * q.1 - q.1 * iso_vfM m q s) i j) *
    NormedSpace.exp (-t • iso_vfP m q)

/-- The extremal flow (`λ_cost = -1`) with the constant control `e_m` from `q`, in closed form. -/
noncomputable def iso_vertexFlow (m : Fin 3) (q : iso_PhasePt) (t : ℝ) : iso_PhasePt :=
  (iso_vfX m q t, iso_vfΛ₁ m q t, iso_vfΛR m q t)

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

/-- The point `q_fix(y₀) = (Φ(i y₀), Λ₁(0), Λ_R(0))` of the strong lift of Theorem 7.5.1
(`λ_cost = -1`). For `y₀ = y_oct` it is the octagon's normalized initial condition. -/
noncomputable def iso_qFix (y0 : ℝ) : iso_PhasePt := (Φ 0 y0, strongΛ₁ y0 0, strongΛR y0 0)

/-- From `q_fix(y₀)` the `e₃`-flow is the explicit lift of Theorem 7.5.1. -/
theorem iso_vertexFlow_qFix (y0 : ℝ) (hy0 : 1 / √3 < y0) (t : ℝ) :
    iso_vertexFlow 2 (iso_qFix y0) t = (segX y0 t, strongΛ₁ y0 t, strongΛR y0 t) := by
  sorry

/-! ### Step 2: transversality of the switching times -/

/-- The slope of `χ₃₂` at `t = 0` along the strong lift: `2√3 (4 - Y - Y ℓ)/(3y₀²)`,
`Y = 1 + 3y₀²`, `ℓ = ln(4/Y)`. -/
noncomputable def iso_chi32Slope (y0 : ℝ) : ℝ :=
  2 * √3 * (4 - (1 + 3 * y0 ^ 2) - (1 + 3 * y0 ^ 2) * ellSw y0) / (3 * y0 ^ 2)

/-- The remark after Lemma 7.5.3: `χ₃₂` vanishes at `t = 0` with slope `iso_chi32Slope y₀`
(`∂f/∂r = -∂f/∂y = y((4 - y) - y ln(4/y))` on the diagonal, eqn:f'). -/
theorem iso_chi32_hasDerivAt (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    HasDerivAt (fun t ↦ switchingFn 2 1 (strongΛR y0 t) (segX y0 t)) (iso_chi32Slope y0) 0 := by
  sorry

/-- By the symmetry `χ₃₁(t_sw - t) = χ₃₂(t)` (proof of Lemma 7.5.3), `χ₃₁` vanishes at `t_sw`
with slope `-iso_chi32Slope y₀`: the end of the first arc is a transversal switching time, the
hypothesis of the implicit function theorem for the Poincaré time. -/
theorem iso_chi31_hasDerivAt (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    HasDerivAt (fun t ↦ switchingFn 2 0 (strongΛR y0 t) (segX y0 t)) (-iso_chi32Slope y0)
      (switchTime y0) := by
  sorry

/-- The vector field of the state–costate equations (`λ_cost = -1`) with control `u`:
`(X', Λ₁', Λ_R') = ([P, X], [Λ₁, X], eqn:lamR)`, `P = Z_u/⟨Z_u, X⟩`. -/
noncomputable def iso_extremalField (u : Fin 3 → ℝ) (q : iso_PhasePt) : iso_PhasePt :=
  (controlP u q.1 * q.1 - q.1 * controlP u q.1, q.2.1 * q.1 - q.1 * q.2.1,
    costateRHS (-1) q.2.1 q.2.2 q.1 u)

/-- On the switching surface `χ₂₃ = 0`, the derivative of `χ₃₂` along the state–costate vector
field is the same for every control `u` on the edge `[e₂, e₃]` of `U_T` (it is the Poisson
bracket `{H₃, H₂}`: the Hamiltonian vector field of `H_u` is a convex combination of those of
`H₂` and `H₃` where `H₂ = H₃`). With `iso_chi32_hasDerivAt` this excludes singular arcs and
chattering near the octagon's switching points. -/
theorem iso_edge_slope (q : iso_PhasePt) (hX : q.1.trace = 0) (hR : q.2.2.trace = 0)
    (hstar : IsStarState q.1) (hχ : switchingFn 1 2 q.2.2 q.1 = 0) (u : Fin 3 → ℝ)
    (hu : u ∈ controlSimplex) (hu0 : u 0 = 0) :
    HasDerivAt (fun s : ℝ ↦ switchingFn 2 1 (q.2.2 + s • (iso_extremalField u q).2.2)
        (q.1 + s • (iso_extremalField u q).1))
      (deriv (fun s : ℝ ↦ switchingFn 2 1 (q.2.2 + s • (iso_extremalField (vertex 2) q).2.2)
        (q.1 + s • (iso_extremalField (vertex 2) q).1)) 0) 0 := by
  sorry

/-- The slope of the remark after Lemma 7.5.3 is positive: `4 - Y - Y ln(4/Y) > 0` for
`Y = 1 + 3y₀² ∈ (2, 4)`, by `ln x < x - 1` (`x = 4/Y ≠ 1`). -/
theorem iso_chi32Slope_pos (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) : 0 < iso_chi32Slope y0 := by
  obtain ⟨hY2, hY4⟩ := hmax_y_mem hy0 hy1
  have hy : 0 < y0 := poly_y0_pos hy0
  have hYpos : 0 < 1 + 3 * y0 ^ 2 := by linarith
  have hlog : ellSw y0 < 4 / (1 + 3 * y0 ^ 2) - 1 := by
    rw [ellSw, show 3 * y0 ^ 2 + 1 = 1 + 3 * y0 ^ 2 by ring]
    refine Real.log_lt_sub_one_of_pos (by positivity) fun h ↦ ?_
    rw [div_eq_one_iff_eq hYpos.ne'] at h
    linarith
  have hkey : 0 < 4 - (1 + 3 * y0 ^ 2) - (1 + 3 * y0 ^ 2) * ellSw y0 := by
    have h' := mul_lt_mul_of_pos_left hlog hYpos
    rw [mul_sub, mul_div_cancel₀ _ hYpos.ne', mul_one] at h'
    linarith
  unfold iso_chi32Slope
  positivity


/-! ### Step 3: the Poincaré section and map -/

/-- The constraints defining the manifold `M_d` (with `d = det Λ₁` left free) and the Poincaré
section `χ₂₃ = 0`: `X, Λ₁, Λ_R ∈ 𝔰𝔩₂(ℝ)`, `det X = 1`, `⟨X, Λ_R⟩ = 0`, `H = 0` and `χ₂₃ = 0`. The
Hamiltonian is taken at `e₃`; on the section `H(e₂) = H(e₃)`, the maximum near the octagon. -/
def iso_IsSectionPt (q : iso_PhasePt) : Prop :=
  q.1.trace = 0 ∧ q.2.1.trace = 0 ∧ q.2.2.trace = 0 ∧ q.1.det = 1 ∧ traceForm q.1 q.2.2 = 0 ∧
    hamiltonian (-1) q.2.1 q.2.2 q.1 (vertex 2) = 0 ∧ switchingFn 1 2 q.2.2 q.1 = 0

/-- The four-dimensional Poincaré section `N_d` (`det Λ₁ = d`). -/
def iso_sectionN (d : ℝ) : Set iso_PhasePt := {q | iso_IsSectionPt q ∧ q.2.1.det = d}

/-- The Poincaré time `t_sw(q)`: the first positive zero of `χ₃₁` along the `e₃`-flow from `q`. -/
noncomputable def iso_poincareTime (q : iso_PhasePt) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ switchingFn 2 0 (iso_vertexFlow 2 q t).2.2 (iso_vertexFlow 2 q t).1 = 0}

/-- The Poincaré map `f(q) = Ad(R) q(t_sw(q), q)`. -/
noncomputable def iso_poincareMap (q : iso_PhasePt) : iso_PhasePt :=
  iso_adR (iso_vertexFlow 2 q (iso_poincareTime q))

/-- The switching times `t_i = Σ_{j < i} t_sw(f^j q)` of the orbit of `q`. -/
noncomputable def iso_poincareSwitchTimes (q : iso_PhasePt) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range i, iso_poincareTime (iso_poincareMap^[j] q)

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

/-- `q_fix(y₀)` lies on the section (Theorem 7.5.1: `Λ_R(0) ⊥ X(0)`, `χ₂₃(0) = 0`, `H = 0`). -/
theorem iso_qFix_isSectionPt (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    iso_IsSectionPt (iso_qFix y0) := by
  have hy : 0 < y0 := poly_y0_pos hy0
  obtain ⟨htr, -, -, hperp, hchi23, hH, -, -, -⟩ := strongLift_isStrongLift y0 hy0
  have h0 : (0 : ℝ) ∈ Icc 0 (switchTime y0) := ⟨le_rfl, (str_switchTime_pos y0 hy0 hy1).le⟩
  rw [str_segX_zero y0 hy] at hperp hchi23 hH
  refine ⟨by simp [iso_qFix, Φ, Matrix.trace_fin_two], (htr 0 h0).1, (htr 0 h0).2, ?_, ?_, hH,
    hchi23⟩
  · simp only [iso_qFix, Φ, Matrix.det_fin_two_of]
    field_simp
    ring
  · rw [poly_traceForm_comm]
    exact hperp

/-- The Poincaré time of `q_fix(y₀)` is `t_sw(y₀)`: by Lemma 7.5.3, `χ₃₁ > 0` on `[0, t_sw)` and
`χ₃₁(t_sw) = 0`. -/
theorem iso_poincareTime_qFix (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    iso_poincareTime (iso_qFix y0) = switchTime y0 := by
  have hτ := str_switchTime_pos y0 hy0 hy1
  have hχ := lemma7_5_3 y0 hy0 hy1 _ _ (strongLift_isStrongLift y0 hy0)
  obtain ⟨-, -, -, -, -, -, hchi31, -, -⟩ := strongLift_isStrongLift y0 hy0
  refine IsLeast.csInf_eq ⟨⟨hτ, ?_⟩, fun t ht ↦ ?_⟩
  · rw [iso_vertexFlow_qFix y0 hy0]
    exact hchi31
  · obtain ⟨ht0, ht⟩ := ht
    rw [iso_vertexFlow_qFix y0 hy0] at ht
    refine le_of_not_gt fun hlt ↦ ?_
    exact hlt.ne ((hχ t ⟨ht0.le, hlt.le⟩).2.2.1 ht)

/-- Every `q_fix(y₀)` is a fixed point of the Poincaré map: the strong transversality conditions
of Theorem 7.5.1 and `X(z₀, t_sw) = R⁻¹ X₀ R` (`segX_switchTime`). -/
theorem iso_poincareMap_qFix (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    iso_poincareMap (iso_qFix y0) = iso_qFix y0 := by
  obtain ⟨-, -, -, -, -, -, -, hR, h1⟩ := strongLift_isStrongLift y0 hy0
  have hc : ∀ A : Mat2, R * (R⁻¹ * A * R) * R⁻¹ = A := fun A ↦ by
    rw [← mul_assoc, ← mul_assoc, poly_R_mul_inv, one_mul, mul_assoc, poly_R_mul_inv, mul_one]
  rw [iso_poincareMap, iso_poincareTime_qFix y0 hy0 hy1, iso_vertexFlow_qFix y0 hy0, iso_adR]
  simp only [segX_switchTime y0 hy0, hR, h1, hc, iso_qFix]

/-- The coordinates `(X₀₀, X₀₁, X₁₀, Λ₁₀₀, Λ₁₀₁, Λ₁₁₀, Λ_R₀₀, Λ_R₀₁, Λ_R₁₀) ∈ ℝ⁹` of a point of
`𝔰𝔩₂(ℝ)³`. -/
def iso_phaseCoords (q : iso_PhasePt) : Fin 9 → ℝ :=
  ![q.1 0 0, q.1 0 1, q.1 1 0, q.2.1 0 0, q.2.1 0 1, q.2.1 1 0, q.2.2 0 0, q.2.2 0 1, q.2.2 1 0]

/-- The traceless matrices with given coordinates. -/
def iso_phaseOfCoords (v : Fin 9 → ℝ) : iso_PhasePt :=
  (!![v 0, v 1; v 2, -v 0], !![v 3, v 4; v 5, -v 3], !![v 6, v 7; v 8, -v 6])

/-- The Poincaré map in coordinates. -/
noncomputable def iso_poincareMapCoords (v : Fin 9 → ℝ) : Fin 9 → ℝ :=
  iso_phaseCoords (iso_poincareMap (iso_phaseOfCoords v))

/-- The Poincaré map is strictly differentiable at `q_oct` (in coordinates): the vertex flow is
smooth in `(q, t)`, and by `iso_chi31_hasDerivAt` and the implicit function theorem the Poincaré
time is a `C¹` function of `q` near `q_oct`. -/
theorem iso_poincareMapCoords_hasStrictFDerivAt :
    HasStrictFDerivAt iso_poincareMapCoords
      (fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1))))
      (iso_phaseCoords (iso_qFix (y₀ 1))) := by
  sorry

/-! ### Step 4: the direct calculation

The tangent space `T N_d` at `q_fix(y₀)` is the common kernel of the differentials of
`det X`, `⟨X, Λ_R⟩`, `H(e₃)`, `χ₂₃` and `det Λ₁`; it is four-dimensional and invariant under the
derivative of the Poincaré map (the first three functions and `det Λ₁` are invariants of the map,
and its image lies in the section). With `u = y₀²`, `ℓ = ln(4/(3u + 1))`, `Y = 1 + 3u`, the
derivative has, in the basis `iso_sectionBasis y₀ ℓ`, the matrix `iso_sectionMatrix u ℓ`,
computed in closed form by differentiating the closed-form flow (scratch computation, exact in
`(y₀, ℓ)`; it reproduces the multipliers of the smoothed `(6k+2)`-gons for `k = 1, 2, 3, 5`
found by an independent numerical computation). -/

/-- The constraint map `(det X - 1, ⟨X, Λ_R⟩, H(e₃), χ₂₃, det Λ₁)` in coordinates. -/
noncomputable def iso_sectionConstraints (v : Fin 9 → ℝ) : Fin 5 → ℝ :=
  let q := iso_phaseOfCoords v
  ![q.1.det - 1, traceForm q.1 q.2.2, hamiltonian (-1) q.2.1 q.2.2 q.1 (vertex 2),
    switchingFn 1 2 q.2.2 q.1, q.2.1.det]

/-- The tangent space of the section `N_{d_oct}` at `q_oct`, in coordinates. -/
noncomputable def iso_tangentSection : Submodule ℝ (Fin 9 → ℝ) :=
  LinearMap.ker (fderiv ℝ iso_sectionConstraints (iso_phaseCoords (iso_qFix (y₀ 1)))).toLinearMap

/-- A basis of the tangent space of `N_d` at `q_fix(y₀)` (`ℓ = ln(4/(3y₀² + 1))`), in
coordinates: the free coordinates are `δX₀₀`, `δX₀₁`, `δΛ₁₀₀`, `δΛ₁₀₁` (rescaled by `1`, `1/√3`,
`1/y₀`, `1/(√3 y₀)`), the other five solve the linearized constraints. -/
noncomputable def iso_sectionBasis (y L : ℝ) : Fin 4 → Fin 9 → ℝ :=
  ![![1, 0, 0, 0, 0, 0, -(9*L*y^6 + 21*L*y^4 + 3*L*y^2 - L + 18*y^6 - 9*y^4 - 12*y^2 + 3)/(24*y^5),
      0, 0],
    ![0, √3/3, √3/(3*y^2), 0, 0, 0, 0,
      √3*(3*y^2 + 1)*(3*L*y^4 + 2*L*y^2 - L + 6*y^4 - 9*y^2 + 3)/(36*y^5),
      -√3*(3*L*y^2 + L + 3*y^2 - 3)/(9*y^5)],
    ![0, 0, 0, 1/y, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, √3/(3*y), √3*(y^2 + 1)*(3*y^2 - 1)/(12*y^5), 0,
      -√3*(y - 1)*(y + 1)*(3*y^2 + 1)/(12*y^3), -√3*(y - 1)*(y + 1)*(3*y^2 + 1)/(12*y^5)]]

/-- The matrix of the derivative of the Poincaré map on `T N_d` at `q_fix(y₀)` in the basis
`iso_sectionBasis`, with `u = y₀²` and `L = ln(4/(3u + 1))`; the common factor of the
denominators is `3Lu + L + 3u - 3 = YL + Y - 4 < 0`, `Y = 1 + 3u`. -/
noncomputable def iso_sectionMatrix (u L : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(81*L*u^4 + 162*L*u^3 - 12*L*u^2 - 10*L*u + 3*L + 216*u^4 - 243*u^3 - 3*u^2 + 39*u - 9) /
      (2*u*(3*u + 1)^2*(3*L*u + L + 3*u - 3)),
    4*(6*L*u^2 - L*u - L + 9*u^3 - 12*u^2 + 3)/(u*(3*u + 1)^2*(3*L*u + L + 3*u - 3)),
    -36*u*(u - 1)/((3*u + 1)^2*(3*L*u + L + 3*u - 3)),
    -12*(u - 1)/((3*u + 1)^2*(3*L*u + L + 3*u - 3));
    3*(135*L*u^4 + 216*L*u^3 + 6*L*u^2 - 8*L*u + 3*L + 270*u^4 - 261*u^3 - 33*u^2 + 33*u - 9) /
      (2*(3*u + 1)^2*(3*L*u + L + 3*u - 3)),
    (27*L*u^3 + 99*L*u^2 - 3*L*u - 11*L + 135*u^3 - 153*u^2 - 15*u + 33) /
      ((3*u + 1)^2*(3*L*u + L + 3*u - 3)),
    -108*u^2*(u - 1)/((3*u + 1)^2*(3*L*u + L + 3*u - 3)),
    -36*u*(u - 1)/((3*u + 1)^2*(3*L*u + L + 3*u - 3));
    (u - 1)*(3*L*u + L - 6*u - 3)*(135*L*u^5 + 261*L*u^4 + 126*L*u^3 - 6*L*u^2 - 5*L*u + L +
        270*u^5 - 171*u^4 - 72*u^3 - 42*u^2 + 18*u - 3) /
      (16*u^3*(3*u + 1)^2*(3*L*u + L + 3*u - 3)),
    (u - 1)*(3*L*u + L - 6*u - 3)*(18*L*u^3 + 15*L*u^2 - L + 27*u^4 - 27*u^3 - 3*u + 3) /
      (6*u^3*(3*u + 1)^2*(3*L*u + L + 3*u - 3)),
    -(81*L*u^4 + 18*L*u^3 - 36*L*u^2 - 2*L*u + 3*L + 45*u^3 - 51*u^2 + 15*u - 9) /
      (2*u*(3*u + 1)^2*(3*L*u + L + 3*u - 3)),
    -(45*L*u^4 + 24*L*u^3 - 6*L*u^2 + L + 18*u^4 + 9*u^3 - 27*u^2 + 3*u - 3) /
      (2*u^2*(3*u + 1)^2*(3*L*u + L + 3*u - 3));
    (u - 1)*(3*u - 1)*(3*L*u + L - 6*u - 3)/(u*(3*u + 1)^2),
    2*(u - 1)*(3*L*u + L - 6*u - 3)/(u*(3*u + 1)^2),
    24*u/(3*u + 1)^2,
    -(9*u^2 + 6*u - 7)/(3*u + 1)^2]

/-- `e₁ = tr A`, with `Y = 1 + 3u`. -/
noncomputable def iso_sectionE1 (u L : ℝ) : ℝ :=
  8 * (2*L*(1 + 3*u)^2 - 3*L*(1 + 3*u) + (1 + 3*u)^3 - 7*(1 + 3*u)^2 + 13*(1 + 3*u) - 4) /
    ((1 + 3*u)^2 * (L*(1 + 3*u) + (1 + 3*u) - 4))

/-- `e₂`, the second coefficient of the characteristic polynomial, with `Y = 1 + 3u`. -/
noncomputable def iso_sectionE2 (u L : ℝ) : ℝ :=
  -2 * (L*(1 + 3*u)^4 + 16*L*(1 + 3*u)^3 - 72*L*(1 + 3*u)^2 + 64*L + 9*(1 + 3*u)^4 -
      60*(1 + 3*u)^3 + 40*(1 + 3*u)^2 + 304*(1 + 3*u) - 320) /
    ((1 + 3*u)^3 * (L*(1 + 3*u) + (1 + 3*u) - 4))

/-- `iso_sectionBasis` is a basis of the tangent space of the section at `q_oct`. -/
theorem iso_sectionBasis_mem (j : Fin 4) :
    iso_sectionBasis (y₀ 1) (ellSw (y₀ 1)) j ∈ iso_tangentSection := by
  sorry

theorem iso_sectionBasis_linearIndependent :
    LinearIndependent ℝ (iso_sectionBasis (y₀ 1) (ellSw (y₀ 1))) := by
  sorry

/-- **The direct calculation.** The derivative of the Poincaré map at `q_oct` maps the basis
vectors by the matrix `iso_sectionMatrix`. -/
theorem iso_fderiv_basis (j : Fin 4) :
    fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1)))
        (iso_sectionBasis (y₀ 1) (ellSw (y₀ 1)) j) =
      ∑ i, iso_sectionMatrix (y₀ 1 ^ 2) (ellSw (y₀ 1)) i j •
        iso_sectionBasis (y₀ 1) (ellSw (y₀ 1)) i := by
  sorry

open Polynomial in
/-- The characteristic polynomial of `iso_sectionMatrix` is reciprocal,
`z⁴ - e₁ z³ + e₂ z² - e₁ z + 1` (the Poincaré map is symplectic); an identity of rational
functions in `(u, L)` (checked exactly with sympy). -/
theorem iso_sectionMatrix_charpoly (u L : ℝ) (hu : 0 < u) (hL : 3 * L * u + L + 3 * u - 3 ≠ 0) :
    (iso_sectionMatrix u L).charpoly =
      X ^ 4 - C (iso_sectionE1 u L) * X ^ 3 + C (iso_sectionE2 u L) * X ^ 2 -
        C (iso_sectionE1 u L) * X + 1 := by
  sorry

open Polynomial in
/-- For a `4 × 4` matrix with reciprocal characteristic polynomial `z⁴ - e₁z³ + e₂z² - e₁z + 1`,
`det(M² - cM + 1) = p(c)²` with `p(w) = w² - e₁w + e₂ - 2` (the resultant of the characteristic
polynomial and `z² - cz + 1`: `χ(α) = α² p(α + 1/α)` at the roots `α, 1/α` of `z² - cz + 1`). -/
theorem iso_det_quadratic (M : Matrix (Fin 4) (Fin 4) ℝ) (e₁ e₂ : ℝ)
    (hM : M.charpoly = X ^ 4 - C e₁ * X ^ 3 + C e₂ * X ^ 2 - C e₁ * X + 1) (c : ℝ) :
    (M ^ 2 - c • M + 1).det = (c ^ 2 - e₁ * c + e₂ - 2) ^ 2 := by
  apply Complex.ofReal_injective
  set N : Matrix (Fin 4) (Fin 4) ℂ := Complex.ofRealHom.mapMatrix M with hN
  have hdet : ((M ^ 2 - c • M + 1).det : ℂ) = (N ^ 2 - (c : ℂ) • N + 1).det := by
    have := RingHom.map_det Complex.ofRealHom (M ^ 2 - c • M + 1)
    rw [Complex.ofRealHom_eq_coe] at this
    rw [this, map_add, map_sub, map_pow, map_one]
    congr 3
    ext i j
    simp [hN]
  have hcp : N.charpoly =
      X ^ 4 - C (e₁ : ℂ) * X ^ 3 + C (e₂ : ℂ) * X ^ 2 - C (e₁ : ℂ) * X + 1 := by
    rw [hN, RingHom.mapMatrix_apply, Matrix.charpoly_map, hM]
    simp
  -- `det(N - z) = χ(z)`
  have hev : ∀ z : ℂ, (N - z • 1).det = z ^ 4 - e₁ * z ^ 3 + e₂ * z ^ 2 - e₁ * z + 1 := by
    intro z
    have h1 := Matrix.eval_charpoly N z
    rw [hcp] at h1
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one,
      scalar_apply] at h1
    rw [show N - z • 1 = -(Matrix.scalar (Fin 4) z - N) by
      rw [Matrix.scalar_apply, neg_sub, Matrix.smul_one_eq_diagonal]]
    rw [Matrix.det_neg, Matrix.scalar_apply, ← h1]
    simp only [Fintype.card_fin]
    ring
  -- the roots `α, β = 1/α` of `z² - cz + 1`
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((c : ℂ) ^ 2 - 4) (by norm_num : 0 < 2)
  set α : ℂ := ((c : ℂ) + w) / 2 with hα
  set β : ℂ := (c : ℂ) - α with hβ
  have hαq : α ^ 2 - (c : ℂ) * α + 1 = 0 := by
    rw [hα]; linear_combination hw / 4
  have hfac : N ^ 2 - (c : ℂ) • N + 1 = (N - α • 1) * (N - β • 1) := by
    have hαβ : α * β = 1 := by rw [hβ]; linear_combination -hαq
    have hsum : α + β = c := by rw [hβ]; ring
    rw [sub_mul, mul_sub, mul_sub]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_smul,
      mul_comm β α, hαβ, one_smul]
    rw [← hsum, add_smul, sq]
    abel
  -- `χ(α) χ(β) = p(c)²`
  rw [hdet, hfac, Matrix.det_mul, hev, hev, hβ]
  push_cast
  linear_combination (α ^ 6 - 3*α^5*c + 3*α^4*c^2 + α^4*c*e₁ - α^4*e₁^2 + 2*α^4*e₂ - α^4 -
    α^3*c^3 - 2*α^3*c^2*e₁ + 2*α^3*c*e₁^2 - 4*α^3*c*e₂ + 2*α^3*c + α^2*c^3*e₁ - α^2*c^2*e₁^2 +
    3*α^2*c^2*e₂ - α^2*c^2 - α^2*c*e₁*e₂ + 2*α^2*c*e₁ - α^2*e₁^2 + α^2*e₂^2 - 2*α^2*e₂ +
    3*α^2 - α*c^3*e₂ + α*c^2*e₁*e₂ - 2*α*c^2*e₁ + α*c*e₁^2 - α*c*e₂^2 + 2*α*c*e₂ - 3*α*c +
    c^3*e₁ - c^2*e₁^2 - c^2*e₂ + 4*c^2 + 2*c*e₁*e₂ - 5*c*e₁ - e₂^2 + 4*e₂ - 3) * hαq


/-! ### Step 5: the certified inequalities and hyperbolicity -/

lemma iso_one_add_three_y₀_one_sq : 1 + 3 * y₀ 1 ^ 2 = 2 * √2 := by
  rw [poly_three_y₀_one_sq, poly_sqrt8]; ring

lemma iso_ellSw_octagon : ellSw (y₀ 1) = Real.log 2 / 2 := by
  rw [ellSw, poly_four_div_octagon, Real.log_sqrt (by norm_num)]

lemma iso_sqrt_two_bounds : (1.4142 : ℝ) < √2 ∧ √2 < 1.4143 :=
  ⟨by rw [Real.lt_sqrt (by norm_num)]; norm_num, by rw [Real.sqrt_lt' (by norm_num)]; norm_num⟩

/-- The common denominator `YL + Y - 4 = √2 (ln 2 + 2 - 2√2)` of `iso_sectionMatrix` is negative at
the octagon. -/
lemma iso_octagon_den :
    3 * ellSw (y₀ 1) * y₀ 1 ^ 2 + ellSw (y₀ 1) + 3 * y₀ 1 ^ 2 - 3 < 0 := by
  have hY := iso_one_add_three_y₀_one_sq
  have e : 3 * ellSw (y₀ 1) * y₀ 1 ^ 2 + ellSw (y₀ 1) + 3 * y₀ 1 ^ 2 - 3 =
      ellSw (y₀ 1) * (1 + 3 * y₀ 1 ^ 2) + (1 + 3 * y₀ 1 ^ 2) - 4 := by ring
  rw [e, hY, iso_ellSw_octagon]
  obtain ⟨hs1, hs2⟩ := iso_sqrt_two_bounds
  have hl := Real.log_two_lt_d9
  nlinarith

/-- `e₁` at the octagon: `((4√2 - 3) ln 2 + 42 - 30√2)/(ln 2 + 2 - 2√2) ≈ -10.4612`. -/
lemma iso_sectionE1_octagon :
    iso_sectionE1 (y₀ 1 ^ 2) (ellSw (y₀ 1)) =
      ((4 * √2 - 3) * Real.log 2 + 42 - 30 * √2) / (Real.log 2 + 2 - 2 * √2) := by
  have hY : 1 + 3 * y₀ 1 ^ 2 = 2 * √2 := iso_one_add_three_y₀_one_sq
  have hs2 : √2 ^ 2 = 2 := poly_sqrt_two_sq
  have hs3 : √2 ^ 3 = 2 * √2 := by rw [pow_succ, hs2]
  have hs0 : 0 < √2 := by positivity
  obtain ⟨hlo, hhi⟩ := iso_sqrt_two_bounds
  have hl := Real.log_two_lt_d9
  have hD : Real.log 2 + 2 - 2 * √2 ≠ 0 := by nlinarith
  have hden : Real.log 2 / 2 * (2 * √2) + 2 * √2 - 4 = √2 * (Real.log 2 + 2 - 2 * √2) := by
    linear_combination (2 : ℝ) * hs2
  rw [iso_sectionE1, hY, iso_ellSw_octagon, hden]
  field_simp
  ring_nf
  simp only [hs2, hs3, show √2 ^ 4 = 4 by rw [show 4 = 2 * 2 by rfl, pow_mul, hs2]; norm_num]
  ring

/-- `χ_A(-1) = 2 + 2e₁ + e₂` at the octagon: `(10 ln 2 + 52 - 42√2)/(ln 2 + 2 - 2√2) ≈ 3.4410`. -/
lemma iso_chiNegOne_octagon :
    2 + 2 * iso_sectionE1 (y₀ 1 ^ 2) (ellSw (y₀ 1)) + iso_sectionE2 (y₀ 1 ^ 2) (ellSw (y₀ 1)) =
      (10 * Real.log 2 + 52 - 42 * √2) / (Real.log 2 + 2 - 2 * √2) := by
  have hY : 1 + 3 * y₀ 1 ^ 2 = 2 * √2 := iso_one_add_three_y₀_one_sq
  have hs2 : √2 ^ 2 = 2 := poly_sqrt_two_sq
  have hs3 : √2 ^ 3 = 2 * √2 := by rw [pow_succ, hs2]
  have hs4 : √2 ^ 4 = 4 := by rw [show 4 = 2 * 2 by rfl, pow_mul, hs2]; norm_num
  have hs5 : √2 ^ 5 = 4 * √2 := by rw [pow_succ, hs4]
  have hs0 : 0 < √2 := by positivity
  obtain ⟨hlo, hhi⟩ := iso_sqrt_two_bounds
  have hl := Real.log_two_lt_d9
  have hD : Real.log 2 + 2 - 2 * √2 ≠ 0 := by nlinarith
  have hden : Real.log 2 / 2 * (2 * √2) + 2 * √2 - 4 = √2 * (Real.log 2 + 2 - 2 * √2) := by
    linear_combination (2 : ℝ) * hs2
  rw [iso_sectionE1, iso_sectionE2, hY, iso_ellSw_octagon, hden]
  field_simp
  ring_nf
  simp only [hs2, hs3, hs4, hs5]
  ring

/-- **The certified inequalities** of the direct calculation for the octagon: `-e₁ > 4` and
`p(-2) = χ_A(-1) = 2 + 2e₁ + e₂ > 0`, from `ln 2 ∈ (0.6931471803, 0.6931471808)` and
`√2 ∈ (1.4142, 1.4143)`. They reduce to `ln 2 + 2 - 2√2 < 0`,
`(4√2 + 1) ln 2 + 50 - 38√2 > 0` (`≈ 0.874`) and `10 ln 2 + 52 - 42√2 < 0` (`≈ -0.465`). -/
theorem iso_octagon_bounds :
    4 < -iso_sectionE1 (y₀ 1 ^ 2) (ellSw (y₀ 1)) ∧
      0 < 2 + 2 * iso_sectionE1 (y₀ 1 ^ 2) (ellSw (y₀ 1)) +
        iso_sectionE2 (y₀ 1 ^ 2) (ellSw (y₀ 1)) := by
  rw [iso_chiNegOne_octagon, iso_sectionE1_octagon]
  obtain ⟨hs1, hs2⟩ := iso_sqrt_two_bounds
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hD : Real.log 2 + 2 - 2 * √2 < 0 := by nlinarith
  constructor
  · rw [← neg_div, lt_div_iff_of_neg hD]
    nlinarith [mul_pos (sub_pos.2 hs1) (sub_pos.2 hl1)]
  · exact div_pos_of_neg_of_neg (by nlinarith) hD

/-- The octagon's section matrix has no eigenvalue of modulus `1`: for every `θ`,
`det(A² - 2cos θ A + 1) = p(2cos θ)² > 0`, since `p(w) = (w + 2)² + (-e₁ - 4)(w + 2) + p(-2)` is
positive for `w ≥ -2`. (A complex eigenvalue `e^{iθ}` of the real matrix `A` would make
`A² - 2cos θ A + 1 = (A - e^{iθ})(A - e^{-iθ})` singular.) -/
theorem iso_sectionMatrix_octagon_hyperbolic (θ : ℝ) :
    ((iso_sectionMatrix (y₀ 1 ^ 2) (ellSw (y₀ 1))) ^ 2 -
        (2 * Real.cos θ) • iso_sectionMatrix (y₀ 1 ^ 2) (ellSw (y₀ 1)) + 1).det ≠ 0 := by
  have hu : 0 < y₀ 1 ^ 2 := by
    have := poly_y0_pos (poly_y₀_mem le_rfl).1
    positivity
  rw [iso_det_quadratic _ _ _ (iso_sectionMatrix_charpoly _ _ hu iso_octagon_den.ne)]
  obtain ⟨ha, hb⟩ := iso_octagon_bounds
  have hc := Real.neg_one_le_cos θ
  have hp : 0 < (2 * Real.cos θ) ^ 2 - iso_sectionE1 (y₀ 1 ^ 2) (ellSw (y₀ 1)) * (2 * Real.cos θ) +
      iso_sectionE2 (y₀ 1 ^ 2) (ellSw (y₀ 1)) - 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 ha.le) (show 0 ≤ 2 * Real.cos θ + 2 by linarith),
      sq_nonneg (2 * Real.cos θ + 2)]
  positivity

/-- **"Direct calculation shows that the fixed point `q_oct` is hyperbolic"**: the derivative `A`
of the Poincaré map on the tangent space of the section has no eigenvalue of modulus `1`, in the
real form: `A²v - 2cos θ Av + v = 0` only for `v = 0`. (From `iso_sectionBasis_mem`,
`iso_sectionBasis_linearIndependent`, `iso_fderiv_basis` and
`iso_sectionMatrix_octagon_hyperbolic`, once the tangent space is known to be four-dimensional.) -/
theorem iso_hyperbolic (θ : ℝ) (v : Fin 9 → ℝ) (hv : v ∈ iso_tangentSection)
    (h : fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1)))
          (fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1))) v) -
        (2 * Real.cos θ) • fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1))) v +
          v = 0) :
    v = 0 := by
  sorry

/-! ### Step 6: the implicit function theorem -/

/-- Near `q_oct`, the fixed points of `f⁴` on the section are the `q_fix(y₀)`. In coordinates
`(d, ξ)` on `N = ⋃_d N_d` (or with `X₁₀ = 1/y₀` as the parameter), `f⁴ - id` has an invertible
partial derivative `A⁴ - I` in `ξ` (by `iso_hyperbolic` with `θ ∈ {0, π/2, π}`), so its zero set
is a graph over the parameter (`HasStrictFDerivAt.implicitFunctionOfProdDomain`), which the
family `q_fix(y₀)` (`iso_poincareMap_qFix`) fills. -/
theorem iso_fixedPoints :
    ∃ V ∈ 𝓝 (iso_qFix (y₀ 1)), ∀ q ∈ V, iso_IsSectionPt q → iso_poincareMap^[4] q = q →
      ∃ y0 ∈ Ioo (1 / √3) 1, q = iso_qFix y0 := by
  sorry

/-! ### Step 7: the final transversality condition -/

/-- If `A ∈ SL₂(ℝ)` and `A⁴ = -I` then `(tr A)² = 2`: by Cayley–Hamilton `A⁴ + I =
(t² - 2)(tA - I)`, `t = tr A`; if `t² ≠ 2` then `tA = I` and `t² = t(a + d) = 2` anyway. -/
theorem iso_trace_sq_of_pow_four (A : Mat2) (hdet : A.det = 1) (h4 : A ^ 4 = -1) :
    A.trace ^ 2 = 2 := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hdet
  have h00 : (A ^ 4) 0 0 = -1 := by rw [h4]; simp
  have h11 : (A ^ 4) 1 1 = -1 := by rw [h4]; simp
  simp only [pow_succ, pow_zero, one_mul, Matrix.mul_apply, Fin.sum_univ_two] at h00 h11
  rw [Matrix.trace_fin_two]
  set a := A 0 0
  set b := A 0 1
  set c := A 1 0
  set d := A 1 1
  have e00 : ((a + d) ^ 2 - 2) * ((a + d) * a - 1) = 0 := by
    linear_combination h00 - (-3 * a ^ 2 - 3 * a * d - b * c - d ^ 2 + 1) * hd
  have e11 : ((a + d) ^ 2 - 2) * ((a + d) * d - 1) = 0 := by
    linear_combination h11 - (-a ^ 2 - 3 * a * d - b * c - 3 * d ^ 2 + 1) * hd
  by_contra hne
  have h2 : (a + d) ^ 2 - 2 ≠ 0 := sub_ne_zero.mpr hne
  have ha : (a + d) * a - 1 = 0 := (mul_eq_zero.mp e00).resolve_left h2
  have hd' : (a + d) * d - 1 = 0 := (mul_eq_zero.mp e11).resolve_left h2
  exact hne (by linear_combination ha + hd')

/-- The final transversality condition picks the octagon in the family: if the trajectory from
`q_fix(y₀)` with four switching intervals ends at `g(4 t_sw) = R`, then `y₀ = y_oct`
(`g(4t_sw) = h⁴R⁴` with `h = g_sw R⁻¹`, so `h⁴ = R⁻³ = -I`, `(tr h)² = 2`, `tr h = 4/(1 + 3y₀²)`;
the converse direction of Lemma 7.5.5 for `k = 1`). -/
theorem iso_y0_of_closing (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1)
    (h : polygonG y0 (switchTime y0) (4 * switchTime y0) = R) : y0 = y₀ 1 := by
  have hy : 0 < y0 := poly_y0_pos hy0
  have hτ := str_switchTime_pos y0 hy0 hy1
  set hh := segG y0 (switchTime y0) * R⁻¹ with hhdef
  -- `g(4 t_sw) = h⁴ R⁴ = -h⁴ R`
  have hfl : ⌊4 * switchTime y0 / switchTime y0⌋₊ = 4 := by
    rw [mul_div_cancel_right₀ _ hτ.ne']
    exact_mod_cast Nat.floor_natCast 4
  have hR4 : R ^ 4 = -R := by rw [pow_succ, poly_R_pow_three, neg_one_mul]
  rw [polygonG, hfl, show 4 * switchTime y0 - ((4 : ℕ) : ℝ) * switchTime y0 = 0 by push_cast; ring,
    str_segG_zero y0 hy, mul_one, hR4, ← hhdef] at h
  have h4 : hh ^ 4 = -1 := by
    have := congrArg (· * R⁻¹) h
    simp only [Matrix.mul_neg, Matrix.neg_mul, mul_assoc, poly_R_mul_inv, mul_one] at this
    rw [← neg_neg (hh ^ 4), this]
  have hdet : hh.det = 1 := by
    rw [hhdef, Matrix.det_mul, (seg_solution y0 0 hy).2.2.2.2 _, poly_det_Rinv, one_mul]
  have htr := iso_trace_sq_of_pow_four hh hdet h4
  rw [hhdef, trace_segG_switchTime y0 hy0] at htr
  -- `4/(1 + 3y₀²) = √2`, so `3y₀² = 2√2 - 1 = 3 y_oct²`
  have hpos : 0 < 4 / (1 + 3 * y0 ^ 2) := by positivity
  have hsq : 4 / (1 + 3 * y0 ^ 2) = √2 := by rw [← htr, Real.sqrt_sq hpos.le]
  have hs2 : √2 ^ 2 = 2 := poly_sqrt_two_sq
  have h3 : 3 * y0 ^ 2 = 3 * y₀ 1 ^ 2 := by
    rw [poly_three_y₀_one_sq, poly_sqrt8]
    rw [div_eq_iff (by positivity)] at hsq
    nlinarith
  have hy1' : 0 < y₀ 1 := poly_y0_pos (poly_y₀_mem le_rfl).1
  have hprod : (y0 - y₀ 1) * (y0 + y₀ 1) = 0 := by linear_combination h3 / 3
  rcases mul_eq_zero.mp hprod with h' | h'
  · linarith
  · linarith

/-! ### Assembly

`theorem7_7_1` follows: given an extremal as in the statement, rescale it (`iso_smul`), restart
it on the section near `q_oct` (`iso_section_crossing`, `iso_shift`), apply `iso_return` to get
`f⁴ q₀ = q₀` and the four arcs, `iso_fixedPoints` to get `q₀ = q_fix(y₀)`, `iso_arc_eq_vertexFlow`
and `iso_vertexFlow_qFix` to identify the arcs with the spline of `y₀`, and `iso_y0_of_closing` with
`g(T) = R` to get `y₀ = y_oct`; then `T = 4 t_sw = t_f`, and undoing the restart gives the shift
`s` (reduced mod `3 t_sw`, the period of `(X, Λ₁, Λ_R)`; `g` is unchanged by this reduction since
`R³ = -I`). -/

end SmoothedPolygons
