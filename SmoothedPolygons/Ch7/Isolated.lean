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
the theorem; the sketch is made into a sequence of lemmas, all proved, in the modules

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
   `iso_chi31_hasDerivAt`, `iso_edge_slope`). The remark after Lemma 7.5.3 states that `χ₃₂`
   vanishes at `0` with positive derivative; the derivative is computed here from eqn:f',
   `2√3(4 - Y - Y ln(4/Y))/(3y₀²) > 0`, `Y = 1 + 3y₀²`. By the symmetry
   `χ₃₁(t_sw - t) = χ₃₂(t)` of the proof of Lemma 7.5.3 (TeX 6220), `χ₃₁` vanishes at `t_sw` with
   the opposite slope. On the switching surface `χ₂₃ = 0` the derivative of `χ₃₂` along the
   state–costate vector field is the same for every control on the edge `[e₂, e₃]` of `U_T` (it
   is the Poisson bracket `{H₃, H₂}`), so near the octagon's switching points no singular arc and
   no chattering can occur.
3. *Same switching structure* (`iso_section_crossing`, `iso_return`). An extremal whose initial
   condition is near the octagon's and whose terminal time is near `t_f` is bang-bang with
   controls `e₃, e₁, e₂, e₃` (up to the shift), crosses the section `χ₂₃ = 0` near `t = 0` or near
   `t = 3t_sw` (near `t = T` it crosses the conjugate surface `χ₃₁ = 0` instead), and, restarted
   there, returns to its initial point after four applications of the Poincaré map `f` (eqn:fp).
   The proof (`SmoothedPolygons.Ch7.Isolated.Return`) shows that an extremal uses `e₃` for as long
   as the closed-form `e₃`-flow from its initial point has `χ₃₁, χ₃₂ > 0` (continuation with the
   maximum condition and `iso_arc_eq_vertexFlow`); the flow from points near `q_oct` inherits the
   strict inequalities of Lemma 7.5.3 and the transversal zeros of step 2 by joint continuity and
   compactness; and on the switching surface a first-order expansion of `χ₃₂` along the integral
   curve, with `iso_edge_slope`, shows that `χ₃₂` becomes positive at once (no singular arc, no
   chattering).
4. *The Poincaré map* (`iso_poincareTime`, `iso_poincareMap`, `iso_poincareMap_qFix`,
   `iso_poincareMapCoords_hasStrictFDerivAt`). `f(q) = Ad(R) q(t_sw(q), q)`, with `t_sw(q)` the
   first positive zero of `χ₃₁` along the `e₃`-flow; by step 2 and the implicit function theorem,
   near each `q_fix(y₀)` the time `t_sw(q)` is a function of `q` strictly differentiable at
   `q_fix(y₀)`, and so is `f` (`ipc_fderiv_structure`; at `q_oct`:
   `iso_poincareMapCoords_hasStrictFDerivAt`). Every `q_fix(y₀)`, `y₀ ∈ (1/√3, 1)`, is a fixed
   point (Theorem 7.5.1, Lemma 7.5.3).
5. *The direct calculation* (`iso_sectionMatrix`, `iso_sectionBasis`, `iso_fderiv_basis`,
   `iso_sectionMatrix_charpoly`, `iso_octagon_bounds`, `iso_sectionMatrix_octagon_hyperbolic`,
   `iso_hyperbolic`). On the tangent space of the four-dimensional section `N_{d_oct}` at
   `q_oct` the derivative of `f` has, in the basis `iso_sectionBasis`, the explicit matrix
   `iso_sectionMatrix (y₀²) ℓ`, `ℓ = ln(4/(3y₀² + 1))`, `y₀ = y_oct` (`iso_fderiv_basis`, proved
   at `y_oct` only; the closed form in `(y₀, ℓ)` comes from a symbolic computation for all `y₀`).
   Its characteristic polynomial is the reciprocal polynomial `z⁴ - e₁z³ + e₂z² - e₁z + 1`
   (`iso_sectionMatrix_charpoly`, an identity in `(u, ℓ)`): what one expects for a symplectic
   map, checked here directly (symplecticity of `f` is not proved). For the octagon
   (`Y = 2√2`, `ℓ = ln 2/2`) the multipliers are `-7.74641, -2.11221, -0.47344, -0.12909`; with
   `w = z + 1/z` the polynomial becomes `z² p(w)`, `p(w) = w² - e₁w + e₂ - 2`, and `p > 0` on
   `[-2, 2]` because `-e₁ > 4` and `p(-2) = 2 + 2e₁ + e₂ > 0`; these two inequalities reduce to
   `(4√2 + 1) ln 2 + 50 - 38√2 > 0` and `10 ln 2 + 52 - 42√2 < 0` (`iso_octagon_bounds`, proved).
   So no multiplier has modulus `1`: the fixed point is hyperbolic.
6. *The fixed points of `f⁴` near `q_oct`* (`iso_fixedPoints`). The book: "By the implicit
   function theorem, for each `d` near `d_oct`, the function `f_d⁴ - I` can be inverted in an open
   neighborhood of the fixed point `q_fix(d)`" (TeX 6616–6618), with `q_fix(d) = q_fix(y₀(d))` and
   `y₀(d)` the inverse of `y₀ ↦ d(y₀) = det Λ₁(q_fix(y₀))` (TeX 6581, Remark 7.5.2). Here the
   inverse function theorem is applied once, at `q_oct`, to
   `Ψ = (section constraints, f⁴ - id) : ℝ⁹ → ℝ⁵ × ℝ⁹`, whose constraints include `d = det Λ₁`:
   its derivative `w ↦ (Dc w, (A⁴ - I)w)` is injective, since `A⁴ - I` is invertible on
   `T N_{d_oct}` by step 5, so `Ψ` is injective near `q_oct`. By Remark 7.5.2 (`remark7_5_2`: `d`
   is strictly increasing with range `(0, 9/4)`), `y₀(d)` exists for `d` near `d_oct` and is near
   `y_oct`; a fixed point `q` of `f⁴` on the section near `q_oct` with `det Λ₁(q) = d` has the same
   image under `Ψ` as `q_fix(y₀(d))`, so `q = q_fix(y₀(d))` (departure from the paper: see the
   gaps below).
7. *Final transversality* (`iso_trace_sq_of_pow_four`, `iso_y0_of_closing`). For the extremal
   from `q_fix(y₀)` with four switching intervals, `g(t_f) = (g_sw R⁻¹)⁴ R⁴`, so `g(t_f) = R` means
   `(g_sw R⁻¹)⁴ = -I`, hence `(tr(g_sw R⁻¹))² = 2` by comparing eigenvalues as in the proof of
   Lemma 7.5.5 (an eigenvalue `λ` has `λ⁴ = -1`), `4/(1 + 3y₀²) = √2` and `y₀ = y_oct` (proved).
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
* The remark after Lemma 7.5.3 asserts only that the derivative of `χ₃₂` at `0` is positive (its
  value is computed in step 2 from eqn:f'); the Poincaré time needs the transversal zero of `χ₃₁`
  at `t_sw`, which follows by the symmetry `χ₃₁(t_sw - t) = χ₃₂(t)` of the proof of Lemma 7.5.3
  (TeX 6220).
* The proof defines the switching functions by `χ_ij = ⟨Λ_R, P_i - P_j⟩` (TeX 6573), the opposite
  sign of eqn:switch (TeX 6072–6078: `χ_ij = ⟨Λ_R, P_{i,j} - P_{i,i}⟩`, i.e. `⟨Λ_R, P_j - P_i⟩`),
  which the formalization uses (`switchingFn`). This is harmless: the proof only uses the zero
  set `χ_ij = 0` (the section `χ₂₃ = 0`, the switching times).
* "Direct calculation shows that the fixed point `q_oct` is hyperbolic" is not given; step 5
  supplies it, with the Jacobian in closed form.
* Departure from the paper (step 6): the book applies the implicit function theorem to
  `f_d⁴ − I` for each `d` separately, after asserting that `q_fix(d)` stays hyperbolic for nearby
  `d` (TeX 6615); the uniqueness "thus the only fixed points near `q_oct` are the `q_fix(d)`"
  needs neighbourhoods uniform in `d`, which this does not give. The formal proof applies the
  inverse function theorem once, at `q_oct`, to `(section constraints, f⁴ − id)`, whose
  constraints include `d`; this gives the uniformity, and the hyperbolicity of `q_fix(d)` for
  `d ≠ d_oct` is not needed. The parameter `y₀(d)` is obtained, as in the book, from Remark 7.5.2
  (monotonicity and range of `d(y₀)`, `remark7_5_2`).
* "The only fixed point `q_fix(d)` satisfying (eqn:theta-k) is `q_oct`" uses Lemma 7.5.5 in the
  converse direction (`g(t_f) = R` implies the trace condition); its proof (TeX 6303–6332)
  compares eigenvalues, which step 7 follows for `k = 1`.

## The direct calculation in closed form

With `u = y₀²`, `Y = 1 + 3u`, `ℓ = ln(4/Y)` and `D = Yℓ + Y - 4 < 0`, the coefficients of the
characteristic polynomial of `iso_sectionMatrix u ℓ` (the matrix of the section map at
`q_fix(y₀)` by the symbolic computation; proved to be that matrix at `y_oct` only) are
`e₁ = 8(ℓY(2Y - 3) + (Y - 4)(Y² - 3Y + 1))/(Y²D)` and
`e₂ = -2(ℓ(Y⁴ + 16Y³ - 72Y² + 64) + 9Y⁴ - 60Y³ + 40Y² + 304Y - 320)/(Y³D)`, with
`χ(-1) = 32(ℓ(3Y² - 4) + 4Y² - 21Y + 20)/(Y³D)`; for the octagon `e₁ ≈ -10.46115`,
`e₂ ≈ 22.36330`, `χ(-1) ≈ 3.44100`, `χ(1) ≈ 45.28561`. The slope of `χ₃₁` at `t_sw` is
`2√3 D/(3u) = -iso_chi32Slope y₀`. These were obtained by differentiating the closed-form flow
symbolically and are exact identities in `(y₀, ℓ)` (`ℓ` treated as an independent symbol); in
Lean, `e₁`, `e₂` are proved for `iso_sectionMatrix` for all `(u, ℓ)`
(`iso_sectionMatrix_charpoly`) and the slope of `χ₃₁` for all `y₀` (`iso_chi31_hasDerivAt`).

What is proved in this file: `theorem7_7_1` (the assembly) and `theorem7_7_1_octagon`
(non-vacuity). The assembly follows the plan (section *Assembly* below) and fills in two points
the plan leaves implicit: the group trajectory of the restarted extremal is the spline of `y₀` by
uniqueness for `g' = gX` (`ifp_g_unique`), and the control of the original extremal is recovered
almost everywhere from the maximum condition, since away from its switching times the octagon's
control is the unique maximizer of the Hamiltonian (Lemma 7.5.3, conjugated; `ifp_octagon_max`).
Undoing the restart uses the twisted periodicity of the octagon's lift (`ifp_unshift`,
`ifp_unshift_g`).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### Assembly helpers -/

/-- Shifting the argument of a piecewise curve by `n` switching intervals conjugates it. -/
lemma ifp_pw_add {A B : Mat2} {τ : ℝ} (hτ : 0 < τ) (f0 : ℝ → Mat2) {x : ℝ} (hx : 0 ≤ x)
    (n : ℕ) : poly_pw A B τ f0 (x + n * τ) = A ^ n * poly_pw A B τ f0 x * B ^ n := by
  have hfl : ⌊(x + n * τ) / τ⌋₊ = ⌊x / τ⌋₊ + n := by
    rw [add_div, mul_div_cancel_right₀ _ hτ.ne', Nat.floor_add_natCast (div_nonneg hx hτ.le)]
  have hsub : x + n * τ - ((⌊x / τ⌋₊ + n : ℕ) : ℝ) * τ = x - ⌊x / τ⌋₊ * τ := by
    push_cast; ring
  simp only [poly_pw, hfl, hsub]
  rw [show A ^ (⌊x / τ⌋₊ + n) = A ^ n * A ^ ⌊x / τ⌋₊ by rw [← pow_add, add_comm], pow_add]
  simp only [Matrix.mul_assoc]

/-- The octagon's state and costates have period `3τ` (`R³ = -I₂` is central). -/
lemma ifp_pw_three {τ : ℝ} (hτ : 0 < τ) (f0 : ℝ → Mat2) {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    poly_pw R⁻¹ R τ f0 (x + 3 * τ * k) = poly_pw R⁻¹ R τ f0 x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := ifp_pw_add (A := R⁻¹) (B := R) hτ f0 (x := x + 3 * τ * k) (by positivity) 3
    rw [show x + 3 * τ * k + ((3 : ℕ) : ℝ) * τ = x + 3 * τ * ((k + 1 : ℕ) : ℝ) by push_cast; ring,
      ih, poly_Rinv_pow_three, poly_R_pow_three] at h
    rw [h]
    simp

/-- After four switching intervals the octagon's state and costates are conjugated by `R`. -/
lemma ifp_pw_four {τ : ℝ} (hτ : 0 < τ) (f0 : ℝ → Mat2) {x : ℝ} (hx : 0 ≤ x) :
    poly_pw R⁻¹ R τ f0 (x + 4 * τ) = R⁻¹ * poly_pw R⁻¹ R τ f0 x * R := by
  have h := ifp_pw_add (A := R⁻¹) (B := R) hτ f0 hx (3 * 1 + 1)
  rw [poly_conj_pow_three_mul_add_one] at h
  rw [← h]
  norm_num

/-- The time `s_oct = 3τ⌈s/(3τ)⌉ - s ∈ [0, 3τ)` of the octagon that corresponds to time `0` of an
extremal restarted at `s` (`≡ -s` modulo the period `3τ`). -/
noncomputable def ifp_sOct (τ s : ℝ) : ℝ := 3 * τ * ⌈s / (3 * τ)⌉₊ - s

lemma ifp_sOct_mem {τ s : ℝ} (hτ : 0 < τ) (hs : 0 ≤ s) : ifp_sOct τ s ∈ Ico 0 (3 * τ) := by
  have h3 : 0 < 3 * τ := by positivity
  have h1 := Nat.le_ceil (s / (3 * τ))
  have h2 := Nat.ceil_lt_add_one (div_nonneg hs h3.le)
  have e : 3 * τ * (s / (3 * τ)) = s := by field_simp
  unfold ifp_sOct
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h1 h3.le]
  · nlinarith [mul_lt_mul_of_pos_left h2 h3]

/-- Undoing a restart, for the state and the costates: if the twisted-periodic continuation of
`F` (on `[0, T]`, `T = 4τ`, `F(T) = R⁻¹F(0)R`) started at `s` is the octagon's curve
`O = poly_pw R⁻¹ R τ f₀`, then `F` is `O` started at `s_oct`. -/
lemma ifp_unshift {τ T s : ℝ} (hτ : 0 < τ) (hT : T = 4 * τ) (hs : s ∈ Ico 0 T)
    {F f0 : ℝ → Mat2} (hF : F T = R⁻¹ * F 0 * R)
    (h : ∀ t ∈ Icc 0 T, poly_pw R⁻¹ R T F (s + t) = poly_pw R⁻¹ R τ f0 t) :
    ∀ t ∈ Icc 0 T, F t = poly_pw R⁻¹ R τ f0 (ifp_sOct τ s + t) := by
  have hTpos : 0 < T := by rw [hT]; positivity
  have hE1 : ∀ x ∈ Icc 0 T, poly_pw R⁻¹ R T F x = F x := fun x hx ↦ by
    have := poly_pw_of_mem_Icc (A := R⁻¹) (B := R) hTpos hF (i := 0) (t := x) (by simpa using hx)
    simpa using this
  have hE2 : ∀ x, 0 ≤ x → poly_pw R⁻¹ R T F (x + T) = R⁻¹ * poly_pw R⁻¹ R T F x * R :=
    fun x hx ↦ by simpa using ifp_pw_add (A := R⁻¹) (B := R) hTpos F hx 1
  have h2 : ∀ t ∈ Icc 0 (2 * T), poly_pw R⁻¹ R T F (s + t) = poly_pw R⁻¹ R τ f0 t := by
    intro t ht
    rcases le_or_gt t T with htT | htT
    · exact h t ⟨ht.1, htT⟩
    · have h' := h (t - T) ⟨by linarith, by linarith [ht.2]⟩
      have hO := ifp_pw_four hτ f0 (x := t - T) (by linarith)
      rw [show t - T + 4 * τ = t by rw [hT]; ring] at hO
      rw [show s + t = (s + (t - T)) + T by ring, hE2 _ (by linarith [hs.1]), h', hO]
  intro t ht
  obtain ⟨hso0, -⟩ := ifp_sOct_mem hτ hs.1
  have key : F t = R * poly_pw R⁻¹ R T F (t + T) * R⁻¹ := by
    rw [hE2 t ht.1, hE1 t ht]
    simp only [← Matrix.mul_assoc, poly_R_mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, poly_R_mul_inv, Matrix.mul_one]
  rw [key, show t + T = s + (t + T - s) by ring,
    h2 _ ⟨by linarith [hs.2, ht.1], by linarith [hs.1, ht.2]⟩,
    ← ifp_pw_three hτ f0 (by linarith [hs.2, ht.1] : 0 ≤ t + T - s) ⌈s / (3 * τ)⌉₊,
    show t + T - s + 3 * τ * ⌈s / (3 * τ)⌉₊ = (ifp_sOct τ s + t) + 4 * τ by
      unfold ifp_sOct; rw [hT]; ring,
    ifp_pw_four hτ f0 (by linarith [ht.1])]
  simp only [← Matrix.mul_assoc, poly_R_mul_inv, Matrix.one_mul]
  rw [Matrix.mul_assoc, poly_R_mul_inv, Matrix.mul_one]

/-- Undoing a restart, for the group trajectory. `G` is twisted periodic: `G(x + 3τ) = C G(x)`
with `C` invertible and `G(x + T) = G(x) R`. -/
lemma ifp_unshift_g {τ T s : ℝ} (hτ : 0 < τ) (hT : T = 4 * τ) (hs : s ∈ Ico 0 T)
    {g G : ℝ → Mat2} (hg0 : g 0 = 1) (hgT : g T = R) (hgdet : ∀ t ∈ Icc 0 T, (g t).det = 1)
    (hGdet : ∀ x, 0 ≤ x → (G x).det = 1) {C : Mat2} (hC : IsUnit C.det)
    (hG3 : ∀ x, 0 ≤ x → G (x + 3 * τ) = C * G x) (hG4 : ∀ x, 0 ≤ x → G (x + T) = G x * R)
    (h : ∀ t ∈ Icc 0 T, (poly_pw 1 R T g s)⁻¹ * poly_pw 1 R T g (s + t) = G t) :
    ∀ t ∈ Icc 0 T, g t = (G (ifp_sOct τ s))⁻¹ * G (ifp_sOct τ s + t) := by
  have hTpos : 0 < T := by rw [hT]; positivity
  have hglue : g T = 1 * g 0 * R := by rw [hg0, hgT]; simp
  have hE1 : ∀ x ∈ Icc 0 T, poly_pw 1 R T g x = g x := fun x hx ↦ by
    have := poly_pw_of_mem_Icc (A := 1) (B := R) hTpos hglue (i := 0) (t := x) (by simpa using hx)
    simpa using this
  have hE2 : ∀ x, 0 ≤ x → poly_pw 1 R T g (x + T) = poly_pw 1 R T g x * R :=
    fun x hx ↦ by simpa using ifp_pw_add (A := 1) (B := R) hTpos g hx 1
  have hunit : ∀ M : Mat2, M.det = 1 → IsUnit M.det := fun M hM ↦ by rw [hM]; exact isUnit_one
  have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
  have ha : IsUnit (g s).det := hunit _ (hgdet s hs')
  have h1 : ∀ t ∈ Icc 0 T, poly_pw 1 R T g (s + t) = g s * G t := fun t ht ↦ by
    rw [← h t ht, hE1 s hs', ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]
  have h2 : ∀ t ∈ Icc 0 (2 * T), poly_pw 1 R T g (s + t) = g s * G t := by
    intro t ht
    rcases le_or_gt t T with htT | htT
    · exact h1 t ⟨ht.1, htT⟩
    · rw [show s + t = (s + (t - T)) + T by ring, hE2 _ (by linarith [hs.1]),
        h1 _ ⟨by linarith, by linarith [ht.2]⟩, Matrix.mul_assoc, ← hG4 _ (by linarith)]
      congr 2
      ring
  -- `G` modulo the period `3τ`
  have hGk : ∀ k : ℕ, ∃ Ck : Mat2, IsUnit Ck.det ∧
      ∀ x, 0 ≤ x → G (x + 3 * τ * k) = Ck * G x := by
    intro k
    induction k with
    | zero => exact ⟨1, by simp, fun x _ ↦ by simp⟩
    | succ k ih =>
      obtain ⟨Ck, hCk, hk⟩ := ih
      refine ⟨C * Ck, by rw [Matrix.det_mul]; exact hC.mul hCk, fun x hx ↦ ?_⟩
      rw [show x + 3 * τ * ((k + 1 : ℕ) : ℝ) = (x + 3 * τ * k) + 3 * τ by push_cast; ring,
        hG3 _ (by positivity), hk x hx, Matrix.mul_assoc]
  obtain ⟨Ck, hCk, hk⟩ := hGk ⌈s / (3 * τ)⌉₊
  have hquot : ∀ x y, 0 ≤ x → 0 ≤ y →
      (G (x + 3 * τ * ⌈s / (3 * τ)⌉₊))⁻¹ * G (y + 3 * τ * ⌈s / (3 * τ)⌉₊) = (G x)⁻¹ * G y := by
    intro x y hx hy
    rw [hk x hx, hk y hy, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc Ck⁻¹,
      Matrix.nonsing_inv_mul _ hCk, Matrix.one_mul]
  obtain ⟨hso0, -⟩ := ifp_sOct_mem hτ hs.1
  have hshift : ∀ x, 0 ≤ x → x + 3 * τ * ⌈s / (3 * τ)⌉₊ - s = x - s + 3 * τ * ⌈s / (3 * τ)⌉₊ :=
    fun x _ ↦ by ring
  -- `g(t) = g(s) G(t + T - s) R⁻¹`
  have hgt : ∀ t ∈ Icc 0 T, g t = g s * G (t + T - s) * R⁻¹ := by
    intro t ht
    have := h2 (t + T - s) ⟨by linarith [hs.2, ht.1], by linarith [hs.1, ht.2]⟩
    rw [show s + (t + T - s) = t + T by ring, hE2 t ht.1, hE1 t ht] at this
    rw [← this, Matrix.mul_assoc, poly_R_mul_inv, Matrix.mul_one]
  have hT0 : T - s = 0 + T - s := by ring
  have hG0 := hgt 0 ⟨le_rfl, hTpos.le⟩
  rw [hg0, ← hT0] at hG0
  -- so `g(s) = R G(T - s)⁻¹`
  have hGTs : IsUnit (G (T - s)).det := hunit _ (hGdet _ (by linarith [hs.2]))
  have hgs : g s = R * (G (T - s))⁻¹ := by
    have := congrArg (· * (R * (G (T - s))⁻¹)) hG0
    simp only [Matrix.one_mul] at this
    rw [this, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc R⁻¹, poly_inv_mul_R,
      Matrix.one_mul, Matrix.mul_nonsing_inv _ hGTs, Matrix.mul_one]
  intro t ht
  rw [hgt t ht, hgs]
  have hq := hquot (T - s) (t + T - s) (by linarith [hs.2]) (by linarith [hs.2, ht.1])
  have e1 : T - s + 3 * τ * ⌈s / (3 * τ)⌉₊ = ifp_sOct τ s + T := by unfold ifp_sOct; ring
  have e2 : t + T - s + 3 * τ * ⌈s / (3 * τ)⌉₊ = (ifp_sOct τ s + t) + T := by
    unfold ifp_sOct; ring
  rw [e1, e2, hG4 _ hso0, hG4 _ (by linarith [ht.1]), Matrix.mul_inv_rev] at hq
  rw [Matrix.mul_assoc R, ← hq]
  simp only [← Matrix.mul_assoc, poly_R_mul_inv, Matrix.one_mul]
  rw [Matrix.mul_assoc _ R, poly_R_mul_inv, Matrix.mul_one]

/-- The group trajectory is determined by the state trajectory: if `g' = gX` with `g(0) = I₂` and
`X` is the spline of `y₀` on `[0, Nτ]`, then `g` is the spline's group trajectory there. -/
lemma ifp_g_unique {y0 : ℝ} (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) {N : ℕ} (hN : 1 ≤ N)
    {g X : ℝ → Mat2} (hgI : IsIntegralCurve g (fun t ↦ g t * X t) (N * switchTime y0))
    (hg0 : g 0 = 1) (hX : ∀ t ∈ Icc 0 (N * switchTime y0), X t = polygonX y0 (switchTime y0) t) :
    ∀ t ∈ Icc 0 (N * switchTime y0), g t = polygonG y0 (switchTime y0) t := by
  set τ := switchTime y0 with hτdef
  have hτ : 0 < τ := poly_switchTime_pos hy0 hy1
  obtain ⟨⟨-, -, -, -, hGI, -⟩, hG0, -⟩ := poly_isStateTrajectory y0 hy0 hy1 N hN
  have hXc : ContinuousOn (polygonX y0 τ) (Icc 0 (N * τ)) :=
    poly_pw_continuousOn hτ (poly_segX_glue hy0)
      (poly_segX_continuous (poly_y0_pos hy0)).continuousOn N
  have hgc : ContinuousOn g (Icc 0 (N * τ)) := Matrix.continuousOn_of_eq_add_integral hgI
  have hGc : ContinuousOn (polygonG y0 τ) (Icc 0 (N * τ)) :=
    Matrix.continuousOn_of_eq_add_integral hGI
  have hgX : ContinuousOn (fun t ↦ g t * X t) (Icc 0 (N * τ)) :=
    (hgc.mul hXc).congr fun t ht ↦ by simp only [hX t ht, Pi.mul_apply]
  refine fun t ht ↦ Matrix.ODE_solution_unique_mul_right hXc hgc (fun s hs ↦ ?_) hGc
    (fun s hs ↦ ?_) (by rw [hg0, hG0]) ht
  · have := Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hgI (Ico_subset_Icc_self hs)
      (hgX s (Ico_subset_Icc_self hs))
    rwa [hX s (Ico_subset_Icc_self hs)] at this
  · exact Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hGI (Ico_subset_Icc_self hs)
      ((hGc.mul hXc) s (Ico_subset_Icc_self hs))

/-- The Hamiltonian is homogeneous of degree one in the costate `(Λ₁, Λ_R, λ_cost)`. -/
lemma ifp_hamiltonian_smul (c lam : ℝ) (Λ₁ ΛR X : Mat2) (v : Fin 3 → ℝ) :
    hamiltonian (c * lam) (c • Λ₁) (c • ΛR) X v = c * hamiltonian lam Λ₁ ΛR X v := by
  have hJ : (3 / 2 * (c * lam)) • J = c • ((3 / 2 * lam) • J) := by rw [smul_smul]; ring_nf
  have htf : ∀ A B : Mat2, traceForm (c • A) B = c * traceForm A B := fun A B ↦ by
    simp [traceForm, Matrix.trace_smul]
  simp only [hamiltonian, hJ, ← smul_sub, htf]
  ring

/-- Away from its switching times, the smoothed octagon's control is the only maximizer of the
Hamiltonian along its lift (Lemma 7.5.3 gives the strict inequalities, conjugated to the `i`-th
switching interval). -/
lemma ifp_octagon_max {x : ℝ} (hx : 0 ≤ x) (hxn : ∀ n : ℕ, x ≠ n * tsw 1)
    {w : Fin 3 → ℝ} (hw : w ∈ controlSimplex)
    (hmax : ∀ v ∈ controlSimplex,
      hamiltonian (-1) (octΛ₁ x) (octΛR x) (polygonX (y₀ 1) (tsw 1) x) v ≤
        hamiltonian (-1) (octΛ₁ x) (octΛR x) (polygonX (y₀ 1) (tsw 1) x) w) :
    w = polygonControl 1 x := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  set y := y₀ 1
  set τ := tsw 1 with hτdef
  have hτ : 0 < τ := poly_switchTime_pos hy0 hy1
  obtain ⟨hf1, hf2⟩ := poly_floor_mem hτ hx
  set i := ⌊x / τ⌋₊ with hi
  have hx' : x - i * τ ∈ Ioo 0 τ := ⟨by
    have := hxn i; exact sub_pos.2 (lt_of_le_of_ne hf1 (Ne.symm this)), by linarith⟩
  have hxI : x ∈ Ico ((i : ℝ) * τ) ((i + 1) * τ) := ⟨hf1, hf2⟩
  have hX : polygonX y τ x = R⁻¹ ^ i * segX y (x - i * τ) * R ^ i := by
    rw [poly_polygonX_eq, poly_pw_of_mem_Ico hτ hxI]
  have h1 : octΛ₁ x = R⁻¹ ^ i * strongΛ₁ y (x - i * τ) * R ^ i := by
    rw [octΛ₁, poly_pw_of_mem_Ico hτ hxI]
  have hR : octΛR x = R⁻¹ ^ i * strongΛR y (x - i * τ) * R ^ i := by
    rw [octΛR, poly_pw_of_mem_Ico hτ hxI]
  have hctrl : polygonControl 1 x = vertex (poly_idx i) := rfl
  rw [hX, h1, hR] at hmax
  rw [hctrl]
  have hs : x - i * τ ∈ Icc 0 (switchTime y) := Ioo_subset_Icc_self hx'
  refine irt_eq_vertex_of_max (poly_isStarState_conj_pow i (segX_star y hy0 hy1 _ hs))
    (fun j hj ↦ ?_) hw (hmax _ (poly_vertex_mem _))
  set m : Fin 3 := ⟨(j.val + 2 * i) % 3, Nat.mod_lt _ (by norm_num)⟩ with hmdef
  have hm : (⟨(m.val + i) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = j := by
    ext; simp only [hmdef]; omega
  have hm2 : m ≠ 2 := by
    intro h; apply hj; rw [← hm, h]; rfl
  rw [← hm, poly_hamiltonian_conj (poly_Rpow_mul_Rinvpow i) (poly_conj_pow_J i)
    (poly_conj_pow_vertex i _), poly_hamiltonian_conj (poly_Rpow_mul_Rinvpow i)
    (poly_conj_pow_J i) (poly_conj_pow_vertex_two i)]
  have hχ := lemma7_5_3 y hy0 hy1 _ _ (strongLift_isStrongLift y hy0) _ hs
  have hsub := poly_hamiltonian_sub (-1) (strongΛ₁ y (x - i * τ)) (strongΛR y (x - i * τ))
    (segX y (x - i * τ)) 2 m
  have hpos : 0 < switchingFn 2 m (strongΛR y (x - i * τ)) (segX y (x - i * τ)) := by
    have hlt := m.isLt
    have hne : m.val ≠ 2 := fun h ↦ hm2 (Fin.ext h)
    rcases (by omega : m.val = 0 ∨ m.val = 1) with h | h
    · rw [show m = 0 from Fin.ext h]
      exact lt_of_le_of_ne hχ.1 fun h ↦ hx'.2.ne (hχ.2.2.1 h.symm)
    · rw [show m = 1 from Fin.ext h]
      exact lt_of_le_of_ne hχ.2.1 fun h ↦ hx'.1.ne' (hχ.2.2.2 h.symm)
  linarith

/-- The normalization `(X₀, Λ₁, Λ_R, λ) ↦ (X₀, Λ₁/(-λ), Λ_R/(-λ))` of an initial condition in the
cotangent space to `λ_cost = -1`. -/
noncomputable def ifp_normalize (p : Mat2 × Mat2 × Mat2 × ℝ) : iso_PhasePt :=
  (p.1, (-p.2.2.2)⁻¹ • p.2.1, (-p.2.2.2)⁻¹ • p.2.2.1)

lemma ifp_normalize_oct : ifp_normalize octInitialCondition = iso_qFix (y₀ 1) := by
  simp [ifp_normalize, octInitialCondition, iso_qFix]

lemma ifp_normalize_continuousAt : ContinuousAt ifp_normalize octInitialCondition := by
  unfold ifp_normalize
  have h : (-octInitialCondition.2.2.2) ≠ 0 := by simp [octInitialCondition]
  fun_prop (disch := exact h)

lemma ifp_iterate_qFix {y0 : ℝ} (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (i : ℕ) :
    iso_poincareMap^[i] (iso_qFix y0) = iso_qFix y0 :=
  Function.iterate_fixed (iso_poincareMap_qFix y0 hy0 hy1) i

lemma ifp_switchTimes_qFix {y0 : ℝ} (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (i : ℕ) :
    iso_poincareSwitchTimes (iso_qFix y0) i = i * switchTime y0 := by
  simp [iso_poincareSwitchTimes, ifp_iterate_qFix hy0 hy1, iso_poincareTime_qFix y0 hy0 hy1]

/-- The group trajectory of a spline has determinant one. -/
lemma ifp_det_polygonG {y0 : ℝ} (hy : 0 < y0) (τ x : ℝ) : (polygonG y0 τ x).det = 1 := by
  simp only [polygonG, Matrix.det_mul, Matrix.det_pow, (seg_solution y0 0 hy).2.2.2.2,
    poly_det_Rinv, poly_det_R, one_pow, mul_one]

/-- Over three switching intervals the spline's group trajectory is multiplied on the left by
`-(g_sw R⁻¹)³`. -/
lemma ifp_polygonG_three {y0 : ℝ} (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) {x : ℝ} (hx : 0 ≤ x) :
    polygonG y0 (switchTime y0) (x + 3 * switchTime y0) =
      -(segG y0 (switchTime y0) * R⁻¹) ^ 3 * polygonG y0 (switchTime y0) x := by
  have h := ifp_pw_add (A := segG y0 (switchTime y0) * R⁻¹) (B := R)
    (poly_switchTime_pos hy0 hy1) (segG y0) hx 3
  rw [← poly_polygonG_eq] at h
  rw [show (3 : ℝ) * switchTime y0 = ((3 : ℕ) : ℝ) * switchTime y0 by norm_num, h,
    poly_R_pow_three]
  simp

/-- If the spline closes up after four switching intervals (`g(4t_sw) = R`), its group
trajectory satisfies `g(x + 4t_sw) = g(x)R`. -/
lemma ifp_polygonG_four {y0 : ℝ} (hy0 : 1 / √3 < y0) (hy1 : y0 < 1)
    (hclose : polygonG y0 (switchTime y0) (4 * switchTime y0) = R) {x : ℝ} (hx : 0 ≤ x) :
    polygonG y0 (switchTime y0) (x + 4 * switchTime y0) = polygonG y0 (switchTime y0) x * R := by
  have hτ := poly_switchTime_pos hy0 hy1
  set H := segG y0 (switchTime y0) * R⁻¹
  have h4 : ∀ z, 0 ≤ z → polygonG y0 (switchTime y0) (z + 4 * switchTime y0) =
      H ^ 4 * polygonG y0 (switchTime y0) z * R ^ 4 := fun z hz ↦ by
    have h := ifp_pw_add (A := H) (B := R) hτ (segG y0) hz 4
    rw [← poly_polygonG_eq] at h
    rw [← h]; norm_num
  have hR4 : R ^ 4 = -R := by rw [pow_succ, poly_R_pow_three, neg_one_mul]
  have h0 : polygonG y0 (switchTime y0) 0 = 1 := by
    simp [polygonG, (seg_solution y0 0 (poly_y0_pos hy0)).2.2.1]
  have hH4 : H ^ 4 = -1 := by
    have := h4 0 le_rfl
    rw [zero_add, hclose, h0, Matrix.mul_one, hR4] at this
    have h' := congrArg (· * R⁻¹) this
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, poly_R_mul_inv,
      Matrix.mul_one] at h'
    rw [h', neg_neg]
  rw [h4 x hx, hH4, hR4]
  simp

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
  obtain ⟨Vr, hVr, εr, hεr, hret⟩ := iso_return
  obtain ⟨Vf, hVf, hfix⟩ := iso_fixedPoints
  obtain ⟨Us, hUs, εs, hεs, hsc⟩ := iso_section_crossing (Vr ∩ Vf) (inter_mem hVr hVf)
  have hU1 : ifp_normalize ⁻¹' Us ∈ 𝓝 octInitialCondition :=
    ifp_normalize_continuousAt.preimage_mem_nhds (by rwa [ifp_normalize_oct])
  have hU2 : {p : Mat2 × Mat2 × Mat2 × ℝ | p.2.2.2 < 0} ∈ 𝓝 octInitialCondition :=
    (isOpen_lt continuous_snd.snd.snd continuous_const).mem_nhds (by simp [octInitialCondition])
  refine ⟨ifp_normalize ⁻¹' Us ∩ {p | p.2.2.2 < 0}, inter_mem hU1 hU2, min εr εs,
    lt_min hεr hεs, ?_⟩
  intro T u g X Λ₁ ΛR lam hext hT ⟨c, hc, hmemU, hneg⟩
  -- Step 0: normalize the costate (`λ_cost = -1`)
  have hlam : lam < 0 := by
    have h : c * lam < 0 := hneg
    by_contra h'
    exact (mul_nonneg hc.le (not_lt.1 h')).not_gt h
  set κ := (-lam)⁻¹ with hκ
  have hκpos : 0 < κ := inv_pos.2 (neg_pos.2 hlam)
  have hκlam : κ * lam = -1 := by rw [hκ, inv_mul_eq_div, div_neg, div_self hlam.ne]
  have hext1 := iso_smul hext hκpos
  rw [hκlam] at hext1
  have hmem1 : (X 0, κ • Λ₁ 0, κ • ΛR 0) ∈ Us := by
    have e : ∀ M : Mat2, (-(c * lam))⁻¹ • c • M = κ • M := fun M ↦ by
      rw [smul_smul, hκ]; congr 1; field_simp
    have h := hmemU
    simp only [mem_preimage, ifp_normalize, e] at h
    exact h
  -- Step 3: restart on the section and return after four turns
  obtain ⟨s, hs, hsV, hsSec⟩ := hsc T u g X (fun t ↦ κ • Λ₁ t) (fun t ↦ κ • ΛR t) hext1
    (lt_of_lt_of_le hT (min_le_right _ _)) hmem1
  have hshift := iso_shift hext1 hs.1
  set X' : ℝ → Mat2 := fun t ↦ poly_pw R⁻¹ R T X (s + t) with hX'
  set L1' : ℝ → Mat2 := fun t ↦ poly_pw R⁻¹ R T (fun t ↦ κ • Λ₁ t) (s + t) with hL1'
  set LR' : ℝ → Mat2 := fun t ↦ poly_pw R⁻¹ R T (fun t ↦ κ • ΛR t) (s + t) with hLR'
  set g' : ℝ → Mat2 := fun t ↦ (poly_pw 1 R T g s)⁻¹ * poly_pw 1 R T g (s + t) with hg'
  have hq0 : (X' 0, L1' 0, LR' 0) = (poly_pw R⁻¹ R T X s,
      poly_pw R⁻¹ R T (fun t ↦ κ • Λ₁ t) s, poly_pw R⁻¹ R T (fun t ↦ κ • ΛR t) s) := by
    simp only [hX', hL1', hLR', add_zero]
  rw [← hq0] at hsV hsSec
  obtain ⟨hf4, hTsum, harc⟩ := hret T _ g' X' L1' LR' hshift
    (lt_of_lt_of_le hT (min_le_left _ _)) hsV.1 hsSec
  -- Step 6: the fixed point is some `q_fix(y₀)`
  obtain ⟨y0, ⟨hy0, hy1⟩, hq⟩ := hfix _ hsV.2 hsSec hf4
  rw [hq] at hTsum harc
  set τ := switchTime y0 with hτdef
  have hτ : 0 < τ := poly_switchTime_pos hy0 hy1
  have hy : 0 < y0 := poly_y0_pos hy0
  simp only [ifp_switchTimes_qFix hy0 hy1, ifp_iterate_qFix hy0 hy1,
    iso_vertexFlow_qFix y0 hy0] at hTsum harc
  rw [← hτdef] at hTsum harc
  have hT4 : T = 4 * τ := by rw [hTsum]; norm_num
  have hT4' : ((4 : ℕ) : ℝ) * switchTime y0 = T := by rw [hT4, hτdef]; norm_num
  -- Step 1: the restarted extremal is the spline of `y₀` with the strong lift
  obtain ⟨-, -, -, -, -, -, -, hgR, hg1⟩ := strongLift_isStrongLift y0 hy0
  have hpiece : ∀ t ∈ Icc 0 T, X' t = polygonX y0 τ t ∧
      L1' t = poly_pw R⁻¹ R τ (strongΛ₁ y0) t ∧ L1' t = L1' t ∧
      LR' t = poly_pw R⁻¹ R τ (strongΛR y0) t := by
    intro t ht
    rw [← hT4'] at ht
    obtain ⟨i, hi, hti⟩ := poly_exists_piece hτ (by norm_num) ht
    have h := harc i hi t (by push_cast; exact hti)
    simp only [iso_adRinvPow, Prod.mk.injEq] at h
    obtain ⟨hX, h1, hR⟩ := h
    refine ⟨?_, ?_, rfl, ?_⟩
    · rw [hX, poly_Xp_eq hy0 hy1 rfl hti, poly_Xp]
    · rw [h1, poly_pw_of_mem_Icc hτ hg1 hti]
    · rw [hR, poly_pw_of_mem_Icc hτ hgR hti]
  -- the group trajectory, and Step 7: `g(t_f) = R` forces `y₀ = y_oct`
  obtain ⟨⟨-, -, -, -, hgI, -⟩, hg0', hgT', -⟩ := hshift
  have hgG : ∀ t ∈ Icc 0 T, g' t = polygonG y0 τ t := by
    rw [← hT4'] at hgI ⊢
    exact ifp_g_unique hy0 hy1 (by norm_num) hgI hg0' fun t ht ↦ (hpiece t (hT4' ▸ ht)).1
  have hTpos : 0 ≤ T := by rw [hT4]; positivity
  have hclose : polygonG y0 τ (4 * τ) = R := by
    rw [← hT4, ← hgG T ⟨hTpos, le_rfl⟩]
    exact hgT'
  have hyoct := iso_y0_of_closing y0 hy0 hy1 hclose
  subst hyoct
  have hτoct : τ = tsw 1 := by rw [hτdef, tsw_eq_switchTime]
  obtain ⟨hso0, -⟩ := ifp_sOct_mem hτ hs.1
  have hlift : ∀ t ∈ Icc 0 T, X t = polygonX (y₀ 1) τ (ifp_sOct τ s + t) ∧
      g t = (polygonG (y₀ 1) τ (ifp_sOct τ s))⁻¹ * polygonG (y₀ 1) τ (ifp_sOct τ s + t) ∧
      Λ₁ t = (-lam) • octΛ₁ (ifp_sOct τ s + t) ∧ ΛR t = (-lam) • octΛR (ifp_sOct τ s + t) := by
    intro t ht
    obtain ⟨hext0, hextg0, hextgT, hextXT, -, -, -, -, -, -, -⟩ := hext
    obtain ⟨-, -, -, -, h1T, hRT, -, -, -, -, -⟩ := hext1
    refine ⟨ifp_unshift hτ hT4 hs hextXT (fun t ht ↦ (hpiece t ht).1) t ht, ?_, ?_, ?_⟩
    · refine ifp_unshift_g hτ hT4 hs hextg0 hextgT (fun t ht ↦ (hext0.2.2.2.1 t ht).1)
        (fun x _ ↦ ifp_det_polygonG (poly_y0_pos hy0) τ x) ?_
        (fun x hx ↦ ifp_polygonG_three hy0 hy1 hx) (fun x hx ↦ ?_) hgG t ht
      · rw [Matrix.det_neg, Matrix.det_pow, Matrix.det_mul, (seg_solution _ 0 hy).2.2.2.2,
          poly_det_Rinv]
        norm_num
      · rw [hT4]; exact ifp_polygonG_four hy0 hy1 hclose hx
    · have h := ifp_unshift hτ hT4 hs h1T (fun t ht ↦ (hpiece t ht).2.1) t ht
      rw [octΛ₁, ← hτoct, ← h, smul_smul, hκ, mul_inv_cancel₀ (neg_pos.2 hlam).ne', one_smul]
    · have h := ifp_unshift hτ hT4 hs hRT (fun t ht ↦ (hpiece t ht).2.2.2) t ht
      rw [octΛR, ← hτoct, ← h, smul_smul, hκ, mul_inv_cancel₀ (neg_pos.2 hlam).ne', one_smul]
  refine ⟨by rw [hT4, tf, hτoct]; norm_num, hlam, ifp_sOct τ s, ifp_sOct_mem hτ hs.1,
    fun t ht ↦ hlift t ht, ?_⟩
  -- the control, from the maximum condition (Lemma 7.5.3 away from the switching times)
  obtain ⟨hst, -, -, -, -, -, -, -, -, -, hmax⟩ := hext
  filter_upwards [hmax, (countable_range fun n : ℕ ↦ n * τ - ifp_sOct τ s).ae_notMem volume]
    with t hmt hS ht
  have htI : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  obtain ⟨hXt, -, h1t, hRt⟩ := hlift t htI
  obtain ⟨-, hle⟩ := hmt ht
  have e : ∀ (A B Y : Mat2) (v : Fin 3 → ℝ), hamiltonian lam ((-lam) • A) ((-lam) • B) Y v =
      (-lam) * hamiltonian (-1) A B Y v := fun A B Y v ↦ by
    rw [← ifp_hamiltonian_smul]; congr 1; ring
  refine ifp_octagon_max (by linarith [ht.1]) (fun n hn ↦ hS ⟨n, by
    change (n : ℝ) * τ - ifp_sOct τ s = t; rw [← hτoct] at hn; linarith⟩)
    (hst.2.2.1 t htI) fun v hv ↦ ?_
  have h := hle v hv
  rw [hXt, h1t, hRt, e, e] at h
  exact le_of_mul_le_mul_left h (neg_pos.2 hlam)

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
