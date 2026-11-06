module

public import SmoothedPolygons.Ch7.DiscreteK
public import SmoothedPolygons.Ch7.StrongTransversality

/-!
# Theorem 7.7.1: definitions

The vocabulary of Theorem 7.7.1 (`SmoothedPolygons.Ch7.Isolated`) and all definitions of its
proof plan: the octagon's lift and its initial condition, the conic neighbourhood and the
time-shifted octagon (the statement); the twisted-periodic continuation of a control (step 0); the
closed-form extremal flow with a vertex control (step 1); the slope of `χ₃₂`, the state–costate
vector field (step 2); the Poincaré section, time and map, in matrices and in coordinates `ℝ⁹`
(steps 3–4); the tangent space of the section, its basis, the matrix of the derivative of the
Poincaré map and the coefficients of its characteristic polynomial (step 5). The plan and the
reading of the theorem are explained in `SmoothedPolygons.Ch7.Isolated`.
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

/-! ### The twisted-periodic continuation of a control (step 0) -/

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

/-- The point `q_fix(y₀) = (Φ(i y₀), Λ₁(0), Λ_R(0))` of the strong lift of Theorem 7.5.1
(`λ_cost = -1`). For `y₀ = y_oct` it is the octagon's normalized initial condition. -/
noncomputable def iso_qFix (y0 : ℝ) : iso_PhasePt := (Φ 0 y0, strongΛ₁ y0 0, strongΛR y0 0)

/-! ### Transversality of the switching times (step 2) -/

/-- The slope of `χ₃₂` at `t = 0` along the strong lift: `2√3 (4 - Y - Y ℓ)/(3y₀²)`,
`Y = 1 + 3y₀²`, `ℓ = ln(4/Y)`. -/
noncomputable def iso_chi32Slope (y0 : ℝ) : ℝ :=
  2 * √3 * (4 - (1 + 3 * y0 ^ 2) - (1 + 3 * y0 ^ 2) * ellSw y0) / (3 * y0 ^ 2)

/-- The vector field of the state–costate equations (`λ_cost = -1`) with control `u`:
`(X', Λ₁', Λ_R') = ([P, X], [Λ₁, X], eqn:lamR)`, `P = Z_u/⟨Z_u, X⟩`. -/
noncomputable def iso_extremalField (u : Fin 3 → ℝ) (q : iso_PhasePt) : iso_PhasePt :=
  (controlP u q.1 * q.1 - q.1 * controlP u q.1, q.2.1 * q.1 - q.1 * q.2.1,
    costateRHS (-1) q.2.1 q.2.2 q.1 u)

/-! ### The Poincaré section and map (steps 3–4) -/

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

/-! ### The direct calculation (step 5)

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

end SmoothedPolygons
