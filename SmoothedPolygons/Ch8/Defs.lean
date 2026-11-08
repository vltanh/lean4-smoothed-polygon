module

public import SmoothedPolygons.Ch6.PeriodicExtension
public import External.Pontryagin

/-!
# Chapter 8: definitions

The objects of Chapter 8 (Singular Locus, TeX 6631–7674) and the vocabulary its statements share:

* extremal lifted trajectories on a time interval `[a, b]` (`IsExtremalOn`): Chapter 8 works with
  "an extremal lifted trajectory on `[t₁, t₂]`" (Theorems 8.3.1, 8.3.2), the state–costate system
  of Problem 6.7.1 with the conditions of the maximum principle (§6.2) and no boundary
  conditions; `IsPontryaginExtremal` is such a trajectory on `[0, T]` with the transversality
  conditions (6.6.1), and restricts to every subinterval
  (`IsPontryaginExtremal.isExtremalOn`);
* the edge control problem (Definition 8.1.1): its state `(x, y, s)`, control `u_e ∈ [-½, ½]`,
  dynamics (8.1.3), state space and cost (8.1.5), and its extremals (`IsEdgeProblemExtremal`), the
  lifted trajectories satisfying the conclusions of the maximum principle (§6.2: Hamilton's
  equations, the maximum condition, `H ≡ 0` for the free terminal time, `(λ_cost, λ) ≠ 0`,
  `λ_cost ≤ 0` constant), with the objects of `External.pontryagin_maximum_principle`;
* the edge coordinates of a Reinhardt trajectory whose control lies in an edge of `U_T`
  (TeX 6678–6730, "by rotational symmetry" for the other edges, TeX 6774–6775), and edge
  extremals (Definition 8.1.2, `IsEdgeExtremalOn`);
* the faces of `U_T` maximizing the Hamiltonian (§7.3, `hamiltonianArgmax`; the regions
  `(T*O_J)_I`), the edges of `U_T` (`controlEdge`);
* the singular locus (Definition 8.2.4, `singularLocus`);
* bang-bang controls with finitely many switches (`IsFiniteBangBang`; Definition 7.3.2 with the
  finiteness of Theorems 8.1.4, 8.3.2 and 16.3.1).

Conventions. Controls `u = (u₀, u₁, u₂)` are `Fin 3 → ℝ`, `vertex i` is the vertex `e_{i+1}`
(`Pi.single i 1`). The edge `{u_k = 0}` of `U_T` is the segment from `vertex (k + 1)` to
`vertex (k + 2)`. The state of the edge problem is `q = (x, y, s) : Fin 3 → ℝ` (indices `0, 1, 2`),
so that the costate `(λ₁, λ₂, λ₃)` dual to `(x, y, s)` (TeX 6761–6764) is `p(e₀), p(e₁), p(e₂)`
(`edgeCostate p 0`, `edgeCostate p 1`, `edgeCostate p 2`). The rotation by `R` (conjugation)
takes `Z_u` to `Z_{u'}` with the coordinates of `u` permuted cyclically
(`R⁻¹ Z_{e_m} R = Z_{e_{m+1}}`, `poly_Rinv_conj_vertex`); `X ↦ Rʲ X R⁻ʲ` takes a control in the
edge `{u_j = 0}` to a control in the edge `{u₀ = 0}`, which is the edge the book treats.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-! ### Extremal lifted trajectories on an interval -/

/-- An **extremal lifted trajectory on `[a, b]`** of the Reinhardt control problem (Chapter 8:
"Consider an extremal lifted trajectory on `[t₁, t₂]`", TeX 7449; "along a lifted extremal",
TeX 7129, 7176): the state–costate system of Problem 6.7.1 on `[a, b]` with the conditions of the
maximum principle of §6.2 (`λ_cost ≤ 0` constant, nontriviality of the reduced costate
`(λ_cost, Λ₁, Λ_R)`, the maximum condition and `H = 0` almost everywhere) and no boundary
conditions, written after the time shift `t ↦ a + t` as `IsStateCostateSolution` on
`[0, b - a]`. It includes `a < b`.

Nontriviality is imposed on the reduced costate, as Chapter 8 uses it (TeX 7163–7166, 7583;
inventory, gap G1); `IsPontryaginExtremal` imposes the same condition. -/
def IsExtremalOn (a b : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) : Prop :=
  IsStateCostateSolution (b - a) (fun t ↦ u (a + t)) (fun t ↦ g (a + t)) (fun t ↦ X (a + t))
    (fun t ↦ Λ₁ (a + t)) (fun t ↦ ΛR (a + t)) lam

/-! ### The edge control problem (Definition 8.1.1) -/

/-- The control `u = (0, ½ + u_e, ½ - u_e)` on the edge `{u₀ = 0}` of `U_T` with parameter
`u_e ∈ [-½, ½]` (TeX 6684–6689). -/
noncomputable def edgeControl (ue : ℝ) : Fin 3 → ℝ := ![0, 1 / 2 + ue, 1 / 2 - ue]

/-- The right-hand side `f₂(x, y, u_e) = 2√3 y² u_e / (-1 + 2√3 x u_e)` of `y' = f₂` on the edge
`{u₀ = 0}` (TeX 6697–6700; the specialization of Lemma 4.5.2 to `u = (0, ½ + u_e, ½ - u_e)`). -/
noncomputable def edgeF₂ (x y ue : ℝ) : ℝ := 2 * √3 * y ^ 2 * ue / (-1 + 2 * √3 * x * ue)

/-- The state space of the edge control problem (Definition 8.1.1): the open set of
`(x, y, s) ∈ ℝ³` with `y > 0` and `-1/√3 < x < 1/√3`. It contains the star domain (in the
coordinates `x, y`). -/
def edgeDomain : Set (Fin 3 → ℝ) := {q | 0 < q 1 ∧ -(1 / √3) < q 0 ∧ q 0 < 1 / √3}

/-- The control set `[-½, ½]` of the edge control problem (Definition 8.1.1). -/
noncomputable def edgeControlSet : Set ℝ := Icc (-(1 / 2)) (1 / 2)

/-- The state equations (8.1.3) (`eqn:xy-edge`) of the edge control problem, for the state
`q = (x, y, s)`: `x' = y`, `y' = f₂(x, y, u_e)`, `s' = 1/y`. -/
noncomputable def edgeField (q : Fin 3 → ℝ) (ue : ℝ) : Fin 3 → ℝ :=
  ![q 1, edgeF₂ (q 0) (q 1) ue, 1 / q 1]

/-- The cost integrand `φ_edge(x, y) = x²/y` of the edge control problem (8.1.5)
(`eqn:edge:cost`). -/
noncomputable def edgeCost (q : Fin 3 → ℝ) (_ue : ℝ) : ℝ := q 0 ^ 2 / q 1

/-- The costate `λ_{i+1} = p(e_i)` dual to the state coordinate `i` of the edge problem: `λ₁`,
`λ₂`, `λ₃` dual to `x`, `y`, `s` (TeX 6761–6764). -/
noncomputable def edgeCostate (p : StrongDual ℝ (Fin 3 → ℝ)) (i : Fin 3) : ℝ :=
  p (Pi.single i 1)

/-- An **extremal lifted trajectory of the edge control problem** on `[0, T]`
(Definition 8.1.1, `def:edge-extremal`, with the conditions of the maximum principle of §6.2):
the pair `(u_e, q)` is admissible in the state space `edgeDomain` with controls in `[-½, ½]`
(the state equations (8.1.3) in Carathéodory's sense, measurable control), and the covector curve
`p` with the constant `λ_cost = ν` satisfies

* `ν ≤ 0` and `(ν, p(t)) ≠ 0` for every `t ∈ [0, T]`;
* Hamilton's equations for the costate, `p' = -∂H/∂q` (`Pontryagin.IsAdjoint`, integral form);
* the maximum condition for the Hamiltonian (8.1.6) (`eqn:edge:ham`)
  `H = λ₁ y + λ₂ f₂(x, y, u_e) + λ₃/y + λ_cost x²/y` (`Pontryagin.controlHamiltonian`) over
  `[-½, ½]`, almost everywhere;
* `H = 0` almost everywhere (free terminal time).

With fixed endpoints (8.1.4) the transversality conditions are empty. These are the conclusions
of `External.pontryagin_maximum_principle` for the edge problem. -/
def IsEdgeProblemExtremal (T : ℝ) (ue : ℝ → ℝ) (q : ℝ → Fin 3 → ℝ) (ν : ℝ)
    (p : ℝ → StrongDual ℝ (Fin 3 → ℝ)) : Prop :=
  0 < T ∧ Pontryagin.IsAdmissibleIn edgeField edgeDomain edgeControlSet (q 0) T ue q ∧ ν ≤ 0 ∧
    (∀ t ∈ Icc 0 T, (ν, p t) ≠ 0) ∧ Pontryagin.IsAdjoint edgeField edgeCost ν ue q T p ∧
    Pontryagin.IsMaximal edgeField edgeCost ν edgeControlSet ue q T p ∧
    ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
      Pontryagin.controlHamiltonian edgeField edgeCost ν (q t) (p t) (ue t) = 0

/-! ### Edge coordinates of a Reinhardt trajectory -/

/-- The rotation `X ↦ Rʲ X R⁻ʲ` that takes a control in the edge `{u_j = 0}` of `U_T` to a control
in the edge `{u₀ = 0}` treated by the book ("By rotational symmetry, we obtain edge control
systems likewise for the other edges of `U_T`", TeX 6774–6775): `Rʲ Z_u R⁻ʲ = Z_{u'}` with
`u'_m = u_{m+j}`. It is also applied to `g`, `Λ₁` and `Λ_R`. -/
noncomputable def edgeFrame (j : Fin 3) (M : Mat2) : Mat2 := R ^ (j : ℕ) * M * R⁻¹ ^ (j : ℕ)

/-- The edge parameter `u_e = (u_{j+1} - u_{j+2})/2` of a control `u` in the edge `{u_j = 0}`:
after the rotation `edgeFrame j`, `u = (0, ½ + u_e, ½ - u_e)` (TeX 6684–6689). -/
noncomputable def edgeParam (j : Fin 3) (u : Fin 3 → ℝ) : ℝ := (u (j + 1) - u (j + 2)) / 2

/-- The state `(x, y, s)` of the `j`-th edge control problem attached to the Reinhardt trajectory
`X` from the time `a`, as a function of the elapsed time `t` (TeX 6690–6730): `z = x + iy` is the
point of the upper half-plane with `Φ(z) = Rʲ X(a + t) R⁻ʲ` (so `x = X̃₀₀/X̃₁₀` and `y = 1/X̃₁₀`
for `X̃ = Rʲ X R⁻ʲ`, Lemma 4.2.1), and `s(t) = ∫ₐ^{a+t} dτ/y(τ)`, with `s(0) = 0` ("We can take
`s₀ = 0`", TeX 6732). -/
noncomputable def edgeState (j : Fin 3) (X : ℝ → Mat2) (a t : ℝ) : Fin 3 → ℝ :=
  ![edgeFrame j (X (a + t)) 0 0 / edgeFrame j (X (a + t)) 1 0, 1 / edgeFrame j (X (a + t)) 1 0,
    ∫ τ in a..a + t, edgeFrame j (X τ) 1 0]

/-- **Definition 8.1.2** (edge extremal). A Reinhardt trajectory `(g, X)` with control `u` is
*edge extremal* on `[a, b]` if on every subinterval `[c, d] ⊆ [a, b]` on which some component
`u_j` of the control is zero almost everywhere, the trajectory is extremal with respect to the
corresponding edge control problem: the edge state `(x, y, s)` of the trajectory on `[c, d]`
(`edgeState j X c`) with the edge control `u_e = edgeParam j u` lifts to an extremal of the edge
control problem (`IsEdgeProblemExtremal`, fixed endpoints those of the trajectory, (8.1.4)).

The edge state does not involve `g`, which on such an interval is determined by `(s, x)`
(equation (8.1.1), `eqn_g_edge`); the definition therefore takes `u` and `X` only. -/
def IsEdgeExtremalOn (a b : ℝ) (u : ℝ → Fin 3 → ℝ) (X : ℝ → Mat2) : Prop :=
  ∀ (j : Fin 3) (c d : ℝ), a ≤ c → c < d → d ≤ b → (∀ᵐ t, t ∈ Ioo c d → u t j = 0) →
    ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ (Fin 3 → ℝ)),
      IsEdgeProblemExtremal (d - c) (fun t ↦ edgeParam j (u (c + t))) (edgeState j X c) ν p

/-! ### Faces of the control simplex and the maximizers of the Hamiltonian (§7.3) -/

/-- The set of controls in `U_T` maximizing the Hamiltonian `H(Λ₁, Λ_R, X; Z_u)`
(equation `eqn:max-ham`, §7.3): `(X, Λ_R) ∈ (T*O_J)_I` exactly when this set is the face
`(U_T)_I` spanned by the vertices `e_i`, `i ∈ I` (TeX 5813–5826). -/
def hamiltonianArgmax (lam : ℝ) (Λ₁ ΛR X : Mat2) : Set (Fin 3 → ℝ) :=
  {u ∈ controlSimplex | ∀ v ∈ controlSimplex,
    hamiltonian lam Λ₁ ΛR X v ≤ hamiltonian lam Λ₁ ΛR X u}

/-- The edge `{u ∈ U_T | u_k = 0}` of the control simplex, the face spanned by `vertex (k + 1)`
and `vertex (k + 2)`. -/
def controlEdge (k : Fin 3) : Set (Fin 3 → ℝ) := {u ∈ controlSimplex | u k = 0}

/-! ### The singular locus (Definition 8.2.4) -/

/-- **Definition 8.2.4** (singular locus).
`𝒮_sing = {(g, Λ₁, X, Λ_R) = (g₀, (3/2) λ_cost J, J, 0) | g₀ ∈ SL₂(ℝ), λ_cost ≠ 0}`, a subset of
the extended state space `T*(SL₂(ℝ) × 𝔰𝔩₂(ℝ))`, whose points are written `(g, Λ₁, X, Λ_R)`.
It lies over the point `z = i` of the star domain (`Φ(i) = J`).

The constant `λ_cost` is bound by the set-builder, as printed. Along an extremal with multiplier
`λ_cost`, the lift meets `𝒮_sing` at `t` exactly when `λ_cost ≠ 0`, `Λ₁(t) = (3/2) λ_cost J`,
`X(t) = J` and `Λ_R(t) = 0` with the extremal's own `λ_cost`
(`IsExtremalOn.mem_singularLocus_iff`, from `H = 0`). -/
def singularLocus : Set (Mat2 × Mat2 × Mat2 × Mat2) :=
  {q | ∃ lam : ℝ, lam ≠ 0 ∧ q.1.det = 1 ∧ q.2.1 = (3 / 2 * lam) • J ∧ q.2.2.1 = J ∧
    q.2.2.2 = 0}

/-- The rotation `exp(Jt) = [[cos t, -sin t], [sin t, cos t]]`: the singular subarcs are
`g(t) = g₀ exp(Jt)` (Theorem 8.2.3). -/
noncomputable def expJ (t : ℝ) : Mat2 := !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

/-- The centre `(⅓, ⅓, ⅓)` of the control simplex `U_T` (Theorem 8.2.3), with `Z_u = J/3`. -/
noncomputable def controlCentre : Fin 3 → ℝ := ![1 / 3, 1 / 3, 1 / 3]

/-! ### Bang-bang controls with finitely many switches -/

/-- The control `u` is **bang-bang with finitely many switches on `[a, b]`** (Definition 7.3.2;
Theorems 8.1.4, 8.3.2, 16.3.1: "equal a.e. to a piecewise constant function … with finitely many
switches"): off a finite set `S` of times, `u` is almost everywhere constant near each time of
`(a, b)`, equal to a vertex of `U_T`. (On each interval between consecutive points of `S ∪ {a, b}`
it is then almost everywhere equal to one vertex.) -/
def IsFiniteBangBang (a b : ℝ) (u : ℝ → Fin 3 → ℝ) : Prop :=
  ∃ S : Finset ℝ, ∀ t ∈ Ioo a b, t ∉ S → ∃ i : Fin 3, ∃ ε > 0,
    ∀ᵐ τ, τ ∈ Ioo (t - ε) (t + ε) → u τ = vertex i

/-! ### Basic facts about extremals on intervals -/

/-- An integral curve on `[0, S]`, restarted at `s ≥ 0`, is an integral curve on `[0, T]` when
`s + T ≤ S`. -/
private lemma l3a_isIntegralCurve_shift {F V : ℝ → Mat2} {S s T : ℝ}
    (hI : IsIntegralCurve F V S) (hs : 0 ≤ s) (hT : 0 ≤ T) (hsT : s + T ≤ S) :
    IsIntegralCurve (fun t ↦ F (s + t)) (fun t ↦ V (s + t)) T := by
  intro i j
  obtain ⟨hint, heq⟩ := hI i j
  have hS : 0 ≤ S := by linarith
  have hsub : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ S →
      IntervalIntegrable (fun σ ↦ V σ i j) volume a b := fun ha hab hb ↦
    hint.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hS]; exact Icc_subset_Icc ha hb)
  refine ⟨?_, fun t ht ↦ ?_⟩
  · have := (hsub hs (by linarith) hsT).comp_add_left s
    simpa only [sub_self, add_sub_cancel_left] using this
  · have hcomp := intervalIntegral.integral_comp_add_left (fun σ ↦ V σ i j) s (a := 0) (b := t)
    simp only [add_zero] at hcomp ⊢
    rw [hcomp, heq (s + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩, heq s ⟨hs, by linarith⟩,
      ← intervalIntegral.integral_add_adjacent_intervals (hsub le_rfl hs (by linarith))
        (hsub hs (by linarith [ht.1]) (by linarith [ht.2]))]
    ring

/-- The state–costate system on `[0, T]`, restarted at `s ≥ 0`, solves the system on `[0, T']`
when `s + T' ≤ T`: the integral equations restrict (`l3a_isIntegralCurve_shift`), the pointwise
conditions are those at the times `s + t ∈ [0, T]`, and the almost-everywhere conditions pass
through the translation `t ↦ s + t`, which preserves Lebesgue measure. -/
private lemma l3a_isStateCostateSolution_shift {T s T' : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsStateCostateSolution T u g X Λ₁ ΛR lam)
    (hs : 0 ≤ s) (hT' : 0 < T') (hsT : s + T' ≤ T) :
    IsStateCostateSolution T' (fun t ↦ u (s + t)) (fun t ↦ g (s + t)) (fun t ↦ X (s + t))
      (fun t ↦ Λ₁ (s + t)) (fun t ↦ ΛR (s + t)) lam := by
  obtain ⟨⟨-, hum, husim, hst, hgI, hXI⟩, hlam, hpt, hI1, hIR, hmax⟩ := h
  have hmem : ∀ t ∈ Icc 0 T', s + t ∈ Icc 0 T := fun t ht ↦
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨⟨hT', hum.comp (measurable_const_add s), fun t ht ↦ husim _ (hmem t ht),
    fun t ht ↦ hst _ (hmem t ht), l3a_isIntegralCurve_shift hgI hs hT'.le hsT,
    l3a_isIntegralCurve_shift hXI hs hT'.le hsT⟩, hlam, fun t ht ↦ hpt _ (hmem t ht),
    l3a_isIntegralCurve_shift hI1 hs hT'.le hsT, l3a_isIntegralCurve_shift hIR hs hT'.le hsT, ?_⟩
  filter_upwards [(measurePreserving_add_left volume s).quasiMeasurePreserving.ae hmax]
    with t ht ht'
  exact ht ⟨by linarith [ht'.1], by linarith [ht'.2]⟩

/-- `|⟨M, Z_u⟩| ≤ Σᵢⱼ |Mᵢⱼ|` for `u ∈ U_T`: the entries of `Z_u` are at most `1` in absolute
value. -/
private lemma l3a_abs_traceForm_controlMatrix_le (M : Mat2) {u : Fin 3 → ℝ}
    (hu : u ∈ controlSimplex) :
    |traceForm M (controlMatrix u)| ≤ |M 0 0| + |M 0 1| + |M 1 0| + |M 1 1| := by
  obtain ⟨hu01, hsum⟩ := hu
  obtain ⟨h00, h01⟩ := hu01 0
  obtain ⟨h10, h11⟩ := hu01 1
  obtain ⟨h20, h21⟩ := hu01 2
  have h3 : 1 ≤ √3 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs3 : 0 < √3 := by positivity
  have hZ : ∀ i j, |controlMatrix u i j| ≤ 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [controlMatrix, Fin.zero_eta, Fin.isValue,
      Fin.mk_one, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one] <;> rw [abs_le]
    · constructor
      · rw [le_div_iff₀ hs3]; nlinarith
      · rw [div_le_iff₀ hs3]; nlinarith
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor
      · rw [le_div_iff₀ hs3]; nlinarith
      · rw [div_le_iff₀ hs3]; nlinarith
  have hterm : ∀ i j k l, |M i j * controlMatrix u k l| ≤ |M i j| := fun i j k l ↦ by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hZ k l)
  have htr : traceForm M (controlMatrix u) = M 0 0 * controlMatrix u 0 0 +
      M 0 1 * controlMatrix u 1 0 + (M 1 0 * controlMatrix u 0 1 +
        M 1 1 * controlMatrix u 1 1) := by
    simp only [traceForm, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  rw [htr]
  refine (abs_add_le _ _).trans ?_
  have e1 := (abs_add_le (M 0 0 * controlMatrix u 0 0) (M 0 1 * controlMatrix u 1 0))
  have e2 := (abs_add_le (M 1 0 * controlMatrix u 0 1) (M 1 1 * controlMatrix u 1 1))
  linarith [hterm 0 0 0 0, hterm 0 1 1 0, hterm 1 0 0 1, hterm 1 1 1 1]

/-- `⟨J, Z_u⟩ = -2/3` for `u ∈ U_T`. -/
private lemma l3a_traceForm_J_controlMatrix {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) :
    traceForm J (controlMatrix u) = -(2 / 3) := by
  have hsum := hu.2
  simp only [traceForm, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, J,
    controlMatrix, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, Fin.isValue]
  linarith

/-- **`H = 0` at a time where `Λ_R = 0` and `X = J`.** Along a solution of the state–costate
system, `H = 0` holds almost everywhere; at a time `t` with `Λ_R(t) = 0` and `X(t) = J` it holds
at `t` itself, where `H` reduces to `⟨Λ₁ - (3/2) λ_cost J, X⟩`. Near `t`, the first term of `H` is
close to its value at `t`, `|⟨X, Z_u⟩| ≥ 1/3` (since `⟨J, Z_u⟩ = -2/3`) and
`|⟨Λ_R, Z_u⟩| ≤ Σ |Λ_R|ᵢⱼ` is small, uniformly in `u ∈ U_T`; if the first term did not vanish at
`t`, `H` would not vanish on a nonempty open set of times, which has positive measure. -/
private lemma l3a_traceForm_eq_zero {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (h : IsStateCostateSolution T u g X Λ₁ ΛR lam) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hR : ΛR t = 0) (hX : X t = J) :
    traceForm (Λ₁ t - (3 / 2 * lam) • J) (X t) = 0 := by
  obtain ⟨⟨hT, -, husim, -, -, hXI⟩, -, -, hI1, hIR, hmax⟩ := h
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  have h1c : ContinuousOn Λ₁ (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hI1
  have hRc : ContinuousOn ΛR (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hIR
  -- the first term `f` of `H`, and the size `ent` of a matrix
  obtain ⟨ent, hent⟩ : ∃ ent : Mat2 → ℝ,
      ent = fun M ↦ |M 0 0| + |M 0 1| + |M 1 0| + |M 1 1| := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ,
      f = fun τ ↦ traceForm (Λ₁ τ - (3 / 2 * lam) • J) (X τ) := ⟨_, rfl⟩
  have hel : ∀ i j, Continuous fun M : Mat2 ↦ M i j := fun i j ↦ continuous_id.matrix_elem i j
  have hentc : Continuous ent := by
    rw [hent]
    exact (((hel 0 0).abs.add (hel 0 1).abs).add (hel 1 0).abs).add (hel 1 1).abs
  have htf : Continuous fun p : Mat2 × Mat2 ↦ traceForm p.1 p.2 := by
    unfold traceForm
    exact (continuous_fst.matrix_mul continuous_snd).matrix_trace
  have hfc' := htf.continuousAt.comp_continuousWithinAt
    (((h1c t ht).sub (continuousWithinAt_const (b := (3 / 2 * lam) • J))).prodMk (hXc t ht))
  have hfc : ContinuousWithinAt f (Icc 0 T) t := by
    rw [hf]
    exact hfc'
  have hRe := hentc.continuousAt.comp_continuousWithinAt (hRc t ht)
  have hXe := hentc.continuousAt.comp_continuousWithinAt
    ((hXc t ht).sub (continuousWithinAt_const (b := J)))
  have hRt : (ent ∘ ΛR) t = 0 := by simp [hent, hR]
  have hXt : (ent ∘ fun τ ↦ X τ - J) t = 0 := by simp [hent, hX]
  rw [show traceForm (Λ₁ t - (3 / 2 * lam) • J) (X t) = f t by rw [hf]]
  by_contra hc
  have hcpos : 0 < |f t| := abs_pos.2 hc
  -- near `t`: `f` is close to `f t`, `Λ_R` is small and `X` is close to `J`
  have hev : ∀ᶠ τ in 𝓝[Ioo 0 T] t,
      |f τ - f t| < |f t| / 2 ∧ ent (ΛR τ) < |f t| / 6 ∧ ent (X τ - J) < 1 / 3 := by
    refine (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)).filter_mono
      (nhdsWithin_mono t Ioo_subset_Icc_self)
    · have := Metric.tendsto_nhds.1 hfc.tendsto (|f t| / 2) (by positivity)
      simpa only [Real.dist_eq] using this
    · have := hRt ▸ hRe.tendsto
      exact this.eventually (gt_mem_nhds (by positivity))
    · have := hXt ▸ hXe.tendsto
      exact this.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨V, hVo, htV, hVsub⟩ := mem_nhdsWithin.1 hev
  have hne : (V ∩ Ioo 0 T).Nonempty :=
    mem_closure_iff.1 (by rw [closure_Ioo hT.ne]; exact ht) V hVo htV
  refine ((hVo.inter isOpen_Ioo).measure_pos volume hne).ne'
    (measure_mono_null (fun τ hτ ↦ ?_) (ae_iff.1 hmax))
  obtain ⟨hfτ, hRτ, hXτ⟩ := hVsub hτ
  have hτI : τ ∈ Ioo 0 T := hτ.2
  have hu := husim τ (Ioo_subset_Icc_self hτI)
  simp only [mem_ofPred_eq, not_imp]
  refine ⟨hτI, fun hH ↦ ?_⟩
  have hH0 := hH.1
  -- `⟨X, Z_u⟩ = -2/3 + ⟨X - J, Z_u⟩ ≤ -1/3`
  have hXZ : traceForm (X τ) (controlMatrix (u τ)) ≤ -(1 / 3) := by
    have e : traceForm (X τ) (controlMatrix (u τ)) =
        traceForm J (controlMatrix (u τ)) + traceForm (X τ - J) (controlMatrix (u τ)) := by
      simp only [traceForm, Matrix.sub_mul, Matrix.trace_sub]
      ring
    rw [e, l3a_traceForm_J_controlMatrix hu]
    have h1 := (abs_le.1 (l3a_abs_traceForm_controlMatrix_le (X τ - J) hu)).2
    have h2 : ent (X τ - J) = |(X τ - J) 0 0| + |(X τ - J) 0 1| + |(X τ - J) 1 0| +
        |(X τ - J) 1 1| := by rw [hent]
    linarith
  -- `|⟨Λ_R, Z_u⟩ / ⟨X, Z_u⟩| ≤ 3 Σ |Λ_R|ᵢⱼ < |f t| / 2`
  have hq : |traceForm (ΛR τ) (controlMatrix (u τ)) / traceForm (X τ) (controlMatrix (u τ))|
      < |f t| / 2 := by
    rw [abs_div, div_lt_iff₀ (by rw [abs_pos]; linarith)]
    have h1 := l3a_abs_traceForm_controlMatrix_le (ΛR τ) hu
    have h1' : ent (ΛR τ) = |ΛR τ 0 0| + |ΛR τ 0 1| + |ΛR τ 1 0| + |ΛR τ 1 1| := by rw [hent]
    have h2 : 1 / 3 ≤ |traceForm (X τ) (controlMatrix (u τ))| := by
      rw [abs_of_neg (by linarith)]; linarith
    calc |traceForm (ΛR τ) (controlMatrix (u τ))| ≤ ent (ΛR τ) := h1' ▸ h1
      _ < |f t| / 2 * (1 / 3) := by linarith
      _ ≤ |f t| / 2 * |traceForm (X τ) (controlMatrix (u τ))| := by gcongr
  have hHf : hamiltonian lam (Λ₁ τ) (ΛR τ) (X τ) (u τ) = f τ -
      traceForm (ΛR τ) (controlMatrix (u τ)) / traceForm (X τ) (controlMatrix (u τ)) := by
    rw [hf]; rfl
  rw [hHf, sub_eq_zero] at hH0
  have hfτ' : |f t| / 2 < |f τ| := by
    have := abs_sub_abs_le_abs_sub (f t) (f τ)
    rw [abs_sub_comm] at this
    linarith
  rw [hH0] at hfτ'
  linarith

/-- A Pontryagin extremal on `[0, T]` is an extremal lifted trajectory on every subinterval
`[a, b]`. Proof: `isPontryaginExtremal_iff`, and the restriction of the integral equations and of
the almost-everywhere conditions to `[a, b]` after the time shift `t ↦ a + t`
(`l3a_isStateCostateSolution_shift`). -/
theorem IsPontryaginExtremal.isExtremalOn {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T) : IsExtremalOn a b u g X Λ₁ ΛR lam :=
  l3a_isStateCostateSolution_shift (isPontryaginExtremal_iff.1 h).1 ha (by linarith)
    (by linarith)

/-- An extremal lifted trajectory on `[a, b]` is one on every subinterval `[c, d]` (the time shift
`t ↦ (c - a) + t` of the system on `[0, b - a]`, `l3a_isStateCostateSolution_shift`). -/
theorem IsExtremalOn.mono {a b c d : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (h : IsExtremalOn a b u g X Λ₁ ΛR lam) (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) :
    IsExtremalOn c d u g X Λ₁ ΛR lam := by
  have := l3a_isStateCostateSolution_shift h (s := c - a) (T' := d - c) (by linarith)
    (by linarith) (by linarith)
  have e : ∀ t, a + (c - a + t) = c + t := fun t ↦ by ring
  simp only [e] at this
  exact this

/-- Edge extremality on `[a, b]` passes to subintervals (immediate from Definition 8.1.2). -/
theorem IsEdgeExtremalOn.mono {a b c d : ℝ} {u : ℝ → Fin 3 → ℝ} {X : ℝ → Mat2}
    (h : IsEdgeExtremalOn a b u X) (hac : a ≤ c) (hdb : d ≤ b) : IsEdgeExtremalOn c d u X :=
  fun j c' d' hc' hcd' hd' hu ↦ h j c' d' (hac.trans hc') hcd' (hd'.trans hdb) hu

/-- Along an extremal lifted trajectory on `[a, b]`, the lift `(g, Λ₁, X, Λ_R)` is continuous on
`[a, b]` (its entries are indefinite integrals of integrable functions). -/
theorem IsExtremalOn.continuousOn_lift {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (h : IsExtremalOn a b u g X Λ₁ ΛR lam) :
    ContinuousOn (fun t ↦ (g t, Λ₁ t, X t, ΛR t)) (Icc a b) := by
  obtain ⟨⟨-, -, -, -, hgI, hXI⟩, -, -, hI1, hIR, -⟩ := h
  have hc : ∀ {F V : ℝ → Mat2}, IsIntegralCurve (fun t ↦ F (a + t)) V (b - a) →
      ContinuousOn F (Icc a b) := fun {F V} hI ↦ by
    have h1 := (Matrix.continuousOn_of_eq_add_integral hI).comp
      (continuous_sub_right a).continuousOn
      (fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩ : MapsTo (fun t ↦ t - a) (Icc a b)
        (Icc 0 (b - a)))
    refine h1.congr fun t _ ↦ ?_
    simp only [Function.comp_apply, add_sub_cancel]
  exact (hc hgI).prodMk ((hc hI1).prodMk ((hc hXI).prodMk (hc hIR)))

/-- **Meeting the singular locus along an extremal.** Along an extremal lifted trajectory with
multiplier `λ_cost`, the lift is in `𝒮_sing` at `t ∈ [a, b]` if and only if `λ_cost ≠ 0`,
`Λ₁(t) = (3/2) λ_cost J`, `X(t) = J` and `Λ_R(t) = 0`; so the set of such times is closed.

Proof: at a time with `Λ_R(t) = 0` the Hamiltonian `H(Λ₁, Λ_R, X; Z_u) = ⟨Λ₁ - (3/2)λ_cost J, X⟩`
does not depend on the control, and `H = 0` almost everywhere extends to `t` by continuity
(`l3a_traceForm_eq_zero`: the control-dependent term `⟨Λ_R, Z_u⟩/⟨X, Z_u⟩` is at most
`3 Σ |Λ_R|ᵢⱼ` near `t`, uniformly in `u ∈ U_T`, because `⟨J, Z_u⟩ = -2/3` and `X` is near `J`);
with `Λ₁(t) = (3/2) μ J` and `X(t) = J` this gives `-3(μ - λ_cost) = 0`. -/
theorem IsExtremalOn.mem_singularLocus_iff {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (h : IsExtremalOn a b u g X Λ₁ ΛR lam) {t : ℝ} (ht : t ∈ Icc a b) :
    (g t, Λ₁ t, X t, ΛR t) ∈ singularLocus ↔
      lam ≠ 0 ∧ Λ₁ t = (3 / 2 * lam) • J ∧ X t = J ∧ ΛR t = 0 := by
  have e : a + (t - a) = t := by ring
  have ht' : t - a ∈ Icc 0 (b - a) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  constructor
  · rintro ⟨μ, hμ, -, h1, hX, hR⟩
    dsimp only at h1 hX hR
    -- `H = 0` at `t` gives `⟨(3/2)(μ - λ_cost) J, J⟩ = -3(μ - λ_cost) = 0`
    have hH := l3a_traceForm_eq_zero h ht' (by simp only [e]; exact hR) (by simp only [e]; exact hX)
    simp only [e, h1, hX] at hH
    have hμl : μ = lam := by
      simp only [traceForm, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, J,
        Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, of_apply, cons_val', cons_val_zero,
        cons_val_one, empty_val', cons_val_fin_one, Fin.isValue] at hH
      linarith
    subst hμl
    exact ⟨hμ, h1, hX, hR⟩
  · rintro ⟨hl, h1, hX, hR⟩
    have hdet := (h.1.2.2.2.1 (t - a) ht').1
    simp only [e] at hdet
    exact ⟨lam, hl, hdet, h1, hX, hR⟩

end SmoothedPolygons
