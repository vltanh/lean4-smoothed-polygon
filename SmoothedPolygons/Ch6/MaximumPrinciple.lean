module

public import SmoothedPolygons.Ch6.LiftedSystem
public import SmoothedPolygons.Ch6.HalfPlane
public import SmoothedPolygons.Ch6.PeriodicExtension
public import External.Pontryagin
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The maximum principle for the Reinhardt problem (§6.2, §6.6)

The book applies the Pontryagin maximum principle, cited from `zelikin2004control`
(Agrachev–Sachkov), to the Reinhardt control problem (§6.2, TeX 4662–4830), computes the costate
equations in Lie-algebra form (§§6.4–6.5, 6.8), derives the transversality conditions (6.6.1)
(§6.6, TeX 5157–5215), and collects the result as Problem 6.7.1; Proposition 8.1.3 then says (TeX
6791) "We have seen that the global minimizer must be extremal". That statement is
`exists_isPontryaginExtremal_of_isReinhardtMinimizer`: every global minimizer of Problem 3.6.2
(`IsReinhardtMinimizer`) lifts to a Pontryagin extremal (`IsPontryaginExtremal`).

## Route

1. The minimizer lifts to a minimizer of the lifted problem on `ℝ³ × 𝔥*`
   (`IsReinhardtMinimizer.exists_lift`, `SmoothedPolygons/Ch6/LiftedSystem.lean`).
2. The maximum principle (`External.pontryagin_maximum_principle`: free terminal time, integral
   cost, the boundary map `liftedBoundary` a submersion) gives `ν ≤ 0` and a costate
   `p(t) ∈ (ℝ³ × ℝ²)*`.
3. Translation (`isPontryaginExtremal_of_costate`): the `ℝ³`-part of `p` is the left-trivialized
   costate `Λ₁` (Proposition 3.6.1: `⟨Λ₁, Y⟩ = p(Dπ⁻¹(gY), 0)`, i.e. `p(iwasawaField q Y, 0)`), the
   `ℝ²`-part is the half-plane costate `ν = T*Φ(-Λ_R)` (`cotangentNu`, Lemma 6.8.1), which
   determines `Λ_R ∈ X^⊥`; `(p ↦ (Λ₁, Λ_R))` is a linear isomorphism, so `(ν, p) ≠ 0` is
   `(λ_cost, Λ₁, Λ_R) ≠ 0`; the adjoint equation becomes `Λ₁' = [Λ₁, X]` (the content of
   Propositions 6.4.1 and 6.5.1 in the chart) and the `Λ_R` equation (Theorem 6.8.3); the
   Hamiltonian `⟨p, f⟩ + ν φ` is `hamiltonian ν Λ₁ Λ_R X u` (Theorem 6.8.2); transversality for
   the `z`-coupling gives `Λ_R(T) = R⁻¹Λ_R(0)R`, and `Λ₁(T) = R⁻¹Λ₁(0)R` follows from `g(T) = R`
   (Corollary 6.5.3, as Remark 6.6.1 says: `remark6_6_1_lambda1`).

## The translation, step by step

* **Costates.** `Λ₁ = ct_lam1 p(t)` is the traceless matrix with `⟨Λ₁, Y⟩ = p(V_Y, 0)` for the
  basis `H, E, F` of `𝔰𝔩₂(ℝ)`, where `V_Y(s, r, θ) = iwasawaField (s, r, θ) Y` is the lift of the
  left-invariant field `g ↦ gY`; it is linear in `Y`, so the identity holds for every traceless
  `Y` (`ct_traceForm_lam1`). `Λ_R = ct_lamR z p(t)` is the element of `X^⊥` with
  `T*Φ(-Λ_R) = (p(0, e₁), p(0, e₂))` (`ct_cotangentNu_lamR`): its entries are polynomials in
  `x, y, p(0, e₁), p(0, e₂)`.
* **Hamiltonian** (`ct_controlHamiltonian_eq`): `⟨p, f(q, u)⟩ + ν φ(q, u) =
  ⟨Λ₁ - (3/2)νJ, Φ(z)⟩ + ν₁ f₁ + ν₂ f₂`, which is `hamiltonian ν Λ₁ Λ_R X u` by Theorem 6.8.2;
  the maximum condition and `H = 0` transfer verbatim.
* **Nontriviality** (`ct_eq_zero_of_lam`): `V_Y` ranges over `ℝ³` as `Y` ranges over `𝔰𝔩₂(ℝ)`,
  and `Λ_R = 0` forces `ν₁ = ν₂ = 0`; so `Λ₁ = Λ_R = 0` gives `p = 0`.
* **`Λ₁' = [Λ₁, X]`** (`ct_hasDerivAt_lam1`): by the adjoint equation, `⟨Λ₁, Y⟩' =
  p(DV_Y · V_X - DV_X · V_Y, 0) = p([V_X, V_Y], 0) = p(V_{[X, Y]}, 0) = ⟨[Λ₁, X], Y⟩`; the bracket
  identity `[V_X, V_Y] = V_{[X, Y]}` of the lifted left-invariant fields is `ct_dField_bracket`.
* **The `Λ_R` equation** (`ct_hasDerivAt_lamR`): the adjoint equation says `ν' = -dH` for
  `H = planeHamiltonian` (`ct_adjoint_apply_x`, `ct_adjoint_apply_y`). Theorem 6.8.3 is the
  converse implication (from the `Λ_R` equation to `ν' = -dH`); it is applied to the curve
  `L(s) = Λ_R(t) + (s - t) C` through `Λ_R(t)` with velocity `C` = the right-hand side of the
  `Λ_R` equation, which gives `T*Φ(-(Λ_R'(t) - C)) = 0`; since `Λ_R'(t) - C` is traceless and
  orthogonal to `X(t)` (differentiate `⟨Λ_R, X⟩ = 0`), it vanishes (Lemma 6.8.1: `T*Φ(-·)` is
  injective on `X^⊥`).
* **Integral form.** `q` and `p` are Lipschitz on `[0, T]`, so the entries of `Λ₁`, `Λ_R` (smooth
  functions of `(q, p)`) are absolutely continuous; the a.e. derivatives (Lebesgue's
  differentiation theorem for the integral equations of `q`, `p` and `X`) give the integral
  equations of `IsPontryaginExtremal` by the fundamental theorem of calculus for absolutely
  continuous functions (`ct_eq_add_integral`).
* **Transversality for `Λ_R`** (`ct_lamR_transversality`): `G = liftedBoundary` has
  `((0, δ), (0, Mδ)) ∈ ker G'` with `M` the derivative of the Möbius map of `R⁻¹` at `z(0)`, so
  `ν(0)(δ) = ν(T)(Mδ)`, i.e. `⟨-Λ_R(0), Y_{z(0)}(δ)⟩ = ⟨-Λ_R(T), Y_{z(T)}(Mδ)⟩`. Differentiating
  `Φ(R⁻¹ · z) = R⁻¹Φ(z)R` (Remark 4.2.2, `Φ_mobius`) with Lemma 4.2.4 gives
  `[Y_{z(T)}(Mδ), X(T)] = R⁻¹[Y_{z(0)}(δ), X(0)]R`, so `Y_{z(T)}(Mδ) - R⁻¹Y_{z(0)}(δ)R` is a
  multiple of `X(T)` (`orb_centralizer`), which is orthogonal to `Λ_R(T)`; hence
  `T*Φ(-Λ_R(0)) = T*Φ(-RΛ_R(T)R⁻¹)` at `z(0)`, and `Λ_R(0) = RΛ_R(T)R⁻¹` (Lemma 6.8.1).

## Departures from the book's route

The book applies the PMP on `SL₂(ℝ) × 𝔰𝔩₂(ℝ)`, where it yields the spurious multiplier
`(0, 0, cX)` (E21; inventory §3.4); the state space here is `SL₂(ℝ) × 𝔥*` in the global chart
`ℝ³ × 𝔥*` (Iwasawa coordinates of the universal cover), on which the nontriviality condition is
the reduced one of `IsPontryaginExtremal`. The book's "smooth manifold" and "closed control set"
are read through the chart and the compact `U_T`.

Departure from the paper (in the proof of the translation): the book derives `Λ₁' = [Λ₁, X]`
and `Λ_R' = …` from Hamilton's equations on `T*SL₂(ℝ) × T*𝔰𝔩₂(ℝ)` (Proposition 6.5.1: the
Euler–Arnold equation for `Λ₁ = pg` and `Λ₂' = -δH/δX`). With the state space `SL₂(ℝ) × 𝔥*`
those hypotheses are not available (the costate determines `Λ₂` only modulo `ℝX`, E21), so
`Λ₁' = [Λ₁, X]` is computed in the chart from the bracket of the lifted left-invariant fields,
and the `Λ_R` equation is obtained from the half-plane form of the costate equation
(Theorem 6.8.3), which the book states as equivalent. Corollary 6.5.4 is not needed.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Pontryagin ControlSystem Matrix
open scoped NNReal

/-! ### The costates `Λ₁`, `Λ_R` of a covector -/

/-- `iwasawaField p` is linear in the matrix. -/
private lemma ct_iwasawaField_add_smul (p : ℝ × ℝ × ℝ) (a : ℝ) (A B : Mat2) :
    iwasawaField p (a • A + B) = a • iwasawaField p A + iwasawaField p B := by
  simp only [iwasawaField, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    ring
  · simp only
  · simp only

private lemma ct_iwasawaField_zero (p : ℝ × ℝ × ℝ) : iwasawaField p 0 = 0 := by
  simp [iwasawaField]

private lemma ct_iwasawaField_decomp (p : ℝ × ℝ × ℝ) (Y : Mat2) (hY : Y.trace = 0) :
    iwasawaField p Y = Y 0 0 • iwasawaField p !![1, 0; 0, -1] +
      (Y 0 1 • iwasawaField p !![0, 1; 0, 0] + Y 1 0 • iwasawaField p !![0, 0; 1, 0]) := by
  calc iwasawaField p Y = iwasawaField p (Y 0 0 • !![1, 0; 0, -1] +
        (Y 0 1 • !![0, 1; 0, 0] + (Y 1 0 • !![0, 0; 1, 0] + 0))) := by
        congr 1
        have hY' : Y 1 1 = -Y 0 0 := by rw [Matrix.trace_fin_two] at hY; linarith
        ext i j; fin_cases i <;> fin_cases j <;> simp [hY']
    _ = _ := by
        rw [ct_iwasawaField_add_smul, ct_iwasawaField_add_smul, ct_iwasawaField_add_smul,
          ct_iwasawaField_zero, add_zero]

/-- The left-trivialized costate `Λ₁` of a covector `π` at the point `p` of the Iwasawa chart
(Proposition 3.6.1): the traceless matrix with `⟨Λ₁, Y⟩ = π(iwasawaField p Y, 0)` for every
traceless `Y` (`ct_traceForm_lam1`). -/
private noncomputable def ct_lam1 (p : ℝ × ℝ × ℝ) (π : StrongDual ℝ LiftedState) : Mat2 :=
  !![π (iwasawaField p !![1, 0; 0, -1], 0) / 2, π (iwasawaField p !![0, 0; 1, 0], 0);
    π (iwasawaField p !![0, 1; 0, 0], 0), -(π (iwasawaField p !![1, 0; 0, -1], 0) / 2)]

/-- The reduced costate `Λ_R ∈ X^⊥` of a covector `π` at the point `z = x + iy` of the
half-plane: the matrix with `T*Φ(-Λ_R) = (π(0, e₁), π(0, e₂))` (Lemma 6.8.1, `eqn:nu`). -/
private noncomputable def ct_lamR (z : ℝ × ℝ) (π : StrongDual ℝ LiftedState) : Mat2 :=
  !![-(z.1 * π (0, (1, 0)) + z.2 * π (0, (0, 1))),
    π (0, (1, 0)) * (z.1 ^ 2 - z.2 ^ 2) + 2 * z.1 * z.2 * π (0, (0, 1));
    -π (0, (1, 0)), z.1 * π (0, (1, 0)) + z.2 * π (0, (0, 1))]

private lemma ct_traceForm_lam1 (p : ℝ × ℝ × ℝ) (π : StrongDual ℝ LiftedState) {Y : Mat2}
    (hY : Y.trace = 0) : traceForm (ct_lam1 p π) Y = π (iwasawaField p Y, 0) := by
  have hY' : Y 1 1 = -Y 0 0 := by rw [Matrix.trace_fin_two] at hY; linarith
  rw [ct_iwasawaField_decomp p Y hY]
  have e : ∀ (a b c : ℝ) (A B C : ℝ × ℝ × ℝ),
      ((a • A + (b • B + c • C), (0 : ℝ × ℝ)) : LiftedState) =
        a • ((A, 0) : LiftedState) + (b • ((B, 0) : LiftedState) + c • ((C, 0) : LiftedState)) := by
    intro a b c A B C; ext <;> simp
  rw [e, map_add, map_add, map_smul, map_smul, map_smul]
  simp only [traceForm, ct_lam1, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, hY']
  ring

private lemma ct_trace_lam1 (p : ℝ × ℝ × ℝ) (π : StrongDual ℝ LiftedState) :
    (ct_lam1 p π).trace = 0 := by
  simp [ct_lam1, Matrix.trace_fin_two]

private lemma ct_trace_lamR (z : ℝ × ℝ) (π : StrongDual ℝ LiftedState) :
    (ct_lamR z π).trace = 0 := by
  simp [ct_lamR, Matrix.trace_fin_two]

private lemma ct_traceForm_lamR_Φ (z : ℝ × ℝ) (π : StrongDual ℝ LiftedState) (hy : z.2 ≠ 0) :
    traceForm (ct_lamR z π) (Φ z.1 z.2) = 0 := by
  simp [traceForm, ct_lamR, Φ, Matrix.trace_fin_two]
  field_simp
  ring

/-- In coordinates, `T*Φ(-Λ) = (-Λ₁₀, (Λ₁₁ - Λ₀₀)/(2y) + Λ₁₀ x / y)`. -/
private lemma ct_cotangentNu_eq (x y : ℝ) (Λ : Mat2) (hy : y ≠ 0) :
    cotangentNu x y Λ = (-Λ 1 0, (Λ 1 1 - Λ 0 0) / (2 * y) + Λ 1 0 * x / y) := by
  rw [Matrix.eta_fin_two Λ]
  simp [cotangentNu, traceForm, tangentLift, Matrix.trace_fin_two, hy]
  field_simp
  ring

private lemma ct_cotangentNu_lamR (z : ℝ × ℝ) (π : StrongDual ℝ LiftedState) (hy : z.2 ≠ 0) :
    cotangentNu z.1 z.2 (ct_lamR z π) = (π (0, (1, 0)), π (0, (0, 1))) := by
  rw [ct_cotangentNu_eq _ _ _ hy]
  simp [ct_lamR]
  field_simp
  ring

/-- `T*Φ(-·)` is injective on `X^⊥ ∩ 𝔰𝔩₂(ℝ)`. -/
private lemma ct_eq_zero_of_cotangentNu (x y : ℝ) (E : Mat2) (hy : y ≠ 0) (htr : E.trace = 0)
    (hν : cotangentNu x y E = 0) (hperp : traceForm E (Φ x y) = 0) : E = 0 := by
  rw [ct_cotangentNu_eq _ _ _ hy] at hν
  have h1 : E 1 0 = 0 := by have := congrArg Prod.fst hν; simp at this; linarith
  have h2 : (E 1 1 - E 0 0) / (2 * y) + E 1 0 * x / y = 0 := congrArg Prod.snd hν
  rw [h1, zero_mul, zero_div, add_zero, div_eq_zero_iff] at h2
  rw [Matrix.trace_fin_two] at htr
  have h00 : E 0 0 = 0 := by rcases h2 with h2 | h2 <;> [linarith; (exfalso; simp [hy] at h2)]
  have h11 : E 1 1 = 0 := by linarith
  have h01 : E 0 1 = 0 := by
    have key : traceForm E (Φ x y) = E 0 1 / y := by
      simp [traceForm, Φ, Matrix.trace_fin_two, Matrix.mul_apply, h1, h00, h11, div_eq_mul_inv]
    rw [key, div_eq_zero_iff] at hperp
    exact hperp.resolve_right hy
  ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h00, h11, h01]

/-- **The Hamiltonian in the chart** (Proposition 6.4.1, Theorem 6.8.2 before `ν = T*Φ(-Λ_R)`):
`⟨π, f(q, u)⟩ + ν φ(q, u) = ⟨Λ₁ - (3/2)νJ, Φ(z)⟩ + π(0, e₁) f₁ + π(0, e₂) f₂`. -/
private lemma ct_controlHamiltonian_eq (ν : ℝ) (q : LiftedState) (π : StrongDual ℝ LiftedState)
    (u : Fin 3 → ℝ) :
    controlHamiltonian liftedField liftedCost ν q π u =
      planeHamiltonian ν (ct_lam1 q.1 π) q.2.1 q.2.2 (π (0, (1, 0))) (π (0, (0, 1))) u := by
  have hΦ : (Φ q.2.1 q.2.2).trace = 0 := by simp [Φ, Matrix.trace_fin_two]; ring
  have e : (liftedField q u : LiftedState) = ((iwasawaField q.1 (Φ q.2.1 q.2.2), 0) : LiftedState) +
      (halfPlaneF₁ q.2.1 q.2.2 u • ((0, (1, 0)) : LiftedState) +
        halfPlaneF₂ q.2.1 q.2.2 u • ((0, (0, 1)) : LiftedState)) := by
    ext <;> simp [liftedField]
  rw [controlHamiltonian, e, map_add, map_add, map_smul, map_smul, ← ct_traceForm_lam1 _ _ hΦ,
    planeHamiltonian, liftedCost]
  simp only [traceForm, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul]
  ring

private lemma ct_iwasawaK_mul_neg (θ : ℝ) : iwasawaK θ * iwasawaK (-θ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [iwasawaK, Matrix.mul_apply, ← sq, Real.cos_sq_add_sin_sq, Real.sin_sq_add_cos_sq] <;>
    ring

/-- Every vector of `ℝ³` is `iwasawaField p Y` for a traceless `Y` (the chart is a local
diffeomorphism). -/
private lemma ct_exists_iwasawaField_eq (p w : ℝ × ℝ × ℝ) :
    ∃ Y : Mat2, Y.trace = 0 ∧ iwasawaField p Y = w := by
  set W : Mat2 := !![w.2.1, w.1 * Real.exp (-(2 * p.2.1)) - w.2.2; w.2.2, -w.2.1]
  refine ⟨iwasawaK (-p.2.2) * W * iwasawaK p.2.2, ?_, ?_⟩
  · rw [Matrix.trace_mul_cycle, ct_iwasawaK_mul_neg, Matrix.one_mul]
    simp [W, Matrix.trace_fin_two]
  · have hW : iwasawaK p.2.2 * (iwasawaK (-p.2.2) * W * iwasawaK p.2.2) *
        iwasawaK (-p.2.2) = W := by
      simp only [← Matrix.mul_assoc, ct_iwasawaK_mul_neg, Matrix.one_mul]
      rw [Matrix.mul_assoc, ct_iwasawaK_mul_neg, Matrix.mul_one]
    rw [iwasawaField, hW]
    simp only [W, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    refine Prod.ext ?_ rfl
    simp only [sub_add_cancel, mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      mul_one]

/-- **Nontriviality** (E21): the covector `π` vanishes if `Λ₁` and `Λ_R` do. -/
private lemma ct_eq_zero_of_lam (p : ℝ × ℝ × ℝ) (z : ℝ × ℝ) (hy : 0 < z.2)
    (π : StrongDual ℝ LiftedState) (h1 : ct_lam1 p π = 0) (hR : ct_lamR z π = 0) : π = 0 := by
  have hp : ∀ w : ℝ × ℝ × ℝ, π (w, 0) = 0 := by
    intro w
    obtain ⟨Y, hY, rfl⟩ := ct_exists_iwasawaField_eq p w
    rw [← ct_traceForm_lam1 p π hY, h1]
    simp [traceForm]
  have hν₁ : π (0, (1, 0)) = 0 := by
    have := congrFun (congrFun hR 1) 0
    simpa [ct_lamR] using this
  have hν₂ : π (0, (0, 1)) = 0 := by
    have := congrFun (congrFun hR 0) 0
    simpa [ct_lamR, hν₁, hy.ne'] using this
  refine ContinuousLinearMap.ext fun ⟨w, a, b⟩ ↦ ?_
  have e : ((w, (a, b)) : LiftedState) = ((w, 0) : LiftedState) +
      (a • ((0, (1, 0)) : LiftedState) + b • ((0, (0, 1)) : LiftedState)) := by ext <;> simp
  rw [e, map_add, map_add, map_smul, map_smul, hp, hν₁, hν₂]
  simp

/-! ### The lifted left-invariant fields and their bracket -/

private lemma ct_hasDerivAt_fst {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {γ : ℝ → E × F} {v : E × F} {t : ℝ}
    (h : HasDerivAt γ v t) : HasDerivAt (fun s ↦ (γ s).1) v.1 t :=
  (hasFDerivAt_fst (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t h

private lemma ct_hasDerivAt_snd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {γ : ℝ → E × F} {v : E × F} {t : ℝ}
    (h : HasDerivAt γ v t) : HasDerivAt (fun s ↦ (γ s).2) v.2 t :=
  (hasFDerivAt_snd (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t h

private lemma ct_iwasawaK_mul_J (θ : ℝ) : iwasawaK θ * J = J * iwasawaK θ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [iwasawaK, J, Matrix.mul_apply]

private lemma ct_hasDerivAt_iwasawaK (θ : ℝ) :
    HasDerivAtEntrywise (fun s ↦ iwasawaK s) (J * iwasawaK θ) θ := by
  rw [hasDerivAtEntrywise_fin_two_iff]
  simp only [iwasawaK, J, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.mul_apply,
    Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using Real.hasDerivAt_cos θ
  · simpa using (Real.hasDerivAt_sin θ).fun_neg
  · simpa using Real.hasDerivAt_sin θ
  · simpa using Real.hasDerivAt_cos θ

/-- The derivative of `θ ↦ k_θ Y k_{-θ}` is `[J, k_θ Y k_{-θ}]`. -/
private lemma ct_hasDerivAt_conj (Y : Mat2) (θ : ℝ) :
    HasDerivAtEntrywise (fun s ↦ iwasawaK s * Y * iwasawaK (-s))
      (J * (iwasawaK θ * Y * iwasawaK (-θ)) - iwasawaK θ * Y * iwasawaK (-θ) * J) θ := by
  have h2 : HasDerivAtEntrywise (fun s ↦ iwasawaK (-s)) (-(J * iwasawaK (-θ))) θ :=
    ((ct_hasDerivAt_iwasawaK (-θ)).scomp (h := fun s ↦ -s) (hasDerivAt_neg θ)).congr_deriv
      (by rw [neg_one_smul])
  refine (((ct_hasDerivAt_iwasawaK θ).mul_const Y).mul h2).congr_deriv ?_
  rw [← ct_iwasawaK_mul_J (-θ)]
  noncomm_ring

/-- The derivative of the lifted field `p ↦ iwasawaField p Y` in the direction `v`. -/
private noncomputable def ct_dField (p : ℝ × ℝ × ℝ) (Y : Mat2) (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (2 * v.2.1 * (iwasawaField p Y).1, 0, 0) + v.2.2 • iwasawaField p (J * Y - Y * J)

private lemma ct_hasDerivAt_iwasawaField {γ : ℝ → ℝ × ℝ × ℝ} {v : ℝ × ℝ × ℝ} {t : ℝ}
    (hγ : HasDerivAt γ v t) (Y : Mat2) :
    HasDerivAt (fun s ↦ iwasawaField (γ s) Y) (ct_dField (γ t) Y v) t := by
  have hr : HasDerivAt (fun s ↦ (γ s).2.1) v.2.1 t := ct_hasDerivAt_fst (ct_hasDerivAt_snd hγ)
  have hθ : HasDerivAt (fun s ↦ (γ s).2.2) v.2.2 t := ct_hasDerivAt_snd (ct_hasDerivAt_snd hγ)
  have hW := (ct_hasDerivAt_conj Y (γ t).2.2).scomp hθ
  have hE : HasDerivAt (fun s ↦ Real.exp (2 * (γ s).2.1))
      (Real.exp (2 * (γ t).2.1) * (2 * v.2.1)) t := (hr.const_mul 2).exp
  have hkc : ∀ θ : ℝ, iwasawaK θ * (J * Y - Y * J) * iwasawaK (-θ) =
      J * (iwasawaK θ * Y * iwasawaK (-θ)) - iwasawaK θ * Y * iwasawaK (-θ) * J := by
    intro θ
    rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, ct_iwasawaK_mul_J,
      Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      ← ct_iwasawaK_mul_J (-θ)]
    simp only [Matrix.mul_assoc]
  refine ((hE.fun_mul ((hW 0 1).fun_add (hW 1 0))).prodMk ((hW 0 0).prodMk (hW 1 0))).congr_deriv
    ?_
  simp only [ct_dField, iwasawaField, hkc, Matrix.smul_apply, smul_eq_mul, Prod.smul_mk,
    Prod.mk_add_mk, Matrix.sub_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

private lemma ct_iwasawaK_neg_mul (θ : ℝ) : iwasawaK (-θ) * iwasawaK θ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [iwasawaK, Matrix.mul_apply, ← sq, Real.cos_sq_add_sin_sq, Real.sin_sq_add_cos_sq] <;>
    ring

/-- The algebra behind `ct_dField_bracket`, with `W = K Z K'`, `K' K = 1`, `K` and `K'` commuting
with `J`. -/
private lemma ct_bracket_aux (e : ℝ) (K K' X Y : Mat2) (hKK : K' * K = 1) (hJK : K * J = J * K)
    (hJK' : K' * J = J * K') (hX : X.trace = 0) (hY : Y.trace = 0) :
    ((2 * (K * X * K') 0 0 * (e * ((K * Y * K') 0 1 + (K * Y * K') 1 0)), 0, 0) +
        (K * X * K') 1 0 • (e * ((K * (J * Y - Y * J) * K') 0 1 + (K * (J * Y - Y * J) * K') 1 0),
          (K * (J * Y - Y * J) * K') 0 0, (K * (J * Y - Y * J) * K') 1 0) : ℝ × ℝ × ℝ) -
      ((2 * (K * Y * K') 0 0 * (e * ((K * X * K') 0 1 + (K * X * K') 1 0)), 0, 0) +
        (K * Y * K') 1 0 • (e * ((K * (J * X - X * J) * K') 0 1 + (K * (J * X - X * J) * K') 1 0),
          (K * (J * X - X * J) * K') 0 0, (K * (J * X - X * J) * K') 1 0)) =
      (e * ((K * (X * Y - Y * X) * K') 0 1 + (K * (X * Y - Y * X) * K') 1 0),
        (K * (X * Y - Y * X) * K') 0 0, (K * (X * Y - Y * X) * K') 1 0) := by
  have hconj : ∀ A B : Mat2, K * (A * B - B * A) * K' =
      (K * A * K') * (K * B * K') - (K * B * K') * (K * A * K') := by
    intro A B
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc K' K, hKK, Matrix.one_mul]
    noncomm_ring
  have hJ : ∀ A : Mat2, K * (J * A - A * J) * K' = J * (K * A * K') - (K * A * K') * J := by
    intro A
    calc K * (J * A - A * J) * K' = (K * J) * A * K' - K * A * (J * K') := by noncomm_ring
      _ = _ := by rw [hJK, ← hJK']; noncomm_ring
  have htr : ∀ A : Mat2, A.trace = 0 → (K * A * K') 1 1 = -(K * A * K') 0 0 := by
    intro A hA
    have : (K * A * K').trace = 0 := by
      rw [Matrix.trace_mul_cycle, hKK, Matrix.one_mul, hA]
    rw [Matrix.trace_fin_two] at this
    linarith
  rw [hJ, hJ, hconj]
  have hA := htr X hX
  have hB := htr Y hY
  generalize K * X * K' = A at hA ⊢
  generalize K * Y * K' = B at hB ⊢
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, J, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Prod.smul_mk, Prod.mk_add_mk, Prod.mk_sub_mk, smul_eq_mul, hA, hB]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- **The bracket of the lifted fields**: `[V_X, V_Y] = V_{[X, Y]}` for the lifts
`V_Z(p) = iwasawaField p Z` of the left-invariant fields `g ↦ gZ` (traceless `X`, `Y`). -/
private lemma ct_dField_bracket (p : ℝ × ℝ × ℝ) {X Y : Mat2} (hX : X.trace = 0)
    (hY : Y.trace = 0) :
    ct_dField p Y (iwasawaField p X) - ct_dField p X (iwasawaField p Y) =
      iwasawaField p (X * Y - Y * X) :=
  ct_bracket_aux _ _ _ _ _ (ct_iwasawaK_neg_mul p.2.2) (ct_iwasawaK_mul_J _)
    (ct_iwasawaK_mul_J _) hX hY

/-! ### Calculus tools -/

/-- The derivative of `f` at `x` in the direction `v` is the derivative of `f` along the line
`x + s v`. -/
private lemma ct_fderiv_apply_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x v : E} {f' : F}
    (hf : DifferentiableAt ℝ f x) (h : HasDerivAt (fun s : ℝ ↦ f (x + s • v)) f' 0) :
    fderiv ℝ f x v = f' := by
  have hl : HasDerivAt (fun s : ℝ ↦ x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by simpa using hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt (0 : ℝ) hl).unique h

/-- A curve given by an indefinite integral has the integrand as derivative at almost every
interior point (Lebesgue's differentiation theorem). -/
private lemma ct_ae_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f v : ℝ → E} {T c : ℝ} (hv : IntervalIntegrable v volume 0 T)
    (hc : c ∈ Icc 0 T) {a : E} (hf : ∀ t ∈ Icc 0 T, f t = a + ∫ s in c..t, v s) :
    ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt f (v t) t := by
  have hT : 0 ≤ T := hc.1.trans hc.2
  filter_upwards [IntervalIntegrable.ae_hasDerivAt_integral hv] with t ht htI
  have hIcc : Icc 0 T ⊆ uIcc 0 T := Icc_subset_uIcc
  have h := (ht (hIcc (Ioo_subset_Icc_self htI)) c (hIcc hc)).const_add a
  exact h.congr_of_eventuallyEq (eventually_of_mem (Icc_mem_nhds htI.1 htI.2)
    fun s hs ↦ hf s hs)

/-- **FTC for absolutely continuous functions**, in integral form: an absolutely continuous `f`
with derivative `v` at almost every point of `(0, T)` is the indefinite integral of `v`. -/
private lemma ct_eq_add_integral {f v : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : AbsolutelyContinuousOnInterval f 0 T) (hd : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt f (v t) t) :
    IntervalIntegrable v volume 0 T ∧ ∀ t ∈ Icc 0 T, f t = f 0 + ∫ s in (0 : ℝ)..t, v s := by
  have hae : ∀ᵐ t, t ∈ Ioc 0 T → deriv f t = v t := by
    have hT' : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [hd, hT'] with t ht htT htI
    exact (ht ⟨htI.1, lt_of_le_of_ne htI.2 htT⟩).deriv
  have hint : IntervalIntegrable v volume 0 T := by
    refine (hf.intervalIntegrable_deriv).congr_ae ?_
    rw [uIoc_of_le hT]
    exact (ae_restrict_iff' measurableSet_Ioc).2 hae
  refine ⟨hint, fun t ht ↦ ?_⟩
  have hsub : uIcc 0 t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc_right ht.2
  have h := (hf.mono hsub).integral_deriv_eq_sub
  have h' : ∫ s in (0 : ℝ)..t, v s = ∫ s in (0 : ℝ)..t, deriv f s := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le ht.1]
    filter_upwards [hae] with s hs hst
    exact (hs ⟨hst.1, hst.2.trans ht.2⟩).symm
  rw [h', h]
  ring

/-- A `C¹` function of a curve that is Lipschitz on `[0, T]` is absolutely continuous on
`[0, T]`. -/
private lemma ct_absolutelyContinuous_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Γ : ℝ → F} {K : ℝ≥0} {T : ℝ} (hT : 0 ≤ T) (hΓ : LipschitzOnWith K Γ (Icc 0 T))
    {h : F → ℝ} (hh : ContDiff ℝ 1 h) :
    AbsolutelyContinuousOnInterval (fun t ↦ h (Γ t)) 0 T := by
  have hc : IsCompact (Γ '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hΓ.continuousOn
  obtain ⟨K', hK'⟩ := hh.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hc
  have hL : LipschitzOnWith (K' * K) (fun t ↦ h (Γ t)) (uIcc 0 T) := by
    rw [uIcc_of_le hT]
    exact hK'.comp hΓ (mapsTo_image _ _)
  exact hL.absolutelyContinuousOnInterval

/-- The lifted field `V_Y = iwasawaField · Y` is smooth. -/
private lemma ct_contDiff_iwasawaField (Y : Mat2) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ ↦ iwasawaField p Y) := by
  simp only [iwasawaField, iwasawaK, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Real.cos_neg, Real.sin_neg]
  fun_prop

/-- `(q, π) ↦ π(V_Y(q.1), 0)` is smooth. -/
private lemma ct_contDiff_eval2 (Y : Mat2) :
    ContDiff ℝ 1 (fun w : LiftedState × StrongDual ℝ LiftedState ↦
      w.2 (iwasawaField w.1.1 Y, 0)) := by
  have := ct_contDiff_iwasawaField Y
  fun_prop

/-! ### The adjoint equation in the chart -/

/-- The integrand of the adjoint equation is the derivative of the Hamiltonian
`q' ↦ ⟨π, f(q', u)⟩ + ν φ(q', u)`. -/
private lemma ct_hasFDerivAt_ham {ν : ℝ} {q : LiftedState} {u : Fin 3 → ℝ}
    (hq : q ∈ liftedDomain) (hu : u ∈ controlSimplex) (π : StrongDual ℝ LiftedState) :
    HasFDerivAt (fun q' ↦ π (liftedField q' u) + ν * liftedCost q' u)
      (π.comp (fderiv ℝ (liftedField · u) q) + ν • fderiv ℝ (liftedCost · u) q) q :=
  (π.hasFDerivAt.comp q (isC1On_liftedField.differentiableAt q hq u hu).hasFDerivAt).fun_add
    ((isC1On_liftedCost.differentiableAt q hq u hu).hasFDerivAt.const_mul ν)

/-- The adjoint equation's integrand in the `ℝ³`-directions: `⟨π, ∂_p f(q, u) w⟩ + ν ∂_p φ(q, u) w
= π(D_p V_X(p) w, 0)` with `X = Φ(z)` (the cost and the `z`-dynamics do not depend on `p`). -/
private lemma ct_adjoint_apply_fst {ν : ℝ} {q : LiftedState} {u : Fin 3 → ℝ}
    (hq : q ∈ liftedDomain) (hu : u ∈ controlSimplex) (π : StrongDual ℝ LiftedState)
    (w : ℝ × ℝ × ℝ) :
    (π.comp (fderiv ℝ (liftedField · u) q) + ν • fderiv ℝ (liftedCost · u) q) (w, 0) =
      π (ct_dField q.1 (Φ q.2.1 q.2.2) w, 0) := by
  have hγ : HasDerivAt (fun s : ℝ ↦ q.1 + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add q.1
  have hl : HasDerivAt (fun s : ℝ ↦ ((q.1 + s • w, q.2) : LiftedState)) (w, 0) 0 :=
    hγ.prodMk (hasDerivAt_const _ _)
  have h1 := (ct_hasFDerivAt_ham hq hu π (ν := ν)).comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 : HasDerivAt (fun s : ℝ ↦ π (liftedField (q.1 + s • w, q.2) u) +
      ν * liftedCost (q.1 + s • w, q.2) u) (π (ct_dField q.1 (Φ q.2.1 q.2.2) w, 0)) 0 := by
    have hw := (ct_hasDerivAt_iwasawaField hγ (Φ q.2.1 q.2.2)).prodMk
      (hasDerivAt_const (0 : ℝ) (halfPlaneF₁ q.2.1 q.2.2 u, halfPlaneF₂ q.2.1 q.2.2 u))
    have h := (π.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hw).add_const (ν * liftedCost q u)
    simp only [zero_smul, add_zero] at h
    exact h
  exact h1.unique h2

/-- The adjoint equation's integrand in the direction `∂/∂x`: `-∂H/∂x` with
`H = planeHamiltonian` (Theorem 6.8.2 before the identification `ν = T*Φ(-Λ_R)`). -/
private lemma ct_adjoint_apply_x {ν : ℝ} {q : LiftedState} {u : Fin 3 → ℝ}
    (hq : q ∈ liftedDomain) (hu : u ∈ controlSimplex) (π : StrongDual ℝ LiftedState) :
    (π.comp (fderiv ℝ (liftedField · u) q) + ν • fderiv ℝ (liftedCost · u) q) (0, (1, 0)) =
      deriv (fun ξ ↦ planeHamiltonian ν (ct_lam1 q.1 π) ξ q.2.2 (π (0, (1, 0)))
        (π (0, (0, 1))) u) q.2.1 := by
  have hl : HasDerivAt (fun ξ : ℝ ↦ ((q.1, (ξ, q.2.2)) : LiftedState)) (0, (1, 0)) q.2.1 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _))
  have h := (ct_hasFDerivAt_ham hq hu π (ν := ν)).comp_hasDerivAt_of_eq q.2.1 hl (by simp)
  have e : (fun ξ ↦ planeHamiltonian ν (ct_lam1 q.1 π) ξ q.2.2 (π (0, (1, 0)))
      (π (0, (0, 1))) u) = (fun q' ↦ π (liftedField q' u) + ν * liftedCost q' u) ∘
        (fun ξ : ℝ ↦ ((q.1, (ξ, q.2.2)) : LiftedState)) := by
    funext ξ
    exact (ct_controlHamiltonian_eq ν (q.1, (ξ, q.2.2)) π u).symm
  rw [e, h.deriv]

/-- The adjoint equation's integrand in the direction `∂/∂y`. -/
private lemma ct_adjoint_apply_y {ν : ℝ} {q : LiftedState} {u : Fin 3 → ℝ}
    (hq : q ∈ liftedDomain) (hu : u ∈ controlSimplex) (π : StrongDual ℝ LiftedState) :
    (π.comp (fderiv ℝ (liftedField · u) q) + ν • fderiv ℝ (liftedCost · u) q) (0, (0, 1)) =
      deriv (fun η ↦ planeHamiltonian ν (ct_lam1 q.1 π) q.2.1 η (π (0, (1, 0)))
        (π (0, (0, 1))) u) q.2.2 := by
  have hl : HasDerivAt (fun η : ℝ ↦ ((q.1, (q.2.1, η)) : LiftedState)) (0, (0, 1)) q.2.2 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
  have h := (ct_hasFDerivAt_ham hq hu π (ν := ν)).comp_hasDerivAt_of_eq q.2.2 hl (by simp)
  have e : (fun η ↦ planeHamiltonian ν (ct_lam1 q.1 π) q.2.1 η (π (0, (1, 0)))
      (π (0, (0, 1))) u) = (fun q' ↦ π (liftedField q' u) + ν * liftedCost q' u) ∘
        (fun η : ℝ ↦ ((q.1, (q.2.1, η)) : LiftedState)) := by
    funext η
    exact (ct_controlHamiltonian_eq ν (q.1, (q.2.1, η)) π u).symm
  rw [e, h.deriv]

/-! ### The costate equation for `Λ₁` -/

/-- The entries of `[Λ, X]` through the trace form, for traceless `Λ`, `X`. -/
private lemma ct_bracket_entries {Λ X : Mat2} (hΛ : Λ.trace = 0) (hX : X.trace = 0) :
    (Λ * X - X * Λ) 0 0 = traceForm Λ (X * !![1, 0; 0, -1] - !![1, 0; 0, -1] * X) / 2 ∧
      (Λ * X - X * Λ) 0 1 = traceForm Λ (X * !![0, 0; 1, 0] - !![0, 0; 1, 0] * X) ∧
      (Λ * X - X * Λ) 1 0 = traceForm Λ (X * !![0, 1; 0, 0] - !![0, 1; 0, 0] * X) ∧
      (Λ * X - X * Λ) 1 1 = -(traceForm Λ (X * !![1, 0; 0, -1] - !![1, 0; 0, -1] * X) / 2) := by
  rw [Matrix.trace_fin_two] at hΛ hX
  have h1 : Λ 1 1 = -Λ 0 0 := by linarith
  have h2 : X 1 1 = -X 0 0 := by linarith
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.sub_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, h1, h2]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- **The costate equation `Λ₁' = [Λ₁, X]`** at a time where the state and the costate are
differentiable (Propositions 3.6.1, 6.4.1, 6.5.1 in the chart): for traceless `Y`,
`⟨Λ₁, Y⟩ = π(V_Y(p), 0)` with `V_Y = iwasawaField · Y`, so by the adjoint equation
`⟨Λ₁, Y⟩' = π([V_X, V_Y](p), 0) = π(V_{[X, Y]}(p), 0) = ⟨[Λ₁, X], Y⟩`. -/
private lemma ct_hasDerivAt_lam1 {ν : ℝ} {u : ℝ → Fin 3 → ℝ} {q : ℝ → LiftedState}
    {p : ℝ → StrongDual ℝ LiftedState} {t : ℝ} (hdom : q t ∈ liftedDomain)
    (hu : u t ∈ controlSimplex) (hqt : HasDerivAt q (liftedField (q t) (u t)) t)
    (hpt : HasDerivAt p (-((p t).comp (fderiv ℝ (liftedField · (u t)) (q t)) +
      ν • fderiv ℝ (liftedCost · (u t)) (q t))) t) :
    HasDerivAtEntrywise (fun s ↦ ct_lam1 (q s).1 (p s))
      (ct_lam1 (q t).1 (p t) * Φ (q t).2.1 (q t).2.2 -
        Φ (q t).2.1 (q t).2.2 * ct_lam1 (q t).1 (p t)) t := by
  set Xt := Φ (q t).2.1 (q t).2.2
  have hXtr : Xt.trace = 0 := by simp [Xt, Φ, Matrix.trace_fin_two]; ring
  have hc : ∀ Y : Mat2, Y.trace = 0 → HasDerivAt (fun s ↦ p s (iwasawaField (q s).1 Y, 0))
      (p t (iwasawaField (q t).1 (Xt * Y - Y * Xt), 0)) t := by
    intro Y hY
    have hγ : HasDerivAt (fun s ↦ (q s).1) (iwasawaField (q t).1 Xt) t := ct_hasDerivAt_fst hqt
    have hw : HasDerivAt (fun s ↦ ((iwasawaField (q s).1 Y, (0 : ℝ × ℝ)) : LiftedState))
        (ct_dField (q t).1 Y (iwasawaField (q t).1 Xt), 0) t :=
      (ct_hasDerivAt_iwasawaField hγ Y).prodMk (hasDerivAt_const _ _)
    refine (hpt.clm_apply hw).congr_deriv ?_
    rw [neg_apply, ct_adjoint_apply_fst hdom hu, ← ct_dField_bracket _ hXtr hY]
    have e : ((ct_dField (q t).1 Y (iwasawaField (q t).1 Xt) -
        ct_dField (q t).1 Xt (iwasawaField (q t).1 Y), (0 : ℝ × ℝ)) : LiftedState) =
        ((ct_dField (q t).1 Y (iwasawaField (q t).1 Xt), 0) : LiftedState) -
          ((ct_dField (q t).1 Xt (iwasawaField (q t).1 Y), 0) : LiftedState) := by
      ext <;> simp
    rw [e, map_sub]
    abel
  have hH := hc !![1, 0; 0, -1] (by simp [Matrix.trace_fin_two])
  have hE := hc !![0, 1; 0, 0] (by simp [Matrix.trace_fin_two])
  have hF := hc !![0, 0; 1, 0] (by simp [Matrix.trace_fin_two])
  obtain ⟨e00, e01, e10, e11⟩ := ct_bracket_entries (ct_trace_lam1 (q t).1 (p t)) hXtr
  have tr : ∀ Y : Mat2, Y.trace = 0 → (Xt * Y - Y * Xt).trace = 0 := fun Y _ ↦ by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  rw [hasDerivAtEntrywise_fin_two_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00, ct_traceForm_lam1 _ _ (tr _ (by simp [Matrix.trace_fin_two]))]
    exact hH.div_const 2
  · rw [e01, ct_traceForm_lam1 _ _ (tr _ (by simp [Matrix.trace_fin_two]))]
    exact hF
  · rw [e10, ct_traceForm_lam1 _ _ (tr _ (by simp [Matrix.trace_fin_two]))]
    exact hE
  · rw [e11, ct_traceForm_lam1 _ _ (tr _ (by simp [Matrix.trace_fin_two]))]
    exact (hH.div_const 2).neg

/-! ### The costate equation for `Λ_R` -/

private lemma ct_cotangentNu_sub (x y : ℝ) (A B : Mat2) :
    cotangentNu x y (A - B) = cotangentNu x y A - cotangentNu x y B := by
  simp only [cotangentNu, traceForm, neg_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.neg_mul,
    Matrix.trace_neg, Prod.mk_sub_mk]
  congr 1 <;> ring

/-- The derivative of `s ↦ T*Φ(-Δ(s))` at a time where `Δ` vanishes is `T*Φ(-Δ')`. -/
private lemma ct_hasDerivAt_cotangentNu {x y : ℝ → ℝ} {Δ : ℝ → Mat2} {x' y' t : ℝ}
    {Δ' : Mat2} (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t) (hy0 : y t ≠ 0)
    (hΔ : HasDerivAtEntrywise Δ Δ' t) (hΔ0 : Δ t = 0) :
    HasDerivAt (fun s ↦ cotangentNu (x s) (y s) (Δ s)) (cotangentNu (x t) (y t) Δ') t := by
  have hev : ∀ᶠ s in 𝓝 t, y s ≠ 0 := hy.continuousAt.eventually_ne hy0
  have h2y : 2 * y t ≠ 0 := mul_ne_zero two_ne_zero hy0
  have h1 := (hΔ 1 0).fun_neg
  have h2 := (((hΔ 1 1).fun_sub (hΔ 0 0)).fun_div (hy.const_mul 2) h2y).fun_add
    (((hΔ 1 0).fun_mul hx).fun_div hy hy0)
  refine ((h1.prodMk h2).congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hev] with s hs
    exact ct_cotangentNu_eq _ _ _ hs
  · rw [ct_cotangentNu_eq _ _ _ hy0]
    have e : ∀ i j, Δ t i j = 0 := fun i j ↦ by rw [hΔ0]; rfl
    simp only [e]
    refine Prod.ext rfl ?_
    simp only
    field_simp
    ring

private lemma ct_trace_costateRHS (lam : ℝ) (Λ₁ Λ X : Mat2) (u : Fin 3 → ℝ) :
    (costateRHS lam Λ₁ Λ X u).trace = 0 := by
  unfold costateRHS
  generalize controlP u X = P
  generalize traceForm Λ P = κ
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- `⟨[P, Λ_R] - ⟨Λ_R, P⟩[P, X] + [M, X], X⟩ = -⟨Λ_R, [P, X]⟩`. -/
private lemma ct_traceForm_costateRHS (lam : ℝ) (Λ₁ Λ X : Mat2) (u : Fin 3 → ℝ) :
    traceForm (costateRHS lam Λ₁ Λ X u) X =
      -traceForm Λ (controlP u X * X - X * controlP u X) := by
  unfold costateRHS
  generalize controlP u X = P
  generalize traceForm Λ P = κ
  simp [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **The costate equation for `Λ_R`** at a time where the state, `X` and the costate are
differentiable. The `z`-part `(π(0, e₁), π(0, e₂))` of the costate is `ν = T*Φ(-Λ_R)`
(Lemma 6.8.1), and the adjoint equation says `ν' = -dH` with `H = planeHamiltonian`
(`ct_adjoint_apply_x`, `ct_adjoint_apply_y`). By Theorem 6.8.3, the curve `L` through `Λ_R(t)`
with velocity `C` = the right-hand side of the costate equation has the same `(T*Φ(-L))'` at `t`.
So `T*Φ(-(Λ_R' - C)) = 0`; with `tr(Λ_R' - C) = 0` and `⟨Λ_R' - C, X⟩ = 0` (differentiate
`⟨Λ_R, X⟩ = 0`), `Λ_R' = C`. -/
private lemma ct_hasDerivAt_lamR {ν : ℝ} {u : ℝ → Fin 3 → ℝ} {q : ℝ → LiftedState}
    {p : ℝ → StrongDual ℝ LiftedState} {X : ℝ → Mat2} {t : ℝ} (hdom : q t ∈ liftedDomain)
    (hu : u t ∈ controlSimplex)
    (hev : ∀ᶠ s in 𝓝 t, X s = Φ (q s).2.1 (q s).2.2 ∧ 0 < (q s).2.2)
    (hqt : HasDerivAt q (liftedField (q t) (u t)) t)
    (hpt : HasDerivAt p (-((p t).comp (fderiv ℝ (liftedField · (u t)) (q t)) +
      ν • fderiv ℝ (liftedCost · (u t)) (q t))) t)
    (hXt : HasDerivAtEntrywise X (controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) t) :
    HasDerivAtEntrywise (fun s ↦ ct_lamR (q s).2 (p s))
      (costateRHS ν (ct_lam1 (q t).1 (p t)) (ct_lamR (q t).2 (p t)) (X t) (u t)) t := by
  obtain ⟨hXt0, hy0⟩ := hev.self_of_nhds
  set A := (p t).comp (fderiv ℝ (liftedField · (u t)) (q t)) +
    ν • fderiv ℝ (liftedCost · (u t)) (q t) with hA
  have hx : HasDerivAt (fun s ↦ (q s).2.1) (halfPlaneF₁ (q t).2.1 (q t).2.2 (u t)) t :=
    ct_hasDerivAt_fst (ct_hasDerivAt_snd hqt)
  have hy : HasDerivAt (fun s ↦ (q s).2.2) (halfPlaneF₂ (q t).2.1 (q t).2.2 (u t)) t :=
    ct_hasDerivAt_snd (ct_hasDerivAt_snd hqt)
  have hν₁ : HasDerivAt (fun s ↦ p s (0, (1, 0))) (-A (0, (1, 0))) t := by
    simpa using hpt.clm_apply (hasDerivAt_const t ((0, (1, 0)) : LiftedState))
  have hν₂ : HasDerivAt (fun s ↦ p s (0, (0, 1))) (-A (0, (0, 1))) t := by
    simpa using hpt.clm_apply (hasDerivAt_const t ((0, (0, 1)) : LiftedState))
  -- `Λ_R` is differentiable at `t`
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun s ↦ ct_lamR (q s).2 (p s) i j) t := by
    have h1 := hx.differentiableAt
    have h2 := hy.differentiableAt
    have h3 := hν₁.differentiableAt
    have h4 := hν₂.differentiableAt
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [ct_lamR, neg_add_rev, Fin.mk_one, Fin.isValue, Fin.zero_eta, of_apply, cons_val',
        cons_val_zero, cons_val_one, cons_val_fin_one] <;> fun_prop
  set D : Mat2 := Matrix.of fun i j ↦ deriv (fun s ↦ ct_lamR (q s).2 (p s) i j) t
  have hD : HasDerivAtEntrywise (fun s ↦ ct_lamR (q s).2 (p s)) D t :=
    fun i j ↦ (hdiff i j).hasDerivAt
  set C := costateRHS ν (ct_lam1 (q t).1 (p t)) (ct_lamR (q t).2 (p t)) (X t) (u t)
  -- the auxiliary curve through `Λ_R(t)` with velocity `C`
  set L : ℝ → Mat2 := fun s ↦ ct_lamR (q t).2 (p t) + (s - t) • C with hL_def
  have hL : HasDerivAtEntrywise L C t := by
    intro i j
    have h := (((hasDerivAt_id t).sub_const t).mul_const (C i j)).const_add
      (ct_lamR (q t).2 (p t) i j)
    simpa [hL_def] using h
  have hLt : L t = ct_lamR (q t).2 (p t) := by simp [hL_def]
  -- Theorem 6.8.3 along `(x, y, L)`
  have hthm := theorem6_8_3 ν (u t) (fun s ↦ (q s).2.1) (fun s ↦ (q s).2.2)
    (fun _ ↦ ct_lam1 (q t).1 (p t)) L t hdom.2 hu hx hy
    (by rw [hLt]; exact ct_trace_lamR _ _) (by rw [hLt]; exact ct_traceForm_lamR_Φ _ _ hy0.ne')
    (by rw [hLt, ← hXt0]; exact hL)
  rw [hLt, ct_cotangentNu_lamR _ _ hy0.ne'] at hthm
  -- the derivative of `T*Φ(-Λ_R) = (π(0, e₁), π(0, e₂))`, from the adjoint equation
  have hN : HasDerivAt (fun s ↦ cotangentNu (q s).2.1 (q s).2.2 (ct_lamR (q s).2 (p s)))
      (-A (0, (1, 0)), -A (0, (0, 1))) t := by
    refine (hν₁.prodMk hν₂).congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs
    exact ct_cotangentNu_lamR _ _ hs.2.ne'
  -- the derivative of `T*Φ(-L)`, from Theorem 6.8.3
  have hNL : HasDerivAt (fun s ↦ cotangentNu (q s).2.1 (q s).2.2 (L s))
      (-A (0, (1, 0)), -A (0, (0, 1))) t := by
    rw [hA, ct_adjoint_apply_x hdom hu, ct_adjoint_apply_y hdom hu]
    exact hthm.1.prodMk hthm.2
  -- hence `T*Φ(-(Λ_R' - C)) = 0`
  have hΔ := ct_hasDerivAt_cotangentNu hx hy hy0.ne' (hD.sub hL) (by rw [hLt, sub_self])
  have hΔ' : HasDerivAt (fun s ↦ cotangentNu (q s).2.1 (q s).2.2 (ct_lamR (q s).2 (p s) - L s))
      0 t := by
    have h := hN.sub hNL
    rw [sub_self] at h
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ct_cotangentNu_sub _ _ _ _)
  have hν0 : cotangentNu (q t).2.1 (q t).2.2 (D - C) = 0 := hΔ.unique hΔ'
  -- `tr (Λ_R' - C) = 0`
  have htr : (D - C).trace = 0 := by
    have h11 : D 1 1 = -D 0 0 := by
      refine (hD 1 1).unique ((hD 0 0).fun_neg.congr_of_eventuallyEq
        (Eventually.of_forall fun s ↦ ?_))
      simp [ct_lamR]
    rw [Matrix.trace_sub, ct_trace_costateRHS, Matrix.trace_fin_two, h11]
    ring
  -- `⟨Λ_R' - C, X⟩ = 0`, from `⟨Λ_R, X⟩ = 0` and `X' = [P, X]`
  have hperp : traceForm (D - C) (Φ (q t).2.1 (q t).2.2) = 0 := by
    have h := (hD.mul hXt).trace
    have h0 : HasDerivAt (fun s ↦ (ct_lamR (q s).2 (p s) * X s).trace) 0 t :=
      (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (by
        filter_upwards [hev] with s hs
        rw [hs.1]
        exact ct_traceForm_lamR_Φ _ _ hs.2.ne')
    have e := h.unique h0
    rw [Matrix.trace_add] at e
    have e2 := ct_traceForm_costateRHS ν (ct_lam1 (q t).1 (p t)) (ct_lamR (q t).2 (p t)) (X t) (u t)
    rw [← hXt0, traceForm, Matrix.sub_mul, Matrix.trace_sub]
    simp only [traceForm] at e2
    rw [e2]
    linarith
  have hDC : D = C := sub_eq_zero.1 (ct_eq_zero_of_cotangentNu _ _ _ hy0.ne' htr hν0 hperp)
  rw [← hDC]
  exact hD

/-! ### Transversality for `Λ_R` -/

private lemma ct_det_R : R.det = 1 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp [R, Matrix.det_fin_two]
  linear_combination h3 / 4

/-- `Φ` is injective on `y ≠ 0`. -/
private lemma ct_Φ_injective {z z' : ℝ × ℝ} (hz : z.2 ≠ 0) (h : Φ z.1 z.2 = Φ z'.1 z'.2) :
    z = z' := by
  have h10 : 1 / z.2 = 1 / z'.2 := by simpa [Φ] using congrFun (congrFun h 1) 0
  have h00 : z.1 / z.2 = z'.1 / z'.2 := by simpa [Φ] using congrFun (congrFun h 0) 0
  have hy : z.2 = z'.2 := by
    rw [one_div, one_div, _root_.inv_inj] at h10
    exact h10
  rw [← hy, div_left_inj' hz] at h00
  exact Prod.ext h00 hy

/-- The `z`-part of a covector is `⟨-Λ_R, Y_z(·)⟩` (`ν = T*Φ(-Λ_R)`, `eqn:nu`). -/
private lemma ct_apply_eq_traceForm (z : ℝ × ℝ) (π : StrongDual ℝ LiftedState) (hz : z.2 ≠ 0)
    (w : ℝ × ℝ) : π (0, w) = traceForm (-ct_lamR z π) (tangentLift z.1 z.2 w.1 w.2) := by
  have e : ((0, w) : LiftedState) =
      w.1 • ((0, (1, 0)) : LiftedState) + w.2 • ((0, (0, 1)) : LiftedState) := by
    ext <;> simp
  rw [e, map_add, map_smul, map_smul]
  simp [traceForm, ct_lamR, tangentLift, Matrix.trace_fin_two]
  field_simp
  ring

/-- **The tangent map of `Φ` is equivariant** under the Möbius action of `R⁻¹` (Remark 4.2.2,
Lemma 4.2.4): `[Y_{z'}(M δ), Φ(z')] = R⁻¹ [Y_z(δ), Φ(z)] R` for `z' = R⁻¹ · z` and `M` the
derivative of the Möbius map at `z`. -/
private lemma ct_tangent_mobius {z : ℝ × ℝ} (hz : 0 < z.2)
    (hmob : DifferentiableAt ℝ (mobius R⁻¹) z) (δ : ℝ × ℝ) :
    tangentLift (mobius R⁻¹ z).1 (mobius R⁻¹ z).2 (fderiv ℝ (mobius R⁻¹) z δ).1
          (fderiv ℝ (mobius R⁻¹) z δ).2 * Φ (mobius R⁻¹ z).1 (mobius R⁻¹ z).2 -
        Φ (mobius R⁻¹ z).1 (mobius R⁻¹ z).2 * tangentLift (mobius R⁻¹ z).1 (mobius R⁻¹ z).2
          (fderiv ℝ (mobius R⁻¹) z δ).1 (fderiv ℝ (mobius R⁻¹) z δ).2 =
      R⁻¹ * (tangentLift z.1 z.2 δ.1 δ.2 * Φ z.1 z.2 - Φ z.1 z.2 * tangentLift z.1 z.2 δ.1 δ.2) *
        R := by
  have hRu : IsUnit R.det := by rw [ct_det_R]; exact isUnit_one
  have hdet : R⁻¹.det = 1 := by rw [Matrix.det_nonsing_inv, ct_det_R, Ring.inverse_one]
  have hRR : R⁻¹⁻¹ = R := Matrix.nonsing_inv_nonsing_inv R hRu
  set z' := mobius R⁻¹ z
  set w := fderiv ℝ (mobius R⁻¹) z δ
  have hz' : 0 < z'.2 := (Φ_mobius hdet hz).1
  have hl : HasDerivAt (fun s : ℝ ↦ z + s • δ) δ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add z
  have hm := hmob.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  -- near `s = 0`, `Φ(R⁻¹ · (z + sδ)) = R⁻¹ Φ(z + sδ) R`
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), Φ (mobius R⁻¹ (z + s • δ)).1 (mobius R⁻¹ (z + s • δ)).2 =
      R⁻¹ * Φ (z.1 + s * δ.1) (z.2 + s * δ.2) * R := by
    have hc : ContinuousAt (fun s : ℝ ↦ z.2 + s * δ.2) 0 := by fun_prop
    filter_upwards [hc.eventually (Ioi_mem_nhds (by simpa using hz))] with s hs
    have := (Φ_mobius hdet (z := z + s • δ) (by simpa using hs)).2
    rw [hRR] at this
    simpa using this
  have hR := ((lemma4_2_4 z.1 z.2 δ.1 δ.2 hz).const_mul R⁻¹).mul_const R
  ext i j
  have hΦd : DifferentiableAt ℝ (fun v : ℝ × ℝ ↦ Φ v.1 v.2 i j) z' := by
    have hy : z'.2 ≠ 0 := hz'.ne'
    fin_cases i <;> fin_cases j <;>
      simp only [Φ, neg_add_rev, one_div, Fin.mk_one, Fin.isValue, Fin.zero_eta, of_apply,
        cons_val', cons_val_zero, cons_val_one, cons_val_fin_one] <;> fun_prop (disch := simp [hy])
  -- the chain rule
  have h1 := hΦd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hm (by simp [z'])
  have h2 := h1.unique (((hR i j).congr_of_eventuallyEq (hev.mono fun s hs ↦ by
    simp only [Function.comp_apply]; rw [hs])))
  -- the derivative of `Φ` at `z'` (Lemma 4.2.4)
  have h3 : fderiv ℝ (fun v : ℝ × ℝ ↦ Φ v.1 v.2 i j) z' w =
      (tangentLift z'.1 z'.2 w.1 w.2 * Φ z'.1 z'.2 - Φ z'.1 z'.2 * tangentLift z'.1 z'.2 w.1 w.2)
        i j := by
    refine ct_fderiv_apply_eq hΦd ?_
    simpa using lemma4_2_4 z'.1 z'.2 w.1 w.2 hz' i j
  rw [← h3]
  simpa using h2

/-- **Transversality for `Λ_R`** (§6.6, `eqn:transversality`): the transversality condition
`(-π(0), π(T)) ⊥ ker G'` of the maximum principle for the coupling `z(T) = R⁻¹ · z(0)` gives
`Λ_R(T) = R⁻¹Λ_R(0)R`. For `δ ∈ ℝ²`, `((0, δ), (0, Mδ)) ∈ ker G'` (`M` the derivative of the
Möbius map), so `⟨-Λ_R(0), Y_{z₀}(δ)⟩ = ⟨-Λ_R(T), Y_{z_T}(Mδ)⟩`; by the equivariance of `Φ`,
`Y_{z_T}(Mδ) - R⁻¹Y_{z₀}(δ)R` commutes with `X(T)`, so it is a multiple of `X(T) ⊥ Λ_R(T)`,
and `T*Φ(-Λ_R(0)) = T*Φ(-RΛ_R(T)R⁻¹)` at `z₀`; both lie in `X(0)^⊥` (Lemma 6.8.1). -/
private lemma ct_lamR_transversality {q0 qT : LiftedState} {π0 πT : StrongDual ℝ LiftedState}
    (hy0 : 0 < q0.2.2) (hyT : 0 < qT.2.2)
    (hX : Φ qT.2.1 qT.2.2 = R⁻¹ * Φ q0.2.1 q0.2.2 * R)
    (hT : ∀ v w : LiftedState, fderiv ℝ (liftedBoundary qT.1) (q0, qT) (v, w) = 0 →
      -π0 v + πT w = 0) :
    ct_lamR qT.2 πT = R⁻¹ * ct_lamR q0.2 π0 * R := by
  have hRu : IsUnit R.det := by rw [ct_det_R]; exact isUnit_one
  have hRR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRu
  have hRR' : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRu
  have hdet : R⁻¹.det = 1 := by rw [Matrix.det_nonsing_inv, ct_det_R, Ring.inverse_one]
  have hRinv : R⁻¹⁻¹ = R := Matrix.nonsing_inv_nonsing_inv R hRu
  set G := liftedBoundary qT.1
  have hG : DifferentiableAt ℝ G (q0, qT) :=
    (contDiffAt_liftedBoundary qT.1 (w := (q0, qT)) hy0).differentiableAt one_ne_zero
  -- the Möbius map is differentiable at `z₀` (it is a component of `G`)
  have hmob : DifferentiableAt ℝ (mobius R⁻¹) q0.2 := by
    have e : mobius R⁻¹ = fun w ↦ qT.2 - (G ((q0.1, w), qT)).2.2 := by
      funext w; simp [G, liftedBoundary]
    rw [e]
    have hc : DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ (((q0.1, w), qT) : LiftedState × LiftedState))
        q0.2 := by fun_prop
    exact (differentiableAt_const _).sub (hG.comp q0.2 hc).snd.snd
  set M := fderiv ℝ (mobius R⁻¹) q0.2
  -- `((0, δ), (0, Mδ)) ∈ ker G'`
  have hker : ∀ δ : ℝ × ℝ, fderiv ℝ G (q0, qT) ((0, δ), (0, M δ)) = 0 := by
    intro δ
    refine ct_fderiv_apply_eq hG ?_
    have e : (fun s : ℝ ↦ G ((q0, qT) + s • (((0, δ), (0, M δ)) : LiftedState × LiftedState))) =
        fun s ↦ (q0.1, (0 : ℝ × ℝ × ℝ), (qT.2 + s • M δ) - mobius R⁻¹ (q0.2 + s • δ)) := by
      funext s; simp [G, liftedBoundary]
    rw [e]
    have hl : HasDerivAt (fun s : ℝ ↦ q0.2 + s • δ) δ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add q0.2
    have h1 := hmob.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    have h2 : HasDerivAt (fun s : ℝ ↦ qT.2 + s • M δ) (M δ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (M δ)).const_add qT.2
    have h3 := h2.sub h1
    rw [sub_self] at h3
    exact ((hasDerivAt_const (0 : ℝ) q0.1).prodMk
      ((hasDerivAt_const (0 : ℝ) (0 : ℝ × ℝ × ℝ)).prodMk h3)).congr_deriv
        (by simp only [Prod.mk_zero_zero])
  -- `z(T) = R⁻¹ · z(0)`
  have hzT : qT.2 = mobius R⁻¹ q0.2 := by
    have h := (Φ_mobius hdet hy0).2
    rw [hRinv, ← hX] at h
    exact ct_Φ_injective hyT.ne' h.symm
  set Λ0 := ct_lamR q0.2 π0
  set ΛT := ct_lamR qT.2 πT
  set X0 := Φ q0.2.1 q0.2.2
  set XT := Φ qT.2.1 qT.2.2
  have hXTtr : XT.trace = 0 := by simp [XT, Φ, Matrix.trace_fin_two]; ring
  have hXT0 : XT ≠ 0 := fun h ↦ by
    have := congrFun (congrFun h 1) 0
    simp [XT, Φ, hyT.ne'] at this
  have hperpT : traceForm ΛT XT = 0 := ct_traceForm_lamR_Φ _ _ hyT.ne'
  have htrT : ΛT.trace = 0 := ct_trace_lamR _ _
  set V := R * ΛT * R⁻¹
  -- `⟨-Λ_R(0), Y_{z₀}(δ)⟩ = ⟨-RΛ_R(T)R⁻¹, Y_{z₀}(δ)⟩`
  have key : ∀ δ : ℝ × ℝ, traceForm (-Λ0) (tangentLift q0.2.1 q0.2.2 δ.1 δ.2) =
      traceForm (-V) (tangentLift q0.2.1 q0.2.2 δ.1 δ.2) := by
    intro δ
    set Y0 := tangentLift q0.2.1 q0.2.2 δ.1 δ.2
    set Y1 := tangentLift qT.2.1 qT.2.2 (M δ).1 (M δ).2
    have hT' := hT _ _ (hker δ)
    rw [ct_apply_eq_traceForm _ _ hy0.ne', ct_apply_eq_traceForm _ _ hyT.ne'] at hT'
    have hbr : Y1 * XT - XT * Y1 = R⁻¹ * (Y0 * X0 - X0 * Y0) * R := by
      have h := ct_tangent_mobius hy0 hmob δ
      rw [← hzT] at h
      exact h
    have hY0tr : Y0.trace = 0 := by simp [Y0, tangentLift, Matrix.trace_fin_two]; ring
    have hY1tr : Y1.trace = 0 := by simp [Y1, tangentLift, Matrix.trace_fin_two]; ring
    -- `Y1 - R⁻¹ Y0 R` commutes with `X(T) = R⁻¹ X(0) R`
    obtain ⟨k, hk⟩ := orb_centralizer XT (Y1 - R⁻¹ * Y0 * R) hXTtr hXT0
      (by rw [Matrix.trace_sub, hY1tr, Matrix.trace_mul_cycle, hRR, Matrix.one_mul, hY0tr,
        sub_zero])
      (by
        rw [Matrix.sub_mul, Matrix.mul_sub, sub_sub_sub_comm, hbr, hX]
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc R R⁻¹, hRR, Matrix.one_mul]
        noncomm_ring)
    have hY1 : Y1 = R⁻¹ * Y0 * R + k • XT := by rw [← hk]; abel
    have e1 : traceForm (-ΛT) Y1 = traceForm (-V) Y0 := by
      rw [hY1]
      simp only [traceForm, Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul,
        Matrix.neg_mul, Matrix.trace_neg]
      rw [show (ΛT * XT).trace = 0 from hperpT, neg_zero, smul_zero, add_zero]
      have e : ΛT * (R⁻¹ * Y0 * R) = (ΛT * R⁻¹ * Y0) * R := by simp only [Matrix.mul_assoc]
      rw [e, Matrix.trace_mul_comm]
      simp only [V, Matrix.mul_assoc]
    linarith
  -- so `T*Φ(-(Λ_R(0) - RΛ_R(T)R⁻¹)) = 0` at `z₀`, and `Λ_R(0) = RΛ_R(T)R⁻¹`
  have hΛ : Λ0 - V = 0 := by
    refine ct_eq_zero_of_cotangentNu q0.2.1 q0.2.2 _ hy0.ne' ?_ ?_ ?_
    · rw [Matrix.trace_sub, ct_trace_lamR, Matrix.trace_mul_cycle, hRR', Matrix.one_mul, htrT,
        sub_zero]
    · rw [ct_cotangentNu_sub]
      have k1 := key (1, 0)
      have k2 := key (0, 1)
      simp only [cotangentNu]
      rw [k1, k2, sub_self]
    · rw [traceForm, Matrix.sub_mul, Matrix.trace_sub, ← traceForm, ct_traceForm_lamR_Φ _ _ hy0.ne',
        zero_sub, neg_eq_zero]
      have : (V * X0).trace = traceForm ΛT XT := by
        simp only [V, XT, hX, traceForm, Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
      rw [this, hperpT]
  have hΛ0 : Λ0 = V := sub_eq_zero.1 hΛ
  rw [hΛ0]
  simp only [V, ← Matrix.mul_assoc, hRR', Matrix.one_mul]
  rw [Matrix.mul_assoc, hRR', Matrix.mul_one]

/-! ### The translation -/

/-- **Translation of the costate.** Let `(u, g, X)` be admissible for the Reinhardt problem, `q`
its lift to `ℝ³ × 𝔥*` (`π(q(t).1) = g(t)`, `Φ(q(t).2) = X(t)`, `q(0).1 = 0`), and `(ν, p)` a
multiplier and costate satisfying the conclusions of the maximum principle for the lifted
problem (`External.pontryagin_maximum_principle` with the boundary map
`liftedBoundary (q T).1`). Then the left-trivialized costate `Λ₁` and the reduced costate `Λ_R`
read off from `p` make `(u, g, X, Λ₁, Λ_R, ν)` a Pontryagin extremal.

Proof: see the module docstring, "The translation, step by step" (Propositions 3.6.1, 6.4.1 and
6.5.1 in the chart, Lemma 6.8.1, Theorems 6.8.2, 6.8.3, Corollary 6.5.3 through Remark 6.6.1);
the a.e. derivatives are turned into integral equations by the fundamental theorem of calculus
for absolutely continuous functions. The hypotheses `hq0` and `iwasawa (q t).1 = g t` are not
used: the conditions on `g` come with `h`. -/
theorem isPontryaginExtremal_of_costate {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) {q : ℝ → LiftedState} (hq0 : (q 0).1 = 0)
    (hq : ∀ t ∈ Icc 0 T, iwasawa (q t).1 = g t ∧ Φ (q t).2.1 (q t).2.2 = X t)
    (hadm : IsAdmissibleIn liftedField liftedDomain controlSimplex (q 0) T u q) {ν : ℝ}
    {p : ℝ → StrongDual ℝ LiftedState} (hν : ν ≤ 0) (hlip : ∃ K, LipschitzOnWith K p (Icc 0 T))
    (hN : ∀ t ∈ Icc 0 T, (ν, p t) ≠ 0) (hA : IsAdjoint liftedField liftedCost ν u q T p)
    (hM : IsMaximal liftedField liftedCost ν controlSimplex u q T p)
    (hZ : ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
      controlHamiltonian liftedField liftedCost ν (q t) (p t) (u t) = 0)
    (hT : ∀ v w : LiftedState, fderiv ℝ (liftedBoundary (q T).1) (q 0, q T) (v, w) = 0 →
      -p 0 v + p T w = 0) :
    ∃ Λ₁ ΛR : ℝ → Mat2, IsPontryaginExtremal T u g X Λ₁ ΛR ν := by
  obtain ⟨hst, hg0, hgT, hXT⟩ := h
  have hT0 : 0 < T := hst.1
  have hIcc : ∀ {t : ℝ}, t ∈ Ioo 0 T → t ∈ Icc 0 T := fun ht ↦ Ioo_subset_Icc_self ht
  have hdom : ∀ t ∈ Icc 0 T, q t ∈ liftedDomain := hadm.2
  have huU : ∀ t ∈ Icc 0 T, u t ∈ controlSimplex := hadm.1.2.1
  have hy : ∀ t ∈ Icc 0 T, 0 < (q t).2.2 := fun t ht ↦ (hdom t ht).2.1
  have hX : ∀ t ∈ Icc 0 T, X t = Φ (q t).2.1 (q t).2.2 := fun t ht ↦ (hq t ht).2.symm
  -- `q` and `p` are Lipschitz on `[0, T]`, so the costates are absolutely continuous
  obtain ⟨Kp, hKp⟩ := hlip
  have hKq : IsCompact ((q '' Icc 0 T) ×ˢ controlSimplex) :=
    (isCompact_Icc.image_of_continuousOn hadm.1.2.2.1).prod isCompact_controlSimplex
  obtain ⟨M, hM'⟩ := hKq.exists_bound_of_continuousOn (isC1On_liftedField.continuousOn.mono (by
    rintro ⟨_, v⟩ ⟨⟨s, hs, rfl⟩, hv⟩
    exact ⟨hdom s hs, hv⟩))
  have hqlip : LipschitzOnWith (Real.toNNReal M) q (Icc 0 T) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
    rw [dist_eq_norm, Real.dist_eq]
    refine (hadm.1.norm_sub_le (fun s hs ↦ hM' (q s, u s) ⟨⟨s, hs, rfl⟩, huU s hs⟩) hb ha).trans ?_
    exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal M) (abs_nonneg _)
  have hac : ∀ F : LiftedState × StrongDual ℝ LiftedState → ℝ, ContDiff ℝ 1 F →
      AbsolutelyContinuousOnInterval (fun t ↦ F (q t, p t)) 0 T :=
    fun F hF ↦ ct_absolutelyContinuous_comp hT0.le (hqlip.prodMk hKp) hF
  -- almost everywhere, the state, the costate and `X` are differentiable
  have hq' : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt q (liftedField (q t) (u t)) t :=
    ct_ae_hasDerivAt hadm.1.2.2.2.1 ⟨le_rfl, hT0.le⟩ hadm.1.2.2.2.2
  have hp' : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt p (-((p t).comp (fderiv ℝ (liftedField · (u t)) (q t))
      + ν • fderiv ℝ (liftedCost · (u t)) (q t))) t := by
    refine ct_ae_hasDerivAt (v := fun r ↦ -((p r).comp (linearization liftedField u q r) +
      ν • fderiv ℝ (liftedCost · (u r)) (q r))) hA.1.neg ⟨hT0.le, le_rfl⟩ (a := p T)
      fun t ht ↦ ?_
    rw [hA.2 t ht, intervalIntegral.integral_neg, intervalIntegral.integral_symm]
  have hXd : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAtEntrywise X
      (controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) t := by
    have hXI := hst.2.2.2.2.2
    have h : ∀ i j, ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt (fun s ↦ X s i j)
        ((controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) i j) t :=
      fun i j ↦ ct_ae_hasDerivAt (hXI i j).1 ⟨le_rfl, hT0.le⟩ (hXI i j).2
    filter_upwards [ae_all_iff.2 fun i ↦ ae_all_iff.2 (h i)] with t ht htI i j
    exact ht i j htI
  -- the costate equations, almost everywhere
  have hΛ₁d : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAtEntrywise (fun s ↦ ct_lam1 (q s).1 (p s))
      (ct_lam1 (q t).1 (p t) * X t - X t * ct_lam1 (q t).1 (p t)) t := by
    filter_upwards [hq', hp'] with t hqt hpt htI
    rw [hX t (hIcc htI)]
    exact ct_hasDerivAt_lam1 (hdom t (hIcc htI)) (huU t (hIcc htI)) (hqt htI) (hpt htI)
  have hΛRd : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAtEntrywise (fun s ↦ ct_lamR (q s).2 (p s))
      (costateRHS ν (ct_lam1 (q t).1 (p t)) (ct_lamR (q t).2 (p t)) (X t) (u t)) t := by
    filter_upwards [hq', hp', hXd] with t hqt hpt hXt htI
    refine ct_hasDerivAt_lamR (hdom t (hIcc htI)) (huU t (hIcc htI)) ?_ (hqt htI) (hpt htI)
      (hXt htI)
    filter_upwards [Ioo_mem_nhds htI.1 htI.2] with s hs
    exact ⟨hX s (hIcc hs), hy s (hIcc hs)⟩
  -- in integral form
  have hΛ₁ : IsIntegralCurve (fun t ↦ ct_lam1 (q t).1 (p t))
      (fun t ↦ ct_lam1 (q t).1 (p t) * X t - X t * ct_lam1 (q t).1 (p t)) T := by
    have hF : ∀ i j, ContDiff ℝ 1 (fun w : LiftedState × StrongDual ℝ LiftedState ↦
        ct_lam1 w.1.1 w.2 i j) := by
      have h1 := ct_contDiff_eval2 !![1, 0; 0, -1]
      have h2 := ct_contDiff_eval2 !![0, 1; 0, 0]
      have h3 := ct_contDiff_eval2 !![0, 0; 1, 0]
      intro i j
      fin_cases i <;> fin_cases j
      · exact h1.div_const 2
      · exact h3
      · exact h2
      · exact (h1.div_const 2).neg
    intro i j
    refine ct_eq_add_integral (f := fun t ↦ ct_lam1 (q t).1 (p t) i j)
      (v := fun t ↦ (ct_lam1 (q t).1 (p t) * X t - X t * ct_lam1 (q t).1 (p t)) i j) hT0.le
      (hac (fun w ↦ ct_lam1 w.1.1 w.2 i j) (hF i j)) ?_
    filter_upwards [hΛ₁d] with t ht htI using ht htI i j
  have hΛR : IsIntegralCurve (fun t ↦ ct_lamR (q t).2 (p t))
      (fun t ↦ costateRHS ν (ct_lam1 (q t).1 (p t)) (ct_lamR (q t).2 (p t)) (X t) (u t)) T := by
    have hF : ∀ i j, ContDiff ℝ 1 (fun w : LiftedState × StrongDual ℝ LiftedState ↦
        ct_lamR w.1.2 w.2 i j) := by
      intro i j
      fin_cases i <;> fin_cases j <;>
      simp only [ct_lamR, neg_add_rev, Fin.mk_one, Fin.isValue, Fin.zero_eta, of_apply, cons_val',
        cons_val_zero, cons_val_one, cons_val_fin_one] <;> fun_prop
    intro i j
    refine ct_eq_add_integral (f := fun t ↦ ct_lamR (q t).2 (p t) i j)
      (v := fun t ↦ costateRHS ν (ct_lam1 (q t).1 (p t)) (ct_lamR (q t).2 (p t)) (X t) (u t) i j)
      hT0.le (hac (fun w ↦ ct_lamR w.1.2 w.2 i j) (hF i j)) ?_
    filter_upwards [hΛRd] with t ht htI using ht htI i j
  refine ⟨fun t ↦ ct_lam1 (q t).1 (p t), fun t ↦ ct_lamR (q t).2 (p t), hst, hg0, hgT, hXT,
    ?_, ?_, hν, ?_, hΛ₁, hΛR, ?_⟩
  · -- transversality for `Λ₁`: Remark 6.6.1 (Corollary 6.5.3 and `g(T) = R`)
    exact remark6_6_1_lambda1 hst hg0 hgT hΛ₁
  · -- transversality for `Λ_R`
    rw [hX T ⟨hT0.le, le_rfl⟩, hX 0 ⟨le_rfl, hT0.le⟩] at hXT
    exact ct_lamR_transversality (hy 0 ⟨le_rfl, hT0.le⟩) (hy T ⟨hT0.le, le_rfl⟩) hXT hT
  · intro t ht
    refine ⟨ct_trace_lam1 _ _, ct_trace_lamR _ _, ?_, ?_⟩
    · rw [hX t ht]
      exact ct_traceForm_lamR_Φ _ _ (hy t ht).ne'
    · -- nontriviality (E21)
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2, h3⟩ := hcon
      apply hN t ht
      rw [h1, ct_eq_zero_of_lam _ _ (hy t ht) _ h2 h3]
      rfl
  · -- the maximum condition and `H = 0`
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hM,
      (ae_restrict_iff' measurableSet_Icc).1 hZ] with t hMt hZt htI
    have ht := hIcc htI
    have hH : ∀ v ∈ controlSimplex, hamiltonian ν (ct_lam1 (q t).1 (p t))
        (ct_lamR (q t).2 (p t)) (X t) v =
          controlHamiltonian liftedField liftedCost ν (q t) (p t) v := by
      intro v hv
      rw [hX t ht, theorem6_8_2 ν _ _ _ _ v (hdom t ht).2 hv
        (ct_traceForm_lamR_Φ _ _ (hy t ht).ne'), ct_cotangentNu_lamR _ _ (hy t ht).ne',
        ct_controlHamiltonian_eq]
    refine ⟨by rw [hH _ (huU t ht)]; exact hZt ht, fun v hv ↦ ?_⟩
    rw [hH v hv, hH _ (huU t ht)]
    exact hMt ht v hv

/-- **The global minimizer is a Pontryagin extremal** (`sec:PMP`, label of this formalization:
§6.2 and §6.6 of the book, TeX 4662–4830 and 5157–5215, summarized in Problem 6.7.1 and used in
the proof of Proposition 8.1.3, TeX 6791: "We have seen that the global minimizer must be
extremal"). Every global minimizer `(u, g, X)` of the Reinhardt control problem (Problem 3.6.2)
lifts to a Pontryagin extremal: there are costates `Λ₁, Λ_R` and a multiplier `λ_cost ≤ 0` with
the state–costate equations of Problem 6.7.1, the maximum condition and `H = 0` almost
everywhere, the nontriviality `(λ_cost, Λ₁, Λ_R) ≠ 0` at every time, and the transversality
conditions (6.6.1).

The book applies the maximum principle on `SL₂(ℝ) × 𝔰𝔩₂(ℝ)`; the proof applies it on
`SL₂(ℝ) × 𝔥*` in the chart `ℝ³ × 𝔥*` (see the module docstring and inventory §3.4, E21).

Proof: `IsReinhardtMinimizer.exists_lift`, `External.pontryagin_maximum_principle` (with
`isC1On_liftedField`, `isC1On_liftedCost`, `isCompact_controlSimplex`,
`contDiffAt_liftedBoundary`, `surjective_fderiv_liftedBoundary`), and
`isPontryaginExtremal_of_costate`. -/
theorem exists_isPontryaginExtremal_of_isReinhardtMinimizer {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsReinhardtMinimizer T u g X) :
    ∃ (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ), IsPontryaginExtremal T u g X Λ₁ ΛR lam := by
  obtain ⟨q, hq0, hq, hmin⟩ := h.exists_lift
  have hadm := hmin.2.1
  have hy : 0 < (q 0).2.2 := (hadm.2 0 ⟨le_rfl, hmin.1.le⟩).2.1
  obtain ⟨ν, p, hν, hlip, hN, hA, hM, hZ, hT⟩ :=
    External.pontryagin_maximum_principle isOpen_liftedDomain isCompact_controlSimplex
      isC1On_liftedField isC1On_liftedCost hmin (contDiffAt_liftedBoundary (q T).1 hy)
      (surjective_fderiv_liftedBoundary (q T).1 hy) hmin.2.2.1
      (Eventually.of_forall fun _ hz ↦ hz)
  obtain ⟨Λ₁, ΛR, hext⟩ :=
    isPontryaginExtremal_of_costate h.1 hq0 hq hadm hν hlip hN hA hM hZ hT
  exact ⟨Λ₁, ΛR, ν, hext⟩

end SmoothedPolygons
