module

public import SmoothedPolygons.Ch6.Hamiltonian
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The Hamiltonian and costate equations in the upper half-plane (§6.8)

The cotangent space of the adjoint orbit (Lemma 6.8.1), the covector `ν = T*Φ(-Λ_R)`
(`eqn:nu`), the Hamiltonian in half-plane coordinates (Theorem 6.8.2), and the costate equation
`ν' = -dH` (Theorem 6.8.3).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- The orthogonal complement `X^⊥ = {Y ∈ 𝔰𝔩₂(ℝ) | ⟨Y, X⟩ = 0}` of `X` for the trace form. -/
def perpSl2 (X : Mat2) : Submodule ℝ Mat2 :=
  sl2 ⊓ LinearMap.ker ((Matrix.traceLinearMap (Fin 2) ℝ ℝ).comp (LinearMap.mulRight ℝ X))

/-- **Lemma 6.8.1** (`lem:cotangent-space-OX`). For `X ∈ 𝔰𝔩₂(ℝ)`, `X ≠ 0` (in the book,
`X ∈ O_J`): `X^⊥ = {[W, X] | W ∈ 𝔰𝔩₂(ℝ)}`, and `T*_X O_X ≅ (𝔰𝔩₂(ℝ)/ℝX)* ≅ X^⊥`, the second
isomorphism pairing `Y ∈ X^⊥` with `W + ℝX` by the trace form.

Proof as in the book: `⟨[W, X], X⟩ = ⟨W, [X, X]⟩ = 0` and both spaces have dimension two
(`orb_adImage_eq_perp`); `Y ↦ (W + ℝX ↦ ⟨Y, W⟩)` is well defined since `⟨Y, X⟩ = 0`, injective
since the trace form is nondegenerate on `𝔰𝔩₂(ℝ)`, and `dim X^⊥ = 2 = dim (𝔰𝔩₂(ℝ)/ℝX)*`. -/
theorem lemma6_8_1 (X : Mat2) (hX : X.trace = 0) (hX0 : X ≠ 0) :
    (perpSl2 X : Set Mat2) = adImage X ∧
      ∃ e : perpSl2 X ≃ₗ[ℝ] Module.Dual ℝ (sl2 ⧸ (ℝ ∙ (⟨X, by simpa [sl2] using hX⟩ : sl2))),
        ∀ (Y : perpSl2 X) (W : sl2), e Y (Submodule.Quotient.mk W) = traceForm Y W := by
  -- `X^⊥ = {[W, X]}`: orthogonality `⟨[W, X], X⟩ = 0` and dimension count
  have hperp : perpSl2 X = adImage X := (orb_adImage_eq_perp X hX hX0).symm
  refine ⟨by rw [hperp], ?_⟩
  set L := ℝ ∙ (⟨X, by simpa [sl2] using hX⟩ : sl2)
  -- `Y ∈ X^⊥` pairs with `W + ℝX` by `⟨Y, W⟩`, well defined since `⟨Y, X⟩ = 0`
  have hvan : ∀ Y : perpSl2 X, L ≤ LinearMap.ker (((Matrix.traceLinearMap (Fin 2) ℝ ℝ).comp
      (LinearMap.mulLeft ℝ (Y : Mat2))).comp sl2.subtype) := fun Y ↦ by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    exact Y.2.2
  let F : perpSl2 X →ₗ[ℝ] Module.Dual ℝ (sl2 ⧸ L) :=
    { toFun := fun Y ↦ L.liftQ _ (hvan Y)
      map_add' := fun Y Y' ↦ by
        ext W; simp [Matrix.add_mul]
      map_smul' := fun c Y ↦ by
        ext W; simp }
  -- the trace form is nondegenerate on `𝔰𝔩₂(ℝ)`
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Y hY
    have hW : ∀ W : Mat2, W.trace = 0 → ((Y : Mat2) * W).trace = 0 := fun W hW ↦ by
      have := LinearMap.congr_fun hY (Submodule.Quotient.mk ⟨W, by simpa [sl2] using hW⟩)
      simpa [F] using this
    have hYtr : (Y : Mat2).trace = 0 := Y.2.1
    have h1 := hW !![1, 0; 0, -1] (by simp [trace_fin_two])
    have h2 := hW !![0, 1; 0, 0] (by simp [trace_fin_two])
    have h3 := hW !![0, 0; 1, 0] (by simp [trace_fin_two])
    rw [Matrix.eta_fin_two (Y : Mat2)] at h1 h2 h3
    rw [trace_fin_two] at hYtr
    simp [trace_fin_two] at h1 h2 h3
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  have hdim : Module.finrank ℝ (perpSl2 X) = Module.finrank ℝ (Module.Dual ℝ (sl2 ⧸ L)) := by
    have h := L.finrank_quotient_add_finrank
    rw [orb_finrank_sl2, finrank_span_singleton] at h
    · rw [hperp, orb_finrank_adImage X hX hX0, Subspace.dual_finrank_eq]
      omega
    · exact fun h ↦ hX0 (congrArg Subtype.val h)
  exact ⟨F.linearEquivOfInjective hinj hdim, fun Y W ↦ rfl⟩

/-- The covector `ν = T*Φ(-Λ_R) = ν₁ dx + ν₂ dy ∈ T*_z𝔥` (`eqn:nu`): `ν(r) = ⟨-Λ_R, Y_z(r)⟩`, where
`Y_z(r)` represents `T_zΦ(r)` in `𝔰𝔩₂(ℝ)/ℝX` (Lemma 4.2.4) and `Λ_R ∈ X^⊥ ≅ T*_X O_X`
(Lemma 6.8.1). -/
noncomputable def cotangentNu (x y : ℝ) (ΛR : Mat2) : ℝ × ℝ :=
  (traceForm (-ΛR) (tangentLift x y 1 0), traceForm (-ΛR) (tangentLift x y 0 1))

/-- The Hamiltonian in half-plane coordinates,
`H(Λ₁, x, y, ν₁, ν₂; u) = ⟨Λ₁ - (3/2) λ_cost J, X⟩ + ν₁ f₁ + ν₂ f₂` with `X = Φ(x + iy)`. -/
noncomputable def planeHamiltonian (lam : ℝ) (Λ₁ : Mat2) (x y ν₁ ν₂ : ℝ) (u : Fin 3 → ℝ) : ℝ :=
  traceForm (Λ₁ - (3 / 2 * lam) • J) (Φ x y) + ν₁ * halfPlaneF₁ x y u + ν₂ * halfPlaneF₂ x y u

/-- On the star domain `D = 2ax + b - c(x² + y²) < 0` for `Z_u = [[a, b], [c, -a]]`, `u ∈ U_T`:
`D = u₀(1/3 - x² - y²) + u₁(2x/√3 - 2/3) + u₂(-2x/√3 - 2/3)` and the three coefficients are
negative on `𝔥*`. (`D = y ⟨Z_u, Φ(x + iy)⟩`.) -/
private lemma orb_denom_neg (x y : ℝ) (u : Fin 3 → ℝ) (hxy : (x, y) ∈ starDomain)
    (hu : u ∈ controlSimplex) :
    2 * controlMatrix u 0 0 * x + controlMatrix u 0 1 - controlMatrix u 1 0 * x ^ 2 -
      controlMatrix u 1 0 * y ^ 2 < 0 := by
  obtain ⟨-, hx1, hx2, hr⟩ := hxy
  obtain ⟨hu', hsum⟩ := hu
  have hs : 0 < √3 := by positivity
  have hs2 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have k0 : 1 / 3 - x ^ 2 - y ^ 2 < 0 := by simp only at hr; linarith
  have k1 : 2 * x / √3 - 2 / 3 < 0 := by
    have : x * √3 < 1 := by simp only at hx2; rwa [lt_div_iff₀ hs] at hx2
    rw [div_sub' (by positivity), div_neg_iff]; right; constructor <;> nlinarith
  have k2 : -2 * x / √3 - 2 / 3 < 0 := by
    have : -1 < x * √3 := by
      have h' : -x < 1 / √3 := by simp only at hx1; linarith
      rw [lt_div_iff₀ hs] at h'; linarith
    rw [div_sub' (by positivity), div_neg_iff]; right; constructor <;> nlinarith
  have hD : 2 * controlMatrix u 0 0 * x + controlMatrix u 0 1 - controlMatrix u 1 0 * x ^ 2 -
      controlMatrix u 1 0 * y ^ 2 = u 0 * (1 / 3 - x ^ 2 - y ^ 2) + u 1 * (2 * x / √3 - 2 / 3) +
        u 2 * (-2 * x / √3 - 2 / 3) := by
    simp [controlMatrix]; ring
  rw [hD]
  obtain ⟨h0, -⟩ := hu' 0
  obtain ⟨h1, -⟩ := hu' 1
  obtain ⟨h2, -⟩ := hu' 2
  have e0 := mul_nonpos_of_nonneg_of_nonpos h0 k0.le
  have e1 := mul_nonpos_of_nonneg_of_nonpos h1 k1.le
  have e2 := mul_nonpos_of_nonneg_of_nonpos h2 k2.le
  rcases h0.lt_or_eq with h0 | h0
  · linarith [mul_neg_of_pos_of_neg h0 k0]
  rcases h1.lt_or_eq with h1 | h1
  · linarith [mul_neg_of_pos_of_neg h1 k1]
  have h2 : 0 < u 2 := by linarith
  linarith [mul_neg_of_pos_of_neg h2 k2]

/-- `⟨Z, Φ(x + iy)⟩ = D/y` with `D = 2ax + b - cx² - cy²` for traceless `Z = [[a, b], [c, -a]]`. -/
private lemma orb_traceForm_Φ (Z : Mat2) (hZ : Z 1 1 = -Z 0 0) (x y : ℝ) (hy : y ≠ 0) :
    traceForm Z (Φ x y) = (2 * Z 0 0 * x + Z 0 1 - Z 1 0 * x ^ 2 - Z 1 0 * y ^ 2) / y := by
  rw [traceForm, Matrix.eta_fin_two Z, hZ, Φ]
  simp [trace_fin_two]
  field_simp
  ring

/-- Equation `eqn:tangent-map-f1f2`, computed: for traceless `Z = [[a, b], [c, -a]]` and
`D = 2ax + b - cx² - cy² ≠ 0`, `[Y_z(f₁, f₂), X] = [Z/⟨Z, X⟩, X]` with `X = Φ(x + iy)`. -/
private lemma orb_bracket_tangentLift (x y : ℝ) (Z : Mat2) (hZ : Z 1 1 = -Z 0 0) (hy : y ≠ 0)
    (hD : 2 * Z 0 0 * x + Z 0 1 - Z 1 0 * x ^ 2 - Z 1 0 * y ^ 2 ≠ 0) :
    tangentLift x y (y * (2 * Z 0 0 * x + Z 0 1 - Z 1 0 * x ^ 2 + Z 1 0 * y ^ 2) /
          (2 * Z 0 0 * x + Z 0 1 - Z 1 0 * x ^ 2 - Z 1 0 * y ^ 2))
        (2 * y ^ 2 * (Z 0 0 - Z 1 0 * x) /
          (2 * Z 0 0 * x + Z 0 1 - Z 1 0 * x ^ 2 - Z 1 0 * y ^ 2)) *
          Φ x y -
        Φ x y * tangentLift x y (y * (2 * Z 0 0 * x + Z 0 1 - Z 1 0 * x ^ 2 + Z 1 0 * y ^ 2) /
          (2 * Z 0 0 * x + Z 0 1 - Z 1 0 * x ^ 2 - Z 1 0 * y ^ 2))
        (2 * y ^ 2 * (Z 0 0 - Z 1 0 * x) /
          (2 * Z 0 0 * x + Z 0 1 - Z 1 0 * x ^ 2 - Z 1 0 * y ^ 2)) =
      (traceForm Z (Φ x y))⁻¹ • Z * Φ x y - Φ x y * (traceForm Z (Φ x y))⁻¹ • Z := by
  rw [orb_traceForm_Φ Z hZ x y hy]
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, Z = !![a, b; c, -a] :=
    ⟨Z 0 0, Z 0 1, Z 1 0, by rw [← hZ]; exact Matrix.eta_fin_two Z⟩
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hD ⊢
  ext i j; fin_cases i <;> fin_cases j <;> simp [tangentLift, Φ] <;> field_simp <;> ring

/-- **Theorem 6.8.2** (`thm:plane-hamiltonian`, Hamiltonian in the upper half-plane). With
`ν = T*Φ(-Λ_R)`, the Hamiltonian `H(Λ₁, Λ_R, X; Z_u)` becomes
`⟨Λ₁ - (3/2) λ_cost J, X⟩ + ν₁ f₁ + ν₂ f₂` in half-plane coordinates.

Proof as in the book: `H₂ = ⟨-Λ_R, P⟩ = ⟨-Λ_R, P + ℝX⟩ = ⟨-Λ_R, Y_z(f₁, f₂)⟩ = ν₁ f₁ + ν₂ f₂`,
using `Λ_R ⊥ X` and `TΦ(f₁, f₂) = [P]` (`eqn:tangent-map-f1f2`): `[Y_z(f₁, f₂), X] = [P, X]`, so
`Y_z(f₁, f₂) - P` lies in the centralizer `ℝX` of `X`. The bracket identity is the third conjunct of
Lemma 4.5.2, which is stated along trajectories; here it is checked directly
(`orb_bracket_tangentLift`). The hypothesis `tr Λ_R = 0` is not needed. -/
theorem theorem6_8_2 (lam : ℝ) (Λ₁ ΛR : Mat2) (x y : ℝ) (u : Fin 3 → ℝ)
    (hxy : (x, y) ∈ starDomain) (hu : u ∈ controlSimplex) (hΛ : ΛR.trace = 0)
    (hperp : traceForm ΛR (Φ x y) = 0) :
    hamiltonian lam Λ₁ ΛR (Φ x y) u =
      planeHamiltonian lam Λ₁ x y (cotangentNu x y ΛR).1 (cotangentNu x y ΛR).2 u := by
  have hy : y ≠ 0 := hxy.1.ne'
  have hZ : controlMatrix u 1 1 = -controlMatrix u 0 0 := by simp [controlMatrix]; ring
  have hD := (orb_denom_neg x y u hxy hu).ne
  -- `X = Φ(x + iy)` is a nonzero element of `𝔰𝔩₂(ℝ)`
  have hXtr : (Φ x y).trace = 0 := by simp [Φ, trace_fin_two]; ring
  have hX0 : Φ x y ≠ 0 := fun h ↦ by
    have := congrFun (congrFun h 1) 0
    simp [Φ, hy] at this
  set Y := tangentLift x y (halfPlaneF₁ x y u) (halfPlaneF₂ x y u)
  set P := controlP u (Φ x y)
  -- `eqn:tangent-map-f1f2`: `[Y_z(f₁, f₂), X] = [P, X]`, so `Y_z(f₁, f₂) - P ∈ ℝX`
  have htan : Y * Φ x y - Φ x y * Y = P * Φ x y - Φ x y * P :=
    orb_bracket_tangentLift x y (controlMatrix u) hZ hy hD
  have hYtr : Y.trace = 0 := by simp [Y, tangentLift, trace_fin_two, neg_div]
  have hPtr : P.trace = 0 := by
    simp only [P, controlP, trace_smul, smul_eq_mul]
    rw [(controlMatrix_spec u).1, mul_zero]
  obtain ⟨k, hk⟩ := orb_centralizer (Φ x y) (Y - P) hXtr hX0
    (by rw [trace_sub, hYtr, hPtr, sub_zero])
    (by rw [Matrix.sub_mul, Matrix.mul_sub, sub_sub_sub_comm, htan, sub_self])
  -- `H₂ = ⟨-Λ_R, Z_u/⟨Z_u, X⟩⟩ = ⟨-Λ_R, P + kX⟩ = ⟨-Λ_R, Y_z(f₁, f₂)⟩ = ν₁ f₁ + ν₂ f₂`
  have h1 : traceForm ΛR (controlMatrix u) / traceForm (Φ x y) (controlMatrix u) =
      traceForm ΛR P := by
    simp only [P, controlP, traceForm, Matrix.mul_smul, trace_smul, smul_eq_mul]
    rw [trace_mul_comm (Φ x y), div_eq_inv_mul]
  have h2 : traceForm ΛR P = traceForm ΛR Y := by
    have hP : P = Y - k • Φ x y := by rw [← hk]; abel
    have h0 : (ΛR * Φ x y).trace = 0 := hperp
    rw [hP, traceForm, traceForm, Matrix.mul_sub, trace_sub, Matrix.mul_smul, trace_smul, h0,
      smul_zero, sub_zero]
  have h3 : Y = halfPlaneF₁ x y u • tangentLift x y 1 0 +
      halfPlaneF₂ x y u • tangentLift x y 0 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Y, tangentLift] <;> field_simp
    ring
  rw [hamiltonian, planeHamiltonian, cotangentNu, h1, h2, h3]
  simp only [traceForm, Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, smul_eq_mul,
    Matrix.neg_mul, trace_neg]
  ring

/-- `∂f₁/∂x` for `f₁ = y(2ax + b - cx² + cy²)/D`, `D = 2ax + b - cx² - cy²`. -/
private lemma orb_hasDerivAt_f₁_x (a b c x y : ℝ) (hD : 2 * a * x + b - c * x ^ 2 - c * y ^ 2 ≠ 0) :
    HasDerivAt (fun ξ ↦ y * (2 * a * ξ + b - c * ξ ^ 2 + c * y ^ 2) /
        (2 * a * ξ + b - c * ξ ^ 2 - c * y ^ 2))
      (-4 * c * y ^ 3 * (a - c * x) / (2 * a * x + b - c * x ^ 2 - c * y ^ 2) ^ 2) x := by
  have hl : HasDerivAt (fun ξ : ℝ ↦ 2 * a * ξ + b - c * ξ ^ 2) (2 * a - c * (2 * x)) x := by
    have := (((hasDerivAt_id' x).const_mul (2 * a)).add_const b).sub
      ((hasDerivAt_pow 2 x).const_mul c)
    convert this using 1; simp
  convert ((hl.add_const (c * y ^ 2)).const_mul y).div (hl.sub_const (c * y ^ 2)) hD using 1
  field_simp
  ring

/-- `∂f₂/∂x` for `f₂ = 2y²(a - cx)/D`. -/
private lemma orb_hasDerivAt_f₂_x (a b c x y : ℝ) (hD : 2 * a * x + b - c * x ^ 2 - c * y ^ 2 ≠ 0) :
    HasDerivAt (fun ξ ↦ 2 * y ^ 2 * (a - c * ξ) / (2 * a * ξ + b - c * ξ ^ 2 - c * y ^ 2))
      (2 * y ^ 2 * (-c * (2 * a * x + b - c * x ^ 2 - c * y ^ 2) - 2 * (a - c * x) ^ 2) /
        (2 * a * x + b - c * x ^ 2 - c * y ^ 2) ^ 2) x := by
  have hl : HasDerivAt (fun ξ : ℝ ↦ 2 * a * ξ + b - c * ξ ^ 2) (2 * a - c * (2 * x)) x := by
    have := (((hasDerivAt_id' x).const_mul (2 * a)).add_const b).sub
      ((hasDerivAt_pow 2 x).const_mul c)
    convert this using 1; simp
  have hn : HasDerivAt (fun ξ : ℝ ↦ 2 * y ^ 2 * (a - c * ξ)) (2 * y ^ 2 * (-c)) x := by
    convert (((hasDerivAt_id' x).const_mul c).const_sub a).const_mul (2 * y ^ 2) using 1; ring
  convert hn.div (hl.sub_const (c * y ^ 2)) hD using 1
  field_simp

/-- `∂f₁/∂y`. -/
private lemma orb_hasDerivAt_f₁_y (a b c x y : ℝ) (hD : 2 * a * x + b - c * x ^ 2 - c * y ^ 2 ≠ 0) :
    HasDerivAt (fun η ↦ η * (2 * a * x + b - c * x ^ 2 + c * η ^ 2) /
        (2 * a * x + b - c * x ^ 2 - c * η ^ 2))
      ((2 * a * x + b - c * x ^ 2 + c * y ^ 2) / (2 * a * x + b - c * x ^ 2 - c * y ^ 2) +
        2 * c * y ^ 2 * (2 * (2 * a * x + b - c * x ^ 2)) /
          (2 * a * x + b - c * x ^ 2 - c * y ^ 2) ^ 2) y := by
  have hq : HasDerivAt (fun η : ℝ ↦ c * η ^ 2) (c * (2 * y)) y := by
    convert (hasDerivAt_pow 2 y).const_mul c using 1; simp
  convert ((hasDerivAt_id' y).mul (hq.const_add (2 * a * x + b - c * x ^ 2))).div
    (hq.const_sub (2 * a * x + b - c * x ^ 2)) hD using 1
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- `∂f₂/∂y`. -/
private lemma orb_hasDerivAt_f₂_y (a b c x y : ℝ) (hD : 2 * a * x + b - c * x ^ 2 - c * y ^ 2 ≠ 0) :
    HasDerivAt (fun η ↦ 2 * η ^ 2 * (a - c * x) / (2 * a * x + b - c * x ^ 2 - c * η ^ 2))
      (4 * y * (a - c * x) / (2 * a * x + b - c * x ^ 2 - c * y ^ 2) +
        4 * c * y ^ 3 * (a - c * x) / (2 * a * x + b - c * x ^ 2 - c * y ^ 2) ^ 2) y := by
  have hq : HasDerivAt (fun η : ℝ ↦ c * η ^ 2) (c * (2 * y)) y := by
    convert (hasDerivAt_pow 2 y).const_mul c using 1; simp
  have hn : HasDerivAt (fun η : ℝ ↦ 2 * η ^ 2 * (a - c * x)) (2 * (2 * y) * (a - c * x)) y := by
    convert ((hasDerivAt_pow 2 y).const_mul 2).mul_const (a - c * x) using 1; simp
  convert hn.div (hq.const_sub (2 * a * x + b - c * x ^ 2)) hD using 1
  field_simp
  ring

/-- In coordinates, `ν = T*Φ(-Λ)` is `ν₁ = -Λ₁₀`, `ν₂ = (Λ₁₁ - Λ₀₀)/(2y) + Λ₁₀ x/y`. -/
private lemma orb_cotangentNu_eq (x y : ℝ) (Λ : Mat2) (hy : y ≠ 0) :
    cotangentNu x y Λ = (-Λ 1 0, (Λ 1 1 - Λ 0 0) / (2 * y) + Λ 1 0 * x / y) := by
  rw [Matrix.eta_fin_two Λ]
  simp [cotangentNu, traceForm, tangentLift, trace_fin_two, hy]
  field_simp
  ring

/-- `∂Φ/∂x = [Y_z(1, 0), Φ]` (Lemma 4.2.4). -/
private lemma orb_hasDerivAt_Φ_x (x y : ℝ) (hy : 0 < y) :
    HasDerivAtEntrywise (fun ξ ↦ Φ ξ y)
      (tangentLift x y 1 0 * Φ x y - Φ x y * tangentLift x y 1 0) x := by
  have h : HasDerivAtEntrywise (fun s ↦ Φ (x + s * 1) (y + s * 0))
      (tangentLift x y 1 0 * Φ x y - Φ x y * tangentLift x y 1 0) ((fun ξ : ℝ ↦ ξ - x) x) := by
    simp only [sub_self]; exact lemma4_2_4 x y 1 0 hy
  convert h.scomp (h := fun ξ : ℝ ↦ ξ - x) ((hasDerivAt_id' x).sub_const x) using 1
  · funext ξ; simp
  · simp

/-- `∂Φ/∂y = [Y_z(0, 1), Φ]` (Lemma 4.2.4). -/
private lemma orb_hasDerivAt_Φ_y (x y : ℝ) (hy : 0 < y) :
    HasDerivAtEntrywise (fun η ↦ Φ x η)
      (tangentLift x y 0 1 * Φ x y - Φ x y * tangentLift x y 0 1) y := by
  have h : HasDerivAtEntrywise (fun s ↦ Φ (x + s * 0) (y + s * 1))
      (tangentLift x y 0 1 * Φ x y - Φ x y * tangentLift x y 0 1) ((fun η : ℝ ↦ η - y) y) := by
    simp only [sub_self]; exact lemma4_2_4 x y 0 1 hy
  convert h.scomp (h := fun η : ℝ ↦ η - y) ((hasDerivAt_id' y).sub_const y) using 1
  · funext η; simp
  · simp

/-- **Theorem 6.8.3** (`thm:lamR-dynamics`). The costate equation for `Λ_R` becomes Hamilton's
equation `ν' = -dH = -(∂H/∂x) dx - (∂H/∂y) dy` for `ν = T*Φ(-Λ_R)`, the partial derivatives of
`H(Λ₁, x, y, ν₁, ν₂; u)` being taken with `Λ₁, ν₁, ν₂` fixed. (The book omits the proof.)

The omitted direct calculation: in coordinates `ν₁ = -Λ_R₁₀` and
`ν₂ = (Λ_R₁₁ - Λ_R₀₀)/(2y) + Λ_R₁₀ x/y` (`orb_cotangentNu_eq`), so `ν'` follows from
`x' = f₁`, `y' = f₂`, `Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩[P, X] + [-Λ₁ + (3/2)λ_cost J, X]`; the partial
derivatives of `H` use `∂Φ/∂x = [Y_z(1, 0), Φ]`, `∂Φ/∂y = [Y_z(0, 1), Φ]` (Lemma 4.2.4) and the
partial derivatives of `f₁, f₂`. The two sides agree as rational functions of `x, y`, the entries
of `Λ₁, Λ_R, Z_u` and `λ_cost` once `tr Λ_R = 0` and `⟨Λ_R, X⟩ = 0` are used to eliminate
`Λ_R₁₁` and `Λ_R₀₁`; the denominators `y` and `D = y ⟨Z_u, X⟩` do not vanish on `𝔥*`. -/
theorem theorem6_8_3 (lam : ℝ) (u : Fin 3 → ℝ) (x y : ℝ → ℝ) (Λ₁ ΛR : ℝ → Mat2) (t : ℝ)
    (hxy : (x t, y t) ∈ starDomain) (hu : u ∈ controlSimplex)
    (hx : HasDerivAt x (halfPlaneF₁ (x t) (y t) u) t)
    (hy : HasDerivAt y (halfPlaneF₂ (x t) (y t) u) t)
    (hΛ : (ΛR t).trace = 0) (hperp : traceForm (ΛR t) (Φ (x t) (y t)) = 0)
    (hΛR : HasDerivAtEntrywise ΛR (costateRHS lam (Λ₁ t) (ΛR t) (Φ (x t) (y t)) u) t) :
    HasDerivAt (fun s ↦ (cotangentNu (x s) (y s) (ΛR s)).1)
        (-deriv (fun ξ ↦ planeHamiltonian lam (Λ₁ t) ξ (y t)
          (cotangentNu (x t) (y t) (ΛR t)).1 (cotangentNu (x t) (y t) (ΛR t)).2 u) (x t)) t ∧
      HasDerivAt (fun s ↦ (cotangentNu (x s) (y s) (ΛR s)).2)
        (-deriv (fun η ↦ planeHamiltonian lam (Λ₁ t) (x t) η
          (cotangentNu (x t) (y t) (ΛR t)).1 (cotangentNu (x t) (y t) (ΛR t)).2 u) (y t)) t := by
  have hy0 : 0 < y t := hxy.1
  have hD := (orb_denom_neg (x t) (y t) u hxy hu).ne
  have hZ : controlMatrix u 1 1 = -controlMatrix u 0 0 := by simp [controlMatrix]; ring
  have hev : ∀ᶠ s in nhds t, y s ≠ 0 := hy.continuousAt.eventually_ne hy0.ne'
  set ν₁ := (cotangentNu (x t) (y t) (ΛR t)).1
  set ν₂ := (cotangentNu (x t) (y t) (ΛR t)).2
  set R := costateRHS lam (Λ₁ t) (ΛR t) (Φ (x t) (y t)) u
  -- `ν₁ = -Λ_R₁₀` and `ν₂ = (Λ_R₁₁ - Λ_R₀₀)/(2y) + Λ_R₁₀ x/y` near `t`
  have hν₁ : HasDerivAt (fun s ↦ (cotangentNu (x s) (y s) (ΛR s)).1) (-R 1 0) t := by
    refine (hΛR 1 0).neg.congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs
    rw [orb_cotangentNu_eq _ _ _ hs]
    rfl
  have hν₂ := (((hΛR 1 1).sub (hΛR 0 0)).div (hy.const_mul 2) (by positivity)).add
    (((hΛR 1 0).mul hx).div hy hy0.ne')
  replace hν₂ := hν₂.congr_of_eventuallyEq (f₁ := fun s ↦ (cotangentNu (x s) (y s) (ΛR s)).2) (by
    filter_upwards [hev] with s hs
    rw [orb_cotangentNu_eq _ _ _ hs]
    rfl)
  -- the partial derivatives of `H(Λ₁, x, y, ν₁, ν₂; u)`
  have hHx : HasDerivAt (fun ξ ↦ planeHamiltonian lam (Λ₁ t) ξ (y t) ν₁ ν₂ u) _ (x t) :=
    ((((orb_hasDerivAt_Φ_x (x t) (y t) hy0).const_mul (Λ₁ t - (3 / 2 * lam) • J)).trace).add
      ((orb_hasDerivAt_f₁_x _ _ _ _ _ hD).const_mul ν₁)).add
      ((orb_hasDerivAt_f₂_x _ _ _ _ _ hD).const_mul ν₂)
  have hHy : HasDerivAt (fun η ↦ planeHamiltonian lam (Λ₁ t) (x t) η ν₁ ν₂ u) _ (y t) :=
    ((((orb_hasDerivAt_Φ_y (x t) (y t) hy0).const_mul (Λ₁ t - (3 / 2 * lam) • J)).trace).add
      ((orb_hasDerivAt_f₁_y _ _ _ _ _ hD).const_mul ν₁)).add
      ((orb_hasDerivAt_f₂_y _ _ _ _ _ hD).const_mul ν₂)
  rw [hHx.deriv, hHy.deriv]
  -- the identities: a rational-function identity in the entries, using `tr Λ_R = 0`,
  -- `⟨Λ_R, X⟩ = 0`
  have hs : ΛR t 1 1 = -ΛR t 0 0 := by rw [trace_fin_two] at hΛ; linarith
  have hq : ΛR t 0 1 = ΛR t 1 0 * (x t ^ 2 + y t ^ 2) - 2 * ΛR t 0 0 * x t := by
    rw [traceForm, Matrix.eta_fin_two (ΛR t), hs] at hperp
    simp [Φ, trace_fin_two] at hperp
    field_simp at hperp
    linear_combination hperp
  have hP : controlP u (Φ (x t) (y t)) =
      (y t / (2 * controlMatrix u 0 0 * x t + controlMatrix u 0 1 - controlMatrix u 1 0 * x t ^ 2 -
        controlMatrix u 1 0 * y t ^ 2)) • controlMatrix u := by
    rw [controlP, orb_traceForm_Φ _ hZ _ _ hy0.ne', inv_div]
  obtain ⟨a, b, c, hZeq⟩ : ∃ a b c, controlMatrix u = !![a, b; c, -a] :=
    ⟨_, _, _, by rw [Matrix.eta_fin_two (controlMatrix u), hZ]⟩
  have hy0' := hy0.ne'
  refine ⟨hν₁.congr_deriv ?_, hν₂.congr_deriv ?_⟩
  all_goals
    simp only [ν₁, ν₂, R, orb_cotangentNu_eq _ _ _ hy0.ne', costateRHS, hP, halfPlaneF₁,
      halfPlaneF₂, Pi.sub_apply, Pi.mul_apply]
    rw [hZeq] at hD ⊢
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at hD ⊢
    generalize hDdef : 2 * a * x t + b - c * x t ^ 2 - c * y t ^ 2 = D at hD ⊢
    rw [Matrix.eta_fin_two (ΛR t), Matrix.eta_fin_two (Λ₁ t)]
    simp [traceForm, Φ, tangentLift, J, trace_fin_two, hs, hq]
    field_simp
    subst hDdef
    ring

end SmoothedPolygons
