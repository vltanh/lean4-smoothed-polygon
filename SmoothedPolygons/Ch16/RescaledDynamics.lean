module

public import SmoothedPolygons.Ch16.ClusterCoordinates
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Chapter 16: the rescaled Reinhardt dynamics near the divisor (§16.4.2, part 1)

§16.4.2 of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX 12887–12918: "In Section 14.2, the
asymptotic formulas in `r₀` for the Reinhardt switching functions are functions of rescaled time
`s` … By the earlier asymptotic formulas (adapted to this system of variables), the switching
functions extend analytically to a neighborhood of `r = 0`. When `r = 0`, the Reinhardt switching
function agrees with the Fuller switching function"), in the form the proof of N5 uses: in the
blow-up coordinates `z = (ρ y₁, ρ² y₂, ρ³ y₃)` of §16.4.1 and in rescaled time `s = t/ρ`, the
Reinhardt state–costate vector field and the Reinhardt Hamiltonians converge, as `ρ → 0⁺`, to the
Fuller vector field (13.2.1) and to `24 H_F`, **uniformly in the control `v ∈ U_T`** and in `y` on
compact sets.

* `simplexToUT`: the control `v` of the simplex as the point `Σ_m v_m ζ^m` of the triangle `U_T`
  (the correspondence `e_j ↦ ζ^{j-1}` of TeX 11655–11657, extended affinely);
* `fullerField u y = (-iu, y₁, y₂)`: the Fuller vector field (13.2.1) (`z₁' = -iu`, `z₂' = z₁`,
  `z₃' = z₂`);
* `rescaledField ρ v y`: the Reinhardt vector field `iso_extremalField v` (`λ_cost = -1`) at the
  phase point with Fuller coordinates `(ρ y₁, ρ² y₂, ρ³ y₃)`, read in Fuller coordinates
  (`fullerCoords` is `ℝ`-linear) and rescaled: `d/ds` of `scale ρ⁻¹ ẑ(q(s ρ))`;
* `tendstoUniformlyOn_rescaledField`, `tendstoUniformlyOn_rescaledHam`: the uniform convergence;
* `mapClusterPt_switchAng_mem_sectionZero`: the cluster points of the switching points lie in the
  Fuller section.

The uniformity in `v ∈ U_T` is what makes relaxed (weak-*) limits of the rescaled controls
legitimate: the Reinhardt field depends on `v` through `Z_v/⟨Z_v, X⟩` (not affinely), but its
limit is affine in `u = simplexToUT v`, so a limit of rescaled trajectories is a Fuller trajectory
with the weak limit of the controls (`SmoothedPolygons/Ch16/RescaledLimits.lean`).

## Proofs

The plan was to expand the field with `O(ρ^k)` error terms uniform in `v` (the estimates of
`thm:ode-oh`, TeX 9249–9265). The formal proof makes the expansion exact instead, which gives the
uniformity for free:

* **Exact factorization** (`l6f_phase`): `phaseOfFuller (scale ρ y) = (J + ρA, -(3/2)J + ρ²B,
  ρ³C)` with `A, B, C` explicit and continuous in `(ρ, y)`: the square roots enter only through
  `⟨w⟩ - 1 = |w|²/(⟨w⟩ + 1)`, so `jbr(2ρy₁) = 1 + ρ²α`, `jbr(4iρ²y₂) = 1 + ρ⁴β`, and
  `RR(w, c)/⟨w⟩ = ρ⁴γ`, with `α, β, γ` continuous.
* **The field** (`l6f_field`, bracket algebra): `[Λ₁, X] = ρ K₂` with
  `K₂ = -(3/2)[J, A] + ρ[B, J] + ρ²[B, A]`, and the `Λ_R`-equation is `ρ² K₃` with
  `K₃ = ρ[P, C] - ρ⟨C, P⟩[P, X] - [B, J] - ρ[B, A]`, `P = Z_v/⟨Z_v, X⟩`. Since `cayleyZ` is
  `ℝ`-linear, `rescaledField ρ v y = G(ρ, v, y) := (cayleyZ[P, X]/2, -i cayleyZ K₂/6,
  cayleyZ K₃/12)` for `ρ ≠ 0` (`l6f_rescaledField_eq`).
* **At `ρ = 0`** (`l6f_G_zero`): `X = J`, `P = -(3/2) Z_v` (`⟨Z_v, J⟩ = -2/3` on the simplex),
  and `G(0, v, y) = (-i u, y₁, y₂)`, `u = simplexToUT v`; `G` is continuous at every `(0, v, y)`,
  `v ∈ U_T` (`l6f_continuousAt_G`; `⟨Z_v, J⟩ ≠ 0`).
* **Uniformity** (`l6f_tendstoUniformlyOn`): if `F_ρ = G(ρ, ·)` on a compact `S` for `ρ > 0`
  and `G` is continuous at every `(0, p)`, `p ∈ S`, then `F_ρ → G(0, ·)` uniformly on `S`
  (locally uniform convergence plus compactness, `tendstoLocallyUniformlyOn_iff_filter`). Applied
  on `U_T × K`.
* **The Hamiltonian** (`l6f_ham_eq`, `l6f_GH_zero`): `H(Z_v)/ρ³ = 3ρβ + ⟨B, A⟩ -
  ⟨C, Z_v⟩/⟨X, Z_v⟩` exactly (`⟨B, J⟩ = 3ρ²β`), which is `24 H_F(y, simplexToUT v)` at `ρ = 0`.
* **The cluster points** (`mapClusterPt_switchAng_mem_sectionZero`): at a switching time the two
  vertices adjacent to the switch maximize the Hamiltonian over the vertices, with value `0` (the
  maximum condition and `H = 0` almost everywhere on each side, and continuity of `H(e_k)` along
  the lift, `IsExtremalOn.exists_phaseHam_eq_zero_of_isSwitchingTime`). Writing the switching point
  as `phaseOfFuller (scale r_n ξ_n)`, dividing by `r_n³` and passing to the limit along a
  subsequence `ξ_n → ξ` (`tendstoUniformlyOn_rescaledHam` on `U_T × Ξ`), the vector
  `(24 H_F(ξ, ζ^k))_k` lies in the closed set of vectors with entries `≤ 0` and two zero entries:
  two vertices maximize (`ξ₃ ∈ 𝒲`, `mem_walls_of_maximizers`) and `H_F⁺(ξ) = 0`.

## Not formalized

The book's further claims of §16.4.2 — the third `s`-derivative of the rescaled switching
functions is nonzero for small `r`, so they "behave qualitatively like a monic cubic polynomial"
(at most three zeros, TeX 12888–12902), Weierstrass preparation at the roots, the Reinhardt cells
`𝒞_k^R`, parts `𝒟_i^R` and branch maps (TeX 12919–12987) — are not used by the proof of N5: the
zero count bounds the zeros of one constant-control piece, not the number of pieces (the third
derivative of `χ_ij` along the true trajectory changes sign with the control), and the
relaxed-limit argument needs neither cells nor Weierstrass polynomials.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology
open TriFuller

/-- A control `v` of the simplex as the point `Σ_m v_m ζ^m` of the triangle `U_T` (the vertex
`e_{m+1}` corresponds to `ζ^m`, TeX 11655–11657). -/
noncomputable def simplexToUT (v : Fin 3 → ℝ) : ℂ := ∑ m : Fin 3, (v m : ℂ) * ζ ^ (m : ℕ)

/-- The Fuller vector field (13.2.1) (TeX 10683–10696) with control `u`:
`(z₁, z₂, z₃)' = (-iu, z₁, z₂)`. -/
noncomputable def fullerField (u : ℂ) (y : Fin 3 → ℂ) : Fin 3 → ℂ := ![-I * u, y 0, y 1]

/-- The rescaled Reinhardt vector field: the state–costate field `iso_extremalField v`
(`λ_cost = -1`) at the phase point with Fuller coordinates `(ρ y₁, ρ² y₂, ρ³ y₃)`, in Fuller
coordinates, for the rescaled variables `y = scale ρ⁻¹ ẑ` and the rescaled time `s = t/ρ`. -/
noncomputable def rescaledField (ρ : ℝ) (v : Fin 3 → ℝ) (y : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ρ • scale ρ⁻¹ (fullerCoords (iso_extremalField v (phaseOfFuller (scale ρ y))))


/-! ### Helpers: the phase point in blow-up coordinates

With `w = 2ρy₁`, `b = 4iρ²y₂`, `c = 12ρ³y₃` (`phaseOfFuller (scale ρ y)`):
`X = J + ρA`, `Λ₁ = -(3/2)J + ρ²B`, `Λ_R = ρ³C`, where `A`, `B`, `C` are continuous in `(ρ, y)`
(the square roots enter through `⟨w⟩ - 1 = |w|²/(⟨w⟩ + 1)`). -/

/-- `⟨w⟩² = 1 + |w|²`. -/
private lemma l6f_jbr_sq (w : ℂ) : jbr w ^ 2 = 1 + ‖w‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

private lemma l6f_one_le_jbr (w : ℂ) : 1 ≤ jbr w :=
  Real.one_le_sqrt.2 (by nlinarith [norm_nonneg w])

/-- `⟨w⟩ - 1 = |w|²/(⟨w⟩ + 1)`. -/
private lemma l6f_jbr_sub_one (w : ℂ) : jbr w = 1 + ‖w‖ ^ 2 / (jbr w + 1) := by
  have h1 := l6f_one_le_jbr w
  have h2 := l6f_jbr_sq w
  field_simp
  nlinarith

/-- `jbr(2ρy₁) - 1 = ρ² α`. -/
private noncomputable def l6f_α (ρ : ℝ) (y : Fin 3 → ℂ) : ℝ :=
  4 * ‖y 0‖ ^ 2 / (jbr (2 * ((ρ : ℂ) * y 0)) + 1)

/-- `jbr(4iρ²y₂) - 1 = ρ⁴ β`. -/
private noncomputable def l6f_β (ρ : ℝ) (y : Fin 3 → ℂ) : ℝ :=
  16 * ‖y 1‖ ^ 2 / (jbr (4 * I * ((ρ : ℂ) ^ 2 * y 1)) + 1)

/-- `RR(2ρy₁, 12ρ³y₃)/jbr(2ρy₁) = ρ⁴ γ`. -/
private noncomputable def l6f_γ (ρ : ℝ) (y : Fin 3 → ℂ) : ℝ :=
  24 * RR (y 0) (y 2) / jbr (2 * ((ρ : ℂ) * y 0))

/-- `X = J + ρ A`. -/
private noncomputable def l6f_A (ρ : ℝ) (y : Fin 3 → ℂ) : Mat2 :=
  !![2 * (y 0).im, 2 * (y 0).re - ρ * l6f_α ρ y; 2 * (y 0).re + ρ * l6f_α ρ y, -(2 * (y 0).im)]

/-- `Λ₁ = -(3/2) J + ρ² B`. -/
private noncomputable def l6f_B (ρ : ℝ) (y : Fin 3 → ℂ) : Mat2 :=
  !![6 * (y 1).re, -(6 * (y 1).im) + 3 / 2 * (ρ ^ 2 * l6f_β ρ y);
    -(6 * (y 1).im) - 3 / 2 * (ρ ^ 2 * l6f_β ρ y), -(6 * (y 1).re)]

/-- `Λ_R = ρ³ C`. -/
private noncomputable def l6f_C (ρ : ℝ) (y : Fin 3 → ℂ) : Mat2 :=
  !![12 * (y 2).im, 12 * (y 2).re - ρ * l6f_γ ρ y; 12 * (y 2).re + ρ * l6f_γ ρ y,
    -(12 * (y 2).im)]

private lemma l6f_jbr0 (ρ : ℝ) (y : Fin 3 → ℂ) :
    jbr (2 * ((ρ : ℂ) * y 0)) = 1 + ρ ^ 2 * l6f_α ρ y := by
  have h := l6f_jbr_sub_one (2 * ((ρ : ℂ) * y 0))
  have hn : ‖2 * ((ρ : ℂ) * y 0)‖ ^ 2 = 4 * ρ ^ 2 * ‖y 0‖ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
    norm_num
    ring
  rw [hn] at h
  rw [l6f_α]
  linear_combination h

private lemma l6f_jbr1 (ρ : ℝ) (y : Fin 3 → ℂ) :
    jbr (4 * I * ((ρ : ℂ) ^ 2 * y 1)) = 1 + ρ ^ 4 * l6f_β ρ y := by
  have h := l6f_jbr_sub_one (4 * I * ((ρ : ℂ) ^ 2 * y 1))
  have hn : ‖4 * I * ((ρ : ℂ) ^ 2 * y 1)‖ ^ 2 = 16 * ρ ^ 4 * ‖y 1‖ ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    norm_num
    ring
  rw [hn] at h
  rw [l6f_β]
  linear_combination h

private lemma l6f_RR02 (ρ : ℝ) (y : Fin 3 → ℂ) :
    RR (2 * ((ρ : ℂ) * y 0)) (12 * ((ρ : ℂ) ^ 3 * y 2)) / jbr (2 * ((ρ : ℂ) * y 0)) =
      ρ ^ 4 * l6f_γ ρ y := by
  have hj : jbr (2 * ((ρ : ℂ) * y 0)) ≠ 0 := by linarith [l6f_one_le_jbr (2 * ((ρ : ℂ) * y 0))]
  rw [l6f_γ, mul_div_assoc', eq_div_iff hj, div_mul_cancel₀ _ hj]
  simp only [RR_eq_re_mul_add_im_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The phase point in blow-up coordinates**: `phaseOfFuller (scale ρ y) =
(J + ρA, -(3/2)J + ρ²B, ρ³C)`. -/
private lemma l6f_phase (ρ : ℝ) (y : Fin 3 → ℂ) :
    phaseOfFuller (scale ρ y) =
      (J + ρ • l6f_A ρ y, (-(3 / 2) : ℝ) • J + ρ ^ 2 • l6f_B ρ y, ρ ^ 3 • l6f_C ρ y) := by
  have e0 := l6f_jbr0 ρ y
  have e1 := l6f_jbr1 ρ y
  have e2 := l6f_RR02 ρ y
  simp only [phaseOfFuller, scale, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [e2, e0, e1]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [l6f_A, l6f_B, l6f_C, J, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow] <;> ring

/-! ### Helpers: the rescaled field in closed form -/

private lemma l6f_continuous_cayleyZ : Continuous cayleyZ := by
  have : cayleyZ = fun M : Mat2 ↦ (((M 0 1 + M 1 0) / 2 : ℝ) : ℂ) + (M 0 0 : ℂ) * I :=
    funext cayleyZ_eq
  rw [this]
  fun_prop

/-- **The state–costate field at `(J + ρA, -(3/2)J + ρ²B, ρ³C)`** (`λ_cost = -1`): `[Λ₁, X]` is
`ρ` times `K₂ = -(3/2)[J, A] + ρ[B, J] + ρ²[B, A]` and the `Λ_R`-equation is `ρ²` times
`K₃ = ρ[P, C] - ρ⟨C, P⟩[P, X] - [B, J] - ρ[B, A]`. -/
private lemma l6f_field (ρ : ℝ) (v : Fin 3 → ℝ) (A B C : Mat2) :
    iso_extremalField v (J + ρ • A, (-(3 / 2) : ℝ) • J + ρ ^ 2 • B, ρ ^ 3 • C) =
      (controlP v (J + ρ • A) * (J + ρ • A) - (J + ρ • A) * controlP v (J + ρ • A),
        ρ • ((-(3 / 2) : ℝ) • (J * A - A * J) + ρ • (B * J - J * B) + ρ ^ 2 • (B * A - A * B)),
        ρ ^ 2 • (ρ • (controlP v (J + ρ • A) * C - C * controlP v (J + ρ • A)) -
          (ρ * traceForm C (controlP v (J + ρ • A))) •
            (controlP v (J + ρ • A) * (J + ρ • A) - (J + ρ • A) * controlP v (J + ρ • A)) -
          (B * J - J * B) - ρ • (B * A - A * B))) := by
  set P := controlP v (J + ρ • A) with hP
  simp only [iso_extremalField, costateRHS, ← hP]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
    module
  · simp only [traceForm_smul_left, add_mul, mul_add, neg_mul, mul_neg,
      smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, neg_add, neg_smul]
    module

/-- The state `X = J + ρ A`. -/
private noncomputable def l6f_Xm (ρ : ℝ) (y : Fin 3 → ℂ) : Mat2 := J + ρ • l6f_A ρ y

/-- `K₂ = -(3/2)[J, A] + ρ[B, J] + ρ²[B, A]`. -/
private noncomputable def l6f_K2 (ρ : ℝ) (y : Fin 3 → ℂ) : Mat2 :=
  (-(3 / 2) : ℝ) • (J * l6f_A ρ y - l6f_A ρ y * J) + ρ • (l6f_B ρ y * J - J * l6f_B ρ y) +
    ρ ^ 2 • (l6f_B ρ y * l6f_A ρ y - l6f_A ρ y * l6f_B ρ y)

/-- `K₃ = ρ[P, C] - ρ⟨C, P⟩[P, X] - [B, J] - ρ[B, A]`. -/
private noncomputable def l6f_K3 (ρ : ℝ) (v : Fin 3 → ℝ) (y : Fin 3 → ℂ) : Mat2 :=
  ρ • (controlP v (l6f_Xm ρ y) * l6f_C ρ y - l6f_C ρ y * controlP v (l6f_Xm ρ y)) -
    (ρ * traceForm (l6f_C ρ y) (controlP v (l6f_Xm ρ y))) •
      (controlP v (l6f_Xm ρ y) * l6f_Xm ρ y - l6f_Xm ρ y * controlP v (l6f_Xm ρ y)) -
    (l6f_B ρ y * J - J * l6f_B ρ y) - ρ • (l6f_B ρ y * l6f_A ρ y - l6f_A ρ y * l6f_B ρ y)

/-- The rescaled field in closed form, continuous at `ρ = 0`. -/
private noncomputable def l6f_G (q : ℝ × (Fin 3 → ℝ) × (Fin 3 → ℂ)) : Fin 3 → ℂ :=
  ![cayleyZ (controlP q.2.1 (l6f_Xm q.1 q.2.2) * l6f_Xm q.1 q.2.2 -
      l6f_Xm q.1 q.2.2 * controlP q.2.1 (l6f_Xm q.1 q.2.2)) / 2,
    -I * cayleyZ (l6f_K2 q.1 q.2.2) / 6, cayleyZ (l6f_K3 q.1 q.2.1 q.2.2) / 12]

private lemma l6f_rescaledField_eq {ρ : ℝ} (hρ : ρ ≠ 0) (v : Fin 3 → ℝ) (y : Fin 3 → ℂ) :
    rescaledField ρ v y = l6f_G (ρ, v, y) := by
  rw [rescaledField, l6f_phase, l6f_field]
  have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ
  funext j
  fin_cases j <;>
    simp only [fullerCoords, scale, l6f_G, l6f_Xm, l6f_K2, l6f_K3, cayleyZ_smul,
      Pi.smul_apply, Complex.real_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Complex.ofReal_inv,
      Complex.ofReal_pow, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    field_simp

/-! ### Helpers: the values at `ρ = 0` -/

private lemma l6f_sqrt3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

private lemma l6f_simplexToUT_re (v : Fin 3 → ℝ) :
    (simplexToUT v).re = v 0 - v 1 / 2 - v 2 / 2 := by
  simp [simplexToUT, Fin.sum_univ_three, ζ_re, ζ_sq_re]
  ring

private lemma l6f_simplexToUT_im (v : Fin 3 → ℝ) :
    (simplexToUT v).im = √3 / 2 * (v 1 - v 2) := by
  simp [simplexToUT, Fin.sum_univ_three, ζ_im, ζ_sq_im]
  ring

private lemma l6f_Xm_zero (y : Fin 3 → ℂ) : l6f_Xm 0 y = J := by simp [l6f_Xm]

/-- `⟨Z_v, J⟩ = -2/3` on the simplex. -/
private lemma l6f_traceForm_J {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) :
    traceForm (controlMatrix v) J = -2 / 3 := by
  have h := hv.2
  simp [traceForm, controlMatrix, J, Matrix.trace_fin_two]
  linarith

private lemma l6f_controlP_J {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) :
    controlP v J = (-(3 / 2) : ℝ) • controlMatrix v := by
  rw [controlP, l6f_traceForm_J hv]
  norm_num

private lemma l6f_A_zero (y : Fin 3 → ℂ) :
    l6f_A 0 y = !![2 * (y 0).im, 2 * (y 0).re; 2 * (y 0).re, -(2 * (y 0).im)] := by
  simp [l6f_A]

private lemma l6f_B_zero (y : Fin 3 → ℂ) :
    l6f_B 0 y = !![6 * (y 1).re, -(6 * (y 1).im); -(6 * (y 1).im), -(6 * (y 1).re)] := by
  simp [l6f_B]

private lemma l6f_C_zero (y : Fin 3 → ℂ) :
    l6f_C 0 y = !![12 * (y 2).im, 12 * (y 2).re; 12 * (y 2).re, -(12 * (y 2).im)] := by
  simp [l6f_C]

/-- **The rescaled field at `ρ = 0` is the Fuller field** with control `simplexToUT v`. -/
private lemma l6f_G_zero {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) (y : Fin 3 → ℂ) :
    l6f_G (0, v, y) = fullerField (simplexToUT v) y := by
  have h3 := l6f_sqrt3
  have hs3 : √3 ≠ 0 := by positivity
  funext j
  fin_cases j
  · simp only [l6f_G, l6f_Xm_zero, l6f_controlP_J hv, fullerField, Matrix.cons_val_zero,
      Fin.zero_eta]
    apply Complex.ext
    · simp [cayleyZ, controlMatrix, J, l6f_simplexToUT_im]
      field_simp
      have h3' : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      linear_combination (-4 * (v 1 - v 2)) * h3'
    · simp [cayleyZ, controlMatrix, J, l6f_simplexToUT_re]
      have := hv.2
      linarith
  · simp only [l6f_G, l6f_K2, l6f_A_zero, l6f_B_zero, fullerField, Matrix.cons_val_one,
      Fin.mk_one]
    apply Complex.ext <;>
      simp [cayleyZ, J] <;> ring
  · simp only [l6f_G, l6f_K3, l6f_A_zero, l6f_B_zero, l6f_C_zero, fullerField,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Fin.reduceFinMk]
    apply Complex.ext <;>
      simp [cayleyZ, J] <;> ring

/-! ### Helpers: continuity at `ρ = 0` -/

private lemma l6f_continuous_jbr : Continuous jbr := by
  unfold jbr
  fun_prop

private lemma l6f_continuous_α : Continuous fun q : ℝ × (Fin 3 → ℂ) ↦ l6f_α q.1 q.2 := by
  unfold l6f_α
  have := l6f_continuous_jbr
  refine Continuous.div (by fun_prop) (by fun_prop) fun q ↦ ?_
  linarith [l6f_one_le_jbr (2 * ((q.1 : ℂ) * q.2 0))]

private lemma l6f_continuous_β : Continuous fun q : ℝ × (Fin 3 → ℂ) ↦ l6f_β q.1 q.2 := by
  unfold l6f_β
  have := l6f_continuous_jbr
  refine Continuous.div (by fun_prop) (by fun_prop) fun q ↦ ?_
  linarith [l6f_one_le_jbr (4 * I * ((q.1 : ℂ) ^ 2 * q.2 1))]

private lemma l6f_continuous_γ : Continuous fun q : ℝ × (Fin 3 → ℂ) ↦ l6f_γ q.1 q.2 := by
  unfold l6f_γ
  have := l6f_continuous_jbr
  refine Continuous.div (by unfold RR; fun_prop) (by fun_prop) fun q ↦ ?_
  linarith [l6f_one_le_jbr (2 * ((q.1 : ℂ) * q.2 0))]

private lemma l6f_continuous_A : Continuous fun q : ℝ × (Fin 3 → ℂ) ↦ l6f_A q.1 q.2 := by
  have := l6f_continuous_α
  refine continuous_matrix fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp only [l6f_A, Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> fun_prop

private lemma l6f_continuous_B : Continuous fun q : ℝ × (Fin 3 → ℂ) ↦ l6f_B q.1 q.2 := by
  have := l6f_continuous_β
  refine continuous_matrix fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp only [l6f_B, Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> fun_prop

private lemma l6f_continuous_C : Continuous fun q : ℝ × (Fin 3 → ℂ) ↦ l6f_C q.1 q.2 := by
  have := l6f_continuous_γ
  refine continuous_matrix fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp only [l6f_C, Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> fun_prop

private lemma l6f_continuous_controlMatrix : Continuous controlMatrix := by
  refine continuous_matrix fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp only [controlMatrix, Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
    fun_prop

/-- The parameter space `(ρ, v, y)`. -/
private abbrev l6f_Q : Type := ℝ × (Fin 3 → ℝ) × (Fin 3 → ℂ)

private lemma l6f_continuous_traceForm {f g : l6f_Q → Mat2} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun q ↦ traceForm (f q) (g q) :=
  (hf.mul hg).matrix_trace

/-- The continuous building blocks of `l6f_G` and `l6f_GH`. -/
private lemma l6f_blocks :
    Continuous (fun q : l6f_Q ↦ l6f_A q.1 q.2.2) ∧ Continuous (fun q : l6f_Q ↦ l6f_B q.1 q.2.2) ∧
      Continuous (fun q : l6f_Q ↦ l6f_C q.1 q.2.2) ∧
      Continuous (fun q : l6f_Q ↦ l6f_Xm q.1 q.2.2) ∧
      Continuous (fun q : l6f_Q ↦ controlMatrix q.2.1) ∧
      Continuous (fun q : l6f_Q ↦ l6f_β q.1 q.2.2) := by
  have hp : Continuous fun q : l6f_Q ↦ (q.1, q.2.2) :=
    continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  have hA := l6f_continuous_A.comp hp
  refine ⟨hA, l6f_continuous_B.comp hp, l6f_continuous_C.comp hp,
    continuous_const.add (continuous_fst.smul hA),
    l6f_continuous_controlMatrix.comp (continuous_fst.comp continuous_snd),
    l6f_continuous_β.comp hp⟩

/-- `P = Z_v/⟨Z_v, X⟩` is continuous at `(0, v, y)`, `v ∈ U_T` (`⟨Z_v, J⟩ = -2/3`). -/
private lemma l6f_continuousAt_P {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) (y : Fin 3 → ℂ) :
    ContinuousAt (fun q : l6f_Q ↦ controlP q.2.1 (l6f_Xm q.1 q.2.2)) (0, v, y) ∧
      traceForm (l6f_Xm 0 y) (controlMatrix v) ≠ 0 := by
  obtain ⟨-, -, -, hX, hZ, -⟩ := l6f_blocks
  have hne : traceForm (controlMatrix v) (l6f_Xm 0 y) ≠ 0 := by
    rw [l6f_Xm_zero, l6f_traceForm_J hv]; norm_num
  have hinv : ContinuousAt
      (fun q : l6f_Q ↦ (traceForm (controlMatrix q.2.1) (l6f_Xm q.1 q.2.2))⁻¹) (0, v, y) :=
    (l6f_continuous_traceForm hZ hX).continuousAt.inv₀ hne
  refine ⟨hinv.smul hZ.continuousAt, ?_⟩
  rw [poly_traceForm_comm]
  exact hne

private lemma l6f_continuousAt_G {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) (y : Fin 3 → ℂ) :
    ContinuousAt l6f_G (0, v, y) := by
  obtain ⟨hA, hB, hC, hX, -, -⟩ := l6f_blocks
  have hP := (l6f_continuousAt_P hv y).1
  have hcz := l6f_continuous_cayleyZ
  have hJ : Continuous fun _ : l6f_Q ↦ J := continuous_const
  have h0 : ContinuousAt (fun q : l6f_Q ↦ controlP q.2.1 (l6f_Xm q.1 q.2.2) * l6f_Xm q.1 q.2.2 -
      l6f_Xm q.1 q.2.2 * controlP q.2.1 (l6f_Xm q.1 q.2.2)) (0, v, y) :=
    (hP.mul hX.continuousAt).sub (hX.continuousAt.mul hP)
  have h2 : Continuous fun q : l6f_Q ↦ l6f_K2 q.1 q.2.2 := by
    unfold l6f_K2
    exact (((continuous_const : Continuous fun _ : l6f_Q ↦ (-(3 / 2) : ℝ)).smul
      ((hJ.mul hA).sub (hA.mul hJ))).add
      (continuous_fst.smul ((hB.mul hJ).sub (hJ.mul hB)))).add
      ((continuous_fst.pow 2).smul ((hB.mul hA).sub (hA.mul hB)))
  have h3 : ContinuousAt (fun q : l6f_Q ↦ l6f_K3 q.1 q.2.1 q.2.2) (0, v, y) := by
    unfold l6f_K3
    have hPC : ContinuousAt (fun q : l6f_Q ↦ traceForm (l6f_C q.1 q.2.2)
        (controlP q.2.1 (l6f_Xm q.1 q.2.2))) (0, v, y) :=
      (continuous_id.matrix_trace).continuousAt.comp (hC.continuousAt.mul hP)
    exact (((continuous_fst.continuousAt.smul
      ((hP.mul hC.continuousAt).sub (hC.continuousAt.mul hP))).sub
      ((continuous_fst.continuousAt.mul hPC).smul h0)).sub
      ((hB.mul hJ).sub (hJ.mul hB)).continuousAt).sub
      (continuous_fst.smul ((hB.mul hA).sub (hA.mul hB))).continuousAt
  refine continuousAt_pi.2 fun j ↦ ?_
  fin_cases j
  · exact (hcz.continuousAt.comp h0).div_const 2
  · exact (continuousAt_const.mul (hcz.comp h2).continuousAt).div_const 6
  · exact (hcz.continuousAt.comp h3).div_const 12

/-! ### Helpers: the rescaled Hamiltonian -/

/-- The rescaled Hamiltonian `H(Z_v)/ρ³` in closed form:
`3ρβ + ⟨B, A⟩ - ⟨C, Z_v⟩/⟨X, Z_v⟩`. -/
private noncomputable def l6f_GH (q : l6f_Q) : ℝ :=
  3 * q.1 * l6f_β q.1 q.2.2 + traceForm (l6f_B q.1 q.2.2) (l6f_A q.1 q.2.2) -
    traceForm (l6f_C q.1 q.2.2) (controlMatrix q.2.1) /
      traceForm (l6f_Xm q.1 q.2.2) (controlMatrix q.2.1)

private lemma l6f_ham_eq {ρ : ℝ} (hρ : ρ ≠ 0) (v : Fin 3 → ℝ) (y : Fin 3 → ℂ) :
    phaseHam (phaseOfFuller (scale ρ y)) v / ρ ^ 3 = l6f_GH (ρ, v, y) := by
  rw [phaseHam, l6f_phase]
  simp only [hamiltonian]
  have e1 : ((-(3 / 2) : ℝ) • J + ρ ^ 2 • l6f_B ρ y) - (3 / 2 * -1 : ℝ) • J =
      ρ ^ 2 • l6f_B ρ y := by module
  have eBJ : traceForm (l6f_B ρ y) J = 3 * ρ ^ 2 * l6f_β ρ y := by
    simp [traceForm, l6f_B, J, Matrix.trace_fin_two]
    ring
  have e2 : traceForm (ρ ^ 2 • l6f_B ρ y) (J + ρ • l6f_A ρ y) =
      ρ ^ 3 * (3 * ρ * l6f_β ρ y + traceForm (l6f_B ρ y) (l6f_A ρ y)) := by
    rw [traceForm_smul_left]
    simp only [traceForm, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
      smul_eq_mul]
    rw [show (l6f_B ρ y * J).trace = traceForm (l6f_B ρ y) J from rfl, eBJ]
    ring
  rw [e1, e2, traceForm_smul_left, l6f_GH]
  simp only [l6f_Xm]
  field_simp

private lemma l6f_continuousAt_GH {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) (y : Fin 3 → ℂ) :
    ContinuousAt l6f_GH (0, v, y) := by
  obtain ⟨hA, hB, hC, hX, hZ, hβ⟩ := l6f_blocks
  have hne := (l6f_continuousAt_P hv y).2
  unfold l6f_GH
  exact (((continuous_const.mul continuous_fst).mul hβ).add
    (l6f_continuous_traceForm hB hA)).continuousAt.sub
    ((l6f_continuous_traceForm hC hZ).continuousAt.div
      (l6f_continuous_traceForm hX hZ).continuousAt hne)

/-- **The rescaled Hamiltonian at `ρ = 0` is `24 H_F`.** -/
private lemma l6f_GH_zero {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) (y : Fin 3 → ℂ) :
    l6f_GH (0, v, y) = 24 * ham y (simplexToUT v) := by
  have h3' : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3 : √3 ≠ 0 := by positivity
  have hJZ : traceForm J (controlMatrix v) = -2 / 3 := by
    rw [traceForm, Matrix.trace_mul_comm]; exact l6f_traceForm_J hv
  simp only [l6f_GH, l6f_Xm_zero, hJZ, l6f_A_zero, l6f_B_zero, l6f_C_zero, mul_zero, zero_mul,
    zero_add]
  simp [traceForm, controlMatrix, Matrix.trace_fin_two, ham,
    RR_eq_re_mul_add_im_mul, l6f_simplexToUT_re, l6f_simplexToUT_im]
  field_simp
  linear_combination (-24 * (y 2).im * (v 1 - v 2)) * h3'

/-! ### Helper: uniform limits from continuity at `ρ = 0` -/

/-- **Uniform convergence on a compact set from a continuous extension**: if `F ρ = G(ρ, ·)` on
`S` for `ρ > 0`, `G(0, ·) = f` on `S` and `G` is continuous at every `(0, p)`, `p ∈ S`, then
`F ρ → f` uniformly on `S` as `ρ → 0⁺`. -/
private lemma l6f_tendstoUniformlyOn {α E : Type*} [TopologicalSpace α] [UniformSpace E]
    {F : ℝ → α → E} {f : α → E} {S : Set α} (hS : IsCompact S) (G : ℝ × α → E)
    (hFG : ∀ ρ > 0, ∀ p ∈ S, F ρ p = G (ρ, p)) (hG0 : ∀ p ∈ S, G (0, p) = f p)
    (hGc : ∀ p ∈ S, ContinuousAt G (0, p)) : TendstoUniformlyOn F f (𝓝[>] 0) S := by
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS,
    tendstoLocallyUniformlyOn_iff_filter]
  intro x hx
  rw [tendstoUniformlyOnFilter_iff_tendsto]
  have hle : 𝓝[>] (0 : ℝ) ×ˢ 𝓝[S] x ≤ 𝓝 ((0 : ℝ), x) := by
    rw [nhds_prod_eq]; exact Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds
  have hev : ∀ᶠ q : ℝ × α in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[S] x, 0 < q.1 ∧ q.2 ∈ S :=
    Filter.mem_of_superset (prod_mem_prod self_mem_nhdsWithin self_mem_nhdsWithin)
      fun q hq ↦ hq
  have h1 : Tendsto (fun q : ℝ × α ↦ F q.1 q.2) (𝓝[>] 0 ×ˢ 𝓝[S] x) (𝓝 (G (0, x))) := by
    refine ((hGc x hx).tendsto.mono_left hle).congr' ?_
    filter_upwards [hev] with q hq
    exact (hFG q.1 hq.1 q.2 hq.2).symm
  have hc : ContinuousAt (fun p ↦ G (0, p)) x :=
    (hGc x hx).comp (continuous_const.prodMk continuous_id).continuousAt
  have h2 : Tendsto (fun q : ℝ × α ↦ f q.2) (𝓝[>] 0 ×ˢ 𝓝[S] x) (𝓝 (G (0, x))) := by
    refine ((hc.tendsto.mono_left nhdsWithin_le_nhds).comp tendsto_snd).congr' ?_
    filter_upwards [hev] with q hq
    exact hG0 q.2 hq.2
  exact (h2.prodMk_nhds h1).mono_right (nhds_le_uniformity _)

/-- **The rescaled Reinhardt vector field converges to the Fuller vector field, uniformly in the
control** (§16.4.2, TeX 12908–12918, with the estimates of `thm:ode-oh`, TeX 9249–9265, for
triangular control): on `U_T × K`, `K` compact,
`rescaledField ρ v y → fullerField (simplexToUT v) y` uniformly as `ρ → 0⁺`. -/
theorem tendstoUniformlyOn_rescaledField {K : Set (Fin 3 → ℂ)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun ρ (p : (Fin 3 → ℝ) × (Fin 3 → ℂ)) ↦ rescaledField ρ p.1 p.2)
      (fun p ↦ fullerField (simplexToUT p.1) p.2) (𝓝[>] 0) (controlSimplex ×ˢ K) :=
  l6f_tendstoUniformlyOn (isCompact_controlSimplex.prod hK) l6f_G
    (fun _ hρ p _ ↦ l6f_rescaledField_eq hρ.ne' p.1 p.2) (fun p hp ↦ l6f_G_zero hp.1 p.2)
    (fun p hp ↦ l6f_continuousAt_G hp.1 p.2)

/-- **The rescaled Reinhardt Hamiltonians converge to the Fuller Hamiltonian, uniformly in the
control** (TeX 11651–11658 and the remark after (11.2.6), in blow-up coordinates):
`H(Z_v)/ρ³ → 24 H_F(y, simplexToUT v)` uniformly on `U_T × K` as `ρ → 0⁺`. -/
theorem tendstoUniformlyOn_rescaledHam {K : Set (Fin 3 → ℂ)} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun ρ (p : (Fin 3 → ℝ) × (Fin 3 → ℂ)) ↦ phaseHam (phaseOfFuller (scale ρ p.2)) p.1 / ρ ^ 3)
      (fun p ↦ 24 * ham p.2 (simplexToUT p.1)) (𝓝[>] 0) (controlSimplex ×ˢ K) :=
  l6f_tendstoUniformlyOn (isCompact_controlSimplex.prod hK) l6f_GH
    (fun _ hρ p _ ↦ l6f_ham_eq hρ.ne' p.1 p.2) (fun p hp ↦ l6f_GH_zero hp.1 p.2)
    (fun p hp ↦ l6f_continuousAt_GH hp.1 p.2)


/-! ### Helpers: the Fuller section -/

/-- The vertices of the simplex are mapped to the cube roots of unity. -/
theorem simplexToUT_vertex (k : Fin 3) : simplexToUT (vertex k) = ζ ^ (k : ℕ) := by
  fin_cases k <;> simp [simplexToUT, vertex, Fin.sum_univ_three]

private lemma l6f_continuous_ham (c : ℂ) : Continuous fun w : Fin 3 → ℂ ↦ ham w c := by
  unfold ham RR
  fun_prop

/-- Two distinct vertices tying at `H_F = 0 = H_F⁺` put `ξ` in the Fuller section. -/
private lemma l6f_mem_sectionZero {ξ : Fin 3 → ℂ} (hξ : ξ ≠ 0) (hle : ∀ x ∈ VT, ham ξ x ≤ 0)
    {u v : ℂ} (hu : u ∈ VT) (hv : v ∈ VT) (huv : u ≠ v) (hu0 : ham ξ u = 0)
    (hv0 : ham ξ v = 0) : ξ ∈ sectionZero := by
  have key : ∀ w ∈ VT, ham ξ w = 0 → ∀ x ∈ VT, RR (ξ 2) x ≤ RR (ξ 2) w := by
    intro w _ hw0 x hx
    have h := hle x hx
    rw [← hw0] at h
    simp only [ham, add_le_add_iff_left] at h
    rw [RR_comm (ξ 2) x, RR_comm (ξ 2) w]
    exact h
  refine ⟨hξ, mem_walls_of_maximizers hu hv huv (key u hu hu0) (key v hv hv0), ?_⟩
  rw [hamMax_eq_of_forall_le hu fun x hx ↦ (hle x hx).trans hu0.ge, hu0]

/-- Two zero entries make the pairwise products vanish. -/
private lemma l6f_pairs {x : Fin 3 → ℝ} {i j : Fin 3} (hij : i ≠ j) (hi : x i = 0)
    (hj : x j = 0) : x 0 * x 1 = 0 ∧ x 1 * x 2 = 0 ∧ x 0 * x 2 = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all

private lemma l6f_ζ_ne : ζ ≠ 1 ∧ ζ ^ 2 ≠ 1 ∧ ζ ≠ ζ ^ 2 := by
  have h3 : 0 < √3 := by positivity
  refine ⟨ζ_ne_one, fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congrArg Complex.re h
    rw [ζ_sq_re, Complex.one_re] at this
    norm_num at this
  · have := congrArg Complex.im h
    rw [ζ_im, ζ_sq_im] at this
    linarith

/-- **The cluster points of the switching points lie in the Fuller section** (TeX 13028–13036:
"Consider the set of cluster points on the exceptional divisor, viewed as a union of the two big
cells"): along a chattering arc, every cluster point `ξ` of the angular components `ξ_n` of the
switching points has `ξ₃` on a wall and `H_F⁺(ξ) = 0` (the limits, after rescaling by `ρ³`, of the
tie of the two maximizing vertices at a switching time and of `H = 0`;
`tendstoUniformlyOn_rescaledHam`, `mem_walls_of_maximizers`).

Proof: write the switching point `q_n = phaseOfFuller (scale r_n ξ_n)`, `r_n = φ(ẑ(q_n)) → 0⁺`
(`IsChatteringArcInto.switchPoints`, `phaseOfFuller_fullerCoords`). At `τ_n` the two adjacent
vertices `e_i`, `e_j` maximize `H` over the vertices with value `0`
(`IsExtremalOn.exists_phaseHam_eq_zero_of_isSwitchingTime`); after division
by `r_n³` the vector `h_n = (H(q_n, e_k)/r_n³)_k` lies in the closed set of vectors with entries
`≤ 0` and two zero entries (pairwise products `0`). Along a subsequence `ξ_n → ξ`,
`h_n → (24 H_F(ξ, ζ^k))_k` (`tendstoUniformlyOn_rescaledHam` on `U_T × Ξ`, `Ξ` compact), so two
distinct vertices maximize `H_F(ξ, ·)` with value `0`: `H_F⁺(ξ) = 0` and `ξ₃ ∈ 𝒲`
(`mem_walls_of_maximizers`). -/
theorem mapClusterPt_switchAng_mem_sectionZero {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ)
    {ξ : Fin 3 → ℂ} (hξ : MapClusterPt ξ atTop (switchAng X Λ₁ ΛR τ)) : ξ ∈ sectionZero := by
  obtain ⟨hblow, -, hne, hlim, hXi⟩ := h.switchPoints
  obtain ⟨hext, -, -, -, -, hmem, -, hiff⟩ := h
  set ξs := switchAng X Λ₁ ΛR τ with hξs
  set r : ℕ → ℝ := fun n ↦ weightedNorm (fullerCoords (phaseAt X Λ₁ ΛR (τ n))) with hrdef
  have hr : ∀ n, 0 < r n := fun n ↦ weightedNorm_pos (hne n)
  have hr0 : Tendsto r atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hr⟩
    have := (continuous_weightedNorm.tendsto 0).comp hlim
    rwa [weightedNorm_zero] at this
  have hq : ∀ n, phaseAt X Λ₁ ΛR (τ n) = phaseOfFuller (scale (r n) (ξs n)) := by
    intro n
    rw [hξs, switchAng, scale_weightedNorm_ang (hne n),
      phaseOfFuller_fullerCoords (hblow _ (Ioo_subset_Icc_self (hmem n)))]
  -- the rescaled Hamiltonians of the vertices
  set hv : ℕ → Fin 3 → ℝ := fun n k ↦
    phaseHam (phaseOfFuller (scale (r n) (ξs n))) (vertex k) / r n ^ 3 with hvdef
  set C : Set (Fin 3 → ℝ) := {x | (∀ k, x k ≤ 0) ∧ x 0 * x 1 = 0 ∧ x 1 * x 2 = 0 ∧
    x 0 * x 2 = 0} with hCdef
  have hC : IsClosed C := by
    have h1 : IsClosed {x : Fin 3 → ℝ | ∀ k, x k ≤ 0} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun k ↦ isClosed_le (continuous_apply k) continuous_const
    have h2 : IsClosed {x : Fin 3 → ℝ | x 0 * x 1 = 0 ∧ x 1 * x 2 = 0 ∧ x 0 * x 2 = 0} :=
      (isClosed_eq (by fun_prop) continuous_const).inter
        ((isClosed_eq (by fun_prop) continuous_const).inter
          (isClosed_eq (by fun_prop) continuous_const))
    exact h1.inter h2
  have hvC : ∀ n, hv n ∈ C := by
    intro n
    obtain ⟨i, j, hij, hle, hi, hj⟩ :=
      IsExtremalOn.exists_phaseHam_eq_zero_of_isSwitchingTime hext (hmem n) ((hiff (τ n) (hmem n)).2
          ⟨n, rfl⟩)
    rw [hq n] at hle hi hj
    have hzi : hv n i = 0 := by simp [hvdef, hi]
    have hzj : hv n j = 0 := by simp [hvdef, hj]
    exact ⟨fun k ↦ div_nonpos_of_nonpos_of_nonneg (hle k) (pow_pos (hr n) 3).le,
      l6f_pairs hij hzi hzj⟩
  -- the limit along a subsequence
  obtain ⟨φ, hφ, hξφ⟩ := hξ.tendsto_subseq
  have hU := tendstoUniformlyOn_iff_tendsto.1 (tendstoUniformlyOn_rescaledHam isCompact_Xi)
  have hlimk : ∀ k : Fin 3,
      Tendsto (fun n ↦ hv (φ n) k) atTop (𝓝 (24 * ham ξ (ζ ^ (k : ℕ)))) := by
    intro k
    have hg : Tendsto (fun n ↦ (r (φ n), (vertex k, ξs (φ n)))) atTop
        (𝓝[>] 0 ×ˢ 𝓟 (controlSimplex ×ˢ Xi)) :=
      (hr0.comp hφ.tendsto_atTop).prodMk
        (tendsto_principal.2 (Eventually.of_forall fun n ↦ ⟨poly_vertex_mem k, hXi (φ n)⟩))
    have hf : Tendsto (fun n ↦ 24 * ham (ξs (φ n)) (simplexToUT (vertex k))) atTop
        (𝓝 (24 * ham ξ (simplexToUT (vertex k)))) :=
      (((l6f_continuous_ham _).tendsto ξ).comp hξφ).const_mul 24
    have := hf.congr_uniformity (hU.comp hg)
    rwa [simplexToUT_vertex] at this
  have hT : Tendsto (fun n ↦ hv (φ n)) atTop (𝓝 (fun k : Fin 3 ↦ 24 * ham ξ (ζ ^ (k : ℕ)))) :=
    tendsto_pi_nhds.2 hlimk
  have hCξ : (fun k : Fin 3 ↦ 24 * ham ξ (ζ ^ (k : ℕ))) ∈ C :=
    hC.mem_of_tendsto hT (Eventually.of_forall fun n ↦ hvC (φ n))
  have hξXi : ξ ∈ Xi :=
    (isClosed_eq continuous_weightedNorm continuous_const).mem_of_tendsto hξφ
      (Eventually.of_forall fun n ↦ hXi (φ n))
  obtain ⟨hle, h01, h12, h02⟩ := hCξ
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one] at hle h01 h12 h02
  have hle' : ∀ x ∈ VT, ham ξ x ≤ 0 := by
    intro x hx
    rcases mem_VT.1 hx with rfl | rfl | rfl
    · have := hle 0; simp at this; linarith
    · have := hle 1; simp at this; linarith
    · have := hle 2; simp at this; linarith
  have hξ0 := ne_zero_of_mem_Xi hξXi
  obtain ⟨n1, n2, n12⟩ := l6f_ζ_ne
  rcases mul_eq_zero.1 h01 with e0 | e1
  · have e0' : ham ξ 1 = 0 := by linarith
    rcases mul_eq_zero.1 h12 with e1 | e2
    · exact l6f_mem_sectionZero hξ0 hle' one_mem_VT ζ_mem_VT (Ne.symm n1) e0' (by linarith)
    · exact l6f_mem_sectionZero hξ0 hle' one_mem_VT ζ_sq_mem_VT (Ne.symm n2) e0' (by linarith)
  · rcases mul_eq_zero.1 h02 with e0 | e2
    · exact l6f_mem_sectionZero hξ0 hle' one_mem_VT ζ_mem_VT (Ne.symm n1) (by linarith)
        (by linarith)
    · exact l6f_mem_sectionZero hξ0 hle' ζ_mem_VT ζ_sq_mem_VT n12 (by linarith) (by linarith)

end SmoothedPolygons
