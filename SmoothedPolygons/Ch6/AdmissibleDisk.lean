module

public import SmoothedPolygons.Ch6.Winding
public import SmoothedPolygons.Ch7.SmoothedPolygonDisk
public import SmoothedPolygons.Ch6.MatrixMinimizer

/-!
# The disk bounded by an admissible trajectory of winding number one (E15)

Problem 3.6.2 opens with "The convex disks in `𝔎_bal` in circle representation arise via the
following optimal control problem" (TeX 3205). Its converse, that an admissible trajectory bounds a
balanced disk whose area is the cost, is used without proof at TeX 4579 (§6.1: "By
Theorem 5.0.2, we may assume that `z` lies in the compact set `𝔥**`", Theorem 5.0.2 being a
statement about balanced disks); REPORT.md, E15. It is false as stated: an admissible trajectory
may wind `1 + 6m` times around the origin
(`exists_isReinhardtAdmissible_not_isWindingOne`, `SmoothedPolygons/Ch6/Winding.lean`). For
winding number one (`IsWindingOne`) it holds: `exists_isBalancedPair_of_isReinhardtAdmissible`.

This is the form of the converse that §6.1 needs: by `isWindingOne_of_reinhardtCost_lt`, every
admissible trajectory of cost less than `7π/2`, in particular every one at most as costly as the
smoothed octagon, has winding number one.

## Proof: the argument of `smoothedPolygonDisk_isBalancedPair`, generalized

The book gives no proof. `SmoothedPolygons/Ch7/SmoothedPolygonDisk.lean` proves the statement for
the smoothed `(6k+2)`-gons; its argument is generalized as follows.

1. *Periodic extension* (`ad_ext`). On `[0, ∞)`, `G` is the piecewise curve `g(t - nT) Rⁿ` on
   `[nT, (n+1)T)` and `X̃` is `R⁻ⁿ X(t - nT) Rⁿ` (`poly_pw`, as for the smoothed polygons); both
   are `6T`-periodic there (`R⁶ = I`, `oct_R_pow_six`) and are extended to `ℝ` by reduction modulo
   `6T`. The pieces join continuously by `g(T) = R`, `X(T) = R⁻¹X(0)R`, so `G` and `X̃` are
   continuous and `G(t + T) = G(t) R`, `X̃(t + T) = R⁻¹X̃(t)R` (`ad_ext_add`). Since `X` is
   continuous (an integral curve), `G` is an integral curve of the continuous `G X̃` on every
   `[0, NT]` (`poly_pw_isIntegralCurve`), so `G' = G X̃` everywhere, also at the junctions
   (`ad_G_hasDerivAt`). `det G = 1` and `X̃` takes star values (`poly_isStarState_conj_pow`).
2. *The multi-curve* `σ_j(t) = G(t) s_j*` (`ad_σ`). Multi-points: `det G = 1`
   (`oct_isMultiPoint_mulVec`). Star condition from the star inequalities (`oct_star_mulVec`, the
   converse of Corollary 3.1.6). Regularity: `σ_j' = G X̃ s_j* ≠ 0`. The shift
   `σ_j(t + T) = σ_{j+1}(t)` from `R s_j* = s_{j+1}*` (`oct_R_mulVec_sixthRoot`), hence
   `σ_j(t) = σ_{j+n}(t - nT)` for `n ∈ ℤ`, also for the derivatives (`ad_shift_int`,
   `ad_deriv_shift`).
   *Lipschitz tangents* (`ad_σ_lipschitz`): `[P, X]` is bounded on `[0, T]`, since `⟨Z_u, X⟩ < 0`
   (Lemma 3.3.4, `poly_traceForm_neg`) on the compact set `X([0, T]) × U_T`; so the entries of
   `X`, and of `g` (`g' = gX` continuous), are Lipschitz on `[0, T]` (integral curves with bounded
   right-hand sides), and so is `σ_j' = g X s_j*`. By the shift the same constant works on every
   `[nT, (n+1)T]`, and the pieces join (`ad_lipschitzWith_of_pieces`).
   *Curvature* (`ad_σ_curvature`): almost everywhere on `(0, T)`, `X' = [P, X]` with
   `u(t) ∈ U_T` (Lebesgue's differentiation theorem, `ae_hasDerivAt_of_eq_add_integral`), and
   `det(σ_j', σ_j'') = det(X s_j*, (X² + [P, X]) s_j*)`, a positive multiple of
   `-2u_m/⟨Z_u, X⟩ ≥ 0` (`oct_stateCurvature_eq`, Definition 3.3.2 read backwards;
   `ad_det2_curv`, the analogue of `oct_det2_curv` for any `u ∈ U_T`); the shift carries this to
   almost every `t ∈ ℝ` (`ad_ae_of_shift`).
3. *Simplicity from winding number one* (`ad_injOn_of_winding`). With `z = σ₀` seen in `ℂ`, the
   phase `φ = oct_phase z z'` increases strictly (`det(σ₀, σ₀') > 0`) and
   `σ₀ = e^L (cos φ, sin φ)` (`oct_eq_exp`). On `[0, T]`, `φ` and the angle `θ` of `IsWindingOne`
   are two continuous angles of `σ₀` vanishing at `0`, so `φ(T) = θ(T) = π/3`. The difference
   `D(t) = φ(t + T) - φ(t)` is continuous with `sin D(t) > 0` (the consecutive points `σ₀(t)`,
   `σ₀(t + T) = σ₁(t)` of a multi-point have `det = √3/2`) and `D(0) = π/3`, so `D(t) ∈ (0, π)` for
   all `t` (intermediate values). At `t = kT`, `σ₀((k + 1)T) = R σ₀(kT)` (`G(kT) = Rᵏ`) gives
   `D(kT) ≡ π/3 mod 2π`, hence `D(kT) = π/3` and `φ(6T) = 2π`: a curve turning counterclockwise
   about the origin by exactly `2π` over a period is simple on the period (`oct_injOn_of_phase`).
4. *The disk.* `K` is the region swept from the origin by `σ₀` over a period
   (`PlaneCurve.radialHull`); `PlaneCurve.IsStarCurve` (`Basic/Analysis/Convex/StarCurve.lean`,
   `StarCurveConvex.lean`) gives convexity (`convex_radialHull`, from the curvature condition),
   compactness, `0` in the interior and `∂K = σ₀([0, 6T))`, as in
   `smoothedPolygonDisk_isBalancedPair`; central symmetry from `σ₀(t + 3T) = σ₃(t) = -σ₀(t)`.
5. *Area.* `area(K) = cost` by the area formula `eqn_cost`
   (`SmoothedPolygons/Ch3/AreaFormula.lean`), with `G = g` on `[0, T]`.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix Filter
open scoped Topology Interval

/-! ### Shifts -/

/-- One period later, the piecewise curve `Aⁿ f(t - nτ) Bⁿ` is conjugated once more. -/
private lemma ad_pw_add {A B : Mat2} {τ : ℝ} (hτ : 0 < τ) (f0 : ℝ → Mat2) {t : ℝ}
    (ht : 0 ≤ t) : poly_pw A B τ f0 (t + τ) = A * poly_pw A B τ f0 t * B := by
  have hk : ⌊(t + τ) / τ⌋₊ = ⌊t / τ⌋₊ + 1 := by
    rw [add_div, div_self hτ.ne', Nat.floor_add_one (div_nonneg ht hτ.le)]
  simp only [poly_pw, hk]
  push_cast
  rw [show t + τ - ((⌊t / τ⌋₊ : ℝ) + 1) * τ = t - ⌊t / τ⌋₊ * τ by ring, pow_succ', pow_succ]
  simp only [Matrix.mul_assoc]

private lemma ad_pw_add_nat {A B : Mat2} {τ : ℝ} (hτ : 0 < τ) (f0 : ℝ → Mat2) {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) :
    poly_pw A B τ f0 (t + n * τ) = A ^ n * poly_pw A B τ f0 t * B ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show t + ((n + 1 : ℕ) : ℝ) * τ = (t + n * τ) + τ by push_cast; ring,
      ad_pw_add hτ f0 (add_nonneg ht (by positivity)), ih, pow_succ', pow_succ]
    simp only [Matrix.mul_assoc]

/-- A family with `f_j(t + τ) = f_{j+1}(t)` satisfies `f_j(t + mτ) = f_{j+m}(t)`. -/
private lemma ad_shift_nat {α : Type*} {f : ZMod 6 → ℝ → α} {τ : ℝ}
    (h : ∀ j t, f j (t + τ) = f (j + 1) t) (m : ℕ) (j : ZMod 6) (t : ℝ) :
    f j (t + m * τ) = f (j + m) t := by
  induction m generalizing j t with
  | zero => simp
  | succ m ih =>
    rw [show t + ((m + 1 : ℕ) : ℝ) * τ = (t + τ) + m * τ by push_cast; ring, ih, h]
    congr 1
    push_cast
    ring

/-- A family with `f_j(t + τ) = f_{j+1}(t)` satisfies `f_j(t) = f_{j+n}(t - nτ)`, `n ∈ ℤ`. -/
private lemma ad_shift_int {α : Type*} {f : ZMod 6 → ℝ → α} {τ : ℝ}
    (h : ∀ j t, f j (t + τ) = f (j + 1) t) (n : ℤ) (j : ZMod 6) (t : ℝ) :
    f j t = f (j + n) (t - n * τ) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · push_cast
    rw [← ad_shift_nat h m j (t - m * τ), sub_add_cancel]
  · push_cast
    rw [show t - -(m : ℝ) * τ = t + m * τ by ring, ad_shift_nat h m]
    congr 1
    ring

/-- The derivatives of a family with `f_j(t + τ) = f_{j+1}(t)` satisfy the same relation. -/
private lemma ad_deriv_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ZMod 6 → ℝ → E} {τ : ℝ} (h : ∀ j t, f j (t + τ) = f (j + 1) t) (j : ZMod 6) (t : ℝ) :
    deriv (f j) (t + τ) = deriv (f (j + 1)) t := by
  rw [← deriv_comp_add_const]
  congr 1
  funext x
  exact h j x

/-- A property holding almost everywhere on `(0, τ)` for every member of a family with
`κ_j(t + τ) = κ_{j+1}(t)` holds almost everywhere on `ℝ`. -/
private lemma ad_ae_of_shift {κ : ZMod 6 → ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hsh : ∀ j t, κ j (t + τ) = κ (j + 1) t) (h : ∀ j, ∀ᵐ t, t ∈ Ioo 0 τ → 0 ≤ κ j t)
    (j : ZMod 6) : ∀ᵐ t, 0 ≤ κ j t := by
  have hi : ∀ (n : ℤ) (j : ZMod 6), ∀ᵐ t, t - n * τ ∈ Ioo 0 τ → 0 ≤ κ j (t - n * τ) :=
    fun n j ↦ (measurePreserving_sub_right volume ((n : ℝ) * τ)).quasiMeasurePreserving.ae (h j)
  have hS : ∀ᵐ t, t ∉ range (fun n : ℤ ↦ (n : ℝ) * τ) := (countable_range _).ae_notMem _
  filter_upwards [ae_all_iff.2 fun n ↦ ae_all_iff.2 fun j ↦ hi n j, hS] with t ht htS
  have h1 := Int.floor_le (t / τ)
  have h2 := Int.lt_floor_add_one (t / τ)
  rw [le_div_iff₀ hτ] at h1
  rw [div_lt_iff₀ hτ] at h2
  have h1' : (⌊t / τ⌋ : ℝ) * τ < t := lt_of_le_of_ne h1 fun he ↦ htS ⟨_, he⟩
  rw [ad_shift_int hsh ⌊t / τ⌋ j t]
  exact ht _ _ ⟨by linarith, by linarith⟩

/-! ### Lipschitz functions -/

/-- `f` is Lipschitz and bounded on `s`. -/
private def ad_LipBdd (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  (∃ K, LipschitzOnWith K f s) ∧ ∃ M, ∀ x ∈ s, |f x| ≤ M

private lemma ad_LipBdd_const (c : ℝ) (s : Set ℝ) : ad_LipBdd (fun _ ↦ c) s :=
  ⟨⟨0, (LipschitzWith.const c).lipschitzOnWith⟩, |c|, fun _ _ ↦ le_rfl⟩

private lemma ad_LipBdd_add {f g : ℝ → ℝ} {s : Set ℝ} (hf : ad_LipBdd f s)
    (hg : ad_LipBdd g s) : ad_LipBdd (fun x ↦ f x + g x) s := by
  obtain ⟨⟨Kf, hKf⟩, Mf, hMf⟩ := hf
  obtain ⟨⟨Kg, hKg⟩, Mg, hMg⟩ := hg
  exact ⟨⟨_, hKf.add hKg⟩, Mf + Mg,
    fun x hx ↦ (abs_add_le _ _).trans (add_le_add (hMf x hx) (hMg x hx))⟩

/-- The product of two bounded Lipschitz functions is Lipschitz (and bounded). -/
private lemma ad_LipBdd_mul {f g : ℝ → ℝ} {s : Set ℝ} (hf : ad_LipBdd f s)
    (hg : ad_LipBdd g s) : ad_LipBdd (fun x ↦ f x * g x) s := by
  obtain ⟨⟨Kf, hKf⟩, Mf, hMf⟩ := hf
  obtain ⟨⟨Kg, hKg⟩, Mg, hMg⟩ := hg
  refine ⟨⟨_, LipschitzOnWith.of_dist_le' (K := Mf * Kg + Mg * Kf) fun x hx y hy ↦ ?_⟩,
    Mf * Mg, fun x hx ↦ ?_⟩
  · have h1 := hKf.dist_le_mul x hx y hy
    have h2 := hKg.dist_le_mul x hx y hy
    have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf x hx)
    have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg y hy)
    simp only [Real.dist_eq] at h1 h2 ⊢
    calc |f x * g x - f y * g y| = |f x * (g x - g y) + g y * (f x - f y)| := by
          congr 1; ring
      _ ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ Mf * (Kg * |x - y|) + Mg * (Kf * |x - y|) := by
          gcongr
          · exact hMf x hx
          · exact hMg y hy
      _ = (Mf * Kg + Mg * Kf) * |x - y| := by ring
  · rw [abs_mul]
    exact mul_le_mul (hMf x hx) (hMg x hx) (abs_nonneg _) ((abs_nonneg _).trans (hMf x hx))

/-- A function in integral form with a bounded integrand is Lipschitz and bounded on `[0, T]`. -/
private lemma ad_LipBdd_of_integral {f v : ℝ → ℝ} {T M : ℝ} (hT : 0 ≤ T)
    (hv : IntervalIntegrable v volume 0 T)
    (hf : ∀ t ∈ Icc 0 T, f t = f 0 + ∫ s in (0 : ℝ)..t, v s) (hM : ∀ t ∈ Icc 0 T, |v t| ≤ M) :
    ad_LipBdd f (Icc 0 T) := by
  have hsub : ∀ a ∈ Icc 0 T, uIcc 0 a ⊆ uIcc 0 T := fun a ha ↦ by
    rw [uIcc_of_le ha.1, uIcc_of_le hT]; exact Icc_subset_Icc_right ha.2
  have hlip : LipschitzOnWith (Real.toNNReal M) f (Icc 0 T) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
    have e : f a - f b = ∫ s in b..a, v s := by
      rw [hf a ha, hf b hb, add_sub_add_left_eq_sub,
        intervalIntegral.integral_interval_sub_left (hv.mono_set (hsub a ha))
          (hv.mono_set (hsub b hb))]
    rw [Real.dist_eq, e, Real.dist_eq]
    have hI : ∀ x ∈ Ι b a, ‖v x‖ ≤ M := by
      intro x hx
      rw [Real.norm_eq_abs]
      refine hM x ⟨?_, ?_⟩
      · rcases le_total a b with hab | hab
        · rw [uIoc_of_ge hab] at hx; linarith [hx.1, ha.1]
        · rw [uIoc_of_le hab] at hx; linarith [hx.1, hb.1]
      · rcases le_total a b with hab | hab
        · rw [uIoc_of_ge hab] at hx; linarith [hx.2, hb.2]
        · rw [uIoc_of_le hab] at hx; linarith [hx.2, ha.2]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hI).trans ?_
    rw [abs_sub_comm]
    exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal M) (abs_nonneg _)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hlip.continuousOn
  exact ⟨⟨_, hlip⟩, B, fun x hx ↦ by simpa [Real.norm_eq_abs] using hB x hx⟩

/-- A function that is `K`-Lipschitz on every interval `[nτ, (n+1)τ]` is `K`-Lipschitz. -/
private lemma ad_lipschitzWith_of_pieces {f : ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ) {K : NNReal}
    (h : ∀ n : ℤ, LipschitzOnWith K f (Icc (n * τ) ((n + 1) * τ))) : LipschitzWith K f := by
  have hfl : ∀ x : ℝ, (⌊x / τ⌋ : ℝ) * τ ≤ x ∧ x < (⌊x / τ⌋ + 1) * τ := fun x ↦
    ⟨(le_div_iff₀ hτ).1 (Int.floor_le _), (div_lt_iff₀ hτ).1 (Int.lt_floor_add_one _)⟩
  have key : ∀ N : ℕ, ∀ x y, x ≤ y → ⌊y / τ⌋ ≤ ⌊x / τ⌋ + N →
      dist (f x) (f y) ≤ K * (y - x) := by
    intro N
    induction N with
    | zero =>
      intro x y hxy hN
      have hle : (⌊y / τ⌋ : ℝ) ≤ ⌊x / τ⌋ := by exact_mod_cast (by simpa using hN)
      have hy := (hfl y).2
      have hx := hfl x
      have hy' : y ≤ (⌊x / τ⌋ + 1) * τ := by nlinarith
      have := (h ⌊x / τ⌋).dist_le_mul x ⟨hx.1, hx.2.le⟩ y ⟨by linarith, hy'⟩
      rwa [Real.dist_eq x y, abs_sub_comm, abs_of_nonneg (by linarith)] at this
    | succ N ih =>
      intro x y hxy hN
      by_cases hc : ⌊y / τ⌋ ≤ ⌊x / τ⌋ + N
      · exact ih x y hxy hc
      · set n := ⌊x / τ⌋ with hn
        have hx := hfl x
        rw [← hn] at hx
        have hn1 : n + 1 ≤ ⌊y / τ⌋ := by omega
        have hn1' : (n : ℝ) + 1 ≤ ⌊y / τ⌋ := by exact_mod_cast hn1
        have hzy : ((n : ℝ) + 1) * τ ≤ y := by nlinarith [(hfl y).1]
        have hzfl : ⌊((n : ℝ) + 1) * τ / τ⌋ = n + 1 := by
          rw [mul_div_assoc, div_self hτ.ne', mul_one, Int.floor_add_one, Int.floor_intCast]
        have h1 := (h n).dist_le_mul x ⟨hx.1, hx.2.le⟩ (((n : ℝ) + 1) * τ)
          ⟨by nlinarith, le_rfl⟩
        have h2 := ih (((n : ℝ) + 1) * τ) y hzy (by rw [hzfl]; omega)
        rw [Real.dist_eq x, abs_sub_comm, abs_of_nonneg (by linarith)] at h1
        calc dist (f x) (f y) ≤ dist (f x) (f (((n : ℝ) + 1) * τ)) +
              dist (f (((n : ℝ) + 1) * τ)) (f y) := dist_triangle _ _ _
          _ ≤ K * (((n : ℝ) + 1) * τ - x) + K * (y - ((n : ℝ) + 1) * τ) := add_le_add h1 h2
          _ = K * (y - x) := by ring
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rcases le_total x y with hxy | hxy
  · rw [Real.dist_eq x y, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact key (⌊y / τ⌋ - ⌊x / τ⌋).toNat x y hxy (by omega)
  · rw [dist_comm, Real.dist_eq x y, abs_of_nonneg (by linarith)]
    exact key (⌊x / τ⌋ - ⌊y / τ⌋).toNat y x hxy (by omega)

/-- A plane curve whose coordinates are `K`-Lipschitz is `K`-Lipschitz (sup metric). -/
private lemma ad_lipschitzWith_pi {F : ℝ → Fin 2 → ℝ} {K : NNReal}
    (h : ∀ i, LipschitzWith K fun t ↦ F t i) : LipschitzWith K F :=
  LipschitzWith.of_dist_le_mul fun x y ↦
    (dist_pi_le_iff (by positivity)).2 fun i ↦ (h i).dist_le_mul x y

/-! ### The periodic extension -/

/-- The extension of a curve `f` on `[0, T]` by `f(t + T) = A f(t) R`, with period `6T`: the
piecewise curve `Aⁿ f(t - nT) Rⁿ` on `[nT, (n+1)T)` (`poly_pw`), reduced modulo `6T`. -/
private noncomputable def ad_ext (A : Mat2) (T : ℝ) (f : ℝ → Mat2) (t : ℝ) : Mat2 :=
  poly_pw A R T f (oct_red (6 * T) t)

section Ext

variable {A : Mat2} {T : ℝ} {f : ℝ → Mat2}

private lemma ad_pw_add_P (hT : 0 < T) (hA : A ^ 6 = 1) {s : ℝ} (hs : 0 ≤ s) :
    poly_pw A R T f (s + 6 * T) = poly_pw A R T f s := by
  have := ad_pw_add_nat (A := A) (B := R) hT f hs 6
  rw [hA, oct_R_pow_six, Matrix.one_mul, Matrix.mul_one] at this
  rw [← this]
  norm_num

private lemma ad_ext_of_nonneg (hT : 0 < T) (hA : A ^ 6 = 1) {s : ℝ} (hs : 0 ≤ s) :
    ad_ext A T f s = poly_pw A R T f s :=
  oct_ext_eq (by positivity) (fun _ hs ↦ ad_pw_add_P hT hA hs) hs

private lemma ad_ext_periodic (hT : 0 < T) : Function.Periodic (ad_ext A T f) (6 * T) :=
  fun t ↦ by simp only [ad_ext, oct_red_add (by positivity : (0 : ℝ) < 6 * T)]

private lemma ad_ext_add (hT : 0 < T) (hA : A ^ 6 = 1) (t : ℝ) :
    ad_ext A T f (t + T) = A * ad_ext A T f t * R := by
  obtain ⟨n, hn⟩ := oct_exists_int_add_pos (by positivity : (0 : ℝ) < 6 * T) t
  have hper := (ad_ext_periodic (A := A) (f := f) hT).int_mul n
  rw [← hper t, ← hper (t + T), show t + T + n * (6 * T) = (t + n * (6 * T)) + T by ring,
    ad_ext_of_nonneg hT hA (by linarith), ad_ext_of_nonneg hT hA hn.le, ad_pw_add hT f hn.le]

private lemma ad_ext_eq (hT : 0 < T) (hA : A ^ 6 = 1) (hglue : f T = A * f 0 * R) {t : ℝ}
    (ht : t ∈ Icc 0 T) : ad_ext A T f t = f t := by
  rw [ad_ext_of_nonneg hT hA ht.1, poly_pw_of_mem_Icc (i := 0) hT hglue (by simpa using ht)]
  simp

private lemma ad_ext_mem (hT : 0 < T) (t : ℝ) :
    ∃ n : ℕ, ∃ s ∈ Icc 0 T, ad_ext A T f t = A ^ n * f s * R ^ n := by
  have hr := (oct_red_mem (by positivity : (0 : ℝ) < 6 * T) t).1
  obtain ⟨h1, h2⟩ := poly_floor_mem hT hr
  exact ⟨_, _, ⟨by linarith, by linarith⟩, rfl⟩

/-- The extension is continuous: on `[0, ∞)` the pieces join continuously by the gluing
condition, and the reduction modulo `6T` is harmless by periodicity. -/
private lemma ad_ext_continuous (hT : 0 < T) (hA : A ^ 6 = 1) (hglue : f T = A * f 0 * R)
    (hf : ContinuousOn f (Icc 0 T)) : Continuous (ad_ext A T f) := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  have hP : (0 : ℝ) < 6 * T := by positivity
  obtain ⟨n, hn⟩ := oct_exists_int_add_pos hP t
  have hper := (ad_ext_periodic (A := A) (f := f) hT).int_mul n
  have hpos : ∀ s, 0 < s → ContinuousAt (ad_ext A T f) s := by
    intro s hs
    obtain ⟨N, hN⟩ := exists_nat_gt (s / T)
    have hsN : s < N * T := by rwa [div_lt_iff₀ hT] at hN
    have hc := (poly_pw_continuousOn (A := A) (B := R) hT hglue hf N).continuousAt
      (Icc_mem_nhds hs hsN)
    exact hc.congr (Filter.eventually_of_mem (Ioi_mem_nhds hs) fun x hx ↦
      (ad_ext_of_nonneg hT hA (le_of_lt hx)).symm)
  have h2 : ContinuousAt (fun x ↦ ad_ext A T f (x + n * (6 * T))) t :=
    ContinuousAt.comp (g := ad_ext A T f) (f := fun x ↦ x + n * (6 * T)) (hpos _ hn)
      (by fun_prop)
  rwa [show (fun x ↦ ad_ext A T f (x + n * (6 * T))) = ad_ext A T f from funext hper] at h2

end Ext


/-! ### Generalities on the curvature and the winding -/

/-- The curvature condition along a solution of `X' = [P, X]`, `P = Z_u/⟨Z_u, X⟩`, for any
control `u ∈ U_T`: `det(Xs_j*, (X² + [P, X]) s_j*) = det(s_j*, (X + X⁻¹X') s_j*) ≥ 0`, since the
curvatures are `-2u_j/⟨Z_u, X⟩ ≥ 0` (`oct_stateCurvature_eq`; Definition 3.3.2 read backwards). -/
private lemma ad_det2_curv {X : Mat2} (hX : IsStarState X) {u : Fin 3 → ℝ}
    (hu : u ∈ controlSimplex) (j : ZMod 6) :
    0 ≤ det2 (X *ᵥ sixthRoot j)
      ((X * X + (controlP u X * X - X * controlP u X)) *ᵥ sixthRoot j) := by
  have hc := poly_traceForm_neg hu hX
  have hdetX : X.det ≠ 0 := by rw [hX.2.1]; norm_num
  have hmul : X * X + (controlP u X * X - X * controlP u X) =
      X * (X + X⁻¹ * (controlP u X * X - X * controlP u X)) := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdetX),
      Matrix.one_mul]
  rw [hmul, ← Matrix.mulVec_mulVec, oct_det2_mulVec, hX.2.1, one_mul]
  -- `s_j* = ±s_{2m'}*`, and `det(s_{2m'}*, (X + X⁻¹X') s_{2m'}*) = κ_{m'} ∝ u_{m'} ≥ 0`
  have hs : ∃ m' : Fin 3, sixthRoot j = sixthRoot (2 * (m'.val : ZMod 6)) ∨
      sixthRoot j = -sixthRoot (2 * (m'.val : ZMod 6)) := by
    have e : ∀ a b : ZMod 6, a + 3 = b → sixthRoot b = -sixthRoot a := fun a b h ↦ by
      rw [← h]; exact (algA_isMultiPoint_sixthRoot a).2.1
    fin_cases j
    · exact ⟨0, Or.inl rfl⟩
    · refine ⟨2, Or.inr ?_⟩
      change sixthRoot 1 = -sixthRoot 4
      rw [e 1 4 rfl, neg_neg]
    · exact ⟨1, Or.inl rfl⟩
    · exact ⟨0, Or.inr (e 0 3 rfl)⟩
    · exact ⟨2, Or.inl rfl⟩
    · exact ⟨1, Or.inr (e 2 5 rfl)⟩
  obtain ⟨m', hm'⟩ := hs
  have hκ := oct_stateCurvature_eq hX u hc.ne m'
  rw [stateCurvature, controlP] at hκ
  rw [controlP] at *
  have hκ' : det2 (sixthRoot j) ((X + X⁻¹ * ((traceForm (controlMatrix u) X)⁻¹ •
      controlMatrix u * X - X * ((traceForm (controlMatrix u) X)⁻¹ •
      controlMatrix u))) *ᵥ sixthRoot j) =
      -2 * (traceForm (controlMatrix u) X)⁻¹ * u m' := by
    rcases hm' with h | h
    · rw [h, hκ]
    · rw [h, Matrix.mulVec_neg, oct_det2_neg, hκ]
  rw [hκ']
  have hv : 0 ≤ u m' := (hu.1 m').1
  have : 0 < -2 * (traceForm (controlMatrix u) X)⁻¹ := by
    have := inv_lt_zero.2 hc
    linarith
  positivity

/-- `R` acts on the plane seen in `ℂ` as the rotation by `π/3`. -/
private lemma ad_toC_R (v : Fin 2 → ℝ) :
    PlaneCurve.sc_toC (R *ᵥ v) =
      Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) * PlaneCurve.sc_toC v := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  apply Complex.ext <;>
    simp [PlaneCurve.sc_toC, R, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- **Simplicity from winding number one.** Let `γ` be a `C¹` curve turning counterclockwise about
the origin (`det(γ, γ') > 0`), with `γ(0) = s₀*`, `det(γ(t), γ(t + T)) > 0` for all `t` (consecutive
points of a multi-point), `γ((k + 1)T) = R γ(kT)`, and whose continuous angle `θ` with `θ(0) = 0`
on `[0, T]` ends at `θ(T) = π/3`. Then `γ` is injective on `[0, 6T)`.

The phase `φ` of `γ` (`oct_phase`) agrees with `θ` on `[0, T]`, so `φ(T) = π/3`. The difference
`D(t) = φ(t + T) - φ(t)` is continuous with `sin D > 0` everywhere and `D(0) = π/3`, so
`D(t) ∈ (0, π)` for all `t`; at `t = kT` it is `π/3` modulo `2π` (the rotation by `R`), hence
`D(kT) = π/3` and `φ(6T) = 2π`; then `oct_injOn_of_phase`. -/
private lemma ad_injOn_of_winding {γ : ℝ → Fin 2 → ℝ} {T : ℝ} (hT : 0 < T)
    (hC1 : ContDiff ℝ 1 γ) (hcross : ∀ t, 0 < det2 (γ t) (deriv γ t))
    (hnext : ∀ t, 0 < det2 (γ t) (γ (t + T))) (hrot : ∀ k : ℕ, γ (k * T + T) = R *ᵥ γ (k * T))
    (h0 : γ 0 = sixthRoot 0) {θ : ℝ → ℝ} (hθc : ContinuousOn θ (Icc 0 T)) (hθ0 : θ 0 = 0)
    (hθT : θ T = Real.pi / 3)
    (hθ : ∀ t ∈ Icc 0 T, ∃ r : ℝ, 0 < r ∧ γ t = r • ![Real.cos (θ t), Real.sin (θ t)]) :
    InjOn γ (Ico 0 (6 * T)) := by
  set z : ℝ → ℂ := fun t ↦ PlaneCurve.sc_toC (γ t) with hzdef
  set z' : ℝ → ℂ := fun t ↦ PlaneCurve.sc_toC (deriv γ t) with hz'def
  have hpi := Real.pi_pos
  have hγd : ∀ t, HasDerivAt γ (deriv γ t) t := fun t ↦
    ((hC1.differentiable one_ne_zero) t).hasDerivAt
  have hz : ∀ t, HasDerivAt z (z' t) t := by
    intro t
    have h0 := (hasDerivAt_pi.1 (hγd t) 0).ofReal_comp
    have h1 := (hasDerivAt_pi.1 (hγd t) 1).ofReal_comp
    exact h0.add (h1.mul_const Complex.I)
  have hz' : Continuous z' := PlaneCurve.sc_continuous_toC.comp (hC1.continuous_deriv le_rfl)
  have hγ0 : ∀ t, γ t ≠ 0 := fun t h ↦ by
    have := hcross t
    rw [h] at this
    simp [det2] at this
  have hz0 : ∀ t, z t ≠ 0 := fun t h ↦ hγ0 t (PlaneCurve.sc_toC_eq_zero.1 h)
  have hpos : ∀ t, 0 < (z' t / z t).im := by
    intro t
    have e := PlaneCurve.sc_logDeriv_im (γ := γ) t
    simp only [PlaneCurve.sc_logDeriv] at e
    rw [e]
    exact div_pos (hcross t) (Complex.normSq_pos.2 (hz0 t))
  set φ := oct_phase z z' with hφdef
  set L := oct_logmod z z' with hLdef
  -- the polar form `γ = e^L (cos φ, sin φ)`
  have hpolar : ∀ t, γ t 0 = Real.exp (L t) * Real.cos (φ t) ∧
      γ t 1 = Real.exp (L t) * Real.sin (φ t) := by
    intro t
    have he := oct_eq_exp hz hz' hz0 t
    have hz00 : z 0 = 1 := by
      simp only [hzdef, h0, algA_sixthRoot_zero]
      apply Complex.ext <;> simp [PlaneCurve.sc_toC]
    rw [hz00, one_mul] at he
    have hre := congrArg Complex.re he
    have him := congrArg Complex.im he
    rw [Complex.exp_re] at hre
    rw [Complex.exp_im] at him
    simp only [hzdef, PlaneCurve.sc_toC_re, PlaneCurve.sc_toC_im, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      Complex.add_im, Complex.mul_im] at hre him
    simp only [mul_zero, sub_zero, mul_one, add_zero, zero_add] at hre him
    exact ⟨hre, him⟩
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun t ↦
    (oct_phase_hasDerivAt hz hz' hz0 t).continuousAt
  have hφ0 : φ 0 = 0 := oct_phase_zero
  -- winding number one: `φ(T) = θ(T) = π/3`
  have hφT : φ T = Real.pi / 3 := by
    have hψ : ∀ t ∈ Icc 0 T, 0 < Real.cos (θ t - φ t) ∧ Real.sin (θ t - φ t) = 0 := by
      intro t ht
      obtain ⟨r, hr, hγ⟩ := hθ t ht
      obtain ⟨a0, a1⟩ := hpolar t
      have e0 : γ t 0 = r * Real.cos (θ t) := by rw [hγ]; simp
      have e1 : γ t 1 = r * Real.sin (θ t) := by rw [hγ]; simp
      rw [e0] at a0
      rw [e1] at a1
      have hE := Real.exp_pos (L t)
      have hcs := Real.sin_sq_add_cos_sq (φ t)
      rw [Real.cos_sub, Real.sin_sub]
      constructor
      · have : r * (Real.cos (θ t) * Real.cos (φ t) + Real.sin (θ t) * Real.sin (φ t)) =
            Real.exp (L t) := by
          linear_combination Real.cos (φ t) * a0 + Real.sin (φ t) * a1 + Real.exp (L t) * hcs
        exact pos_of_mul_pos_right (this ▸ hE) hr.le
      · have : r * (Real.sin (θ t) * Real.cos (φ t) - Real.cos (θ t) * Real.sin (φ t)) = 0 := by
          linear_combination Real.cos (φ t) * a1 - Real.sin (φ t) * a0
        exact (mul_eq_zero.1 this).resolve_left hr.ne'
    have hψc : ContinuousOn (fun t ↦ θ t - φ t) (Icc 0 T) := hθc.sub hφc.continuousOn
    have hlt : θ T - φ T < Real.pi := by
      by_contra hc
      replace hc := not_lt.1 hc
      obtain ⟨s, hs, hsπ⟩ := intermediate_value_Icc hT.le hψc
        ⟨by simp only [hθ0, hφ0, sub_zero]; exact hpi.le, hc⟩
      have := (hψ s hs).1
      rw [show θ s - φ s = Real.pi from hsπ, Real.cos_pi] at this
      linarith
    have hgt : -Real.pi < θ T - φ T := by
      by_contra hc
      replace hc := not_lt.1 hc
      obtain ⟨s, hs, hsπ⟩ := intermediate_value_Icc' hT.le hψc
        ⟨hc, by simp only [hθ0, hφ0, sub_zero]; linarith⟩
      have := (hψ s hs).1
      rw [show θ s - φ s = -Real.pi from hsπ, Real.cos_neg, Real.cos_pi] at this
      linarith
    have := (Real.sin_eq_zero_iff_of_lt_of_lt hgt hlt).1 (hψ T ⟨hT.le, le_rfl⟩).2
    linarith
  -- consecutive points: `sin (φ(t + T) - φ(t)) > 0`
  have hsinD : ∀ t, 0 < Real.sin (φ (t + T) - φ t) := by
    intro t
    have hd := hnext t
    obtain ⟨a0, a1⟩ := hpolar t
    obtain ⟨b0, b1⟩ := hpolar (t + T)
    simp only [det2] at hd
    rw [a0, a1, b0, b1] at hd
    have e : Real.exp (L t) * Real.cos (φ t) * (Real.exp (L (t + T)) * Real.sin (φ (t + T))) -
        Real.exp (L t) * Real.sin (φ t) * (Real.exp (L (t + T)) * Real.cos (φ (t + T))) =
        (Real.exp (L t) * Real.exp (L (t + T))) * Real.sin (φ (t + T) - φ t) := by
      rw [Real.sin_sub]; ring
    rw [e] at hd
    exact pos_of_mul_pos_right hd (by positivity)
  -- `D(t) = φ(t + T) - φ(t) ∈ (0, π)`
  have hDc : Continuous fun t ↦ φ (t + T) - φ t :=
    (hφc.comp (continuous_id.add continuous_const)).sub hφc
  have hD0 : φ (0 + T) - φ 0 = Real.pi / 3 := by rw [zero_add, hφT, hφ0, sub_zero]
  have hDmem : ∀ t, 0 < φ (t + T) - φ t ∧ φ (t + T) - φ t < Real.pi := by
    intro t
    constructor
    · by_contra hc
      replace hc := not_lt.1 hc
      obtain ⟨s, -, hs⟩ := intermediate_value_uIcc (a := 0) (b := t) hDc.continuousOn
        (mem_uIcc.2 (Or.inr ⟨hc, by rw [hD0]; positivity⟩))
      have := hsinD s
      simp only at hs
      rw [hs, Real.sin_zero] at this
      exact lt_irrefl _ this
    · by_contra hc
      replace hc := not_lt.1 hc
      obtain ⟨s, -, hs⟩ := intermediate_value_uIcc (a := 0) (b := t) hDc.continuousOn
        (mem_uIcc.2 (Or.inl ⟨by rw [hD0]; linarith, hc⟩))
      have := hsinD s
      simp only at hs
      rw [hs, Real.sin_pi] at this
      exact lt_irrefl _ this
  -- at the times `kT`, `D = π/3`
  have hDk : ∀ k : ℕ, φ (k * T + T) - φ (k * T) = Real.pi / 3 := by
    intro k
    obtain ⟨n, hn⟩ := oct_phase_sub_of_eq hz hz' hz0 (a := k * T) (b := k * T + T)
      (w := ((Real.pi / 3 : ℝ) : ℂ)) (by simp only [hzdef]; rw [hrot k, ad_toC_R])
    rw [Complex.ofReal_re, ← hφdef] at hn
    have hm := hDmem (k * T)
    rw [hn] at hm ⊢
    have h1 : (n : ℝ) < 1 := by nlinarith
    have h2 : (-1 : ℝ) < n := by nlinarith
    have hn0 : n = 0 := by
      have : n < 1 := by exact_mod_cast h1
      have : -1 < n := by exact_mod_cast h2
      omega
    rw [hn0]
    simp
  have hφk : ∀ k : ℕ, φ (k * T) = k * (Real.pi / 3) := by
    intro k
    induction k with
    | zero => simp [hφ0]
    | succ k ih =>
      have := hDk k
      push_cast
      rw [show ((k : ℝ) + 1) * T = k * T + T by ring]
      linarith
  have hφ6 : oct_phase z z' (6 * T) = 2 * Real.pi := by
    have := hφk 6
    push_cast at this
    rw [← hφdef, this]
    ring
  have hinj := oct_injOn_of_phase hz hz' hz0 hpos hφ6
  intro a ha b hb hab
  exact hinj ha hb (by simp only [hzdef, hab])

/-! ### The extension of an admissible trajectory -/

section Admissible

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}

private lemma ad_T_pos (h : IsReinhardtAdmissible T u g X) : 0 < T := h.1.1

private lemma ad_glue_g (h : IsReinhardtAdmissible T u g X) : g T = 1 * g 0 * R := by
  rw [h.2.2.1, h.2.1, Matrix.one_mul, Matrix.one_mul]

private lemma ad_g_continuousOn (h : IsReinhardtAdmissible T u g X) :
    ContinuousOn g (Icc 0 T) :=
  Matrix.continuousOn_of_eq_add_integral h.1.2.2.2.2.1

private lemma ad_X_continuousOn (h : IsReinhardtAdmissible T u g X) :
    ContinuousOn X (Icc 0 T) :=
  Matrix.continuousOn_of_eq_add_integral h.1.2.2.2.2.2

/-- `g' = gX` on `(0, T)` (`X` is continuous). -/
private lemma ad_g_hasDerivAt (h : IsReinhardtAdmissible T u g X) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAtEntrywise g (g t * X t) t :=
  Matrix.hasDerivAtEntrywise_of_eq_add_integral h.1.2.2.2.2.1 ht
    (((ad_g_continuousOn h).mul (ad_X_continuousOn h)).continuousAt (Icc_mem_nhds ht.1 ht.2))

/-- On `[0, ∞)` the extension of `g` has derivative `G X̃` at every positive time, also at the
junctions: it is an integral curve of the continuous `G X̃`. -/
private lemma ad_Gpw_hasDerivAt (h : IsReinhardtAdmissible T u g X) {s : ℝ} (hs : 0 < s) :
    HasDerivAtEntrywise (poly_pw 1 R T g) (poly_pw 1 R T g s * poly_pw R⁻¹ R T X s) s := by
  have hT := ad_T_pos h
  obtain ⟨N, hN⟩ := exists_nat_gt (s / T)
  have hsN : s < N * T := by rwa [div_lt_iff₀ hT] at hN
  have hI : IsIntegralCurve (poly_pw 1 R T g)
      (fun t ↦ poly_pw 1 R T g t * poly_pw R⁻¹ R T X t) (N * T) := by
    refine poly_pw_isIntegralCurve hT (ad_glue_g h) (ad_g_continuousOn h)
      ((ad_g_continuousOn h).mul (ad_X_continuousOn h)) (fun s hs ↦ ad_g_hasDerivAt h hs) N ?_
    intro i _ t ht
    rw [poly_pw_of_mem_Ico hT ht, poly_pw_of_mem_Ico hT ht]
    simp only [one_pow, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (R ^ i) (R⁻¹ ^ i), poly_Rpow_mul_Rinvpow, Matrix.one_mul,
      Pi.mul_apply, Matrix.mul_assoc]
  have hc := ((poly_pw_continuousOn hT (ad_glue_g h) (ad_g_continuousOn h) N).mul
    (poly_pw_continuousOn hT h.2.2.2 (ad_X_continuousOn h) N)).continuousAt
    (Icc_mem_nhds hs hsN)
  exact Matrix.hasDerivAtEntrywise_of_eq_add_integral hI ⟨hs, hsN⟩ hc

private lemma ad_G_eq (h : IsReinhardtAdmissible T u g X) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ad_ext 1 T g t = g t :=
  ad_ext_eq (ad_T_pos h) (one_pow 6) (ad_glue_g h) ht

private lemma ad_X_eq (h : IsReinhardtAdmissible T u g X) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ad_ext R⁻¹ T X t = X t :=
  ad_ext_eq (ad_T_pos h) oct_Rinv_pow_six h.2.2.2 ht

private lemma ad_G_continuous (h : IsReinhardtAdmissible T u g X) : Continuous (ad_ext 1 T g) :=
  ad_ext_continuous (ad_T_pos h) (one_pow 6) (ad_glue_g h) (ad_g_continuousOn h)

private lemma ad_X_continuous (h : IsReinhardtAdmissible T u g X) :
    Continuous (ad_ext R⁻¹ T X) :=
  ad_ext_continuous (ad_T_pos h) oct_Rinv_pow_six h.2.2.2 (ad_X_continuousOn h)

/-- `G' = G X̃` everywhere. -/
private lemma ad_G_hasDerivAt (h : IsReinhardtAdmissible T u g X) (t : ℝ) :
    HasDerivAtEntrywise (ad_ext 1 T g) (ad_ext 1 T g t * ad_ext R⁻¹ T X t) t := by
  have hT := ad_T_pos h
  have hP : (0 : ℝ) < 6 * T := by positivity
  obtain ⟨n, hn⟩ := oct_exists_int_add_pos hP t
  have hperG := (ad_ext_periodic (A := 1) (f := g) hT).int_mul n
  have hperX := (ad_ext_periodic (A := R⁻¹) (f := X) hT).int_mul n
  have h1 : HasDerivAtEntrywise (ad_ext 1 T g)
      (ad_ext 1 T g (t + n * (6 * T)) * ad_ext R⁻¹ T X (t + n * (6 * T)))
      (t + n * (6 * T)) := by
    rw [ad_ext_of_nonneg hT (one_pow 6) hn.le, ad_ext_of_nonneg hT oct_Rinv_pow_six hn.le]
    exact (ad_Gpw_hasDerivAt h hn).congr_of_eventuallyEq
      (Filter.eventually_of_mem (Ioi_mem_nhds hn) fun x hx ↦
        ad_ext_of_nonneg hT (one_pow 6) (le_of_lt hx))
  have h2 := HasDerivAtEntrywise.scomp (h := fun x ↦ x + n * (6 * T)) h1
    ((hasDerivAt_id' t).add_const _)
  rw [one_smul, hperG, hperX, show (fun x ↦ ad_ext 1 T g (x + n * (6 * T))) =
    ad_ext 1 T g from funext hperG] at h2
  exact h2

/-- `det G = 1` and `X̃` takes star values (the star domain is invariant under `R`, §4.6). -/
private lemma ad_det_star (h : IsReinhardtAdmissible T u g X) (t : ℝ) :
    (ad_ext 1 T g t).det = 1 ∧ IsStarState (ad_ext R⁻¹ T X t) := by
  have hT := ad_T_pos h
  have hst := h.1.2.2.2.1
  constructor
  · obtain ⟨n, s, hs, he⟩ := ad_ext_mem (A := 1) (f := g) hT t
    rw [he, Matrix.det_mul, Matrix.det_mul, one_pow, Matrix.det_one, Matrix.det_pow, poly_det_R,
      one_pow, (hst s hs).1]
    ring
  · obtain ⟨n, s, hs, he⟩ := ad_ext_mem (A := R⁻¹) (f := X) hT t
    rw [he]
    exact poly_isStarState_conj_pow n (hst s hs).2

/-- `G(kT) = Rᵏ`. -/
private lemma ad_G_nat (h : IsReinhardtAdmissible T u g X) (k : ℕ) :
    ad_ext 1 T g (k * T) = R ^ k := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, zero_mul, ad_G_eq h ⟨le_rfl, (ad_T_pos h).le⟩, h.2.1, pow_zero]
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : ℝ) * T = k * T + T by push_cast; ring,
      ad_ext_add (ad_T_pos h) (one_pow 6), ih, Matrix.one_mul, pow_succ]

/-! ### The multi-curve -/

/-- The multi-curve `σ_j(t) = G(t) s_j*` of the extended trajectory. -/
private noncomputable def ad_σ (T : ℝ) (g : ℝ → Mat2) (j : ZMod 6) (t : ℝ) : Fin 2 → ℝ :=
  ad_ext 1 T g t *ᵥ sixthRoot j

private lemma ad_σ_hasDerivAt (h : IsReinhardtAdmissible T u g X) (j : ZMod 6) (t : ℝ) :
    HasDerivAt (ad_σ T g j) ((ad_ext 1 T g t * ad_ext R⁻¹ T X t) *ᵥ sixthRoot j) t :=
  (ad_G_hasDerivAt h t).mulVec_const _

private lemma ad_σ_deriv (h : IsReinhardtAdmissible T u g X) (j : ZMod 6) (t : ℝ) :
    deriv (ad_σ T g j) t = (ad_ext 1 T g t * ad_ext R⁻¹ T X t) *ᵥ sixthRoot j :=
  (ad_σ_hasDerivAt h j t).deriv

private lemma ad_σ_contDiff (h : IsReinhardtAdmissible T u g X) (j : ZMod 6) :
    ContDiff ℝ 1 (ad_σ T g j) := by
  refine contDiff_one_iff_deriv.2 ⟨fun t ↦ (ad_σ_hasDerivAt h j t).differentiableAt, ?_⟩
  rw [show deriv (ad_σ T g j) = _ from funext (ad_σ_deriv h j)]
  exact ((ad_G_continuous h).matrix_mul (ad_X_continuous h)).matrix_mulVec continuous_const

private lemma ad_σ_deriv_ne_zero (h : IsReinhardtAdmissible T u g X) (j : ZMod 6) (t : ℝ) :
    deriv (ad_σ T g j) t ≠ 0 := by
  rw [ad_σ_deriv h j]
  intro h0
  have hdet : (ad_ext 1 T g t * ad_ext R⁻¹ T X t).det ≠ 0 := by
    rw [Matrix.det_mul, (ad_det_star h t).1, (ad_det_star h t).2.2.1]; norm_num
  exact oct_sixthRoot_ne_zero j (Matrix.eq_zero_of_mulVec_eq_zero hdet h0)

private lemma ad_σ_isMultiPoint (h : IsReinhardtAdmissible T u g X) (t : ℝ) :
    IsMultiPoint fun j ↦ ad_σ T g j t :=
  oct_isMultiPoint_mulVec (ad_det_star h t).1

/-- The star condition, from the star inequalities `ρᵢ(X̃) > 0` (`oct_star_mulVec`). -/
private lemma ad_σ_star (h : IsReinhardtAdmissible T u g X) (j : ZMod 6) (t : ℝ) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ deriv (ad_σ T g j) t =
      α • (ad_σ T g (j + 1) t - ad_σ T g j t) + β • ad_σ T g (j + 1) t := by
  obtain ⟨α, β, hα, hβ, he⟩ := oct_star_mulVec (ad_det_star h t).2 j
  refine ⟨α, β, hα, hβ, ?_⟩
  rw [ad_σ_deriv h j]
  simp only [ad_σ]
  rw [← Matrix.mulVec_mulVec, he, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_sub]

private lemma ad_σ_periodic (h : IsReinhardtAdmissible T u g X) (j : ZMod 6) (t : ℝ) :
    ad_σ T g j (t + 6 * T) = ad_σ T g j t := by
  simp only [ad_σ, ad_ext_periodic (A := 1) (f := g) (ad_T_pos h) t]

/-- `σ_j(t + T) = σ_{j+1}(t)`, from `G(t + T) = G(t) R` and `R s_j* = s_{j+1}*`. -/
private lemma ad_σ_add (h : IsReinhardtAdmissible T u g X) (j : ZMod 6) (t : ℝ) :
    ad_σ T g j (t + T) = ad_σ T g (j + 1) t := by
  simp only [ad_σ]
  rw [ad_ext_add (ad_T_pos h) (one_pow 6), Matrix.one_mul, ← Matrix.mulVec_mulVec,
    oct_R_mulVec_sixthRoot]

private lemma ad_σ_eq_shift (h : IsReinhardtAdmissible T u g X) (j : ZMod 6) :
    ad_σ T g j = fun t ↦ ad_σ T g 0 (t + j.val * T) := by
  funext t
  rw [ad_shift_nat (ad_σ_add h), zero_add, ZMod.natCast_zmod_val]

/-! ### Lipschitz tangents -/

/-- The bracket `[P, X]` of the state equation is bounded on `[0, T]`: `⟨Z_u, X⟩ < 0`
(Lemma 3.3.4) on the compact set `X([0, T]) × U_T`, so that `P = Z_u/⟨Z_u, X⟩` is continuous
there. -/
private lemma ad_bracket_bound (h : IsReinhardtAdmissible T u g X) (i j : Fin 2) :
    ∃ M, ∀ t ∈ Icc 0 T, |(controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) i j| ≤ M := by
  have hXc := ad_X_continuousOn h
  have hst := h.1.2.2.2.1
  set S := (X '' Icc 0 T) ×ˢ controlSimplex with hS
  have hK : IsCompact S :=
    (isCompact_Icc.image_of_continuousOn hXc).prod isCompact_controlSimplex
  have hZ : Continuous controlMatrix := by
    unfold controlMatrix
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> dsimp <;> fun_prop
  have hZ2 : Continuous fun w : Mat2 × (Fin 3 → ℝ) ↦ controlMatrix w.2 := hZ.comp continuous_snd
  have hPc : ContinuousOn (fun w : Mat2 × (Fin 3 → ℝ) ↦ controlP w.2 w.1) S := by
    unfold controlP
    refine ContinuousOn.smul (f := fun w : Mat2 × (Fin 3 → ℝ) ↦
      (traceForm (controlMatrix w.2) w.1)⁻¹) ?_ hZ2.continuousOn
    refine ContinuousOn.inv₀ ?_ fun w hw ↦ ?_
    · exact (hZ2.matrix_mul continuous_fst).matrix_trace.continuousOn
    · obtain ⟨⟨s, hs, hsw⟩, hw2⟩ := hw
      rw [← hsw]
      exact (poly_traceForm_neg hw2 (hst s hs).2).ne
  have hBc : ContinuousOn (fun w : Mat2 × (Fin 3 → ℝ) ↦
      (controlP w.2 w.1 * w.1 - w.1 * controlP w.2 w.1) i j) S :=
    (continuous_id.matrix_elem i j).comp_continuousOn
      ((hPc.mul continuous_fst.continuousOn).sub (continuous_fst.continuousOn.mul hPc))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hBc
  exact ⟨M, fun t ht ↦ by
    simpa [Real.norm_eq_abs] using hM (X t, u t) ⟨⟨t, ht, rfl⟩, h.1.2.2.1 t ht⟩⟩

/-- The entries of `g` are Lipschitz and bounded on `[0, T]` (`g' = gX` is continuous). -/
private lemma ad_g_LipBdd (h : IsReinhardtAdmissible T u g X) (i j : Fin 2) :
    ad_LipBdd (fun t ↦ g t i j) (Icc 0 T) := by
  have hgI := h.1.2.2.2.2.1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuous_id.matrix_elem i j).comp_continuousOn
      ((ad_g_continuousOn h).mul (ad_X_continuousOn h)))
  exact ad_LipBdd_of_integral (ad_T_pos h).le (hgI i j).1 (hgI i j).2
    fun t ht ↦ by simpa [Real.norm_eq_abs] using hM t ht

/-- The entries of `X` are Lipschitz and bounded on `[0, T]` (`X' = [P, X]` is bounded). -/
private lemma ad_X_LipBdd (h : IsReinhardtAdmissible T u g X) (i j : Fin 2) :
    ad_LipBdd (fun t ↦ X t i j) (Icc 0 T) := by
  have hXI := h.1.2.2.2.2.2
  obtain ⟨M, hM⟩ := ad_bracket_bound h i j
  exact ad_LipBdd_of_integral (ad_T_pos h).le (hXI i j).1 (hXI i j).2 hM

private lemma ad_LipBdd_mulVec {A B : ℝ → Mat2} {s : Set ℝ}
    (hA : ∀ i j, ad_LipBdd (fun t ↦ A t i j) s) (hB : ∀ i j, ad_LipBdd (fun t ↦ B t i j) s)
    (v : Fin 2 → ℝ) (i : Fin 2) : ad_LipBdd (fun t ↦ ((A t * B t) *ᵥ v) i) s := by
  have e : (fun t ↦ ((A t * B t) *ᵥ v) i) = fun t ↦
      (A t i 0 * B t 0 0 + A t i 1 * B t 1 0) * v 0 +
        (A t i 0 * B t 0 1 + A t i 1 * B t 1 1) * v 1 := by
    funext t
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e]
  exact ad_LipBdd_add
    (ad_LipBdd_mul (ad_LipBdd_add (ad_LipBdd_mul (hA i 0) (hB 0 0))
      (ad_LipBdd_mul (hA i 1) (hB 1 0))) (ad_LipBdd_const _ _))
    (ad_LipBdd_mul (ad_LipBdd_add (ad_LipBdd_mul (hA i 0) (hB 0 1))
      (ad_LipBdd_mul (hA i 1) (hB 1 1))) (ad_LipBdd_const _ _))

/-- **The tangents `σ_j'` are Lipschitz.** On `[0, T]`, `σ_j' = g X s_j*` with `g` and `X`
Lipschitz (integral curves with bounded right-hand sides); by `σ_j'(t + T) = σ_{j+1}'(t)` the same
constant works on every `[nT, (n+1)T]`, and the pieces join. -/
private lemma ad_σ_lipschitz (h : IsReinhardtAdmissible T u g X) (j : ZMod 6) :
    ∃ C, LipschitzWith C (deriv (ad_σ T g j)) := by
  have hT := ad_T_pos h
  have hsh := ad_deriv_shift (ad_σ_add h)
  have hK : ∀ k : ZMod 6, ∀ i : Fin 2,
      ∃ K, LipschitzOnWith K (fun t ↦ deriv (ad_σ T g k) t i) (Icc 0 T) := by
    intro k i
    obtain ⟨⟨K, hK⟩, -⟩ := ad_LipBdd_mulVec (ad_g_LipBdd h) (ad_X_LipBdd h) (sixthRoot k) i
    have e : ∀ t ∈ Icc 0 T, deriv (ad_σ T g k) t i = ((g t * X t) *ᵥ sixthRoot k) i :=
      fun t ht ↦ by rw [ad_σ_deriv h k, ad_G_eq h ht, ad_X_eq h ht]
    refine ⟨K, fun a ha b hb ↦ ?_⟩
    change edist (deriv (ad_σ T g k) a i) (deriv (ad_σ T g k) b i) ≤ _
    rw [e a ha, e b hb]
    exact hK ha hb
  choose K hK using hK
  set C := ∑ k : ZMod 6, ∑ i : Fin 2, K k i
  have hKC : ∀ k i, K k i ≤ C := fun k i ↦
    (Finset.single_le_sum (f := fun i ↦ K k i) (fun _ _ ↦ zero_le) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun k ↦ ∑ i, K k i) (fun _ _ ↦ zero_le) (Finset.mem_univ k))
  refine ⟨C, ad_lipschitzWith_pi fun i ↦ ad_lipschitzWith_of_pieces hT fun n ↦ ?_⟩
  have e : ∀ t, deriv (ad_σ T g j) t i = deriv (ad_σ T g (j + n)) (t - n * T) i := fun t ↦ by
    rw [ad_shift_int (f := fun k ↦ deriv (ad_σ T g k)) hsh n j t]
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
  rw [e a, e b]
  have := ((hK (j + n) i).weaken (hKC _ _)).dist_le_mul (a - n * T)
    ⟨by linarith [ha.1], by linarith [ha.2]⟩ (b - n * T) ⟨by linarith [hb.1], by linarith [hb.2]⟩
  rwa [Real.dist_eq (a - n * T), show a - n * T - (b - n * T) = a - b by ring,
    ← Real.dist_eq] at this

/-! ### The curvature condition -/

/-- On `(0, T)`, almost everywhere, `X' = [P, X]` with `u(t) ∈ U_T`, and the curvature
`det(σ_j', σ_j'') = det(X s_j*, (X² + [P, X]) s_j*)` is `≥ 0` (`ad_det2_curv`). -/
private lemma ad_curv_Ioo (h : IsReinhardtAdmissible T u g X) (j : ZMod 6) :
    ∀ᵐ t, t ∈ Ioo 0 T → 0 ≤ det2 (deriv (ad_σ T g j) t) (deriv (deriv (ad_σ T g j)) t) := by
  obtain ⟨hT, -, hu, hst, -, hXI⟩ := h.1
  have hXd : ∀ i k, ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt (fun s ↦ X s i k)
      ((controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) i k) t := fun i k ↦
    ae_hasDerivAt_of_eq_add_integral (hXI i k).1 ⟨le_rfl, hT.le⟩ (hXI i k).2
  filter_upwards [ae_all_iff.2 fun i ↦ ae_all_iff.2 fun k ↦ hXd i k] with t ht htI
  have hX : HasDerivAtEntrywise X (controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) t :=
    fun i k ↦ ht i k htI
  have hI : t ∈ Icc 0 T := Ioo_subset_Icc_self htI
  have hloc : deriv (ad_σ T g j) =ᶠ[𝓝 t] fun s ↦ (g s * X s) *ᵥ sixthRoot j := by
    filter_upwards [Icc_mem_nhds htI.1 htI.2] with s hs
    rw [ad_σ_deriv h j, ad_G_eq h hs, ad_X_eq h hs]
  have hd := ((ad_g_hasDerivAt h htI).mul hX).mulVec_const (sixthRoot j)
  rw [(hd.congr_of_eventuallyEq hloc).deriv, hloc.eq_of_nhds]
  rw [show g t * X t * X t + g t * (controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) =
    g t * (X t * X t + (controlP (u t) (X t) * X t - X t * controlP (u t) (X t))) by
      rw [Matrix.mul_add, Matrix.mul_assoc], ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    oct_det2_mulVec, (hst t hI).1, one_mul]
  exact ad_det2_curv (hst t hI).2 (hu t hI) j

/-- **The curvature condition** `det(σ_j', σ_j'') ≥ 0` almost everywhere on `ℝ`, from `(0, T)`
by the shift relation. -/
private lemma ad_σ_curvature (h : IsReinhardtAdmissible T u g X) (j : ZMod 6) :
    ∀ᵐ t, 0 ≤ det2 (deriv (ad_σ T g j) t) (deriv (deriv (ad_σ T g j)) t) := by
  have hsh1 := ad_deriv_shift (ad_σ_add h)
  have hsh2 := ad_deriv_shift (f := fun k ↦ deriv (ad_σ T g k)) hsh1
  exact ad_ae_of_shift
    (κ := fun k t ↦ det2 (deriv (ad_σ T g k) t) (deriv (deriv (ad_σ T g k)) t))
    (ad_T_pos h) (fun k t ↦ by simp only [hsh1, hsh2]) (ad_curv_Ioo h) j

/-! ### Simplicity and the disk -/

/-- `det(σ₀, σ₀') > 0`: `σ₀` turns counterclockwise about the origin. -/
private lemma ad_cross_pos (h : IsReinhardtAdmissible T u g X) (t : ℝ) :
    0 < det2 (ad_σ T g 0 t) (deriv (ad_σ T g 0) t) := by
  obtain ⟨α, β, hα, hβ, hd⟩ := ad_σ_star h 0 t
  have hmp := ((ad_σ_isMultiPoint h t) 0).2.2
  simp only [zero_add] at hmp hd
  exact oct_det2_pos_of_star hα hβ hd hmp

/-- **`σ₀` is simple on a period** (winding number one, `ad_injOn_of_winding`). -/
private lemma ad_σ0_injOn (h : IsReinhardtAdmissible T u g X) (hw : IsWindingOne T g) :
    InjOn (ad_σ T g 0) (Ico 0 (6 * T)) := by
  obtain ⟨θ, hθc, hθ0, hθT, hθ⟩ := hw
  refine ad_injOn_of_winding (ad_T_pos h) (ad_σ_contDiff h 0) (ad_cross_pos h) (fun t ↦ ?_)
    (fun k ↦ ?_) ?_ hθc hθ0 hθT fun t ht ↦ ?_
  · rw [ad_σ_add h, ((ad_σ_isMultiPoint h t) 0).2.2]
    positivity
  · simp only [ad_σ]
    rw [ad_ext_add (ad_T_pos h) (one_pow 6), ad_G_nat h, Matrix.one_mul, Matrix.mulVec_mulVec,
      ← pow_succ, pow_succ']
  · simp only [ad_σ]
    rw [ad_G_eq h ⟨le_rfl, (ad_T_pos h).le⟩, h.2.1, Matrix.one_mulVec]
  · simp only [ad_σ]
    rw [ad_G_eq h ht]
    exact hθ t ht

/-- `σ₀` is a star-shaped closed curve with period `6T`. -/
private lemma ad_isStarCurve (h : IsReinhardtAdmissible T u g X) (hw : IsWindingOne T g) :
    PlaneCurve.IsStarCurve (ad_σ T g 0) (6 * T) where
  pos := by have := ad_T_pos h; positivity
  contDiff := ad_σ_contDiff h 0
  periodic := ad_σ_periodic h 0
  injOn := ad_σ0_injOn h hw
  cross_pos := ad_cross_pos h

private lemma ad_σ_injOn (h : IsReinhardtAdmissible T u g X) (hw : IsWindingOne T g)
    (j : ZMod 6) : InjOn (ad_σ T g j) (Ico 0 (6 * T)) := by
  have hP : (0 : ℝ) < 6 * T := by have := ad_T_pos h; positivity
  rw [ad_σ_eq_shift h j]
  exact oct_injOn_shift hP (ad_σ_periodic h 0) (ad_σ0_injOn h hw) _

private lemma ad_σ_image (h : IsReinhardtAdmissible T u g X) (hw : IsWindingOne T g)
    (j : ZMod 6) :
    ad_σ T g j '' Ico 0 (6 * T) = frontier (PlaneCurve.radialHull (ad_σ T g 0) 0 (6 * T)) := by
  have hP : (0 : ℝ) < 6 * T := by have := ad_T_pos h; positivity
  rw [(ad_isStarCurve h hw).frontier_radialHull, oct_image_Ico hP (ad_σ_periodic h j),
    oct_image_Ico hP (ad_σ_periodic h 0), ad_σ_eq_shift h j]
  exact (Equiv.addRight ((ZMod.val j : ℝ) * T)).surjective.range_comp (ad_σ T g 0)

/-- Central symmetry: `σ₀(t + 3T) = σ₃(t) = -σ₀(t)`. -/
private lemma ad_disk_neg (h : IsReinhardtAdmissible T u g X) :
    ∀ x ∈ PlaneCurve.radialHull (ad_σ T g 0) 0 (6 * T),
      -x ∈ PlaneCurve.radialHull (ad_σ T g 0) 0 (6 * T) := by
  have hP : (0 : ℝ) < 6 * T := by have := ad_T_pos h; positivity
  rintro x ⟨t, -, r, hr, rfl⟩
  refine ⟨oct_red (6 * T) (t + 3 * T), Ico_subset_Icc_self (oct_red_mem hP _), r, hr, ?_⟩
  have h3 := ad_shift_nat (ad_σ_add h) 3 0 t
  have hmp := ((ad_σ_isMultiPoint h t) 0).2.1
  simp only [zero_add] at hmp h3
  push_cast at h3
  rw [oct_periodic_red (ad_σ_periodic h 0), h3, hmp, smul_neg]

end Admissible

/-- **The converse of Problem 3.6.2 for winding number one**
(`pbm:reinhardt-optimal-control:converse`, label of this formalization; E15, used without proof at
TeX 4579). An admissible trajectory `(g, X)` of the Reinhardt control problem on `[0, T]` whose
curve `g s₀*` winds once (`IsWindingOne`) extends to `G` on `ℝ` (`G(t + T) = G(t) R`) such that
`σ_j(t) = G(t) s_j*` is the multi-curve of a balanced pair `(K, σ)` in circle representation with
`σ_j(t + T) = σ_{j+1}(t)`, `G = g` and `G⁻¹G' = X` on `[0, T]`, `G⁻¹G'` a star state everywhere, and
`area(K)` equal to the cost of the trajectory. The hypothesis `IsWindingOne` cannot be dropped
(`exists_isReinhardtAdmissible_not_isWindingOne`). -/
theorem exists_isBalancedPair_of_isReinhardtAdmissible {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsReinhardtAdmissible T u g X) (hw : IsWindingOne T g) :
    ∃ (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (G : ℝ → Mat2),
      (∀ t ∈ Icc 0 T, G t = g t) ∧
      (∀ t ∈ Icc 0 T, (G t)⁻¹ * derivEntrywise G t = X t) ∧
      (∀ t, IsStarState ((G t)⁻¹ * derivEntrywise G t)) ∧
      (∀ j t, σ j t = G t *ᵥ sixthRoot j) ∧ (∀ j t, σ j (t + T) = σ (j + 1) t) ∧
      IsBalancedPair K σ T ∧ IsCircleRepresentation σ ∧
      volume K = ENNReal.ofReal (reinhardtCost T X) := by
  have hT := ad_T_pos h
  have hstar := ad_isStarCurve h hw
  have hbal : IsBalancedPair (PlaneCurve.radialHull (ad_σ T g 0) 0 (6 * T)) (ad_σ T g) T :=
    ⟨⟨hstar.convex_radialHull (ad_σ_lipschitz h 0) (ad_σ_curvature h 0),
      hstar.isCompact_radialHull, ⟨0, hstar.zero_mem_interior_radialHull⟩, ad_disk_neg h⟩,
      fun j ↦ ⟨ad_σ_contDiff h j, ad_σ_deriv_ne_zero h j⟩, ad_σ_lipschitz h,
      ad_σ_isMultiPoint h, ad_σ_curvature h, ad_σ_star h, hT, ad_σ_periodic h,
      ad_σ_injOn h hw, ad_σ_image h hw⟩
  have hGX : ∀ t, (ad_ext 1 T g t)⁻¹ * derivEntrywise (ad_ext 1 T g) t = ad_ext R⁻¹ T X t := by
    intro t
    have hu : IsUnit (ad_ext 1 T g t).det := by rw [(ad_det_star h t).1]; exact isUnit_one
    rw [(ad_G_hasDerivAt h t).derivEntrywise, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  refine ⟨_, ad_σ T g, ad_ext 1 T g, fun t ht ↦ ad_G_eq h ht,
    fun t ht ↦ by rw [hGX, ad_X_eq h ht], fun t ↦ by rw [hGX]; exact (ad_det_star h t).2,
    fun _ _ ↦ rfl, ad_σ_add h, hbal, fun j ↦ ?_, ?_⟩
  · simp only [ad_σ]
    rw [ad_G_eq h ⟨le_rfl, hT.le⟩, h.2.1, Matrix.one_mulVec]
  · exact eqn_cost hbal g X (fun j t ht ↦ by simp only [ad_σ]; rw [ad_G_eq h ht])
      (fun t ht ↦ ad_g_hasDerivAt h ht) (ad_σ_add h)

end SmoothedPolygons
