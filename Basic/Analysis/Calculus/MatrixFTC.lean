module

public import Basic.Analysis.Calculus.MatrixEntrywise
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Fundamental theorem of calculus and uniqueness of ODE solutions for matrix-valued curves

Bridges between classical (entrywise) derivatives and Carathéodory solutions, i.e. curves
`f : ℝ → Matrix m n ℝ` given entry by entry as indefinite integrals
`f t i j = f a i j + ∫ s in a..t, v s i j`, and uniqueness theorems for (linear) matrix ODEs.
The integral form below is, for `a = 0` and `b = T`, literally the body of
`SmoothedPolygons.IsIntegralCurve f v T`, so the lemmas producing or consuming it apply to
`IsIntegralCurve` directly.

All curves are real matrix-valued; the index types are arbitrary (`Fintype` where needed).

## API

FTC-2 (derivative to integral):
* `Matrix.integral_eq_of_hasDerivAtEntrywise_off_countable_of_le`: if `f` is continuous on
  `[a, b]`, has entrywise derivative `v t` at every `t ∈ Ioo a b \ S` with `S` countable, and the
  entries of `v` are interval integrable, then `∫ t in a..b, v t i j = f b i j - f a i j`;
* `Matrix.intervalIntegrable_of_hasDerivAtEntrywise_off_countable`: if moreover the entries of
  `v` are bounded on `Ioo a b \ S`, they are interval integrable (no measurability assumption is
  needed: `v` agrees a.e. with a derivative, which is measurable);
* `Matrix.eq_add_integral_of_hasDerivAtEntrywise_off_countable`: the conclusion in the integral
  form `∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume a b ∧
  ∀ t ∈ Set.Icc a b, f t i j = f a i j + ∫ s in a..t, v s i j`;
* `Matrix.eq_add_integral_of_hasDerivWithinAtEntrywise`: the same from derivatives within
  `Icc a b` at every point of `Icc a b`.

FTC-1 (integral to derivative), from the integral form:
* `Matrix.continuousOn_of_eq_add_integral`: `f` is continuous on `Icc a b`;
* `Matrix.hasDerivAtEntrywise_of_eq_add_integral`: `f` has entrywise derivative `v t` at every
  `t ∈ Ioo a b` where `v` is continuous;
* `Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral`: `f` has entrywise derivative `v t`
  within `Icc a b` at every `t ∈ Icc a b` where `v` is continuous within `Icc a b`.

Constant curves (zero derivative), for `f` continuous on `Icc a b`:
* `Matrix.constant_of_hasDerivWithinAtEntrywise_zero`: right derivatives (within `Ici t`) zero
  on `Ico a b` (entries in any normed field `𝕜` over `ℝ`);
* `Matrix.constant_of_hasDerivWithinAtEntrywise_Icc_zero`: derivatives within `Icc a b` zero on
  `Ico a b`;
* `Matrix.constant_of_hasDerivAtEntrywise_zero`: derivatives zero on `Ioo a b` (real entries).

Uniqueness for ODEs (Gronwall), for curves continuous on `Icc a b` with derivatives (within
`Ici t`, or within `Icc a b` for the `_Icc` versions) at every `t ∈ Ico a b`:
* `Matrix.eq_zero_of_hasDerivWithinAtEntrywise_bound` (and `_Icc`): if `D a = 0` and
  `|D' t i j| ≤ K * ∑ k, ∑ l, |D t k l|`, then `D = 0` on `Icc a b`;
* `Matrix.ODE_solution_unique_of_bound` (and `_Icc`): two solutions of `X' = G t X` with the same
  initial value agree on `Icc a b`, if
  `|G t P i j - G t Q i j| ≤ K * ∑ k, ∑ l, |P k l - Q k l|` for `t ∈ Ico a b`;
* `Matrix.ODE_solution_unique_affine` (and `_Icc`): the same for the affine equation
  `X' = L t X + F t` with `L t` linear and `|L t P i j| ≤ K * ∑ k, ∑ l, |P k l|` (e.g. `L t` with
  coefficients bounded by `K`);
* `Matrix.ODE_solution_unique_mul_right`: two solutions of `X' = X * A t` (derivatives within
  `Icc a b`) with `A` continuous on `Icc a b` and the same initial value agree on `Icc a b`;
* `Matrix.ODE_solution_unique_mul_left`: the same for `X' = A t * X`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace Matrix

variable {m n : Type*}

/-! ### From derivatives to integrals -/

section FTC2

variable {f v : ℝ → Matrix m n ℝ} {a b : ℝ} {S : Set ℝ}

/-- **FTC-2**, entrywise, for a curve differentiable off a countable set. -/
theorem integral_eq_of_hasDerivAtEntrywise_off_countable_of_le (hab : a ≤ b) (hS : S.Countable)
    (hf : ContinuousOn f (Icc a b)) (hderiv : ∀ t ∈ Ioo a b \ S, HasDerivAtEntrywise f (v t) t)
    (hint : ∀ i j, IntervalIntegrable (fun t ↦ v t i j) volume a b) (i : m) (j : n) :
    ∫ t in a..b, v t i j = f b i j - f a i j :=
  integral_eq_of_hasDerivAt_off_countable_of_le (fun t ↦ f t i j) (fun t ↦ v t i j) hab hS
    (continuousOn_iff_entrywise.1 hf i j) (fun t ht ↦ hderiv t ht i j) (hint i j)

/-- A bounded entrywise derivative (off a countable set) is interval integrable. No measurability
assumption is needed since `v` agrees almost everywhere with a derivative. -/
theorem intervalIntegrable_of_hasDerivAtEntrywise_off_countable (hab : a ≤ b) (hS : S.Countable)
    (hderiv : ∀ t ∈ Ioo a b \ S, HasDerivAtEntrywise f (v t) t)
    (hbdd : ∀ i j, ∃ C, ∀ t ∈ Ioo a b \ S, |v t i j| ≤ C) (i : m) (j : n) :
    IntervalIntegrable (fun t ↦ v t i j) volume a b := by
  obtain ⟨C, hC⟩ := hbdd i j
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc a b)), t ∈ Ioo a b \ S := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [(hS.union (countable_singleton b)).ae_notMem volume] with t ht htab
    simp only [mem_union, mem_singleton_iff, not_or] at ht
    exact ⟨⟨htab.1, lt_of_le_of_ne htab.2 ht.2⟩, ht.1⟩
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Integrable.of_bound ?_ C ?_
  · refine (stronglyMeasurable_deriv (fun s ↦ f s i j)).aestronglyMeasurable.congr ?_
    filter_upwards [hae] with t ht
    exact (hderiv t ht i j).deriv
  · filter_upwards [hae] with t ht
    rw [Real.norm_eq_abs]
    exact hC t ht

/-- **FTC-2** in integral form: a curve continuous on `[a, b]` with entrywise derivative `v` off a
countable set, and `v` interval integrable, is the indefinite integral of `v`. For `a = 0`,
`b = T` the conclusion is `SmoothedPolygons.IsIntegralCurve f v T`. -/
theorem eq_add_integral_of_hasDerivAtEntrywise_off_countable (hS : S.Countable)
    (hf : ContinuousOn f (Icc a b)) (hderiv : ∀ t ∈ Ioo a b \ S, HasDerivAtEntrywise f (v t) t)
    (hint : ∀ i j, IntervalIntegrable (fun t ↦ v t i j) volume a b) :
    ∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume a b ∧
      ∀ t ∈ Set.Icc a b, f t i j = f a i j + ∫ s in a..t, v s i j := by
  intro i j
  refine ⟨hint i j, fun t ht ↦ ?_⟩
  rw [integral_eq_of_hasDerivAtEntrywise_off_countable_of_le ht.1 hS
    (hf.mono (Icc_subset_Icc_right ht.2))
    (fun x hx ↦ hderiv x ⟨Ioo_subset_Ioo_right ht.2 hx.1, hx.2⟩)
    (fun k l ↦ (hint k l).mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ht))) i j]
  ring

/-- **FTC-2** in integral form, from derivatives within `Icc a b` at every point of `Icc a b`. -/
theorem eq_add_integral_of_hasDerivWithinAtEntrywise
    (hderiv : ∀ t ∈ Icc a b, HasDerivWithinAtEntrywise f (v t) (Icc a b) t)
    (hint : ∀ i j, IntervalIntegrable (fun t ↦ v t i j) volume a b) :
    ∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume a b ∧
      ∀ t ∈ Set.Icc a b, f t i j = f a i j + ∫ s in a..t, v s i j :=
  eq_add_integral_of_hasDerivAtEntrywise_off_countable countable_empty
    (HasDerivWithinAtEntrywise.continuousOn hderiv)
    (fun t ht ↦ (hderiv t (Ioo_subset_Icc_self ht.1)).hasDerivAtEntrywise
      (Icc_mem_nhds ht.1.1 ht.1.2)) hint

end FTC2

/-! ### From integrals to derivatives -/

section FTC1

variable {f v : ℝ → Matrix m n ℝ} {a b t : ℝ}

/-- A curve given in integral form is continuous. -/
theorem continuousOn_of_eq_add_integral
    (h : ∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume a b ∧
      ∀ t ∈ Set.Icc a b, f t i j = f a i j + ∫ s in a..t, v s i j) :
    ContinuousOn f (Icc a b) := by
  rcases le_or_gt a b with hab | hab
  · refine continuousOn_iff_entrywise.2 fun i j ↦ ?_
    have hc := intervalIntegral.continuousOn_primitive_interval' (h i j).1 left_mem_uIcc
    rw [uIcc_of_le hab] at hc
    exact (continuousOn_const.add hc).congr fun t ht ↦ (h i j).2 t ht
  · simp [Icc_eq_empty_of_lt hab]

/-- **FTC-1**: a curve given in integral form has entrywise derivative `v t` at every interior
point `t` where `v` is continuous. -/
theorem hasDerivAtEntrywise_of_eq_add_integral
    (h : ∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume a b ∧
      ∀ t ∈ Set.Icc a b, f t i j = f a i j + ∫ s in a..t, v s i j)
    (ht : t ∈ Ioo a b) (hv : ContinuousAt v t) : HasDerivAtEntrywise f (v t) t := by
  intro i j
  have hab : a ≤ b := (ht.1.trans ht.2).le
  have hint : IntervalIntegrable (fun s ↦ v s i j) volume a t :=
    (h i j).1.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc (Ioo_subset_Icc_self ht)))
  have hmeas : StronglyMeasurableAtFilter (fun s ↦ v s i j) (𝓝 t) :=
    ⟨Ioo a b, Ioo_mem_nhds ht.1 ht.2,
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 (h i j).1).mono_set
        Ioo_subset_Ioc_self).aestronglyMeasurable⟩
  have hd := intervalIntegral.integral_hasDerivAt_right hint hmeas
    (continuousAt_iff_entrywise.1 hv i j)
  exact (hd.const_add (f a i j)).congr_of_eventuallyEq
    (eventually_of_mem (Icc_mem_nhds ht.1 ht.2) fun s hs ↦ (h i j).2 s hs)

/-- **FTC-1** within `Icc a b`: a curve given in integral form has entrywise derivative `v t`
within `Icc a b` at every point `t ∈ Icc a b` where `v` is continuous within `Icc a b`. -/
theorem hasDerivWithinAtEntrywise_of_eq_add_integral
    (h : ∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume a b ∧
      ∀ t ∈ Set.Icc a b, f t i j = f a i j + ∫ s in a..t, v s i j)
    (ht : t ∈ Icc a b) (hv : ContinuousWithinAt v (Icc a b) t) :
    HasDerivWithinAtEntrywise f (v t) (Icc a b) t := by
  intro i j
  have : Fact (t ∈ Icc a b) := ⟨ht⟩
  have hab : a ≤ b := ht.1.trans ht.2
  have hint : IntervalIntegrable (fun s ↦ v s i j) volume a t :=
    (h i j).1.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ht))
  have hmeas : StronglyMeasurableAtFilter (fun s ↦ v s i j) (𝓝[Icc a b] t) :=
    ⟨Icc a b, self_mem_nhdsWithin,
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 (h i j).1).aestronglyMeasurable⟩
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (s := Icc a b) (t := Icc a b)
    hint hmeas (continuousWithinAt_iff_entrywise.1 hv i j)
  exact (hd.const_add (f a i j)).congr (fun s hs ↦ (h i j).2 s hs) ((h i j).2 t ht)

end FTC1

/-! ### Curves with zero derivative -/

section Constant

variable {a b : ℝ}

/-- `Icc a b` is a right neighbourhood of every point of `Ico a b`. -/
private lemma Icc_mem_nhdsGE_of_mem_Ico {t : ℝ} (ht : t ∈ Ico a b) : Icc a b ∈ 𝓝[≥] t :=
  mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)

/-- A curve, continuous on `[a, b]`, with zero right derivatives on `[a, b)` is constant. -/
theorem constant_of_hasDerivWithinAtEntrywise_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] {f : ℝ → Matrix m n 𝕜} (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise f 0 (Ici t) t) :
    ∀ t ∈ Icc a b, f t = f a := fun t ht ↦ ext fun i j ↦
  constant_of_has_deriv_right_zero (continuousOn_iff_entrywise.1 hf i j)
    (fun x hx ↦ hderiv x hx i j) t ht

/-- A curve, continuous on `[a, b]`, with zero derivatives within `[a, b]` on `[a, b)` is
constant. -/
theorem constant_of_hasDerivWithinAtEntrywise_Icc_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] {f : ℝ → Matrix m n 𝕜} (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise f 0 (Icc a b) t) :
    ∀ t ∈ Icc a b, f t = f a :=
  constant_of_hasDerivWithinAtEntrywise_zero hf fun t ht ↦
    (hderiv t ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem_Ico ht)

/-- A real curve, continuous on `[a, b]`, with zero derivatives on `(a, b)` is constant. -/
theorem constant_of_hasDerivAtEntrywise_zero {f : ℝ → Matrix m n ℝ}
    (hf : ContinuousOn f (Icc a b)) (hderiv : ∀ t ∈ Ioo a b, HasDerivAtEntrywise f 0 t) :
    ∀ t ∈ Icc a b, f t = f a := by
  intro t ht
  have h := eq_add_integral_of_hasDerivAtEntrywise_off_countable (v := fun _ ↦ 0) countable_empty
    hf (fun s hs ↦ hderiv s hs.1) (fun _ _ ↦ intervalIntegrable_const)
  ext i j
  simpa using (h i j).2 t ht

end Constant

/-! ### Uniqueness for ODEs -/

section ODE

variable [Fintype m] [Fintype n] {a b K : ℝ}

/-- **Gronwall**, entrywise: a curve vanishing at `a` whose right derivative is bounded entrywise
by `K` times the sum of the absolute values of its entries vanishes on `[a, b]`. -/
theorem eq_zero_of_hasDerivWithinAtEntrywise_bound {D V : ℝ → Matrix m n ℝ}
    (hD : ContinuousOn D (Icc a b))
    (hD' : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise D (V t) (Ici t) t) (ha : D a = 0)
    (hV : ∀ t ∈ Ico a b, ∀ i j, |V t i j| ≤ K * ∑ k, ∑ l, |D t k l|) :
    ∀ t ∈ Icc a b, D t = 0 := by
  open scoped Matrix.Norms.Elementwise in
  refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (K := max K 0 * (Fintype.card m * Fintype.card n)) hD
    (fun t ht ↦ (hD' t ht).hasDerivWithinAt) ha fun t ht ↦ ?_
  have hsum : ∑ k, ∑ l, |D t k l| ≤ Fintype.card m * Fintype.card n * ‖D t‖ := by
    calc ∑ k, ∑ l, |D t k l| ≤ ∑ _k : m, ∑ _l : n, ‖D t‖ :=
          Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun l _ ↦ by
            simpa only [Real.norm_eq_abs] using norm_apply_le_norm (D t) (i := k) (j := l)
      _ = Fintype.card m * Fintype.card n * ‖D t‖ := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  refine (norm_le_iff (by positivity)).2 fun i j ↦ ?_
  rw [Real.norm_eq_abs]
  calc |V t i j| ≤ K * ∑ k, ∑ l, |D t k l| := hV t ht i j
    _ ≤ max K 0 * ∑ k, ∑ l, |D t k l| :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max K 0 * (Fintype.card m * Fintype.card n * ‖D t‖) :=
        mul_le_mul_of_nonneg_left hsum (le_max_right _ _)
    _ = max K 0 * (Fintype.card m * Fintype.card n) * ‖D t‖ := by ring

/-- **Gronwall**, entrywise, with derivatives within `Icc a b`. -/
theorem eq_zero_of_hasDerivWithinAtEntrywise_bound_Icc {D V : ℝ → Matrix m n ℝ}
    (hD : ContinuousOn D (Icc a b))
    (hD' : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise D (V t) (Icc a b) t) (ha : D a = 0)
    (hV : ∀ t ∈ Ico a b, ∀ i j, |V t i j| ≤ K * ∑ k, ∑ l, |D t k l|) :
    ∀ t ∈ Icc a b, D t = 0 :=
  eq_zero_of_hasDerivWithinAtEntrywise_bound hD
    (fun t ht ↦ (hD' t ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem_Ico ht)) ha hV

/-- Uniqueness of solutions of `X' = G t X` on `[a, b]` with a given initial value, for a vector
field `G t` which is Lipschitz in the sense
`|G t P i j - G t Q i j| ≤ K * ∑ k, ∑ l, |P k l - Q k l|`. -/
theorem ODE_solution_unique_of_bound {G : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {X Y : ℝ → Matrix m n ℝ}
    (hG : ∀ t ∈ Ico a b, ∀ P Q : Matrix m n ℝ, ∀ i j,
      |G t P i j - G t Q i j| ≤ K * ∑ k, ∑ l, |P k l - Q k l|)
    (hX : ContinuousOn X (Icc a b))
    (hX' : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise X (G t (X t)) (Ici t) t)
    (hY : ContinuousOn Y (Icc a b))
    (hY' : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise Y (G t (Y t)) (Ici t) t)
    (ha : X a = Y a) : EqOn X Y (Icc a b) := fun t ht ↦
  sub_eq_zero.1 <| eq_zero_of_hasDerivWithinAtEntrywise_bound (D := fun s ↦ X s - Y s)
    (V := fun s ↦ G s (X s) - G s (Y s)) (hX.sub hY) (fun s hs ↦ (hX' s hs).sub (hY' s hs))
    (sub_eq_zero.2 ha) (fun s hs i j ↦ hG s hs (X s) (Y s) i j) t ht

/-- Uniqueness of solutions of `X' = G t X` on `[a, b]` with a given initial value, with
derivatives within `Icc a b`. -/
theorem ODE_solution_unique_of_bound_Icc {G : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {X Y : ℝ → Matrix m n ℝ}
    (hG : ∀ t ∈ Ico a b, ∀ P Q : Matrix m n ℝ, ∀ i j,
      |G t P i j - G t Q i j| ≤ K * ∑ k, ∑ l, |P k l - Q k l|)
    (hX : ContinuousOn X (Icc a b))
    (hX' : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise X (G t (X t)) (Icc a b) t)
    (hY : ContinuousOn Y (Icc a b))
    (hY' : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise Y (G t (Y t)) (Icc a b) t)
    (ha : X a = Y a) : EqOn X Y (Icc a b) :=
  ODE_solution_unique_of_bound hG hX
    (fun t ht ↦ (hX' t ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem_Ico ht)) hY
    (fun t ht ↦ (hY' t ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem_Ico ht)) ha

/-- Uniqueness of solutions of the affine equation `X' = L t X + F t` on `[a, b]` with a given
initial value, where each `L t` is linear with `|L t P i j| ≤ K * ∑ k, ∑ l, |P k l|` (for
instance, `L t` has coefficients bounded by `K`). -/
theorem ODE_solution_unique_affine {L : ℝ → Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ}
    {F X Y : ℝ → Matrix m n ℝ}
    (hL : ∀ t ∈ Ico a b, ∀ P : Matrix m n ℝ, ∀ i j, |L t P i j| ≤ K * ∑ k, ∑ l, |P k l|)
    (hX : ContinuousOn X (Icc a b))
    (hX' : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise X (L t (X t) + F t) (Ici t) t)
    (hY : ContinuousOn Y (Icc a b))
    (hY' : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise Y (L t (Y t) + F t) (Ici t) t)
    (ha : X a = Y a) : EqOn X Y (Icc a b) :=
  ODE_solution_unique_of_bound (G := fun t P ↦ L t P + F t) (fun t ht P Q i j ↦ by
    simpa [map_sub] using hL t ht (P - Q) i j) hX hX' hY hY' ha

/-- Uniqueness of solutions of the affine equation `X' = L t X + F t` on `[a, b]` with a given
initial value, with derivatives within `Icc a b`. -/
theorem ODE_solution_unique_affine_Icc {L : ℝ → Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ}
    {F X Y : ℝ → Matrix m n ℝ}
    (hL : ∀ t ∈ Ico a b, ∀ P : Matrix m n ℝ, ∀ i j, |L t P i j| ≤ K * ∑ k, ∑ l, |P k l|)
    (hX : ContinuousOn X (Icc a b))
    (hX' : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise X (L t (X t) + F t) (Icc a b) t)
    (hY : ContinuousOn Y (Icc a b))
    (hY' : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise Y (L t (Y t) + F t) (Icc a b) t)
    (ha : X a = Y a) : EqOn X Y (Icc a b) :=
  ODE_solution_unique_affine hL hX
    (fun t ht ↦ (hX' t ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem_Ico ht)) hY
    (fun t ht ↦ (hY' t ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem_Ico ht)) ha

/-- A matrix curve continuous on a compact interval has uniformly bounded entries there. -/
private lemma exists_abs_le_of_continuousOn {p q : Type*} [Finite p] [Finite q]
    {A : ℝ → Matrix p q ℝ} (hA : ContinuousOn A (Icc a b)) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ k l, |A t k l| ≤ C := by
  have := Fintype.ofFinite p
  have := Fintype.ofFinite q
  open scoped Matrix.Norms.Elementwise in
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  refine ⟨max C 0, le_max_right _ _, fun t ht k l ↦ ?_⟩
  rw [← Real.norm_eq_abs]
  exact (norm_apply_le_norm (A t)).trans ((hC t ht).trans (le_max_left _ _))

private lemma abs_mul_apply_le_right (P : Matrix m n ℝ) (A : Matrix n n ℝ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ k l, |A k l| ≤ C) (i : m) (j : n) :
    |(P * A) i j| ≤ C * ∑ k, ∑ l, |P k l| := by
  calc |(P * A) i j| = |∑ k, P i k * A k j| := by rw [Matrix.mul_apply]
    _ ≤ ∑ k, |P i k * A k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, C * |P i k| := Finset.sum_le_sum fun k _ ↦ by
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hC k j) (abs_nonneg _)
    _ = C * ∑ k, |P i k| := (Finset.mul_sum _ _ _).symm
    _ ≤ C * ∑ k, ∑ l, |P k l| := mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (f := fun k ↦ ∑ l, |P k l|)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)) hC0

private lemma abs_mul_apply_le_left (A : Matrix m m ℝ) (P : Matrix m n ℝ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ k l, |A k l| ≤ C) (i : m) (j : n) :
    |(A * P) i j| ≤ C * ∑ k, ∑ l, |P k l| := by
  calc |(A * P) i j| = |∑ k, A i k * P k j| := by rw [Matrix.mul_apply]
    _ ≤ ∑ k, |A i k * P k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, C * |P k j| := Finset.sum_le_sum fun k _ ↦ by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hC i k) (abs_nonneg _)
    _ = C * ∑ k, |P k j| := (Finset.mul_sum _ _ _).symm
    _ ≤ C * ∑ k, ∑ l, |P k l| := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun k _ ↦ Finset.single_le_sum (f := fun l ↦ |P k l|)
          (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)) hC0

omit [Fintype m] in
/-- Uniqueness of solutions of the linear equation `X' = X * A t` on `[a, b]` with a given initial
value, for `A` continuous on `[a, b]`. -/
theorem ODE_solution_unique_mul_right [Finite m] {A : ℝ → Matrix n n ℝ} {X Y : ℝ → Matrix m n ℝ}
    (hA : ContinuousOn A (Icc a b)) (hX : ContinuousOn X (Icc a b))
    (hX' : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise X (X t * A t) (Icc a b) t)
    (hY : ContinuousOn Y (Icc a b))
    (hY' : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise Y (Y t * A t) (Icc a b) t)
    (ha : X a = Y a) : EqOn X Y (Icc a b) := by
  have := Fintype.ofFinite m
  obtain ⟨C, hC0, hC⟩ := exists_abs_le_of_continuousOn hA
  refine ODE_solution_unique_of_bound_Icc (G := fun t P ↦ P * A t) (K := C)
    (fun t ht P Q i j ↦ ?_) hX hX' hY hY' ha
  rw [← Matrix.sub_apply, ← Matrix.sub_mul]
  exact abs_mul_apply_le_right _ _ hC0 (hC t (Ico_subset_Icc_self ht)) i j

omit [Fintype n] in
/-- Uniqueness of solutions of the linear equation `X' = A t * X` on `[a, b]` with a given initial
value, for `A` continuous on `[a, b]`. -/
theorem ODE_solution_unique_mul_left [Finite n] {A : ℝ → Matrix m m ℝ} {X Y : ℝ → Matrix m n ℝ}
    (hA : ContinuousOn A (Icc a b)) (hX : ContinuousOn X (Icc a b))
    (hX' : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise X (A t * X t) (Icc a b) t)
    (hY : ContinuousOn Y (Icc a b))
    (hY' : ∀ t ∈ Ico a b, HasDerivWithinAtEntrywise Y (A t * Y t) (Icc a b) t)
    (ha : X a = Y a) : EqOn X Y (Icc a b) := by
  have := Fintype.ofFinite n
  obtain ⟨C, hC0, hC⟩ := exists_abs_le_of_continuousOn hA
  refine ODE_solution_unique_of_bound_Icc (G := fun t P ↦ A t * P) (K := C)
    (fun t ht P Q i j ↦ ?_) hX hX' hY hY' ha
  rw [← Matrix.sub_apply, ← Matrix.mul_sub]
  exact abs_mul_apply_le_left _ _ hC0 (hC t (Ico_subset_Icc_self ht)) i j

end ODE

end Matrix
