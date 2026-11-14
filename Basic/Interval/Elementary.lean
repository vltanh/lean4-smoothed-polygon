module

public import Basic.Interval.Dyadic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Interval enclosures of `sin`, `cos` and `arctan`

Enclosures by Taylor polynomials with a remainder bound, evaluated in fixed-point dyadic interval
arithmetic (`Basic/Interval/Dyadic.lean`), computable by the kernel.

* **Remainder bounds.** The Taylor series of `sin`, `cos` (for `|y| ≤ 1`) and `arctan` (for
  `|y| < 1`) are alternating with decreasing terms, so a partial sum is within the first omitted
  term (`Real.abs_sin_sub_altSum_le`, `Real.abs_cos_sub_altSum_le`, `Real.abs_arctan_sub_altSum_le`,
  from `alternating_series_error_bound`).
* **Series in interval arithmetic** (`altLoop`, `seriesEnclosure`): the terms are computed by a
  recurrence (`term (i + 1) = term i · y² / …`) and summed until a term is below `2⁻ᵖ`; the last
  term bounds the remainder.
* **`sin` and `cos` at a point** (`sinCosPoint`): the argument is halved `k` times until it is at
  most `1/2`, the two series are summed, and `sin 2y = 2 sin y cos y`, `cos 2y = 1 - 2 sin² y` are
  applied `k` times.
* **`sin` and `cos` on an interval** (`sinCos`): from the values at the midpoint `c` by
  `sin (c + h) = sin c cos h + cos c sin h` with `cos h ∈ [1 - r²/2, 1]`, `sin h ∈ [-r, r]` for
  `|h| ≤ r` (second-order accurate in the radius `r`).
* **`arctan` on an interval** (`arctan`): `arctan` is increasing, so its values at the endpoints
  bound it; at a point `|y| < 1` the series is used, otherwise `(-2, 2) ⊇ (-π/2, π/2)`.
-/

@[expose] public section

open Finset

/-! ### Remainder bounds -/

namespace Real

/-- The partial sum `∑_{i < n} (-1)ⁱ f i` of an alternating series. -/
noncomputable def altSum (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, (-1) ^ i * f i

/-- The terms `y^(2i+1) / (2i+1)!` of the sine series. -/
noncomputable def sinTerm (y : ℝ) (i : ℕ) : ℝ := y ^ (2 * i + 1) / (2 * i + 1).factorial

/-- The terms `y^(2i) / (2i)!` of the cosine series. -/
noncomputable def cosTerm (y : ℝ) (i : ℕ) : ℝ := y ^ (2 * i) / (2 * i).factorial

/-- The terms `y^(2i+1) / (2i+1)` of the arctangent series. -/
noncomputable def atanTerm (y : ℝ) (i : ℕ) : ℝ := y ^ (2 * i + 1) / (2 * i + 1 : ℕ)

theorem altSum_succ (f : ℕ → ℝ) (n : ℕ) :
    altSum f (n + 1) = altSum f n + (-1) ^ n * f n := by
  simp [altSum, sum_range_succ]

theorem sinTerm_succ (y : ℝ) (i : ℕ) :
    sinTerm y (i + 1) = sinTerm y i * y ^ 2 / ((2 * i + 2) * (2 * i + 3) : ℕ) := by
  unfold sinTerm
  rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  have : ((2 * i + 1).factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem cosTerm_succ (y : ℝ) (i : ℕ) :
    cosTerm y (i + 1) = cosTerm y i * y ^ 2 / ((2 * i + 1) * (2 * i + 2) : ℕ) := by
  unfold cosTerm
  rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  have : ((2 * i).factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem atanTerm_succ (y : ℝ) (i : ℕ) :
    atanTerm y (i + 1) = (2 * i + 1 : ℕ) * (atanTerm y i * y ^ 2) / (2 * i + 3 : ℕ) := by
  unfold atanTerm
  rw [show 2 * (i + 1) + 1 = 2 * i + 3 by ring]
  have : ((2 * i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem sinTerm_zero (y : ℝ) : sinTerm y 0 = y := by simp [sinTerm]

theorem cosTerm_zero (y : ℝ) : cosTerm y 0 = 1 := by simp [cosTerm]

theorem atanTerm_zero (y : ℝ) : atanTerm y 0 = y := by simp [atanTerm]

/-- The alternating series remainder for a nonnegative antitone summable sequence. -/
private theorem abs_sub_altSum_le {f : ℕ → ℝ} {F : ℝ} (hF : HasSum (fun i ↦ (-1) ^ i * f i) F)
    (hf : Antitone f) (hs : Summable f) (n : ℕ) : |F - altSum f n| ≤ f n := by
  have := alternating_series_error_bound f hf hs n
  rwa [hF.tsum_eq] at this

/-- **The sine remainder**: `|sin y - ∑_{i<n} (-1)ⁱ y^(2i+1)/(2i+1)!| ≤ |y|^(2n+1)/(2n+1)!` for
`|y| ≤ 1`. -/
theorem abs_sin_sub_altSum_le {y : ℝ} (hy : |y| ≤ 1) (n : ℕ) :
    |sin y - altSum (sinTerm y) n| ≤ |sinTerm y n| := by
  -- the case `0 ≤ y ≤ 1`
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → |sin y - altSum (sinTerm y) n| ≤ |sinTerm y n| := by
    intro y h0 h1
    have hnn : ∀ i, 0 ≤ sinTerm y i := fun i ↦ by unfold sinTerm; positivity
    have hanti : Antitone (sinTerm y) := by
      refine antitone_nat_of_succ_le fun i ↦ ?_
      rw [sinTerm_succ]
      have hy2 : y ^ 2 ≤ 1 := by nlinarith
      have hd : (1 : ℝ) ≤ ((2 * i + 2) * (2 * i + 3) : ℕ) := by
        have : 1 ≤ (2 * i + 2) * (2 * i + 3) := by nlinarith
        exact_mod_cast this
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hnn i]
    have hsum : Summable (sinTerm y) :=
      (Real.summable_pow_div_factorial y).comp_injective
        (fun a b h ↦ by simpa using h : Function.Injective fun i : ℕ ↦ 2 * i + 1)
    have hF : HasSum (fun i ↦ (-1) ^ i * sinTerm y i) (sin y) := by
      convert Real.hasSum_sin y using 1
      funext i; simp [sinTerm, mul_div_assoc]
    rw [abs_of_nonneg (hnn n)]
    exact abs_sub_altSum_le hF hanti hsum n
  rcases le_total 0 y with h | h
  · exact key y h (abs_le.1 hy).2
  · have e1 : ∀ i, sinTerm (-y) i = -sinTerm y i := fun i ↦ by
      simp [sinTerm, Odd.neg_pow (⟨i, rfl⟩ : Odd (2 * i + 1)), neg_div]
    have e2 : altSum (sinTerm (-y)) n = -altSum (sinTerm y) n := by
      simp [altSum, e1, Finset.sum_neg_distrib]
    have := key (-y) (by linarith) (by linarith [(abs_le.1 hy).1])
    rw [Real.sin_neg, e2, e1, abs_neg] at this
    rwa [show -sin y - -altSum (sinTerm y) n = -(sin y - altSum (sinTerm y) n) by ring,
      abs_neg] at this

/-- **The cosine remainder**: `|cos y - ∑_{i<n} (-1)ⁱ y^(2i)/(2i)!| ≤ y^(2n)/(2n)!` for
`|y| ≤ 1`. -/
theorem abs_cos_sub_altSum_le {y : ℝ} (hy : |y| ≤ 1) (n : ℕ) :
    |cos y - altSum (cosTerm y) n| ≤ |cosTerm y n| := by
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → |cos y - altSum (cosTerm y) n| ≤ |cosTerm y n| := by
    intro y h0 h1
    have hnn : ∀ i, 0 ≤ cosTerm y i := fun i ↦ by unfold cosTerm; positivity
    have hanti : Antitone (cosTerm y) := by
      refine antitone_nat_of_succ_le fun i ↦ ?_
      rw [cosTerm_succ]
      have hy2 : y ^ 2 ≤ 1 := by nlinarith
      have hd : (1 : ℝ) ≤ ((2 * i + 1) * (2 * i + 2) : ℕ) := by
        have : 1 ≤ (2 * i + 1) * (2 * i + 2) := by nlinarith
        exact_mod_cast this
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hnn i]
    have hsum : Summable (cosTerm y) :=
      (Real.summable_pow_div_factorial y).comp_injective
        (fun a b h ↦ by simpa using h : Function.Injective fun i : ℕ ↦ 2 * i)
    have hF : HasSum (fun i ↦ (-1) ^ i * cosTerm y i) (cos y) := by
      convert Real.hasSum_cos y using 1
      funext i; simp [cosTerm, mul_div_assoc]
    rw [abs_of_nonneg (hnn n)]
    exact abs_sub_altSum_le hF hanti hsum n
  rcases le_total 0 y with h | h
  · exact key y h (abs_le.1 hy).2
  · have e1 : ∀ i, cosTerm (-y) i = cosTerm y i := fun i ↦ by
      simp [cosTerm, Even.neg_pow (⟨i, two_mul i⟩ : Even (2 * i))]
    have e2 : altSum (cosTerm (-y)) n = altSum (cosTerm y) n := by simp [altSum, e1]
    have := key (-y) (by linarith) (by linarith [(abs_le.1 hy).1])
    rwa [Real.cos_neg, e2, e1] at this

/-- **The arctangent remainder**:
`|arctan y - ∑_{i<n} (-1)ⁱ y^(2i+1)/(2i+1)| ≤ |y|^(2n+1)/(2n+1)` for `|y| < 1`. -/
theorem abs_arctan_sub_altSum_le {y : ℝ} (hy : |y| < 1) (n : ℕ) :
    |arctan y - altSum (atanTerm y) n| ≤ |atanTerm y n| := by
  have key : ∀ y : ℝ, 0 ≤ y → y < 1 → |arctan y - altSum (atanTerm y) n| ≤ |atanTerm y n| := by
    intro y h0 h1
    have hnn : ∀ i, 0 ≤ atanTerm y i := fun i ↦ by unfold atanTerm; positivity
    have hanti : Antitone (atanTerm y) := by
      refine antitone_nat_of_succ_le fun i ↦ ?_
      unfold atanTerm
      rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by ring, pow_add]
      have hy2 : y ^ 2 ≤ 1 := by nlinarith
      have hp : 0 ≤ y ^ (2 * i + 1) := by positivity
      have hd : ((2 * i + 1 : ℕ) : ℝ) ≤ ((2 * i + 1 + 2 : ℕ) : ℝ) := by exact_mod_cast by omega
      have hd0 : (0 : ℝ) < ((2 * i + 1 : ℕ) : ℝ) := by positivity
      calc y ^ (2 * i + 1) * y ^ 2 / ((2 * i + 1 + 2 : ℕ) : ℝ)
          ≤ y ^ (2 * i + 1) / ((2 * i + 1 + 2 : ℕ) : ℝ) := by
            gcongr; nlinarith
        _ ≤ y ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ) := div_le_div_of_nonneg_left hp hd0 hd
    have hsum : Summable (atanTerm y) := by
      refine Summable.of_nonneg_of_le hnn (fun i ↦ ?_) (summable_geometric_of_lt_one h0 h1)
      unfold atanTerm
      have h1' : (1 : ℝ) ≤ ((2 * i + 1 : ℕ) : ℝ) := by exact_mod_cast by omega
      calc y ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ) ≤ y ^ (2 * i + 1) :=
            div_le_self (by positivity) h1'
        _ ≤ y ^ i := pow_le_pow_of_le_one h0 h1.le (by omega)
    have hF : HasSum (fun i ↦ (-1) ^ i * atanTerm y i) (arctan y) := by
      have h := Real.hasSum_arctan (x := y) (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
      convert h using 1
      funext i; simp [atanTerm, mul_div_assoc]
    rw [abs_of_nonneg (hnn n)]
    exact abs_sub_altSum_le hF hanti hsum n
  rcases le_total 0 y with h | h
  · exact key y h (abs_lt.1 hy).2
  · have e1 : ∀ i, atanTerm (-y) i = -atanTerm y i := fun i ↦ by
      simp [atanTerm, Odd.neg_pow (⟨i, rfl⟩ : Odd (2 * i + 1)), neg_div]
    have e2 : altSum (atanTerm (-y)) n = -altSum (atanTerm y) n := by
      simp [altSum, e1, Finset.sum_neg_distrib]
    have := key (-y) (by linarith) (by linarith [(abs_lt.1 hy).1])
    rw [Real.arctan_neg, e2, e1, abs_neg] at this
    rwa [show -arctan y - -altSum (atanTerm y) n = -(arctan y - altSum (atanTerm y) n) by ring,
      abs_neg] at this

end Real

namespace DyadicInterval

/-! ### Alternating series in interval arithmetic -/

/-- Sum an alternating series: `T` encloses the current term, `S` the partial sum before it,
`next i T` the term `i + 1`; stop when the term is at most `2⁻ᵖ` or the fuel runs out. -/
def altLoop (next : ℕ → DyadicInterval → DyadicInterval) :
    ℕ → ℕ → DyadicInterval → DyadicInterval → DyadicInterval × DyadicInterval
  | 0, _, T, S => (T, S)
  | n + 1, i, T, S =>
    if T.mag ≤ 1 then (T, S)
    else altLoop next n (i + 1) (next i T) (if i % 2 = 0 then add S T else sub S T)

theorem altLoop_sound {p : ℕ} {f : ℕ → ℝ} {next : ℕ → DyadicInterval → DyadicInterval}
    (hnext : ∀ i T, Mem p T (f i) → Mem p (next i T) (f (i + 1))) :
    ∀ (n i : ℕ) (T S : DyadicInterval), Mem p T (f i) → Mem p S (Real.altSum f i) →
      ∃ j, Mem p (altLoop next n i T S).1 (f j) ∧ Mem p (altLoop next n i T S).2 (Real.altSum f j)
  | 0, i, T, S, hT, hS => ⟨i, hT, hS⟩
  | n + 1, i, T, S, hT, hS => by
    unfold altLoop
    by_cases h : T.mag ≤ 1
    · rw [ite_eq_left h]; exact ⟨i, hT, hS⟩
    · rw [ite_eq_right h]
      refine altLoop_sound hnext n (i + 1) _ _ (hnext i T hT) ?_
      rw [Real.altSum_succ]
      by_cases hi : i % 2 = 0
      · rw [ite_eq_left hi]
        have : (-1 : ℝ) ^ i = 1 := Even.neg_one_pow (Nat.even_iff.2 hi)
        rw [this, one_mul]; exact mem_add hS hT
      · rw [ite_eq_right hi]
        have : (-1 : ℝ) ^ i = -1 := Odd.neg_one_pow (Nat.odd_iff.2 (by omega))
        rw [this, neg_one_mul, ← sub_eq_add_neg]; exact mem_sub hS hT

/-- The sum of an alternating series with the last computed term as the remainder bound. -/
def seriesEnclosure (next : ℕ → DyadicInterval → DyadicInterval) (fuel : ℕ)
    (T₀ : DyadicInterval) : DyadicInterval :=
  let R := altLoop next fuel 0 T₀ ⟨0, 0⟩
  add R.2 ⟨-(R.1.mag : ℤ), R.1.mag⟩

theorem mem_seriesEnclosure {p : ℕ} {f : ℕ → ℝ} {F : ℝ}
    {next : ℕ → DyadicInterval → DyadicInterval}
    (hnext : ∀ i T, Mem p T (f i) → Mem p (next i T) (f (i + 1)))
    (hF : ∀ n, |F - Real.altSum f n| ≤ |f n|) (fuel : ℕ) {T₀ : DyadicInterval}
    (h₀ : Mem p T₀ (f 0)) : Mem p (seriesEnclosure next fuel T₀) F := by
  have hS0 : Mem p ⟨0, 0⟩ (Real.altSum f 0) := by simp [Mem, Real.altSum]
  obtain ⟨j, hT, hS⟩ := altLoop_sound hnext fuel 0 T₀ ⟨0, 0⟩ h₀ hS0
  have hr : Mem p ⟨-((altLoop next fuel 0 T₀ ⟨0, 0⟩).1.mag : ℤ),
      (altLoop next fuel 0 T₀ ⟨0, 0⟩).1.mag⟩ (F - Real.altSum f j) := by
    have h1 := (hF j).trans (abs_le_mag hT)
    obtain ⟨h2, h3⟩ := abs_le.1 h1
    refine ⟨?_, ?_⟩
    · simp only [Int.cast_neg, Int.cast_natCast, neg_div]; exact h2
    · simpa using h3
  have := mem_add hS hr
  rwa [add_sub_cancel] at this

/-! ### `sin` and `cos` -/

/-- The recurrence of the sine terms: multiply by `y²` and divide by `(2i+2)(2i+3)`. -/
def sinNext (p : ℕ) (Y2 : DyadicInterval) (i : ℕ) (T : DyadicInterval) : DyadicInterval :=
  divNat (mul p T Y2) ((2 * i + 2) * (2 * i + 3))

/-- The recurrence of the cosine terms: multiply by `y²` and divide by `(2i+1)(2i+2)`. -/
def cosNext (p : ℕ) (Y2 : DyadicInterval) (i : ℕ) (T : DyadicInterval) : DyadicInterval :=
  divNat (mul p T Y2) ((2 * i + 1) * (2 * i + 2))

/-- The interval `[-1, 1]`. -/
def unit (p : ℕ) : DyadicInterval := ⟨-scale p, scale p⟩

theorem mem_unit (p : ℕ) {x : ℝ} (hx : |x| ≤ 1) : Mem p (unit p) x := by
  have hp := two_pow_pos' p
  obtain ⟨h1, h2⟩ := abs_le.1 hx
  constructor
  · simp only [unit, Int.cast_neg, scale_cast, neg_div, div_self hp.ne']; exact h1
  · simp only [unit, scale_cast, div_self hp.ne']; exact h2

theorem mem_one (p : ℕ) : Mem p (ofInt (scale p)) 1 := by
  have := mem_ofInt p (scale p)
  rwa [scale_cast, div_self (two_pow_pos' p).ne'] at this

/-- `(sin y, cos y)` for `|y| ≤ 1` by the Taylor series (`[-1, 1]` otherwise). -/
def sinCosSeries (p : ℕ) (Y : DyadicInterval) : DyadicInterval × DyadicInterval :=
  if (Y.mag : ℤ) ≤ scale p then
    (seriesEnclosure (sinNext p (sq p Y)) (p + 8) Y,
      seriesEnclosure (cosNext p (sq p Y)) (p + 8) (ofInt (scale p)))
  else (unit p, unit p)

theorem mem_sinCosSeries {p : ℕ} {Y : DyadicInterval} {y : ℝ} (hy : Mem p Y y) :
    Mem p (sinCosSeries p Y).1 (Real.sin y) ∧ Mem p (sinCosSeries p Y).2 (Real.cos y) := by
  unfold sinCosSeries
  split_ifs with h
  · have hy1 : |y| ≤ 1 := by
      refine (abs_le_mag hy).trans ?_
      rw [div_le_one (two_pow_pos' p)]
      have : ((Y.mag : ℤ) : ℝ) ≤ ((scale p : ℤ) : ℝ) := by exact_mod_cast h
      simpa [scale_cast] using this
    have hy2 := mem_sq hy
    constructor
    · refine mem_seriesEnclosure (f := Real.sinTerm y) (fun i T hT ↦ ?_)
        (Real.abs_sin_sub_altSum_le hy1) _ (by rwa [Real.sinTerm_zero])
      rw [Real.sinTerm_succ]
      exact mem_divNat (by positivity) (mem_mul hT hy2)
    · refine mem_seriesEnclosure (f := Real.cosTerm y) (fun i T hT ↦ ?_)
        (Real.abs_cos_sub_altSum_le hy1) _ (by rw [Real.cosTerm_zero]; exact mem_one p)
      rw [Real.cosTerm_succ]
      exact mem_divNat (by positivity) (mem_mul hT hy2)
  · exact ⟨mem_unit p (Real.abs_sin_le_one y), mem_unit p (Real.abs_cos_le_one y)⟩

/-- The double-angle step `(sin y, cos y) ↦ (2 sin y cos y, 1 - 2 sin² y)`. -/
def doubleSC (p : ℕ) (SC : DyadicInterval × DyadicInterval) : DyadicInterval × DyadicInterval :=
  (clampUnit p (smulNat 2 (mul p SC.1 SC.2)),
    clampUnit p (sub (ofInt (scale p)) (smulNat 2 (sq p SC.1))))

theorem mem_doubleSC {p : ℕ} {SC : DyadicInterval × DyadicInterval} {y : ℝ}
    (h : Mem p SC.1 (Real.sin y) ∧ Mem p SC.2 (Real.cos y)) :
    Mem p (doubleSC p SC).1 (Real.sin (2 * y)) ∧ Mem p (doubleSC p SC).2 (Real.cos (2 * y)) := by
  constructor
  · refine mem_clampUnit ?_ (Real.abs_sin_le_one _)
    rw [Real.sin_two_mul, mul_assoc]
    exact_mod_cast mem_smulNat 2 (mem_mul h.1 h.2)
  · refine mem_clampUnit ?_ (Real.abs_cos_le_one _)
    rw [Real.cos_two_mul, Real.cos_sq', show 2 * (1 - Real.sin y ^ 2) - 1 =
      1 - (2 : ℕ) * Real.sin y ^ 2 by push_cast; ring]
    exact mem_sub (mem_one p) (mem_smulNat 2 (mem_sq h.1))

/-- `k` double-angle steps. -/
def iterDouble (p : ℕ) : ℕ → DyadicInterval × DyadicInterval → DyadicInterval × DyadicInterval
  | 0, SC => SC
  | k + 1, SC => doubleSC p (iterDouble p k SC)

theorem mem_iterDouble {p : ℕ} {SC : DyadicInterval × DyadicInterval} {y : ℝ}
    (h : Mem p SC.1 (Real.sin y) ∧ Mem p SC.2 (Real.cos y)) :
    ∀ k : ℕ, Mem p (iterDouble p k SC).1 (Real.sin (2 ^ k * y)) ∧
      Mem p (iterDouble p k SC).2 (Real.cos (2 ^ k * y))
  | 0 => by simpa [iterDouble] using h
  | k + 1 => by
    rw [pow_succ, mul_comm (2 ^ k : ℝ) 2, mul_assoc]
    exact mem_doubleSC (mem_iterDouble h k)

/-- The number of halvings of `a` until it is at most `b` (with fuel). -/
def halvings : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, a, b => if a ≤ b then 0 else halvings n (a / 2) b + 1

/-- `(sin (c/2ᵖ), cos (c/2ᵖ))`: halve the argument `k` times to `|y| ≤ 1/2`, sum the series,
double back. -/
def sinCosPoint (p : ℕ) (c : ℤ) : DyadicInterval × DyadicInterval :=
  let k := halvings (p + 64) c.natAbs (2 ^ p / 2)
  iterDouble p k (sinCosSeries p ⟨fdiv c (scale k), cdiv c (scale k)⟩)

theorem mem_sinCosPoint (p : ℕ) (c : ℤ) :
    Mem p (sinCosPoint p c).1 (Real.sin ((c : ℝ) / 2 ^ p)) ∧
      Mem p (sinCosPoint p c).2 (Real.cos ((c : ℝ) / 2 ^ p)) := by
  unfold sinCosPoint
  set k := halvings (p + 64) c.natAbs (2 ^ p / 2)
  have hY : Mem p ⟨fdiv c (scale k), cdiv c (scale k)⟩ ((c : ℝ) / 2 ^ (p + k)) :=
    ⟨fdiv_scale_le p c k, le_cdiv_scale p c k⟩
  have := mem_iterDouble (mem_sinCosSeries hY) k
  have e : (2 : ℝ) ^ k * ((c : ℝ) / 2 ^ (p + k)) = (c : ℝ) / 2 ^ p := by
    rw [pow_add]; field_simp
  rwa [e] at this

/-- `(sin x, cos x)` on an interval `X`, from the values at the midpoint `c`:
`sin (c + h) = sin c cos h + cos c sin h`, `cos (c + h) = cos c cos h - sin c sin h`,
`cos h ∈ [1 - r²/2, 1]`, `sin h ∈ [-r, r]`. -/
def sinCos (p : ℕ) (X : DyadicInterval) : DyadicInterval × DyadicInterval :=
  let c := (X.lo + X.hi) / 2
  let r := max (X.hi - c) (c - X.lo)
  let SC := sinCosPoint p c
  let R : DyadicInterval := ⟨-r, r⟩
  let CH : DyadicInterval := ⟨scale p - cdiv (r * r) (scale (p + 1)), scale p⟩
  (clampUnit p (add (mul p SC.1 CH) (mul p SC.2 R)),
    clampUnit p (sub (mul p SC.2 CH) (mul p SC.1 R)))

/-- `sin` of an interval. -/
def sin (p : ℕ) (X : DyadicInterval) : DyadicInterval := (sinCos p X).1

/-- `cos` of an interval. -/
def cos (p : ℕ) (X : DyadicInterval) : DyadicInterval := (sinCos p X).2

theorem mem_sinCos {p : ℕ} {X : DyadicInterval} {x : ℝ} (hx : Mem p X x) :
    Mem p (sinCos p X).1 (Real.sin x) ∧ Mem p (sinCos p X).2 (Real.cos x) := by
  unfold sinCos
  set c := (X.lo + X.hi) / 2
  set r := max (X.hi - c) (c - X.lo)
  have hp := two_pow_pos' p
  obtain ⟨hS, hC⟩ := mem_sinCosPoint p c
  set h := x - (c : ℝ) / 2 ^ p with hh
  have hxch : x = (c : ℝ) / 2 ^ p + h := by ring
  -- `|h| ≤ r / 2ᵖ`
  have habs : |h| ≤ (r : ℝ) / 2 ^ p := by
    obtain ⟨h1, h2⟩ := hx
    rw [abs_le]
    constructor
    · have : ((c - X.lo : ℤ) : ℝ) ≤ r := by exact_mod_cast le_max_right _ _
      push_cast at this
      have e : -((r : ℝ) / 2 ^ p) ≤ ((X.lo : ℝ) - c) / 2 ^ p := by
        rw [neg_div', div_le_div_iff_of_pos_right hp]; linarith
      calc -((r : ℝ) / 2 ^ p) ≤ ((X.lo : ℝ) - c) / 2 ^ p := e
        _ = (X.lo : ℝ) / 2 ^ p - (c : ℝ) / 2 ^ p := by ring
        _ ≤ h := by rw [hh]; linarith
    · have : ((X.hi - c : ℤ) : ℝ) ≤ r := by exact_mod_cast le_max_left _ _
      push_cast at this
      calc h ≤ (X.hi : ℝ) / 2 ^ p - (c : ℝ) / 2 ^ p := by rw [hh]; linarith
        _ = ((X.hi : ℝ) - c) / 2 ^ p := by ring
        _ ≤ (r : ℝ) / 2 ^ p := div_le_div_of_nonneg_right (by linarith) hp.le
  have hR : Mem p ⟨-r, r⟩ (Real.sin h) := by
    obtain ⟨h1, h2⟩ := abs_le.1 (Real.abs_sin_le_abs.trans habs)
    exact ⟨by simpa [neg_div] using h1, h2⟩
  have hCH : Mem p ⟨scale p - cdiv (r * r) (scale (p + 1)), scale p⟩ (Real.cos h) := by
    constructor
    · have h1 := Real.one_sub_sq_div_two_le_cos (x := h)
      have h2 : h ^ 2 ≤ ((r : ℝ) / 2 ^ p) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      have h3 := le_cdiv (n := r * r) (scale_pos (p + 1))
      rw [scale_cast] at h3
      have e : ((scale p - cdiv (r * r) (scale (p + 1)) : ℤ) : ℝ) / 2 ^ p =
          1 - ((cdiv (r * r) (scale (p + 1)) : ℤ) : ℝ) / 2 ^ p := by
        push_cast [scale_cast]; field_simp
      rw [e]
      have e2 : ((r : ℝ) / 2 ^ p) ^ 2 / 2 = ((r * r : ℤ) : ℝ) / 2 ^ (p + 1) / 2 ^ p := by
        push_cast; field_simp; ring
      have h4 : ((r * r : ℤ) : ℝ) / 2 ^ (p + 1) / 2 ^ p ≤
          ((cdiv (r * r) (scale (p + 1)) : ℤ) : ℝ) / 2 ^ p :=
        div_le_div_of_nonneg_right h3 hp.le
      nlinarith
    · simp only [scale_cast, div_self hp.ne']; exact Real.cos_le_one h
  constructor
  · refine mem_clampUnit ?_ (Real.abs_sin_le_one _)
    rw [hxch, Real.sin_add]
    exact mem_add (mem_mul hS hCH) (mem_mul hC hR)
  · refine mem_clampUnit ?_ (Real.abs_cos_le_one _)
    rw [hxch, Real.cos_add]
    exact mem_sub (mem_mul hC hCH) (mem_mul hS hR)

theorem mem_sin {p : ℕ} {X : DyadicInterval} {x : ℝ} (hx : Mem p X x) :
    Mem p (sin p X) (Real.sin x) := (mem_sinCos hx).1

theorem mem_cos {p : ℕ} {X : DyadicInterval} {x : ℝ} (hx : Mem p X x) :
    Mem p (cos p X) (Real.cos x) := (mem_sinCos hx).2

/-! ### `arctan` -/

/-- The recurrence of the arctangent terms: multiply by `y² (2i+1)/(2i+3)`. -/
def atanNext (p : ℕ) (Y2 : DyadicInterval) (i : ℕ) (T : DyadicInterval) : DyadicInterval :=
  divNat (smulNat (2 * i + 1) (mul p T Y2)) (2 * i + 3)

/-- `arctan` at the point `m / 2ᵖ`: the series if `|m / 2ᵖ| < 1`, else `[-2, 2]`. -/
def arctanPoint (p : ℕ) (m : ℤ) : DyadicInterval :=
  if (m.natAbs : ℤ) < scale p then
    seriesEnclosure (atanNext p (sq p (ofInt m))) (4 * p + 16) (ofInt m)
  else ⟨-2 * scale p, 2 * scale p⟩

theorem mem_arctanPoint (p : ℕ) (m : ℤ) :
    Mem p (arctanPoint p m) (Real.arctan ((m : ℝ) / 2 ^ p)) := by
  have hp := two_pow_pos' p
  unfold arctanPoint
  split_ifs with h
  · have hy : Mem p (ofInt m) ((m : ℝ) / 2 ^ p) := mem_ofInt p m
    have hy1 : |(m : ℝ) / 2 ^ p| < 1 := by
      rw [abs_div, abs_of_pos hp, div_lt_one hp]
      have : ((m.natAbs : ℤ) : ℝ) < ((scale p : ℤ) : ℝ) := by exact_mod_cast h
      simpa [scale_cast, Nat.cast_natAbs, Int.cast_abs] using this
    refine mem_seriesEnclosure (f := Real.atanTerm ((m : ℝ) / 2 ^ p)) (fun i T hT ↦ ?_)
      (Real.abs_arctan_sub_altSum_le hy1) _ (by rwa [Real.atanTerm_zero])
    rw [Real.atanTerm_succ]
    exact mem_divNat (by omega) (mem_smulNat _ (mem_mul hT (mem_sq hy)))
  · have h1 := Real.neg_pi_div_two_lt_arctan ((m : ℝ) / 2 ^ p)
    have h2 := Real.arctan_lt_pi_div_two ((m : ℝ) / 2 ^ p)
    have h3 := Real.pi_lt_four
    constructor
    · change ((-2 * scale p : ℤ) : ℝ) / 2 ^ p ≤ _
      push_cast [scale_cast]; rw [mul_div_assoc, div_self hp.ne']; linarith
    · change _ ≤ ((2 * scale p : ℤ) : ℝ) / 2 ^ p
      push_cast [scale_cast]; rw [mul_div_assoc, div_self hp.ne']; linarith

/-- `arctan` of an interval (`arctan` is increasing). -/
def arctan (p : ℕ) (X : DyadicInterval) : DyadicInterval :=
  ⟨(arctanPoint p X.lo).lo, (arctanPoint p X.hi).hi⟩

theorem mem_arctan {p : ℕ} {X : DyadicInterval} {x : ℝ} (hx : Mem p X x) :
    Mem p (arctan p X) (Real.arctan x) :=
  ⟨(mem_arctanPoint p X.lo).1.trans (Real.arctan_strictMono.monotone hx.1),
    (Real.arctan_strictMono.monotone hx.2).trans (mem_arctanPoint p X.hi).2⟩

end DyadicInterval
