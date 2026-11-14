module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Rat.Floor
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Fixed-point dyadic interval arithmetic

Closed intervals `[lo / 2ᵖ, hi / 2ᵖ]` with integer endpoints `lo hi : ℤ` at a precision `p : ℕ`
fixed for a whole computation (fixed-point dyadic numbers). All operations are computable by
structural recursion on integers, so that the kernel can evaluate them (`decide +kernel`): the
kernel reduces `Nat` arithmetic on literals (`+`, `-`, `*`, `/`, `%`, `^`, comparisons) by GMP,
and `Int` arithmetic reduces to it. Rounding is outward: lower endpoints are rounded down and upper
endpoints up.

* `DyadicInterval.Mem p I x`: `x ∈ [I.lo / 2ᵖ, I.hi / 2ᵖ]`;
* exact operations: `add`, `neg`, `sub`, `smulNat`; rounded: `mul`, `sq`, `divNat`, `inv?`, `div?`
  (the last two return `none` when the divisor interval contains `0`), `sqrt` (by an integer
  square root checked by squaring), `ofRat`, `pi` (from `Real.pi_gt_d20`, `Real.pi_lt_d20`),
  `hull`, `clampUnit` (intersection with `[-1, 1]`);
* each operation has a soundness theorem `mem_op`: if `x ∈ I` and `y ∈ J` then
  `op x y ∈ op I J`.

Bool-valued tests (`hiLt`, `loGt`, `magLe`) decide inequalities for every point of an interval.
-/

@[expose] public section

/-- A closed interval with endpoints `lo / 2ᵖ` and `hi / 2ᵖ`; the precision `p` is a parameter of
the operations. An interval with `lo > hi` is empty. -/
structure DyadicInterval where
  /-- the lower endpoint, in units of `2⁻ᵖ` -/
  lo : ℤ
  /-- the upper endpoint, in units of `2⁻ᵖ` -/
  hi : ℤ
  deriving DecidableEq, Inhabited

namespace DyadicInterval

/-! ### Membership -/

/-- `x` lies in the interval `I` at precision `p`. -/
def Mem (p : ℕ) (I : DyadicInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) / 2 ^ p ≤ x ∧ x ≤ (I.hi : ℝ) / 2 ^ p

/-- The scale `2ᵖ` as an integer (computed by `Nat.pow`, which the kernel accelerates). -/
def scale (p : ℕ) : ℤ := ((2 ^ p : ℕ) : ℤ)

theorem scale_pos (p : ℕ) : 0 < scale p := by
  unfold scale; exact_mod_cast Nat.two_pow_pos p

theorem scale_cast (p : ℕ) : ((scale p : ℤ) : ℝ) = 2 ^ p := by
  simp [scale]

theorem two_pow_pos' (p : ℕ) : (0 : ℝ) < 2 ^ p := by positivity

/-- Floor division by a positive integer. -/
def fdiv (n d : ℤ) : ℤ := n / d

/-- Ceiling division by a positive integer. -/
def cdiv (n d : ℤ) : ℤ := -((-n) / d)

theorem fdiv_le {n d : ℤ} (hd : 0 < d) : ((fdiv n d : ℤ) : ℝ) ≤ (n : ℝ) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [le_div_iff₀ hd']
  exact_mod_cast Int.ediv_mul_le n hd.ne'

theorem le_cdiv {n d : ℤ} (hd : 0 < d) : (n : ℝ) / d ≤ ((cdiv n d : ℤ) : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h := fdiv_le (n := -n) hd
  simp only [fdiv, Int.cast_neg] at h
  simp only [cdiv, Int.cast_neg]
  rw [neg_div] at h
  linarith

/-- `fdiv` by the scale, as a real inequality at two precisions. -/
theorem fdiv_scale_le (p : ℕ) (n : ℤ) (q : ℕ) :
    ((fdiv n (scale q) : ℤ) : ℝ) / 2 ^ p ≤ (n : ℝ) / 2 ^ (p + q) := by
  have h := fdiv_le (n := n) (scale_pos q)
  rw [scale_cast] at h
  rw [pow_add, ← div_div]
  exact div_le_div_of_nonneg_right h (by positivity) |>.trans_eq (by ring)

theorem le_cdiv_scale (p : ℕ) (n : ℤ) (q : ℕ) :
    (n : ℝ) / 2 ^ (p + q) ≤ ((cdiv n (scale q) : ℤ) : ℝ) / 2 ^ p := by
  have h := le_cdiv (n := n) (scale_pos q)
  rw [scale_cast] at h
  rw [pow_add, ← div_div]
  exact (by ring : (n : ℝ) / 2 ^ q / 2 ^ p = (n : ℝ) / 2 ^ q / 2 ^ p).trans_le
    (div_le_div_of_nonneg_right h (by positivity)) |>.trans_eq' (by ring)

/-! ### Exact operations -/

/-- The point interval `[m / 2ᵖ, m / 2ᵖ]`. -/
def ofInt (m : ℤ) : DyadicInterval := ⟨m, m⟩

theorem mem_ofInt (p : ℕ) (m : ℤ) : Mem p (ofInt m) ((m : ℝ) / 2 ^ p) := ⟨le_rfl, le_rfl⟩

/-- Sum of intervals (exact). -/
def add (I J : DyadicInterval) : DyadicInterval := ⟨I.lo + J.lo, I.hi + J.hi⟩

theorem mem_add {p : ℕ} {I J : DyadicInterval} {x y : ℝ} (hx : Mem p I x) (hy : Mem p J y) :
    Mem p (add I J) (x + y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  constructor
  · simp only [add, Int.cast_add, add_div]; linarith
  · simp only [add, Int.cast_add, add_div]; linarith

/-- Negation of an interval (exact). -/
def neg (I : DyadicInterval) : DyadicInterval := ⟨-I.hi, -I.lo⟩

theorem mem_neg {p : ℕ} {I : DyadicInterval} {x : ℝ} (hx : Mem p I x) : Mem p (neg I) (-x) := by
  obtain ⟨h1, h2⟩ := hx
  constructor
  · simp only [neg, Int.cast_neg, neg_div]; linarith
  · simp only [neg, Int.cast_neg, neg_div]; linarith

/-- Difference of intervals (exact). -/
def sub (I J : DyadicInterval) : DyadicInterval := add I (neg J)

theorem mem_sub {p : ℕ} {I J : DyadicInterval} {x y : ℝ} (hx : Mem p I x) (hy : Mem p J y) :
    Mem p (sub I J) (x - y) := by
  rw [sub_eq_add_neg]; exact mem_add hx (mem_neg hy)

/-- Multiplication by a natural number (exact). -/
def smulNat (n : ℕ) (I : DyadicInterval) : DyadicInterval := ⟨n * I.lo, n * I.hi⟩

theorem mem_smulNat {p : ℕ} (n : ℕ) {I : DyadicInterval} {x : ℝ} (hx : Mem p I x) :
    Mem p (smulNat n I) (n * x) := by
  obtain ⟨h1, h2⟩ := hx
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · simp only [smulNat, Int.cast_mul, Int.cast_natCast, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h1 hn
  · simp only [smulNat, Int.cast_mul, Int.cast_natCast, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h2 hn

/-- The convex hull of two intervals. -/
def hull (I J : DyadicInterval) : DyadicInterval := ⟨min I.lo J.lo, max I.hi J.hi⟩

theorem mem_hull_left {p : ℕ} {I : DyadicInterval} (J : DyadicInterval) {x : ℝ}
    (hx : Mem p I x) : Mem p (hull I J) x := by
  obtain ⟨h1, h2⟩ := hx
  have hp := two_pow_pos' p
  constructor
  · refine le_trans ?_ h1
    simp only [hull, Int.cast_min]
    exact div_le_div_of_nonneg_right (min_le_left _ _) hp.le
  · refine h2.trans ?_
    simp only [hull, Int.cast_max]
    exact div_le_div_of_nonneg_right (le_max_left _ _) hp.le

theorem mem_hull_right {p : ℕ} (I : DyadicInterval) {J : DyadicInterval} {x : ℝ}
    (hx : Mem p J x) : Mem p (hull I J) x := by
  obtain ⟨h1, h2⟩ := hx
  have hp := two_pow_pos' p
  constructor
  · refine le_trans ?_ h1
    simp only [hull, Int.cast_min]
    exact div_le_div_of_nonneg_right (min_le_right _ _) hp.le
  · refine h2.trans ?_
    simp only [hull, Int.cast_max]
    exact div_le_div_of_nonneg_right (le_max_right _ _) hp.le

/-! ### Rounded operations -/

/-- Real products: `xy` lies between the least and the greatest of the four endpoint products. -/
theorem mul_mem_minmax {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  -- `u ↦ u v` is monotone or antitone, so `x y` lies between `a y` and `b y`, and `a y` between
  -- `a c` and `a d`
  have key : ∀ u v w s : ℝ, v ≤ s → v ≤ w → w ≤ s →
      min (u * v) (u * s) ≤ u * w ∧ u * w ≤ max (u * v) (u * s) := by
    intro u v w s _ h h'
    rcases le_total 0 u with hu | hu
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h hu),
        (mul_le_mul_of_nonneg_left h' hu).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h' hu),
        (mul_le_mul_of_nonpos_left h hu).trans (le_max_left _ _)⟩
  have hcd : c ≤ d := h3.trans h4
  have hab : a ≤ b := h1.trans h2
  obtain ⟨ha1, ha2⟩ := key a c y d hcd h3 h4
  obtain ⟨hb1, hb2⟩ := key b c y d hcd h3 h4
  obtain ⟨hy1, hy2⟩ := key y a x b hab h1 h2
  rw [mul_comm y a, mul_comm y b, mul_comm y x] at hy1 hy2
  constructor
  · refine le_trans ?_ hy1
    rcases min_choice (a * y) (b * y) with h | h <;> rw [h]
    · exact (min_le_left _ _).trans ha1
    · exact (min_le_right _ _).trans hb1
  · refine hy2.trans ?_
    rcases max_choice (a * y) (b * y) with h | h <;> rw [h]
    · exact ha2.trans (le_max_left _ _)
    · exact hb2.trans (le_max_right _ _)

/-- Product of intervals, rounded outward to precision `p`, by the signs of the endpoints
(Moore's nine cases; two endpoint products except when both intervals contain `0`). -/
def mul (p : ℕ) (I J : DyadicInterval) : DyadicInterval :=
  let s := scale p
  if 0 ≤ I.lo then
    if 0 ≤ J.lo then ⟨fdiv (I.lo * J.lo) s, cdiv (I.hi * J.hi) s⟩
    else if J.hi ≤ 0 then ⟨fdiv (I.hi * J.lo) s, cdiv (I.lo * J.hi) s⟩
    else ⟨fdiv (I.hi * J.lo) s, cdiv (I.hi * J.hi) s⟩
  else if I.hi ≤ 0 then
    if 0 ≤ J.lo then ⟨fdiv (I.lo * J.hi) s, cdiv (I.hi * J.lo) s⟩
    else if J.hi ≤ 0 then ⟨fdiv (I.hi * J.hi) s, cdiv (I.lo * J.lo) s⟩
    else ⟨fdiv (I.lo * J.hi) s, cdiv (I.lo * J.lo) s⟩
  else
    if 0 ≤ J.lo then ⟨fdiv (I.lo * J.hi) s, cdiv (I.hi * J.hi) s⟩
    else if J.hi ≤ 0 then ⟨fdiv (I.hi * J.lo) s, cdiv (I.lo * J.lo) s⟩
    else ⟨fdiv (min (I.lo * J.hi) (I.hi * J.lo)) s, cdiv (max (I.lo * J.lo) (I.hi * J.hi)) s⟩

/-- An interval `⟨⌊L/2ᵖ⌋, ⌈U/2ᵖ⌉⟩` of products at precision `2p` rounded to precision `p`. -/
theorem mem_of_prod_bounds {p : ℕ} {L U : ℤ} {z : ℝ} (hL : (L : ℝ) / 2 ^ (p + p) ≤ z)
    (hU : z ≤ (U : ℝ) / 2 ^ (p + p)) :
    Mem p ⟨fdiv L (scale p), cdiv U (scale p)⟩ z :=
  ⟨(fdiv_scale_le p L p).trans hL, hU.trans (le_cdiv_scale p U p)⟩

theorem mem_mul {p : ℕ} {I J : DyadicInterval} {x y : ℝ} (hx : Mem p I x) (hy : Mem p J y) :
    Mem p (mul p I J) (x * y) := by
  have hp := two_pow_pos' p
  have e : ∀ u v : ℤ, ((u * v : ℤ) : ℝ) / 2 ^ (p + p) = ((u : ℝ) / 2 ^ p) * ((v : ℝ) / 2 ^ p) := by
    intro u v; push_cast; rw [pow_add]; ring
  set a := (I.lo : ℝ) / 2 ^ p
  set b := (I.hi : ℝ) / 2 ^ p
  set c := (J.lo : ℝ) / 2 ^ p
  set d := (J.hi : ℝ) / 2 ^ p
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have sg : ∀ u : ℤ, (0 ≤ u ↔ 0 ≤ (u : ℝ) / 2 ^ p) ∧ (u ≤ 0 ↔ (u : ℝ) / 2 ^ p ≤ 0) := by
    intro u
    constructor
    · rw [le_div_iff₀ hp, zero_mul]; exact_mod_cast Iff.rfl
    · rw [div_le_iff₀ hp, zero_mul]; exact_mod_cast Iff.rfl
  unfold mul
  split_ifs
  all_goals try
    (refine mem_of_prod_bounds ?_ ?_ <;> rw [e] <;>
      simp only [(sg _).1, (sg _).2, not_le] at * <;> nlinarith)
  -- the case `0 ∈ I`, `0 ∈ J`
  simp only [(sg _).1, (sg _).2, not_le] at *
  refine mem_of_prod_bounds ?_ ?_
  · rw [Int.cast_min, ← min_div_div_right (two_pow_pos' (p + p)).le, e, e]
    rcases le_total 0 x with hx0 | hx0
    · exact (min_le_right _ _).trans (by nlinarith)
    · exact (min_le_left _ _).trans (by nlinarith)
  · rw [Int.cast_max, ← max_div_div_right (two_pow_pos' (p + p)).le, e, e]
    rcases le_total 0 x with hx0 | hx0
    · exact (by nlinarith : x * y ≤ b * d).trans (le_max_right _ _)
    · exact (by nlinarith : x * y ≤ a * c).trans (le_max_left _ _)

/-- The square of an interval, rounded outward; tighter than `mul p I I` when `0 ∈ I`. -/
def sq (p : ℕ) (I : DyadicInterval) : DyadicInterval :=
  if 0 ≤ I.lo then mul p I I
  else if I.hi ≤ 0 then mul p (neg I) (neg I)
  else ⟨0, cdiv (max (I.lo * I.lo) (I.hi * I.hi)) (scale p)⟩

theorem mem_sq {p : ℕ} {I : DyadicInterval} {x : ℝ} (hx : Mem p I x) :
    Mem p (sq p I) (x ^ 2) := by
  unfold sq
  split_ifs with h1 h2
  · rw [pow_two]; exact mem_mul hx hx
  · rw [pow_two, ← neg_mul_neg]; exact mem_mul (mem_neg hx) (mem_neg hx)
  · obtain ⟨hx1, hx2⟩ := hx
    have hp := two_pow_pos' p
    push Not at h1 h2
    refine ⟨by rw [Int.cast_zero, zero_div]; positivity, ?_⟩
    refine le_trans ?_ (le_cdiv_scale p _ p)
    rw [Int.cast_max, ← max_div_div_right (two_pow_pos' (p + p)).le]
    have e : ∀ u : ℤ, ((u * u : ℤ) : ℝ) / 2 ^ (p + p) = ((u : ℝ) / 2 ^ p) ^ 2 := by
      intro u; push_cast; rw [pow_add]; ring
    rw [e, e]
    rcases le_total 0 x with h | h
    · exact (pow_le_pow_left₀ h hx2 2).trans (le_max_right _ _)
    · have : (-x) ^ 2 ≤ (-((I.lo : ℝ) / 2 ^ p)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      rw [neg_sq, neg_sq] at this
      exact this.trans (le_max_left _ _)

/-- Division by a positive natural number, rounded outward. -/
def divNat (I : DyadicInterval) (n : ℕ) : DyadicInterval :=
  ⟨fdiv I.lo n, cdiv I.hi n⟩

theorem mem_divNat {p : ℕ} {I : DyadicInterval} {x : ℝ} {n : ℕ} (hn : 0 < n) (hx : Mem p I x) :
    Mem p (divNat I n) (x / n) := by
  obtain ⟨h1, h2⟩ := hx
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hp := two_pow_pos' p
  constructor
  · have := fdiv_le (n := I.lo) hn'
    simp only [Int.cast_natCast] at this
    calc ((fdiv I.lo n : ℤ) : ℝ) / 2 ^ p ≤ (I.lo : ℝ) / n / 2 ^ p :=
          div_le_div_of_nonneg_right this hp.le
      _ = (I.lo : ℝ) / 2 ^ p / n := by ring
      _ ≤ x / n := div_le_div_of_nonneg_right h1 hnr.le
  · have := le_cdiv (n := I.hi) hn'
    simp only [Int.cast_natCast] at this
    calc x / n ≤ (I.hi : ℝ) / 2 ^ p / n := div_le_div_of_nonneg_right h2 hnr.le
      _ = (I.hi : ℝ) / n / 2 ^ p := by ring
      _ ≤ ((cdiv I.hi n : ℤ) : ℝ) / 2 ^ p := div_le_div_of_nonneg_right this hp.le

/-- The reciprocal of an interval of positive numbers, rounded outward. -/
def invPos (p : ℕ) (I : DyadicInterval) : DyadicInterval :=
  ⟨fdiv (scale (p + p)) I.hi, cdiv (scale (p + p)) I.lo⟩

theorem mem_invPos {p : ℕ} {I : DyadicInterval} (hI : 0 < I.lo) {x : ℝ} (hx : Mem p I x) :
    Mem p (invPos p I) x⁻¹ := by
  obtain ⟨h1, h2⟩ := hx
  have hp := two_pow_pos' p
  have hlo : (0 : ℝ) < I.lo := by exact_mod_cast hI
  have hxpos : 0 < x := lt_of_lt_of_le (div_pos hlo hp) h1
  have hhi : (0 : ℝ) < I.hi := by
    have := h1.trans h2
    rw [div_le_div_iff_of_pos_right hp] at this
    linarith
  have hhi' : (0 : ℤ) < I.hi := by exact_mod_cast hhi
  have e : ∀ u : ℝ, 0 < u → ((scale (p + p) : ℤ) : ℝ) / u / 2 ^ p = (u / 2 ^ p)⁻¹ := by
    intro u hu; rw [scale_cast, pow_add]; field_simp
  constructor
  · calc ((fdiv (scale (p + p)) I.hi : ℤ) : ℝ) / 2 ^ p
          ≤ ((scale (p + p) : ℤ) : ℝ) / I.hi / 2 ^ p :=
            div_le_div_of_nonneg_right (fdiv_le hhi') hp.le
      _ = ((I.hi : ℝ) / 2 ^ p)⁻¹ := e _ hhi
      _ ≤ x⁻¹ := inv_anti₀ hxpos h2
  · calc x⁻¹ ≤ ((I.lo : ℝ) / 2 ^ p)⁻¹ := inv_anti₀ (div_pos hlo hp) h1
      _ = ((scale (p + p) : ℤ) : ℝ) / I.lo / 2 ^ p := (e _ hlo).symm
      _ ≤ ((cdiv (scale (p + p)) I.lo : ℤ) : ℝ) / 2 ^ p :=
            div_le_div_of_nonneg_right (le_cdiv hI) hp.le

/-- The reciprocal of an interval not containing `0`, rounded outward; `none` if `0 ∈ I`. -/
def inv? (p : ℕ) (I : DyadicInterval) : Option DyadicInterval :=
  if 0 < I.lo then some (invPos p I)
  else if I.hi < 0 then some (neg (invPos p (neg I)))
  else none

theorem mem_inv? {p : ℕ} {I K : DyadicInterval} (h : inv? p I = some K) {x : ℝ}
    (hx : Mem p I x) : Mem p K x⁻¹ := by
  unfold inv? at h
  split_ifs at h with h1 h2
  · cases h; exact mem_invPos h1 hx
  · cases h
    have := mem_neg (mem_invPos (I := neg I) (by simp [neg]; omega) (mem_neg hx))
    rwa [inv_neg, neg_neg] at this

/-- A point of an interval `I` with `inv? p I = some K` is nonzero. -/
theorem ne_zero_of_inv? {p : ℕ} {I K : DyadicInterval} (h : inv? p I = some K) {x : ℝ}
    (hx : Mem p I x) : x ≠ 0 := by
  unfold inv? at h
  have hp := two_pow_pos' p
  obtain ⟨h1, h2⟩ := hx
  split_ifs at h with ha hb
  · have : (0 : ℝ) < I.lo := by exact_mod_cast ha
    exact (lt_of_lt_of_le (div_pos this hp) h1).ne'
  · have : (I.hi : ℝ) < 0 := by exact_mod_cast hb
    exact (lt_of_le_of_lt h2 (div_neg_of_neg_of_pos this hp)).ne

/-- Quotient of intervals, rounded outward; `none` if the divisor interval contains `0`. -/
def div? (p : ℕ) (I J : DyadicInterval) : Option DyadicInterval :=
  (inv? p J).map (mul p I)

theorem mem_div? {p : ℕ} {I J K : DyadicInterval} (h : div? p I J = some K) {x y : ℝ}
    (hx : Mem p I x) (hy : Mem p J y) : Mem p K (x / y) := by
  unfold div? at h
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [div_eq_mul_inv]
  exact mem_mul hx (mem_inv? hL hy)

/-! ### Square roots -/

/-- Newton's iteration for the integer square root, with fuel. -/
def isqrtAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | fuel + 1, n, x =>
    let y := (x + n / x) / 2
    if y < x then isqrtAux fuel n y else x

/-- A candidate for `⌊√n⌋` (Newton's iteration from `n`); its correctness is not needed, since
`sqrtLo` and `sqrtHi` check it. -/
def isqrt (n : ℕ) : ℕ := if n ≤ 1 then n else isqrtAux 256 n n

/-- A natural number `s` with `s² ≤ n`. -/
def sqrtLo (n : ℕ) : ℕ := let s := isqrt n; if s * s ≤ n then s else 0

/-- A natural number `s` with `n ≤ s²`. -/
def sqrtHi (n : ℕ) : ℕ :=
  let s := isqrt n
  if n ≤ s * s then s else if n ≤ (s + 1) * (s + 1) then s + 1 else n

theorem sqrtLo_sq_le (n : ℕ) : sqrtLo n * sqrtLo n ≤ n := by
  unfold sqrtLo; dsimp only; split_ifs with h <;> simp_all

theorem le_sqrtHi_sq (n : ℕ) : n ≤ sqrtHi n * sqrtHi n := by
  unfold sqrtHi
  dsimp only
  split_ifs with h h'
  · exact h
  · exact h'
  · exact Nat.le_mul_self n

/-- `√` of an interval, rounded outward (`Real.sqrt` is monotone and vanishes on `(-∞, 0]`). -/
def sqrt (p : ℕ) (I : DyadicInterval) : DyadicInterval :=
  ⟨sqrtLo ((max I.lo 0).toNat * 2 ^ p), sqrtHi ((max I.hi 0).toNat * 2 ^ p)⟩

theorem mem_sqrt {p : ℕ} {I : DyadicInterval} {x : ℝ} (hx : Mem p I x) :
    Mem p (sqrt p I) (Real.sqrt x) := by
  obtain ⟨h1, h2⟩ := hx
  have hp := two_pow_pos' p
  -- `√(m 2ᵖ) / 2ᵖ = √(m / 2ᵖ)` for `m ≥ 0`
  have e : ∀ m : ℤ, Real.sqrt (((max m 0).toNat * 2 ^ p : ℕ) : ℝ) / 2 ^ p =
      Real.sqrt (((max m 0 : ℤ) : ℝ) / 2 ^ p) := by
    intro m
    have hm : ((max m 0).toNat : ℝ) = ((max m 0 : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (le_max_right m 0)
    push_cast
    rw [hm, Real.sqrt_div' _ hp.le, Real.sqrt_mul' _ hp.le]
    have h2p : Real.sqrt (2 ^ p) * Real.sqrt (2 ^ p) = 2 ^ p := Real.mul_self_sqrt hp.le
    have hs : 0 < Real.sqrt ((2 : ℝ) ^ p) := Real.sqrt_pos.2 hp
    rw [div_eq_div_iff hp.ne' hs.ne', mul_assoc, h2p]
    push_cast
    ring
  constructor
  · -- lower endpoint
    set n := (max I.lo 0).toNat * 2 ^ p
    have hs : (sqrtLo n : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      exact_mod_cast (pow_two (sqrtLo n)).symm ▸ sqrtLo_sq_le n
    calc ((sqrtLo n : ℤ) : ℝ) / 2 ^ p ≤ Real.sqrt (n : ℝ) / 2 ^ p := by
          push_cast; exact div_le_div_of_nonneg_right hs hp.le
      _ = Real.sqrt (((max I.lo 0 : ℤ) : ℝ) / 2 ^ p) := e I.lo
      _ ≤ Real.sqrt x := by
          rcases le_total I.lo 0 with h | h
          · rw [max_eq_right h]
            simp
          · rw [max_eq_left h]; exact Real.sqrt_le_sqrt h1
  · -- upper endpoint
    set n := (max I.hi 0).toNat * 2 ^ p
    have hs : Real.sqrt (n : ℝ) ≤ (sqrtHi n : ℝ) := by
      rw [Real.sqrt_le_left (by positivity)]
      exact_mod_cast (pow_two (sqrtHi n)).symm ▸ le_sqrtHi_sq n
    calc Real.sqrt x ≤ Real.sqrt (((max I.hi 0 : ℤ) : ℝ) / 2 ^ p) := by
          apply Real.sqrt_le_sqrt
          refine h2.trans ?_
          exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) hp.le
      _ = Real.sqrt (n : ℝ) / 2 ^ p := (e I.hi).symm
      _ ≤ ((sqrtHi n : ℤ) : ℝ) / 2 ^ p := by
          push_cast; exact div_le_div_of_nonneg_right hs hp.le

/-! ### Constants -/

/-- The interval `[⌊q 2ᵖ⌋ / 2ᵖ, ⌈q 2ᵖ⌉ / 2ᵖ]` around a rational number `q`. -/
def ofRat (p : ℕ) (q : ℚ) : DyadicInterval := ⟨⌊q * 2 ^ p⌋, ⌈q * 2 ^ p⌉⟩

theorem mem_ofRat (p : ℕ) (q : ℚ) : Mem p (ofRat p q) (q : ℝ) := by
  have hp := two_pow_pos' p
  have h1 := Int.floor_le (q * 2 ^ p)
  have h2 := Int.le_ceil (q * 2 ^ p)
  have h1' : ((⌊q * 2 ^ p⌋ : ℤ) : ℝ) ≤ (q : ℝ) * 2 ^ p := by exact_mod_cast h1
  have h2' : (q : ℝ) * 2 ^ p ≤ ((⌈q * 2 ^ p⌉ : ℤ) : ℝ) := by exact_mod_cast h2
  constructor
  · change ((⌊q * 2 ^ p⌋ : ℤ) : ℝ) / 2 ^ p ≤ q
    rw [div_le_iff₀ hp]; exact h1'
  · change (q : ℝ) ≤ ((⌈q * 2 ^ p⌉ : ℤ) : ℝ) / 2 ^ p
    rw [le_div_iff₀ hp]; exact h2'

/-- A rational lower bound for `π` (`Real.pi_gt_d20`). -/
def piLo : ℚ := 314159265358979323846 / 100000000000000000000

/-- A rational upper bound for `π` (`Real.pi_lt_d20`). -/
def piHi : ℚ := 314159265358979323847 / 100000000000000000000

theorem piLo_lt_pi : (piLo : ℝ) < Real.pi := by
  have h := Real.pi_gt_d20
  have e : (piLo : ℝ) = 3.14159265358979323846 := by unfold piLo; push_cast; norm_num
  rw [e]; exact h

theorem pi_lt_piHi : Real.pi < (piHi : ℝ) := by
  have h := Real.pi_lt_d20
  have e : (piHi : ℝ) = 3.14159265358979323847 := by unfold piHi; push_cast; norm_num
  rw [e]; exact h

/-- An enclosure of `π` (Mathlib's twenty-digit bounds `Real.pi_gt_d20`, `Real.pi_lt_d20`). -/
def pi (p : ℕ) : DyadicInterval := ⟨(ofRat p piLo).lo, (ofRat p piHi).hi⟩

theorem mem_pi (p : ℕ) : Mem p (pi p) Real.pi :=
  ⟨(mem_ofRat p piLo).1.trans piLo_lt_pi.le, pi_lt_piHi.le.trans (mem_ofRat p piHi).2⟩

/-- The intersection with `[-1, 1]` (sound for quantities known to lie in `[-1, 1]`). -/
def clampUnit (p : ℕ) (I : DyadicInterval) : DyadicInterval :=
  ⟨max I.lo (-scale p), min I.hi (scale p)⟩

theorem mem_clampUnit {p : ℕ} {I : DyadicInterval} {x : ℝ} (hx : Mem p I x) (h : |x| ≤ 1) :
    Mem p (clampUnit p I) x := by
  obtain ⟨h1, h2⟩ := hx
  have hp := two_pow_pos' p
  obtain ⟨h3, h4⟩ := abs_le.1 h
  rw [div_le_iff₀ hp] at h1
  rw [le_div_iff₀ hp] at h2
  constructor
  · simp only [clampUnit, Int.cast_max, Int.cast_neg, scale_cast]
    rw [div_le_iff₀ hp]
    exact max_le h1 (by nlinarith)
  · simp only [clampUnit, Int.cast_min, scale_cast]
    rw [le_div_iff₀ hp]
    exact le_min h2 (by nlinarith)

/-! ### Tests -/

/-- Every point of `I` is negative (`I.hi < 0`). -/
def hiNeg (I : DyadicInterval) : Bool := decide (I.hi < 0)

/-- Every point of `I` is positive (`0 < I.lo`). -/
def loPos (I : DyadicInterval) : Bool := decide (0 < I.lo)

theorem neg_of_hiNeg {p : ℕ} {I : DyadicInterval} (h : hiNeg I = true) {x : ℝ}
    (hx : Mem p I x) : x < 0 := by
  have h' : (I.hi : ℝ) < 0 := by exact_mod_cast of_decide_eq_true h
  exact lt_of_le_of_lt hx.2 (div_neg_of_neg_of_pos h' (two_pow_pos' p))

theorem pos_of_loPos {p : ℕ} {I : DyadicInterval} (h : loPos I = true) {x : ℝ}
    (hx : Mem p I x) : 0 < x := by
  have h' : (0 : ℝ) < I.lo := by exact_mod_cast of_decide_eq_true h
  exact lt_of_lt_of_le (div_pos h' (two_pow_pos' p)) hx.1

/-- Every point of `I` is at most the rational `q`. -/
def hiLe (p : ℕ) (I : DyadicInterval) (q : ℚ) : Bool := decide ((I.hi : ℚ) ≤ q * 2 ^ p)

/-- Every point of `I` is at least the rational `q`. -/
def loGe (p : ℕ) (I : DyadicInterval) (q : ℚ) : Bool := decide (q * 2 ^ p ≤ (I.lo : ℚ))

theorem le_of_hiLe {p : ℕ} {I : DyadicInterval} {q : ℚ} (h : hiLe p I q = true) {x : ℝ}
    (hx : Mem p I x) : x ≤ q := by
  have h' : (I.hi : ℝ) ≤ q * 2 ^ p := by exact_mod_cast of_decide_eq_true h
  refine hx.2.trans ?_
  rw [div_le_iff₀ (two_pow_pos' p)]
  exact h'

theorem ge_of_loGe {p : ℕ} {I : DyadicInterval} {q : ℚ} (h : loGe p I q = true) {x : ℝ}
    (hx : Mem p I x) : (q : ℝ) ≤ x := by
  have h' : (q : ℝ) * 2 ^ p ≤ I.lo := by exact_mod_cast of_decide_eq_true h
  refine le_trans ?_ hx.1
  rw [le_div_iff₀ (two_pow_pos' p)]
  exact h'

/-- The magnitude `max |lo| |hi|` of the interval, in units of `2⁻ᵖ`. -/
def mag (I : DyadicInterval) : ℕ := max I.lo.natAbs I.hi.natAbs

theorem abs_le_mag {p : ℕ} {I : DyadicInterval} {x : ℝ} (hx : Mem p I x) :
    |x| ≤ (I.mag : ℝ) / 2 ^ p := by
  obtain ⟨h1, h2⟩ := hx
  have hp := two_pow_pos' p
  have hlo : -((I.mag : ℝ)) ≤ I.lo := by
    have : (I.lo.natAbs : ℝ) ≤ I.mag := by exact_mod_cast le_max_left _ _
    have h' : |(I.lo : ℝ)| = I.lo.natAbs := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    linarith [neg_abs_le (I.lo : ℝ)]
  have hhi : (I.hi : ℝ) ≤ I.mag := by
    have : (I.hi.natAbs : ℝ) ≤ I.mag := by exact_mod_cast le_max_right _ _
    have h' : |(I.hi : ℝ)| = I.hi.natAbs := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    linarith [le_abs_self (I.hi : ℝ)]
  rw [abs_le]
  constructor
  · have := (div_le_iff₀ hp).1 h1
    rw [neg_div', div_le_iff₀ hp]
    linarith
  · exact h2.trans (div_le_div_of_nonneg_right hhi hp.le)

/-- Every point of `I` has absolute value at most the rational `q`. -/
def magLe (p : ℕ) (I : DyadicInterval) (q : ℚ) : Bool := decide (((I.mag : ℤ) : ℚ) ≤ q * 2 ^ p)

theorem abs_le_of_magLe {p : ℕ} {I : DyadicInterval} {q : ℚ} (h : magLe p I q = true) {x : ℝ}
    (hx : Mem p I x) : |x| ≤ q := by
  have h' : ((I.mag : ℤ) : ℝ) ≤ q * 2 ^ p := by exact_mod_cast of_decide_eq_true h
  refine (abs_le_mag hx).trans ?_
  rw [div_le_iff₀ (two_pow_pos' p)]
  exact_mod_cast h'

end DyadicInterval
