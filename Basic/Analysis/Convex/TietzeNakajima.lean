module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.Monotone

/-!
# The Tietze–Nakajima theorem in the plane

A closed connected subset of the plane which is locally convex is convex. Used by the cell lemma
of Fejes Tóth's packing theorem (`Basic.Analysis.Convex.CellDecomposition.PinwheelHoles`).

## Proof

Write `φ(x, y) = q + x (a - q) + y (c - q)`.

* `tn_wedge_step`, `tn_wedge` (*wedge lemma*, uses only local convexity): if `[q, a] ⊆ S` and
  `[q, c] ⊆ S`, then `conv {q, a, q + τ (c - q)} ⊆ S` for some `τ > 0`. Let `s*` be the
  supremum of the `s ∈ [0, 1]` such that `conv {q, φ(s, 0), φ(0, τ)} ⊆ S` for some `τ > 0`.
  Local convexity at `p* = φ(s*, 0)` (radius `r`) applied to `φ(s, 0)`, `φ(s₁, 0)` and a point
  `u = φ((1 - λ) s, λ τ)` of the old triangle near `p*`, with `s ≤ s* ≤ s₁`, `s < s₁` near `s*`,
  gives `conv {q, φ(s₁, 0), φ(0, λ τ)} ⊆ conv {q, φ(s, 0), φ(0, τ)} ∪ conv {φ(s, 0), φ(s₁, 0), u}`
  inside `S`; hence `s* = 1` and the supremum is attained.
* `tn_triangle` (*triangle lemma*, uses closedness): if `[b, a] ∪ [b, c] ⊆ S` then
  `conv {a, b, c} ⊆ S`. The set of `t ∈ [0, 1]` with `conv {a, b, b + t (c - b)} ⊆ S` is closed;
  at its maximum `t* < 1` the wedge lemma at `q = b + t* (c - b)` would enlarge it.
* Main theorem: for `x ∈ S`, the set `A = {y | [x, y] ⊆ S}` is closed, and for `y ∈ A` and
  `S ∩ B(y, r)` convex, every `z ∈ S ∩ B(y, r)` lies in `A` (triangle lemma for `x, y, z`).
  The union of these balls is open, so connectedness of `S` gives `S ⊆ A`.
-/

@[expose] public section

open Set Metric

namespace PlaneConvex

/-- A convex combination of three points of a convex set lies in it. -/
private lemma tn_convex_three {C : Set (Fin 2 → ℝ)} (hC : Convex ℝ C) {p₁ p₂ p₃ : Fin 2 → ℝ}
    (h₁ : p₁ ∈ C) (h₂ : p₂ ∈ C) (h₃ : p₃ ∈ C) {w₁ w₂ w₃ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hw₃ : 0 ≤ w₃) (hw : w₁ + w₂ + w₃ = 1) : w₁ • p₁ + w₂ • p₂ + w₃ • p₃ ∈ C := by
  have := hC.sum_mem (t := Finset.univ) (w := ![w₁, w₂, w₃]) (z := ![p₁, p₂, p₃])
    (by intro i _; fin_cases i <;> simpa) (by simpa [Fin.sum_univ_three] using hw)
    (by intro i _; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_three] using this

/-- Distance between two points `q + x (a - q) + y (c - q)`. -/
private lemma tn_dist_le (q a c : Fin 2 → ℝ) (x y x' y' : ℝ) :
    dist (q + x • (a - q) + y • (c - q)) (q + x' • (a - q) + y' • (c - q)) ≤
      |x - x'| * ‖a - q‖ + |y - y'| * ‖c - q‖ := by
  rw [dist_eq_norm]
  have : q + x • (a - q) + y • (c - q) - (q + x' • (a - q) + y' • (c - q)) =
      (x - x') • (a - q) + (y - y') • (c - q) := by
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]

/-- One step of the wedge lemma: local convexity at `p* = q + s₀ (a - q)` pushes the wedge
`conv {q, q + s (a - q), q + τ (c - q)} ⊆ S` from `s` to `s₁`, for `s ≤ s₀ ≤ s₁` close to `s₀`. -/
private lemma tn_wedge_step {S : Set (Fin 2 → ℝ)} {q a c : Fin 2 → ℝ}
    (hA : ∀ s ∈ Icc (0 : ℝ) 1, q + s • (a - q) ∈ S)
    {s s₀ s₁ τ r : ℝ} (hs0 : 0 ≤ s) (hss₁ : s < s₁) (hs₁ : s₁ ≤ 1) (hss₀ : s ≤ s₀)
    (hs₀₁ : s₀ ≤ s₁) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hW : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≤ s → y ≤ τ → x * τ + y * s ≤ s * τ →
      q + x • (a - q) + y • (c - q) ∈ S)
    (hr : 0 < r) (hconv : Convex ℝ (S ∩ ball (q + s₀ • (a - q)) r))
    (hclose : (s₀ - s) * ‖a - q‖ < r / 2) (hclose₁ : (s₁ - s₀) * ‖a - q‖ < r / 2) :
    ∃ τ₁, 0 < τ₁ ∧ τ₁ ≤ 1 ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≤ s₁ → y ≤ τ₁ →
      x * τ₁ + y * s₁ ≤ s₁ * τ₁ → q + x • (a - q) + y • (c - q) ∈ S := by
  have hM : 0 ≤ ‖a - q‖ := norm_nonneg _
  have hN : 0 ≤ ‖c - q‖ := norm_nonneg _
  set l : ℝ := min 1 (r / (2 * (‖a - q‖ + ‖c - q‖ + 1))) with hl
  have hl0 : 0 < l := lt_min one_pos (div_pos hr (by positivity))
  have hl1 : l ≤ 1 := min_le_left _ _
  have hlr : l * (‖a - q‖ + ‖c - q‖) < r / 2 := by
    calc l * (‖a - q‖ + ‖c - q‖)
        ≤ r / (2 * (‖a - q‖ + ‖c - q‖ + 1)) * (‖a - q‖ + ‖c - q‖) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ < r / 2 := by
          rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  refine ⟨l * τ, mul_pos hl0 hτ0, by nlinarith, ?_⟩
  intro x y hx hy hxs hyτ hxy
  by_cases hin : x ≤ s ∧ x * τ + y * s ≤ s * τ
  · exact hW x y hx hy hin.1 (hyτ.trans (by nlinarith)) hin.2
  have hge : s * τ ≤ x * τ + y * s := by
    rcases not_and_or.1 hin with h | h
    · nlinarith [mul_nonneg hy hs0, not_le.1 h]
    · exact (not_le.1 h).le
  -- the ball around `p*` and three points of `S` in it
  have hcenter : q + s₀ • (a - q) = q + s₀ • (a - q) + (0 : ℝ) • (c - q) := by simp
  rw [hcenter] at hconv
  have hp : q + s • (a - q) + (0 : ℝ) • (c - q) ∈
      S ∩ ball (q + s₀ • (a - q) + (0 : ℝ) • (c - q)) r := by
    refine ⟨by simpa using hA s ⟨hs0, by linarith⟩, ?_⟩
    rw [mem_ball]
    refine (tn_dist_le q a c _ _ _ _).trans_lt ?_
    rw [sub_self, abs_zero, zero_mul, add_zero, abs_of_nonpos (by linarith), neg_sub]
    linarith
  have hp₁ : q + s₁ • (a - q) + (0 : ℝ) • (c - q) ∈
      S ∩ ball (q + s₀ • (a - q) + (0 : ℝ) • (c - q)) r := by
    refine ⟨by simpa using hA s₁ ⟨by linarith, hs₁⟩, ?_⟩
    rw [mem_ball]
    refine (tn_dist_le q a c _ _ _ _).trans_lt ?_
    rw [sub_self, abs_zero, zero_mul, add_zero, abs_of_nonneg (by linarith)]
    linarith
  have hu : q + ((1 - l) * s) • (a - q) + (l * τ) • (c - q) ∈
      S ∩ ball (q + s₀ • (a - q) + (0 : ℝ) • (c - q)) r := by
    refine ⟨hW _ _ (by nlinarith) (by positivity) (by nlinarith) (by nlinarith)
      (le_of_eq (by ring)), ?_⟩
    rw [mem_ball]
    refine (tn_dist_le q a c _ _ _ _).trans_lt ?_
    have h1 : |(1 - l) * s - s₀| ≤ (s₀ - s) + l := by
      rw [abs_le]; constructor <;> nlinarith
    have h2 : |l * τ - 0| ≤ l := by
      rw [sub_zero, abs_of_pos (mul_pos hl0 hτ0)]; nlinarith
    calc |(1 - l) * s - s₀| * ‖a - q‖ + |l * τ - 0| * ‖c - q‖
        ≤ ((s₀ - s) + l) * ‖a - q‖ + l * ‖c - q‖ :=
          add_le_add (mul_le_mul_of_nonneg_right h1 hM) (mul_le_mul_of_nonneg_right h2 hN)
      _ < r := by nlinarith
  -- barycentric weights
  have hD : 0 < l * τ * (s₁ - s) := by
    have := sub_pos.2 hss₁
    positivity
  have hnum : 0 ≤ l * τ * (s₁ - s) - l * (x * τ - s * τ + y * s) - y * (s₁ - s) := by
    nlinarith [mul_nonneg (mul_nonneg hy hs0) (sub_nonneg.2 hl1)]
  have hw₁ := div_nonneg hnum hD.le
  have hw₂ : 0 ≤ l * (x * τ - s * τ + y * s) / (l * τ * (s₁ - s)) :=
    div_nonneg (mul_nonneg hl0.le (by linarith)) hD.le
  have hw₃ : 0 ≤ y * (s₁ - s) / (l * τ * (s₁ - s)) :=
    div_nonneg (mul_nonneg hy (by linarith)) hD.le
  have hsum : (l * τ * (s₁ - s) - l * (x * τ - s * τ + y * s) - y * (s₁ - s)) /
      (l * τ * (s₁ - s)) + l * (x * τ - s * τ + y * s) / (l * τ * (s₁ - s)) +
      y * (s₁ - s) / (l * τ * (s₁ - s)) = 1 := by
    rw [← add_div, ← add_div, div_eq_one_iff_eq hD.ne']
    ring
  have hmem := tn_convex_three hconv hp hp₁ hu hw₁ hw₂ hw₃ hsum
  convert hmem.1 using 1
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **Wedge lemma.** If `[q, a] ⊆ S` and `[q, c] ⊆ S` for a locally convex `S`, then the triangle
`conv {q, a, q + τ (c - q)}` lies in `S` for some `τ ∈ (0, 1]`. -/
private lemma tn_wedge {S : Set (Fin 2 → ℝ)}
    (hloc : ∀ p ∈ S, ∃ r > 0, Convex ℝ (S ∩ Metric.ball p r)) {q a c : Fin 2 → ℝ}
    (hA : ∀ s ∈ Icc (0 : ℝ) 1, q + s • (a - q) ∈ S)
    (hC : ∀ y ∈ Icc (0 : ℝ) 1, q + y • (c - q) ∈ S) :
    ∃ τ, 0 < τ ∧ τ ≤ 1 ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≤ 1 → y ≤ τ →
      x * τ + y * 1 ≤ 1 * τ → q + x • (a - q) + y • (c - q) ∈ S := by
  set Q : Set ℝ := {s | 0 ≤ s ∧ s ≤ 1 ∧ ∃ τ, 0 < τ ∧ τ ≤ 1 ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
    x ≤ s → y ≤ τ → x * τ + y * s ≤ s * τ → q + x • (a - q) + y • (c - q) ∈ S} with hQ
  suffices h1 : (1 : ℝ) ∈ Q from h1.2.2
  by_contra h1
  have h0 : (0 : ℝ) ∈ Q := by
    refine ⟨le_rfl, zero_le_one, 1, one_pos, le_rfl, ?_⟩
    intro x y hx hy hx0 hy1 _
    obtain rfl : x = 0 := le_antisymm hx0 hx
    simpa using hC y ⟨hy, hy1⟩
  have hbdd : BddAbove Q := ⟨1, fun s hs => hs.2.1⟩
  have hne : Q.Nonempty := ⟨0, h0⟩
  have hs₀0 : 0 ≤ sSup Q := le_csSup hbdd h0
  have hs₀1 : sSup Q ≤ 1 := csSup_le hne fun s hs => hs.2.1
  obtain ⟨r, hr, hconv⟩ := hloc _ (hA (sSup Q) ⟨hs₀0, hs₀1⟩)
  have hM : 0 ≤ ‖a - q‖ := norm_nonneg _
  set ε : ℝ := r / (2 * (‖a - q‖ + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have hεM : ε * ‖a - q‖ < r / 2 := by
    rw [hε_def, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨s, hsQ, hs⟩ := exists_lt_of_lt_csSup hne (show sSup Q - ε < sSup Q by linarith)
  have hss₀ : s ≤ sSup Q := le_csSup hbdd hsQ
  have hs1' : s < 1 := lt_of_le_of_ne hsQ.2.1 (by rintro rfl; exact h1 hsQ)
  obtain ⟨hs0, -, τ, hτ0, hτ1, hW⟩ := hsQ
  have hss₁ : s < min 1 (sSup Q + ε) := lt_min hs1' (by linarith)
  have hs₀₁ : sSup Q ≤ min 1 (sSup Q + ε) := le_min hs₀1 (by linarith)
  have hclose : (sSup Q - s) * ‖a - q‖ < r / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith) hM) hεM
  have hclose₁ : (min 1 (sSup Q + ε) - sSup Q) * ‖a - q‖ < r / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith [min_le_right 1 (sSup Q + ε)]) hM)
      hεM
  obtain ⟨τ₁, hτ₁0, hτ₁1, hW₁⟩ := tn_wedge_step hA hs0 hss₁ (min_le_left _ _) hss₀ hs₀₁ hτ0 hτ1
    hW hr hconv hclose hclose₁
  have hs₁Q : min 1 (sSup Q + ε) ∈ Q :=
    ⟨by linarith, min_le_left _ _, τ₁, hτ₁0, hτ₁1, hW₁⟩
  have hle := le_csSup hbdd hs₁Q
  by_cases hcase : sSup Q + ε ≤ 1
  · rw [min_eq_right hcase] at hle
    linarith
  · rw [min_eq_left (le_of_not_ge hcase)] at hs₁Q
    exact h1 hs₁Q

/-- **Triangle lemma.** If `[b, a] ∪ [b, c] ⊆ S` for a closed locally convex `S`, then the
triangle `conv {a, b, c}` lies in `S`. -/
private lemma tn_triangle {S : Set (Fin 2 → ℝ)} (hS : IsClosed S)
    (hloc : ∀ p ∈ S, ∃ r > 0, Convex ℝ (S ∩ Metric.ball p r)) {a b c : Fin 2 → ℝ}
    (hab : ∀ x ∈ Icc (0 : ℝ) 1, b + x • (a - b) ∈ S)
    (hbc : ∀ y ∈ Icc (0 : ℝ) 1, b + y • (c - b) ∈ S) :
    ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x + y ≤ 1 → b + x • (a - b) + y • (c - b) ∈ S := by
  set I : Set ℝ := Icc 0 1 ∩ {t | ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x + y ≤ 1 →
    b + x • (a - b) + (y * t) • (c - b) ∈ S} with hI
  have hIc : IsClosed I := by
    refine isClosed_Icc.inter ?_
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact hS.preimage (by fun_prop)
  have h0 : (0 : ℝ) ∈ I :=
    ⟨⟨le_rfl, zero_le_one⟩, fun x y hx hy hxy => by simpa using hab x ⟨hx, by linarith⟩⟩
  have hbdd : BddAbove I := ⟨1, fun t ht => ht.1.2⟩
  have hmem : sSup I ∈ I := hIc.csSup_mem ⟨0, h0⟩ hbdd
  suffices h1 : sSup I = 1 by
    intro x y hx hy hxy
    have := hmem.2 x y hx hy hxy
    rwa [h1, mul_one] at this
  by_contra hne1
  have ht₀1 : sSup I < 1 := lt_of_le_of_ne hmem.1.2 hne1
  have ht₀0 : 0 ≤ sSup I := hmem.1.1
  set t₀ := sSup I with ht₀
  have hA : ∀ s ∈ Icc (0 : ℝ) 1, (b + t₀ • (c - b)) + s • (a - (b + t₀ • (c - b))) ∈ S := by
    intro s hs
    have := hmem.2 s (1 - s) hs.1 (by linarith [hs.2]) (by linarith)
    convert this using 1
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hC : ∀ y ∈ Icc (0 : ℝ) 1, (b + t₀ • (c - b)) + y • (c - (b + t₀ • (c - b))) ∈ S := by
    intro y hy
    have := hbc (t₀ + y * (1 - t₀)) ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩
    convert this using 1
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  obtain ⟨τ, hτ0, hτ1, hW⟩ := tn_wedge hloc hA hC
  have ht₁0 : 0 ≤ t₀ + τ * (1 - t₀) := by nlinarith
  have ht₁I : t₀ + τ * (1 - t₀) ∈ I := by
    refine ⟨⟨ht₁0, by nlinarith⟩, fun x y hx hy hxy => ?_⟩
    by_cases hcase : y * (t₀ + τ * (1 - t₀)) ≤ t₀ * (1 - x)
    · rcases eq_or_lt_of_le ht₀0 with h | h
      · have hy0 : y * (t₀ + τ * (1 - t₀)) = 0 :=
          le_antisymm (hcase.trans_eq (by rw [← h, zero_mul])) (mul_nonneg hy ht₁0)
        have := hmem.2 x 0 hx le_rfl (by linarith)
        rw [hy0]
        simpa using this
      · have hle : y * (t₀ + τ * (1 - t₀)) / t₀ ≤ 1 - x := by
          rw [div_le_iff₀ h]; linarith
        have := hmem.2 x (y * (t₀ + τ * (1 - t₀)) / t₀) hx (by positivity) (by linarith)
        convert this using 3
        field_simp
    · rw [not_le] at hcase
      have hpos : 0 < 1 - t₀ := by linarith
      have hy' : (y * (t₀ + τ * (1 - t₀)) - t₀ * (1 - x)) / (1 - t₀) ≤ τ - x * τ := by
        rw [div_le_iff₀ hpos]
        nlinarith [mul_le_mul_of_nonneg_right (show y ≤ 1 - x by linarith) ht₁0]
      have := hW x ((y * (t₀ + τ * (1 - t₀)) - t₀ * (1 - x)) / (1 - t₀)) hx
        (div_nonneg (by linarith) hpos.le) (by linarith) (by nlinarith) (by linarith)
      convert this using 1
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  have := le_csSup hbdd ht₁I
  nlinarith [mul_pos hτ0 (sub_pos.2 ht₀1)]

/-- **The Tietze–Nakajima theorem in the plane.** A closed connected set which is locally convex
(every point `p` of `S` has a ball `B(p, r)` with `S ∩ B(p, r)` convex) is convex.

Argument (Tietze 1928, Nakajima 1928; see F. A. Valentine, *Convex Sets*, Thm 4.4).
(1) *Wedge lemma* (`tn_wedge`): if `[q, a] ∪ [q, c] ⊆ S` then `conv {q, a, q + τ (c - q)} ⊆ S`
for some `τ > 0`; the apex side `[q, q + s (a - q)]` of such a wedge is pushed from `s` to `1`
by local convexity at the point `q + s* (a - q)`, `s*` the supremum of the admissible `s`.
(2) *Triangle lemma* (`tn_triangle`): if `[p₁, p₀] ∪ [p₁, p₂] ⊆ S` then
`conv {p₀, p₁, p₂} ⊆ S`. The set of `t ∈ [0, 1]` with `conv {p₀, p₁, p₁ + t (p₂ - p₁)} ⊆ S` is
closed; at its maximum `t* < 1` the wedge lemma at `q* = p₁ + t* (p₂ - p₁)` would enlarge it.
(3) For `x ∈ S`, the set of `y` with `[x, y] ⊆ S` is closed, and by (2) it contains
`S ∩ B(y, r)` whenever it contains `y` and `S ∩ B(y, r)` is convex; as `S` is connected it
contains `S`. (This replaces the polygonal paths of the classical proof.) -/
theorem pin_convex_of_isClosed_of_isConnected {S : Set (Fin 2 → ℝ)} (hS : IsClosed S)
    (hconn : IsConnected S) (hloc : ∀ p ∈ S, ∃ r > 0, Convex ℝ (S ∩ Metric.ball p r)) :
    Convex ℝ S := by
  intro x hx
  set A : Set (Fin 2 → ℝ) := {y | ∀ θ ∈ Icc (0 : ℝ) 1, x + θ • (y - x) ∈ S} with hA
  have hAc : IsClosed A := by
    simp only [hA, Set.ofPred_forall]
    exact isClosed_iInter fun θ => isClosed_iInter fun _ => hS.preimage (by fun_prop)
  have key : ∀ y ∈ A, ∀ r : ℝ, Convex ℝ (S ∩ ball y r) → ∀ z ∈ S ∩ ball y r, z ∈ A := by
    intro y hyA r hconv z hz
    have hr : 0 < r := dist_nonneg.trans_lt hz.2
    have hy : y ∈ S ∩ ball y r := ⟨by simpa using hyA 1 ⟨zero_le_one, le_rfl⟩, mem_ball_self hr⟩
    have htri := tn_triangle hS hloc (a := x) (b := y) (c := z)
      (fun t ht => by
        have := hyA (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
        convert this using 1
        ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring)
      (fun t ht => by
        have := hconv hy hz (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1 (by ring)
        convert this.1 using 1
        ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring)
    intro θ hθ
    have := htri (1 - θ) θ (by linarith [hθ.2]) hθ.1 (by linarith)
    convert this using 1
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  set u : Set (Fin 2 → ℝ) :=
    {z | ∃ y ∈ A, ∃ r > 0, Convex ℝ (S ∩ ball y r) ∧ z ∈ ball y r} with hu_def
  have hu : IsOpen u := by
    rw [Metric.isOpen_iff]
    rintro z ⟨y, hyA, r, hr, hconv, hz⟩
    refine ⟨r - dist z y, sub_pos.2 hz, fun w hw => ⟨y, hyA, r, hr, hconv, ?_⟩⟩
    rw [mem_ball] at hw ⊢
    linarith [dist_triangle w z y]
  have hSu : S ⊆ u ∪ Aᶜ := by
    intro z hz
    by_cases hzA : z ∈ A
    · obtain ⟨r, hr, hconv⟩ := hloc z hz
      exact Or.inl ⟨z, hzA, r, hr, hconv, mem_ball_self hr⟩
    · exact Or.inr hzA
  have hSuA : ∀ z ∈ S, z ∈ u → z ∈ A := by
    rintro z hz ⟨y, hyA, r, -, hconv, hzb⟩
    exact key y hyA r hconv z ⟨hz, hzb⟩
  have hdisj : S ∩ (u ∩ Aᶜ) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and,
      not_not]
    exact hSuA z
  have hxA : x ∈ A := fun θ _ => by simpa using hx
  rcases isPreconnected_iff_subset_of_disjoint.1 hconn.isPreconnected u Aᶜ hu hAc.isOpen_compl
    hSu hdisj with h | h
  · intro z hz α β hα hβ hαβ
    have := hSuA z hz (h hz) β ⟨hβ, by linarith⟩
    obtain rfl : α = 1 - β := by linarith
    convert this using 1
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  · exact absurd hxA (h hx)

end PlaneConvex
