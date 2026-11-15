module

public import SmoothedPolygons.Ch16.Certificates.DOutMapsToCheck
public import SmoothedPolygons.Ch16.Certificates.ContractionBox
public import SmoothedPolygons.Ch16.BasinHypotheses

/-!
# `F(𝒟₀₀) ⊆ 𝒟₀₀`: a kernel-checked interval certificate

The first conjunct of `DOutContracts` (`SmoothedPolygons/Ch16/BasinHypotheses.lean`):
`MapsTo poincareAngZero (boxSet 0 0) (boxSet 0 0)` (`mapsTo_boxSet_zero_zero`), for the box
`𝒟₀₀ = {r₂ ∈ [0, 1], ψ ∈ [0, π/3], θ₂ ∈ [π - 1.1, π]}` of cell coordinates, faces included.

## The structure of the map on `𝒟₀₀` (exact, no numerics)

With `ζ z₁ = x₁ + i y₁ = r₁ e^{iφ₁}`, `ζ z₂ = x₂ + i y₂ = r₂ e^{iφ₂}` (`φ₁ = θ₁ + 2π/3`,
`φ₂ = θ₂ + 2π/3`) and `κ = r₁ r₂ sin ψ`, the switching cubic of the controls `ζ → 1` along the
control `ζ` is `D(t) = V₂(t) = -√3 κ + y₂ t + y₁ t²/2 + t³/12` (`ham_one_sub_ham_ζ`); on `𝒟₀₀`,
`y₂ ≤ 0 ≤ κ` (`cellBox_facts`), so `D(t)/t²` is strictly increasing on `t > 0` (`V₂_mul_sq_lt`):
`D` has at most one positive root `τ`, with `D < 0` before it and `D > 0` after it. The cubic of
`ζ → ζ²` is `-√3 Im z₃(t)`, and `Im z₃(t) = r₂ sin θ₂ t + r₁ sin θ₁ t²/2 + t³/12 > 0`.
* Off the face piece `{r₂ = 0, θ₁ ≤ π/3}`, `D` is negative somewhere on `t > 0`
  (`exists_V₂_neg`), so the root `τ` exists, `ζ` is the first control (it is optimal on
  `[0, τ]`) and `τ` is the first switching time, by the definitions themselves
  (`firstControl_firstSwitchTime`; the tie points such as `(-1, 0, 0)` need no separate
  treatment).
* At `τ`, the rotated image `w = ζ F(z)` has `w₃ = U₂ + i V₂` with `V₂ = D(τ) = 0` and
  `U₂ = -(2/√3) Im z₃(τ) < 0` (`flow_two_im_eq`): it lies on the wall `𝒲₀` with `x₃ < 0`, so its
  class is the class of its cell coordinates (`cellClass_cellCoords`), which lie in
  `(0, 1) × (0, π) × (-π, π]`. Moreover `V₁ = Im w₂ = D'(τ) > 0` (`V₁_pos_of_root`): the image
  lies in the first big open cell; the cell is decided by the switching cubics, not by a metric
  margin (the "structural fact" of `notes/briefs/l5_numerics_report.md`).
* Only two inequalities are left for the numerics: `ψ' < π/3`, which follows from
  `C₁ = U₀ (V₁ - √3 U₁) - V₀ (U₁ + √3 V₁) < 0` (`toIcoMod_lt_pi_div_three`), and
  `θ₂' > 2π/3 ≥ π - 1.1`, which follows from `C₂ = V₁ + √3 U₁ < 0`
  (`two_pi_div_three_lt_arg`); `U₀ + i V₀ = w₁`, `U₁ + i V₁ = w₂` are polynomial in `τ`. Their
  numerical margins are large (`ψ' ≤ 0.194`, `θ₂' ≥ 2.733`).
* On the face piece `{r₂ = 0, θ₁ ≤ π/3}` the first control is `1`; the class of
  `(e^{iθ₁}, 0, 0)` is that of its rotation `(e^{i(θ₁ + 2π/3)}, 0, 0)`, the cell point
  `(0, 0, θ₁ + 2π/3)` of `𝒟₀₀` off the face piece (`cellClass_face`, the `V_T`-equivariance).

## The certificate

The numerical part is checked on the rational coordinates `(r₂, a, b)`, `a = tan (ψ/2)`,
`b = tan ((π - θ₂)/2)` (`trigR_tan_half`, `coeffsR_cell`), which map `𝒟₀₀` into
`[0, 1] × [0, 37/64] × [0, 5/8]` (`mem_root_of_cellBox`; `tan (π/6) = 1/√3 ≤ 37/64`,
`tan (0.55) ≤ 5/8` by `Real.sin_bound`, `Real.cos_bound`): every coefficient is a rational
function of `(r₂, a, b)`, so no `sin`, `cos` or `arctan` enclosure is evaluated. The tree of
`SmoothedPolygons/Ch16/Certificates/DOutMapsToData.lean` (248 boxes) gives on each box a bracket
`[tl, th]` of `τ` (`D(th) > 0`, and `D(tl) < 0` unless `tl = 0`) and `C₁, C₂ < 0` on
`box × [tl, th]` (`Good`, `checkTree_sound`). Near the segment `{r₂ = 0, θ₁ = π/3}`, where
`τ → 0` and the image tends to the corner `(0, 0, π)` (raw margin `0`), the conditions are
checked in the form divided by `τ`, with `r₂/τ² = (τ/12 + y₁/2)/(√3 r₁ sin ψ - sin φ₂ τ)` from
`D(τ) = 0` (`mode = true`); there they have margin `√3`.

`#print axioms mapsTo_boxSet_zero_zero`: `propext`, `Classical.choice`, `Quot.sound`.
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.DOutMaps

open DyadicInterval Set ContractionBox
open Complex (I)

/-! ### The real formulas of the check -/

/-- `(cos (2 arctan a), sin (2 arctan a))` as rational functions of `a`. -/
noncomputable def trigR (a : ℝ) : ℝ × ℝ := (2 * (1 + a ^ 2)⁻¹ - 1, 2 * (a * (1 + a ^ 2)⁻¹))

/-- The real coefficients (the fields of `Coeffs`). -/
structure CoeffsR where
  /-- `r₁` -/
  r1 : ℝ
  /-- `sin ψ` -/
  sa : ℝ
  /-- `cos φ₂` -/
  c2 : ℝ
  /-- `sin φ₂` -/
  s2 : ℝ
  /-- `x₁` -/
  x1 : ℝ
  /-- `y₁` -/
  y1 : ℝ
  /-- `x₂` -/
  x2 : ℝ
  /-- `y₂` -/
  y2 : ℝ
  /-- `κ` -/
  k : ℝ

/-- The coefficients at `(r₂, a, b)` (the real version of `coeffsI`). -/
noncomputable def coeffsR (r a b : ℝ) : CoeffsR :=
  let ca := (trigR a).1
  let sa := (trigR a).2
  let cb := (trigR b).1
  let sb := (trigR b).2
  let cg := cb * ca - sb * sa
  let sg := sb * ca + cb * sa
  let r1 := 1 - r
  let c1 := (cg - √3 * sg) / 2
  let s1 := -((√3 * cg + sg) / 2)
  let c2 := (cb - √3 * sb) / 2
  let s2 := -((√3 * cb + sb) / 2)
  ⟨r1, sa, c2, s2, r1 * c1, r1 * s1, r * c2, r * s2, r1 * r * sa⟩

/-- The switching cubic `D(t) = t (y₂ + t (y₁/2 + t/12)) - √3 κ`. -/
noncomputable def dR (c : CoeffsR) (t : ℝ) : ℝ := t * (c.y2 + t * (c.y1 / 2 + t / 12)) - √3 * c.k

/-- `U₀ = x₁ - √3 t/2`. -/
noncomputable def u0R (c : CoeffsR) (t : ℝ) : ℝ := c.x1 - √3 * t / 2

/-- `V₀ = y₁ + t/2`. -/
noncomputable def v0R (c : CoeffsR) (t : ℝ) : ℝ := c.y1 + t / 2

/-- The denominator `√3 r₁ sin ψ - sin φ₂ t` of `r₂ / t²` at a root of `D`. -/
noncomputable def denR (c : CoeffsR) (t : ℝ) : ℝ := √3 * c.r1 * c.sa - c.s2 * t

/-- `u₁`: `U₁` (`mode = false`) or `U₁ / t` through `D(t) = 0` (`mode = true`). -/
noncomputable def u1R (c : CoeffsR) (t : ℝ) (mode : Bool) : ℝ :=
  if mode then t * ((t / 12 + c.y1 / 2) / denR c t) * c.c2 + (c.x1 - √3 * t / 4)
  else c.x2 + t * (c.x1 - √3 * t / 4)

/-- `v₁`: `V₁` (`mode = false`) or `V₁ / t` through `D(t) = 0` (`mode = true`). -/
noncomputable def v1R (c : CoeffsR) (t : ℝ) (mode : Bool) : ℝ :=
  if mode then t * ((t / 12 + c.y1 / 2) / denR c t) * c.s2 + (c.y1 + t / 4)
  else c.y2 + t * (c.y1 + t / 4)

/-- The condition of the check at the time `t`. -/
def CondR (c : CoeffsR) (t : ℝ) (mode : Bool) : Prop :=
  (mode = true → denR c t ≠ 0) ∧ v1R c t mode + √3 * u1R c t mode < 0 ∧
    u0R c t * (v1R c t mode - √3 * u1R c t mode) -
      v0R c t * (u1R c t mode + √3 * v1R c t mode) < 0

/-- What a certificate leaf gives at a point `(r₂, a, b)` of its box. -/
def Good (r a b : ℝ) : Prop :=
  ∃ tl th : ℝ, 0 ≤ tl ∧ tl ≤ th ∧ 0 < dR (coeffsR r a b) th ∧
    (tl = 0 ∨ dR (coeffsR r a b) tl < 0) ∧
    ∀ t ∈ Icc tl th, ∃ mode, CondR (coeffsR r a b) t mode

/-! ### Soundness of the interval check -/

theorem mem_s3I : Mem prec s3I (√3) := by
  constructor
  · rw [Real.le_sqrt (by norm_num [s3I]) (by norm_num)]
    norm_num [s3I]
  · rw [show ((s3I.hi : ℤ) : ℝ) / 2 ^ prec = √((((s3I.hi : ℤ) : ℝ) / 2 ^ prec) ^ 2) from
      (Real.sqrt_sq (by norm_num [s3I])).symm]
    exact Real.sqrt_le_sqrt (by norm_num [s3I])

theorem mem_trigI {A : DyadicInterval} {a : ℝ} (ha : Mem prec A a)
    (hA : nz (add (one prec) (sq prec A)) = true) :
    Mem prec (trigI A).1 (trigR a).1 ∧ Mem prec (trigI A).2 (trigR a).2 := by
  have hi := mem_invT hA (mem_add (mem_one prec) (mem_sq ha))
  constructor
  · have := mem_sub (mem_smulNat 2 hi) (mem_one prec)
    exact_mod_cast this
  · have := mem_smulNat 2 (mem_mul ha hi)
    exact_mod_cast this

/-- Enclosure of the real coefficients by the interval ones. -/
def Coeffs.Encl (C : Coeffs) (c : CoeffsR) : Prop :=
  Mem prec C.r1 c.r1 ∧ Mem prec C.sa c.sa ∧ Mem prec C.c2 c.c2 ∧ Mem prec C.s2 c.s2 ∧
    Mem prec C.x1 c.x1 ∧ Mem prec C.y1 c.y1 ∧ Mem prec C.x2 c.x2 ∧ Mem prec C.y2 c.y2 ∧
    Mem prec C.k c.k

theorem mem_div2 {X : DyadicInterval} {x : ℝ} (h : Mem prec X x) :
    Mem prec (divNat X 2) (x / 2) := by
  have := mem_divNat (n := 2) (by norm_num) h
  exact_mod_cast this

theorem mem_divN {X : DyadicInterval} {x : ℝ} (n : ℕ) (hn : 0 < n) (h : Mem prec X x) :
    Mem prec (divNat X n) (x / n) := mem_divNat hn h

theorem mem_coeffsI {R A B : DyadicInterval} {r a b : ℝ} (hr : Mem prec R r) (ha : Mem prec A a)
    (hb : Mem prec B b) (hA : nz (add (one prec) (sq prec A)) = true)
    (hB : nz (add (one prec) (sq prec B)) = true) : (coeffsI R A B).Encl (coeffsR r a b) := by
  obtain ⟨hca, hsa⟩ := mem_trigI ha hA
  obtain ⟨hcb, hsb⟩ := mem_trigI hb hB
  have hcg := mem_sub (mem_mul hcb hca) (mem_mul hsb hsa)
  have hsg := mem_add (mem_mul hsb hca) (mem_mul hcb hsa)
  have hr1 := mem_sub (mem_one prec) hr
  have hc1 := mem_div2 (mem_sub hcg (mem_mul mem_s3I hsg))
  have hs1 := mem_neg (mem_div2 (mem_add (mem_mul mem_s3I hcg) hsg))
  have hc2 := mem_div2 (mem_sub hcb (mem_mul mem_s3I hsb))
  have hs2 := mem_neg (mem_div2 (mem_add (mem_mul mem_s3I hcb) hsb))
  exact ⟨hr1, hsa, hc2, hs2, mem_mul hr1 hc1, mem_mul hr1 hs1, mem_mul hr hc2, mem_mul hr hs2,
    mem_mul (mem_mul hr1 hr) hsa⟩

theorem mem_dI {C : Coeffs} {c : CoeffsR} (hC : C.Encl c) {T : DyadicInterval} {t : ℝ}
    (ht : Mem prec T t) : Mem prec (dI C T) (dR c t) := by
  obtain ⟨-, -, -, -, -, hy1, -, hy2, hk⟩ := hC
  have h12 : Mem prec (divNat T 12) (t / 12) := by
    have := mem_divN 12 (by norm_num) ht
    exact_mod_cast this
  exact mem_sub (mem_mul ht (mem_add hy2 (mem_mul ht (mem_add (mem_div2 hy1) h12))))
    (mem_mul mem_s3I hk)

theorem condI_sound {C : Coeffs} {c : CoeffsR} (hC : C.Encl c) {T : DyadicInterval} {t : ℝ}
    (ht : Mem prec T t) {mode : Bool} (h : condI C T mode = true) : CondR c t mode := by
  obtain ⟨hr1, hsa, hc2, hs2, hx1, hy1, hx2, hy2, -⟩ := hC
  have h4 : ∀ {X : DyadicInterval} {x : ℝ}, Mem prec X x → Mem prec (divNat X 4) (x / 4) := by
    intro X x hX
    have := mem_divN 4 (by norm_num) hX
    exact_mod_cast this
  have h12 : Mem prec (divNat T 12) (t / 12) := by
    have := mem_divN 12 (by norm_num) ht
    exact_mod_cast this
  have hU0 : Mem prec (sub C.x1 (divNat (mul prec s3I T) 2)) (u0R c t) :=
    mem_sub hx1 (by have := mem_div2 (mem_mul mem_s3I ht); simpa [mul_div_assoc] using this)
  have hV0 : Mem prec (add C.y1 (divNat T 2)) (v0R c t) := mem_add hy1 (mem_div2 ht)
  have hx14 : Mem prec (sub C.x1 (divNat (mul prec s3I T) 4)) (c.x1 - √3 * t / 4) :=
    mem_sub hx1 (h4 (mem_mul mem_s3I ht))
  have hy14 : Mem prec (add C.y1 (divNat T 4)) (c.y1 + t / 4) := mem_add hy1 (h4 ht)
  have hden : Mem prec (sub (mul prec (mul prec s3I C.r1) C.sa) (mul prec C.s2 T)) (denR c t) :=
    mem_sub (mem_mul (mem_mul mem_s3I hr1) hsa) (mem_mul hs2 ht)
  unfold condI at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hm, h2⟩, h1⟩ := h
  -- the enclosures of `u₁`, `v₁`
  have huv : ∃ U V : DyadicInterval, Mem prec U (u1R c t mode) ∧ Mem prec V (v1R c t mode) ∧
      hiNeg (add V (mul prec s3I U)) = true ∧
      hiNeg (sub (mul prec (sub C.x1 (divNat (mul prec s3I T) 2))
        (sub V (mul prec s3I U))) (mul prec (add C.y1 (divNat T 2)) (add U (mul prec s3I V)))) =
        true := by
    cases mode with
    | false =>
      exact ⟨_, _, mem_add hx2 (mem_mul ht hx14), mem_add hy2 (mem_mul ht hy14), h2, h1⟩
    | true =>
      have hnz : nz (sub (mul prec (mul prec s3I C.r1) C.sa) (mul prec C.s2 T)) = true := by
        simpa using hm
      have hTR := mem_mul ht (mem_divT hnz (mem_add h12 (mem_div2 hy1)) hden)
      exact ⟨_, _, mem_add (mem_mul hTR hc2) hx14, mem_add (mem_mul hTR hs2) hy14, h2, h1⟩
  obtain ⟨U, V, hU, hV, hc2', hc1'⟩ := huv
  refine ⟨fun hmode ↦ ?_, neg_of_hiNeg hc2' (mem_add hV (mem_mul mem_s3I hU)),
    neg_of_hiNeg hc1' (mem_sub (mem_mul hU0 (mem_sub hV (mem_mul mem_s3I hU)))
      (mem_mul hV0 (mem_add hU (mem_mul mem_s3I hV))))⟩
  subst hmode
  exact ne_zero_of_nz (by simpa using hm) hden

theorem mem_mk {lo hi : ℤ} {t : ℝ} (h1 : (lo : ℝ) / 2 ^ prec ≤ t) (h2 : t ≤ (hi : ℝ) / 2 ^ prec) :
    Mem prec ⟨lo, hi⟩ t := ⟨h1, h2⟩

theorem piecesOK_sound {C : Coeffs} {c : CoeffsR} (hC : C.Encl c) {mode : Bool} :
    ∀ (d : ℕ) (tl th : ℤ), piecesOK C mode d tl th = true →
      ∀ t ∈ Icc ((tl : ℝ) / 2 ^ prec) ((th : ℝ) / 2 ^ prec), CondR c t mode
  | 0, tl, th, h, t, ht => condI_sound hC (mem_mk ht.1 ht.2) h
  | d + 1, tl, th, h, t, ht => by
    simp only [piecesOK, Bool.and_eq_true] at h
    rcases le_total t ((((tl + th) / 2 : ℤ) : ℝ) / 2 ^ prec) with h' | h'
    · exact piecesOK_sound hC d _ _ h.1 t ⟨ht.1, h'⟩
    · exact piecesOK_sound hC d _ _ h.2 t ⟨h', ht.2⟩

theorem leafOK_sound {X : Box3} {tl th : ℤ} {mode : Bool} {d : ℕ}
    (h : leafOK X tl th mode d = true) {r a b : ℝ} (hr : Mem prec X.r r) (ha : Mem prec X.a a)
    (hb : Mem prec X.b b) : Good r a b := by
  unfold leafOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hA, hB⟩, htl0⟩, htlth⟩, hpos⟩, hneg⟩, hpc⟩ := h
  have hC := mem_coeffsI hr ha hb hA hB
  refine ⟨(tl : ℝ) / 2 ^ prec, (th : ℝ) / 2 ^ prec, by positivity,
    div_le_div_of_nonneg_right (by exact_mod_cast htlth) (by positivity),
    pos_of_loPos hpos (mem_dI hC (mem_mk le_rfl le_rfl)), ?_,
    fun t ht ↦ ⟨mode, piecesOK_sound hC d tl th hpc t ht⟩⟩
  rcases hneg with h0 | h0
  · left; simp [h0]
  · right; exact neg_of_hiNeg h0 (mem_dI hC (mem_mk le_rfl le_rfl))

/-- The membership of a point in a box. -/
def Box3.Mem (X : Box3) (r a b : ℝ) : Prop :=
  DyadicInterval.Mem prec X.r r ∧ DyadicInterval.Mem prec X.a a ∧ DyadicInterval.Mem prec X.b b

theorem mem_halves {I : DyadicInterval} {x : ℝ} (h : DyadicInterval.Mem prec I x) :
    DyadicInterval.Mem prec (lowerHalf I) x ∨ DyadicInterval.Mem prec (upperHalf I) x := by
  rcases le_total x ((((I.lo + I.hi) / 2 : ℤ) : ℝ) / 2 ^ prec) with h' | h'
  · exact Or.inl ⟨h.1, h'⟩
  · exact Or.inr ⟨h', h.2⟩

theorem Box3.mem_lower_or_upper {X : Box3} {r a b : ℝ} (h : X.Mem r a b) (k : ℕ) :
    (X.lower k).Mem r a b ∨ (X.upper k).Mem r a b := by
  obtain ⟨hr, ha, hb⟩ := h
  rcases k with _ | _ | k
  · rcases mem_halves hr with h | h
    · exact Or.inl ⟨h, ha, hb⟩
    · exact Or.inr ⟨h, ha, hb⟩
  · rcases mem_halves ha with h | h
    · exact Or.inl ⟨hr, h, hb⟩
    · exact Or.inr ⟨hr, h, hb⟩
  · rcases mem_halves hb with h | h
    · exact Or.inl ⟨hr, ha, h⟩
    · exact Or.inr ⟨hr, ha, h⟩

theorem checkTree_sound : ∀ (T : Tree) (X : Box3), checkTree X T = true →
    ∀ r a b, X.Mem r a b → Good r a b
  | .leaf tl th mode d, X, h, r, a, b, hm => leafOK_sound h hm.1 hm.2.1 hm.2.2
  | .node k l u, X, h, r, a, b, hm => by
    simp only [checkTree, Bool.and_eq_true] at h
    rcases X.mem_lower_or_upper hm k with h' | h'
    · exact checkTree_sound l _ h.1 r a b h'
    · exact checkTree_sound u _ h.2 r a b h'

/-- **The certificate tree passes the check** (the kernel checks of `DOutMapsToCheck.lean`). -/
theorem checkTree_root : checkTree root tree = true := by
  simp only [tree, checkTree, check_0l_2l_1l, check_0l_2l_1u, check_0l_2u_1l, check_0l_2u_1u,
    check_0u_2l_1l, check_0u_2l_1u, check_0u_2u_1l, check_0u_2u_1u, Bool.and_self]

/-- Every point of the root box `[0, 1] × [0, 37/64] × [0, 5/8]` is good. -/
theorem good_of_mem_root {r a b : ℝ} (hr : r ∈ Icc 0 1) (ha : a ∈ Icc 0 (37 / 64))
    (hb : b ∈ Icc 0 (5 / 8)) : Good r a b := by
  refine checkTree_sound tree root checkTree_root r a b ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals norm_num [root]
  exacts [hr.1, hr.2, ha.1, by linarith [ha.2], hb.1, by linarith [hb.2]]

/-! ### The coordinates `a = tan (ψ/2)`, `b = tan ((π - θ₂)/2)` -/

/-- The half-angle substitution: `cos x = 2/(1 + a²) - 1`, `sin x = 2a/(1 + a²)` for
`a = tan (x/2)`. -/
theorem trigR_tan_half {x : ℝ} (hx : 0 < Real.cos (x / 2)) :
    (trigR (Real.tan (x / 2))).1 = Real.cos x ∧ (trigR (Real.tan (x / 2))).2 = Real.sin x := by
  have hc := hx.ne'
  have h1 : 1 + Real.tan (x / 2) ^ 2 = (Real.cos (x / 2) ^ 2)⁻¹ := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    linarith [Real.sin_sq_add_cos_sq (x / 2)]
  have e1 : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have e2 : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  simp only [trigR, h1, inv_inv]
  refine ⟨e1.symm, ?_⟩
  rw [e2, Real.tan_eq_sin_div_cos]
  field_simp

/-- The coefficients of the check at `(r₂, tan (ψ/2), tan ((π - θ₂)/2))` are those of the cell
point `p = (r₂, ψ, θ₂)`. -/
theorem coeffsR_cell {p : Fin 3 → ℝ} (h1 : 0 < Real.cos (p 1 / 2))
    (h2 : 0 < Real.cos ((Real.pi - p 2) / 2)) :
    (coeffsR (p 0) (Real.tan (p 1 / 2)) (Real.tan ((Real.pi - p 2) / 2))).r1 = 1 - p 0 ∧
    (coeffsR (p 0) (Real.tan (p 1 / 2)) (Real.tan ((Real.pi - p 2) / 2))).sa = Real.sin (p 1) ∧
    (coeffsR (p 0) (Real.tan (p 1 / 2)) (Real.tan ((Real.pi - p 2) / 2))).c2 =
      Real.cos (p 2 + 2 / 3 * Real.pi) ∧
    (coeffsR (p 0) (Real.tan (p 1 / 2)) (Real.tan ((Real.pi - p 2) / 2))).s2 =
      Real.sin (p 2 + 2 / 3 * Real.pi) ∧
    (coeffsR (p 0) (Real.tan (p 1 / 2)) (Real.tan ((Real.pi - p 2) / 2))).x1 = cx₁ p ∧
    (coeffsR (p 0) (Real.tan (p 1 / 2)) (Real.tan ((Real.pi - p 2) / 2))).y1 = cy₁ p ∧
    (coeffsR (p 0) (Real.tan (p 1 / 2)) (Real.tan ((Real.pi - p 2) / 2))).x2 = cx₂ p ∧
    (coeffsR (p 0) (Real.tan (p 1 / 2)) (Real.tan ((Real.pi - p 2) / 2))).y2 = cy₂ p ∧
    (coeffsR (p 0) (Real.tan (p 1 / 2)) (Real.tan ((Real.pi - p 2) / 2))).k = cκ p := by
  obtain ⟨ea, fa⟩ := trigR_tan_half h1
  obtain ⟨eb, fb⟩ := trigR_tan_half h2
  rw [Real.cos_pi_sub] at eb
  rw [Real.sin_pi_sub] at fb
  have k1 : Real.cos (p 2 - p 1 + 2 / 3 * Real.pi) =
      Real.cos (p 2 - p 1) * (-1 / 2) - Real.sin (p 2 - p 1) * (√3 / 2) := by
    rw [Real.cos_add, cos_two_thirds_pi, sin_two_thirds_pi]
  have k2 : Real.sin (p 2 - p 1 + 2 / 3 * Real.pi) =
      Real.sin (p 2 - p 1) * (-1 / 2) + Real.cos (p 2 - p 1) * (√3 / 2) := by
    rw [Real.sin_add, cos_two_thirds_pi, sin_two_thirds_pi]
  have k3 : Real.cos (p 2 + 2 / 3 * Real.pi) =
      Real.cos (p 2) * (-1 / 2) - Real.sin (p 2) * (√3 / 2) := by
    rw [Real.cos_add, cos_two_thirds_pi, sin_two_thirds_pi]
  have k4 : Real.sin (p 2 + 2 / 3 * Real.pi) =
      Real.sin (p 2) * (-1 / 2) + Real.cos (p 2) * (√3 / 2) := by
    rw [Real.sin_add, cos_two_thirds_pi, sin_two_thirds_pi]
  simp only [coeffsR, ea, fa, eb, fb, cx₁, cy₁, cx₂, cy₂, cκ, k1, k2, k3, k4, Real.cos_sub,
    Real.sin_sub]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | ring

/-! ### The switching cubic on `𝒟₀₀` -/

section Cubic

variable {p : Fin 3 → ℝ}

/-- `D(t)/t²` is strictly increasing when `y₂ ≤ 0 ≤ κ` (one sign change of the coefficients). -/
theorem V₂_mul_sq_lt (hy : cy₂ p ≤ 0) (hk : 0 ≤ cκ p) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    V₂ p s * t ^ 2 < V₂ p t * s ^ 2 := by
  have e : V₂ p t * s ^ 2 - V₂ p s * t ^ 2 =
      (t - s) * (√3 * cκ p * (t + s) - cy₂ p * s * t + s ^ 2 * t ^ 2 / 12) := by
    unfold V₂; ring
  have h3 : 0 ≤ √3 := Real.sqrt_nonneg 3
  have ht : 0 < t := hs.trans hst
  have : 0 < (t - s) * (√3 * cκ p * (t + s) - cy₂ p * s * t + s ^ 2 * t ^ 2 / 12) := by
    apply mul_pos (by linarith)
    have : 0 ≤ √3 * cκ p * (t + s) := by positivity
    have : 0 ≤ -cy₂ p * s * t := by
      have := mul_pos hs ht
      nlinarith
    have : 0 < s ^ 2 * t ^ 2 / 12 := by positivity
    linarith
  linarith

theorem V₂_pos_of_nonneg (hy : cy₂ p ≤ 0) (hk : 0 ≤ cκ p) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (h : 0 ≤ V₂ p s) : 0 < V₂ p t := by
  have := V₂_mul_sq_lt hy hk hs hst
  have h2 : 0 ≤ V₂ p s * t ^ 2 := mul_nonneg h (sq_nonneg t)
  have hs2 : 0 < s ^ 2 := by positivity
  by_contra hc
  push Not at hc
  nlinarith

theorem V₂_neg_of_nonpos (hy : cy₂ p ≤ 0) (hk : 0 ≤ cκ p) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (h : V₂ p t ≤ 0) : V₂ p s < 0 := by
  by_contra hc
  push Not at hc
  linarith [V₂_pos_of_nonneg hy hk hs hst hc]

/-- At a positive root of `D`, `V₁ = Im ζ z₂ = D'` is positive:
`τ V₁(τ) = τ³/12 - y₂ τ + 2√3 κ`. -/
theorem V₁_pos_of_root (hy : cy₂ p ≤ 0) (hk : 0 ≤ cκ p) {τ : ℝ} (hτ : 0 < τ)
    (h0 : V₂ p τ = 0) : 0 < V₁ p τ := by
  have e : τ * V₁ p τ = τ ^ 3 / 12 - cy₂ p * τ + 2 * (√3 * cκ p) + 2 * V₂ p τ := by
    unfold V₁ V₂; ring
  rw [h0, mul_zero, add_zero] at e
  have : 0 ≤ √3 * cκ p := mul_nonneg (Real.sqrt_nonneg 3) hk
  have : 0 < τ ^ 3 / 12 := by positivity
  have : 0 ≤ -cy₂ p * τ := mul_nonneg (by linarith) hτ.le
  have : 0 < τ * V₁ p τ := by linarith
  exact pos_of_mul_pos_right this hτ.le

/-- `Im z₃(t) = -(√3/2) U₂ - V₂/2` (`ζ z₃ = U₂ + i V₂`, `z₃ = ζ² (ζ z₃)`). -/
theorem flow_two_im_eq (t : ℝ) :
    (flow t (cellPoint p) ζ 2).im = -(√3 / 2) * U₂ p t - V₂ p t / 2 := by
  obtain ⟨-, -, -, -, e1, e2⟩ := zeta_flow p t
  have e : flow t (cellPoint p) ζ 2 = ζ ^ 2 * (ζ * flow t (cellPoint p) ζ 2) := by
    rw [← mul_assoc, ← pow_succ, ζ_pow_three, one_mul]
  rw [e, Complex.mul_im, e1, e2, ζ_sq_re, ζ_sq_im]
  ring

end Cubic

/-! ### The angles of the image -/

/-- `arg w ≥ 2π/3` when `Im w > 0` and `Im w + √3 Re w < 0`. -/
theorem two_pi_div_three_lt_arg {w : ℂ} (h1 : 0 < w.im) (h2 : w.im + √3 * w.re < 0) :
    2 * Real.pi / 3 < Complex.arg w := by
  have h3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hre : w.re < 0 := by nlinarith
  rw [arg_eq_arctan_add_pi hre h1.le]
  have hq : -√3 < w.im / w.re := by
    rw [lt_div_iff_of_neg hre]; linarith
  have harc : Real.arctan (√3) = Real.pi / 3 := by
    rw [← Real.tan_pi_div_three, Real.arctan_tan (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])]
  have := Real.arctan_strictMono hq
  rw [Real.arctan_neg, harc] at this
  linarith

/-- `ψ' < π/3` for the angle `ψ' ∈ (0, π)` from `w₀` to `w₁` when
`(Re w₀ Im w₁ - Im w₀ Re w₁) - √3 (Re w₀ Re w₁ + Im w₀ Im w₁) < 0`. -/
theorem toIcoMod_lt_pi_div_three {w₀ w₁ : ℂ}
    (hψ : toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) ∈ Ioo 0 Real.pi)
    (h : w₀.re * (w₁.im - √3 * w₁.re) - w₀.im * (w₁.re + √3 * w₁.im) < 0) :
    toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) < Real.pi / 3 := by
  set ψ := toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) with hψdef
  have hw₀ : w₀ ≠ 0 := by
    rintro rfl; simp at h
  have hw₁ : w₁ ≠ 0 := by
    rintro rfl; simp at h
  have e : ψ = Complex.arg w₁ - Complex.arg w₀ -
      (toIcoDiv Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) : ℝ) * (2 * Real.pi) := by
    rw [hψdef, ← zsmul_eq_mul]
    exact eq_sub_of_add_eq (toIcoMod_add_toIcoDiv_zsmul _ _ _)
  have hs : Real.sin ψ = Real.sin (Complex.arg w₁ - Complex.arg w₀) := by
    rw [e, Real.sin_sub_int_mul_two_pi]
  have hc : Real.cos ψ = Real.cos (Complex.arg w₁ - Complex.arg w₀) := by
    rw [e, Real.cos_sub_int_mul_two_pi]
  have n0 : 0 < ‖w₀‖ := norm_pos_iff.2 hw₀
  have n1 : 0 < ‖w₁‖ := norm_pos_iff.2 hw₁
  have key : Real.sin ψ - √3 * Real.cos ψ < 0 := by
    rw [hs, hc, Real.sin_sub, Real.cos_sub, Complex.sin_arg, Complex.sin_arg,
      Complex.cos_arg hw₀, Complex.cos_arg hw₁]
    have e2 : w₁.im / ‖w₁‖ * (w₀.re / ‖w₀‖) - w₁.re / ‖w₁‖ * (w₀.im / ‖w₀‖) -
        √3 * (w₁.re / ‖w₁‖ * (w₀.re / ‖w₀‖) + w₁.im / ‖w₁‖ * (w₀.im / ‖w₀‖)) =
        (w₀.re * (w₁.im - √3 * w₁.re) - w₀.im * (w₁.re + √3 * w₁.im)) / (‖w₀‖ * ‖w₁‖) := by
      field_simp
      ring
    rw [e2]
    exact div_neg_of_neg_of_pos h (mul_pos n0 n1)
  by_contra hge
  push Not at hge
  have hpos : 0 ≤ Real.sin (ψ - Real.pi / 3) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hψ.2])
  rw [Real.sin_sub, Real.cos_pi_div_three, Real.sin_pi_div_three] at hpos
  linarith

/-! ### The Fuller–Poincaré map on `𝒟₀₀` -/

theorem mem_cellBox_zero_zero {p : Fin 3 → ℝ} : p ∈ cellBox 0 0 ↔
    p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc 0 (Real.pi / 3) ∧ p 2 ∈ Icc (Real.pi - 1.1) Real.pi := by
  simp [cellBox, basinA, basinB]

/-- The signs on `𝒟₀₀`: `y₂ ≤ 0 ≤ κ`, `sin θ₂ ≥ 0`, `sin θ₁ ≥ 0`. -/
theorem cellBox_facts {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0) :
    cy₂ p ≤ 0 ∧ 0 ≤ cκ p ∧ 0 ≤ Real.sin (p 2) ∧ 0 ≤ Real.sin (p 2 - p 1) ∧ p ∈ cellDomain := by
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := mem_cellBox_zero_zero.1 hp
  have hpi := Real.pi_gt_three
  refine ⟨?_, ?_, Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) h2',
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith), ⟨⟨h0, h0'⟩,
      ⟨h1, by linarith⟩, ⟨by linarith, h2'⟩⟩⟩
  · have : 0 ≤ Real.sin (p 2 + 2 / 3 * Real.pi - Real.pi) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at this
    unfold cy₂
    nlinarith
  · unfold cκ
    have := Real.sin_nonneg_of_nonneg_of_le_pi h1 (by linarith)
    have : 0 ≤ 1 - p 0 := by linarith
    positivity

/-- Off the face piece `r₂ = 0, θ₁ ≤ π/3`, the switching cubic is negative somewhere on
`t > 0`. -/
theorem exists_V₂_neg {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0)
    (hB : ¬(p 0 = 0 ∧ p 2 - p 1 ≤ Real.pi / 3)) : ∃ s, 0 < s ∧ V₂ p s < 0 := by
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := mem_cellBox_zero_zero.1 hp
  obtain ⟨hy, hk, -, -, -⟩ := cellBox_facts hp
  have hpi := Real.pi_gt_three
  have h3 : 0 ≤ √3 := Real.sqrt_nonneg 3
  have hy1 : |cy₁ p| ≤ 1 := by
    unfold cy₁
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - p 0)]
    have := Real.abs_sin_le_one (p 2 - p 1 + 2 / 3 * Real.pi)
    nlinarith [abs_nonneg (Real.sin (p 2 - p 1 + 2 / 3 * Real.pi))]
  rcases h0.lt_or_eq with h0 | h0
  · -- `r₂ > 0`: `y₂ < 0`
    have hs : 0 < Real.sin (p 2 + 2 / 3 * Real.pi - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at hs
    have hy' : cy₂ p < 0 := by unfold cy₂; nlinarith
    refine ⟨min 1 (-cy₂ p), lt_min one_pos (by linarith), ?_⟩
    set s := min 1 (-cy₂ p)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hs2 : s ≤ -cy₂ p := min_le_right _ _
    have hs0 : 0 < s := lt_min one_pos (by linarith)
    have e1 : cy₁ p * s ^ 2 / 2 ≤ s ^ 2 / 2 := by
      have := (abs_le.1 hy1).2
      nlinarith [sq_nonneg s]
    have e2 : s ^ 3 / 12 ≤ s ^ 2 / 12 := by nlinarith [sq_nonneg s]
    have e3 : 0 ≤ √3 * cκ p := mul_nonneg h3 hk
    have e4 : s ^ 2 * (7 / 12) + cy₂ p * s ≤ s * (5 / 12 * cy₂ p) := by nlinarith
    unfold V₂
    nlinarith
  · -- `r₂ = 0`: `θ₁ > π/3`, `y₁ < 0`
    have hθ : Real.pi / 3 < p 2 - p 1 := by
      by_contra hc; push Not at hc; exact hB ⟨h0.symm, hc⟩
    have hs : 0 < Real.sin (p 2 - p 1 + 2 / 3 * Real.pi - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at hs
    have hy1' : cy₁ p < 0 := by unfold cy₁; rw [← h0]; linarith
    have e0 : cy₂ p = 0 := by unfold cy₂; rw [← h0]; ring
    have ek : cκ p = 0 := by unfold cκ; rw [← h0]; ring
    refine ⟨-3 * cy₁ p, by linarith, ?_⟩
    have e : V₂ p (-3 * cy₁ p) = 9 / 4 * cy₁ p ^ 3 := by unfold V₂; rw [e0, ek]; ring
    rw [e]
    have : cy₁ p ^ 3 < 0 := Odd.pow_neg (by decide) hy1'
    linarith

/-- The first control is `ζ` and the first switch is at the root `τ` of `D`, when `D < 0` on
`(0, τ)`, `D > 0` on `(τ, ∞)` and `Im z₃(t) > 0` for `t > 0` (the control `1` beats `ζ` exactly
when `D > 0`, `ham_one_sub_ham_ζ`, and `ζ²` never does, `ham_ζ_sq_sub_ham_ζ`). -/
theorem firstControl_firstSwitchTime {p : Fin 3 → ℝ} (hz : cellPoint p ≠ 0) (hk : 0 ≤ cκ p)
    (hY : ∀ t, 0 < t → 0 < (flow t (cellPoint p) ζ 2).im) {τ : ℝ} (hτ : 0 < τ)
    (hneg : ∀ t, 0 < t → t < τ → V₂ p t < 0) (hpos : ∀ t, τ < t → 0 < V₂ p t)
    (h0 : V₂ p τ = 0) : firstControl (cellPoint p) = ζ ∧ firstSwitchTime (cellPoint p) = τ := by
  have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hY0 : 0 ≤ (flow 0 (cellPoint p) ζ 2).im := by rw [flow_two_im]; simp
  -- `ζ` maximizes on `[0, τ]`
  have hfc : firstControl (cellPoint p) = ζ := by
    refine (firstControl_eq_iff hz).2 ⟨ζ_mem_VT, τ, hτ, fun t ht v hv ↦ ?_⟩
    have hD : V₂ p t ≤ 0 := by
      rcases ht.1.lt_or_eq with h | h
      · rcases ht.2.lt_or_eq with h' | h'
        · exact (hneg t h h').le
        · rw [h', h0]
      · have e : V₂ p 0 = -(√3 * cκ p) := by unfold V₂; ring
        rw [← h, e]
        linarith [mul_nonneg (Real.sqrt_nonneg 3) hk]
    have hYt : 0 ≤ (flow t (cellPoint p) ζ 2).im := by
      rcases ht.1.lt_or_eq with h | h
      · exact (hY t h).le
      · rw [← h]; exact hY0
    rcases mem_VT.1 hv with rfl | rfl | rfl
    · have := ham_one_sub_ham_ζ p t
      nlinarith
    · exact le_rfl
    · have := ham_ζ_sq_sub_ham_ζ p t
      nlinarith
  refine ⟨hfc, ?_⟩
  -- the beaten times are the times with `D > 0`
  have key : ∀ t, 0 < t → ((∃ v ∈ VT, ham (flow t (cellPoint p) ζ) ζ <
      ham (flow t (cellPoint p) ζ) v) ↔ 0 < V₂ p t) := by
    intro t ht
    constructor
    · rintro ⟨v, hv, hlt⟩
      rcases mem_VT.1 hv with rfl | rfl | rfl
      · have := ham_one_sub_ham_ζ p t
        by_contra hc
        push Not at hc
        nlinarith
      · exact absurd hlt (lt_irrefl _)
      · have := ham_ζ_sq_sub_ham_ζ p t
        have hy := hY t ht
        nlinarith
    · intro hD
      refine ⟨1, one_mem_VT, ?_⟩
      have := ham_one_sub_ham_ζ p t
      nlinarith [mul_pos hs3 hD]
  unfold firstSwitchTime
  rw [hfc]
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨τ + 1, by linarith, (key _ (by linarith)).2 (hpos _ (by linarith))⟩
  · rintro a ⟨ha, hbeat⟩
    have hD := (key a ha).1 hbeat
    by_contra hlt
    push Not at hlt
    linarith [hneg a ha hlt]
  · intro w hw
    exact ⟨(τ + w) / 2, ⟨by linarith, (key _ (by linarith)).2 (hpos _ (by linarith))⟩,
      by linarith⟩

/-- `tan (11/20) ≤ 5/8` (`Real.sin_bound`, `Real.cos_bound`). -/
theorem tan_eleven_twentieths_le : Real.tan (11 / 20) ≤ 5 / 8 := by
  have hs := Real.sin_bound (x := 11 / 20) (by norm_num [abs_of_pos])
  have hc := Real.cos_bound (x := 11 / 20) (by norm_num [abs_of_pos])
  rw [abs_le] at hs hc
  have hc0 : 0 < Real.cos (11 / 20) := by norm_num [abs_of_pos] at hc; linarith [hc.1]
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hc0]
  norm_num [abs_of_pos] at hs hc
  linarith [hs.2, hc.1]

/-- The coordinates `(r₂, tan (ψ/2), tan ((π - θ₂)/2))` of a point of `𝒟₀₀` lie in the root
box. -/
theorem mem_root_of_cellBox {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0) :
    p 0 ∈ Icc 0 1 ∧ Real.tan (p 1 / 2) ∈ Icc 0 (37 / 64) ∧
      Real.tan ((Real.pi - p 2) / 2) ∈ Icc 0 (5 / 8) ∧ 0 < Real.cos (p 1 / 2) ∧
      0 < Real.cos ((Real.pi - p 2) / 2) := by
  obtain ⟨h0, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := mem_cellBox_zero_zero.1 hp
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  have hmono := Real.strictMonoOn_tan.monotoneOn
  refine ⟨h0, ⟨Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith), ?_⟩,
    ⟨Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith), ?_⟩,
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩,
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩⟩
  · have := hmono ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      (show p 1 / 2 ≤ Real.pi / 6 by linarith)
    rw [Real.tan_pi_div_six] at this
    refine this.trans ?_
    have h3 : (64 / 37 : ℝ) ≤ √3 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · have := hmono ⟨by linarith, by linarith⟩ ⟨by norm_num; linarith, by norm_num; linarith⟩
      (show (Real.pi - p 2) / 2 ≤ 11 / 20 by norm_num at h2 ⊢; linarith)
    exact this.trans tan_eleven_twentieths_le

/-- **The image of a point of `𝒟₀₀` off the face piece `r₂ = 0, θ₁ ≤ π/3`**: the first control
is `ζ`, the switch is the root of `D` certified by the tree, and the cell coordinates of the image
satisfy `ψ < π/3` and `θ₂ > 2π/3 ≥ π - 1.1`. -/
theorem poincareAngZero_mem_of_not_face {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0)
    (hB : ¬(p 0 = 0 ∧ p 2 - p 1 ≤ Real.pi / 3)) : poincareAngZero (cellClass p) ∈ boxSet 0 0 := by
  obtain ⟨hy, hk, hs2, hs21, hdom⟩ := cellBox_facts hp
  obtain ⟨s, hs, hVs⟩ := exists_V₂_neg hp hB
  obtain ⟨hr, ha, hb, hc1, hc2⟩ := mem_root_of_cellBox hp
  obtain ⟨tl, th, htl0, htlth, hth, htl, hcond⟩ := good_of_mem_root hr ha hb
  obtain ⟨e_r1, e_sa, e_c2, e_s2, e_x1, e_y1, e_x2, e_y2, e_k⟩ := coeffsR_cell hc1 hc2
  set c := coeffsR (p 0) (Real.tan (p 1 / 2)) (Real.tan ((Real.pi - p 2) / 2)) with hc
  have hD : ∀ t, dR c t = V₂ p t := by
    intro t; simp only [dR, e_y1, e_y2, e_k, V₂]; ring
  rw [hD] at hth
  rw [hD] at htl
  have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hV0 : V₂ p 0 ≤ 0 := by
    have e : V₂ p 0 = -(√3 * cκ p) := by unfold V₂; ring
    rw [e]; linarith [mul_nonneg hs3.le hk]
  have hth0 : 0 < th := by
    rcases (htl0.trans htlth).lt_or_eq with h | h
    · exact h
    · rw [← h] at hth; linarith
  -- the root `τ` of `D` in `(s, th)`
  have hsth : s < th := by
    by_contra hc'
    push Not at hc'
    rcases hc'.lt_or_eq with h | h
    · linarith [V₂_pos_of_nonneg hy hk hth0 h hth.le]
    · rw [h] at hth; linarith
  have hcont : ContinuousOn (V₂ p) (Icc s th) := by
    unfold V₂; fun_prop
  obtain ⟨τ, hτ, h0⟩ := intermediate_value_Ioo hsth.le hcont ⟨hVs, hth⟩
  have hτ0 : 0 < τ := hs.trans hτ.1
  have hneg : ∀ t, 0 < t → t < τ → V₂ p t < 0 := fun t ht htτ ↦
    V₂_neg_of_nonpos hy hk ht htτ h0.le
  have hpos : ∀ t, τ < t → 0 < V₂ p t := fun t htτ ↦ V₂_pos_of_nonneg hy hk hτ0 htτ h0.ge
  have htlτ : tl ≤ τ := by
    rcases htl with h | h
    · rw [h]; exact hτ0.le
    · by_contra hc'
      push Not at hc'
      linarith [hpos tl hc']
  -- the conditions at `τ`, in terms of `ζ z(τ)`
  have hU₀ : u0R c τ = U₀ p τ := by simp only [u0R, U₀, e_x1]; ring
  have hV₀ : v0R c τ = V₀ p τ := by simp only [v0R, V₀, e_y1]
  have hcond' : V₁ p τ + √3 * U₁ p τ < 0 ∧
      U₀ p τ * (V₁ p τ - √3 * U₁ p τ) - V₀ p τ * (U₁ p τ + √3 * V₁ p τ) < 0 := by
    obtain ⟨mode, hden, h2, h1⟩ := hcond τ ⟨htlτ, hτ.2.le⟩
    obtain ⟨μ, hμ, hu, hv⟩ : ∃ μ : ℝ, 0 < μ ∧ u1R c τ mode = μ * U₁ p τ ∧
        v1R c τ mode = μ * V₁ p τ := by
      cases mode with
      | false =>
        refine ⟨1, one_pos, ?_, ?_⟩
        · simp only [u1R, Bool.false_eq_true, ↓reduceIte, U₁, e_x1, e_x2]; ring
        · simp only [v1R, Bool.false_eq_true, ↓reduceIte, V₁, e_y1, e_y2]; ring
      | true =>
        have hd := hden rfl
        have hroot : (τ / 12 + c.y1 / 2) / denR c τ = p 0 / τ ^ 2 := by
          rw [div_eq_div_iff hd (by positivity)]
          have hx2 : c.x2 = p 0 * c.c2 := rfl
          have hy2 : c.y2 = p 0 * c.s2 := rfl
          have hk' : c.k = c.r1 * p 0 * c.sa := rfl
          have h0' := h0
          unfold V₂ at h0'
          rw [← e_y2, ← e_k, ← e_y1, hy2, hk'] at h0'
          unfold denR
          linear_combination h0'
        refine ⟨1 / τ, by positivity, ?_, ?_⟩
        · simp only [u1R, ↓reduceIte, hroot, U₁, ← e_x1, ← e_x2]
          have hx2 : c.x2 = p 0 * c.c2 := rfl
          rw [hx2]
          field_simp
          ring
        · simp only [v1R, ↓reduceIte, hroot, V₁, ← e_y1, ← e_y2]
          have hy2 : c.y2 = p 0 * c.s2 := rfl
          rw [hy2]
          field_simp
          ring
    rw [hu, hv] at h2 h1
    rw [hU₀, hV₀] at h1
    constructor
    · have e : μ * V₁ p τ + √3 * (μ * U₁ p τ) = μ * (V₁ p τ + √3 * U₁ p τ) := by ring
      rw [e] at h2
      exact neg_of_mul_neg_right h2 hμ.le
    · have e : U₀ p τ * (μ * V₁ p τ - √3 * (μ * U₁ p τ)) -
          V₀ p τ * (μ * U₁ p τ + √3 * (μ * V₁ p τ)) =
          μ * (U₀ p τ * (V₁ p τ - √3 * U₁ p τ) - V₀ p τ * (U₁ p τ + √3 * V₁ p τ)) := by ring
      rw [e] at h1
      exact neg_of_mul_neg_right h1 hμ.le
  obtain ⟨hC2, hC1⟩ := hcond'
  -- the first control and the first switch
  have hY : ∀ t, 0 < t → 0 < (flow t (cellPoint p) ζ 2).im := by
    intro t ht
    rw [flow_two_im]
    have : 0 ≤ 1 - p 0 := by linarith [hr.2]
    have : 0 ≤ p 0 * Real.sin (p 2) * t := by have := hr.1; positivity
    have : 0 ≤ (1 - p 0) * Real.sin (p 2 - p 1) * t ^ 2 / 2 := by positivity
    have : 0 < t ^ 3 / 12 := by positivity
    linarith
  have hz := cellPoint_mem_sectionZero hdom
  obtain ⟨hfc, hτe⟩ := firstControl_firstSwitchTime hz.1 hk hY hτ0 hneg hpos h0
  have hw := poincare_mem_sectionZero hz
  have hpw : poincare (cellPoint p) = flow τ (cellPoint p) ζ := by rw [poincare, hfc, hτe]
  obtain ⟨e0r, e0i, e1r, e1i, e2r, e2i⟩ := zeta_flow p τ
  have hV₁ := V₁_pos_of_root hy hk hτ0 h0
  have hU₂ : U₂ p τ < 0 := by
    have e := flow_two_im_eq (p := p) τ
    rw [h0] at e
    have := hY τ hτ0
    nlinarith
  -- the rotated image `w = ζ F(z)`, on the wall `𝒲₀`
  set w := ζ • poincare (cellPoint p) with hw_def
  have hζw : w ∈ sectionZero := by
    refine ⟨fun h ↦ hw.1 ?_, ?_, ?_⟩
    · have := congrArg (fun z ↦ ζ⁻¹ • z) h
      simp only [hw_def, smul_zero, inv_smul_smul₀ (show ζ ≠ 0 from fun h ↦ by
        simpa [h] using norm_ζ)] at this
      exact this
    · exact mul_mem_walls ζ_mem_VT hw.2.1
    · have := (hamMax_smul_scale_and_tau ζ_mem_VT one_pos (poincare (cellPoint p))).1
      rw [scale_one, one_pow, one_mul] at this
      rw [hw_def, this, hw.2.2]
  have hw0 : w 0 = ζ * flow τ (cellPoint p) ζ 0 := by
    rw [hw_def, Pi.smul_apply, smul_eq_mul, hpw]
  have hw1 : w 1 = ζ * flow τ (cellPoint p) ζ 1 := by
    rw [hw_def, Pi.smul_apply, smul_eq_mul, hpw]
  have hw2 : w 2 = ζ * flow τ (cellPoint p) ζ 2 := by
    rw [hw_def, Pi.smul_apply, smul_eq_mul, hpw]
  have him : (w 2).im = 0 := by rw [hw2, e2i, h0]
  have hre : (w 2).re < 0 := by rw [hw2, e2r]; exact hU₂
  obtain ⟨⟨c0, c1, -⟩, hcl⟩ := cellClass_cellCoords hζw him hre
  have hcls := classOf_smul_scale ζ_mem_VT one_pos hw
  rw [scale_one] at hcls
  have himage : poincareAngZero (cellClass p) = cellClass (cellCoords w) := by
    change poincareAngZero (classOf (cellPoint p)) = _
    rw [poincareAngZero_classOf hz, hcl, hw_def, hcls]
  rw [himage]
  refine ⟨cellCoords w, ?_, rfl⟩
  rw [mem_cellBox_zero_zero]
  refine ⟨⟨c0.1.le, c0.2.le⟩, ⟨c1.1.le, ?_⟩, ⟨?_, Complex.arg_le_pi _⟩⟩
  · -- `ψ < π/3`
    have := toIcoMod_lt_pi_div_three (w₀ := w 0) (w₁ := w 1) c1
      (by rw [hw0, hw1, e0r, e0i, e1r, e1i]; exact hC1)
    exact this.le
  · -- `θ₂ > 2π/3 ≥ π - 1.1`
    have := two_pi_div_three_lt_arg (w := w 1) (by rw [hw1, e1i]; exact hV₁)
      (by rw [hw1, e1i, e1r]; exact hC2)
    change Real.pi - 1.1 ≤ Complex.arg (w 1)
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith

/-- On the face piece `r₂ = 0`, `θ₁ = θ₂ - ψ ≤ π/3` (first control `1`), the point
`(e^{iθ₁}, 0, 0)` has the same class as its rotation `ζ (e^{iθ₁}, 0, 0) = (e^{i(θ₁ + 2π/3)}, 0, 0)`
(the `V_T`-equivariance), the cell point `(0, 0, θ₁ + 2π/3)` of `𝒟₀₀`. -/
theorem cellClass_face {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0) (h0 : p 0 = 0) :
    cellClass p = cellClass ![0, 0, p 2 - p 1 + 2 * Real.pi / 3] := by
  obtain ⟨-, -, -, -, hdom⟩ := cellBox_facts hp
  have hz := cellPoint_mem_sectionZero hdom
  have e : cellPoint ![0, 0, p 2 - p 1 + 2 * Real.pi / 3] = ζ • scale 1 (cellPoint p) := by
    rw [scale_one]
    funext j
    fin_cases j
    · simp only [cellPoint, Pi.smul_apply, smul_eq_mul, h0, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Fin.zero_eta]
      rw [ζ, sub_zero, Complex.ofReal_one, one_mul, one_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp [cellPoint, h0]
    · simp [cellPoint, h0]
  rw [cellClass, cellClass, e, classOf_smul_scale ζ_mem_VT one_pos hz]

/-- **`F(𝒟₀₀) ⊆ 𝒟₀₀`**, the first conjunct of `DOutContracts`
(`SmoothedPolygons/Ch16/BasinHypotheses.lean`): the Fuller–Poincaré map `poincareAngZero` maps the
box `𝒟₀₀ = 𝒟_out` of `Ξ_{𝒲,0}/V_T` into itself. -/
theorem mapsTo_boxSet_zero_zero : MapsTo poincareAngZero (boxSet 0 0) (boxSet 0 0) := by
  rintro x ⟨p, hp, rfl⟩
  by_cases hA : p 0 = 0 ∧ p 2 - p 1 ≤ Real.pi / 3
  · -- the face piece: change of representative
    obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := mem_cellBox_zero_zero.1 hp
    have hpi := Real.pi_gt_three
    have hp' : ![0, 0, p 2 - p 1 + 2 * Real.pi / 3] ∈ cellBox 0 0 := by
      rw [mem_cellBox_zero_zero]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      refine ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, by positivity⟩, ⟨?_, ?_⟩⟩
      · norm_num at h2 ⊢; linarith
      · linarith [hA.2]
    rw [cellClass_face hp hA.1]
    refine poincareAngZero_mem_of_not_face hp' fun h ↦ ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h
    linarith [h.2]
  · exact poincareAngZero_mem_of_not_face hp hA

/-- `DOutContracts` reduces to its second conjunct (the contraction to `q_out`), the first being
`mapsTo_boxSet_zero_zero`. -/
theorem dOutContracts_of
    (h : ∃ (lo hi : Fin 3 → ℝ) (N : ℕ) (κ : NNReal), κ < 1 ∧ Icc lo hi ⊆ openBoxOne ∧
      (∀ x ∈ boxSet 0 0, poincareAngZero^[N] x ∈ cellClass '' Icc lo hi) ∧
      ∃ g : (Fin 3 → ℝ) → (Fin 3 → ℝ), MapsTo g (Icc lo hi) (Icc lo hi) ∧
        LipschitzOnWith κ g (Icc lo hi) ∧
        ∀ p ∈ Icc lo hi, poincareAngZero (cellClass p) = cellClass (g p)) :
    DOutContracts :=
  ⟨mapsTo_boxSet_zero_zero, h⟩

end SmoothedPolygons.TriFuller.DOutMaps
