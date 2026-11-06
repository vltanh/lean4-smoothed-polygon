module

public import SmoothedPolygons.Ch2.MultiCurve
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Topology

/-!
# Hyperbolic arcs (Lemma 3.1.8)

If two curves `σ_{i-1}` and `σ_{i+1}` of a multi-curve parametrizing the boundary of a centrally
symmetric convex disk move along straight lines during a time interval, then the third curve `σ_i`
moves along a hyperbolic arc whose asymptotes are these two lines (Reinhardt's observation that
the pencil of lines cutting a constant area from a parallelogram envelopes a hyperbola).

The lemma belongs to §3.1 (`SmoothedPolygons.Ch3.StateDynamics`); it is kept in its own module
because it uses only the vocabulary of Chapter 2 (`IsCCSDisk`, `IsMultiCurve`, `det2`) and adding
it to `StateDynamics` would rebuild the modules of Chapters 3–7 that import it.

Conventions. The line through `p` with direction `d ≠ 0` is `{x | det(d, x - p) = 0}`. For two
lines `L₁ = {det(d₁, x - p₁) = 0}` and `L₂ = {det(d₂, x - p₂) = 0}` that are not parallel
(`det(d₁, d₂) ≠ 0`), the level sets `{x | det(d₁, x - p₁) · det(d₂, x - p₂) = c}` with `c ≠ 0` are
exactly the hyperbolas with asymptotes `L₁` and `L₂`, as in Remark 2.2.4 (`hexHyperbolaFun`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- `det(d, x - p) = det(d, x) - det(d, p)`. -/
private lemma sm_det2_sub (d x p : Fin 2 → ℝ) : det2 d (x - p) = det2 d x - det2 d p := by
  simp only [det2, Pi.sub_apply]; ring

private lemma sm_det2_add (d x y : Fin 2 → ℝ) : det2 d (x + y) = det2 d x + det2 d y := by
  simp only [det2, Pi.add_apply]; ring

private lemma sm_det2_neg (d x : Fin 2 → ℝ) : det2 d (-x) = -det2 d x := by
  simp only [det2, Pi.neg_apply]; ring

private lemma sm_det2_smul (d x : Fin 2 → ℝ) (c : ℝ) : det2 d (c • x) = c * det2 d x := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]; ring

private lemma sm_det2_comm (x y : Fin 2 → ℝ) : det2 x y = -det2 y x := by
  simp only [det2]; ring

private lemma sm_det2_self (x : Fin 2 → ℝ) : det2 x x = 0 := by
  simp only [det2]; ring

/-- Cramer's rule in the plane: `det(a, b) c = det(c, b) a + det(a, c) b`. -/
private lemma sm_cramer (a b c : Fin 2 → ℝ) :
    det2 a b • c = det2 c b • a + det2 a c • b := by
  ext k
  fin_cases k <;> simp [det2] <;> ring

private lemma sm_ne_zero_of_det2 {d : Fin 2 → ℝ} (hd : d ≠ 0) : 0 < d 0 ^ 2 + d 1 ^ 2 := by
  by_contra h
  apply hd
  ext k
  fin_cases k <;> simp <;> nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)]

/-- A curve that is constant on a neighbourhood of `t₀` has derivative zero at `t₀`. -/
private lemma sm_derivWithin_eq_zero {f : ℝ → Fin 2 → ℝ} {s U : Set ℝ} {t₀ : ℝ}
    {C : Fin 2 → ℝ} (hU : U ∈ 𝓝 t₀) (hf : ∀ t ∈ U, f t = C) : derivWithin f s t₀ = 0 := by
  have h : f =ᶠ[𝓝 t₀] fun _ ↦ C := Filter.mem_of_superset hU fun t ht ↦ hf t ht
  rw [h.derivWithin_eq_of_nhds]
  simp

/-- **Supporting line.** If a curve `γ` in a convex set `K` with nonempty interior moves along the
line `{det(d, x - p) = 0}` near `t₀`, with nonzero velocity at `t₀`, and `γ(t₀)` is a boundary point
of `K`, then the line supports `K`: `K` lies on one side of it. -/
private lemma sm_support {K : Set (Fin 2 → ℝ)} (hKc : Convex ℝ K) (hKi : (interior K).Nonempty)
    {γ : ℝ → Fin 2 → ℝ} {t₀ : ℝ} {v : Fin 2 → ℝ} (hγ : HasDerivAt γ v t₀) (hv : v ≠ 0)
    (hK : ∀ᶠ t in 𝓝 t₀, γ t ∈ K) (hfr : γ t₀ ∉ interior K) {d p : Fin 2 → ℝ} (hd : d ≠ 0)
    (hline : ∀ᶠ t in 𝓝 t₀, det2 d (γ t - p) = 0) :
    ∃ μ : ℝ, μ ≠ 0 ∧ ∀ x ∈ K, μ * det2 d (x - p) ≤ 0 := by
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point hKc.interior isOpen_interior hfr
  -- `φ ≤ φ(γ t₀)` on `K = closure (interior K)`
  have hle : ∀ x ∈ K, φ x ≤ φ (γ t₀) := by
    intro x hx
    have hcl : K ⊆ closure (interior K) := by
      rw [hKc.closure_interior_eq_closure_of_nonempty_interior hKi]; exact subset_closure
    have : closure (interior K) ⊆ {x | φ x ≤ φ (γ t₀)} :=
      closure_minimal (fun y hy ↦ (hφ y hy).le) (isClosed_le φ.continuous continuous_const)
    exact this (hcl hx)
  -- Fermat: `φ(v) = 0`
  have hmax : IsLocalMax (fun t ↦ φ (γ t)) t₀ := hK.mono fun t ht ↦ hle _ ht
  have hφv : φ v = 0 := IsLocalMax.hasDerivAt_eq_zero hmax (φ.hasFDerivAt.comp_hasDerivAt t₀ hγ)
  -- the velocity is parallel to the line: `det(d, v) = 0`
  have hdv : det2 d v = 0 := by
    have h0 := hasDerivAt_pi.1 hγ 0
    have h1 := hasDerivAt_pi.1 hγ 1
    have hD : HasDerivAt (fun t ↦ det2 d (γ t - p)) (det2 d v) t₀ := by
      simp only [det2, Pi.sub_apply]
      exact ((h1.sub_const (p 1)).const_mul (d 0)).sub ((h0.sub_const (p 0)).const_mul (d 1))
    have hD0 : HasDerivAt (fun t ↦ det2 d (γ t - p)) 0 t₀ :=
      (hasDerivAt_const t₀ (0 : ℝ)).congr_of_eventuallyEq hline
    exact hD.unique hD0
  -- `φ = μ det(d, ·)`
  set a₀ := φ (Pi.single 0 1)
  set a₁ := φ (Pi.single 1 1)
  have hφx : ∀ x : Fin 2 → ℝ, φ x = a₀ * x 0 + a₁ * x 1 := by
    intro x
    have hx : x = x 0 • (Pi.single 0 1 : Fin 2 → ℝ) + x 1 • Pi.single 1 1 := by
      ext k; fin_cases k <;> simp
    conv_lhs => rw [hx]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm (x 0), mul_comm (x 1)]
  have hφd : a₀ * d 0 + a₁ * d 1 = 0 := by
    rw [hφx] at hφv
    simp only [det2] at hdv
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := fun h ↦ hv (by ext k; fin_cases k <;> simp [hv0, h])
      refine (mul_left_inj' hv1).1 ?_
      linear_combination d 1 * hφv + a₀ * hdv
    · refine (mul_left_inj' hv0).1 ?_
      linear_combination d 0 * hφv - a₁ * hdv
  have hd2 := sm_ne_zero_of_det2 hd
  set μ := (a₁ * d 0 - a₀ * d 1) / (d 0 ^ 2 + d 1 ^ 2) with hμ
  have hφμ : ∀ x, φ x = μ * det2 d x := by
    intro x
    have e : φ x * (d 0 ^ 2 + d 1 ^ 2) = (a₁ * d 0 - a₀ * d 1) * det2 d x := by
      rw [hφx, det2]
      linear_combination (d 0 * x 0 + d 1 * x 1) * hφd
    rw [hμ, div_mul_eq_mul_div, eq_div_iff hd2.ne', e]
  refine ⟨μ, fun h0 ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨y, hy⟩ := hKi
    have := hφ y hy
    rw [hφμ, hφμ, h0, zero_mul, zero_mul] at this
    exact lt_irrefl _ this
  · have hγp : det2 d (γ t₀ - p) = 0 := hline.self_of_nhds
    have h1 := hle x hx
    rw [hφμ, hφμ] at h1
    rw [sm_det2_sub] at hγp ⊢
    linear_combination h1 + μ * hγp


/-- From `P x = r d` with `r ≠ 0`, `d ≠ 0`: `x = (r/P) d`. -/
private lemma sm_eq_smul_of_smul {P r : ℝ} {x d : Fin 2 → ℝ} (hd : d ≠ 0) (hr : r ≠ 0)
    (h : P • x = r • d) : x = (r / P) • d := by
  have hP : P ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h
    exact (smul_ne_zero hr hd) h.symm
  rw [div_eq_inv_mul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ hP, one_smul]

private lemma sm_le_of_mul {μ X : ℝ} (h : μ * X ≤ 0) : (0 < μ → X ≤ 0) ∧ (μ < 0 → 0 ≤ X) :=
  ⟨fun hμ ↦ by nlinarith, fun hμ ↦ by nlinarith⟩

/-- The sign bookkeeping of the parallel case: two parallel supporting lines at levels `A`, `B`
of `det(d₁, ·)` with `σ_i = σ_{i-1} + σ_{i+1}` force `A + B = 0`. -/
private lemma sm_sign_cases {μ₁ μ₂ A B : ℝ} (h1 : μ₁ ≠ 0) (h2 : μ₂ ≠ 0)
    (i1 : μ₁ * (-A - A) ≤ 0) (i2 : μ₁ * B ≤ 0) (i3 : μ₁ * (-B - A) ≤ 0)
    (j1 : μ₂ * (-B - B) ≤ 0) (j2 : μ₂ * A ≤ 0) (j3 : μ₂ * (-A - B) ≤ 0) : A + B = 0 := by
  have f1 := sm_le_of_mul i1
  have f2 := sm_le_of_mul i2
  have f3 := sm_le_of_mul i3
  have f4 := sm_le_of_mul j1
  have f5 := sm_le_of_mul j2
  have f6 := sm_le_of_mul j3
  rcases h1.lt_or_gt with h1 | h1 <;> rcases h2.lt_or_gt with h2 | h2
  · linarith [f1.2 h1, f2.2 h1, f3.2 h1, f4.2 h2, f5.2 h2, f6.2 h2]
  · linarith [f1.2 h1, f2.2 h1, f3.2 h1, f4.1 h2, f5.1 h2, f6.1 h2]
  · linarith [f1.1 h1, f2.1 h1, f3.1 h1, f4.2 h2, f5.2 h2, f6.2 h2]
  · linarith [f1.1 h1, f2.1 h1, f3.1 h1, f4.1 h2, f5.1 h2, f6.1 h2]


set_option linter.unusedVariables false in
/-- **Lemma 3.1.8** (`lem:hyp-arc`). Suppose that `K ∈ 𝔎_ccs` and that the boundary of `K` is
parametrized by a `C¹` multi-curve `σ`. If two curves `σ_{i-1}` and `σ_{i+1}` move along straight
lines during some time interval, then the third curve `σ_i` moves along a hyperbolic arc, whose
asymptotes are the lines determined by `σ_{i-1}` and `σ_{i+1}`.

Reading. "The boundary is parametrized by a `C¹` multi-curve" is read, as in §2.4 (TeX 1944–1947:
"we can parameterize the boundary by a regular `C¹` curve"), as: `σ` is a `C¹` multi-curve on
`[0, t_f]` (Definition 2.4.1), every `σ_j(t)` lies on the boundary of `K`, the arcs
`σ_j([0, t_f])` cover the boundary, and the curves are regular (`σ_j' ≠ 0`). The time interval is
`[a, b] ⊆ [0, t_f]` with `a < b`; `σ_{i-1}` moves along the line `L₁` through `p₁` with direction
`d₁ ≠ 0`, and `σ_{i+1}` along the line `L₂` through `p₂` with direction `d₂ ≠ 0` (regular curves
are not constant, so these are the lines determined by `σ_{i-1}` and `σ_{i+1}`).
The conclusion: the lines are not parallel, and `σ_i([a, b])` lies on one hyperbola
`det(d₁, x - p₁) · det(d₂, x - p₂) = c`, `c ≠ 0`, with asymptotes `L₁` and `L₂`.

Without regularity the statement is false: for the square `[-λ, λ]²`, `λ² = √3/2`, the boundary
has a `C¹` multi-curve in which `σ₂ = (-λ, 0)` is constant while `σ₁` and `σ₃ = -σ₀` slide along
the parallel edge lines `y = λ` and `y = -λ`; no hyperbola has parallel asymptotes.

Proof: the book's area argument, made algebraic. Write `u = σ_{i-1}`, `w = σ_{i+1}`; the multi-point
relations give `σ_i = u + w` and `det(u, w) = √3/2`.
(a) `P_K` is a parallelogram (`det(d₁, d₂) ≠ 0`): each line contains an arc of `∂K`, so it supports
`K` (Hahn–Banach at the boundary point and Fermat at an interior time, `sm_support`). If the lines
were parallel, the support inequalities at `±u, ±w, ±σ_i ∈ K` would force `σ_i` onto the line
through `0` parallel to `L₁`, where `det(σ_{i-1}, σ_i) = √3/2` pins it to one point: `σ_i` would be
constant, contradicting regularity.
(b) The area cut off from `P_K` is constant: for every multi-point,
`det(d₁, σ_i - p₁) det(d₂, σ_i - p₂) = det(d₁, p₁) det(d₂, p₂) - (√3/2) det(d₁, d₂)`. In the
coordinates of `P_K`, `4 det(d₁, p₁) det(d₂, p₂)/det(d₁, d₂)` is the (signed) area of `P_K`,
`4 · √3/2 = √12` is the area of the hexagon `H_K(t)` (a centrally symmetric hexagon with edge
midpoints `m_j` has area `4 det(m₀, m₂)`), and `4 det(d₁, σ_i - p₁) det(d₂, σ_i - p₂)/det(d₁, d₂)`
is (up to sign) twice the area of the triangle cut off at the corner `L₁ ∩ L₂` by the edge of
`H_K(t)` with midpoint `σ_i`. So the identity is the book's "`area(P_K) - area(H_K(t))` is
constant", and it places the midpoint `σ_i` directly on the hyperbola enveloped by the cutting
lines; the tangent lines at `±σ_i` themselves are not needed.
(c) `c ≠ 0`: otherwise, for each `t` one factor vanishes; the two zero sets are closed and cover
`[a, b]`, so one has interior points, and there `σ_{i+1}` (resp. `σ_{i-1}`) lies on the line through
`0` parallel to `L₁` (resp. `L₂`), hence is constant, contradicting regularity.

The hypothesis `hcover` (the arcs cover `∂K`, part of "the boundary is parametrized by `σ`") is
not used by the proof; it is kept because it is part of the book's hypothesis. -/
theorem lemma3_1_8 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    {tf : ℝ} (hσ : IsMultiCurve 1 σ tf) (hbd : ∀ j, ∀ t ∈ Set.Icc 0 tf, σ j t ∈ frontier K)
    (hcover : (⋃ j, σ j '' Set.Icc 0 tf) = frontier K)
    (hreg : ∀ j, ∀ t ∈ Set.Icc 0 tf, derivWithin (σ j) (Set.Icc 0 tf) t ≠ 0)
    (i : ZMod 6) {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ tf)
    {p₁ d₁ p₂ d₂ : Fin 2 → ℝ} (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (h₁ : ∀ t ∈ Set.Icc a b, det2 d₁ (σ (i - 1) t - p₁) = 0)
    (h₂ : ∀ t ∈ Set.Icc a b, det2 d₂ (σ (i + 1) t - p₂) = 0) :
    det2 d₁ d₂ ≠ 0 ∧ ∃ c : ℝ, c ≠ 0 ∧ ∀ t ∈ Set.Icc a b,
      det2 d₁ (σ i t - p₁) * det2 d₂ (σ i t - p₂) = c := by
  obtain ⟨hKc, hKcpt, hKi, hKs⟩ := hK
  have hsub : Icc a b ⊆ Icc 0 tf := Icc_subset_Icc ha hb
  -- the multi-point relations `σ_i = σ_{i-1} + σ_{i+1}`, `det(σ_{i-1}, σ_i) = √3/2`
  have hmp : ∀ t ∈ Icc a b, σ i t = σ (i - 1) t + σ (i + 1) t ∧
      det2 (σ (i - 1) t) (σ i t) = √3 / 2 ∧ det2 (σ (i - 1) t) (σ (i + 1) t) = √3 / 2 := by
    intro t ht
    have h := hσ.2 t (hsub ht)
    obtain ⟨h1, -, h3⟩ := h (i - 1)
    obtain ⟨-, h2, -⟩ := h i
    dsimp only at h1 h2 h3
    simp only [show i - 1 + 2 = i + 1 by ring, show i - 1 + 4 = i + 3 by ring,
      show i - 1 + 1 = i by ring] at h1 h3
    rw [h2] at h1
    have hs : σ i t = σ (i - 1) t + σ (i + 1) t := by
      rw [← sub_eq_zero, ← neg_eq_zero]; rw [← h1]; abel
    refine ⟨hs, h3, ?_⟩
    rw [← h3, hs, show σ (i - 1) t + σ (i + 1) t = σ (i + 1) t + σ (i - 1) t from add_comm _ _,
      sm_det2_add, sm_det2_self, add_zero]
  have hK_of : ∀ j, ∀ t ∈ Icc 0 tf, σ j t ∈ K := fun j t ht ↦
    hKcpt.isClosed.frontier_subset (hbd j t ht)
  -- a regular curve is not constant near an interior time
  have hnc : ∀ j (U : Set ℝ) (t₁ : ℝ), U ∈ 𝓝 t₁ → t₁ ∈ Icc 0 tf → ∀ C : Fin 2 → ℝ,
      (∀ t ∈ U, σ j t = C) → False := fun j U t₁ hU ht₁ C hC ↦
    hreg j t₁ ht₁ (sm_derivWithin_eq_zero hU hC)
  set t₀ := (a + b) / 2 with ht₀def
  have ht₀ : t₀ ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have ht₀' : t₀ ∈ Icc 0 tf := hsub (Ioo_subset_Icc_self ht₀)
  have hIab : Icc a b ∈ 𝓝 t₀ := Icc_mem_nhds ht₀.1 ht₀.2
  have hI0 : Icc 0 tf ∈ 𝓝 t₀ := Filter.mem_of_superset hIab hsub
  have hder : ∀ j, HasDerivAt (σ j) (derivWithin (σ j) (Icc 0 tf) t₀) t₀ := by
    intro j
    have hd : DifferentiableAt ℝ (σ j) t₀ :=
      (((hσ.1 j).differentiableOn (by norm_num)) t₀ ht₀').differentiableAt hI0
    rw [derivWithin_of_mem_nhds hI0]
    exact hd.hasDerivAt
  -- the products `det(d₁, σ_i - p₁) det(d₂, σ_i - p₂)` (the area cut off from `P_K`)
  set c := det2 d₁ p₁ * det2 d₂ p₂ - √3 / 2 * det2 d₁ d₂ with hc
  have hid : ∀ t ∈ Icc a b, det2 d₁ (σ i t - p₁) * det2 d₂ (σ i t - p₂) = c := by
    intro t ht
    obtain ⟨hs, -, hdet⟩ := hmp t ht
    have e1 := h₁ t ht
    have e2 := h₂ t ht
    rw [hs, hc]
    generalize σ (i - 1) t = u at e1 hdet
    generalize σ (i + 1) t = w at e2 hdet
    simp only [det2, Pi.sub_apply, Pi.add_apply] at e1 e2 hdet ⊢
    linear_combination
      ((d₂ 0 * u 1 - d₂ 1 * u 0) + 2 * (d₂ 0 * (w 1 - p₂ 1) - d₂ 1 * (w 0 - p₂ 0)) +
        (d₂ 0 * p₂ 1 - d₂ 1 * p₂ 0)) * e1 +
      ((d₁ 0 * w 1 - d₁ 1 * w 0) + (d₁ 0 * p₁ 1 - d₁ 1 * p₁ 0)) * e2 -
      (d₁ 0 * d₂ 1 - d₁ 1 * d₂ 0) * hdet
  have hP₁ : ∀ t ∈ Icc a b, det2 d₁ (σ (i - 1) t) = det2 d₁ p₁ := fun t ht ↦ by
    have := h₁ t ht; rw [sm_det2_sub] at this; linarith
  have hP₂ : ∀ t ∈ Icc a b, det2 d₂ (σ (i + 1) t) = det2 d₂ p₂ := fun t ht ↦ by
    have := h₂ t ht; rw [sm_det2_sub] at this; linarith
  have hab0 : t₀ ∈ Icc a b := Ioo_subset_Icc_self ht₀
  -- (a) the lines are not parallel, so `±L₁, ±L₂` bound a parallelogram `P_K`
  have hD : det2 d₁ d₂ ≠ 0 := by
    intro hD
    have hfr : ∀ j, σ j t₀ ∉ interior K := fun j h ↦ (hbd j t₀ ht₀').2 h
    have hevK : ∀ j, ∀ᶠ t in 𝓝 t₀, σ j t ∈ K := fun j ↦
      Filter.mem_of_superset hI0 fun t ht ↦ hK_of j t ht
    -- both lines support `K` (they contain arcs of the boundary)
    obtain ⟨μ₁, hμ₁, hs₁⟩ := sm_support hKc hKi (hder (i - 1)) (hreg _ _ ht₀') (hevK _)
      (hfr _) hd₁ (Filter.mem_of_superset hIab fun t ht ↦ h₁ t ht)
    obtain ⟨μ₂, hμ₂, hs₂⟩ := sm_support hKc hKi (hder (i + 1)) (hreg _ _ ht₀') (hevK _)
      (hfr _) hd₂ (Filter.mem_of_superset hIab fun t ht ↦ h₂ t ht)
    -- `det(d₂, ·) = κ det(d₁, ·)`
    have hd₁2 := sm_ne_zero_of_det2 hd₁
    set κ := (d₁ 0 * d₂ 0 + d₁ 1 * d₂ 1) / (d₁ 0 ^ 2 + d₁ 1 ^ 2) with hκ
    have hκx : ∀ x, det2 d₂ x = κ * det2 d₁ x := by
      intro x
      have e : det2 d₂ x * (d₁ 0 ^ 2 + d₁ 1 ^ 2) = (d₁ 0 * d₂ 0 + d₁ 1 * d₂ 1) * det2 d₁ x := by
        simp only [det2] at hD ⊢
        linear_combination (-(d₁ 0 * x 0) - d₁ 1 * x 1) * hD
      rw [hκ, div_mul_eq_mul_div, eq_div_iff hd₁2.ne', e]
    have hκ0 : κ ≠ 0 := by
      intro h0
      apply hd₂
      have e0 := hκx (Pi.single 0 1)
      have e1 := hκx (Pi.single 1 1)
      simp [det2, h0] at e0 e1
      ext k; fin_cases k <;> simp [e0, e1]
    -- the values of `det(d₁, ·)` at the multi-point
    obtain ⟨hs, -, -⟩ := hmp t₀ hab0
    have hu := hP₁ t₀ hab0
    have hw : det2 d₂ p₂ = κ * det2 d₁ (σ (i + 1) t₀) := by rw [← hP₂ t₀ hab0, hκx]
    have hmemK : ∀ j, σ j t₀ ∈ K := fun j ↦ hK_of j t₀ ht₀'
    have i1 := hs₁ _ (hKs _ (hmemK (i - 1)))
    have i2 := hs₁ _ (hmemK i)
    have i3 := hs₁ _ (hKs _ (hmemK (i + 1)))
    have j1 := hs₂ _ (hKs _ (hmemK (i + 1)))
    have j2 := hs₂ _ (hmemK i)
    have j3 := hs₂ _ (hKs _ (hmemK (i - 1)))
    rw [sm_det2_sub, sm_det2_neg, hu] at i1
    rw [sm_det2_sub, hs, sm_det2_add, hu] at i2
    rw [sm_det2_sub, sm_det2_neg] at i3
    rw [sm_det2_sub, sm_det2_neg, hw, hκx] at j1
    rw [sm_det2_sub, hw, hs, hκx, sm_det2_add, hu] at j2
    rw [sm_det2_sub, sm_det2_neg, hw, hκx, hu] at j3
    have hAB : det2 d₁ p₁ + det2 d₁ (σ (i + 1) t₀) = 0 :=
      sm_sign_cases hμ₁ (mul_ne_zero hμ₂ hκ0) i1 (by convert i2 using 1; ring) i3
        (by convert j1 using 1; ring) (by convert j2 using 1; ring) (by convert j3 using 1; ring)
    -- so `σ_i` lies on the line through `0` parallel to `L₁`, and is constant
    have hconst : ∀ t ∈ Icc a b, σ i t = (-(√3 / 2) / det2 d₁ p₁) • d₁ := by
      intro t ht
      obtain ⟨hs', hdet, -⟩ := hmp t ht
      have hwt : det2 d₁ (σ (i + 1) t) = det2 d₁ (σ (i + 1) t₀) := by
        have := hP₂ t ht
        rw [hκx, ← hP₂ t₀ hab0, hκx] at this
        exact mul_left_cancel₀ hκ0 this
      have hv0 : det2 d₁ (σ i t) = 0 := by rw [hs', sm_det2_add, hP₁ t ht, hwt, hAB]
      have hcr := sm_cramer d₁ (σ (i - 1) t) (σ i t)
      rw [hP₁ t ht, sm_det2_comm (σ i t), hdet, hv0, zero_smul, add_zero] at hcr
      exact sm_eq_smul_of_smul hd₁ (neg_ne_zero.2 (by positivity)) hcr
    exact hnc i _ t₀ hIab ht₀' _ hconst
  -- (c) the constant is not zero
  refine ⟨hD, c, fun hc0 ↦ ?_, hid⟩
  have hσc : ∀ j, ContinuousOn (σ j) (Icc a b) := fun j ↦ (hσ.1 j).continuousOn.mono hsub
  have hcont : ∀ (d p : Fin 2 → ℝ), ContinuousOn (fun t ↦ det2 d (σ i t - p)) (Icc a b) := by
    intro d p
    have h0 : ContinuousOn (fun t ↦ σ i t 0) (Icc a b) :=
      (continuous_apply 0).comp_continuousOn (hσc i)
    have h1 : ContinuousOn (fun t ↦ σ i t 1) (Icc a b) :=
      (continuous_apply 1).comp_continuousOn (hσc i)
    simp only [det2, Pi.sub_apply]
    exact ((h1.sub continuousOn_const).const_smul (d 0)).sub
      ((h0.sub continuousOn_const).const_smul (d 1))
  set Z₁ := Icc a b ∩ (fun t ↦ det2 d₁ (σ i t - p₁)) ⁻¹' {0} with hZ₁
  set Z₂ := Icc a b ∩ (fun t ↦ det2 d₂ (σ i t - p₂)) ⁻¹' {0} with hZ₂
  have hZ₁c : IsClosed Z₁ :=
    (hcont d₁ p₁).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hunion : Z₁ ∪ Z₂ = Icc a b := by
    ext t
    refine ⟨fun h ↦ h.elim (fun h ↦ h.1) (fun h ↦ h.1), fun ht ↦ ?_⟩
    rcases mul_eq_zero.1 ((hid t ht).trans hc0) with h | h
    exacts [Or.inl ⟨ht, h⟩, Or.inr ⟨ht, h⟩]
  have hZ₁i : interior Z₁ = ∅ := by
    by_contra hne
    obtain ⟨t₁, ht₁⟩ := Set.nonempty_iff_ne_empty.2 hne
    refine hnc (i + 1) (interior Z₁) t₁ (isOpen_interior.mem_nhds ht₁)
      (hsub (interior_subset ht₁).1) ((-(√3 / 2) / det2 d₁ p₁) • d₁) fun t ht ↦ ?_
    obtain ⟨htab, hG⟩ := interior_subset ht
    simp only [mem_preimage, mem_singleton_iff] at hG
    obtain ⟨hs', -, hdet⟩ := hmp t htab
    have hw0 : det2 d₁ (σ (i + 1) t) = 0 := by
      rw [sm_det2_sub, hs', sm_det2_add, hP₁ t htab] at hG; linarith
    have hcr := sm_cramer d₁ (σ (i - 1) t) (σ (i + 1) t)
    rw [hP₁ t htab, sm_det2_comm (σ (i + 1) t), hdet, hw0, zero_smul, add_zero] at hcr
    exact sm_eq_smul_of_smul hd₁ (neg_ne_zero.2 (by positivity)) hcr
  have hZ₂i : interior Z₂ = ∅ := by
    by_contra hne
    obtain ⟨t₁, ht₁⟩ := Set.nonempty_iff_ne_empty.2 hne
    refine hnc (i - 1) (interior Z₂) t₁ (isOpen_interior.mem_nhds ht₁)
      (hsub (interior_subset ht₁).1) ((√3 / 2 / det2 d₂ p₂) • d₂) fun t ht ↦ ?_
    obtain ⟨htab, hG⟩ := interior_subset ht
    simp only [mem_preimage, mem_singleton_iff] at hG
    obtain ⟨hs', -, hdet⟩ := hmp t htab
    have hu0 : det2 d₂ (σ (i - 1) t) = 0 := by
      rw [sm_det2_sub, hs', sm_det2_add, hP₂ t htab] at hG; linarith
    have hcr := sm_cramer d₂ (σ (i + 1) t) (σ (i - 1) t)
    rw [hP₂ t htab, hdet, hu0, zero_smul, add_zero] at hcr
    exact sm_eq_smul_of_smul hd₂ (by positivity) hcr
  have h := interior_union_isClosed_of_interior_empty hZ₁c hZ₂i
  rw [hunion, interior_Icc, hZ₁i] at h
  exact (h ▸ ht₀ : t₀ ∈ (∅ : Set ℝ))

end SmoothedPolygons
