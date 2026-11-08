module

public import SmoothedPolygons.Ch8.SingularLocus
public import SmoothedPolygons.Ch8.EdgeBangBang
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Non-chattering away from the singular locus (§8.3: Theorems 8.3.1, 8.3.2)

* `theorem8_3_1`: Theorem 8.3.1 (`thm:avoid-singular`) in the one-sided form below. Near a time
  `t₀` at which the lift avoids `𝒮_sing`, the maximizers of the Hamiltonian lie in one edge of
  `U_T` at every time just before `t₀`, and in one (possibly different) edge at every time just
  after `t₀`.
* `IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn`: the control form of Theorem 8.3.1
  that the proof of Theorem 8.3.2 quotes, which is two-sided: the control lies in a single edge
  almost everywhere on a neighbourhood of `t₀` (from `theorem8_3_1`, edge extremality and
  Theorem 8.1.4).
* `theorem8_3_2`: Theorem 8.3.2 (`thm:finite-bang-bang`). An extremal lifted trajectory on a
  compact interval that does not meet the singular locus and is edge extremal has a bang-bang
  control with finitely many switches. Its proof (TeX 7598–7605) quotes Theorem 8.3.1 in the form
  "for every `t₀ ∈ [t₁, t₂]`, there exists a neighborhood of `t₀` on which the control takes
  values in a single edge of `U_T` almost everywhere", applies Theorem 8.1.4 on each such
  neighbourhood, and concludes by compactness.

## Theorem 8.3.1 as printed is false (gap G2)

Theorem 8.3.1 (TeX 7448–7458) is printed about the *maximizers*: there are an edge `{i, j}` and a
neighbourhood of `t₀` in `[t₁, t₂]` on which `(X(t), Λ_R(t)) ∈ ⋃_{I ⊆ {i, j}} (T*O_J)_I`, i.e. the
set of maximizers of the Hamiltonian is contained in the edge `{i, j}` of `U_T` at every time of
the neighbourhood. This is false:

* At a time `t₀` with `Λ_R(t₀) = 0` the Hamiltonian does not depend on the control, so the set of
  maximizers at `t₀` itself is all of `U_T`. Such `t₀` off `𝒮_sing` occur on edge-extremal
  extremals. Counterexample (normal; checked numerically): `λ_cost = -1`, `X(0) = Φ(0.1 + 0.9i)`
  (not `J`), `Λ_R(0) = 0`, `Λ₁(0) = -(3/2) J + L` with `0 ≠ L ⊥ X(0)`, so
  `W = [L, X(0)] ≠ 0` and `H(0) = 0`; let `e_a`, `e_b` be the vertices maximizing and minimizing
  `⟨W, P_u⟩` on `U_T` (unique for generic `L`); the control `e_b` on `(-ε, 0)` and `e_a` on
  `(0, ε)` with the solutions of the state and costate equations is, for small `ε`, an extremal
  lifted trajectory (`Λ_R(t) = -Wt + O(t²)`, so the control is the unique maximizer for `t ≠ 0`;
  `H ≡ 0` by conservation on each side and continuity at `0`), it is edge extremal (the control
  lies in the edge spanned by `e_a, e_b`, where an abnormal edge costate with `λ₂(0) = 0`,
  `λ₃ = -λ₁(0) y(0)²`, `λ₂'(0) = -2λ₁(0) ≠ 0` switches once at `0`; constant controls on the two
  halves are edge extremal for the other edges), and it does not meet `𝒮_sing` (`X(0) ≠ J`), yet
  every neighbourhood of `0` contains the time `0` at which all of `U_T` maximizes.
* Reading the conclusion off `t₀`, or almost everywhere, does not save it: along the abnormal
  costate of the edge `{u₀ = 0}` (the conormal family containing Remark 8.1.6's) with
  `Λ_R(t₀) = 0` (take `Λ₁(t₀) = [[1, -2x], [0, -1]]`, `X(t₀) = Φ(x + iy)`, `λ_cost = 0`), the
  control `e₂` on `(t₀ - ε, t₀)` and `e₁` on `(t₀, t₀ + ε)` gives an edge-extremal extremal off
  `𝒮_sing` whose maximizers are the edge `{e₂, e₃}` at every `t < t₀` and the vertex `e₁` at every
  `t > t₀` (checked numerically): no single edge contains them on any two-sided neighbourhood.

## The restatement (the user's decision)

Theorem 8.3.1 is formalized in the *one-sided maximizer form* (`theorem8_3_1`): under the book's
hypotheses there are `ε > 0` and edges `k₋`, `k₊` (`kₗ`, `kᵣ` in Lean) such that the maximizers
lie in the edge `k₋` at every time of `(t₀ - ε, t₀) ∩ [a, b]` and in the edge `k₊` at every time
of `(t₀, t₀ + ε) ∩ [a, b]`. The time `t₀` itself is excluded, and the two edges may differ; both
counterexamples satisfy this form (the first with the vertices `e_b` before and `e_a` after `0`,
the second with the edge `{e₂, e₃}` before and the vertex `e₁` after `t₀`). This is the
inventory's repair of G2 ("restate it with one-sided neighbourhoods; Thm 8.3.2 survives"). The
book's hypotheses are kept, edge extremality included (the binder `_hedge`), although the proof
of the maximizer form does not use it (the book uses it, through Theorem 8.1.4, only to pass to
the control).

The control form that the proof of Theorem 8.3.2 quotes is two-sided and true: on each side of
`t₀` the control lies in one edge almost everywhere (maximum condition), so by edge extremality
and Theorem 8.1.4 it is eventually constant at a vertex, and any two vertices lie in a common
edge. It is the corollary `IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn`.

## The proofs

The proof of Theorem 8.3.1 is the book's (claims (a), (b), (c), with the Gronwall–Bellman
inequality (8.3.1), Corollary A.1.3 two-sided and Lemma 8.2.1), run directly on each side of `t₀`
instead of in the contrapositive; claim (b), a sketch in the book (gap G3), is carried out as a
second-order expansion of `Λ_R`. The step of claim (a) that passes to the control through
Theorem 8.1.4 is not needed for the maximizer form and is the corollary's (a departure forced by
the restatement). The estimates use the entrywise `ℓ¹` norm on `2 × 2` matrices (`l3hN`; the book
uses the Euclidean norm on `𝔰𝔩₂(ℝ)`, any norm does). The private helpers are prefixed `l3h_`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix


/-! ### Helpers: an entrywise norm on `2 × 2` matrices

The estimates of the proof of Theorem 8.3.1 use a norm on `𝔰𝔩₂(ℝ)` (the book's Euclidean norm;
any norm does). The entrywise `ℓ¹` norm is used here: it is submultiplicative, and the curves of
the state–costate system are given entry by entry. -/

/-- The entrywise `ℓ¹` norm `|a| + |b| + |c| + |d|` of a `2 × 2` matrix. -/
private noncomputable def l3hN (M : Mat2) : ℝ := |M 0 0| + |M 0 1| + |M 1 0| + |M 1 1|

private lemma l3hN_nonneg (M : Mat2) : 0 ≤ l3hN M := by unfold l3hN; positivity

private lemma l3h_abs_le_N (M : Mat2) (i j : Fin 2) : |M i j| ≤ l3hN M := by
  have := abs_nonneg (M 0 0); have := abs_nonneg (M 0 1); have := abs_nonneg (M 1 0)
  have := abs_nonneg (M 1 1)
  unfold l3hN
  fin_cases i <;> fin_cases j <;> simp <;> linarith

private lemma l3hN_add (A B : Mat2) : l3hN (A + B) ≤ l3hN A + l3hN B := by
  simp only [l3hN, Matrix.add_apply]
  linarith [abs_add_le (A 0 0) (B 0 0), abs_add_le (A 0 1) (B 0 1), abs_add_le (A 1 0) (B 1 0),
    abs_add_le (A 1 1) (B 1 1)]

private lemma l3hN_sub (A B : Mat2) : l3hN (A - B) ≤ l3hN A + l3hN B := by
  simp only [l3hN, Matrix.sub_apply]
  linarith [abs_sub (A 0 0) (B 0 0), abs_sub (A 0 1) (B 0 1), abs_sub (A 1 0) (B 1 0),
    abs_sub (A 1 1) (B 1 1)]

private lemma l3hN_smul (c : ℝ) (A : Mat2) : l3hN (c • A) = |c| * l3hN A := by
  simp only [l3hN, Matrix.smul_apply, smul_eq_mul, abs_mul]; ring

private lemma l3hN_mul (A B : Mat2) : l3hN (A * B) ≤ l3hN A * l3hN B := by
  have h : ∀ a b c d : ℝ, |a * b + c * d| ≤ |a| * |b| + |c| * |d| := fun a b c d ↦
    (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
  simp only [l3hN, Matrix.mul_apply, Fin.sum_univ_two]
  have p : ∀ x y : ℝ, 0 ≤ |x| * |y| := fun x y ↦ mul_nonneg (abs_nonneg x) (abs_nonneg y)
  nlinarith [h (A 0 0) (B 0 0) (A 0 1) (B 1 0), h (A 0 0) (B 0 1) (A 0 1) (B 1 1),
    h (A 1 0) (B 0 0) (A 1 1) (B 1 0), h (A 1 0) (B 0 1) (A 1 1) (B 1 1),
    p (A 0 0) (B 1 0), p (A 0 0) (B 1 1), p (A 0 1) (B 0 0), p (A 0 1) (B 0 1),
    p (A 1 0) (B 1 0), p (A 1 0) (B 1 1), p (A 1 1) (B 0 0), p (A 1 1) (B 0 1)]

private lemma l3h_abs_traceForm_le (A B : Mat2) : |traceForm A B| ≤ l3hN A * l3hN B := by
  refine le_trans ?_ (l3hN_mul A B)
  rw [traceForm, Matrix.trace_fin_two]
  have := abs_nonneg ((A * B) 0 1); have := abs_nonneg ((A * B) 1 0)
  unfold l3hN
  linarith [abs_add_le ((A * B) 0 0) ((A * B) 1 1)]

private lemma l3hN_bracket (A B : Mat2) : l3hN (A * B - B * A) ≤ 2 * (l3hN A * l3hN B) := by
  have h1 := l3hN_sub (A * B) (B * A); have h2 := l3hN_mul A B; have h3 := l3hN_mul B A
  nlinarith

private lemma l3h_continuousOn_N {f : ℝ → Mat2} {s : Set ℝ} (hf : ContinuousOn f s) :
    ContinuousOn (fun t ↦ l3hN (f t)) s := by
  have h := Matrix.continuousOn_iff_entrywise.1 hf
  exact (((h 0 0).abs.add (h 0 1).abs).add (h 1 0).abs).add (h 1 1).abs

/-- Convergence of matrices is entrywise. -/
private lemma l3h_tendsto_iff {α : Type*} {l : Filter α} {f : α → Mat2} {M : Mat2} :
    Tendsto f l (𝓝 M) ↔ ∀ i j, Tendsto (fun t ↦ f t i j) l (𝓝 (M i j)) :=
  tendsto_pi_nhds.trans <| forall_congr' fun _ ↦ tendsto_pi_nhds

/-! ### Helpers: the control simplex and its faces -/

/-- The denominators `⟨X, Z_u⟩` of the Hamiltonian do not vanish at a star state
(Lemma 3.3.4). -/
private lemma l3h_den_ne {X : Mat2} (hX : IsStarState X) :
    ∀ u ∈ controlSimplex, traceForm X (controlMatrix u) ≠ 0 := fun u hu ↦ by
  rw [poly_traceForm_comm]; exact (poly_traceForm_neg hu hX).ne

/-- **The maximizers lie in an edge as soon as a vertex does not maximize.** The set of
maximizers is a face of `U_T` (Lemma 7.3.1); a control `u` of that face with `u_j > 0` lies in an
open segment from `e_j` to a point of `U_T`, so `e_j` would be a maximizer. -/
private lemma l3h_argmax_subset_controlEdge {lam : ℝ} {Λ₁ ΛR X : Mat2}
    (hden : ∀ u ∈ controlSimplex, traceForm X (controlMatrix u) ≠ 0) {j : Fin 3}
    (hj : vertex j ∉ hamiltonianArgmax lam Λ₁ ΛR X) :
    hamiltonianArgmax lam Λ₁ ΛR X ⊆ controlEdge j := by
  intro u hu
  refine ⟨hu.1, ?_⟩
  obtain ⟨-, -, hext⟩ := lemma7_3_1 controlSimplex isCompact_controlSimplex
    convex_controlSimplex ⟨_, poly_vertex_mem 0⟩ lam Λ₁ ΛR X hden
  obtain ⟨hb, hs⟩ := hu.1
  by_contra hne
  have hpos : 0 < u j := lt_of_le_of_ne (hb j).1 (Ne.symm hne)
  -- the other two coordinates are at most `1 - u j`
  have hle : ∀ i, i ≠ j → u i ≤ 1 - u j := by
    intro i hij
    have := (hb 0).1; have := (hb 1).1; have := (hb 2).1
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
  rcases (hb j).2.lt_or_eq with hlt | heq
  · have h1 : 0 < 1 - u j := by linarith
    set w : Fin 3 → ℝ := (1 - u j)⁻¹ • (u - u j • vertex j) with hw
    have hwi : ∀ i, w i = (1 - u j)⁻¹ * (u i - u j * vertex j i) := fun i ↦ rfl
    have hwmem : w ∈ controlSimplex := by
      refine ⟨fun i ↦ ?_, ?_⟩
      · rw [hwi]
        by_cases hij : i = j
        · subst hij; simp [vertex]
        · simp only [vertex, Pi.single_apply, hij, ite_false, mul_zero, sub_zero]
          rw [inv_mul_eq_div]
          exact ⟨div_nonneg (hb i).1 h1.le, (div_le_one h1).2 (hle i hij)⟩
      · rw [hwi, hwi, hwi, ← mul_add, ← mul_add]
        have hv := (poly_vertex_mem j).2
        rw [show u 0 - u j * vertex j 0 + (u 1 - u j * vertex j 1) + (u 2 - u j * vertex j 2) =
          (u 0 + u 1 + u 2) - u j * (vertex j 0 + vertex j 1 + vertex j 2) by ring, hs, hv,
          mul_one]
        exact inv_mul_cancel₀ h1.ne'
    have hseg : u ∈ openSegment ℝ (vertex j) w := by
      refine ⟨u j, 1 - u j, hpos, h1, by ring, ?_⟩
      rw [hw, smul_inv_smul₀ h1.ne']
      abel
    exact hj (hext.left_mem_of_mem_openSegment (poly_vertex_mem j) hwmem hu hseg)
  · have hu' : u = vertex j := by
      funext i
      by_cases hij : i = j
      · subst hij; simp [vertex, heq]
      · have := hle i hij
        simp only [vertex, Pi.single_apply, hij, ite_false]
        linarith [(hb i).1]
    exact hj (hu' ▸ hu)

/-- **The leading term decides the face** (the step of the proof of Theorem 8.3.1 that reads the
maximizers off the leading term of `Λ_R`, TeX 7553–7557, and the step through "the continuity of
the Hamiltonian", TeX 7476–7480). Along a filter, let `X(t) → X₀` (star states) and
`Λ_R(t) = σ(t) Ṽ(t)` with `σ(t) > 0` and `Ṽ(t) → V`, where `0 ≠ V ∈ X₀^⊥` is traceless. By
Lemma 8.2.1 the maximizers of the Hamiltonian with `Λ_R = V` at `X₀` form a vertex or an edge, so
some vertex `e_j` is beaten by a control `v`; the control-dependent term `-σ(t)⟨Ṽ, Z_u⟩/⟨X, Z_u⟩`
then keeps `e_j` below `v` eventually, and the maximizers at time `t` lie in the edge
`{u_j = 0}` (`l3h_argmax_subset_controlEdge`). -/
private lemma l3h_eventually_argmax_subset {α : Type*} {l : Filter α} {lam : ℝ}
    {Λ₁f ΛRf Xf : α → Mat2} {σ : α → ℝ} {X₀ V : Mat2} (hX₀ : IsStarState X₀)
    (hXf : ∀ᶠ t in l, IsStarState (Xf t)) (hX : Tendsto Xf l (𝓝 X₀))
    (hσ : ∀ᶠ t in l, 0 < σ t) (hL : Tendsto (fun t ↦ (σ t)⁻¹ • ΛRf t) l (𝓝 V))
    (hV : V ≠ 0) (hVtr : V.trace = 0) (hVX : traceForm V X₀ = 0) :
    ∃ k : Fin 3, ∀ᶠ t in l, hamiltonianArgmax lam (Λ₁f t) (ΛRf t) (Xf t) ⊆ controlEdge k := by
  -- Lemma 8.2.1 at the limit: some vertex `e_j` does not maximize
  obtain ⟨j, hj⟩ : ∃ j, vertex j ∉ hamiltonianArgmax lam 0 V X₀ := by
    rcases (lemma8_2_1 hX₀.1 (l3h_den_ne hX₀) hVtr hVX).2 hV lam 0 with ⟨i, hi⟩ | ⟨k, hk⟩
    · refine ⟨i + 1, fun h ↦ ?_⟩
      rw [hi, mem_singleton_iff] at h
      have := congr_fun h (i + 1)
      fin_cases i <;> simp [vertex] at this
    · refine ⟨k, fun h ↦ ?_⟩
      rw [hk] at h
      have := h.2
      fin_cases k <;> simp [vertex] at this
  obtain ⟨v, hv, hlt⟩ : ∃ v ∈ controlSimplex,
      hamiltonian lam 0 V X₀ (vertex j) < hamiltonian lam 0 V X₀ v := by
    by_contra hcon
    exact hj ⟨poly_vertex_mem j, fun v hv ↦ not_lt.1 fun h ↦ hcon ⟨v, hv, h⟩⟩
  -- the ratios `⟨Ṽ, Z_w⟩/⟨X, Z_w⟩` converge
  have hr : ∀ w ∈ controlSimplex, Tendsto (fun t ↦ traceForm ((σ t)⁻¹ • ΛRf t) (controlMatrix w) /
      traceForm (Xf t) (controlMatrix w)) l
      (𝓝 (traceForm V (controlMatrix w) / traceForm X₀ (controlMatrix w))) := by
    intro w hw
    have hc : ∀ Z : Mat2, Continuous fun M : Mat2 ↦ traceForm M Z := fun Z ↦
      (continuous_id.matrix_mul continuous_const).matrix_trace
    exact (((hc _).tendsto _).comp hL).div (((hc _).tendsto _).comp hX) (l3h_den_ne hX₀ w hw)
  have hlt' : traceForm V (controlMatrix v) / traceForm X₀ (controlMatrix v) <
      traceForm V (controlMatrix (vertex j)) / traceForm X₀ (controlMatrix (vertex j)) := by
    simp only [hamiltonian] at hlt
    linarith
  refine ⟨j, ?_⟩
  filter_upwards [(hr v hv).eventually_lt (hr _ (poly_vertex_mem j)) hlt', hσ, hXf] with
    t ht hσt hXt
  refine l3h_argmax_subset_controlEdge (l3h_den_ne hXt) fun hjt ↦ ?_
  have hmax := hjt.2 v hv
  simp only [hamiltonian] at hmax
  simp only [traceForm_smul_left, mul_div_assoc] at ht
  have := (mul_lt_mul_iff_of_pos_left (inv_pos.2 hσt)).1 ht
  linarith

/-! ### Helpers: integrals and the Gronwall–Bellman step -/

/-- `|∫ₐᵇ f| ≤ |∫ₐᵇ g|` when `|f| ≤ g` between `a` and `b`. -/
private lemma l3h_abs_integral_le {f g : ℝ → ℝ} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    (h : ∀ s ∈ uIcc a b, |f s| ≤ g s) : |∫ s in a..b, f s| ≤ |∫ s in a..b, g s| := by
  rcases le_total a b with hab | hba
  · have h1 := intervalIntegral.norm_integral_le_of_norm_le (f := f) hab
      (Eventually.of_forall fun s hs ↦ by
        rw [Real.norm_eq_abs]
        exact h s (Ioc_subset_Icc_self.trans (uIcc_of_le hab).symm.subset hs))
      hg
    exact h1.trans (le_abs_self _)
  · have h1 := intervalIntegral.norm_integral_le_of_norm_le (f := f) hba
      (Eventually.of_forall fun s hs ↦ by
        rw [Real.norm_eq_abs]
        exact h s (Ioc_subset_Icc_self.trans (uIcc_of_ge hba).symm.subset hs))
      hg.symm
    rw [intervalIntegral.integral_symm b a, intervalIntegral.integral_symm b a (f := g), abs_neg,
      abs_neg]
    exact h1.trans (le_abs_self _)

/-- For a nonnegative continuous `f`, `|∫ₐᵇ f| ≤ |∫ₐᶜ f|` when `b` lies between `a` and `c`. -/
private lemma l3h_abs_integral_mono {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ r, 0 ≤ f r)
    {a b c : ℝ} (hb : b ∈ uIcc a c) : |∫ s in a..b, f s| ≤ |∫ s in a..c, f s| := by
  rcases le_total a c with hac | hca
  · rw [uIcc_of_le hac] at hb
    have h1 : 0 ≤ ∫ s in a..b, f s := intervalIntegral.integral_nonneg hb.1 fun r _ ↦ hf0 r
    have h2 : ∫ s in a..b, f s ≤ ∫ s in a..c, f s := intervalIntegral.integral_mono_interval
      le_rfl hb.1 hb.2 (ae_of_all _ fun r ↦ hf0 r) (hf.intervalIntegrable _ _)
    rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
    exact h2
  · rw [uIcc_of_ge hca] at hb
    rw [intervalIntegral.integral_symm b a, intervalIntegral.integral_symm c a, abs_neg, abs_neg]
    have h1 : 0 ≤ ∫ s in b..a, f s := intervalIntegral.integral_nonneg hb.2 fun r _ ↦ hf0 r
    have h2 : ∫ s in b..a, f s ≤ ∫ s in c..a, f s := intervalIntegral.integral_mono_interval
      hb.1 hb.2 le_rfl (ae_of_all _ fun r ↦ hf0 r) (hf.intervalIntegrable _ _)
    rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
    exact h2

/-- **The Gronwall–Bellman step** (the inequality (8.3.1), `eqn:Lambda-bellman`, and its
consequence by Corollary A.1.3, TeX 7518–7545). On `[0, T] ∋ t₀`, let `x, y ≥ 0` be continuous
with `y(t) ≤ C |t - t₀|ⁿ` and `x(t) ≤ C₁ |∫_{t₀}^t (x + y)|`. Then `x(t) = O(|t - t₀|ⁿ⁺¹)` as
`t → t₀` in `[0, T]`.

Proof: `|∫_{t₀}^t y| ≤ C |t - t₀|ⁿ⁺¹`, so `x(t) ≤ C₁ C |t - t₀|ⁿ⁺¹ + C₁ |∫_{t₀}^t x|`;
Corollary A.1.3, two-sided (`corollaryA_1_3_two_sided`), applies to `τ ↦ x(t₀ + τ)`
extended past the ends of `[0, T]` by its values at the ends (the clamped extension keeps the
integral inequality, as its right-hand side only grows when `|τ|` does); this covers `t₀ = 0` and
`t₀ = T`. -/
private lemma l3h_gronwall {T t₀ C C₁ : ℝ} {n : ℕ} {x y : ℝ → ℝ} (hT : 0 ≤ T)
    (ht₀ : t₀ ∈ Icc 0 T) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hx0 : ∀ t ∈ Icc 0 T, 0 ≤ x t) (hy0 : ∀ t ∈ Icc 0 T, 0 ≤ y t)
    (hyC : ∀ t ∈ Icc 0 T, y t ≤ C * |t - t₀| ^ n)
    (h : ∀ t ∈ Icc 0 T, x t ≤ C₁ * |∫ s in t₀..t, (x s + y s)|) :
    x =O[𝓝[Icc 0 T] t₀] fun t ↦ |t - t₀| ^ (n + 1) := by
  -- the inequality with `∫ y` estimated
  have h' : ∀ t ∈ Icc 0 T, x t ≤ C₁ * C * |t - t₀| ^ (n + 1) + C₁ * |∫ s in t₀..t, x s| := by
    intro t ht
    have hsub : uIcc t₀ t ⊆ Icc 0 T := uIcc_subset_Icc ht₀ ht
    have hyI : |∫ s in t₀..t, y s| ≤ C * |t - t₀| ^ n * |t - t₀| := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t₀) (b := t) (f := y)
        (C := C * |t - t₀| ^ n) fun s hs ↦ by
          have hs' : s ∈ Icc 0 T := hsub (uIoc_subset_uIcc hs)
          rw [Real.norm_eq_abs, abs_of_nonneg (hy0 s hs')]
          refine (hyC s hs').trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _)
            (abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hs)) n) hC)
      simpa only [Real.norm_eq_abs] using this
    have hsplit : ∫ s in t₀..t, (x s + y s) = (∫ s in t₀..t, x s) + ∫ s in t₀..t, y s :=
      intervalIntegral.integral_add (hx.mono hsub).intervalIntegrable
        (hy.mono hsub).intervalIntegrable
    calc x t ≤ C₁ * |∫ s in t₀..t, (x s + y s)| := h t ht
      _ ≤ C₁ * (|∫ s in t₀..t, x s| + C * |t - t₀| ^ n * |t - t₀|) := by
          rw [hsplit]
          gcongr
          exact (abs_add_le _ _).trans (by gcongr)
      _ = C₁ * C * |t - t₀| ^ (n + 1) + C₁ * |∫ s in t₀..t, x s| := by ring
  -- the clamp to `[0, T]` and the extended function
  set cl : ℝ → ℝ := fun r ↦ max 0 (min T r) with hcl
  have hclm : ∀ r, cl r ∈ Icc 0 T := fun r ↦ ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩
  have hclid : ∀ r ∈ Icc 0 T, cl r = r := fun r hr ↦ by
    simp only [hcl, min_eq_right hr.2, max_eq_right hr.1]
  have hclc : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  set xt : ℝ → ℝ := fun r ↦ x (cl r) with hxt
  have hxtc : Continuous xt := hx.comp_continuous hclc hclm
  have hxt0 : ∀ r, 0 ≤ xt r := fun r ↦ hx0 _ (hclm r)
  have hξ : ∀ τ ∈ Icc (-1 : ℝ) 1, xt (t₀ + τ) ≤
      C₁ * C * |τ| ^ (n + 1) + C₁ * |∫ s in (0 : ℝ)..τ, xt (t₀ + s)| := by
    intro τ _
    have htm := hclm (t₀ + τ)
    -- the clamped point lies between `t₀` and `t₀ + τ`
    have hbetween : cl (t₀ + τ) ∈ uIcc t₀ (t₀ + τ) := by
      rcases le_total 0 τ with hτ | hτ
      · rw [uIcc_of_le (by linarith)]
        refine ⟨?_, ?_⟩
        · simp only [hcl]; exact le_max_of_le_right (le_min ht₀.2 (by linarith))
        · simp only [hcl]; exact max_le (by linarith [ht₀.1]) (min_le_right _ _)
      · rw [uIcc_of_ge (by linarith)]
        refine ⟨?_, ?_⟩
        · simp only [hcl]; exact le_max_of_le_right (le_min (by linarith [ht₀.2]) le_rfl)
        · simp only [hcl]; exact max_le ht₀.1 ((min_le_right _ _).trans (by linarith))
    have hdist : |cl (t₀ + τ) - t₀| ≤ |τ| := by
      simpa using abs_sub_left_of_mem_uIcc hbetween
    have hI1 : ∫ s in t₀..cl (t₀ + τ), x s = ∫ s in t₀..cl (t₀ + τ), xt s :=
      intervalIntegral.integral_congr fun s hs ↦ by
        simp only [hxt, hclid s (uIcc_subset_Icc ht₀ htm hs)]
    have hI3 : ∫ s in (0 : ℝ)..τ, xt (t₀ + s) = ∫ s in t₀..t₀ + τ, xt s := by
      rw [intervalIntegral.integral_comp_add_left, add_zero]
    calc xt (t₀ + τ) = x (cl (t₀ + τ)) := rfl
      _ ≤ C₁ * C * |cl (t₀ + τ) - t₀| ^ (n + 1) + C₁ * |∫ s in t₀..cl (t₀ + τ), x s| :=
          h' _ htm
      _ ≤ C₁ * C * |τ| ^ (n + 1) + C₁ * |∫ s in (0 : ℝ)..τ, xt (t₀ + s)| := by
          rw [hI1, hI3]
          exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hdist _)
            (mul_nonneg hC₁ hC))
            (mul_le_mul_of_nonneg_left (l3h_abs_integral_mono hxtc hxt0 hbetween) hC₁)
  have hO := corollaryA_1_3_two_sided (x := fun τ ↦ xt (t₀ + τ)) one_pos (Nat.succ_pos n)
    (hxtc.comp (continuous_const.add continuous_id)).continuousOn (fun τ _ ↦ hxt0 _)
    (mul_nonneg hC₁ hC) hC₁ hξ
  have htend : Tendsto (fun t ↦ t - t₀) (𝓝[Icc 0 T] t₀) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by
      simpa using (continuous_sub_right t₀).tendsto t₀)
  refine (hO.comp_tendsto htend).congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Function.comp, hxt, add_sub_cancel, hclid t ht]

/-- **The second-order expansion of an integral** (claim (b) of the proof of Theorem 8.3.1:
from `F(s) = (s - t₀) G + o(s - t₀)`, `∫_{t₀}^t F = (t - t₀)²/2 · G + o((t - t₀)²)`), entrywise:
if `f` is continuous on the interval `S ∋ t₀`, `f(t₀) = 0` and `f(s)/(s - t₀) → c`, then
`(∫_{t₀}^t f)/(t - t₀)² → c/2`. -/
private lemma l3h_tendsto_integral_div_sq {f : ℝ → ℝ} {S : Set ℝ} {t₀ c : ℝ} (hS : S.OrdConnected)
    (ht₀ : t₀ ∈ S) (hf : ContinuousOn f S) (hf0 : f t₀ = 0)
    (hd : Tendsto (fun s ↦ (s - t₀)⁻¹ * f s) (𝓝[S \ {t₀}] t₀) (𝓝 c)) :
    Tendsto (fun t ↦ ((t - t₀) ^ 2)⁻¹ * ∫ s in t₀..t, f s) (𝓝[S \ {t₀}] t₀) (𝓝 (c / 2)) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hd ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδb⟩ := hd (ε / 2) (half_pos hε)
  -- the first-order bound `|f s - (s - t₀) c| ≤ ε/2 |s - t₀|` near `t₀`
  have hb : ∀ s ∈ S, dist s t₀ < δ → |f s - (s - t₀) * c| ≤ ε / 2 * |s - t₀| := by
    intro s hs hsd
    by_cases hst : s = t₀
    · subst hst; simp [hf0]
    have h1 := hδb ⟨hs, hst⟩ hsd
    rw [Real.dist_eq] at h1
    have hne : s - t₀ ≠ 0 := sub_ne_zero.2 hst
    have he : f s - (s - t₀) * c = (s - t₀) * ((s - t₀)⁻¹ * f s - c) := by field_simp
    rw [he, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right h1.le (abs_nonneg _)
  refine ⟨δ, hδ, fun t ht htd ↦ ?_⟩
  have hne : t - t₀ ≠ 0 := sub_ne_zero.2 ht.2
  have hsub : uIcc t₀ t ⊆ S := hS.uIcc_subset ht₀ ht.1
  have hmain : ∫ s in t₀..t, f s = (∫ s in t₀..t, (f s - (s - t₀) * c)) + c * (t - t₀) ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub (hf.mono hsub).intervalIntegrable
      ((by fun_prop : Continuous fun s : ℝ ↦ (s - t₀) * c).intervalIntegrable _ _),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_comp_sub_right (fun s ↦ s),
      integral_id]
    ring
  have hbound : |∫ s in t₀..t, (f s - (s - t₀) * c)| ≤ ε / 2 * |t - t₀| * |t - t₀| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t₀) (b := t)
      (f := fun s ↦ f s - (s - t₀) * c) (C := ε / 2 * |t - t₀|) fun s hs ↦ by
        have hs' := uIoc_subset_uIcc hs
        have hd' := abs_sub_left_of_mem_uIcc hs'
        rw [Real.norm_eq_abs]
        refine (hb s (hsub hs') ?_).trans (by gcongr)
        rw [Real.dist_eq]
        exact hd'.trans_lt (by rwa [← Real.dist_eq])
    simpa only [Real.norm_eq_abs] using this
  have hsq : 0 < (t - t₀) ^ 2 := by positivity
  generalize ∫ s in t₀..t, (f s - (s - t₀) * c) = I at hbound hmain
  rw [Real.dist_eq, hmain]
  have he : ((t - t₀) ^ 2)⁻¹ * (I + c * (t - t₀) ^ 2 / 2) - c / 2 = ((t - t₀) ^ 2)⁻¹ * I := by
    field_simp
    ring
  rw [he, abs_mul, abs_inv, abs_of_pos hsq]
  calc ((t - t₀) ^ 2)⁻¹ * |I| ≤ ((t - t₀) ^ 2)⁻¹ * (ε / 2 * |t - t₀| * |t - t₀|) := by gcongr
    _ = ε / 2 := by
        rw [mul_assoc, ← sq, sq_abs]
        field_simp
    _ < ε := half_lt_self hε

/-! ### Helpers: bounds along an extremal -/

/-- `⟨Z_u, X⟩ = -(2/√3)(ρ₂(X) u₀ + ρ₁(X) u₁ + ρ₀(X) u₂)` for traceless `X` (from the proof of
Lemma 3.3.4). -/
private lemma l3h_traceForm_controlMatrix_eq (X : Mat2) (hX : X.trace = 0) (u : Fin 3 → ℝ) :
    traceForm (controlMatrix u) X = -(2 / √3) * (ρ₂ X * u 0 + ρ₁ X * u 1 + ρ₀ X * u 2) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  have hX11 : X 1 1 = -X 0 0 := by
    rw [Matrix.trace_fin_two] at hX; linear_combination hX
  rw [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  simp [controlMatrix, ρ₀, ρ₁, ρ₂, hX11]
  field_simp
  linear_combination (u 0 * X 1 0 + 3 * u 0 * X 0 1 - 2 * u 1 * X 1 0 - 2 * u 2 * X 1 0) * h3

/-- A positive continuous function on `[0, T]` is bounded below by a positive constant. -/
private lemma l3h_exists_pos_le {T : ℝ} {f : ℝ → ℝ} (hT : 0 ≤ T) (hf : ContinuousOn f (Icc 0 T))
    (hpos : ∀ t ∈ Icc 0 T, 0 < f t) : ∃ μ > 0, ∀ t ∈ Icc 0 T, μ ≤ f t := by
  obtain ⟨t₁, ht₁, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, left_mem_Icc.2 hT⟩ hf
  exact ⟨f t₁, hpos t₁ ht₁, fun t ht ↦ hmin ht⟩

/-- Along a continuous curve of star states on `[0, T]`, the denominators `⟨Z_u, X⟩` are bounded
away from `0` uniformly in `u ∈ U_T` (Lemma 3.3.4 and compactness). -/
private lemma l3h_den_bound {T : ℝ} {X : ℝ → Mat2} (hT : 0 ≤ T) (hXc : ContinuousOn X (Icc 0 T))
    (hXs : ∀ t ∈ Icc 0 T, IsStarState (X t)) :
    ∃ m > 0, ∀ t ∈ Icc 0 T, ∀ u ∈ controlSimplex, m ≤ -traceForm (controlMatrix u) (X t) := by
  have h := Matrix.continuousOn_iff_entrywise.1 hXc
  have hρ0 : ContinuousOn (fun t ↦ ρ₀ (X t)) (Icc 0 T) := by
    simp only [ρ₀]; exact ((h 1 0).add (continuousOn_const.mul (h 0 0))).div_const _
  have hρ1 : ContinuousOn (fun t ↦ ρ₁ (X t)) (Icc 0 T) := by
    simp only [ρ₁]; exact ((h 1 0).sub (continuousOn_const.mul (h 0 0))).div_const _
  have hρ2 : ContinuousOn (fun t ↦ ρ₂ (X t)) (Icc 0 T) := by
    simp only [ρ₂]; exact ((continuousOn_const.mul (h 0 1)).add (h 1 0)).neg.div_const _
  obtain ⟨μ₀, hμ₀, hb₀⟩ := l3h_exists_pos_le hT hρ0 fun t ht ↦ (hXs t ht).2.2.1
  obtain ⟨μ₁, hμ₁, hb₁⟩ := l3h_exists_pos_le hT hρ1 fun t ht ↦ (hXs t ht).2.2.2.1
  obtain ⟨μ₂, hμ₂, hb₂⟩ := l3h_exists_pos_le hT hρ2 fun t ht ↦ (hXs t ht).2.2.2.2
  set μ := min μ₀ (min μ₁ μ₂)
  have hμ : 0 < μ := lt_min hμ₀ (lt_min hμ₁ hμ₂)
  refine ⟨2 / √3 * μ, by positivity, fun t ht u hu ↦ ?_⟩
  have hm0 : μ ≤ ρ₀ (X t) := (min_le_left _ _).trans (hb₀ t ht)
  have hm1 : μ ≤ ρ₁ (X t) := ((min_le_right _ _).trans (min_le_left _ _)).trans (hb₁ t ht)
  have hm2 : μ ≤ ρ₂ (X t) := ((min_le_right _ _).trans (min_le_right _ _)).trans (hb₂ t ht)
  rw [l3h_traceForm_controlMatrix_eq (X t) (hXs t ht).1]
  obtain ⟨hb, hsum⟩ := hu
  have : μ ≤ ρ₂ (X t) * u 0 + ρ₁ (X t) * u 1 + ρ₀ (X t) * u 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hm2 (hb 0).1, mul_le_mul_of_nonneg_right hm1 (hb 1).1,
      mul_le_mul_of_nonneg_right hm0 (hb 2).1]
  have h23 : 0 < 2 / √3 := by positivity
  nlinarith

private lemma l3hN_controlMatrix_le {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) :
    l3hN (controlMatrix u) ≤ 4 := by
  obtain ⟨hb, hs⟩ := hu
  have h3 : 1 ≤ √3 := Real.one_le_sqrt.2 (by norm_num)
  have h3p : 0 < √3 := by positivity
  have b0 := hb 0; have b1 := hb 1; have b2 := hb 2
  have e1 : |(u 1 - u 2) / √3| ≤ 1 := by
    rw [abs_div, abs_of_pos h3p, div_le_one h3p]
    exact (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩).trans h3
  have e2 : |(u 2 - u 1) / √3| ≤ 1 := by
    rw [abs_div, abs_of_pos h3p, div_le_one h3p]
    exact (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩).trans h3
  have e3 : |(u 0 - 2 * u 1 - 2 * u 2) / 3| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have e4 : |u 0| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  simp only [l3hN, controlMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  linarith

private lemma l3hN_controlP_le {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) {X : Mat2} {m : ℝ}
    (hm : 0 < m) (hmX : m ≤ -traceForm (controlMatrix u) X) : l3hN (controlP u X) ≤ 4 / m := by
  unfold controlP
  rw [l3hN_smul, abs_inv, abs_of_neg (by linarith : traceForm (controlMatrix u) X < 0)]
  rw [inv_mul_le_iff₀ (by linarith)]
  have h4 : 4 ≤ -traceForm (controlMatrix u) X * (4 / m) := by
    rw [mul_div_assoc', le_div_iff₀ hm]; linarith
  linarith [l3hN_controlMatrix_le hu]

/-- The control-dependent part `A(Λ) = [P, Λ] - ⟨Λ, P⟩[P, X]` of the costate equation for `Λ_R`
is linear in `Λ` with `‖A(Λ)‖ ≤ ‖Λ‖ (2‖P‖ + 2‖P‖²‖X‖)`. -/
private lemma l3hN_A_le (P M Xm : Mat2) :
    l3hN ((P * M - M * P) - traceForm M P • (P * Xm - Xm * P)) ≤
      l3hN M * (2 * l3hN P + 2 * l3hN P ^ 2 * l3hN Xm) := by
  have h1 := l3hN_sub (P * M - M * P) (traceForm M P • (P * Xm - Xm * P))
  rw [l3hN_smul] at h1
  have h2 := l3hN_bracket P M
  have h3 := l3hN_bracket P Xm
  have h4 := l3h_abs_traceForm_le M P
  have h5 : |traceForm M P| * l3hN (P * Xm - Xm * P) ≤
      (l3hN M * l3hN P) * (2 * (l3hN P * l3hN Xm)) :=
    mul_le_mul h4 h3 (l3hN_nonneg _) (mul_nonneg (l3hN_nonneg _) (l3hN_nonneg _))
  nlinarith

/-- The difference of a curve given in integral form on `[0, T]`, between two times of `[0, T]`. -/
private lemma l3h_sub_eq_integral {f v : ℝ → Mat2} {T : ℝ} (h : IsIntegralCurve f v T)
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (i j : Fin 2) :
    f b i j - f a i j = ∫ s in a..b, v s i j := by
  have hI := (h i j).1
  rw [(h i j).2 b hb, (h i j).2 a ha, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left
      (hI.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hb)))
      (hI.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ha)))]

/-- FTC at `t₀`: `(∫_{t₀}^t f)/(t - t₀) → f(t₀)` within `[0, T]`. -/
private lemma l3h_tendsto_integral_div {f : ℝ → ℝ} {T t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T)
    (hf : ContinuousOn f (Icc 0 T)) :
    Tendsto (fun t ↦ (t - t₀)⁻¹ * ∫ s in t₀..t, f s) (𝓝[Icc 0 T \ {t₀}] t₀) (𝓝 (f t₀)) := by
  have : Fact (t₀ ∈ Icc 0 T) := ⟨ht₀⟩
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (a := t₀) (b := t₀)
    (s := Icc 0 T) (t := Icc 0 T) IntervalIntegrable.refl
    ⟨Icc 0 T, self_mem_nhdsWithin, hf.aestronglyMeasurable measurableSet_Icc⟩ (hf t₀ ht₀)
  rw [hasDerivWithinAt_iff_tendsto_slope] at hd
  refine hd.congr fun t ↦ ?_
  simp [slope_def_field, div_eq_inv_mul]

/-- The two continuity facts used along an extremal on `[0, T]`. -/
private lemma l3h_continuousOn {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsStateCostateSolution T u g X Λ₁ ΛR lam) :
    ContinuousOn X (Icc 0 T) ∧ ContinuousOn Λ₁ (Icc 0 T) ∧ ContinuousOn ΛR (Icc 0 T) :=
  ⟨Matrix.continuousOn_of_eq_add_integral h.1.2.2.2.2.2,
    Matrix.continuousOn_of_eq_add_integral h.2.2.2.1,
    Matrix.continuousOn_of_eq_add_integral h.2.2.2.2.1⟩

/-- **The Hamiltonian vanishes at a zero of `Λ_R`** (TeX 7527–7529: "`Λ_{1,cost}(0) ∈ X(0)^⊥` by
the vanishing of the Hamiltonian at `t = 0`"). The Hamiltonian vanishes almost everywhere; at a
zero of `Λ_R` its control-independent part `⟨Λ_{1,cost}, X⟩` is continuous and its
control-dependent part `-⟨Λ_R, Z_u⟩/⟨X, Z_u⟩` is bounded by a multiple of `‖Λ_R‖ → 0`. -/
private lemma l3h_hamiltonian_zero {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (h : IsStateCostateSolution T u g X Λ₁ ΛR lam) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T)
    (hR : ΛR t₀ = 0) : traceForm (Λ₁ t₀ - (3 / 2 * lam) • J) (X t₀) = 0 := by
  obtain ⟨hXc, hΛ₁c, hΛRc⟩ := l3h_continuousOn h
  have hT := h.1.1
  have hXs : ∀ t ∈ Icc 0 T, IsStarState (X t) := fun t ht ↦ (h.1.2.2.2.1 t ht).2
  obtain ⟨m, hm, hmb⟩ := l3h_den_bound hT.le hXc hXs
  set c : ℝ → ℝ := fun t ↦ traceForm (Λ₁ t - (3 / 2 * lam) • J) (X t) with hcdef
  have hcc : ContinuousOn c (Icc 0 T) := by
    have hK : ContinuousOn (fun t ↦ Λ₁ t - (3 / 2 * lam) • J) (Icc 0 T) :=
      hΛ₁c.sub continuousOn_const
    have hM : ContinuousOn (fun t ↦ (Λ₁ t - (3 / 2 * lam) • J) * X t) (Icc 0 T) := hK.mul hXc
    have hM' := Matrix.continuousOn_iff_entrywise.1 hM
    simp only [hcdef, traceForm, Matrix.trace_fin_two]
    exact (hM' 0 0).add (hM' 1 1)
  by_contra hne
  have hε : 0 < |c t₀| / 2 := by positivity
  have h1 : ∀ᶠ t in 𝓝[Icc 0 T] t₀, |c t - c t₀| < |c t₀| / 2 := by
    have := (hcc t₀ ht₀).tendsto
    rw [Metric.tendsto_nhds] at this
    filter_upwards [this _ hε] with t ht
    rwa [Real.dist_eq] at ht
  have h2 : ∀ᶠ t in 𝓝[Icc 0 T] t₀, 4 / m * l3hN (ΛR t) < |c t₀| / 2 := by
    have hN := (l3h_continuousOn_N hΛRc t₀ ht₀).tendsto
    have h0 : l3hN (ΛR t₀) = 0 := by simp [hR, l3hN]
    rw [h0] at hN
    have := (hN.const_mul (4 / m))
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hε)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 (h1.and h2)
  -- a time of `(0, T) ∩ (t₀ - δ, t₀ + δ)` at which the Hamiltonian vanishes
  have hlt : max 0 (t₀ - δ) < min T (t₀ + δ) :=
    max_lt (lt_min hT (by linarith [ht₀.1])) (lt_min (by linarith [ht₀.2]) (by linarith))
  have hpos : volume (Ioo (max 0 (t₀ - δ)) (min T (t₀ + δ))) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.2 (sub_pos.2 hlt)).ne'
  have hae := h.2.2.2.2.2
  obtain ⟨t, htI, ht⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    ((ae_restrict_iff' measurableSet_Ioo).2 (hae.mono fun t ht htI ↦ ht
      ⟨(le_max_left _ _).trans_lt htI.1, htI.2.trans_le (min_le_left _ _)⟩))
  have htT : t ∈ Icc 0 T :=
    ⟨((le_max_left _ _).trans_lt htI.1).le, (htI.2.trans_le (min_le_left _ _)).le⟩
  have htd : t ∈ Metric.ball t₀ δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [(le_max_right 0 (t₀ - δ)).trans_lt htI.1]
    · linarith [htI.2.trans_le (min_le_right T (t₀ + δ))]
  obtain ⟨hc1, hc2⟩ := hδs ⟨htd, htT⟩
  -- at `t`: `c t = ⟨Λ_R, Z_u⟩/⟨X, Z_u⟩`, which is small
  have huS := h.1.2.2.1 t htT
  have hHt : c t = traceForm (ΛR t) (controlMatrix (u t)) / traceForm (X t) (controlMatrix (u t)) :=
    by have := ht.1; simp only [hamiltonian] at this; simp only [hcdef]; linarith
  have hden := hmb t htT (u t) huS
  have hratio : |c t| ≤ 4 / m * l3hN (ΛR t) := by
    rw [hHt, abs_div, poly_traceForm_comm (X t)]
    have hd : m ≤ |traceForm (controlMatrix (u t)) (X t)| := hden.trans (neg_le_abs _)
    rw [div_le_iff₀ (hm.trans_le hd)]
    have hn := l3h_abs_traceForm_le (ΛR t) (controlMatrix (u t))
    have hZ := l3hN_controlMatrix_le huS
    have hNn := l3hN_nonneg (ΛR t)
    calc |traceForm (ΛR t) (controlMatrix (u t))| ≤ l3hN (ΛR t) * 4 :=
          hn.trans (mul_le_mul_of_nonneg_left hZ hNn)
      _ = 4 / m * l3hN (ΛR t) * m := by field_simp
      _ ≤ 4 / m * l3hN (ΛR t) * |traceForm (controlMatrix (u t)) (X t)| := by gcongr
  have := abs_sub_abs_le_abs_sub (c t₀) (c t)
  rw [abs_sub_comm] at this
  linarith

/-! ### The decomposition `Λ_R = Y + Λ` and the Gronwall estimate -/

/-- The control-independent part `[-Λ_{1,cost}, X] = [-Λ₁ + (3/2) λ_cost J, X]` of the right-hand
side of the costate equation for `Λ_R`. -/
private noncomputable def l3hF (lam : ℝ) (Λ₁ X : ℝ → Mat2) (s : ℝ) : Mat2 :=
  (-Λ₁ s + (3 / 2 * lam) • J) * X s - X s * (-Λ₁ s + (3 / 2 * lam) • J)

/-- `Y(t) = ∫_{t₀}^t [-Λ_{1,cost}, X]` (the book's `Y(t) = -∫₀ᵗ [Λ_{1,cost}, X]`, TeX 7487). -/
private noncomputable def l3hY (lam : ℝ) (Λ₁ X : ℝ → Mat2) (t₀ t : ℝ) : Mat2 :=
  Matrix.of fun i j ↦ ∫ s in t₀..t, l3hF lam Λ₁ X s i j

private lemma l3hF_continuousOn {T lam : ℝ} {Λ₁ X : ℝ → Mat2} (hΛ₁c : ContinuousOn Λ₁ (Icc 0 T))
    (hXc : ContinuousOn X (Icc 0 T)) : ContinuousOn (l3hF lam Λ₁ X) (Icc 0 T) := by
  have hK : ContinuousOn (fun s ↦ -Λ₁ s + (3 / 2 * lam) • J) (Icc 0 T) :=
    hΛ₁c.neg.add continuousOn_const
  exact (hK.mul hXc).sub (hXc.mul hK)

/-- **The estimate (8.3.1) and its consequence** (TeX 7487–7545). Along an extremal on `[0, T]`
with `Λ_R(t₀) = 0`, write `Λ_R = Y + Λ`. Then `Λ' = A(Λ, t) + A(Y, t)` with `A` the
control-dependent part of the costate equation, bounded on `[0, T]`, so
`‖Λ‖ ≤ C₀ |∫_{t₀}^t (‖Λ‖ + ‖Y‖)|` (8.3.1), and `‖Y‖ = O(|t - t₀|ⁿ)` gives
`‖Λ‖ = O(|t - t₀|ⁿ⁺¹)` (Gronwall, Corollary A.1.3; `l3h_gronwall`). So `Λ_R/(t - t₀)ⁿ` has the
limit of `Y/(t - t₀)ⁿ`. -/
private lemma l3h_expansion {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsStateCostateSolution T u g X Λ₁ ΛR lam) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T)
    (hR : ΛR t₀ = 0) {n : ℕ} {C : ℝ} (hC : 0 ≤ C) {V : Mat2}
    (hY : ∀ t ∈ Icc 0 T, l3hN (l3hY lam Λ₁ X t₀ t) ≤ C * |t - t₀| ^ n)
    (hYV : Tendsto (fun t ↦ ((t - t₀) ^ n)⁻¹ • l3hY lam Λ₁ X t₀ t) (𝓝[Icc 0 T \ {t₀}] t₀)
      (𝓝 V)) :
    Tendsto (fun t ↦ ((t - t₀) ^ n)⁻¹ • ΛR t) (𝓝[Icc 0 T \ {t₀}] t₀) (𝓝 V) := by
  obtain ⟨hXc, hΛ₁c, hΛRc⟩ := l3h_continuousOn h
  have hT := h.1.1
  have hXs : ∀ t ∈ Icc 0 T, IsStarState (X t) := fun t ht ↦ (h.1.2.2.2.1 t ht).2
  have huS : ∀ t ∈ Icc 0 T, u t ∈ controlSimplex := h.1.2.2.1
  obtain ⟨m, hm, hmb⟩ := l3h_den_bound hT.le hXc hXs
  obtain ⟨CX, hCX⟩ := isCompact_Icc.exists_bound_of_continuousOn (l3h_continuousOn_N hXc)
  have hCX' : ∀ t ∈ Icc 0 T, l3hN (X t) ≤ CX := fun t ht ↦ (le_abs_self _).trans (hCX t ht)
  have hCX0 : 0 ≤ CX := (l3hN_nonneg _).trans (hCX' 0 ⟨le_rfl, hT.le⟩)
  set C₀ := 2 * (4 / m) + 2 * (4 / m) ^ 2 * CX with hC₀def
  have hC₀ : 0 ≤ C₀ := by positivity
  -- the control-dependent part `A` of the right-hand side, bounded on `[0, T]`
  set A : ℝ → Mat2 := fun s ↦ (controlP (u s) (X s) * ΛR s - ΛR s * controlP (u s) (X s)) -
    traceForm (ΛR s) (controlP (u s) (X s)) •
      (controlP (u s) (X s) * X s - X s * controlP (u s) (X s)) with hAdef
  have hA : ∀ s ∈ Icc 0 T, l3hN (A s) ≤ C₀ * l3hN (ΛR s) := by
    intro s hs
    have hP := l3hN_controlP_le (huS s hs) hm (hmb s hs (u s) (huS s hs))
    have hPn := l3hN_nonneg (controlP (u s) (X s))
    calc l3hN (A s) ≤ l3hN (ΛR s) * (2 * l3hN (controlP (u s) (X s)) +
          2 * l3hN (controlP (u s) (X s)) ^ 2 * l3hN (X s)) := l3hN_A_le _ _ _
      _ ≤ l3hN (ΛR s) * C₀ := by
          refine mul_le_mul_of_nonneg_left ?_ (l3hN_nonneg _)
          rw [hC₀def]
          have := mul_le_mul (pow_le_pow_left₀ hPn hP 2) (hCX' s hs) (l3hN_nonneg _)
            (by positivity)
          linarith
      _ = C₀ * l3hN (ΛR s) := mul_comm _ _
  -- `Y` is continuous, and `Λ_R(t) = ∫_{t₀}^t (A + F)`
  have hFc := l3hF_continuousOn (lam := lam) hΛ₁c hXc
  have hFij : ∀ i j, ContinuousOn (fun s ↦ l3hF lam Λ₁ X s i j) (Icc 0 T) :=
    Matrix.continuousOn_iff_entrywise.1 hFc
  have hYc : ContinuousOn (l3hY lam Λ₁ X t₀) (Icc 0 T) := by
    refine Matrix.continuousOn_iff_entrywise.2 fun i j ↦ ?_
    have := intervalIntegral.continuousOn_primitive_interval' (μ := volume)
      ((hFij i j).intervalIntegrable_of_Icc hT.le) (by rw [uIcc_of_le hT.le]; exact ht₀)
    rw [uIcc_of_le hT.le] at this
    exact this
  have hAint : ∀ i j, IntervalIntegrable (fun s ↦ A s i j) volume 0 T := by
    intro i j
    have h1 := (h.2.2.2.2.1 i j).1
    have h2 := (hFij i j).intervalIntegrable_of_Icc (μ := volume) hT.le
    have e : (fun s ↦ A s i j) = fun s ↦
        ((controlP (u s) (X s) * ΛR s - ΛR s * controlP (u s) (X s)) -
        traceForm (ΛR s) (controlP (u s) (X s)) •
          (controlP (u s) (X s) * X s - X s * controlP (u s) (X s)) +
        ((-Λ₁ s + (3 / 2 * lam) • J) * X s - X s * (-Λ₁ s + (3 / 2 * lam) • J))) i j -
        l3hF lam Λ₁ X s i j := by
      funext s
      simp only [hAdef, l3hF, Matrix.add_apply, add_sub_cancel_right]
    rw [e]
    exact h1.sub h2
  -- `Λ = Λ_R - Y` is the integral of `A`
  set Λ : ℝ → Mat2 := fun t ↦ ΛR t - l3hY lam Λ₁ X t₀ t with hΛdef
  have hΛint : ∀ t ∈ Icc 0 T, ∀ i j, Λ t i j = ∫ s in t₀..t, A s i j := by
    intro t ht i j
    have hsub : uIcc t₀ t ⊆ Icc 0 T := uIcc_subset_Icc ht₀ ht
    have hsub' : uIcc t₀ t ⊆ uIcc 0 T := by rw [uIcc_of_le hT.le]; exact hsub
    have e := l3h_sub_eq_integral h.2.2.2.2.1 ht₀ ht i j
    rw [hR, Matrix.zero_apply, sub_zero] at e
    have e' : ΛR t i j = ∫ s in t₀..t, (A s i j + l3hF lam Λ₁ X s i j) := e
    simp only [hΛdef, Matrix.sub_apply, l3hY, Matrix.of_apply, e']
    rw [intervalIntegral.integral_add ((hAint i j).mono_set hsub')
      ((hFij i j).mono hsub).intervalIntegrable, add_sub_cancel_right]
  have hΛc : ContinuousOn Λ (Icc 0 T) := hΛRc.sub hYc
  -- the Gronwall–Bellman inequality (8.3.1)
  have hx : ∀ t ∈ Icc 0 T, l3hN (Λ t) ≤
      4 * C₀ * |∫ s in t₀..t, (l3hN (Λ s) + l3hN (l3hY lam Λ₁ X t₀ s))| := by
    intro t ht
    have hsub : uIcc t₀ t ⊆ Icc 0 T := uIcc_subset_Icc ht₀ ht
    have hgi : IntervalIntegrable (fun s ↦ C₀ * (l3hN (Λ s) + l3hN (l3hY lam Λ₁ X t₀ s)))
        volume t₀ t :=
      ((continuousOn_const.mul ((l3h_continuousOn_N hΛc).add (l3h_continuousOn_N hYc))).mono
        hsub).intervalIntegrable
    have hentry : ∀ i j, |Λ t i j| ≤
        C₀ * |∫ s in t₀..t, (l3hN (Λ s) + l3hN (l3hY lam Λ₁ X t₀ s))| := by
      intro i j
      rw [hΛint t ht i j]
      refine (l3h_abs_integral_le hgi fun s hs ↦ ?_).trans ?_
      · have hs' := hsub hs
        have hΛR : ΛR s = Λ s + l3hY lam Λ₁ X t₀ s := by simp [hΛdef]
        calc |A s i j| ≤ l3hN (A s) := l3h_abs_le_N _ i j
          _ ≤ C₀ * l3hN (ΛR s) := hA s hs'
          _ ≤ C₀ * (l3hN (Λ s) + l3hN (l3hY lam Λ₁ X t₀ s)) := by
              rw [hΛR]; exact mul_le_mul_of_nonneg_left (l3hN_add _ _) hC₀
      · rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg hC₀]
    calc l3hN (Λ t) = |Λ t 0 0| + |Λ t 0 1| + |Λ t 1 0| + |Λ t 1 1| := rfl
      _ ≤ _ := by linarith [hentry 0 0, hentry 0 1, hentry 1 0, hentry 1 1]
  have hO := l3h_gronwall hT.le ht₀ hC (by positivity) (l3h_continuousOn_N hΛc)
    (l3h_continuousOn_N hYc) (fun t _ ↦ l3hN_nonneg _) (fun t _ ↦ l3hN_nonneg _) hY hx
  -- `|t - t₀|ⁿ⁺¹ = o((t - t₀)ⁿ)`
  have ho : (fun t ↦ |t - t₀| ^ (n + 1)) =o[𝓝[Icc 0 T] t₀] fun t ↦ (t - t₀) ^ n := by
    refine Asymptotics.IsLittleO.of_bound fun c hc ↦ ?_
    have htend : Tendsto (fun t ↦ t - t₀) (𝓝[Icc 0 T] t₀) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using (continuous_sub_right t₀).tendsto t₀)
    filter_upwards [(Metric.tendsto_nhds.1 htend) c hc] with t ht
    rw [Real.dist_eq, sub_zero] at ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_abs, abs_pow, pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_right ht.le (by positivity)
  have hΛlim : ∀ i j, Tendsto (fun t ↦ ((t - t₀) ^ n)⁻¹ * Λ t i j) (𝓝[Icc 0 T \ {t₀}] t₀)
      (𝓝 0) := by
    intro i j
    have hOij : (fun t ↦ Λ t i j) =O[𝓝[Icc 0 T] t₀] fun t ↦ |t - t₀| ^ (n + 1) := by
      refine (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t ↦ ?_)).trans hO
      rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (l3hN_nonneg _)]
      exact l3h_abs_le_N _ i j
    have := (hOij.trans_isLittleO ho).tendsto_div_nhds_zero
    refine (this.mono_left (nhdsWithin_mono _ sdiff_subset)).congr fun t ↦ ?_
    rw [div_eq_inv_mul]
  refine l3h_tendsto_iff.2 fun i j ↦ ?_
  have := ((l3h_tendsto_iff.1 hYV) i j).add (hΛlim i j)
  rw [add_zero] at this
  refine this.congr fun t ↦ ?_
  simp only [Matrix.smul_apply, smul_eq_mul, hΛdef, Matrix.sub_apply]
  ring

private lemma l3hN_le_of_entries {M : Mat2} {c : ℝ} (h : ∀ i j, |M i j| ≤ c) : l3hN M ≤ 4 * c := by
  have := h 0 0; have := h 0 1; have := h 1 0; have := h 1 1
  unfold l3hN; linarith

private lemma l3hN_neg (M : Mat2) : l3hN (-M) = l3hN M := by
  simp [l3hN, abs_neg]

/-- **Claim (a)'s expansion** (TeX 7531–7545): at a zero `t₀` of `Λ_R`,
`Λ_R(t) = (t - t₀) [-Λ_{1,cost}(t₀), X(t₀)] + o(t - t₀)`, i.e. `Λ_R(t)/(t - t₀) → -W` with
`W = [Λ_{1,cost}(t₀), X(t₀)]`: `‖Y(t)‖ ≤ C |t - t₀|` and `Y(t)/(t - t₀) → [-Λ_{1,cost}, X](t₀)`
(the integrand is continuous), and `l3h_expansion` with `n = 1`. -/
private lemma l3h_claim_a {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsStateCostateSolution T u g X Λ₁ ΛR lam) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T)
    (hR : ΛR t₀ = 0) :
    Tendsto (fun t ↦ (t - t₀)⁻¹ • ΛR t) (𝓝[Icc 0 T \ {t₀}] t₀) (𝓝 (l3hF lam Λ₁ X t₀)) := by
  obtain ⟨hXc, hΛ₁c, -⟩ := l3h_continuousOn h
  have hT := h.1.1
  have hFc := l3hF_continuousOn (lam := lam) hΛ₁c hXc
  obtain ⟨MF, hMF⟩ := isCompact_Icc.exists_bound_of_continuousOn (l3h_continuousOn_N hFc)
  have hMF' : ∀ s ∈ Icc 0 T, l3hN (l3hF lam Λ₁ X s) ≤ MF := fun s hs ↦
    (le_abs_self _).trans (hMF s hs)
  have hMF0 : 0 ≤ MF := (l3hN_nonneg _).trans (hMF' 0 ⟨le_rfl, hT.le⟩)
  have hY : ∀ t ∈ Icc 0 T, l3hN (l3hY lam Λ₁ X t₀ t) ≤ 4 * MF * |t - t₀| ^ 1 := by
    intro t ht
    have hsub : uIcc t₀ t ⊆ Icc 0 T := uIcc_subset_Icc ht₀ ht
    rw [pow_one, mul_assoc]
    refine l3hN_le_of_entries fun i j ↦ ?_
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t₀) (b := t)
      (f := fun s ↦ l3hF lam Λ₁ X s i j) (C := MF) fun s hs ↦ by
        rw [Real.norm_eq_abs]
        exact (l3h_abs_le_N _ i j).trans (hMF' s (hsub (uIoc_subset_uIcc hs)))
    simpa only [Real.norm_eq_abs, l3hY, Matrix.of_apply] using this
  have hYV : Tendsto (fun t ↦ ((t - t₀) ^ 1)⁻¹ • l3hY lam Λ₁ X t₀ t) (𝓝[Icc 0 T \ {t₀}] t₀)
      (𝓝 (l3hF lam Λ₁ X t₀)) := by
    refine l3h_tendsto_iff.2 fun i j ↦ ?_
    simpa only [pow_one, Matrix.smul_apply, smul_eq_mul, l3hY, Matrix.of_apply] using
      l3h_tendsto_integral_div ht₀ (Matrix.continuousOn_iff_entrywise.1 hFc i j)
  have := l3h_expansion h ht₀ hR (by positivity) hY hYV
  simpa only [pow_one] using this

/-- **Claim (b)'s expansion** (TeX 7566–7576, a sketch in the book; gap G3): at a zero `t₀` of
`Λ_R` with `Λ_{1,cost}(t₀) = 0`, `Λ_R(t) = (t - t₀)²/2 · G + o((t - t₀)²)` with
`G = -[Λ₁'(t₀), X(t₀)]`, `Λ₁'(t₀) = [Λ₁(t₀), X(t₀)]` (the book's `-W'`). Here
`[-Λ_{1,cost}, X](s) = -[Λ₁(s) - Λ₁(t₀), X(s)]` is `O(|s - t₀|)` and `(s - t₀) G + o(s - t₀)`
(`Λ₁` is `C¹`, `X` continuous), so `‖Y(t)‖ = O(|t - t₀|²)` and `Y(t)/(t - t₀)² → G/2`
(`l3h_tendsto_integral_div_sq`); then `l3h_expansion` with `n = 2`. -/
private lemma l3h_claim_b {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsStateCostateSolution T u g X Λ₁ ΛR lam) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T)
    (hR : ΛR t₀ = 0) (hK : Λ₁ t₀ = (3 / 2 * lam) • J) :
    Tendsto (fun t ↦ ((t - t₀) ^ 2)⁻¹ • ΛR t) (𝓝[Icc 0 T \ {t₀}] t₀)
      (𝓝 ((1 / 2 : ℝ) • -((Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀) * X t₀ -
        X t₀ * (Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀)))) := by
  obtain ⟨hXc, hΛ₁c, -⟩ := l3h_continuousOn h
  have hT := h.1.1
  have hFc := l3hF_continuousOn (lam := lam) hΛ₁c hXc
  have hFij := Matrix.continuousOn_iff_entrywise.1 hFc
  set B' : ℝ → Mat2 := fun s ↦ Λ₁ s * X s - X s * Λ₁ s with hB'def
  have hB'c : ContinuousOn B' (Icc 0 T) := (hΛ₁c.mul hXc).sub (hXc.mul hΛ₁c)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (l3h_continuousOn_N hB'c)
  have hB' : ∀ s ∈ Icc 0 T, l3hN (B' s) ≤ B := fun s hs ↦ (le_abs_self _).trans (hB s hs)
  have hB0 : 0 ≤ B := (l3hN_nonneg _).trans (hB' 0 ⟨le_rfl, hT.le⟩)
  obtain ⟨CX, hCX⟩ := isCompact_Icc.exists_bound_of_continuousOn (l3h_continuousOn_N hXc)
  have hCX' : ∀ t ∈ Icc 0 T, l3hN (X t) ≤ CX := fun t ht ↦ (le_abs_self _).trans (hCX t ht)
  have hCX0 : 0 ≤ CX := (l3hN_nonneg _).trans (hCX' 0 ⟨le_rfl, hT.le⟩)
  -- `Λ₁(s) - Λ₁(t₀) = ∫_{t₀}^s [Λ₁, X]`, of size `O(|s - t₀|)`
  have hDb : ∀ s ∈ Icc 0 T, l3hN (Λ₁ s - Λ₁ t₀) ≤ 4 * (B * |s - t₀|) := by
    intro s hs
    have hsub : uIcc t₀ s ⊆ Icc 0 T := uIcc_subset_Icc ht₀ hs
    refine l3hN_le_of_entries fun i j ↦ ?_
    rw [Matrix.sub_apply, l3h_sub_eq_integral h.2.2.2.1 ht₀ hs i j]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t₀) (b := s)
      (f := fun r ↦ B' r i j) (C := B) fun r hr ↦ by
        rw [Real.norm_eq_abs]
        exact (l3h_abs_le_N _ i j).trans (hB' r (hsub (uIoc_subset_uIcc hr)))
    simpa only [Real.norm_eq_abs] using this
  have hFe : ∀ s, l3hF lam Λ₁ X s = -((Λ₁ s - Λ₁ t₀) * X s - X s * (Λ₁ s - Λ₁ t₀)) := by
    intro s
    simp only [l3hF, hK]
    noncomm_ring
  have hF0 : l3hF lam Λ₁ X t₀ = 0 := by rw [hFe]; simp
  have hFb : ∀ s ∈ Icc 0 T, l3hN (l3hF lam Λ₁ X s) ≤ 8 * B * CX * |s - t₀| := by
    intro s hs
    rw [hFe, l3hN_neg]
    have h1 := l3hN_bracket (Λ₁ s - Λ₁ t₀) (X s)
    have h2 := mul_le_mul (hDb s hs) (hCX' s hs) (l3hN_nonneg _) (by positivity)
    linarith
  have hY : ∀ t ∈ Icc 0 T, l3hN (l3hY lam Λ₁ X t₀ t) ≤ 4 * (8 * B * CX) * |t - t₀| ^ 2 := by
    intro t ht
    have hsub : uIcc t₀ t ⊆ Icc 0 T := uIcc_subset_Icc ht₀ ht
    have hle : l3hN (l3hY lam Λ₁ X t₀ t) ≤ 4 * (8 * B * CX * |t - t₀| * |t - t₀|) := by
      refine l3hN_le_of_entries fun i j ↦ ?_
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t₀) (b := t)
        (f := fun s ↦ l3hF lam Λ₁ X s i j) (C := 8 * B * CX * |t - t₀|) fun s hs ↦ by
          have hs' := uIoc_subset_uIcc hs
          rw [Real.norm_eq_abs]
          refine (l3h_abs_le_N _ i j).trans ((hFb s (hsub hs')).trans ?_)
          exact mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hs') (by positivity)
      simpa only [Real.norm_eq_abs, l3hY, Matrix.of_apply] using this
    calc l3hN (l3hY lam Λ₁ X t₀ t) ≤ 4 * (8 * B * CX * |t - t₀| * |t - t₀|) := hle
      _ = 4 * (8 * B * CX) * |t - t₀| ^ 2 := by ring
  -- `[-Λ_{1,cost}, X](s)/(s - t₀) → G`
  have hDt : Tendsto (fun s ↦ (s - t₀)⁻¹ • (Λ₁ s - Λ₁ t₀)) (𝓝[Icc 0 T \ {t₀}] t₀)
      (𝓝 (B' t₀)) := by
    refine l3h_tendsto_iff.2 fun i j ↦ ?_
    refine (l3h_tendsto_integral_div ht₀ (Matrix.continuousOn_iff_entrywise.1 hB'c i j)).congr'
      ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, l3h_sub_eq_integral h.2.2.2.1 ht₀ hs.1]
  have hXt : Tendsto X (𝓝[Icc 0 T \ {t₀}] t₀) (𝓝 (X t₀)) :=
    ((hXc t₀ ht₀).mono sdiff_subset).tendsto
  have hFt : Tendsto (fun s ↦ (s - t₀)⁻¹ • l3hF lam Λ₁ X s) (𝓝[Icc 0 T \ {t₀}] t₀)
      (𝓝 (-((Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀) * X t₀ - X t₀ * (Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀)))) := by
    refine (((hDt.mul hXt).sub (hXt.mul hDt)).neg).congr fun s ↦ ?_
    rw [hFe]
    simp only [smul_neg, smul_sub, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul]
  have hYV : Tendsto (fun t ↦ ((t - t₀) ^ 2)⁻¹ • l3hY lam Λ₁ X t₀ t) (𝓝[Icc 0 T \ {t₀}] t₀)
      (𝓝 ((1 / 2 : ℝ) • -((Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀) * X t₀ -
        X t₀ * (Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀)))) := by
    refine l3h_tendsto_iff.2 fun i j ↦ ?_
    have hFij' : Tendsto (fun s ↦ (s - t₀)⁻¹ * l3hF lam Λ₁ X s i j) (𝓝[Icc 0 T \ {t₀}] t₀)
        (𝓝 ((-((Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀) * X t₀ -
          X t₀ * (Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀))) i j)) := by
      simpa only [Matrix.smul_apply, smul_eq_mul] using (l3h_tendsto_iff.1 hFt) i j
    have := l3h_tendsto_integral_div_sq ordConnected_Icc ht₀ (hFij i j)
      (by rw [hF0, Matrix.zero_apply]) hFij'
    simp only [Matrix.smul_apply, smul_eq_mul, l3hY, Matrix.of_apply]
    rw [one_div, ← div_eq_inv_mul]
    exact this
  exact l3h_expansion h ht₀ hR (by positivity) hY hYV

/-! ### Algebra in `𝔰𝔩₂(ℝ)` -/

/-- An element of `𝔰𝔩₂(ℝ)` commuting with `X` (`det X ≠ 0`, traceless) and orthogonal to it is
zero: the centralizer of `X` is `ℝ X`, and `⟨X, X⟩ = -2 det X ≠ 0`. -/
private lemma l3h_eq_zero_of_bracket_eq_zero {A Y : Mat2} (hA : A.trace = 0) (hY : Y.trace = 0)
    (hdet : Y.det ≠ 0) (hb : A * Y - Y * A = 0) (hf : traceForm A Y = 0) : A = 0 := by
  have hA11 : A 1 1 = -A 0 0 := by rw [Matrix.trace_fin_two] at hA; linarith
  have hY11 : Y 1 1 = -Y 0 0 := by rw [Matrix.trace_fin_two] at hY; linarith
  have e00 := congrFun (congrFun hb 0) 0
  have e01 := congrFun (congrFun hb 0) 1
  have e10 := congrFun (congrFun hb 1) 0
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply, hA11,
    hY11] at e00 e01 e10
  rw [traceForm, Matrix.trace_fin_two] at hf
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hA11, hY11] at hf
  rw [Matrix.det_fin_two, hY11] at hdet
  have hα : A 0 0 = 0 := by
    have : (Y 0 0 * -Y 0 0 - Y 0 1 * Y 1 0) * A 0 0 = 0 := by
      linear_combination (-(Y 1 0) / 2) * e01 - (Y 0 0 / 2) * e00 - (Y 0 0 / 2) * hf
    exact (mul_eq_zero.1 this).resolve_left hdet
  have hβ : A 0 1 = 0 := by
    have : (Y 0 0 * -Y 0 0 - Y 0 1 * Y 1 0) * A 0 1 = 0 := by
      linear_combination (Y 0 0 / 2) * e01 - (Y 0 1 / 2) * e00 - (Y 0 1 / 2) * hf
    exact (mul_eq_zero.1 this).resolve_left hdet
  have hγ : A 1 0 = 0 := by
    have : (Y 0 0 * -Y 0 0 - Y 0 1 * Y 1 0) * A 1 0 = 0 := by
      linear_combination (-(Y 0 0) / 2) * e10 + (Y 1 0 / 2) * e00 - (Y 1 0 / 2) * hf
    exact (mul_eq_zero.1 this).resolve_left hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hα, hβ, hγ, hA11]

/-- A star state commuting with `J` is `J` (`X ∈ ℝJ ∩ O_J = {J}`, TeX 7584–7585). -/
private lemma l3h_eq_J_of_commute {Y : Mat2} (hY : IsStarState Y) (hc : J * Y - Y * J = 0) :
    Y = J := by
  obtain ⟨htr, hdet, hρ₀, -, -⟩ := hY
  have hJ : J 0 0 = 0 ∧ J 0 1 = -1 ∧ J 1 0 = 1 ∧ J 1 1 = 0 := by simp [J]
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply, hJ.1,
    hJ.2.1, hJ.2.2.1, hJ.2.2.2] at e00 e01
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  simp only [ρ₀] at hρ₀
  have h00 : Y 0 0 = 0 := by linarith
  have h11 : Y 1 1 = 0 := by linarith
  have h01 : Y 0 1 = -Y 1 0 := by linarith
  have hpos : 0 < Y 1 0 := by
    rw [h00, mul_zero, add_zero] at hρ₀
    exact (div_pos_iff_of_pos_right (by positivity)).1 hρ₀
  have h10 : Y 1 0 = 1 := by
    rw [h00, h11, h01] at hdet
    nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, h00, h11, h01, h10]

/-! ### The proof of Theorem 8.3.1 on `[0, T]` -/

/-- Theorem 8.3.1 on `[0, T]` (the time-shifted form), with the conclusion along the one-sided
neighbourhood filters of `t₀`. Steps 0–5 of the docstring of `theorem8_3_1`. -/
private lemma l3h_core {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsStateCostateSolution T u g X Λ₁ ΛR lam) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T)
    (hS : ¬(lam ≠ 0 ∧ Λ₁ t₀ = (3 / 2 * lam) • J ∧ X t₀ = J ∧ ΛR t₀ = 0)) :
    ∃ kₗ kᵣ : Fin 3,
      (∀ᶠ t in 𝓝[Icc 0 T ∩ Iio t₀] t₀,
        hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) ⊆ controlEdge kₗ) ∧
      ∀ᶠ t in 𝓝[Icc 0 T ∩ Ioi t₀] t₀,
        hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) ⊆ controlEdge kᵣ := by
  obtain ⟨hXc, -, hΛRc⟩ := l3h_continuousOn h
  have hXs : ∀ t ∈ Icc 0 T, IsStarState (X t) := fun t ht ↦ (h.1.2.2.2.1 t ht).2
  have hX₀ := hXs t₀ ht₀
  have hpt := h.2.2.1 t₀ ht₀
  have hdet : (X t₀).det ≠ 0 := by rw [hX₀.2.1]; norm_num
  have hLsub : Icc 0 T ∩ Iio t₀ ⊆ Icc 0 T \ {t₀} := fun t ht ↦ ⟨ht.1, ht.2.ne⟩
  have hRsub : Icc 0 T ∩ Ioi t₀ ⊆ Icc 0 T \ {t₀} := fun t ht ↦ ⟨ht.1, ht.2.ne'⟩
  -- the leading-term lemma on a one-sided neighbourhood
  have side : ∀ {s : Set ℝ} (σ : ℝ → ℝ) {V : Mat2}, s ⊆ Icc 0 T → (∀ t ∈ s, 0 < σ t) →
      Tendsto (fun t ↦ (σ t)⁻¹ • ΛR t) (𝓝[s] t₀) (𝓝 V) → V ≠ 0 → V.trace = 0 →
      traceForm V (X t₀) = 0 → ∃ k : Fin 3, ∀ᶠ t in 𝓝[s] t₀,
        hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) ⊆ controlEdge k :=
    fun {s} σ {V} hs hσ hL hV hVtr hVX ↦ l3h_eventually_argmax_subset hX₀
      (eventually_nhdsWithin_of_forall fun t ht ↦ hXs t (hs ht)) ((hXc t₀ ht₀).mono hs).tendsto
      (eventually_nhdsWithin_of_forall hσ) hL hV hVtr hVX
  -- brackets with `X(t₀)` are traceless and orthogonal to `X(t₀)`
  have hbtr : ∀ A : Mat2, (A * X t₀ - X t₀ * A).trace = 0 := fun A ↦ by
    simp only [Matrix.trace_fin_two, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have hbX : ∀ A : Mat2, traceForm (A * X t₀ - X t₀ * A) (X t₀) = 0 := fun A ↦ by
    simp only [traceForm, Matrix.trace_fin_two, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_two]
    ring
  by_cases hR0 : ΛR t₀ = 0
  swap
  · -- step 0: `Λ_R(t₀) ≠ 0`, continuity
    have hL : ∀ {s : Set ℝ}, s ⊆ Icc 0 T →
        Tendsto (fun t ↦ ((fun _ ↦ (1 : ℝ)) t)⁻¹ • ΛR t) (𝓝[s] t₀) (𝓝 (ΛR t₀)) := fun hs ↦ by
      simpa only [inv_one, one_smul] using ((hΛRc t₀ ht₀).mono hs).tendsto
    obtain ⟨kₗ, hkₗ⟩ := side (fun _ ↦ 1) inter_subset_left (fun _ _ ↦ one_pos)
      (hL inter_subset_left) hR0 hpt.2.1 hpt.2.2.1
    obtain ⟨kᵣ, hkᵣ⟩ := side (fun _ ↦ 1) inter_subset_left (fun _ _ ↦ one_pos)
      (hL inter_subset_left) hR0 hpt.2.1 hpt.2.2.1
    exact ⟨kₗ, kᵣ, hkₗ, hkᵣ⟩
  have hH0 := l3h_hamiltonian_zero h ht₀ hR0
  by_cases hW : l3hF lam Λ₁ X t₀ = 0
  · -- `W = 0`: `Λ_{1,cost}(t₀) = 0`
    have hK : Λ₁ t₀ = (3 / 2 * lam) • J := by
      have hKtr : (Λ₁ t₀ - (3 / 2 * lam) • J).trace = 0 := by
        rw [Matrix.trace_sub, Matrix.trace_smul, hpt.1]
        simp [J, Matrix.trace_fin_two]
      have hb : (Λ₁ t₀ - (3 / 2 * lam) • J) * X t₀ - X t₀ * (Λ₁ t₀ - (3 / 2 * lam) • J) = 0 := by
        have e : l3hF lam Λ₁ X t₀ = -((Λ₁ t₀ - (3 / 2 * lam) • J) * X t₀ -
            X t₀ * (Λ₁ t₀ - (3 / 2 * lam) • J)) := by
          unfold l3hF; noncomm_ring
        rw [e, neg_eq_zero] at hW
        exact hW
      exact sub_eq_zero.1 (l3h_eq_zero_of_bracket_eq_zero hKtr hX₀.1 hdet hb hH0)
    by_cases hG : -((Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀) * X t₀ - X t₀ * (Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀))
        = 0
    · -- claim (c): the lift is in the singular locus at `t₀`
      exfalso
      have hD0 : Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀ = 0 :=
        l3h_eq_zero_of_bracket_eq_zero (hbtr _) hX₀.1 hdet (neg_eq_zero.1 hG) (hbX _)
      have hlam : lam ≠ 0 := by
        rintro rfl
        rcases hpt.2.2.2 with h1 | h1 | h1
        · exact h1 rfl
        · exact h1 (by rw [hK]; simp)
        · exact h1 hR0
      have hJX : J * X t₀ - X t₀ * J = 0 := by
        rw [hK, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub] at hD0
        exact (smul_eq_zero.1 hD0).resolve_left (mul_ne_zero (by norm_num) hlam)
      exact hS ⟨hlam, hK, l3h_eq_J_of_commute hX₀ hJX, hR0⟩
    · -- claim (b): the same face on both sides
      have hT2 := l3h_claim_b h ht₀ hR0 hK
      have hV : (1 / 2 : ℝ) • -((Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀) * X t₀ -
          X t₀ * (Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀)) ≠ 0 := smul_ne_zero (by norm_num) hG
      have hVtr : ((1 / 2 : ℝ) • -((Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀) * X t₀ -
          X t₀ * (Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀))).trace = 0 := by
        rw [Matrix.trace_smul, Matrix.trace_neg, hbtr, neg_zero, smul_zero]
      have hVX : traceForm ((1 / 2 : ℝ) • -((Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀) * X t₀ -
          X t₀ * (Λ₁ t₀ * X t₀ - X t₀ * Λ₁ t₀))) (X t₀) = 0 := by
        rw [traceForm_smul_left, traceForm, Matrix.neg_mul, Matrix.trace_neg, ← traceForm,
          hbX, neg_zero, mul_zero]
      have hpos : ∀ t ∈ Icc 0 T \ {t₀}, 0 < (t - t₀) ^ 2 := fun t ht ↦ by
        have := sub_ne_zero.2 ht.2
        positivity
      obtain ⟨kₗ, hkₗ⟩ := side (fun t ↦ (t - t₀) ^ 2) inter_subset_left
        (fun t ht ↦ hpos t (hLsub ht)) (hT2.mono_left (nhdsWithin_mono _ hLsub)) hV hVtr hVX
      obtain ⟨kᵣ, hkᵣ⟩ := side (fun t ↦ (t - t₀) ^ 2) inter_subset_left
        (fun t ht ↦ hpos t (hRsub ht)) (hT2.mono_left (nhdsWithin_mono _ hRsub)) hV hVtr hVX
      exact ⟨kₗ, kᵣ, hkₗ, hkᵣ⟩
  · -- claim (a): `W ≠ 0`, the face of `-W` before `t₀` and of `W` after
    have hT1 := l3h_claim_a h ht₀ hR0
    have hWtr : (l3hF lam Λ₁ X t₀).trace = 0 := hbtr _
    have hWX : traceForm (l3hF lam Λ₁ X t₀) (X t₀) = 0 := hbX _
    obtain ⟨kₗ, hkₗ⟩ := side (fun t ↦ t₀ - t) inter_subset_left (fun t ht ↦ sub_pos.2 ht.2)
      ((hT1.neg.mono_left (nhdsWithin_mono _ hLsub)).congr fun t ↦ by
        rw [← neg_smul, ← inv_neg, neg_sub])
      (neg_ne_zero.2 hW) (by rw [Matrix.trace_neg, hWtr, neg_zero])
      (by rw [traceForm, Matrix.neg_mul, Matrix.trace_neg, ← traceForm, hWX, neg_zero])
    obtain ⟨kᵣ, hkᵣ⟩ := side (fun t ↦ t - t₀) inter_subset_left (fun t ht ↦ sub_pos.2 ht.2)
      (hT1.mono_left (nhdsWithin_mono _ hRsub)) hW hWtr hWX
    exact ⟨kₗ, kᵣ, hkₗ, hkᵣ⟩

/-! ### Helpers for the control form and for Theorem 8.3.2 -/

/-- A translate of an almost-everywhere statement (Lebesgue measure is translation invariant). -/
private lemma l3h_ae_shift {P : ℝ → Prop} (c : ℝ) (h : ∀ᵐ τ, P (c + τ)) : ∀ᵐ t, P t := by
  have := (measurePreserving_sub_right volume c).quasiMeasurePreserving.ae h
  simpa only [add_sub_cancel] using this

/-- The maximum condition of an extremal lifted trajectory on `[a, b]`, in the original time. -/
private lemma l3h_ae_mem_argmax {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) :
    ∀ᵐ t, t ∈ Ioo a b → u t ∈ hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) := by
  have hae := h.2.2.2.2.2
  have hu := h.1.2.2.1
  refine l3h_ae_shift a (hae.mono fun τ hτ hτI ↦ ?_)
  have hτ' : τ ∈ Ioo 0 (b - a) := ⟨by linarith [hτI.1], by linarith [hτI.2]⟩
  exact ⟨hu τ (Ioo_subset_Icc_self hτ'), (hτ hτ').2⟩

private lemma l3h_vertex_injective {i j : Fin 3} (h : vertex i = vertex j) : i = j := by
  by_contra hij
  have := congrFun h i
  simp [vertex, hij] at this

/-- A control in the edge `{u_k = 0}` with edge parameter `±½` is a vertex of that edge. -/
private lemma l3h_eq_vertex_of_edgeParam {k : Fin 3} {v : Fin 3 → ℝ} (hv : v ∈ controlEdge k)
    {e : ℝ} (he : e ∈ ({-(1 / 2), 1 / 2} : Set ℝ)) (hpar : edgeParam k v = e) :
    v = vertex (if e = 1 / 2 then k + 1 else k + 2) := by
  obtain ⟨⟨hb, hs⟩, hk⟩ := hv
  have b0 := hb 0; have b1 := hb 1; have b2 := hb 2
  rcases he with rfl | rfl
  · rw [show (if (-(1 / 2) : ℝ) = 1 / 2 then k + 1 else k + 2) = k + 2 by norm_num]
    funext i
    fin_cases k <;> fin_cases i <;> simp [vertex, edgeParam] at hpar hk ⊢ <;> linarith
  · rw [show (if (1 / 2 : ℝ) = 1 / 2 then k + 1 else k + 2) = k + 1 by norm_num]
    funext i
    fin_cases k <;> fin_cases i <;> simp [vertex, edgeParam] at hpar hk ⊢ <;> linarith

/-- **Theorem 8.1.4 on an interval where the control lies in one edge** (the step of the proof of
Theorem 8.3.2 "By Theorem 8.1.4, the control is bang-bang with finite switching along the edge",
TeX 7602–7604). If the control lies in the edge `{u_k = 0}` almost everywhere on
`(c, d) ⊆ [a, b]`, edge extremality (Definition 8.1.2) gives an extremal of the edge control
problem on `[c, d]`, and Theorem 8.1.4 makes the edge control `u_e = ±½` (the two vertices of the
edge) bang-bang with finitely many switches. -/
private lemma l3h_isFiniteBangBang_of_edge {a b c d : ℝ} {u : ℝ → Fin 3 → ℝ} {X : ℝ → Mat2}
    (hedge : IsEdgeExtremalOn a b u X) (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) {k : Fin 3}
    (hk : ∀ᵐ t, t ∈ Ioo c d → u t ∈ controlEdge k) : IsFiniteBangBang c d u := by
  obtain ⟨ν, p, hp⟩ := hedge k c d hac hcd hdb (hk.mono fun t ht htI ↦ (ht htI).2)
  obtain ⟨S, hS⟩ := theorem8_1_4 hp
  refine ⟨S.image (c + ·), fun t ht htS ↦ ?_⟩
  have hτ : t - c ∈ Ioo 0 (d - c) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hτS : t - c ∉ S := fun h ↦ htS (Finset.mem_image.2 ⟨t - c, h, by ring⟩)
  obtain ⟨e, he, ε, hε, hae⟩ := hS (t - c) hτ hτS
  have hae' : ∀ᵐ σ, σ ∈ Ioo (t - ε) (t + ε) → edgeParam k (u σ) = e :=
    l3h_ae_shift c (hae.mono fun τ hτ' hmem ↦
      hτ' ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)
  refine ⟨if e = 1 / 2 then k + 1 else k + 2, min ε (min (t - c) (d - t)),
    lt_min hε (lt_min (by linarith [ht.1]) (by linarith [ht.2])), ?_⟩
  filter_upwards [hae', hk] with σ h1 h2 hσ
  have m1 := min_le_left ε (min (t - c) (d - t))
  have m2 := (min_le_right ε (min (t - c) (d - t))).trans (min_le_left _ _)
  have m3 := (min_le_right ε (min (t - c) (d - t))).trans (min_le_right _ _)
  exact l3h_eq_vertex_of_edgeParam (h2 ⟨by linarith [hσ.1], by linarith [hσ.2]⟩) he
    (h1 ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)

/-- **A control that is locally almost everywhere a vertex on an open interval is almost
everywhere one vertex there**: the vertex is locally constant, and the interval is connected. -/
theorem exists_ae_eq_vertex_of_locally {α β : ℝ} {u : ℝ → Fin 3 → ℝ}
    (h : ∀ τ ∈ Ioo α β, ∃ i : Fin 3, ∃ ε > 0, ∀ᵐ σ, σ ∈ Ioo (τ - ε) (τ + ε) → u σ = vertex i) :
    ∃ i : Fin 3, ∀ᵐ σ, σ ∈ Ioo α β → u σ = vertex i := by
  rcases le_or_gt β α with hβα | hαβ
  · exact ⟨0, Eventually.of_forall fun σ hσ ↦ absurd (hσ.1.trans hσ.2) (not_lt.2 hβα)⟩
  choose! φ ε hε hφ using h
  -- the vertex is locally constant
  have hloc : ∀ τ ∈ Ioo α β, ∀ᶠ τ' in 𝓝 τ, φ τ' = φ τ := by
    intro τ hτ
    have hετ := hε τ hτ
    filter_upwards [Ioo_mem_nhds (by linarith : τ - ε τ / 2 < τ) (by linarith : τ < τ + ε τ / 2),
      Ioo_mem_nhds hτ.1 hτ.2] with τ' h1 h2
    have hετ' := hε τ' h2
    set r := min (ε τ') (ε τ / 2)
    have hr : 0 < r := lt_min hετ' (half_pos hετ)
    have hr1 : r ≤ ε τ' := min_le_left _ _
    have hr2 : r ≤ ε τ / 2 := min_le_right _ _
    have hpos : volume (Ioo (τ' - r) (τ' + r)) ≠ 0 := by
      rw [Real.volume_Ioo]
      exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
    have hboth : ∀ᵐ σ, σ ∈ Ioo (τ' - r) (τ' + r) → u σ = vertex (φ τ') ∧ u σ = vertex (φ τ) := by
      filter_upwards [hφ τ' h2, hφ τ hτ] with σ hσ1 hσ2 hσ
      exact ⟨hσ1 ⟨by linarith [hσ.1], by linarith [hσ.2]⟩,
        hσ2 ⟨by linarith [hσ.1, h1.1], by linarith [hσ.2, h1.2]⟩⟩
    obtain ⟨σ, -, hσ⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
      ((ae_restrict_iff' measurableSet_Ioo).2 hboth)
    exact l3h_vertex_injective (hσ.1.symm.trans hσ.2)
  have hcont : ContinuousOn φ (Ioo α β) := fun x hx ↦ by
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, nhds_discrete (Fin 3), tendsto_pure]
    exact hloc x hx
  have hmid : (α + β) / 2 ∈ Ioo α β := ⟨by linarith, by linarith⟩
  refine ⟨φ ((α + β) / 2), ?_⟩
  rw [ae_iff]
  refine measure_null_of_locally_null (μ := volume) _ fun x hx ↦ ?_
  have hxI : x ∈ Ioo α β := by_contra fun h' ↦ hx fun h'' ↦ absurd h'' h'
  refine ⟨{σ | ¬(σ ∈ Ioo α β → u σ = vertex (φ ((α + β) / 2)))} ∩ Ioo (x - ε x) (x + ε x),
    inter_mem_nhdsWithin _ (Ioo_mem_nhds (by linarith [hε x hxI]) (by linarith [hε x hxI])), ?_⟩
  refine measure_mono_null (fun σ hσ ↦ ?_) (ae_iff.1 (hφ x hxI))
  simp only [mem_inter_iff, mem_ofPred_eq] at hσ ⊢
  intro h'
  apply hσ.1
  intro hσI
  rw [h' hσ.2, isPreconnected_Ioo.constant hcont hxI hmid]

/-- Near the right end `d` of an interval on which the control is bang-bang with finitely many
switches, the control is almost everywhere one vertex. -/
private lemma l3h_ae_vertex_near_right {c d : ℝ} {u : ℝ → Fin 3 → ℝ} (hcd : c < d)
    (h : IsFiniteBangBang c d u) :
    ∃ m < d, c ≤ m ∧ ∃ i : Fin 3, ∀ᵐ σ, σ ∈ Ioo m d → u σ = vertex i := by
  obtain ⟨S, hS⟩ := h
  have hF : (insert c (S.filter (· < d))).Nonempty := Finset.insert_nonempty _ _
  have hmF : ∀ x ∈ insert c (S.filter (· < d)), x ≤ (insert c (S.filter (· < d))).max' hF :=
    fun x hx ↦ Finset.le_max' _ x hx
  have hm_lt : (insert c (S.filter (· < d))).max' hF < d := by
    rcases Finset.mem_insert.1 (Finset.max'_mem _ hF) with h' | h'
    · rw [h']; exact hcd
    · exact (Finset.mem_filter.1 h').2
  have hcm := hmF c (Finset.mem_insert_self _ _)
  refine ⟨_, hm_lt, hcm, exists_ae_eq_vertex_of_locally fun τ hτ ↦
    hS τ ⟨hcm.trans_lt hτ.1, hτ.2⟩ fun hτS ↦ ?_⟩
  have := hmF τ (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hτS, hτ.2⟩))
  linarith [hτ.1]

/-- Near the left end `c` of an interval on which the control is bang-bang with finitely many
switches, the control is almost everywhere one vertex. -/
private lemma l3h_ae_vertex_near_left {c d : ℝ} {u : ℝ → Fin 3 → ℝ} (hcd : c < d)
    (h : IsFiniteBangBang c d u) :
    ∃ M > c, M ≤ d ∧ ∃ i : Fin 3, ∀ᵐ σ, σ ∈ Ioo c M → u σ = vertex i := by
  obtain ⟨S, hS⟩ := h
  have hF : (insert d (S.filter (c < ·))).Nonempty := Finset.insert_nonempty _ _
  have hmF : ∀ x ∈ insert d (S.filter (c < ·)), (insert d (S.filter (c < ·))).min' hF ≤ x :=
    fun x hx ↦ Finset.min'_le _ x hx
  have hm_gt : c < (insert d (S.filter (c < ·))).min' hF := by
    rcases Finset.mem_insert.1 (Finset.min'_mem _ hF) with h' | h'
    · rw [h']; exact hcd
    · exact (Finset.mem_filter.1 h').2
  have hdm := hmF d (Finset.mem_insert_self _ _)
  refine ⟨_, hm_gt, hdm, exists_ae_eq_vertex_of_locally fun τ hτ ↦
    hS τ ⟨hτ.1, hτ.2.trans_le hdm⟩ fun hτS ↦ ?_⟩
  have := hmF τ (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hτS, hτ.1⟩))
  linarith [hτ.2]

/-! ### Theorem 8.3.1, its control form, and Theorem 8.3.2 -/

/-- **Theorem 8.3.1** (`thm:avoid-singular`), in the one-sided maximizer form. Consider an
extremal lifted trajectory on `[a, b]` and `t₀ ∈ [a, b]` such that the lifted trajectory does not
meet the singular locus at time `t₀`, and assume that the trajectory is also edge extremal
(Definition 8.1.2). Then there are `ε > 0` and edges `k₋ = kₗ`, `k₊ = kᵣ` of `U_T` such that at
every time `t ∈ [a, b]` with `t₀ - ε < t < t₀` the set of maximizers of the Hamiltonian
`hamiltonianArgmax λ_cost Λ₁(t) Λ_R(t) X(t)` is contained in the edge `{u_{kₗ} = 0}`, and at every
time `t ∈ [a, b]` with `t₀ < t < t₀ + ε` it is contained in the edge `{u_{kᵣ} = 0}`.

**Restatement.** The book prints (TeX 7448–7458): "there exists an edge `{i, j}` and a
neighborhood of `t₀` in `[t₁, t₂]` on which `(X(t), Λ_R(t)) ∈ ⋃_{I ⊆ {i,j}} (T*O_J)_I`", i.e. the
maximizers lie in one edge at every time of a two-sided neighbourhood of `t₀`. That is false
(gap G2; module docstring): at a time `t₀` off `𝒮_sing` with `Λ_R(t₀) = 0` all of `U_T` maximizes,
which happens on edge-extremal extremals (normal counterexample `λ_cost = -1`,
`X(0) = Φ(0.1 + 0.9i)`, `Λ_R(0) = 0`, `Λ₁(0) = -(3/2) J + L`, `0 ≠ L ⊥ X(0)`), and the maximizers
can lie in different edges before and after `t₀` (abnormal counterexample on the edge
`{u₀ = 0}`: the edge `{e₂, e₃}` before, the vertex `e₁` after). The user decided to formalize the
one-sided maximizer form stated here, keeping the book's hypotheses. The hypothesis `_hedge`
(edge extremality) is the book's; the proof of the maximizer form does not use it. The control
form used by Theorem 8.3.2 is the corollary
`IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn`.

Proof (the book's proof, TeX 7469–7586, run directly instead of in the contrapositive, after the
time shift to `[0, b - a]`; `l3h_core`). The maximizers are located by one lemma
(`l3h_eventually_argmax_subset`): if `X(t) → X(t₀)` and `Λ_R(t)/σ(t) → V` along one side of `t₀`
with `σ > 0` and `0 ≠ V ∈ X(t₀)^⊥`, then by Lemma 8.2.1 (`lemma8_2_1`) some vertex `e_j` is
beaten by a control `v` for the Hamiltonian with `Λ_R = V`; the control-dependent term
`-σ(t)⟨Λ_R(t)/σ(t), Z_u⟩/⟨X(t), Z_u⟩` keeps `e_j` below `v` on that side near `t₀`, and as the
maximizers form a face of `U_T` (Lemma 7.3.1, `lemma7_3_1`), they lie in the edge `{u_j = 0}`.
0. `Λ_R(t₀) ≠ 0`: the lemma with `σ = 1`, `V = Λ_R(t₀)` (continuity; the book's "by the
   continuity of the Hamiltonian, … By Lemma 8.2.1, `Λ_R(0) = 0`"), `kₗ = kᵣ`. Otherwise the
   Hamiltonian vanishes at `t₀` (`l3h_hamiltonian_zero`: it vanishes almost everywhere and is
   continuous there), so `Λ_{1,cost}(t₀) = Λ₁(t₀) - (3/2) λ_cost J ∈ X(t₀)^⊥`.
1. `Λ₁` is `C¹` (its equation `Λ₁' = [Λ₁, X]` has a continuous right-hand side).
2. `Y(t) = -∫_{t₀}^t [Λ_{1,cost}, X]` (`l3hY`) and `Λ = Λ_R - Y` satisfy `Λ' = A(Λ, t) + A(Y, t)`
   with `A(Λ, t) = [P, Λ] - ⟨Λ, P⟩[P, X]` bounded on `[0, b - a]` (`P = Z_u/⟨Z_u, X⟩`,
   Lemma 3.3.4 and compactness), so `‖Λ‖ ≤ C₀ |∫_{t₀}^t (‖Λ‖ + ‖Y‖)|` (8.3.1,
   `eqn:Lambda-bellman`, in the entrywise `ℓ¹` norm), and Corollary A.1.3 two-sided
   (`corollaryA_1_3_two_sided`, gap G14; at `t₀ = a` or `b` applied to the function extended
   past the end by its value there, `l3h_gronwall`) gives `‖Λ‖ = O(|t - t₀|ⁿ⁺¹)` when
   `‖Y‖ = O(|t - t₀|ⁿ)`; then `Λ_R/(t - t₀)ⁿ` has the limit of `Y/(t - t₀)ⁿ` (`l3h_expansion`).
3. Claim (a): `W = [Λ_{1,cost}(t₀), X(t₀)] ≠ 0`. Then `Λ_R(t)/(t - t₀) → -W` (`l3h_claim_a`,
   `n = 1`), i.e. `Λ_R = -W (t - t₀) + o(t - t₀)`; the lemma with `σ = t - t₀`, `V = -W` after
   `t₀` and `σ = t₀ - t`, `V = W` before (`±W ∈ X(t₀)^⊥ ∖ 0`) gives `kᵣ` and `kₗ` (the book: "for
   sufficiently small `t > 0` (or `t < 0`) there exists a vertex or edge of `U_T` that maximizes
   this Hamiltonian").
4. Claim (b) (a "brief sketch" in the book, gap G3): `W = 0`, so `Λ_{1,cost}(t₀) = 0` (it commutes
   with `X(t₀)` and is orthogonal to it, `l3h_eq_zero_of_bracket_eq_zero`), and
   `W' = [Λ_{1,cost}'(t₀), X(t₀)] ≠ 0`. Then `[Λ_{1,cost}, X] = O(|t - t₀|)` and
   `= (t - t₀) W' + o(t - t₀)`, so `‖Y‖ = O(|t - t₀|²)`, `Y/(t - t₀)² → -W'/2`
   (`l3h_tendsto_integral_div_sq`), and `Λ_R(t)/(t - t₀)² → -W'/2` (`l3h_claim_b`, `n = 2`):
   `Λ_R` has an isolated zero at `t₀` with the same leading direction on both sides; the lemma
   with `σ = (t - t₀)²` gives `kₗ = kᵣ`.
5. Claim (c): `W = W' = 0`. Then `Λ_{1,cost}'(t₀) = [Λ₁(t₀), X(t₀)] = (3/2) λ_cost [J, X(t₀)]`
   commutes with `X(t₀)` and is orthogonal to it, so it vanishes; nontriviality of
   `(λ_cost, Λ₁, Λ_R)` at `t₀` (gap G1) gives `λ_cost ≠ 0`, so `[J, X(t₀)] = 0` and
   `X(t₀) ∈ ℝ J ∩ O_J = {J}` (`l3h_eq_J_of_commute`): the lift is in `𝒮_sing` at `t₀`, against
   the hypothesis.

Departure from the paper (forced by the restatement): in claim (a) the book passes to the
control through Theorem 8.1.4 ("the control function has finite bang-bang switching near
`t = 0`", TeX 7558–7560) to contradict the assumption of its contrapositive. The maximizer form
needs no such step, so neither Theorem 8.1.4 nor edge extremality is used here; that step is in
the corollary `IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn`. -/
theorem theorem8_3_1 {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) (_hedge : IsEdgeExtremalOn a b u X)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hS : (g t₀, Λ₁ t₀, X t₀, ΛR t₀) ∉ singularLocus) :
    ∃ ε > 0, ∃ kₗ kᵣ : Fin 3,
      (∀ t ∈ Icc a b, t₀ - ε < t → t < t₀ →
        hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) ⊆ controlEdge kₗ) ∧
      ∀ t ∈ Icc a b, t₀ < t → t < t₀ + ε →
        hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) ⊆ controlEdge kᵣ := by
  -- the time shift `t ↦ a + t` of `IsExtremalOn`
  have hsol : IsStateCostateSolution (b - a) (fun t ↦ u (a + t)) (fun t ↦ g (a + t))
      (fun t ↦ X (a + t)) (fun t ↦ Λ₁ (a + t)) (fun t ↦ ΛR (a + t)) lam := h
  have ht₀' : t₀ - a ∈ Icc 0 (b - a) := ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
  have he : ∀ t, a + (t - a) = t := fun t ↦ by ring
  have hS' : ¬(lam ≠ 0 ∧ Λ₁ (a + (t₀ - a)) = (3 / 2 * lam) • J ∧ X (a + (t₀ - a)) = J ∧
      ΛR (a + (t₀ - a)) = 0) := by
    rw [he]
    rintro ⟨h1, h2, h3, h4⟩
    have hdet : (g (a + (t₀ - a))).det = 1 := (hsol.1.2.2.2.1 (t₀ - a) ht₀').1
    rw [he] at hdet
    exact hS ⟨lam, h1, hdet, h2, h3, h4⟩
  obtain ⟨kₗ, kᵣ, hL, hR⟩ := l3h_core hsol ht₀' hS'
  obtain ⟨εₗ, hεₗ, hLs⟩ := Metric.mem_nhdsWithin_iff.1 hL
  obtain ⟨εᵣ, hεᵣ, hRs⟩ := Metric.mem_nhdsWithin_iff.1 hR
  have m1 := min_le_left εₗ εᵣ
  have m2 := min_le_right εₗ εᵣ
  refine ⟨min εₗ εᵣ, lt_min hεₗ hεᵣ, kₗ, kᵣ, fun t ht h1 h2 ↦ ?_, fun t ht h1 h2 ↦ ?_⟩
  · have hmem : hamiltonianArgmax lam (Λ₁ (a + (t - a))) (ΛR (a + (t - a))) (X (a + (t - a))) ⊆
        controlEdge kₗ := hLs ⟨by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith,
        ⟨by linarith [ht.1], by linarith [ht.2]⟩, show t - a < t₀ - a by linarith⟩
    rwa [he] at hmem
  · have hmem : hamiltonianArgmax lam (Λ₁ (a + (t - a))) (ΛR (a + (t - a))) (X (a + (t - a))) ⊆
        controlEdge kᵣ := hRs ⟨by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith,
        ⟨by linarith [ht.1], by linarith [ht.2]⟩, show t₀ - a < t - a by linarith⟩
    rwa [he] at hmem

/-- **The control form of Theorem 8.3.1**, as the proof of Theorem 8.3.2 quotes it (TeX 7600–7602:
"for every `t₀ ∈ [t₁, t₂]`, there exists a neighborhood of `t₀` on which the control takes values
in a single edge of `U_T` almost everywhere"). Let an extremal lifted trajectory on `[a, b]` be
edge extremal, and let its lift not meet `𝒮_sing` at `t₀ ∈ [a, b]`. Then for some edge
`{u_k = 0}` of `U_T` and some `ε > 0`, the control lies in that edge at almost every time of
`(t₀ - ε, t₀ + ε) ∩ [a, b]`.

Proof (a corollary of `theorem8_3_1`, with the step of the book's claim (a) that passes to the
control: "by the results of Theorem 8.1.4, the control function has finite bang-bang switching
near `t = 0`", TeX 7558–7560; this step moved here from the proof of Theorem 8.3.1 with the
restatement):
1. `theorem8_3_1` gives `ε`, `kₗ`, `kᵣ`. The maximum condition (`IsExtremalOn`: `u(t)` maximizes
   the Hamiltonian for almost every `t`, `l3h_ae_mem_argmax`) puts `u(t)` in the edge `kₗ` for
   almost every `t ∈ (t₀ - ε, t₀) ∩ [a, b]`, and in the edge `kᵣ` for almost every
   `t ∈ (t₀, t₀ + ε) ∩ [a, b]`.
2. Left side (if `a < t₀`): with `c = max a (t₀ - ε/2)`, edge extremality (Definition 8.1.2) on
   `[c, t₀]` gives an extremal of the edge control problem with control `edgeParam kₗ u`, and
   Theorem 8.1.4 (`theorem8_1_4`) makes the control bang-bang with finitely many switches on
   `[c, t₀]` (`l3h_isFiniteBangBang_of_edge`: `edgeParam = ±½` in the edge `kₗ` means
   `vertex (kₗ + 1)` or `vertex (kₗ + 2)`). After the last switch before `t₀` the control is
   almost everywhere one vertex (`l3h_ae_vertex_near_right`; the interval is connected,
   `exists_ae_eq_vertex_of_locally`). The right side likewise.
3. Any two vertices lie in a common edge (`vertex i`, `vertex j` lie in `controlEdge k` for
   `k ∉ {i, j}`); shrink `ε`. The time `t₀` is a null set. -/
theorem IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn {a b : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsExtremalOn a b u g X Λ₁ ΛR lam)
    (hedge : IsEdgeExtremalOn a b u X) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hS : (g t₀, Λ₁ t₀, X t₀, ΛR t₀) ∉ singularLocus) :
    ∃ k : Fin 3, ∃ ε > 0, ∀ᵐ t, t ∈ Ioo (t₀ - ε) (t₀ + ε) → t ∈ Icc a b → u t ∈ controlEdge k := by
  obtain ⟨ε, hε, kₗ, kᵣ, hL, hR⟩ := theorem8_3_1 h hedge ht₀ hS
  have hmax := l3h_ae_mem_argmax h
  -- left of `t₀`: almost everywhere one vertex
  obtain ⟨m, hm, iₗ, hiₗ⟩ : ∃ m < t₀, ∃ i : Fin 3,
      ∀ᵐ σ, σ ∈ Ioo m t₀ → σ ∈ Icc a b → u σ = vertex i := by
    rcases eq_or_lt_of_le ht₀.1 with h0 | h0
    · refine ⟨t₀ - 1, by linarith, 0, Eventually.of_forall fun σ hσ hσab ↦ ?_⟩
      exact absurd (h0 ▸ hσab.1) (not_le.2 hσ.2)
    · have hc : max a (t₀ - ε / 2) < t₀ := max_lt h0 (by linarith)
      have hk : ∀ᵐ t, t ∈ Ioo (max a (t₀ - ε / 2)) t₀ → u t ∈ controlEdge kₗ := by
        filter_upwards [hmax] with t ht htI
        have htab : t ∈ Ioo a b := ⟨(le_max_left _ _).trans_lt htI.1, htI.2.trans_le ht₀.2⟩
        exact hL t (Ioo_subset_Icc_self htab)
          (by linarith [(le_max_right a (t₀ - ε / 2)).trans_lt htI.1]) htI.2 (ht htab)
      obtain ⟨m, hm, -, i, hi⟩ := l3h_ae_vertex_near_right hc
        (l3h_isFiniteBangBang_of_edge hedge (le_max_left _ _) hc ht₀.2 hk)
      exact ⟨m, hm, i, hi.mono fun σ hσ hσm _ ↦ hσ hσm⟩
  -- right of `t₀`: almost everywhere one vertex
  obtain ⟨M, hM, iᵣ, hiᵣ⟩ : ∃ M > t₀, ∃ i : Fin 3,
      ∀ᵐ σ, σ ∈ Ioo t₀ M → σ ∈ Icc a b → u σ = vertex i := by
    rcases eq_or_lt_of_le ht₀.2 with h0 | h0
    · refine ⟨t₀ + 1, by linarith, 0, Eventually.of_forall fun σ hσ hσab ↦ ?_⟩
      exact absurd (h0 ▸ hσab.2) (not_le.2 hσ.1)
    · have hd : t₀ < min b (t₀ + ε / 2) := lt_min h0 (by linarith)
      have hk : ∀ᵐ t, t ∈ Ioo t₀ (min b (t₀ + ε / 2)) → u t ∈ controlEdge kᵣ := by
        filter_upwards [hmax] with t ht htI
        have htab : t ∈ Ioo a b := ⟨ht₀.1.trans_lt htI.1, htI.2.trans_le (min_le_left _ _)⟩
        exact hR t (Ioo_subset_Icc_self htab) htI.1
          (by linarith [htI.2.trans_le (min_le_right b (t₀ + ε / 2))]) (ht htab)
      obtain ⟨M, hM, -, i, hi⟩ := l3h_ae_vertex_near_left hd
        (l3h_isFiniteBangBang_of_edge hedge ht₀.1 hd (min_le_left _ _) hk)
      exact ⟨M, hM, i, hi.mono fun σ hσ hσM _ ↦ hσ hσM⟩
  -- a common edge of the two vertices
  have hcommon : ∀ i j : Fin 3, ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, hk1, hk2⟩ := hcommon iₗ iᵣ
  have m1 := min_le_left (t₀ - m) (M - t₀)
  have m2 := min_le_right (t₀ - m) (M - t₀)
  refine ⟨k, min (t₀ - m) (M - t₀), lt_min (by linarith) (by linarith), ?_⟩
  filter_upwards [hiₗ, hiᵣ, (Set.countable_singleton t₀).ae_notMem volume] with t h1 h2 h3 htI htab
  rcases lt_trichotomy t t₀ with hlt | heq | hgt
  · rw [h1 ⟨by linarith [htI.1], hlt⟩ htab]
    exact vertex_mem_controlEdge (Ne.symm hk1)
  · exact absurd heq h3
  · rw [h2 ⟨hgt, by linarith [htI.2]⟩ htab]
    exact vertex_mem_controlEdge (Ne.symm hk2)

/-- **Theorem 8.3.2** (`thm:finite-bang-bang`). Consider an extremal lifted trajectory on a compact
interval `[a, b]` that does not meet the singular locus `𝒮_sing`, and assume that the trajectory
`(g, X)` is also edge extremal. Then the control is bang-bang with finitely many switches on
`[a, b]`.

Chapter 1 restates this theorem (TeX 851–856) without the hypothesis "edge extremal"; that
restatement is false for extremal lifted trajectories on an interval (gap G12): by Remark 8.1.6
(`remark8_1_6`, with the sign of G4), every trajectory with an arbitrary measurable control in an
edge of `U_T` lifts to an abnormal extremal lifted trajectory, which does not meet `𝒮_sing`
(`Λ_R ≠ 0`) and need not be bang-bang. The Chapter 8 statement is formalized.

Proof (the book's, TeX 7598–7605): for every `t₀ ∈ [a, b]`, the control form of Theorem 8.3.1
(`IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn`, the corollary of `theorem8_3_1`)
gives a neighbourhood of `t₀` on which the control lies in a single edge a.e.; on its closure in
`[a, b]` the trajectory is edge extremal (Definition 8.1.2), so Theorem 8.1.4 (`theorem8_1_4`)
makes the control bang-bang with finitely many switches there
(`l3h_isFiniteBangBang_of_edge`: `u_e = ±½` are the two vertices of the edge); compactness of
`[a, b]` (finitely many such neighbourhoods, `IsCompact.elim_nhds_subcover`) gives finitely many
switches on `[a, b]` (the switching times of the pieces and their ends). -/
theorem theorem8_3_2 {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) (hedge : IsEdgeExtremalOn a b u X)
    (hS : ∀ t ∈ Icc a b, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus) :
    IsFiniteBangBang a b u := by
  have hab : a < b := by have := h.1.1; linarith
  choose! k ε hε hk using fun x (hx : x ∈ Icc a b) ↦
    h.exists_ae_mem_controlEdge_of_isEdgeExtremalOn hedge hx (hS x hx)
  -- on `[max a (x - ε/2), min b (x + ε/2)]` the control is bang-bang with finitely many switches
  have hcd : ∀ x ∈ Icc a b, max a (x - ε x / 2) < min b (x + ε x / 2) := fun x hx ↦ by
    have := hε x hx
    exact max_lt (lt_min hab (by linarith [hx.1])) (lt_min (by linarith [hx.2]) (by linarith))
  have hfbb : ∀ x ∈ Icc a b, IsFiniteBangBang (max a (x - ε x / 2)) (min b (x + ε x / 2)) u := by
    intro x hx
    refine l3h_isFiniteBangBang_of_edge hedge (le_max_left _ _) (hcd x hx) (min_le_left _ _)
      (k := k x) ?_
    filter_upwards [hk x hx] with t ht htI
    have h1 := (le_max_right a (x - ε x / 2)).trans_lt htI.1
    have h2 := htI.2.trans_le (min_le_right b (x + ε x / 2))
    have := hε x hx
    exact ht ⟨by linarith, by linarith⟩
      ⟨((le_max_left _ _).trans_lt htI.1).le, (htI.2.trans_le (min_le_left _ _)).le⟩
  choose! S hSx using hfbb
  -- a finite subcover of `[a, b]`
  obtain ⟨F, hFs, hcover⟩ := isCompact_Icc.elim_nhds_subcover
    (fun x ↦ Ioo (x - ε x / 2) (x + ε x / 2))
    (fun x hx ↦ Ioo_mem_nhds (by linarith [hε x hx]) (by linarith [hε x hx]))
  refine ⟨F.biUnion fun x ↦ insert (max a (x - ε x / 2)) (insert (min b (x + ε x / 2)) (S x)),
    fun t ht htS ↦ ?_⟩
  obtain ⟨x, hxF, htx⟩ := mem_iUnion₂.1 (hcover (Ioo_subset_Icc_self ht))
  have hx := hFs x hxF
  have hnot : t ∉ insert (max a (x - ε x / 2)) (insert (min b (x + ε x / 2)) (S x)) :=
    fun h' ↦ htS (Finset.mem_biUnion.2 ⟨x, hxF, h'⟩)
  simp only [Finset.mem_insert, not_or] at hnot
  have htcd : t ∈ Ioo (max a (x - ε x / 2)) (min b (x + ε x / 2)) :=
    ⟨lt_of_le_of_ne (max_le ht.1.le htx.1.le) (Ne.symm hnot.1),
      lt_of_le_of_ne (le_min ht.2.le htx.2.le) hnot.2.1⟩
  exact hSx x hx t htcd hnot.2.2

end SmoothedPolygons
