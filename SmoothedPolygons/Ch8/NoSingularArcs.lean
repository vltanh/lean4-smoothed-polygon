module

public import SmoothedPolygons.Ch8.SingularLocus
public import SmoothedPolygons.Ch8.CircleVariation
public import SmoothedPolygons.Ch8.EdgeBangBang
public import SmoothedPolygons.Ch8.EdgeExtremal
public import SmoothedPolygons.Ch8.EdgePullback

/-!
# The global minimizer has no singular subarcs (Theorem 8.2.7)

Theorem 8.2.7 (`thm:no-singular-arcs`, TeX 7315): "The global minimizer of the Reinhardt problem
does not contain any singular subarcs." A singular subarc (Definition 6.2.1(3), `IsSingularSubarc`)
is an open time interval on which the maximum condition does not determine the control: at every
time the Hamiltonian has at least two maximizers in `U_T`. By Lemma 8.2.1 the set of maximizers is
then an edge of `U_T` or all of `U_T`.

## The authors' reading (formalized as `theorem8_2_7`)

The book's proof (TeX 7320–7391) treats only the singular subarcs on which the Hamiltonian is
independent of the control (all of `U_T` maximizes): by Theorem 8.2.6 they are circular arcs, and a
circular arc is not a local minimizer (second variation, `l3st_exists_lt_cost_of_circleArc`).
This covered case is `not_forall_hamiltonian_eq_of_isReinhardtMinimizer`, which is what the proof of
Theorem 16.3.1 uses ("A trajectory cannot remain on the singular locus for any positive interval
of time by Theorem 8.2.7", TeX 12816–12817).

The edge case is left to the edge control problem: "The theorem is only true if we include
secondary edge optimal control problem" (the authors' comment before the theorem, TeX 7300–7302),
"We say Reinhardt problem here rather than Reinhardt control problem because we want to include the
edge control problem" (TeX 7312–7313), and Chapter 1 (TeX 806–821): when the maximizing face is an
edge, the control problem is modified to the edge control problem, whose extremals are bang-bang
with finitely many switches (Theorem 8.1.4). So "singular" refers, on an interval where the control
lies in an edge of `U_T`, to the maximization of the edge problem's Hamiltonian (the minimizer is
edge extremal, Proposition 8.1.3), and elsewhere to the Reinhardt Hamiltonian. `theorem8_2_7`
states this reading (the user's decision): every subarc `(a, b)` of the global minimizer either
contains a subinterval on which the control lies in an edge, and on such an interval the edge arc
has edge costates, none of which has a singular subarc of the edge problem (`IsEdgeSingularSubarc`);
or it contains none, and then no lift is a singular subarc on `(a, b)`.

The edge part holds for every extremal of the edge problem
(`IsEdgeProblemExtremal.not_isEdgeSingularSubarc`: on an edge-singular subarc `λ₂ ≡ 0`, then (8.1.8)
makes `x²` constant, against `x' = y > 0`), the rest by the circle and a localization (on a
singular subarc, near a time with `Λ_R ≠ 0` the maximizers are one edge, so the control lies in
that edge).

Two other readings of the decision were considered and rejected, because they are not provable:

* "Elsewhere" read as "on an interval `(a, b)` on which the control does not lie in a single edge"
  (instead of "on an interval no subinterval of which has the control in an edge"). This brings
  back the open abnormal case: on `(a, b)` the control could alternate between the vertices of the
  edge `{u₀ = 0}` on `(a, c)` and be the vertex `e₀` on `(c, b)` (no single edge contains all
  three vertices), with an abnormal lift conormal to the edge submanifold of `{u₀ = 0}` on
  `(a, c)` and to that of `{u₁ = 0}` (or `{u₂ = 0}`) on `(c, b)`; such a lift is a singular subarc
  on `(a, b)` and is excluded by no argument known here.
* Singularity at a time `t` of an edge interval read pointwise, with *some* edge costate on *some*
  edge interval containing `t` ("the edge Hamiltonian of some edge lift has two maximizers at
  `t`"). This is false in general. Let `u_e ≡ ½` on an edge arc (a vertex control) and
  `x(t) > 0`. The covector `(λ₁, λ₂, λ₃)(t) = (0, 0, x(t)²)` with `ν = -1`, continued by the
  costate equations (8.1.7), has `λ₂(t) = λ₂'(t) = 0` and `λ₂''(t) = -4 x(t)/y(t) < 0`, so
  `λ₂ ≤ 0` near `t`: on a small interval around `t` it is an edge costate (maximum condition
  `λ₂ ≤ 0 ⇒ u_e = ½`, `H_e(t) = 0` and `H_e` constant, `ν ≠ 0`) whose Hamiltonian is independent of
  the control at `t`. Every such `t` would be "singular", so every edge arc with `x > 0` would be
  a singular subarc in this reading.

## Normal lifts: the literal statement

For normal lifts (`λ_cost ≠ 0`) the statement holds as printed:
`not_isSingularSubarc_of_isReinhardtMinimizer_of_isNormalExtremal`. On an interval where the
maximizers are an edge `{u_j = 0}` at every time, the control lies in that edge, and the Reinhardt
costate pulled back to the edge submanifold of (8.1.1) and shifted by `(3/2) λ_cost d(s + x)`
(`edgePullback`, `SmoothedPolygons/Ch8/EdgePullback.lean`) is an edge costate with `H_e = H_R`
(`IsExtremalOn.isEdgeProblemExtremal_edgePullback`), so the edge arc is an edge-singular subarc of
an edge extremal, which is impossible. Intervals that mix edges and all of `U_T` contain, by
continuity, an interval of one of the two kinds; on intervals with `Λ_R ≡ 0` the circle argument
applies.

## Abnormal lifts: the literal statement is open

For abnormal lifts (`λ_cost = 0`) the printed statement (no `IsSingularSubarc` at all, for every
lift of the global minimizer) is neither proved nor refuted, and is not formalized. Along every
trajectory with control in an edge there is a two-parameter family of abnormal costates (the
conormal bundle of the edge submanifold of (8.1.1), which contains Remark 8.1.6's, `remark8_1_6`,
with the sign of gap G4) for which the Hamiltonian vanishes on the edge; the edge is the set of
maximizers where the Hamiltonian at the third vertex is negative. An abnormal lift is
edge-singular on an interval exactly when it is conormal there, and then its pulled-back costate
vanishes, so it gives no edge costate. What is missing is the exclusion of global abnormal lifts
of a global minimizer (with the transversality conditions and the maximum condition on all of
`[0, T]`) that are conormal to an edge submanifold on some interval. No counterexample is known
(none can be exhibited without knowing the minimizer). Theorem 16.3.1 does not depend on it.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-! ### Helpers -/

/-- The Hamiltonian at a fixed control is continuous in time where the costate and the state are,
and `⟨X, Z_v⟩ ≠ 0`. -/
private lemma l3i_continuousAt_hamiltonian {lam : ℝ} {Λ₁ ΛR X : ℝ → Mat2} {t₀ : ℝ}
    (h₁ : ContinuousAt Λ₁ t₀) (hR : ContinuousAt ΛR t₀) (hX : ContinuousAt X t₀)
    {v : Fin 3 → ℝ} (hv : traceForm (X t₀) (controlMatrix v) ≠ 0) :
    ContinuousAt (fun t ↦ hamiltonian lam (Λ₁ t) (ΛR t) (X t) v) t₀ := by
  have hF : ContinuousAt (fun p : Mat2 × Mat2 × Mat2 ↦ hamiltonian lam p.1 p.2.1 p.2.2 v)
      (Λ₁ t₀, ΛR t₀, X t₀) := by
    unfold hamiltonian traceForm
    refine ContinuousAt.sub ?_ (ContinuousAt.div ?_ ?_ hv)
    · exact ((continuous_fst.sub continuous_const).matrix_mul
        (continuous_snd.comp continuous_snd)).matrix_trace.continuousAt
    · exact ((continuous_fst.comp continuous_snd).matrix_mul
        continuous_const).matrix_trace.continuousAt
    · exact ((continuous_snd.comp continuous_snd).matrix_mul
        continuous_const).matrix_trace.continuousAt
  exact ContinuousAt.comp (f := fun t ↦ (Λ₁ t, ΛR t, X t)) hF (h₁.prodMk (hR.prodMk hX))

/-- **Localization on a singular subarc.** Along a Pontryagin extremal, on a singular subarc
`(a, b)` near a time `t₀` with `Λ_R(t₀) ≠ 0`, the maximizers of the Hamiltonian are one edge
`{u_k = 0}` of `U_T` at every time of an interval `(c, d) ∋ t₀`, and the control lies in that edge
almost everywhere there. At `t₀` the maximizers are a vertex or an edge (Lemma 8.2.1), not a
vertex (two maximizers), so an edge `{u_k = 0}`; the vertex `e_k` is strictly worse than `e_{k+1}`
near `t₀` (continuity), so near `t₀` the maximizing edge (Lemma 8.2.1 again) is the one that
misses `e_k`, which is `{u_k = 0}`; the maximum condition puts the control in it. -/
private lemma l3i_exists_edge_of_isSingularSubarc {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ T) (hsing : IsSingularSubarc lam Λ₁ ΛR X a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (hΛ : ΛR t₀ ≠ 0) :
    ∃ (k : Fin 3) (c d : ℝ), a ≤ c ∧ c < d ∧ d ≤ b ∧
      (∀ t ∈ Ioo c d, hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) = controlEdge k) ∧
      ∀ᵐ t, t ∈ Ioo c d → u t k = 0 := by
  obtain ⟨⟨-, -, hu, hgX, -, hXI⟩, -, -, -, -, -, -, hpt, hΛ1I, hΛRI, hae⟩ := hext
  have hXc := Matrix.continuousOn_of_eq_add_integral hXI
  have h1c := Matrix.continuousOn_of_eq_add_integral hΛ1I
  have hRc := Matrix.continuousOn_of_eq_add_integral hΛRI
  have hIcc : ∀ t ∈ Ioo a b, t ∈ Icc 0 T := fun t ht ↦ ⟨ha.trans ht.1.le, ht.2.le.trans hb⟩
  have hden : ∀ t ∈ Icc 0 T, ∀ v ∈ controlSimplex, traceForm (X t) (controlMatrix v) ≠ 0 := by
    intro t ht v hv
    have hs := (hgX t ht).2
    have := (lemma3_3_4 (X t) hs.1).1 ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩ v hv
    rw [poly_traceForm_comm]
    exact this.ne
  -- at a singular time with `Λ_R ≠ 0` the maximizers form an edge
  have hedge : ∀ t ∈ Ioo a b, ΛR t ≠ 0 →
      ∃ k, hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) = controlEdge k := by
    intro t ht hne
    have htI := hIcc t ht
    obtain ⟨-, htrR, hperp, -⟩ := hpt t htI
    rcases (lemma8_2_1 (hgX t htI).2.1 (hden t htI) htrR hperp).2 hne lam (Λ₁ t) with
      ⟨i, hi⟩ | hk
    · exfalso
      obtain ⟨v, hv, w, hw, hvw, hvmax, hwmax⟩ := hsing.2 t ht
      have h1 : v ∈ hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) := ⟨hv, hvmax⟩
      have h2 : w ∈ hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) := ⟨hw, hwmax⟩
      rw [hi] at h1 h2
      exact hvw (h1.trans h2.symm)
    · exact hk
  obtain ⟨k, hk⟩ := hedge t₀ ht₀ hΛ
  have hkk : k + 1 ≠ k := by fin_cases k <;> decide
  -- `e_k` is strictly worse than `e_{k+1}` at `t₀`
  have hlt0 : hamiltonian lam (Λ₁ t₀) (ΛR t₀) (X t₀) (vertex k) <
      hamiltonian lam (Λ₁ t₀) (ΛR t₀) (X t₀) (vertex (k + 1)) := by
    have hf : vertex (k + 1) ∈ hamiltonianArgmax lam (Λ₁ t₀) (ΛR t₀) (X t₀) := by
      rw [hk]; exact vertex_mem_controlEdge hkk
    have he : vertex k ∉ hamiltonianArgmax lam (Λ₁ t₀) (ΛR t₀) (X t₀) := by
      rw [hk]; intro h; simpa [vertex] using h.2
    have : ¬ ∀ v ∈ controlSimplex, hamiltonian lam (Λ₁ t₀) (ΛR t₀) (X t₀) v ≤
        hamiltonian lam (Λ₁ t₀) (ΛR t₀) (X t₀) (vertex k) := fun h ↦ he ⟨poly_vertex_mem k, h⟩
    push Not at this
    obtain ⟨v, hv, hlt⟩ := this
    exact hlt.trans_le (hf.2 v hv)
  -- continuity near `t₀`
  have ht₀I := hIcc t₀ ht₀
  have hmem : Icc 0 T ∈ 𝓝 t₀ :=
    Icc_mem_nhds (ha.trans_lt ht₀.1) (ht₀.2.trans_le hb)
  have hHe := l3i_continuousAt_hamiltonian (lam := lam) (h1c.continuousAt hmem)
    (hRc.continuousAt hmem) (hXc.continuousAt hmem) (hden t₀ ht₀I _ (poly_vertex_mem k))
  have hHf := l3i_continuousAt_hamiltonian (lam := lam) (h1c.continuousAt hmem)
    (hRc.continuousAt hmem) (hXc.continuousAt hmem) (hden t₀ ht₀I _ (poly_vertex_mem (k + 1)))
  have hev : ∀ᶠ t in 𝓝 t₀, (ΛR t ≠ 0 ∧ hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex k) <
      hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex (k + 1))) ∧ t ∈ Ioo a b :=
    (((hRc.continuousAt hmem).eventually_ne hΛ).and (hHe.eventually_lt hHf hlt0)).and
      (Ioo_mem_nhds ht₀.1 ht₀.2)
  obtain ⟨c, d, hcd, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hev
  have hsub' : Ioo (max c a) (min d b) ⊆ Ioo c d := Ioo_subset_Ioo (le_max_left _ _)
    (min_le_left _ _)
  have hc0 : max c a < t₀ := max_lt hcd.1 ht₀.1
  have hd0 : t₀ < min d b := lt_min hcd.2 ht₀.2
  have hargmax : ∀ t ∈ Ioo (max c a) (min d b),
      hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) = controlEdge k := by
    intro t ht
    obtain ⟨⟨hne, hlt⟩, htab⟩ := hsub (hsub' ht)
    obtain ⟨k', hk'⟩ := hedge t htab hne
    rw [hk']
    by_cases hkk' : k' = k
    · rw [hkk']
    · exfalso
      have he : vertex k ∈ hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) := by
        rw [hk']; exact vertex_mem_controlEdge (Ne.symm hkk')
      exact absurd (he.2 _ (poly_vertex_mem (k + 1))) (not_le.2 hlt)
  refine ⟨k, max c a, min d b, le_max_right _ _, hc0.trans hd0, min_le_right _ _, hargmax, ?_⟩
  filter_upwards [hae] with t ht htcd
  have htab := (hsub (hsub' htcd)).2
  have ht0T : t ∈ Ioo 0 T := ⟨ha.trans_lt htab.1, htab.2.trans_le hb⟩
  have hmax : u t ∈ hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) :=
    ⟨hu t (Ioo_subset_Icc_self ht0T), (ht ht0T).2⟩
  rw [hargmax t htcd] at hmax
  exact hmax.2

/-- A **singular subarc of an extremal of the edge control problem** (Definition 6.2.1(3) for the
edge control problem of Definition 8.1.1; the "secondary edge optimal control problem" of
TeX 7300–7302): on the open interval `(α, β)` the maximization of the edge Hamiltonian (8.1.6)
over the control set `[-½, ½]` does not determine the edge control, i.e. at every time it has at
least two maximizers. -/
def IsEdgeSingularSubarc (ν : ℝ) (q : ℝ → Fin 3 → ℝ) (p : ℝ → StrongDual ℝ (Fin 3 → ℝ))
    (α β : ℝ) : Prop :=
  α < β ∧ ∀ t ∈ Ioo α β, ∃ v ∈ edgeControlSet, ∃ w ∈ edgeControlSet, v ≠ w ∧
    (∀ v' ∈ edgeControlSet, Pontryagin.controlHamiltonian edgeField edgeCost ν (q t) (p t) v' ≤
      Pontryagin.controlHamiltonian edgeField edgeCost ν (q t) (p t) v) ∧
    ∀ v' ∈ edgeControlSet, Pontryagin.controlHamiltonian edgeField edgeCost ν (q t) (p t) v' ≤
      Pontryagin.controlHamiltonian edgeField edgeCost ν (q t) (p t) w

/-- **An extremal of the edge control problem has no singular subarc** (the argument of steps 4
and 6 of the proof of Theorem 8.1.4, TeX 6846–6894).

Proof: by (8.1.6) (`eqn_edge_ham`) only `λ₂ f₂(x, y, u_e)` depends on the control, and `f₂` is
injective in `u_e` on `[-½, ½]` (strictly decreasing,
`IsEdgeProblemExtremal.ae_control_eq_of_switching`; here by cross-multiplication), so two distinct
maximizers at `t` force `λ₂(t) = 0`. On an edge-singular subarc `(α, β)`, `λ₂ ≡ 0`, so `λ₂` has
derivative `0` at every `t ∈ (α, β)` and (8.1.8) (`eqn_edge_zero`) gives `ν ≠ 0` and
`x(t)² = -λ₃/ν`, a constant (`λ₃` is constant, `eqn_costate_edge`). But `x' = y > 0` (admissibility
in `edgeDomain`) makes `x` strictly increasing, so it takes three distinct values on `(α, β)`, which
cannot have the same square. -/
theorem IsEdgeProblemExtremal.not_isEdgeSingularSubarc {T : ℝ} {ue : ℝ → ℝ}
    {q : ℝ → Fin 3 → ℝ} {ν : ℝ} {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)}
    (h : IsEdgeProblemExtremal T ue q ν p) {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ T) :
    ¬ IsEdgeSingularSubarc ν q p α β := by
  rintro ⟨hαβ, hsing⟩
  have hext := h
  obtain ⟨hT, ⟨⟨-, -, hcont, hint, hq⟩, hdom⟩, -, -, -, -, -⟩ := h
  have hl3 := (eqn_costate_edge hext).1
  have hI : ∀ t ∈ Ioo α β, t ∈ Icc 0 T := fun t ht ↦ ⟨hα.trans ht.1.le, ht.2.le.trans hβ⟩
  -- two maximizers force `λ₂ = 0`: `f₂` is injective in the control
  have hz : ∀ t ∈ Ioo α β, edgeCostate (p t) 1 = 0 := by
    intro t ht
    obtain ⟨hy, hx1, hx2⟩ := hdom t (hI t ht)
    obtain ⟨v, hv, w, hw, hvw, hvmax, hwmax⟩ := hsing t ht
    have heq := le_antisymm (hwmax v hv) (hvmax w hw)
    rw [eqn_edge_ham, eqn_edge_ham] at heq
    simp only [edgeHamiltonian] at heq
    by_contra hne
    have hf : edgeF₂ (q t 0) (q t 1) v = edgeF₂ (q t 0) (q t 1) w :=
      mul_left_cancel₀ hne (by linarith)
    have hDv := (edgeF₂_denom_neg hx1 hx2 hv).ne
    have hDw := (edgeF₂_denom_neg hx1 hx2 hw).ne
    simp only [edgeF₂] at hf
    rw [div_eq_div_iff hDv hDw] at hf
    apply hvw
    have hy2 : 2 * √3 * q t 1 ^ 2 ≠ 0 := mul_ne_zero (by positivity) (pow_ne_zero 2 hy.ne')
    apply mul_left_cancel₀ hy2
    linear_combination -hf
  -- (8.1.8) at every time of `(α, β)`
  have hz2 : ∀ t ∈ Ioo α β, edgeCostate (p t) 2 = -(q t 0) ^ 2 * ν ∧ ν ≠ 0 := by
    intro t ht
    have hd : HasDerivWithinAt (fun s ↦ edgeCostate (p s) 1) 0 (Icc 0 T) t := by
      refine ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_).hasDerivWithinAt
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using hz s hs
    obtain ⟨h1, -, h2⟩ := eqn_edge_zero hext (hI t ht) (hz t ht) hd
    exact ⟨h1, h2⟩
  have hν : ν ≠ 0 := (hz2 ((α + β) / 2) ⟨by linarith, by linarith⟩).2
  have hsq : ∀ t ∈ Ioo α β, (q t 0) ^ 2 = -edgeCostate (p 0) 2 / ν := by
    intro t ht
    rw [← hl3 t (hI t ht), (hz2 t ht).1]
    field_simp
  -- `x` is strictly increasing (`x' = y > 0`)
  have hx : ∀ t ∈ Icc 0 T, q t 0 = q 0 0 + ∫ s in (0 : ℝ)..t, q s 1 := by
    intro t ht
    have h1 := congrFun (hq t ht) 0
    have hsub : IntervalIntegrable (fun s ↦ edgeField (q s) (ue s)) volume 0 t :=
      hint.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le hT.le]; exact Icc_subset_Icc le_rfl ht.2)
    rw [Pi.add_apply, intervalIntegral.eval_integral hsub] at h1
    simpa [edgeField] using h1
  have hycont : ContinuousOn (fun s ↦ q s 1) (Icc 0 T) :=
    (continuous_apply 1).comp_continuousOn hcont
  have hmono : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s < t → q s 0 < q t 0 := by
    intro s hs t ht hst
    have h0s : IntervalIntegrable (fun σ ↦ q σ 1) volume 0 s :=
      (hycont.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1
    have hst' : IntervalIntegrable (fun σ ↦ q σ 1) volume s t :=
      (hycont.mono (Icc_subset_Icc hs.1 ht.2)).intervalIntegrable_of_Icc hst.le
    rw [hx s hs, hx t ht, ← intervalIntegral.integral_add_adjacent_intervals h0s hst']
    have : 0 < ∫ σ in s..t, q σ 1 := intervalIntegral.intervalIntegral_pos_of_pos_on hst'
      (fun σ hσ ↦ (hdom σ ⟨hs.1.trans hσ.1.le, hσ.2.le.trans ht.2⟩).1) hst
    linarith
  -- three times of `(α, β)` with strictly increasing `x` and equal `x²`
  have h₁ : α + (β - α) / 4 ∈ Ioo α β := ⟨by linarith, by linarith⟩
  have h₂ : α + (β - α) / 2 ∈ Ioo α β := ⟨by linarith, by linarith⟩
  have h₃ : α + 3 * (β - α) / 4 ∈ Ioo α β := ⟨by linarith, by linarith⟩
  have m₁ := hmono _ (hI _ h₁) _ (hI _ h₂) (by linarith)
  have m₂ := hmono _ (hI _ h₂) _ (hI _ h₃) (by linarith)
  have e₁ := hsq _ h₁
  have e₂ := hsq _ h₂
  have e₃ := hsq _ h₃
  have f₁ : (q (α + (β - α) / 2) 0 - q (α + (β - α) / 4) 0) *
      (q (α + (β - α) / 2) 0 + q (α + (β - α) / 4) 0) = 0 := by linear_combination e₂ - e₁
  have f₂ : (q (α + 3 * (β - α) / 4) 0 - q (α + (β - α) / 2) 0) *
      (q (α + 3 * (β - α) / 4) 0 + q (α + (β - α) / 2) 0) = 0 := by linear_combination e₃ - e₂
  rcases mul_eq_zero.1 f₁ with g₁ | g₁ <;> rcases mul_eq_zero.1 f₂ with g₂ | g₂ <;> linarith

/-- **Theorem 8.2.7, the case its proof covers**: a lift of a global minimizer has no singular
subarc on which the Hamiltonian is independent of the control (equivalently, by Theorem 8.2.6, the
lift does not stay in the singular locus on any open interval). This is the part of
Theorem 8.2.7 used by Theorem 16.3.1.

Proof (the book's, TeX 7320–7391): by Theorem 8.2.6 (`theorem8_2_6`, applied to the restriction
`IsPontryaginExtremal.isExtremalOn`) the subarc is a circular arc, `X ≡ J` on `[a, b]`;
by the second variation (`l3st_exists_lt_cost_of_circleArc`) some admissible trajectory has
smaller cost, against minimality. -/
theorem not_forall_hamiltonian_eq_of_isReinhardtMinimizer {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X) {Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ T) :
    ¬ ∀ t ∈ Ioo a b, ∀ v ∈ controlSimplex, ∀ w ∈ controlSimplex,
      hamiltonian lam (Λ₁ t) (ΛR t) (X t) v = hamiltonian lam (Λ₁ t) (ΛR t) (X t) w := by
  intro hconst
  have hE := IsPontryaginExtremal.isExtremalOn hext ha hab hb
  have hv01 : vertex 0 ≠ vertex 1 := by
    intro h
    simpa [vertex] using congrFun h 0
  have hsing : IsSingularSubarc lam Λ₁ ΛR X a b :=
    ⟨hab, fun t ht ↦ ⟨vertex 0, poly_vertex_mem 0, vertex 1, poly_vertex_mem 1, hv01,
      fun v' hv' ↦ (hconst t ht v' hv' _ (poly_vertex_mem 0)).le,
      fun v' hv' ↦ (hconst t ht v' hv' _ (poly_vertex_mem 1)).le⟩⟩
  obtain ⟨hS, -, -⟩ := theorem8_2_6.1 hE le_rfl le_rfl hsing hconst
  have hX : ∀ t ∈ Icc a b, X t = J := fun t ht ↦ by
    obtain ⟨μ, -, -, -, hXJ, -⟩ := hS t ht
    exact hXJ
  obtain ⟨T', u', g', X', hadm, hlt⟩ := l3st_exists_lt_cost_of_circleArc hmin.1 ha hab hb hX
  exact absurd (hmin.2 T' u' g' X' hadm) (not_le.2 hlt)

/-- **Theorem 8.2.7** (`thm:no-singular-arcs`), in the authors' reading: the global minimizer of
the Reinhardt problem contains no subarc on which its control is not determined by maximization,
where on an interval with the control in an edge of `U_T` maximization refers to the Hamiltonian of
the edge control problem, and elsewhere to the Reinhardt Hamiltonian (module docstring; TeX
7300–7302, 7312–7313, 806–821). For a global minimizer and an interval `(a, b) ⊆ [0, T]`:

1. if the control lies in the edge `{u_j = 0}` almost everywhere on `(a, b)`, the edge arc
   `(edgeParam j u, edgeState j X a)` has an edge costate (Proposition 8.1.3: the minimizer is
   edge extremal), and no edge costate of it has a singular subarc of the edge problem
   (`IsEdgeSingularSubarc`) in `[0, b - a]`;
2. if the control lies in no edge on any subinterval of `(a, b)`, no lift of the minimizer to a
   Pontryagin extremal is a singular subarc (`IsSingularSubarc`) on `(a, b)`.

Every subarc either contains a subinterval of the first kind (part 1 applies to it) or is of the
second kind, so in either case the control is determined by the relevant maximization somewhere on
it. The literal statement (`IsSingularSubarc` excluded for every lift on every interval) holds for
normal lifts (`not_isSingularSubarc_of_isReinhardtMinimizer_of_isNormalExtremal`) and is open for
abnormal lifts (module docstring).

Proof:
1. Existence: `proposition8_1_3` (edge extremality on `[0, T]`, applied to `[a, b]`). No singular
   subarc: `IsEdgeProblemExtremal.not_isEdgeSingularSubarc` (Theorem 8.1.4's argument).
2. Suppose a lift is a singular subarc on `(a, b)`. If `Λ_R(t₀) ≠ 0` for some `t₀ ∈ (a, b)`, then
   at `t₀` the maximizers are an edge `{u_k = 0}` (Lemma 8.2.1, `lemma8_2_1`; two maximizers
   exclude a vertex), the third vertex `e_k` is strictly worse near `t₀` (continuity of
   the lift), so near `t₀` the maximizers are that same edge (Lemma 8.2.1 again,
   with `Λ_R ≠ 0` near `t₀`), and the maximum condition puts the control in it almost everywhere
   on a subinterval, against the hypothesis. So `Λ_R ≡ 0` on `(a, b)`, the Hamiltonian is
   independent of the control there, against `not_forall_hamiltonian_eq_of_isReinhardtMinimizer`
   (Theorems 8.2.6 and 8.2.3, the second variation).
The localization of step 2 is shared with
`not_isSingularSubarc_of_isReinhardtMinimizer_of_isNormalExtremal`. -/
theorem theorem8_2_7 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T) :
    (∀ j : Fin 3, (∀ᵐ t, t ∈ Ioo a b → u t j = 0) →
      (∃ (ν : ℝ) (p : ℝ → StrongDual ℝ (Fin 3 → ℝ)),
        IsEdgeProblemExtremal (b - a) (fun t ↦ edgeParam j (u (a + t))) (edgeState j X a) ν p) ∧
      ∀ (ν : ℝ) (p : ℝ → StrongDual ℝ (Fin 3 → ℝ)),
        IsEdgeProblemExtremal (b - a) (fun t ↦ edgeParam j (u (a + t))) (edgeState j X a) ν p →
        ∀ α β : ℝ, 0 ≤ α → β ≤ b - a → ¬ IsEdgeSingularSubarc ν (edgeState j X a) p α β) ∧
    ((∀ (j : Fin 3) (c d : ℝ), a ≤ c → c < d → d ≤ b → ¬ ∀ᵐ t, t ∈ Ioo c d → u t j = 0) →
      ∀ (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ), IsPontryaginExtremal T u g X Λ₁ ΛR lam →
        ¬ IsSingularSubarc lam Λ₁ ΛR X a b) := by
  refine ⟨fun j hu ↦ ⟨(proposition8_1_3 hmin).2 j a b ha hab hb hu,
    fun ν p hp α β hα hβ ↦ hp.not_isEdgeSingularSubarc hα hβ⟩, ?_⟩
  intro hno Λ₁ ΛR lam hext hsing
  by_cases hR : ∃ t₀ ∈ Ioo a b, ΛR t₀ ≠ 0
  · obtain ⟨t₀, ht₀, hne⟩ := hR
    obtain ⟨k, c, d, hac, hcd, hdb, -, hu⟩ :=
      l3i_exists_edge_of_isSingularSubarc hext ha hb hsing ht₀ hne
    exact hno k c d hac hcd hdb hu
  · push Not at hR
    refine not_forall_hamiltonian_eq_of_isReinhardtMinimizer hmin hext ha hab hb ?_
    intro t ht v _ w _
    simp [hamiltonian, hR t ht, traceForm]

/-- **Theorem 8.2.7 for normal lifts, as printed**: a lift of a global minimizer to a normal
Pontryagin extremal (`λ_cost ≠ 0`, Definition 6.2.1(2)) has no singular subarc
(Definition 6.2.1(3)) at all. This is the repair, along the book's lines, of gap G8 for normal
lifts (module docstring); for abnormal lifts the printed statement is open.

Proof:
1. Suppose the lift is a singular subarc on `(a, b)`. If `Λ_R ≡ 0` on `(a, b)`, the Hamiltonian is
   independent of the control there: `not_forall_hamiltonian_eq_of_isReinhardtMinimizer`.
2. Otherwise, as in step 2 of `theorem8_2_7`, there are an edge `{u_k = 0}` and `[c, d] ⊆ (a, b)`,
   `c < d`, on which the maximizers of the Reinhardt Hamiltonian are that edge at every time and
   the control lies in it almost everywhere.
3. The pulled-back costate (`IsExtremalOn.isEdgeProblemExtremal_edgePullback`, on the restriction
   `IsPontryaginExtremal.isExtremalOn` to `[c, d]`, with `λ_cost ≠ 0`) is an edge costate
   of the edge arc, with `H_e(v) = H_R(edgeControlIn k v)`
   (`IsExtremalOn.controlHamiltonian_edgePullback`). Two distinct maximizers of `H_R` in the edge
   give two distinct maximizers of `H_e` in `[-½, ½]` (their edge parameters), at every time of
   `(0, d - c)`: an edge-singular subarc, against
   `IsEdgeProblemExtremal.not_isEdgeSingularSubarc` (`λ₂ ≡ 0`, then (8.1.8) makes `x²` constant,
   against `x' = y > 0`). -/
theorem not_isSingularSubarc_of_isReinhardtMinimizer_of_isNormalExtremal {T : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X)
    {Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (hext : IsNormalExtremal T u g X Λ₁ ΛR lam) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ T) :
    ¬ IsSingularSubarc lam Λ₁ ΛR X a b := by
  intro hsing
  obtain ⟨hext, hlam⟩ := hext
  have hab := hsing.1
  by_cases hR : ∃ t₀ ∈ Ioo a b, ΛR t₀ ≠ 0
  · obtain ⟨t₀, ht₀, hne⟩ := hR
    obtain ⟨k, c, d, hac, hcd, hdb, hmax, hu⟩ :=
      l3i_exists_edge_of_isSingularSubarc hext ha hb hsing ht₀ hne
    have hE := IsPontryaginExtremal.isExtremalOn hext (ha.trans hac) hcd (hdb.trans hb)
    have hpe := hE.isEdgeProblemExtremal_edgePullback hlam hu
    have hHe := hE.controlHamiltonian_edgePullback hu
    refine hpe.not_isEdgeSingularSubarc le_rfl le_rfl ⟨sub_pos.2 hcd, fun τ hτ ↦ ?_⟩
    have ht : c + τ ∈ Ioo c d := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have htab : c + τ ∈ Ioo a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hτI : τ ∈ Icc 0 (d - c) := ⟨hτ.1.le, hτ.2.le⟩
    obtain ⟨v, hv, w, hw, hvw, hvmax, hwmax⟩ := hsing.2 (c + τ) htab
    have hvE : v ∈ controlEdge k := by rw [← hmax _ ht]; exact ⟨hv, hvmax⟩
    have hwE : w ∈ controlEdge k := by rw [← hmax _ ht]; exact ⟨hw, hwmax⟩
    refine ⟨edgeParam k v, edgeParam_mem_edgeControlSet hv, edgeParam k w,
      edgeParam_mem_edgeControlSet hw, ?_, ?_, ?_⟩
    · intro h
      apply hvw
      rw [← edgeControlIn_edgeParam hvE, ← edgeControlIn_edgeParam hwE, h]
    · intro v' hv'
      rw [hHe τ hτI v' hv', hHe τ hτI _ (edgeParam_mem_edgeControlSet hv),
        edgeControlIn_edgeParam hvE]
      exact hvmax _ (edgeControlIn_mem_controlSimplex hv')
    · intro v' hv'
      rw [hHe τ hτI v' hv', hHe τ hτI _ (edgeParam_mem_edgeControlSet hw),
        edgeControlIn_edgeParam hwE]
      exact hwmax _ (edgeControlIn_mem_controlSimplex hv')
  · push Not at hR
    refine not_forall_hamiltonian_eq_of_isReinhardtMinimizer hmin hext ha hab hb ?_
    intro t ht v _ w _
    simp [hamiltonian, hR t ht, traceForm]

end SmoothedPolygons
