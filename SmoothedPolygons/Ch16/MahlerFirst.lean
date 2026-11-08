module

public import SmoothedPolygons.Ch8.EdgeExtremal
public import SmoothedPolygons.Ch8.NoSingularArcs
public import SmoothedPolygons.Ch8.VertexControl
public import SmoothedPolygons.Ch8.PolygonBoundary
public import SmoothedPolygons.Ch6.WorstDisk

/-!
# Mahler's First conjecture, conditional on one named hypothesis (Theorem 16.3.1)

Theorem 16.3.1 (`thm:mahler`, TeX 12789–12795), Mahler's First conjecture: "The global minimizer of
the Reinhardt optimal control problem is a bang-bang solution with finitely many switches. In
particular, the minimizer `K_min` of the Reinhardt problem is a finite-sided smoothed polygon with
rounded hyperbolic arcs at each corner of the sort described by Reinhardt and Mahler."

The book's proof (TeX 12806–12833) is one paragraph. Its first steps use Chapter 8: the minimizer
is extremal and edge extremal (Proposition 8.1.3), so it is bang-bang with finitely many switches
on any interval avoiding the singular locus (Theorem 8.3.2); it cannot stay in the singular locus
for a positive time (Theorem 8.2.7) and cannot reach it with finitely many switches (Lemma 8.3.4).
The last step excludes switching times accumulating at a time where the lift meets the singular
locus, by Theorem 16.4.1 (cluster point, with §16.4.2) and Theorem 14.4.1 (no return) and their
time reversals, with the periodicity of the extremal. Those theorems (Chapters 13–16) are proved in
later layers; here their consequence, in the form the last step uses, is the named hypothesis
`NoChatteringIntoSingularLocus`, a hypothesis of `theorem16_3_1`.

* `NoChatteringIntoSingularLocus`: no Pontryagin extremal of the Reinhardt problem (with its
  boundary conditions) has switching times accumulating, from the left, at a time where its lift
  meets `𝒮_sing`, while being bang-bang off `𝒮_sing` before that time.
* `isFiniteBangBang_of_isReinhardtMinimizer_of_not_mem_singularLocus`: the unconditional
  consequence, the minimizer is bang-bang with finitely many switches on every compact interval on
  which its lift avoids `𝒮_sing` (Theorem 8.3.2 with Proposition 8.1.3).
* `l3st_forall_not_mem_singularLocus`: under the hypothesis, the lift of a global minimizer never
  meets `𝒮_sing` (the core of the proof).
* `theorem16_3_1`: both sentences of Theorem 16.3.1, under the hypothesis.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- `τ` is a **switching time** of the control `u`: near `τ` the control is almost everywhere
constant at a vertex of `U_T` on each side of `τ`, with different vertices on the two sides ("the
control function is necessarily discontinuous where it jumps from one vertex to another",
TeX 5835–5836). -/
def IsSwitchingTime (u : ℝ → Fin 3 → ℝ) (τ : ℝ) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ ∃ ε > 0, (∀ᵐ t, t ∈ Ioo (τ - ε) τ → u t = vertex i) ∧
    ∀ᵐ t, t ∈ Ioo τ (τ + ε) → u t = vertex j

/-- **The lifted trajectory chatters into the time `t` from the left**: on some interval
`(t - δ, t)` the control is bang-bang with finitely many switches on every compact subinterval and
the lift avoids the singular locus, and the switching times accumulate at `t` (every `(t - ε, t)`
contains one). This is the configuration of Theorem 16.4.1 ("the sequence of switching points
… has a cluster point … reached in finite time, and … the switching points themselves are not on
the exceptional divisor") when the lift is in `𝒮_sing` at `t`. -/
def IsChatteringInto (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (t : ℝ) : Prop :=
  ∃ δ > 0, (∀ α β, t - δ < α → β < t → IsFiniteBangBang α β u) ∧
    (∀ τ ∈ Ioo (t - δ) t, (g τ, Λ₁ τ, X τ, ΛR τ) ∉ singularLocus) ∧
    ∀ ε > 0, ∃ τ ∈ Ioo (t - ε) t, IsSwitchingTime u τ

/-- **The named hypothesis of Mahler's First conjecture: no chattering into the singular locus.**
For every Pontryagin extremal of the Reinhardt problem on `[0, T]` (`IsPontryaginExtremal`, which
includes the boundary conditions of Problem 3.6.2 and the transversality conditions (6.6.1)) and
every time `t ∈ (0, T]` at which its lift `(g, Λ₁, X, Λ_R)` meets the singular locus `𝒮_sing`, the
switching times of the control do not accumulate at `t` from the left while the trajectory is
bang-bang off `𝒮_sing` before `t` (`IsChatteringInto`).

**Why it is what Theorems 16.4.1 and 14.4.1 give.** This is the configuration of the last step of
the proof of Theorem 16.3.1 (TeX 12820–12833): "a trajectory such that the infinite sequence of
switching points has a subsequence tending to the singular locus", in finite time. The book
excludes it as follows, and the later layers of this formalization prove the hypothesis along
these lines:
1. At the limit time `t` the lift is in `𝒮_sing`, so the extremal is normal (`λ_cost ≠ 0`,
   `IsExtremalOn.mem_singularLocus_iff`; Lemma 8.2.2), and the costate may be normalized to
   `λ_cost = -1`, the normalization of Chapters 11–16.
2. Passing to the blow-up of `𝒮_sing` (§13.4, §16.4.1; the exceptional divisor is compact), the
   switching points, which are not on `𝒮_sing`, have a cluster point on the exceptional divisor,
   reached at the finite time `t`.
3. Theorem 16.4.1 (`thm:no-chatter`): the cluster point is the fixed point `q_in` and the switching
   points lie on the stable curve `W^s(q_in)`.
4. Theorem 14.4.1 (`thm:no-return`) and its time reversal: a trajectory that tends to `q_in` on the
   exceptional divisor did not emanate at an earlier time from the exceptional divisor.
5. Periodicity: by the transversality conditions the extremal extends periodically
   (Remark 6.6.1, `remark6_6_1`), and `𝒮_sing` is invariant under the rotation (`R` commutes with
   `J`), so the extension meets `𝒮_sing` at `t + T` again, chattering into it from the left; on
   `(e, t + T)`, with `e` the last time before `t + T - δ` in `𝒮_sing`, the trajectory emanates from
   the divisor and then tends to `q_in`, against step 4 ("Thus, the trajectory is not periodic.
   This is contrary to the boundary conditions of the Reinhardt conjecture").
The hypothesis is stated for every Pontryagin extremal that is edge extremal on `[0, T]`
(Definition 8.1.2): the book uses the argument only for the minimizer, which is edge extremal by
Proposition 8.1.3 (`proposition8_1_3`), and the proof of Theorem 14.4.1 needs the excursion
`(e, t + T)` to be bang-bang, which Chapter 8 gives only under edge extremality (Theorem 8.3.2).
Restricting to edge extremals makes the hypothesis weaker, so it asks no more than the book
proves. It concerns only extremals with their boundary conditions (locally, chattering into
`𝒮_sing` does occur: the inward spirals along `W^s(q_in)` of Chapters 13–16).

**Why it is not an axiom.** It is a `Prop`, a hypothesis of `theorem16_3_1`, visible in its
statement; nothing in the library assumes it. `theorem16_3_1` reads "`NoChatteringIntoSingularLocus`
implies Mahler's First conjecture", and its axioms are Lean's standard ones once its proof is
complete. The later layers replace the hypothesis by a proof (Theorems 16.4.1 and 14.4.1).

**Why it suffices** (`l3st_forall_not_mem_singularLocus`): with Chapters 2–8 it rules out every
meeting of the minimizer's lift with `𝒮_sing`; the minimizer is then bang-bang with finitely many
switches by Theorem 8.3.2. -/
def NoChatteringIntoSingularLocus : Prop :=
  ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ),
    IsPontryaginExtremal T u g X Λ₁ ΛR lam → IsEdgeExtremalOn 0 T u X → ∀ t ∈ Ioc 0 T,
      (g t, Λ₁ t, X t, ΛR t) ∈ singularLocus → ¬ IsChatteringInto u g X Λ₁ ΛR t

/-! ### Helpers: locally constant vertex controls -/

/-- **A time inside an interval of finite bang-bang control that is not a switching time has a
neighbourhood on which the control is one vertex.** Off the finite exceptional set the control is
locally a vertex; on each side of the time, next to it, it is therefore one vertex
(`exists_ae_eq_vertex_of_locally`), and the two vertices agree because the time is not a
switching time. -/
private lemma l3m_local_vertex {u : ℝ → Fin 3 → ℝ} {α β t : ℝ} (hbb : IsFiniteBangBang α β u)
    (ht : t ∈ Ioo α β) (hsw : ¬ IsSwitchingTime u t) :
    ∃ i : Fin 3, ∃ η > 0, ∀ᵐ τ, τ ∈ Ioo (t - η) (t + η) → u τ = vertex i := by
  obtain ⟨S, hS⟩ := hbb
  -- a neighbourhood of `t` inside `(α, β)` with no point of `S` other than `t`
  have hfin : ((S.erase t : Finset ℝ) : Set ℝ)ᶜ ∈ 𝓝 t :=
    (S.erase t).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.mem_nhds_iff.1 hfin
  set ρ := min ρ₀ (min (t - α) (β - t)) with hρ
  have hρ1 : ρ ≤ ρ₀ := min_le_left _ _
  have hρ2 : ρ ≤ t - α := (min_le_right _ _).trans (min_le_left _ _)
  have hρ3 : ρ ≤ β - t := (min_le_right _ _).trans (min_le_right _ _)
  have hρpos : 0 < ρ := lt_min hρ₀ (lt_min (by linarith [ht.1]) (by linarith [ht.2]))
  have hloc : ∀ s ∈ Ioo (t - ρ) (t + ρ), s ≠ t →
      ∃ i : Fin 3, ∃ η > 0, ∀ᵐ τ, τ ∈ Ioo (s - η) (s + η) → u τ = vertex i := by
    intro s hs hst
    refine hS s ⟨by linarith [hs.1], by linarith [hs.2]⟩ fun hsS ↦ ?_
    have hsb : s ∈ Metric.ball t ρ₀ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    exact hball hsb (by simp [hsS, hst])
  obtain ⟨i, hi⟩ := exists_ae_eq_vertex_of_locally (α := t - ρ) (β := t) fun s hs ↦
    hloc s ⟨hs.1, by linarith [hs.2]⟩ hs.2.ne
  obtain ⟨j, hj⟩ := exists_ae_eq_vertex_of_locally (α := t) (β := t + ρ) fun s hs ↦
    hloc s ⟨by linarith [hs.1], hs.2⟩ hs.1.ne'
  obtain rfl : i = j := by
    by_contra hij
    exact hsw ⟨i, j, hij, ρ, hρpos, hi, hj⟩
  refine ⟨i, ρ, hρpos, ?_⟩
  have hne : ∀ᵐ τ : ℝ, τ ≠ t := by
    rw [ae_iff]
    simp
  filter_upwards [hi, hj, hne] with τ h1 h2 h3 hτ
  rcases lt_or_gt_of_ne h3 with h | h
  · exact h1 ⟨hτ.1, h⟩
  · exact h2 ⟨h, hτ.2⟩

/-- **The minimizer is bang-bang with finitely many switches away from the singular locus**
(label of this formalization `thm:mahler:away`; the part of Theorem 16.3.1 that holds without the
hypothesis, TeX 12811–12815). Let `(g, X)` be a global minimizer of the Reinhardt problem and
`(Λ₁, Λ_R, λ_cost)` a lift of it to a Pontryagin extremal. On every interval `[a, b] ⊆ [0, T]` on
which the lift does not meet `𝒮_sing`, the control is bang-bang with finitely many switches.

Proof: Proposition 8.1.3 (`proposition8_1_3`: the minimizer is edge extremal on `[0, T]`, so on
`[a, b]`, `IsEdgeExtremalOn.mono`), the restriction of the extremal to `[a, b]`
(`IsPontryaginExtremal.isExtremalOn`), and Theorem 8.3.2 (`theorem8_3_2`). -/
theorem isFiniteBangBang_of_isReinhardtMinimizer_of_not_mem_singularLocus {T : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X)
    {Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
    (hS : ∀ t ∈ Icc a b, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus) :
    IsFiniteBangBang a b u :=
  theorem8_3_2 (IsPontryaginExtremal.isExtremalOn hext ha hab hb)
    (IsEdgeExtremalOn.mono (proposition8_1_3 hmin).2 ha hb) hS

/-- **Under the hypothesis, the lift of a global minimizer never meets the singular locus** (the
core of the proof of Theorem 16.3.1, TeX 12811–12833, with E60's gap repaired: the set of meeting
times could a priori be infinite and nowhere dense, and the proof works on a complementary
interval).

Proof:
1. `Z = {t ∈ [0, T] | lift(t) ∈ 𝒮_sing}` is closed (`IsExtremalOn.mem_singularLocus_iff`,
   `IsExtremalOn.continuousOn_lift`). Suppose `Z ≠ ∅`.
2. `Z ∩ (0, T] ≠ ∅`: if `0 ∈ Z` then `T ∈ Z`, since `X(T) = R⁻¹X(0)R`, `Λ₁(T) = R⁻¹Λ₁(0)R`,
   `Λ_R(T) = R⁻¹Λ_R(0)R` and `R⁻¹JR = J`.
3. `Z` has empty interior ("A trajectory cannot remain on the singular locus for any positive
   interval of time by Theorem 8.2.7"): on an open interval `(0, z)` inside `Z`, `Λ_R ≡ 0`, so by
   Theorem 8.2.3 (`theorem8_2_3`) the interval is a singular subarc and the control is the
   centre `(⅓, ⅓, ⅓)` of `U_T` almost everywhere; in particular no subinterval has its control
   in an edge, and Theorem 8.2.7 (`theorem8_2_7`, its part for such intervals) says that the
   interval is not a singular subarc.
4. Take `z ∈ Z ∩ (0, T]`, `p ∈ (0, z) ∖ Z` (step 3), and `d = inf (Z ∩ [p, T])`: `d ∈ Z`,
   `p < d ≤ z`, and `[p, d)` avoids `Z`.
5. On every compact `[α, β] ⊆ (p, d)` the control is bang-bang with finitely many switches
   (`isFiniteBangBang_of_isReinhardtMinimizer_of_not_mem_singularLocus`: Proposition 8.1.3 and
   Theorem 8.3.2).
6. The hypothesis (`NoChatteringIntoSingularLocus` at `d`, with `δ = d - p`) gives `ε > 0` with no
   switching time in `(d - ε, d)`; with step 5, the control is a.e. constant at one vertex on
   `(d - ε', d)` (the vertex cannot change across a point that is not a switching time, and
   `(d - ε', d)` is connected).
7. Lemma 8.3.4 (`lemma8_3_4`) on `[d - ε', d]` (`IsPontryaginExtremal.isExtremalOn`): the
   lift does not meet `𝒮_sing` at `d` ("A trajectory cannot reach the singular locus with finitely
   many switches"), against `d ∈ Z`.

The step "with step 5, the control is a.e. constant at one vertex" is `l3m_local_vertex` (near each
time of `(d - ε', d)`: on each side the control is one vertex, by connectedness, and the two agree
since the time is not a switching time) and `exists_ae_eq_vertex_of_locally` (a locally constant
vertex control is constant on an interval: connectedness, and a locally null set is null). -/
private theorem l3st_forall_not_mem_singularLocus (hNC : NoChatteringIntoSingularLocus) {T : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X)
    {Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) :
    ∀ t ∈ Icc 0 T, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus := by
  have hT : 0 < T := hmin.1.1.1
  have hedge : IsEdgeExtremalOn 0 T u X := (proposition8_1_3 hmin).2
  have h0T : IsExtremalOn 0 T u g X Λ₁ ΛR lam :=
    IsPontryaginExtremal.isExtremalOn hext le_rfl hT le_rfl
  intro t₀ ht₀ hmem
  have hlam : lam ≠ 0 := ((IsExtremalOn.mem_singularLocus_iff h0T ht₀).1 hmem).1
  have hZ : ∀ t ∈ Icc 0 T, (g t, Λ₁ t, X t, ΛR t) ∈ singularLocus ↔
      Λ₁ t = (3 / 2 * lam) • J ∧ X t = J ∧ ΛR t = 0 := fun t ht ↦ by
    rw [IsExtremalOn.mem_singularLocus_iff h0T ht]
    exact and_iff_right hlam
  -- Step 2: a meeting time in `(0, T]` (by the transversality conditions, `R⁻¹JR = J`)
  obtain ⟨z, hz, hzS⟩ : ∃ z ∈ Ioc 0 T, (g z, Λ₁ z, X z, ΛR z) ∈ singularLocus := by
    rcases ht₀.1.lt_or_eq with h | h
    · exact ⟨t₀, ⟨h, ht₀.2⟩, hmem⟩
    · subst h
      obtain ⟨h1, hX, hR⟩ := (hZ 0 ht₀).1 hmem
      have hext' := hext
      obtain ⟨-, -, -, hXT, h1T, hRT, -⟩ := hext'
      refine ⟨T, ⟨hT, le_rfl⟩, (hZ T ⟨hT.le, le_rfl⟩).2 ⟨?_, ?_, ?_⟩⟩
      · rw [h1T, h1, Matrix.mul_smul, Matrix.smul_mul, R_inv_mul_J_mul_R]
      · rw [hXT, hX, R_inv_mul_J_mul_R]
      · rw [hRT, hR, Matrix.mul_zero, Matrix.zero_mul]
  -- Step 3: the meeting times have empty interior (Theorem 8.2.7, with Theorem 8.2.3)
  obtain ⟨p, hp, hpS⟩ : ∃ p ∈ Ioo 0 z, (g p, Λ₁ p, X p, ΛR p) ∉ singularLocus := by
    by_contra hcon
    push Not at hcon
    -- on `(0, z)` the lift is in `𝒮_sing`, so `Λ_R ≡ 0` there
    have hR : ∀ t ∈ Ioo 0 z, ΛR t = 0 := fun t ht ↦
      ((hZ t ⟨ht.1.le, ht.2.le.trans hz.2⟩).1 (hcon t ht)).2.2
    -- Theorem 8.2.3: `(0, z)` is a singular subarc, with the centre of `U_T` as control a.e.
    obtain ⟨-, hcentre, -, -, hsing⟩ := theorem8_2_3 h0T le_rfl hz.1 hz.2 hR
    -- so no subinterval of `(0, z)` has its control in an edge
    have hno : ∀ (j : Fin 3) (c d : ℝ), 0 ≤ c → c < d → d ≤ z →
        ¬ ∀ᵐ t, t ∈ Ioo c d → u t j = 0 := by
      intro j c d hc hcd hd hu
      have hnull : volume (Ioo c d) = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [hu, hcentre] with t h1 h2 ht
        have h0 := h1 ht
        rw [(h2 ⟨hc.trans_lt ht.1, ht.2.trans_le hd⟩).1] at h0
        fin_cases j <;> simp [controlCentre] at h0
      rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hnull
      linarith
    -- Theorem 8.2.7 (the case without edges): `(0, z)` is not a singular subarc
    exact (theorem8_2_7 hmin le_rfl hz.1 hz.2).2 hno Λ₁ ΛR lam hext hsing
  -- Step 4: the first meeting time `d` after `p`
  set Zp : Set ℝ := Icc p T ∩ (fun t ↦ (g t, Λ₁ t, X t, ΛR t)) ⁻¹'
    {q : Mat2 × Mat2 × Mat2 × Mat2 | q.2.1 = (3 / 2 * lam) • J ∧ q.2.2.1 = J ∧ q.2.2.2 = 0}
    with hZp
  have hZpc : IsClosed Zp := by
    refine ((IsExtremalOn.continuousOn_lift h0T).mono (Icc_subset_Icc_left hp.1.le)
      ).preimage_isClosed_of_isClosed isClosed_Icc ?_
    exact (isClosed_eq (continuous_fst.comp continuous_snd) continuous_const).inter
      ((isClosed_eq (continuous_fst.comp (continuous_snd.comp continuous_snd))
        continuous_const).inter
      (isClosed_eq (continuous_snd.comp (continuous_snd.comp continuous_snd)) continuous_const))
  have hmemZp : ∀ t ∈ Icc p T, t ∈ Zp ↔ (g t, Λ₁ t, X t, ΛR t) ∈ singularLocus := by
    intro t ht
    rw [hZ t ⟨hp.1.le.trans ht.1, ht.2⟩]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨ht, h⟩⟩
  have hbdd : BddBelow Zp := ⟨p, fun t ht ↦ ht.1.1⟩
  have hdZp : sInf Zp ∈ Zp := hZpc.csInf_mem ⟨z, (hmemZp z ⟨hp.2.le, hz.2⟩).2 hzS⟩ hbdd
  set d := sInf Zp with hd
  have hdT : d ≤ T := hdZp.1.2
  have hdS : (g d, Λ₁ d, X d, ΛR d) ∈ singularLocus := (hmemZp d hdZp.1).1 hdZp
  have hpd : p < d := lt_of_le_of_ne hdZp.1.1 fun h ↦ hpS (by rw [h]; exact hdS)
  have hfree : ∀ τ ∈ Ioo p d, (g τ, Λ₁ τ, X τ, ΛR τ) ∉ singularLocus := by
    intro τ hτ hτS
    have hτZ : τ ∈ Zp := (hmemZp τ ⟨hτ.1.le, hτ.2.le.trans hdT⟩).2 hτS
    exact absurd (csInf_le hbdd hτZ) (not_le.2 hτ.2)
  -- Step 5: finite bang-bang on every compact subinterval of `(p, d)` (Theorem 8.3.2)
  have hbb : ∀ α β, p < α → β < d → IsFiniteBangBang α β u := by
    intro α β hα hβ
    rcases lt_or_ge α β with hαβ | hαβ
    · exact isFiniteBangBang_of_isReinhardtMinimizer_of_not_mem_singularLocus hmin hext
        (by linarith [hp.1]) hαβ (by linarith) fun t ht ↦
          hfree t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · exact ⟨∅, fun t ht ↦ absurd (ht.1.trans ht.2) (not_lt.2 hαβ)⟩
  -- Step 6: the hypothesis: no switching time just before `d`
  have hnc := hNC T u g X Λ₁ ΛR lam hext hedge d ⟨hp.1.trans hpd, hdT⟩ hdS
  obtain ⟨ε, hε, hsw⟩ : ∃ ε > 0, ∀ τ ∈ Ioo (d - ε) d, ¬ IsSwitchingTime u τ := by
    by_contra hcon
    push Not at hcon
    exact hnc ⟨d - p, by linarith, fun α β hα hβ ↦ hbb α β (by linarith) hβ,
      fun τ hτ ↦ hfree τ ⟨by linarith [hτ.1], hτ.2⟩, hcon⟩
  -- so the control is one vertex almost everywhere on `(c, d)`
  set c := max p (d - ε) with hc
  have hcd : c < d := max_lt hpd (by linarith)
  have hloc : ∀ t ∈ Ioo c d,
      ∃ i : Fin 3, ∃ η > 0, ∀ᵐ τ, τ ∈ Ioo (t - η) (t + η) → u τ = vertex i := by
    intro t ht
    have h1 : p < t := lt_of_le_of_lt (le_max_left _ _) ht.1
    have h2 : d - ε < t := lt_of_le_of_lt (le_max_right _ _) ht.1
    exact l3m_local_vertex (hbb ((p + t) / 2) ((t + d) / 2) (by linarith) (by linarith [ht.2]))
      ⟨by linarith, by linarith [ht.2]⟩ (hsw t ⟨h2, ht.2⟩)
  obtain ⟨i, hi⟩ := exists_ae_eq_vertex_of_locally hloc
  -- Step 7: Lemma 8.3.4 on `[c, d]`
  have hc0 : 0 ≤ c := hp.1.le.trans (le_max_left _ _)
  exact lemma8_3_4 (IsPontryaginExtremal.isExtremalOn hext hc0 hcd hdT) hi d
    ⟨hcd.le, le_rfl⟩ hdS

/-- **Theorem 16.3.1** (`thm:mahler`; Mahler's First conjecture), **conditional on the named
hypothesis** `NoChatteringIntoSingularLocus` (what Theorems 16.4.1 and 14.4.1 give in the last
step of the book's proof; see its docstring). The global minimizer of the Reinhardt optimal
control problem is a bang-bang solution with finitely many switches. In particular, the minimizer
`K_min` of the Reinhardt problem is a finite-sided smoothed polygon with rounded hyperbolic arcs at
each corner of the sort described by Reinhardt and Mahler (`IsSmoothedPolygon`: no corners, and the
boundary alternates between straight edges and hyperbolic arcs whose asymptotes extend straight
edges).

"The global minimizer" and "the minimizer `K_min`" presuppose uniqueness, which the book does not
prove; the statement is for every global minimizer of Problem 3.6.2 (`IsReinhardtMinimizer`; one
exists, `exists_isReinhardtMinimizer`) and every `K_min` (`IsWorstDisk`; one exists,
`rein_exists_worst`). Chapter 1 restates the theorem verbatim (TeX 867–873).

Proof (the book's, TeX 12806–12833, with the last step as the hypothesis):
1. First sentence. Let `(g, X)` be a global minimizer; it lifts to a Pontryagin extremal
   (Proposition 8.1.3, `proposition8_1_3`, which also gives edge extremality). By
   `l3st_forall_not_mem_singularLocus` (Theorem 8.2.7 with Theorem 8.2.3, Lemma 8.3.4 and the
   hypothesis) the lift avoids `𝒮_sing`, and Theorem 8.3.2 on `[0, T]`
   (`isFiniteBangBang_of_isReinhardtMinimizer_of_not_mem_singularLocus`) gives a bang-bang control
   with finitely many switches.
2. Second sentence ("A bang-bang trajectory with finitely many switches is a polygon with rounded
   corners of the sort described by Reinhardt, so the second statement of the theorem follows from
   the first"). For a `K_min`, some linear image `A K_min` (`det A > 0`) is a balanced disk in
   circle representation whose boundary trajectory is a global minimizer
   (`exists_isReinhardtMinimizer_of_isWorstDisk`, Layer 2's identification); by step 1 and
   Remark 8.3.3 (`remark8_3_3`: §7.2 and Lemma 7.2.1's discussion, Lemma 3.1.8) its boundary is
   that of a smoothed polygon, hence so is the boundary of `K_min`
   (`IsSmoothedPolygonBoundary.of_mulVec_image`); `K_min` is a centrally symmetric convex disk
   (`IsWorstDisk`) without corners (Lemma 2.2.5, `lemma2_2_5`, through
   `ch2_isWorstLatticeDisk_iff_isWorstDisk`). -/
theorem theorem16_3_1 (hNC : NoChatteringIntoSingularLocus) :
    (∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsReinhardtMinimizer T u g X →
      IsFiniteBangBang 0 T u) ∧
    ∀ K : Set (Fin 2 → ℝ), IsWorstDisk K → IsSmoothedPolygon K := by
  -- first sentence
  have first : ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsReinhardtMinimizer T u g X →
      IsFiniteBangBang 0 T u := by
    intro T u g X hmin
    obtain ⟨⟨Λ₁, ΛR, lam, hext⟩, -⟩ := proposition8_1_3 hmin
    exact isFiniteBangBang_of_isReinhardtMinimizer_of_not_mem_singularLocus hmin hext le_rfl
      hmin.1.1.1 le_rfl (l3st_forall_not_mem_singularLocus hNC hmin hext)
  refine ⟨first, fun K hK ↦ ?_⟩
  -- second sentence: a linear image of `K_min` is the disk of a global minimizer
  obtain ⟨A, σ, T, u, g, X, hA, hKσ, -, hσ, hshift, hmin⟩ :=
    exists_isReinhardtMinimizer_of_isWorstDisk hK
  obtain ⟨⟨Λ₁, ΛR, lam, hext⟩, hedge⟩ := proposition8_1_3 hmin
  have hpoly := remark8_3_3 hext hedge (l3st_forall_not_mem_singularLocus hNC hmin hext) hKσ
    (fun j t _ ↦ hσ j t) hshift
  exact ⟨hK.1, (lemma2_2_5.2 K (ch2_isWorstLatticeDisk_iff_isWorstDisk.2 hK)).1,
    IsSmoothedPolygonBoundary.of_mulVec_image hA.ne' hpoly⟩

end SmoothedPolygons
