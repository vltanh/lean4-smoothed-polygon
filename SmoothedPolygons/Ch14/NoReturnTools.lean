module

public import SmoothedPolygons.Ch16.ClusterCoordinates

/-!
# Chapter 14: tools for Theorem 14.4.1 — time reversal on an interval, the first meeting time

Two tools for the proof of Theorem 14.4.1 (`thm:no-return`, Hales–Vajjha, *Packings of Smoothed
Polygons*, TeX 11995–12013), stated here so that "The second statement follows from the first by
time reversal" (TeX 12012–12013) is an instance of the first statement
(`SmoothedPolygons/Ch14/NoReturnProof.lean`, `theorem14_4_1_in`):

* **Time reversal on `[a, c]`** (Remark 10.2.3, `eqn:wbc-reverse`): the reflection `t ↦ a + c - t`
  of an extremal on `[a, c]`, with `g ↦ D g D`, `M ↦ -D M D` (`matTau`) on `X, Λ₁, Λ_R` and the
  controls relabelled `e₂ ↔ e₃` (`reverseControl a c u`), is an extremal on `[a, c]` with the same
  `λ_cost` (`IsExtremalOn.reverse`); finite bang-bang control on `[α, β]` comes from that on the
  reflected interval (`IsFiniteBangBang.reverseControl`); the singular locus is invariant
  (`reverse_mem_singularLocus_iff`); a chattering arc into the singular locus on `[b, c]` becomes a
  chattering arc out of it on `[a, a + c - b]` (`IsChatteringArcInto.reverse`, for any reflection
  centre: the existing `IsChatteringArcOutOf.reverse` reflects about the arc's own midpoint, while
  Theorem 14.4.1 needs the reflection of the whole interval `[a, c]`); the angular components of the
  switching points are mapped by the Fuller `τ` (`switchAng_reverse`), and convergence modulo `V_T`
  is preserved by `τ` (`TendstoModVT.tau`), which maps `q_in` to `q_out`
  (`tau_ang_tau_qOutCart`).
* **The first meeting with the singular locus** after a time at which the lift is off it
  (`IsExtremalOn.exists_first_mem_singularLocus`): the meeting times form a closed set
  (`IsExtremalOn.mem_singularLocus_iff`, continuity of the lift).

`IsExtremalOn.reverse`, `IsFiniteBangBang.reverseControl`, `reverse_mem_singularLocus_iff`,
`switchAng_reverse` and `TendstoModVT.tau` are proved in
`SmoothedPolygons/Ch16/ClusterCoordinates.lean` (imported here), where
`IsChatteringArcOutOf.reverse` and the time reversal of Theorem 16.4.1 (`theorem16_4_1_reverse`,
in `SmoothedPolygons/Ch16/ClusterPoint.lean`) use them too.

## Proofs

`IsChatteringArcInto.reverse`: as `IsChatteringArcOutOf.reverse`, with the reflection
`t ↦ a + c - t` mapping `[b, c]` onto `[a, a + c - b]`: the reflected extremal is
`IsExtremalOn.reverse` on `[b, c]` shifted by `a - b` (`a + c - (a + t) = b + c - (b + t)`), the
switching times are reflected (`isSwitchingTime_reverseControl_iff`).
`tau_ang_tau_qOutCart`: `tau_ang`, `tau_tau`. `exists_first_mem_singularLocus`: `s = sInf Z` with
`Z = {r ∈ [b, t] | lift(r) ∈ 𝒮_sing}`, closed (`mem_singularLocus_iff` turns membership into the
closed conditions `Λ₁ = (3/2) λ J`, `X = J`, `Λ_R = 0`, with `λ ≠ 0` read off at `t`, and the lift
is continuous on `[a, c]`), nonempty (`t`), and `b ∉ Z`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology MeasureTheory
open TriFuller

/-- **Time reversal of a chattering arc into the singular locus**, about any centre: a chattering
arc into the singular locus on `[b, c]`, reflected by `t ↦ a + c - t` (with the phase points
reversed by `matTau`, `g ↦ D g D` and the controls relabelled), is a chattering arc out of the
singular locus on `[a, a + c - b]`, with the switching times `a + c - τ n`. -/
theorem IsChatteringArcInto.reverse (a : ℝ) {b c : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto b c u g X Λ₁ ΛR τ) :
    IsChatteringArcOutOf a (a + c - b) (reverseControl a c u)
      (fun t ↦ diagD * g (a + c - t) * diagD) (fun t ↦ matTau (X (a + c - t)))
      (fun t ↦ matTau (Λ₁ (a + c - t))) (fun t ↦ matTau (ΛR (a + c - t)))
      (fun n ↦ a + c - τ n) := by
  obtain ⟨hext, hc, hoff, hbb, hmono, hτI, hlim, hsw⟩ := h
  refine ⟨?_, ?_, fun t ht ↦ ?_, fun α β hα hβ ↦
    IsFiniteBangBang.reverseControl (hbb _ _ (by linarith) (by linarith)), fun m n hmn ↦ ?_,
    fun n ↦ ⟨by linarith [(hτI n).2], by linarith [(hτI n).1]⟩, ?_, fun t ht ↦ ?_⟩
  · -- `IsExtremalOn.reverse` on `[b, c]`, shifted by `a - b`
    have := hext.reverse
    unfold IsExtremalOn reverseControl at this ⊢
    have e1 : a + c - b - a = c - b := by ring
    have e2 : ∀ t, a + c - (a + t) = c - t := fun t ↦ by ring
    have e3 : ∀ t, b + c - (b + t) = c - t := fun t ↦ by ring
    simp only [e3] at this
    simp only [e1, e2]
    exact this
  · simp only [show a + c - a = c by ring]
    exact reverse_mem_singularLocus_iff.2 hc
  · rw [reverse_mem_singularLocus_iff]
    exact hoff _ ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · have := hmono hmn
    dsimp only
    linarith
  · have := (tendsto_const_nhds (x := a + c)).sub hlim
    rwa [show a + c - c = a by ring] at this
  · rw [isSwitchingTime_reverseControl_iff, hsw _ ⟨by linarith [ht.2], by linarith [ht.1]⟩]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by linarith⟩

/-- `τ` maps the representative `ang (τ q_out)` of `q_in` to the representative `ang q_out` of
`q_out`. -/
theorem tau_ang_tau_qOutCart : tau (ang (tau qOutCart)) = ang qOutCart := by
  rw [tau_ang, tau_tau]

/-- **The first meeting with the singular locus**: if the lift of an extremal on `[a, c]` is off the
singular locus at `b` and on it at `t ∈ [b, c]`, there is a first time `s ∈ (b, t]` at which it
meets the singular locus, and it avoids it on `[b, s)` (the meeting times form a closed set). -/
theorem IsExtremalOn.exists_first_mem_singularLocus {a c lam : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} (h : IsExtremalOn a c u g X Λ₁ ΛR lam) {b t : ℝ} (hab : a ≤ b)
    (hbt : b ≤ t) (htc : t ≤ c) (hb : (g b, Λ₁ b, X b, ΛR b) ∉ singularLocus)
    (ht : (g t, Λ₁ t, X t, ΛR t) ∈ singularLocus) :
    ∃ s ∈ Ioc b t, (g s, Λ₁ s, X s, ΛR s) ∈ singularLocus ∧
      ∀ r ∈ Ico b s, (g r, Λ₁ r, X r, ΛR r) ∉ singularLocus := by
  have hsub : Icc b t ⊆ Icc a c := Icc_subset_Icc hab htc
  have hlam : lam ≠ 0 := ((h.mem_singularLocus_iff (hsub ⟨hbt, le_rfl⟩)).1 ht).1
  -- the meeting times in `[b, t]`, a closed set
  let C : Set (Mat2 × Mat2 × Mat2 × Mat2) :=
    {q | q.2.1 = (3 / 2 * lam) • J ∧ q.2.2.1 = J ∧ q.2.2.2 = 0}
  let Z : Set ℝ := Icc b t ∩ (fun r ↦ (g r, Λ₁ r, X r, ΛR r)) ⁻¹' C
  have hZiff : ∀ r ∈ Icc b t, (g r, Λ₁ r, X r, ΛR r) ∈ singularLocus ↔ r ∈ Z := by
    intro r hr
    rw [h.mem_singularLocus_iff (hsub hr)]
    exact ⟨fun h' ↦ ⟨hr, h'.2⟩, fun h' ↦ ⟨hlam, h'.2⟩⟩
  have hC : IsClosed C :=
    (isClosed_eq (by fun_prop) continuous_const).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_eq (by fun_prop) continuous_const))
  have hZc : IsClosed Z :=
    (h.continuousOn_lift.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc hC
  have hZne : Z.Nonempty := ⟨t, (hZiff t ⟨hbt, le_rfl⟩).1 ht⟩
  have hZbdd : BddBelow Z := ⟨b, fun r hr ↦ hr.1.1⟩
  have hsZ : sInf Z ∈ Z := hZc.csInf_mem hZne hZbdd
  have hbs : b ≠ sInf Z := fun e ↦ hb ((hZiff b ⟨le_rfl, hbt⟩).2 (e ▸ hsZ))
  refine ⟨sInf Z, ⟨lt_of_le_of_ne hsZ.1.1 hbs, hsZ.1.2⟩, (hZiff _ hsZ.1).2 hsZ,
    fun r hr hmem ↦ ?_⟩
  have hrI : r ∈ Icc b t := ⟨hr.1, hr.2.le.trans hsZ.1.2⟩
  have := csInf_le hZbdd ((hZiff r hrI).1 hmem)
  linarith [hr.2]

end SmoothedPolygons
