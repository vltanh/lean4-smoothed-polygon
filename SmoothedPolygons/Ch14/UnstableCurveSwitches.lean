module

public import SmoothedPolygons.Ch14.UnstableCurve
public import SmoothedPolygons.Ch16.NextSwitch

/-!
# Chapter 14: a chattering arc has no switching point whose orbit reaches the star boundary

The dynamical half of the proof of Theorem 14.4.1 (`thm:no-return`, Hales–Vajjha, *Packings of
Smoothed Polygons*, TeX 12005–12010): "Any trajectory that returns to the singular locus must
chatter (that is, must use infinitely many switches to arrive). This would require the unstable
curve to contain a sequence of forward iterates of points tending to the exceptional divisor. This
does not happen, because the unstable curve hits the boundary of the star domain."

Along a chattering arc into the singular locus (`IsChatteringArcInto`: infinitely many switching
times `τ n ↑ b`), if the `n`-th switching point, rotated by `Ad_{R⁻ᵏ}`, is a phase point `q₀` whose
forward orbit under the Reinhardt–Poincaré map reaches the boundary of the star domain
(`ReachesStarBoundary q₀`, the conclusion of the numerical fact N4,
`SmoothedPolygons/Ch14/UnstableCurve.lean`), we get a contradiction
(`IsChatteringArcInto.not_reachesStarBoundary`):

1. `IsChatteringArcInto.iterate_reinPoincare`: while the orbit switches cyclically, the switching
   points `τ (n + j)`, rotated by `Ad_{R^{-(k+j)}}`, are the iterates `F^j q₀`
   (`IsChatteringArcInto.next_switchPoint_eq_reinPoincare`, by induction on `j`);
2. `IsChatteringArcInto.arc_eq_vertexFlow` (`SmoothedPolygons/Ch16/NextSwitch.lean`): from a
   switching point where the control after the switch is `e₂` (`SwitchEntersE2`), the extremal is
   the `e₂`-flow up to the next switching time, at which some other vertex reaches the Hamiltonian
   of `e₂`;
3. `IsChatteringArcInto.false_of_arcLeavesStarDomain`: if the `e₂`-flow from the switching point
   leaves the star domain at a time `T` before any vertex reaches `e₂` (`ArcLeavesStarDomain`), the
   next switching time is not in `(0, T)` (step 2), so the extremal follows the flow up to `T` and
   its state at `τ n + T` is not a star state — but the extremal's states are star states (the state
   constraint of `IsStateTrajectory`): a contradiction. This is "the forward step of the
   Reinhardt–Poincaré map is no longer defined" (TeX 11989–11991), read for an extremal: an
   extremal that switches infinitely often cannot pass through such a point.

## Proofs

Step 2 is `IsChatteringArcInto.arc_eq_vertexFlow` of `SmoothedPolygons/Ch16/NextSwitch.lean`, the
first half of the proof of `IsChatteringArcInto.next_switchPoint_eq_reinPoincare` there (its parts
(i), (ii) and (v)): the control after `τ n` is neither `e₁` nor `e₃` (the two conditions of
`SwitchEntersE2`), so the extremal is the `e₂`-flow on `[τ n, τ (n + 1)]`, and the vertex used
right after `τ (n + 1)` differs from `e₂` and maximizes the Hamiltonian there. Step 3: with
`s = τ (n + 1) - τ n > 0`, `s < T` contradicts the strict maximality of `e₂` at `s`; `s ≥ T` gives
`R⁻ᵏ X(τ n + T) Rᵏ = iso_vfX 1 q₀ T`, a star state by `poly_isStarState_conj_pow` and the state
constraint of `IsExtremalOn`. Step 1: induction on `j`, `Function.iterate_succ_apply'`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology
open TriFuller

/-- **A chattering arc cannot pass through a switching point whose `e₂`-arc leaves the star domain
before any switch**: the extremal would follow the arc out of the star domain. -/
theorem IsChatteringArcInto.false_of_arcLeavesStarDomain {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n k : ℕ)
    {q₀ : iso_PhasePt} (hq : iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = q₀)
    (he : SwitchEntersE2 q₀) (hl : ArcLeavesStarDomain q₀) : False := by
  obtain ⟨harc, j, hj, hle⟩ := h.arc_eq_vertexFlow n k hq he
  obtain ⟨T, hT, hns, hmax⟩ := hl
  obtain ⟨hmono, hτI, -, -⟩ := h.2.2.2.2
  have hlt : τ n < τ (n + 1) := hmono (Nat.lt_succ_self n)
  rcases lt_or_ge (τ (n + 1) - τ n) T with hsT | hsT
  · -- the next switch comes before `T`: `e₂` is still the strict maximizer there
    exact absurd hle (not_le.2 (hmax _ ⟨by linarith, hsT⟩ j hj))
  · -- the extremal follows the `e₂`-flow up to `T`, where the state is not a star state
    apply hns
    have h1 := congrArg Prod.fst (harc (τ n + T) ⟨by linarith, by linarith⟩)
    simp only [add_sub_cancel_left] at h1
    change R⁻¹ ^ k * X (τ n + T) * R ^ k = iso_vfX 1 q₀ T at h1
    rw [← h1]
    have hst := (h.1.1.2.2.2.1 (τ n + T - a) ⟨by linarith [(hτI n).1], by
      linarith [(hτI (n + 1)).2]⟩).2
    simp only [add_sub_cancel] at hst
    exact poly_isStarState_conj_pow k hst

/-- **The switching points follow the Reinhardt–Poincaré map while the orbit switches cyclically**:
if the `n`-th switching point, rotated by `Ad_{R⁻ᵏ}`, is `q₀`, and the iterates `F^j q₀`, `j < K`,
switch cyclically, then the `(n + j)`-th switching point, rotated by `Ad_{R^{-(k+j)}}`, is `F^j q₀`
for `j ≤ K` (`IsChatteringArcInto.next_switchPoint_eq_reinPoincare`, by induction). -/
theorem IsChatteringArcInto.iterate_reinPoincare {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n k : ℕ)
    {q₀ : iso_PhasePt} (hq : iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = q₀) {K : ℕ}
    (he : ∀ j < K, SwitchEntersE2 (reinPoincare^[j] q₀))
    (hs : ∀ j < K, ArcSwitchesToE1 (reinPoincare^[j] q₀)) :
    ∀ j ≤ K, iso_adRinvPow (k + j) (phaseAt X Λ₁ ΛR (τ (n + j))) = reinPoincare^[j] q₀ := by
  intro j hj
  induction j with
  | zero => simpa using hq
  | succ j ih =>
    obtain ⟨h0, h2⟩ := he j (by omega)
    obtain ⟨hpos, hmax, hbeat⟩ := hs j (by omega)
    have := h.next_switchPoint_eq_reinPoincare (n + j) (k + j) (ih (by omega)) h0 h2 hpos hmax
      hbeat
    rw [Function.iterate_succ_apply', show k + (j + 1) = k + j + 1 by ring,
      show n + (j + 1) = n + j + 1 by ring]
    exact this

/-- **No switching point of a chattering arc into the singular locus has a forward orbit reaching
the boundary of the star domain** (TeX 12007–12010: "This would require the unstable curve to
contain a sequence of forward iterates of points tending to the exceptional divisor. This does not
happen, because the unstable curve hits the boundary of the star domain"): the switching points
after `τ n` follow the orbit (`iterate_reinPoincare`) until its arc leaves the star domain, which
the extremal cannot follow (`false_of_arcLeavesStarDomain`). -/
theorem IsChatteringArcInto.not_reachesStarBoundary {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n k : ℕ)
    {q₀ : iso_PhasePt} (hq : iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = q₀) :
    ¬ ReachesStarBoundary q₀ := by
  rintro ⟨K, he, hs, hl⟩
  have hit := h.iterate_reinPoincare n k hq (fun j hj ↦ he j hj.le) hs K le_rfl
  exact h.false_of_arcLeavesStarDomain (n + K) (k + K) hit (he K le_rfl) hl

end SmoothedPolygons
