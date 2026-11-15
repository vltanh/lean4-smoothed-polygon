module

public import SmoothedPolygons.Ch14.NoReturn
public import SmoothedPolygons.Ch14.UnstableCurveSwitches
public import SmoothedPolygons.Ch14.NoReturnTools
public import SmoothedPolygons.Ch16.ClusterPoint

/-!
# Chapter 14: Theorem 14.4.1 (no return) from the numerical fact N4

Theorem 14.4.1 (`thm:no-return`) of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX
11995–12013), as the named proposition `Theorem14_4_1` (`SmoothedPolygons/Ch14/NoReturn.lean`),
proved from the numerical fact N4 (`UnstableCurveLeavesStarDomain`,
`SmoothedPolygons/Ch14/UnstableCurve.lean`: the unstable curve `W^u(q_out)` reaches the boundary of
the star domain, Figure 14.2): `theorem14_4_1`. N4 is proved without computer assistance
(`unstableCurveLeavesStarDomain`, `SmoothedPolygons/Ch14/ArcRegionInvariant.lean`; a departure
from the paper, by the user's decision, REPORT.md E88), so Theorem 14.4.1 holds unconditionally
(`theorem14_4_1_unconditional`, `SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean`).

## The book's proof (TeX 12004–12013), step by step

"All switches must be on the unstable curve, which meets that exceptional divisor at a single point
`(0, x_out)`. Any trajectory that returns to the singular locus must chatter (that is, must use
infinitely many switches to arrive). This would require the unstable curve to contain a sequence of
*forward* iterates of points tending to the exceptional divisor. This does not happen, because the
unstable curve hits the boundary of the star domain. The second statement follows from the first
by time reversal."

First statement (`theorem14_4_1_out`). Let the extremal on `[a, c]` (`λ_cost = -1`, finitely
bang-bang on compact subintervals of `(a, c)`) emanate from `q_out`: a chattering arc out of the
singular locus on `[a, b]` whose switching points `τ n ↓ a` converge backward to `q_out` modulo
`V_T`. Suppose its lift meets the singular locus at some `t ∈ (a, c]`; then `t > b` (the arc avoids
it on `(a, b]`).
1. **The first return.** Let `s ∈ (b, t]` be the first meeting time after `b`
   (`IsExtremalOn.exists_first_mem_singularLocus`): the lift is on the singular locus at `s` and off
   it on `(a, s)`.
2. **"All switches must be on the unstable curve"**: for the extension `e` and the neighborhood `U`
   of N4, eventually each switching point `τ N` of the arc out of `a`, rotated by `Ad_{R⁻ᵏ}`, is
   `lieChart p` with `p ∈ W^u_loc(e, U)`, `r > 0`
   (`IsChatteringArcOutOf.eventually_mem_localUnstableSet`, Theorem 16.4.1 time reversed, from the
   convergence hypothesis; no numerical fact). Fix such `N`.
3. **"Any trajectory that returns to the singular locus must chatter"**: on `[a', s]`, with
   `a' = (τ (N + 1) + τ N)/2 ∈ (a, s)`, the extremal is a chattering arc into the singular locus
   (`exists_isChatteringArcInto`: its switching times in `(a', s)` accumulate at `s`, Lemma 8.3.4);
   `τ N` is one of them, `σ n₀ = τ N` (the arc's switching sequence `σ` enumerates all switching
   times in `(a', s)`, and `τ N` is a switching time there).
4. **"This does not happen, because the unstable curve hits the boundary of the star domain"**: by
   N4 the orbit of `lieChart p` reaches the boundary of the star domain
   (`ReachesStarBoundary (lieChart p)`), which no switching point of a chattering arc can do
   (`IsChatteringArcInto.not_reachesStarBoundary` at `σ n₀`): a contradiction. (Its proof: the
   switching points `σ (n₀ + j)` follow the Reinhardt–Poincaré iterates of `lieChart p` while they
   switch cyclically, and the arc from the last one leaves the star domain before the next switch,
   which an extremal, whose states are star states, cannot do.)

Second statement (`theorem14_4_1_in`), **by time reversal**: the reflection `t ↦ a + c - t` of the
extremal on `[a, c]` (`IsExtremalOn.reverse`, `IsFiniteBangBang.reverseControl`) turns the
chattering arc into the singular locus on `[b, c]` into a chattering arc out of it on
`[a, a + c - b]` (`IsChatteringArcInto.reverse`) whose switching points converge backward to
`τ(q_in) = q_out` (`switchAng_reverse`, `TendstoModVT.tau`, `tau_ang_tau_qOutCart`); the first
statement for the reflected extremal (an instance of `theorem14_4_1_out`) gives that its lift avoids
the singular locus on `(a, c]`, i.e. the original lift avoids it on `[a, c)`
(`reverse_mem_singularLocus_iff`).

The book's "trajectory of the Reinhardt system" lives in the star domain: the hypothesis
`IsExtremalOn a c …` contains the state constraint (`IsStateTrajectory`: `IsStarState (X t)` on
`[a, c]`), which step 4 uses. The finite bang-bang hypothesis of `Theorem14_4_1` (the reading of
"trajectory") is used only on `(a, s)`, where Theorem 8.3.2 gives it anyway: the statement without
it is equivalent (`theorem14_4_1_iff_unrestricted`, `SmoothedPolygons/Ch14/NoReturnReading.lean`).

## Proofs

`theorem14_4_1_out`: steps 1–4 above (the choice of `N` with `eventually_atTop`; the location of
`τ N` in `σ` from the two enumerations: `τ N ∈ (a', s)` is a switching time, so `τ N = σ n₀` by
`IsSwitchingSeqInto`; the bookkeeping of intervals). `theorem14_4_1_in`: the reflection, an instance
of `theorem14_4_1_out`. `theorem14_4_1`: the two together. The helpers are in
`SmoothedPolygons/Ch14/NoReturnTools.lean` (`IsChatteringArcInto.reverse`, the first meeting time),
`UnstableCurveSwitches.lean`, `SmoothedPolygons/Ch16/ClusterCoordinates.lean` (the time reversal:
`IsExtremalOn.reverse`, `IsFiniteBangBang.reverseControl`, `switchAng_reverse`,
`TendstoModVT.tau`, `reverse_mem_singularLocus_iff`) and `SmoothedPolygons/Ch16/ClusterPoint.lean`
(`IsChatteringArcOutOf.eventually_mem_localUnstableSet`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology
open TriFuller

/-- **Theorem 14.4.1, first statement** (`thm:no-return`, TeX 11995–11998), from N4: a trajectory
(an extremal on `[a, c]`, `λ_cost = -1`, finitely bang-bang on compact subintervals of `(a, c)`)
that emanates from `(0, x_out)` — a chattering arc out of the singular locus at `a` on
`[a, b] ⊆ [a, c]` whose switching points converge backward to `q_out` modulo `V_T` — does not return
to the exceptional divisor: its lift avoids the singular locus on `(a, c]`. -/
theorem theorem14_4_1_out (hN4 : UnstableCurveLeavesStarDomain) {a b c : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}
    (hext : IsExtremalOn a c u g X Λ₁ ΛR (-1)) (hb : b ∈ Ioc a c)
    (hbb : ∀ α β, a < α → β < c → IsFiniteBangBang α β u)
    (hout : IsChatteringArcOutOf a b u g X Λ₁ ΛR τ)
    (hconv : TendstoModVT (switchAng X Λ₁ ΛR τ) (ang qOutCart)) :
    ∀ t ∈ Ioc a c, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus := by
  intro t ht hmem
  obtain ⟨e, he, U, hU, hN⟩ := hN4
  obtain ⟨-, -, hoff, -, hanti, hτI, -, hsw⟩ := id hout
  have htb : b < t := by
    by_contra hcon
    exact hoff t ⟨ht.1, not_lt.1 hcon⟩ hmem
  -- Step 1: the first return `s ∈ (b, t]` to the singular locus.
  obtain ⟨s, hs, hsmem, hsoff⟩ :=
    hext.exists_first_mem_singularLocus hb.1.le htb.le ht.2 (hoff b ⟨hb.1, le_rfl⟩) hmem
  -- Step 2: all switches are on the unstable curve; fix `N`.
  obtain ⟨N, hNev⟩ := eventually_atTop.1 (hout.eventually_mem_localUnstableSet hconv he hU)
  obtain ⟨k, p, hp, hp0, hrot⟩ := hNev N le_rfl
  -- Step 3: the return chatters, on `[a', s]` with `a' = (τ (N + 1) + τ N) / 2`.
  have has : a < s := hb.1.trans hs.1
  have hext' : IsExtremalOn a s u g X Λ₁ ΛR (-1) := hext.mono le_rfl has (hs.2.trans ht.2)
  have hoff' : ∀ r ∈ Ioo a s, (g r, Λ₁ r, X r, ΛR r) ∉ singularLocus := by
    intro r hr
    rcases le_or_gt r b with hrb | hrb
    · exact hoff r ⟨hr.1, hrb⟩
    · exact hsoff r ⟨hrb.le, hr.2⟩
  have hbb' : ∀ α β, a < α → β < s → IsFiniteBangBang α β u :=
    fun α β h1 h2 ↦ hbb α β h1 (h2.trans_le (hs.2.trans ht.2))
  have hN1 := hτI (N + 1)
  have hN0 := hτI N
  have hlt : τ (N + 1) < τ N := hanti (Nat.lt_succ_self N)
  obtain ⟨σ, hσ⟩ := exists_isChatteringArcInto hext' hsmem hoff' hbb' ((τ (N + 1) + τ N) / 2)
    ⟨by linarith [hN1.1], by linarith [hN0.2, hs.1]⟩
  -- `τ N` is a switching time in `(a', s)`, so it is `σ n₀` for some `n₀`.
  have hswN : IsSwitchingTime u (τ N) := (hsw (τ N) hN0).2 ⟨N, rfl⟩
  obtain ⟨n₀, hn₀⟩ := (hσ.2.2.2.2.2.2.2 (τ N) ⟨by linarith, by linarith [hN0.2, hs.1]⟩).1 hswN
  -- Step 4: by N4 the orbit of `lieChart p` reaches the star boundary, which `σ n₀` cannot do.
  exact hσ.not_reachesStarBoundary n₀ k (q₀ := lieChart p) (by rw [hn₀]; exact hrot)
    (hN p hp hp0)

/-- **Theorem 14.4.1, second statement** (`thm:no-return`, TeX 11999–12002), from N4, by time
reversal (an instance of `theorem14_4_1_out` for the reflected extremal): a trajectory that tends to
`(0, x_in)` — a chattering arc into the singular locus at `c` on `[b, c] ⊆ [a, c]` whose switching
points converge to `q_in` modulo `V_T` — did not emanate at an earlier time from the exceptional
divisor: its lift avoids the singular locus on `[a, c)`. -/
theorem theorem14_4_1_in (hN4 : UnstableCurveLeavesStarDomain) {a b c : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}
    (hext : IsExtremalOn a c u g X Λ₁ ΛR (-1)) (hb : b ∈ Ico a c)
    (hbb : ∀ α β, a < α → β < c → IsFiniteBangBang α β u)
    (hin : IsChatteringArcInto b c u g X Λ₁ ΛR τ)
    (hconv : TendstoModVT (switchAng X Λ₁ ΛR τ) (ang (tau qOutCart))) :
    ∀ t ∈ Ico a c, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus := by
  intro t ht hmem
  -- The switching points of the reflected arc converge backward to `τ (ang (τ q_out)) = ang q_out`.
  have hang : switchAng (fun t ↦ matTau (X (a + c - t))) (fun t ↦ matTau (Λ₁ (a + c - t)))
      (fun t ↦ matTau (ΛR (a + c - t))) (fun n ↦ a + c - τ n) =
        fun n ↦ tau (switchAng X Λ₁ ΛR τ n) := funext (switchAng_reverse (a + c) X Λ₁ ΛR τ)
  have hconv' := hconv.tau
  rw [tau_ang_tau_qOutCart] at hconv'
  -- The first statement for the reflected extremal on `[a, c]`, at the time `a + c - t ∈ (a, c]`.
  have h1 := theorem14_4_1_out hN4 hext.reverse (b := a + c - b)
    ⟨by linarith [hb.2], by linarith [hb.1]⟩
    (fun α β hα hβ ↦ IsFiniteBangBang.reverseControl (hbb _ _ (by linarith) (by linarith)))
    (hin.reverse a) (by rw [hang]; exact hconv') (a + c - t)
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  apply h1
  simp only [sub_sub_cancel]
  exact reverse_mem_singularLocus_iff.2 hmem

/-- **Theorem 14.4.1** (`thm:no-return`, TeX 11995–12013), for locally finitely bang-bang extremals
(the reading of `Theorem14_4_1`, equivalent to the unrestricted statement,
`theorem14_4_1_iff_unrestricted`), **from the numerical fact N4** (`UnstableCurveLeavesStarDomain`,
Figure 14.2): the book's proof, the first statement by `theorem14_4_1_out` and the second by time
reversal, `theorem14_4_1_in`. -/
theorem theorem14_4_1 (hN4 : UnstableCurveLeavesStarDomain) : Theorem14_4_1 :=
  ⟨fun _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 ↦ theorem14_4_1_out hN4 h1 h2 h3 h4 h5,
    fun _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 ↦ theorem14_4_1_in hN4 h1 h2 h3 h4 h5⟩

end SmoothedPolygons
