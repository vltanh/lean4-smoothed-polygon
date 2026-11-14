module

public import SmoothedPolygons.Ch16.ReinhardtShadowing
public import Basic.Dynamics.HyperbolicBox

/-!
# Chapter 16: Theorem 16.4.1, the cluster point theorem (§16.4.3)

Theorem 16.4.1 (`thm:no-chatter`) of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX
12840–12846, proof 12989–13056): "If the sequence of switching points of a Pontryagin extremal
Reinhardt trajectory has a cluster point on the exceptional divisor of the blow-up, reached in
finite time, and if the switching points themselves are not on the exceptional divisor, then that
cluster point is the fixed point `q_in` and the switching points lie on the stable curve
`W^s(q_in)`."

Formal statement (`theorem16_4_1`): for a chattering arc into the singular locus
(`IsChatteringArcInto`, `λ_cost = -1`), (i) the angular components of the switching points converge
to `q_in` modulo `V_T` (the cluster point is `q_in`, and it is the only one), and (ii) for every
analytic extension `e` of the Reinhardt–Poincaré map at `q_out` (Lemma 14.3.1) and every
neighborhood `U` of the fixed point, eventually each switching point, rotated onto the section
`χ₂₃ = 0`, is the point `lieChartIn p` of the mirrored chart at `q_in` (Remark 14.3.4) with `p` on
the local unstable manifold of `e`, which is the local stable curve `W^s(q_in)` of `e⁻¹`, the
Reinhardt–Poincaré map in the mirrored chart (`remark14_3_4`; a `C^∞` curve, `theorem14_3_3`).
`theorem16_4_1_reverse` is the time reversal (switching points emanating from the divisor converge
to `q_out` backward and lie on `W^u(q_out)`), which the proof of Theorem 14.4.1 needs (G14.11).

## The book's proof (TeX 12991–13056), and this proof

The book: (a) a periodic set of switching points does not approach the divisor, so the switching
sequence is injective; (b) if `q_in` is a cluster point, the switching points lie on `W^s(q_in)`
and, by an `ε` versus `ε/r_scale` argument with the finite time, `q_in` is the only cluster point;
(c) `q_out` is not a cluster point, since otherwise the switching points would lie on
`W^s(q_out)`, which is contained in the divisor; (d) each cluster point is assigned to a part
`𝒟_i` through a subsequence in `𝒟_i^R`; (e) by the upper triangular structure of Table 16.1, a
cluster point in a part gives one in a smaller part, ending in `𝒟_out^R`; (f) a cluster point in
`𝒟_out^R` makes `q_out` a cluster point ("the dynamics are analytic on `𝒟_out^R`, and the set of
cluster points being closed"), against (c).

Gaps (G16.9, G16.10): (b)'s `ε/r_scale` argument is unclear; (c) uses `W^s(q_out) ⊆ divisor`
globally, while Theorem 14.3.3 is local; (d)–(e) need the Reinhardt parts and branch maps of
§16.4.2 (unproved, G16.8) and ignore the diagonal rows of Table 16.1; (f) "analytic on
`𝒟_out^R`" is not established (Lemma 14.3.1 is local at the fixed point). Repair (along the book's
lines, with the ω-limit / hyperbolic-box argument of the plan):

1. (a) holds by construction: `τ` is strictly increasing (`IsSwitchingSeqInto`); the switching
   points have Fuller coordinates `→ 0`, `≠ 0` (`IsChatteringArcInto.switchPoints`).
2. `Ω = switchClusterSet` is nonempty (compactness of `Ξ`) and lies in `Ξ_{𝒲,0}/V_T`
   (`mapClusterPt_switchAng_mem_sectionZero`).
3. (c), local form: `q_out ∉ Ω` (`qOut0_not_mem_switchClusterSet`). Near `q_out`, rotated
   switching points with small `r` are chart points (`tendsto_lieChartInv_phaseOfFuller`,
   `lieChart_lieChartInv`) and consecutive ones follow `e`
   (`IsChatteringArcInto.eventually_follows_out`, from `eventually_isSwitch_reinSwitchTime` and
   `iso_arc_eq_vertexFlow`-type uniqueness); `e` fixes `(0, x̃_out)`, leaves `r = 0` invariant,
   expands transversally by `r_scale > 1` and contracts along the divisor (the derivative facts
   `hasStrictFDerivAt_extension`, not the stable manifold theorem), so the hyperbolic box
   (`Function.not_mapClusterPt_of_transverse_expansion`) excludes `(0, x̃_out)` as a cluster point
   of the chart sequence, whose `r` tends to `0`. No stable manifold theorem is used anywhere in the
   proof of Theorem 16.4.1 (nor in the assembly of Theorem 16.3.1): the "stable curve" of step 5 is
   the local unstable set of `e`, by definition; Theorem 14.3.3 (via Theorem A.3.1) adds that it is
   a
   `C^∞` curve.
4. (d)–(f) replaced: `Ω` is forward invariant under `F_ang` (N5, `ClusterSetForwardInvariant`); a
   point `ω ≠ q_in` of `Ω` has `F^k(ω) → q_out` (Theorem 16.1.1, `theorem16_1_1`, with the three
   named numerical facts of Layer 5), so `q_out ∈ Ω` (closed): impossible by step 3. Hence
   `Ω = {q_in}`, and the angular components converge to `q_in` modulo `V_T`
   (`tendstoModVT_of_forall_mapClusterPt`).
5. (b), the stable curve: near `q_in`, rotated switching points with small `r` are points of
   the mirrored chart (`tendsto_lieChartInInv_phaseOfFuller`) converging to `(0, x̃_out)`, and
   consecutive ones satisfy `e(p_{n+1}) = p_n` (`IsChatteringArcInto.eventually_follows_in`,
   `remark14_3_4`); so `(p_n, p_{n+1}, …)` is a backward `e`-orbit tending to the fixed point,
   and `p_n` lies in the local unstable set of `e` (`Function.eventually_mem_localUnstableSet`).

Departure from the paper: steps 3–5 replace (b)–(f) as described (forced by G16.8–G16.10); the
descent through Table 16.1 on Reinhardt parts is replaced by Theorem 16.1.1 applied to the cluster
set, which is the book's "Repeating the argument of Theorem 16.1.1" done once on the Fuller side.
Size: 600–1,000 lines given N5 and Chapter 14.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology
open TriFuller

/-- **The chart covers the switching points near `q_out`**: for `ξ` with `Im ξ₁ > 0` (as `q_out`'s
representatives on `𝒲₀`), the chart coordinates of the phase point with Fuller coordinates
`(r ξ'₁, r² ξ'₂, r³ ξ'₃)` tend to `(0, fullerChartInv ξ)` as `r → 0⁺`, `ξ' → ξ` (the change of
chart of G16.12: `r_chart = X₁₁ = 2 r Im ξ'₁`, `x̃₂₁ = (X₂₁ - 1)/X₁₁ → Re ξ₁/Im ξ₁`, …). -/
theorem tendsto_lieChartInv_phaseOfFuller {ξ : Fin 3 → ℂ} (hξ : 0 < (ξ 0).im) :
    Tendsto (fun p : ℝ × (Fin 3 → ℂ) ↦ lieChartInv (phaseOfFuller (scale p.1 p.2)))
      (𝓝[{p | 0 < p.1}] (0, ξ)) (𝓝 (0, fullerChartInv ξ)) := by
  sorry

/-- **The mirrored chart covers the switching points near `q_in`**: for `Im ξ₁ < 0` (as `q_in`'s
representatives), the mirrored chart coordinates tend to `(0, fullerChartInv (τ ξ))`. -/
theorem tendsto_lieChartInInv_phaseOfFuller {ξ : Fin 3 → ℂ} (hξ : (ξ 0).im < 0) :
    Tendsto (fun p : ℝ × (Fin 3 → ℂ) ↦ lieChartInInv (phaseOfFuller (scale p.1 p.2)))
      (𝓝[{p | 0 < p.1}] (0, ξ)) (𝓝 (0, fullerChartInv (tau ξ))) := by
  sorry

/-- **Near `q_out`, consecutive switching points follow the extended map** (Lemma 14.3.1: "These
functions give the value of the Reinhardt–Poincaré map", TeX 11838): along a chattering arc, if the
`n`-th switching point, rotated by `Ad_{R⁻ᵏ}`, is the chart point `lieChart p` with `p` near
`(0, x̃_out)` and `r > 0`, then the next one, rotated by `Ad_{R^{-(k+1)}}`, is `lieChart (e p)`:
the extremal follows the control `e₂` (rotated) from the `n`-th switching point, the unique optimal
control (`eventually_isSwitch_reinSwitchTime`), and switches next at `reinSwitchTime`. -/
theorem IsChatteringArcInto.eventually_follows_out {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ)
    {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) :
    ∃ W ∈ 𝓝 chartPtOut, ∀ (n k : ℕ) (p : ℝ × (Fin 3 → ℝ)), p ∈ W → 0 < p.1 →
      iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = lieChart p →
        0 < (e p).1 ∧ iso_adRinvPow (k + 1) (phaseAt X Λ₁ ΛR (τ (n + 1))) = lieChart (e p) := by
  sorry

/-- **Near `q_in`, consecutive switching points follow the inverse of the extended map** (Remark
14.3.4 in the mirrored chart): if the `n`-th switching point, rotated by `Ad_{R⁻ᵏ}`, is
`lieChartIn p` with `p` near `(0, x̃_out)` and `r > 0`, then the next one, rotated by
`Ad_{R^{-(k+1)}}`, is `lieChartIn p'` with `p' = reinChartMapIn p`, `r > 0` and `e p' = p`.

Proof (plan): through `F_in = τ F⁻¹ τ` (`remark14_3_4`), not by direct estimates at `q_in`, where
the switching functions have near-degenerate pairs of roots (see the module docstring of
`SmoothedPolygons/Ch14/FixedPointManifolds.lean`): the time reversal of the single arc
(`iso_vertexFlow_reinTau`, `switchingFn_reinTau`, `reinTau_spec`) carries the arc from
`lieChartIn p` to the arc of the Reinhardt–Poincaré map near `q_out` ending at `lieChart p`, where
`eventually_isSwitch_reinSwitchTime` gives the switching structure. -/
theorem IsChatteringArcInto.eventually_follows_in {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ)
    {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) :
    ∃ W ∈ 𝓝 chartPtOut, ∀ (n k : ℕ) (p : ℝ × (Fin 3 → ℝ)), p ∈ W → 0 < p.1 →
      iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = lieChartIn p →
        0 < (reinChartMapIn p).1 ∧ e (reinChartMapIn p) = p ∧
          iso_adRinvPow (k + 1) (phaseAt X Λ₁ ΛR (τ (n + 1))) = lieChartIn (reinChartMapIn p) := by
  sorry

/-- **`q_out` is not a cluster point** (TeX 13015–13026, claim (c) of the proof, repaired by the
hyperbolic box, G16.9): along a chattering arc into the singular locus, `q_out` is not a cluster
class of the switching points.

Proof (plan). Fix an extension `e` (`lemma14_3_1`) and the neighborhood `W₀` of
`eventually_follows_out`; choose a smaller neighborhood `W₁` with `e(W₁) ⊆ W₀`, on which every
rotated switching point whose chart coordinates lie in `W₀` is a genuine chart point
(`lieChart_lieChartInv`; `lieChartInv` alone ignores `z₃` and the section conditions, so the
representation must be checked). Build the chart sequence **by choice**: `p_n = lieChartInv
(Ad_{R^{-k}} q_n)` for the rotation `k` that makes `q_n` a chart point in `W₀`, if there is one,
and otherwise a junk point `(ρ_n, x̃_far)` with `x̃_far` outside `W₀` and `r = ρ_n → 0`. Then
`(p n).1 → 0` (`X → J` along the arc, `ρ_n → 0`), and on `W₁`, `(p n).1 > 0` and
`p (n + 1) = e (p n)` (`eventually_follows_out`, with `e (p n) ∈ W₀` and the uniqueness of the
chart representation). If `q_out ∈ Ω`, infinitely many rotated switching points have Fuller classes
near `q_out` and small `r`, so their chart coordinates tend to `(0, x̃_out)`
(`tendsto_lieChartInv_phaseOfFuller`) and `(0, x̃_out)` is a cluster point of `p`, against
`Function.not_mapClusterPt_of_transverse_expansion` applied with `W = W₁` and the derivative facts
of `hasStrictFDerivAt_extension` (`∂_r e₁ = r_scale > 1`, the zero block, the Fuller block with
eigenvalues of modulus `< 1/10`, `e (0, x̃) = (0, fullerChartMap x̃)` near `x̃_out`). -/
theorem qOut0_not_mem_switchClusterSet {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) :
    qOut0 ∉ switchClusterSet (switchAng X Λ₁ ΛR τ) := by
  sorry

/-- **Theorem 16.4.1, conditional on N5** (`ClusterSetForwardInvariant`) and on the three named
numerical facts of Theorem 16.1.1. See `theorem16_4_1`. -/
theorem theorem16_4_1_of_clusterSetForwardInvariant (h₁ : DOutContracts)
    (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims) (hN5 : ClusterSetForwardInvariant)
    {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}
    (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) :
    TendstoModVT (switchAng X Λ₁ ΛR τ) (ang (tau qOutCart)) ∧
      ∀ e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)),
        IsReinhardtPoincareExtension e → ∀ U ∈ 𝓝 chartPtOut, ∀ᶠ n in atTop,
          ∃ k : ℕ, ∃ p ∈ Function.localUnstableSet e chartPtOut U, 0 < p.1 ∧
            iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = lieChartIn p := by
  sorry

/-- **Theorem 16.4.1** (`thm:no-chatter`, the cluster point theorem; TeX 12840–12846), with the
three named numerical facts of Theorem 16.1.1 as hypotheses. Let `(u, g, X, Λ₁, Λ_R)` be a
Pontryagin extremal Reinhardt trajectory on `[a, b]` (normalized by `λ_cost = -1`, which
Lemma 8.2.2 allows at the singular locus) whose sequence of switching points `τ n ↑ b` has a
cluster point on the exceptional divisor reached in finite time (the lift meets the singular locus
at `b`), the switching points themselves not being on the divisor (`IsChatteringArcInto`). Then:
* the cluster point is `q_in`: the angular components `ξ_n` of the switching points converge to
  `q_in` (represented by `ang(τ q_out)`) modulo `V_T`, so `q_in` is the only cluster point;
* the switching points lie on the stable curve `W^s(q_in)`: eventually each, rotated onto the
  section `χ₂₃ = 0`, is `lieChartIn p` with `p` on the local unstable manifold of the extended map
  `e` at `q_out`, which is the local stable manifold of the Reinhardt–Poincaré map `e⁻¹` at `q_in`
  in the mirrored chart (Remark 14.3.4), a `C^∞` curve (Theorem 14.3.3).

Proof: `theorem16_4_1_of_clusterSetForwardInvariant` with N5 (`clusterSetForwardInvariant`);
the steps are in the module docstring. -/
theorem theorem16_4_1 (h₁ : DOutContracts) (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims)
    {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}
    (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) :
    TendstoModVT (switchAng X Λ₁ ΛR τ) (ang (tau qOutCart)) ∧
      ∀ e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)),
        IsReinhardtPoincareExtension e → ∀ U ∈ 𝓝 chartPtOut, ∀ᶠ n in atTop,
          ∃ k : ℕ, ∃ p ∈ Function.localUnstableSet e chartPtOut U, 0 < p.1 ∧
            iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = lieChartIn p :=
  theorem16_4_1_of_clusterSetForwardInvariant h₁ h₂ h₃ clusterSetForwardInvariant h

/-- **Theorem 16.4.1, time reversed** (the form used by the proof of Theorem 14.4.1, "All switches
must be on the unstable curve", TeX 12004–12005; G14.11): for a chattering arc out of the singular
locus (switching times `τ n ↓ a`), the angular components of the switching points converge to
`q_out` modulo `V_T`, and eventually each switching point, rotated onto the section `χ₂₃ = 0`, is
`lieChart p` with `p` on the local unstable manifold of `e` (the unstable curve `W^u(q_out)`).

Proof: `IsChatteringArcOutOf.reverse` and `theorem16_4_1`, with `fullerCoords_reinTau`
(`τ` maps `q_in` to `q_out`) and `lieChartIn = τ ∘ lieChart`. -/
theorem theorem16_4_1_reverse (h₁ : DOutContracts) (h₂ : CellTwoEntersDOut)
    (h₃ : BoxSubclaims) {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}
    (h : IsChatteringArcOutOf a b u g X Λ₁ ΛR τ) :
    TendstoModVT (switchAng X Λ₁ ΛR τ) (ang qOutCart) ∧
      ∀ e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)),
        IsReinhardtPoincareExtension e → ∀ U ∈ 𝓝 chartPtOut, ∀ᶠ n in atTop,
          ∃ k : ℕ, ∃ p ∈ Function.localUnstableSet e chartPtOut U, 0 < p.1 ∧
            iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = lieChart p := by
  sorry

end SmoothedPolygons
