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

## Proofs (planned)

`IsExtremalOn.reverse`: the private `l6e_isStateCostateSolution_reverse` of
`SmoothedPolygons/Ch16/ClusterCoordinates.lean` (the reversibility of the state–costate system in
the integral form) applied to the solution `t ↦ (u, g, X, Λ₁, Λ_R)(a + t)` on `[0, c - a]`, as in
the first bullet of the proof of `IsChatteringArcOutOf.reverse`
(`a + c - (a + t) = a + (c - a - t)`). That lemma and its helpers (`l6e_controlP_swap`,
`l6e_hamiltonian_swap`, `l6e_swap_mem_controlSimplex`, `l6e_vertex_swap`,
`l6e_isIntegralCurve_reverse`,
`l6e_isIntegralCurve_matTau`, `l6e_isIntegralCurve_diagD`, `l6e_matTau_comm`, `l6e_matTau_combo`,
`l6e_det_diagD_conj`, …) are private: copy them here with a new prefix (about 200 lines), or make
them public in ClusterCoordinates.lean (no statement changes). `IsFiniteBangBang.reverseControl`
and `reverse_mem_singularLocus_iff` are the private `l6e_isFiniteBangBang_reverse` and
`l6e_mem_singularLocus_reverse` (`reverseControl a c u` depends on `a + c` only).
`IsChatteringArcInto.reverse`: as `IsChatteringArcOutOf.reverse`, with the reflection
`t ↦ a + c - t` mapping `[b, c]` onto `[a, a + c - b]` (`l6e_isSwitchingTime_reverse_iff`).
`switchAng_reverse`: `phaseAt` of the reversed curves at `m - τ n` is `reinTau` of the phase point
at `τ n`; `fullerCoords_reinTau` and `tau_ang` (as in `theorem16_4_1_reverse`).
`TendstoModVT.tau`: `τ` is an isometry of `ℂ³` (sup metric) and maps the `V_T`-orbit of `ξ` onto
that of `τ ξ` (`τ (v • w) = v̄ • τ w`, `V_T` closed under conjugation), so
`infDist (τ ξ_n) (orbit (τ ξ)) = infDist ξ_n (orbit ξ)` (the computation `hiso`, `horb` in the proof
of `theorem16_4_1_reverse`). `exists_first_mem_singularLocus`: `s = sInf Z` with
`Z = {r ∈ [b, t] | lift(r) ∈ 𝒮_sing}`, closed (`mem_singularLocus_iff` turns membership into the
closed conditions `Λ₁ = (3/2) λ J`, `X = J`, `Λ_R = 0`, and the lift is continuous on `[a, c]`),
nonempty (`t`), and `b ∉ Z` (the construction of `e` in the proof of
`noChatteringIntoSingularLocus_of_clusterSetForwardInvariant`, mirrored).
Size: 300–400 lines (about 200 of them the copied reversal helpers).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology MeasureTheory
open TriFuller

/-- **Time reversal of an extremal on `[a, c]`** (Remark 10.2.3, `eqn:wbc-reverse`; "by time
reversal", TeX 12012–12013): reflected by `t ↦ a + c - t`, with `g ↦ D g D`, `M ↦ -D M D` on
`X, Λ₁, Λ_R` and the controls relabelled `e₂ ↔ e₃`, an extremal on `[a, c]` is an extremal on
`[a, c]` with the same `λ_cost`. -/
theorem IsExtremalOn.reverse {a c lam : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsExtremalOn a c u g X Λ₁ ΛR lam) :
    IsExtremalOn a c (reverseControl a c u) (fun t ↦ diagD * g (a + c - t) * diagD)
      (fun t ↦ matTau (X (a + c - t))) (fun t ↦ matTau (Λ₁ (a + c - t)))
      (fun t ↦ matTau (ΛR (a + c - t))) lam := by
  sorry

/-- Finite bang-bang control under the time reversal: the exceptional set is reflected and the
vertices are relabelled (`reverseControl a c u` reflects about `(a + c)/2`). -/
theorem IsFiniteBangBang.reverseControl {a c α β : ℝ} {u : ℝ → Fin 3 → ℝ}
    (h : IsFiniteBangBang (a + c - β) (a + c - α) u) :
    IsFiniteBangBang α β (SmoothedPolygons.reverseControl a c u) := by
  sorry

/-- The singular locus is invariant under the time reversal (`-DJD = J`, `det(DgD) = det g`). -/
theorem reverse_mem_singularLocus_iff {G A B C : Mat2} :
    (diagD * G * diagD, matTau A, matTau B, matTau C) ∈ singularLocus ↔
      (G, A, B, C) ∈ singularLocus := by
  sorry

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
  sorry

/-- **The angular components of the reversed switching points** are the Fuller `τ` of those of the
switching points (`fullerCoords_reinTau`, `tau_ang`). -/
theorem switchAng_reverse (m : ℝ) (X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ) (n : ℕ) :
    switchAng (fun t ↦ matTau (X (m - t))) (fun t ↦ matTau (Λ₁ (m - t)))
        (fun t ↦ matTau (ΛR (m - t))) (fun n ↦ m - τ n) n =
      tau (switchAng X Λ₁ ΛR τ n) := by
  sorry

/-- **Convergence modulo `V_T` is preserved by the Fuller `τ`** (`τ` is an isometry mapping the
`V_T`-orbit of `ξ` onto that of `τ ξ`). -/
theorem TendstoModVT.tau {ξs : ℕ → Fin 3 → ℂ} {ξ : Fin 3 → ℂ} (h : TendstoModVT ξs ξ) :
    TendstoModVT (fun n ↦ TriFuller.tau (ξs n)) (TriFuller.tau ξ) := by
  sorry

/-- `τ` maps the representative `ang (τ q_out)` of `q_in` to the representative `ang q_out` of
`q_out`. -/
theorem tau_ang_tau_qOutCart : tau (ang (tau qOutCart)) = ang qOutCart := by
  sorry

/-- **The first meeting with the singular locus**: if the lift of an extremal on `[a, c]` is off the
singular locus at `b` and on it at `t ∈ [b, c]`, there is a first time `s ∈ (b, t]` at which it
meets the singular locus, and it avoids it on `[b, s)` (the meeting times form a closed set). -/
theorem IsExtremalOn.exists_first_mem_singularLocus {a c lam : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} (h : IsExtremalOn a c u g X Λ₁ ΛR lam) {b t : ℝ} (hab : a ≤ b)
    (hbt : b ≤ t) (htc : t ≤ c) (hb : (g b, Λ₁ b, X b, ΛR b) ∉ singularLocus)
    (ht : (g t, Λ₁ t, X t, ΛR t) ∈ singularLocus) :
    ∃ s ∈ Ioc b t, (g s, Λ₁ s, X s, ΛR s) ∈ singularLocus ∧
      ∀ r ∈ Ico b s, (g r, Λ₁ r, X r, ΛR r) ∉ singularLocus := by
  sorry

end SmoothedPolygons
