module

public import SmoothedPolygons.Ch14.NoReturn
public import SmoothedPolygons.Ch14.NoReturnTools
public import SmoothedPolygons.Ch8.EdgePullback
public import SmoothedPolygons.Ch8.FiniteBangBang

/-!
# Chapter 14: the reading of "trajectory" in Theorem 14.4.1 is no restriction

`Theorem14_4_1` (`SmoothedPolygons/Ch14/NoReturn.lean`) reads "a trajectory of the Reinhardt
system" (Theorem 14.4.1, Hales–Vajjha, *Packings of Smoothed Polygons*, TeX 11995–12002) as an
extremal on `[a, c]` (`λ_cost = -1`) that is bang-bang with finitely many switches on every compact
subinterval of `(a, c)`. Whether the statement without that hypothesis has a counterexample was
left open when it was stated. It has none: **the two statements are equivalent**
(`theorem14_4_1_iff_unrestricted`).

## Why

The finite bang-bang hypothesis is used only before the first return to the singular locus, where
it holds anyway. A normal extremal (`λ_cost = -1 ≠ 0`) is edge extremal on every subinterval
(`IsExtremalOn.isEdgeExtremalOn_of_ne_zero`: the pulled-back costate is an edge costate, E55, E57),
so by Theorem 8.3.2 (`theorem8_3_2`) it is finitely bang-bang on every compact interval on which its
lift avoids the singular locus. In the first statement, if the lift met the singular locus at some
`t ∈ (a, c]`, then `t > b` (the chattering arc out of `a` avoids it on `(a, b]`), and the first
meeting time `s ∈ (b, t]` (`IsExtremalOn.exists_first_mem_singularLocus`) has the lift off the
singular locus on `(a, s)`; so the extremal on `[a, s]` is finitely bang-bang on compact
subintervals of `(a, s)`, and `Theorem14_4_1` on `[a, s]` (with the same `b`) says that the lift
avoids the singular locus at `s`: a contradiction. The second statement is the first for the
reflected extremal (`IsExtremalOn.reverse`, `IsChatteringArcInto.reverse`, as in
`theorem14_4_1_in`, `SmoothedPolygons/Ch14/NoReturnProof.lean`). The converse implication drops a
hypothesis.

Possible counterexamples to the unrestricted statement would have to be non-bang-bang extremals
that return to the singular locus: singular arcs (Theorem 8.2.3) lie in the singular locus, and
edge-singular arcs are excluded for normal extremals by edge extremality (Theorems 8.1.4, 8.3.2);
abnormal extremals (`λ_cost = 0`, Remark 8.1.6, E57), which can use any control in an edge, never
meet the singular locus (`IsExtremalOn.mem_singularLocus_iff` needs `λ_cost ≠ 0`), and every
extremal that meets it can be normalized to `λ_cost = -1` (`IsExtremalOn.normalize`). The bang-bang
clause inside `IsChatteringArcOutOf` / `IsChatteringArcInto` is likewise a consequence of
Theorem 8.3.2 (the lift avoids the singular locus on the open arc); it is kept there because the
switching sequence `τ` is part of the statement.

## Proof

`→`: the argument above (first statement: `exists_first_mem_singularLocus`, `IsExtremalOn.mono`,
`theorem8_3_2` with `isEdgeExtremalOn_of_ne_zero` for `α < β`, the empty case `β ≤ α` directly;
second statement: the reflection, as in `theorem14_4_1_in`). `←`: drop the hypothesis.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology
open TriFuller

/-- **The reading of Theorem 14.4.1 is no restriction**: `Theorem14_4_1` (for extremals that are
finitely bang-bang on compact subintervals of `(a, c)`) is equivalent to the same statement for all
extremals on `[a, c]` with `λ_cost = -1` (Theorem 8.3.2 supplies the finite bang-bang control up to
the first return to the singular locus, which is all the statement needs). -/
theorem theorem14_4_1_iff_unrestricted : Theorem14_4_1 ↔
    (∀ (a b c : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ),
      IsExtremalOn a c u g X Λ₁ ΛR (-1) → b ∈ Ioc a c →
      IsChatteringArcOutOf a b u g X Λ₁ ΛR τ →
      TendstoModVT (switchAng X Λ₁ ΛR τ) (ang qOutCart) →
      ∀ t ∈ Ioc a c, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus) ∧
    ∀ (a b c : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ),
      IsExtremalOn a c u g X Λ₁ ΛR (-1) → b ∈ Ico a c →
      IsChatteringArcInto b c u g X Λ₁ ΛR τ →
      TendstoModVT (switchAng X Λ₁ ΛR τ) (ang (tau qOutCart)) →
      ∀ t ∈ Ico a c, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus := by
  constructor
  · intro hT
    -- The first statement without the finite bang-bang hypothesis.
    have first : ∀ (a b c : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ),
        IsExtremalOn a c u g X Λ₁ ΛR (-1) → b ∈ Ioc a c →
        IsChatteringArcOutOf a b u g X Λ₁ ΛR τ →
        TendstoModVT (switchAng X Λ₁ ΛR τ) (ang qOutCart) →
        ∀ t ∈ Ioc a c, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus := by
      intro a b c u g X Λ₁ ΛR τ hext hb hout hconv t ht hmem
      have hoff := hout.2.2.1
      have htb : b < t := by
        by_contra hcon
        exact hoff t ⟨ht.1, not_lt.1 hcon⟩ hmem
      -- The first meeting time `s ∈ (b, t]`; the lift is off the singular locus on `(a, s)`.
      obtain ⟨s, hs, hsmem, hsoff⟩ :=
        hext.exists_first_mem_singularLocus hb.1.le htb.le ht.2 (hoff b ⟨hb.1, le_rfl⟩) hmem
      have has : a < s := hb.1.trans hs.1
      have hoff' : ∀ r ∈ Ioo a s, (g r, Λ₁ r, X r, ΛR r) ∉ singularLocus := by
        intro r hr
        rcases le_or_gt r b with hrb | hrb
        · exact hoff r ⟨hr.1, hrb⟩
        · exact hsoff r ⟨hrb.le, hr.2⟩
      -- Theorem 8.3.2 on compact subintervals of `(a, s)`.
      have hbb' : ∀ α β, a < α → β < s → IsFiniteBangBang α β u := by
        intro α β hα hβ
        rcases lt_or_ge α β with hαβ | hβα
        · have hsub := hext.mono hα.le hαβ (hβ.le.trans (hs.2.trans ht.2))
          exact theorem8_3_2 hsub (hsub.isEdgeExtremalOn_of_ne_zero (by norm_num))
            fun r hr ↦ hoff' r ⟨hα.trans_le hr.1, hr.2.trans_lt hβ⟩
        · exact ⟨∅, fun r hr _ ↦ absurd (hr.1.trans hr.2) (not_lt.2 hβα)⟩
      -- `Theorem14_4_1` on `[a, s]` (with the same `b`) at `s`: a contradiction.
      exact hT.1 a b s u g X Λ₁ ΛR τ (hext.mono le_rfl has (hs.2.trans ht.2)) ⟨hb.1, hs.1.le⟩
        hbb' hout hconv s ⟨has, le_rfl⟩ hsmem
    refine ⟨first, ?_⟩
    -- The second statement: the first for the reflected extremal, as in `theorem14_4_1_in`.
    intro a b c u g X Λ₁ ΛR τ hext hb hin hconv t ht hmem
    have hang : switchAng (fun t ↦ matTau (X (a + c - t))) (fun t ↦ matTau (Λ₁ (a + c - t)))
        (fun t ↦ matTau (ΛR (a + c - t))) (fun n ↦ a + c - τ n) =
          fun n ↦ tau (switchAng X Λ₁ ΛR τ n) := funext (switchAng_reverse (a + c) X Λ₁ ΛR τ)
    have hconv' := hconv.tau
    rw [tau_ang_tau_qOutCart] at hconv'
    have h1 := first a (a + c - b) c _ _ _ _ _ _ hext.reverse
      ⟨by linarith [hb.2], by linarith [hb.1]⟩ (hin.reverse a) (by rw [hang]; exact hconv')
      (a + c - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    apply h1
    simp only [sub_sub_cancel]
    exact reverse_mem_singularLocus_iff.2 hmem
  · -- `←`: drop the hypothesis.
    intro h
    exact ⟨fun a b c u g X Λ₁ ΛR τ h1 h2 _ h4 h5 ↦ h.1 a b c u g X Λ₁ ΛR τ h1 h2 h4 h5,
      fun a b c u g X Λ₁ ΛR τ h1 h2 _ h4 h5 ↦ h.2 a b c u g X Λ₁ ΛR τ h1 h2 h4 h5⟩

end SmoothedPolygons
