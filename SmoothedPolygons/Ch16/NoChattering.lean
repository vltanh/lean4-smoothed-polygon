module

public import SmoothedPolygons.Ch16.ClusterPoint
public import SmoothedPolygons.Ch14.NoReturn

/-!
# Chapter 16: the hypothesis of Mahler's First from Theorems 16.4.1 and 14.4.1

The last step of the proof of Theorem 16.3.1 (Mahler's First conjecture) of Hales–Vajjha,
*Packings of Smoothed Polygons* (TeX 12817–12833): "The proof then reduces to the consideration of
a trajectory such that the infinite sequence of switching points has a subsequence tending to the
singular locus. Passing to the blow-up, which has a compact exceptional divisor, the sequence of
switching points has a subsequence tending to a limit on the exceptional divisor in finite time.
By Theorem 16.4.1 … the limit is `q_in` and the sequence approaches `q_in` along the stable curve
`W^s(q_in)`. By Theorem 14.4.1 and its time reversal, the stable curve `W^s(q_in)` did not come
from the exceptional divisor at an earlier time. Thus, the trajectory is not periodic. This is
contrary to the boundary conditions of the Reinhardt conjecture."

Layer 3 stated this step as the named hypothesis `NoChatteringIntoSingularLocus` of
`theorem16_3_1` (`SmoothedPolygons/Ch16/MahlerFirst.lean`). Here it is derived from Theorem 16.4.1
(`theorem16_4_1`, proved in this layer from the three named numerical facts of Layer 5 and N5) and
Theorem 14.4.1 (the named proposition `Theorem14_4_1`, Layer 7):

* `noChatteringIntoSingularLocus_of_clusterSetForwardInvariant`: from the numerical facts, N5 and
  Theorem 14.4.1;
* `noChatteringIntoSingularLocus_of_theorem14_4_1`: from the numerical facts and Theorem 14.4.1
  (N5 proved, `clusterSetForwardInvariant`);
* `theorem16_3_1_of_theorem14_4_1`: **Mahler's First conjecture conditional on Theorem 14.4.1 and
  the three named numerical facts of Theorem 16.1.1**.

## The argument (the steps of the docstring of `NoChatteringIntoSingularLocus`)

Let `(u, g, X, Λ₁, Λ_R, λ_cost)` be a Pontryagin extremal on `[0, T]`, edge extremal, whose lift
meets `𝒮_sing` at `t ∈ (0, T]` and chatters into it from the left; we derive a contradiction.
1. `λ_cost ≠ 0` at `𝒮_sing` (`IsExtremalOn.mem_singularLocus_iff`), so `λ_cost < 0`; scaling the
   costate by `-1/λ_cost > 0` (`IsExtremalOn.normalize`) gives `λ_cost = -1`.
2. The periodic extension (Remark 6.6.1, `remark6_6_1`) is a solution of the state–costate system on
   `[0, 2T]` with `X(s + T) = R⁻¹ X(s) R` etc. (`IsExtremalOn 0 (2T)`, normalized as in step 1);
   `𝒮_sing` is invariant under the rotation (`R⁻¹ J R = J`), so the extension meets `𝒮_sing` at
   `t + T` and chatters into it (the rotated copy of the chattering at `t`, `δ ≤ t`).
3. Let `e` be the last time in `[t, t + T - δ]` at which the extension meets `𝒮_sing` (the meeting
   times form a closed set containing `t`). On `(e, t + T)` the lift avoids `𝒮_sing`, and the
   control is bang-bang with finitely many switches on every compact `[α, β] ⊆ (e, t + T)`. The
   extension is **not** claimed to be edge extremal on `[0, 2T]` (an edge arc straddling `T` would
   need one edge costate across `T`, which `IsEdgeExtremalOn 0 T` does not provide); instead the
   finite bang-bang property is glued at `T`: if `α < T < β`, Theorem 8.3.2 (`theorem8_3_2`, with
   the edge extremality of Proposition 8.1.3 on `[0, T]`) on `[α, T]` for the original extremal and
   on
   `[0, β - T]` for the rotated copy (the controls are relabelled by `u'(s + T) = u'(s) ∘ (· - 1)`,
   which preserves finite bang-bang), and the two finite switching sets together with `T` form a
   finite exceptional set on `[α, β]`; if `β ≤ T` or `T ≤ α`, one of the two applies directly.
4. `exists_isChatteringArcInto` applied on `[e, t + T]` (its hypotheses only need the lift off
   `𝒮_sing` on `(e, t + T)`) gives, for any `e' ∈ (e, t + T)`, a chattering arc into `t + T` on
   `[e', t + T]`; Theorem 16.4.1 (`theorem16_4_1`) says its switching points converge to `q_in`.
5. Theorem 14.4.1, second statement (`Theorem14_4_1`), on `[e, t + T]` with `b = e'`: the lift
   avoids `𝒮_sing` at `e`, a contradiction ("Thus, the trajectory is not periodic").
Size: 300–700 lines (the normalization, the gluing of finite bang-bang at `T`, the choice of `e`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology
open TriFuller

/-- **Normalization of the costate** (TeX 11484–11486: "We use the parameter values … `λ_cost = -1`.
Any trajectory that meets the singular locus must have these parameter values"; the Hamiltonian
and the costate equations are homogeneous of degree one in `(Λ₁, Λ_R, λ_cost)`): an extremal with
`λ_cost < 0`, with the costate scaled by `-1/λ_cost`, is an extremal with `λ_cost = -1`, and its
lift meets the singular locus at the same times. -/
theorem IsExtremalOn.normalize {a b lam : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) (hlam : lam < 0) :
    IsExtremalOn a b u g X (fun t ↦ (-lam)⁻¹ • Λ₁ t) (fun t ↦ (-lam)⁻¹ • ΛR t) (-1) ∧
      ∀ t, ((g t, (-lam)⁻¹ • Λ₁ t, X t, (-lam)⁻¹ • ΛR t) ∈ singularLocus ↔
        (g t, Λ₁ t, X t, ΛR t) ∈ singularLocus) := by
  sorry

/-- **The hypothesis of Mahler's First from Theorems 16.4.1 and 14.4.1**, with N5 as a hypothesis
(the steps are in the module docstring). -/
theorem noChatteringIntoSingularLocus_of_clusterSetForwardInvariant (h₁ : DOutContracts)
    (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims) (hN5 : ClusterSetForwardInvariant)
    (hNR : Theorem14_4_1) : NoChatteringIntoSingularLocus := by
  sorry

/-- **The hypothesis of Mahler's First from Theorem 14.4.1** and the three named numerical facts of
Theorem 16.1.1 (Theorem 16.4.1 is proved, `theorem16_4_1`). -/
theorem noChatteringIntoSingularLocus_of_theorem14_4_1 (h₁ : DOutContracts)
    (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims) (hNR : Theorem14_4_1) :
    NoChatteringIntoSingularLocus :=
  noChatteringIntoSingularLocus_of_clusterSetForwardInvariant h₁ h₂ h₃ clusterSetForwardInvariant
    hNR

/-- **Theorem 16.3.1** (`thm:mahler`, Mahler's First conjecture), **conditional on Theorem 14.4.1
and the three named numerical facts of Theorem 16.1.1** (`DOutContracts`, `CellTwoEntersDOut`,
`BoxSubclaims`): the global minimizer of the Reinhardt optimal control problem is a bang-bang
solution with finitely many switches, and the minimizer `K_min` is a finite-sided smoothed polygon
with rounded hyperbolic arcs at each corner of the sort described by Reinhardt and Mahler. -/
theorem theorem16_3_1_of_theorem14_4_1 (h₁ : DOutContracts) (h₂ : CellTwoEntersDOut)
    (h₃ : BoxSubclaims) (hNR : Theorem14_4_1) :
    (∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsReinhardtMinimizer T u g X →
      IsFiniteBangBang 0 T u) ∧
    ∀ K : Set (Fin 2 → ℝ), IsWorstDisk K → IsSmoothedPolygon K :=
  theorem16_3_1 (noChatteringIntoSingularLocus_of_theorem14_4_1 h₁ h₂ h₃ hNR)

end SmoothedPolygons
