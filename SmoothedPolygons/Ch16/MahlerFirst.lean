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
   `l3st_mem_singularLocus_iff`; Lemma 8.2.2), and the costate may be normalized to
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
The hypothesis is stated for every Pontryagin extremal, as Theorem 16.4.1 is; it concerns only
extremals with their boundary conditions (locally, chattering into `𝒮_sing` does occur: the inward
spirals along `W^s(q_in)` of Chapters 13–16).

**Why it is not an axiom.** It is a `Prop`, a hypothesis of `theorem16_3_1`, visible in its
statement; nothing in the library assumes it. `theorem16_3_1` reads "`NoChatteringIntoSingularLocus`
implies Mahler's First conjecture", and its axioms are Lean's standard ones once its proof is
complete. The later layers replace the hypothesis by a proof (Theorems 16.4.1 and 14.4.1).

**Why it suffices** (`l3st_forall_not_mem_singularLocus`): with Chapters 2–8 it rules out every
meeting of the minimizer's lift with `𝒮_sing`; the minimizer is then bang-bang with finitely many
switches by Theorem 8.3.2. -/
def NoChatteringIntoSingularLocus : Prop :=
  ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ),
    IsPontryaginExtremal T u g X Λ₁ ΛR lam → ∀ t ∈ Ioc 0 T,
      (g t, Λ₁ t, X t, ΛR t) ∈ singularLocus → ¬ IsChatteringInto u g X Λ₁ ΛR t

/-- **The minimizer is bang-bang with finitely many switches away from the singular locus**
(label of this formalization `thm:mahler:away`; the part of Theorem 16.3.1 that holds without the
hypothesis, TeX 12811–12815). Let `(g, X)` be a global minimizer of the Reinhardt problem and
`(Λ₁, Λ_R, λ_cost)` a lift of it to a Pontryagin extremal. On every interval `[a, b] ⊆ [0, T]` on
which the lift does not meet `𝒮_sing`, the control is bang-bang with finitely many switches.

Proof: Proposition 8.1.3 (`proposition8_1_3`: the minimizer is edge extremal on `[0, T]`, so on
`[a, b]`, `l3st_isEdgeExtremalOn_mono`), the restriction of the extremal to `[a, b]`
(`l3st_isExtremalOn_of_isPontryaginExtremal`), and Theorem 8.3.2 (`theorem8_3_2`). Expected size:
10–20 lines. -/
theorem isFiniteBangBang_of_isReinhardtMinimizer_of_not_mem_singularLocus {T : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X)
    {Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
    (hS : ∀ t ∈ Icc a b, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus) :
    IsFiniteBangBang a b u := by
  sorry

/-- **Under the hypothesis, the lift of a global minimizer never meets the singular locus** (the
core of the proof of Theorem 16.3.1, TeX 12811–12833, with gap G16.7 repaired: the set of meeting
times could a priori be infinite and nowhere dense, and the proof works on a complementary
interval).

Proof:
1. `Z = {t ∈ [0, T] | lift(t) ∈ 𝒮_sing}` is closed (`l3st_mem_singularLocus_iff`,
   `l3st_continuousOn_lift`). Suppose `Z ≠ ∅`.
2. `Z ∩ (0, T] ≠ ∅`: if `0 ∈ Z` then `T ∈ Z`, since `X(T) = R⁻¹X(0)R`, `Λ₁(T) = R⁻¹Λ₁(0)R`,
   `Λ_R(T) = R⁻¹Λ_R(0)R` and `R⁻¹JR = J`.
3. `Z` has empty interior: on an open interval inside `Z`, `Λ_R ≡ 0`, the Hamiltonian is
   independent of the control, against Theorem 8.2.7 in the case its proof covers
   (`l3st_not_hamiltonian_const_of_isReinhardtMinimizer`; "A trajectory cannot remain on the
   singular locus for any positive interval of time").
4. Take `z ∈ Z ∩ (0, T]`, `p ∈ (0, z) ∖ Z` (step 3), and `d = inf (Z ∩ [p, T])`: `d ∈ Z`,
   `p < d ≤ z`, and `[p, d)` avoids `Z`.
5. On every compact `[α, β] ⊆ (p, d)` the control is bang-bang with finitely many switches
   (`isFiniteBangBang_of_isReinhardtMinimizer_of_not_mem_singularLocus`: Proposition 8.1.3 and
   Theorem 8.3.2).
6. The hypothesis (`NoChatteringIntoSingularLocus` at `d`, with `δ = d - p`) gives `ε > 0` with no
   switching time in `(d - ε, d)`; with step 5, the control is a.e. constant at one vertex on
   `(d - ε', d)` (the vertex cannot change across a point that is not a switching time, and
   `(d - ε', d)` is connected).
7. Lemma 8.3.4 (`lemma8_3_4`) on `[d - ε', d]` (`l3st_isExtremalOn_of_isPontryaginExtremal`): the
   lift does not meet `𝒮_sing` at `d` ("A trajectory cannot reach the singular locus with finitely
   many switches"), against `d ∈ Z`.
Expected size: 200–350 lines. -/
theorem l3st_forall_not_mem_singularLocus (hNC : NoChatteringIntoSingularLocus) {T : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X)
    {Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) :
    ∀ t ∈ Icc 0 T, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus := by
  sorry

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
   `l3st_forall_not_mem_singularLocus` (Theorem 8.2.7's covered case, Lemma 8.3.4 and the
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
   (`l3st_isSmoothedPolygonBoundary_of_image`); `K_min` is a centrally symmetric convex disk
   (`IsWorstDisk`) without corners (Lemma 2.2.5, `lemma2_2_5`, through
   `ch2_isWorstLatticeDisk_iff_isWorstDisk`).
Expected size: 60–120 lines. -/
theorem theorem16_3_1 (hNC : NoChatteringIntoSingularLocus) :
    (∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsReinhardtMinimizer T u g X →
      IsFiniteBangBang 0 T u) ∧
    ∀ K : Set (Fin 2 → ℝ), IsWorstDisk K → IsSmoothedPolygon K := by
  sorry

end SmoothedPolygons
