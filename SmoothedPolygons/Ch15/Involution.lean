module

public import SmoothedPolygons.Ch15.Continuity

/-!
# Chapter 15: the involution `𝔦 = τ F`, the partition `𝒟₀, …, 𝒟₄` (§15.3)

§15.3 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Involution", TeX 12316–12493):

* `F⁻¹ = τ F τ` and the involution `𝔦 := τ ∘ F` (TeX 12324–12328), made precise (gap G15.6):
  - for the Poincaré map `poincare`, `F(τ F(z)) = τ(z)` holds exactly at the **switching points**,
    the points whose first control is not also their most recent control
    (`poincare_tau_poincare_eq_tau_iff`); every image `F(z)` is a switching point, and the points of
    the top faces `𝒞₂(ζ^{±1}, 0, 2)` are not (`not_isSwitchingPoint_of_mem_topFace`), so the book's
    identity on the closed 3-cells fails there for `poincare` (for example
    `z = (-0.3 + 0.7i, -0.6, -0.84) ∈ 𝒞₂(ζ, 0, 2)`: `t_sw(z) = 5.18584`, `t_sw(τ F z) = 9.38584`);
  - for the book's root-based branch maps it holds **branch-wise**: switching at a time `T` with a
    control `u`, then reversing, switching at the same time `T` with `ū` and reversing again is the
    identity (`tau_flow_tau_flow`);
  - on `Ξ_{𝒲,0}/V_T`: `isSwitchingPointQ_poincareAngZero`,
    `poincareAngZero_tauZero_poincareAngZero`, `involution_involution`;
* "in involution" (`InInvolution`), the loci `∂_res = 𝔦(𝒞₂(ζ, 1, 1))`, `∂_A = 𝔦(𝒞₂(ζ, 0, 2))`,
  `∂_{A,ζ²} = 𝔦(𝒞₂^A)` (with the book's `F_A`), `∂_B = 𝔦(𝒞₂^B)`, and the vanishing of the resultant
  and discriminants along them (from Lemma 13.2.4, TeX 12336–12345, 12425–12427, 12441–12443);
* the parts `𝒟₀, …, 𝒟₄` (TeX 12347–12443), the notion of geometric partition, and Proposition
  15.3.2 as the named proposition `Proposition15_3_2`;
* Remark 15.3.1 (with `q_in` and `q_out` corrected, gap G15.1) is in
  `SmoothedPolygons/Ch15/FixedPointCells.lean`.

## The parts

The book defines `𝒟₁` as "the part of the geometric partition [of the first big cell by
`∂_res ∪ ∂_A`] containing the face `𝒞₂(ζ, 0, 2)`", `𝒟₂`, `𝒟₃` as the two parts of the second big
cell cut by `∂_{A,ζ²}`, with active switching functions `χ_{A,0}` and `χ_{B,1}`, `𝒟₄ := 𝔦(𝒟₃)` and
`𝒟₀ := closure(𝒞₃(ζ) ∖ (𝒟₁ ∪ 𝒟₄))`. Here the parts with a given active switching function are
defined directly by the switch of `poincare` on the open boxes (`switchSet`: the first control of
`F(z)` is `1` when the active function is `χ_A`, and `ū` when it is `χ_B`): `𝒟₂`, `𝒟₃` and `𝒟₄` are
the closures of these sets; `𝒟₁` is the closure of the union of the connected components of the
open first box minus `∂_A ∪ ∂_res` whose closures meet the top face; `𝒟₀` is as in the book. That
these coincide with the book's construction (`𝔦(𝒟₃) = 𝒟₄`), form geometric partitions, and carry
continuous extensions `F_i` of `F` is the content of Proposition 15.3.2, which the book supports
only by Figures 15.2–15.3 ("The proof is contained in the discussion leading up to the
proposition"; gap G15.2). It is stated here as the named proposition `Proposition15_3_2`, to be
certified (layer 5b) or kept as a hypothesis; **Theorem 16.1.1 does not use it**
(`SmoothedPolygons/Ch16/GlobalBasin.lean` works with boxes and the switch of `poincare` directly).

## Proofs

The switching-point facts follow from Lemma 13.2.5 (`lemma13_2_5`, `poincare_tau_poincare`):
`F(z)` has most recent control the first control of `z`, which differs from its own first control
(`firstControl_poincare_ne`); `τ` exchanges first and most recent controls (conjugated). The
vanishing along the `∂`-loci: by Lemma 13.2.4 (`lemma13_2_4`) the switching functions at
`τ(z(T, z⁰, u))` with control `ū` are those at `z⁰` reversed in time about `T`, so a root of order
`m` at `t = 0` at `z⁰` becomes a root of order `m` at `t = T`; the rotation (13.2.7)
(`eqn13_2_7`) and the rescaling (Lemma 13.2.1) bring the point to cell coordinates, multiplying the
switching functions by positive constants and rescaling time.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology Polynomial
open scoped Real

namespace TriFuller

/-! ### Switching points and `F⁻¹ = τ F τ` -/

/-- `z` is a **switching point**: its first control is not also its most recent control, so the
extremal through `z` switches at `z` (TeX 10880–10906). -/
def IsSwitchingPoint (z : Fin 3 → ℂ) : Prop := ¬ IsMostRecentControl z (firstControl z)

/-- Every image `F(z)`, `z ≠ 0`, is a switching point: its most recent control is the first control
of `z` (the control used on `[0, t_sw]`), and its first control differs from it
(`firstControl_poincare_ne`). -/
theorem isSwitchingPoint_poincare {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    IsSwitchingPoint (poincare z) := by
  sorry

/-- `τ` preserves switching points: by Lemma 13.2.5 the first control of `τ(z)` is the conjugate
of the most recent control of `z`, and the most recent control of `τ(z)` the conjugate of the first
control of `z`. -/
theorem isSwitchingPoint_tau_iff {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    IsSwitchingPoint (tau z) ↔ IsSwitchingPoint z := by
  sorry

/-- The virial group preserves switching points (Lemmas 13.2.1, 13.2.2). -/
theorem isSwitchingPoint_smul_scale_iff {v : ℂ} (hv : v ∈ VT) {r : ℝ} (hr : 0 < r)
    {z : Fin 3 → ℂ} (hz : z ≠ 0) : IsSwitchingPoint (v • scale r z) ↔ IsSwitchingPoint z := by
  sorry

/-- **`F⁻¹ = τ F τ` for the Poincaré map, exactly at switching points** (TeX 12324–12328; gap
G15.6). For `z ≠ 0`, `F(τ F(z)) = τ(z)` if and only if `z` is a switching point: "if" is
`poincare_tau_poincare`; "only if" because `F(τ F z)` is a switching point
(`isSwitchingPoint_poincare`) and `τ(z)` is one only if `z` is (`isSwitchingPoint_tau_iff`). -/
theorem poincare_tau_poincare_eq_tau_iff {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    poincare (tau (poincare z)) = tau z ↔ IsSwitchingPoint z := by
  sorry

/-- **`F⁻¹ = τ F τ` branch-wise** (TeX 12324–12328; gap G15.6): for any switching time `T` and
control `u` (in particular for the book's root-based maps on closed cells, which switch at a root
`T` of a switching function, double roots included), `τ(z(T, τ(z(T, z⁰, u)), ū)) = z⁰` (Lemma
13.2.5, `tau_flow_neg`, and the flow property `flow_add`). -/
theorem tau_flow_tau_flow (T : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    tau (flow T (tau (flow T z u)) (starRingEnd ℂ u)) = z := by
  sorry

/-- **The top faces consist of non-switching points** (gap G15.6): at a point of `𝒞₂(ζ, 0, 2)`
(resp. `𝒞₂(ζ², 0, 2)`) the switching function `χ_B` has a double root at `t = 0` with
`χ_{B,2}(0) = ±y₁/2 > 0` and `χ_A(0) > 0`, so the first control `ζ` (resp. `ζ²`) is optimal on both
sides of `t = 0` and is also the most recent control. By `poincare_tau_poincare_eq_tau_iff`, the
identity `F⁻¹ = τ F τ` that the book uses on the closed big cells fails on both top faces. -/
theorem not_isSwitchingPoint_of_mem_topFace :
    (∀ p ∈ topFaceOne, ¬ IsSwitchingPoint (cellPoint p)) ∧
      ∀ p ∈ topFaceTwo, ¬ IsSwitchingPoint (cellPoint p) := by
  sorry

/-- **The switching point before a non-switching point**: a non-switching point `z ≠ 0` lies in the
interior of a constant-control arc that starts at a switching point `w` (its most recent switching
time is finite, Lemma 13.2.5): `z = z(s, w, u)` with `0 < s < t_sw(w)`, `u` the first control of
`w`, and `F(w) = F(z)`. -/
theorem exists_isSwitchingPoint_of_not {z : Fin 3 → ℂ} (hz : z ≠ 0)
    (h : ¬ IsSwitchingPoint z) :
    ∃ w : Fin 3 → ℂ, w ≠ 0 ∧ w 2 ∈ walls ∧ IsSwitchingPoint w ∧
      ∃ s ∈ Ioo 0 (firstSwitchTime w), z = flow s w (firstControl w) ∧
        poincare w = poincare z := by
  sorry

/-! ### The involution on `Ξ_{𝒲,0}/V_T` -/

/-- A point of `Ξ_{𝒲,0}/V_T` is a switching point if a representative is (equivalently every one,
`isSwitchingPoint_smul_scale_iff`). -/
def IsSwitchingPointQ (x : XiW0Quot) : Prop :=
  ∃ z ∈ sectionZero, classOf z = x ∧ IsSwitchingPoint z

/-- Every representative of a switching point is a switching point. -/
theorem isSwitchingPointQ_iff (x : XiW0Quot) :
    IsSwitchingPointQ x ↔ ∀ z ∈ sectionZero, classOf z = x → IsSwitchingPoint z := by
  sorry

/-- Every image `F(x)` is a switching point (`isSwitchingPoint_poincare`). -/
theorem isSwitchingPointQ_poincareAngZero (x : XiW0Quot) :
    IsSwitchingPointQ (poincareAngZero x) := by
  sorry

/-- `τ` preserves switching points (`isSwitchingPoint_tau_iff`). -/
theorem isSwitchingPointQ_tauZero_iff (x : XiW0Quot) :
    IsSwitchingPointQ (tauZero x) ↔ IsSwitchingPointQ x := by
  sorry

/-- **`F(τ F(x)) = τ(x)` at switching points of `Ξ_{𝒲,0}/V_T`** (`poincare_tau_poincare`,
`poincareAngZero_classOf`, `tauZero_classOf`). -/
theorem poincareAngZero_tauZero_poincareAngZero {x : XiW0Quot} (hx : IsSwitchingPointQ x) :
    poincareAngZero (tauZero (poincareAngZero x)) = tauZero x := by
  sorry

/-- The involution `𝔦 := τ ∘ F` (TeX 12324–12328). -/
noncomputable def involution (x : XiW0Quot) : XiW0Quot := tauZero (poincareAngZero x)

/-- "`𝔦 := τ ∘ F` is an involution: `𝔦 = 𝔦⁻¹`" (TeX 12326–12328), on switching points (gap G15.6):
`𝔦(𝔦(x)) = τ F τ F x = τ τ x = x`, and `𝔦(x)` is again a switching point. -/
theorem involution_involution {x : XiW0Quot} (hx : IsSwitchingPointQ x) :
    IsSwitchingPointQ (involution x) ∧ involution (involution x) = x := by
  sorry

/-- Two sets are **in involution** if `𝔦(𝒟) = 𝒟̃` and `𝔦(𝒟̃) = 𝒟` (TeX 12330–12332). -/
def InInvolution (D D' : Set XiW0Quot) : Prop := involution '' D = D' ∧ involution '' D' = D

/-- "The two fixed points `q_in, q_out ∈ 𝒟₁` are in involution" (TeX 12363–12364):
`𝔦(q_out) = τ F(q_out) = τ(q_out) = q_in` and `𝔦(q_in) = q_out` (Lemma 13.5.2, `tauQuot_qOut`). -/
theorem inInvolution_qOut0_qIn0 : InInvolution {qOut0} {qIn0} := by
  sorry

/-! ### The loci `∂_res`, `∂_A`, `∂_{A,ζ²}`, `∂_B` -/

/-- The resultant locus `∂_res := 𝔦(𝒞₂(ζ))` (TeX 12333–12336), `𝒞₂(ζ) = 𝒞₂(ζ, 1, 1)` viewed as the
front and back faces of the first big cell. -/
noncomputable def bdRes : Set XiW0Quot := involution '' (cellClass '' frontBackOne)

/-- The discriminant locus `∂_A := 𝔦(𝒞₂(ζ, 0, 2))` (TeX 12339–12343), `𝒞₂(ζ, 0, 2)` viewed as the
top face `θ₂ = π` of the first big cell (where `poincare` is the book's map,
`continuousWithinAt_topFaceOne`). -/
noncomputable def bdA : Set XiW0Quot := involution '' (cellClass '' topFaceOne)

/-- `∂_{A,ζ²} := 𝔦(𝒞₂^A)` (TeX 12424–12426), with the book's root-based map `F_A` on `𝒞₂^A`. -/
noncomputable def bdAζ2 : Set XiW0Quot :=
  (fun p ↦ classOf (tau (cellMapA (cellPoint p)))) '' topFaceTwoA

/-- `∂_B := 𝔦(𝒞₂^B)` (TeX 12441–12442), with `F_B` (which is `poincare` on `𝒞₂^B`,
`firstSwitchTime_topFaceTwo`). -/
noncomputable def bdB : Set XiW0Quot :=
  (fun p ↦ classOf (tau (cellMapB (cellPoint p)))) '' topFaceTwoB

/-- **The resultant and the discriminants vanish along the `∂`-loci** (Lemma 13.2.4, TeX
12336–12345, 12425–12427 (gap G15.4: "`Δ_{A,0}` vanishes along `∂_A`" there means `∂_{A,ζ²}`),
12441–12443), at their points in the open big cells:
* along `∂_res`, `res_AB = 0`: the trajectory reaches `z₃ = 0` at the switching time `T`, a common
  root of `χ_{A,0}` and `χ_{B,1}`;
* along `∂_A`, `Δ_{A,0} = 0`: `χ_B` has a double root at `0` on the top face `𝒞₂(ζ, 0, 2)`, which
  becomes a double root of `χ_{A,0}` at `T` (`χ^ζ_{ζ-ζ²}` reversed and rotated by `ζ²` is
  `χ^ζ_{ζ-1}`);
* along `∂_{A,ζ²}`, `Δ_{A,0} = 0` for the control `ζ²` (`χ_B` on `𝒞₂(ζ², 0, 2)` becomes `χ_A`);
* along `∂_B`, `Δ_{B,1} = 0` (`χ_B` on `𝒞₂(ζ², 0, 2)` becomes `χ_B` of the control `ζ`).

Proof route: Lemma 13.2.4 (`lemma13_2_4`), (13.2.7) (`eqn13_2_7`), Lemma 13.2.1, and
`Polynomial.resultant_eq_zero_iff`, `Polynomial.resultant_deriv` (a double root makes the
discriminant vanish). -/
theorem discr_resAB_eq_zero_of_mem_bd :
    (∀ q ∈ openBoxOne, cellClass q ∈ bdRes → resAB ζ (cellPoint q) = 0) ∧
      (∀ q ∈ openBoxOne, cellClass q ∈ bdA → discrA ζ (cellPoint q) = 0) ∧
      (∀ q ∈ openBoxTwo, cellClass q ∈ bdAζ2 → discrA (ζ ^ 2) (cellPoint q) = 0) ∧
      ∀ q ∈ openBoxOne, cellClass q ∈ bdB → discrB ζ (cellPoint q) = 0 := by
  sorry

/-! ### The parts `𝒟₀, …, 𝒟₄` -/

/-- The points of an open box at which the Poincaré map switches to the control `v`: the first
control of `F(cellPoint p)` is `v` (on the first cell, `v = 1` when the active switching function is
`χ_A`, `v = ζ²` when it is `χ_B`; on the second cell, `v = 1` resp. `v = ζ`). -/
noncomputable def switchSet (box : Set (Fin 3 → ℝ)) (v : ℂ) : Set (Fin 3 → ℝ) :=
  {p | p ∈ box ∧ firstControl (poincare (cellPoint p)) = v}

/-- The points of the open first box in a set of `Ξ_{𝒲,0}/V_T` (for the loci `∂_A`, `∂_res`). -/
noncomputable def boxCoords (S : Set XiW0Quot) : Set (Fin 3 → ℝ) :=
  {p | p ∈ openBoxOne ∧ cellClass p ∈ S}

/-- `𝒟₁` (TeX 12359–12366): "the part of the geometric partition [of the first big cell by
`∂_res ∪ ∂_A`] containing the face `𝒞₂(ζ, 0, 2)` (that is, the face `θ₂ = π`)": the closure of the
union of the connected components of the open first box minus the closure of `∂_A ∪ ∂_res` whose
closures meet the top face. -/
noncomputable def partD1 : Set (Fin 3 → ℝ) :=
  closure {p | p ∈ openBoxOne \ closure (boxCoords (bdA ∪ bdRes)) ∧
    (closure (connectedComponentIn (openBoxOne \ closure (boxCoords (bdA ∪ bdRes))) p) ∩
      topFaceOne).Nonempty}

/-- `𝒟₂` (TeX 12427–12434): the part of the second big cell containing `𝒞₂^A`, on which the active
switching function is `χ_{A,0}`: the closure of the points of the open second box switching to
`1`. -/
noncomputable def partD2 : Set (Fin 3 → ℝ) := closure (switchSet openBoxTwo 1)

/-- `𝒟₃` (TeX 12436–12438): the other part of the second big cell, on which the active switching
function is `χ_{B,1}`: the closure of the points switching to `ζ`. -/
noncomputable def partD3 : Set (Fin 3 → ℝ) := closure (switchSet openBoxTwo ζ)

/-- `𝒟₄ := 𝔦(𝒟₃)` (TeX 12438–12440), the part of the first big cell on which the active switching
function is `χ_{B,1}`: the closure of the points of the open first box switching to `ζ²` (that it is
`𝔦(𝒟₃)` is part of `Proposition15_3_2`). -/
noncomputable def partD4 : Set (Fin 3 → ℝ) := closure (switchSet openBoxOne (ζ ^ 2))

/-- `𝒟₀` (TeX 12440–12443): "the closure of the complement in the first big cell of the union of
`𝒟₁` and `𝒟₄`". -/
noncomputable def partD0 : Set (Fin 3 → ℝ) := closure (closedBoxOne \ (partD1 ∪ partD4))

/-- The five parts, indexed as in the book. -/
noncomputable def partD : Fin 5 → Set (Fin 3 → ℝ) := ![partD0, partD1, partD2, partD3, partD4]

/-- A **geometric partition** of a set (TeX 12347–12350): "a collection of regular closed subsets
covering the set whose interiors are disjoint" (regular closed: the closure of its interior). -/
def IsGeometricPartition {α : Type*} [TopologicalSpace α] (S : Set α) (P : List (Set α)) :
    Prop :=
  (∀ D ∈ P, closure (interior D) = D) ∧ (∀ x, x ∈ S ↔ ∃ D ∈ P, x ∈ D) ∧
    P.Pairwise fun D D' ↦ Disjoint (interior D) (interior D')

/-- **Proposition 15.3.2** (TeX 12467–12491), as a named proposition (it rests on Figures
15.2–15.3; gap G15.2). "Let `𝒟_i`, `i = 0, 1, 2, 3, 4` be the geometric partition of the two big
cells defined as above. The Fuller–Poincaré map extends continuously from the interiors of `𝒟_i`
to functions `F_i` on the closures `𝒟_i`, for `i = 0, 1, 2, 3, 4`. The involution acts on the parts
by `𝒟₃ ↔ 𝒟₄`. Moreover, `𝒟₁, 𝒟₂, 𝒟₀` are each in self involution."

Precisely: `𝒟₀, 𝒟₁, 𝒟₄` and `𝒟₂, 𝒟₃` are geometric partitions of the closed first and second big
cells (in coordinates); there are maps `F_i`, continuous on `𝒟_i` and equal to `F` on the interior
of `𝒟_i`; and `τ ∘ F₃` maps `𝒟₃` onto `𝒟₄`, `τ ∘ F₄` maps `𝒟₄` onto `𝒟₃`, and `τ ∘ F_i` maps `𝒟_i`
onto itself for `i = 0, 1, 2` (as sets of `Ξ_{𝒲,0}/V_T`).

The book's proof sketch: discontinuities in the interior of a big cell lie on
`{res_AB = 0} ∪ {Δ_{A0} = 0} ∪ {Δ_{B1} = 0}` (`continuousAt_firstSwitchTime_of_ne_zero`); by Lemma
13.2.4 the involution maps them to the boundary faces (`discr_resAB_eq_zero_of_mem_bd`); on the
2-cells the only discontinuity is `Δ_{A0} = 0` on `𝒞₂(ζ², 0, 2)` (`firstSwitchTime_topFaceTwo`);
pulling back with `𝔦` gives all discontinuities. The topology (regular closed parts, their number,
`𝒟₀` a "very small bubble" attached to `∂_A`) is read off the figures.

Certification plan (layer 5b): the parts are semi-algebraic in `(r₂, cos ψ, sin ψ, cos θ₂, sin θ₂)`
after the substitution of the explicit Poincaré map; a cylindrical decomposition of the cells by
the signs of `Δ_{A,0}`, `Δ_{B,1}`, `res_AB` and of the switching polynomials at the candidate
roots, with interval enclosures of the root branches, decides the switch and the continuity on each
piece. **Not used by Theorem 16.1.1**, whose numerical hypotheses
(`SmoothedPolygons/Ch16/BasinHypotheses.lean`) avoid the curved parts. -/
def Proposition15_3_2 : Prop :=
  IsGeometricPartition closedBoxOne [partD0, partD1, partD4] ∧
    IsGeometricPartition closedBoxTwo [partD2, partD3] ∧
    ∃ G : Fin 5 → (Fin 3 → ℝ) → XiW0Quot,
      (∀ i, ContinuousOn (G i) (partD i) ∧
        ∀ p ∈ interior (partD i), G i p = poincareAngZero (cellClass p)) ∧
      (fun p ↦ tauZero (G 3 p)) '' partD 3 = cellClass '' partD 4 ∧
      (fun p ↦ tauZero (G 4 p)) '' partD 4 = cellClass '' partD 3 ∧
      ∀ i : Fin 5, i ≤ 2 → (fun p ↦ tauZero (G i p)) '' partD i = cellClass '' partD i

end TriFuller

end SmoothedPolygons
