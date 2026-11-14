module

public import SmoothedPolygons.Ch14.FixedPointManifolds
public import SmoothedPolygons.Ch16.MahlerFirst

/-!
# Chapter 16: switching points near the singular locus in blow-up coordinates (§16.4.1)

§16.4.1 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Coordinates", TeX 12852–12885): the
switching points of a Reinhardt extremal near the singular locus, in the hyperboloid coordinates
`(w, b, c)` rescaled to `z = (w/ρ, -ib/(2ρ), c/(6ρ))` (`fullerCoords`, `ρ = 2`, `d₁ = 3/2`,
`λ_cost = -1`, `ε = 1`), and in the weighted spherical coordinates `z_k = r^k ξ_k`, `φ(ξ) = 1`
(`weightedNorm`, `ang`, §13.4; "The set `{ξ ∈ ℂ³ | φ(ξ) = 1}` is a compact manifold. This is the
angular component in this context").

The vocabulary of Theorem 16.4.1 ("the sequence of switching points of a Pontryagin extremal
Reinhardt trajectory has a cluster point on the exceptional divisor of the blow-up, reached in
finite time, and … the switching points themselves are not on the exceptional divisor"):

* `phaseAt X Λ₁ Λ_R t = (X t, Λ₁ t, Λ_R t)`, the phase point at time `t`;
* `IsSwitchingSeqInto u a b τ`: `τ` enumerates increasingly all switching times in `(a, b)`, and
  `τ n → b`; `IsSwitchingSeqOutOf`: decreasingly, `τ n → a`;
* `IsChatteringArcInto a b … τ`: an extremal on `[a, b]` with `λ_cost = -1` whose lift meets the
  singular locus at `b` and only there, bang-bang with finitely many switches on each compact
  subinterval of `(a, b)`, with switching sequence `τ` (the configuration of Theorem 16.4.1, and of
  the last step of Theorem 16.3.1); `IsChatteringArcOutOf`, its time reversal;
* `switchAng`: the angular components `ξ_n = ang ẑ(q_n)` of the switching points `q_n`;
* `vtOrbit`, `TendstoModVT`: convergence modulo the diagonal action of `V_T` (the classes of the
  switching points in `Ξ/V_T`);
* `switchClusterSet`: the classes in `Ξ_{𝒲,0}/V_T` of the cluster points of `ξ_n` (the cluster
  points on the exceptional divisor).

Results: the existence of the switching sequence (`exists_isChatteringArcInto`, from Lemma 8.3.4:
finitely many switches cannot reach the singular locus); the switching points are phase points of
the blow-up off the singular point, with Fuller coordinates tending to `0`
(`IsChatteringArcInto.switchPoints`); the time reversal of chattering arcs
(`IsChatteringArcOutOf.reverse`, Remark 10.2.3 with `iso_vertexFlow_reinTau`); and convergence
modulo `V_T` from the cluster set (`tendstoModVT_of_forall_mapClusterPt`, compactness of `Ξ`).

## Proofs (plan)

`exists_isChatteringArcInto`: the switching times in `(a, b)` are locally finite in `(a, b)`
(`IsFiniteBangBang` on compact subintervals); if finitely many lay in some `(b - ε, b)`, the control
would be a.e. one vertex there (`l3m_local_vertex`-type argument, as in
`SmoothedPolygons/Ch16/MahlerFirst.lean`) and Lemma 8.3.4 (`lemma8_3_4`) would keep the lift off the
singular locus at `b`; for `a' ∈ (a, b)` the switching times in `(a', b)` are finitely many below
each `β < b`, so they can be enumerated increasingly (switches may accumulate at `a`, so `a' > a`
is needed). `switchPoints`: `det X = 1` and the star conditions give the sheet of `X`;
`det Λ₁` is a constant of motion (`Λ₁' = [Λ₁, X]`), equal to `det((3/2)λ_cost J) = 9/4` at `b`, and
the sheet of `Λ₁` is constant by continuity (the two sheets of `{det = 9/4}` are disjoint closed
sets); `fullerCoords` is continuous with value `0` at the singular point
(`fullerCoords_eq_zero_iff`). `reverse`: the state–costate system is reversible (the computation of
`iso_vertexFlow_reinTau`, for measurable controls in the integral form, with `g ↦ D g D`). Size:
500–900 lines.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology MeasureTheory
open TriFuller

/-- The phase point `(X(t), Λ₁(t), Λ_R(t))` of a lifted trajectory at time `t`. -/
def phaseAt (X Λ₁ ΛR : ℝ → Mat2) (t : ℝ) : iso_PhasePt := (X t, Λ₁ t, ΛR t)

/-- `τ` enumerates increasingly all the switching times of `u` in `(a, b)`, and `τ n → b`. -/
def IsSwitchingSeqInto (u : ℝ → Fin 3 → ℝ) (a b : ℝ) (τ : ℕ → ℝ) : Prop :=
  StrictMono τ ∧ (∀ n, τ n ∈ Ioo a b) ∧ Tendsto τ atTop (𝓝 b) ∧
    ∀ t ∈ Ioo a b, IsSwitchingTime u t ↔ ∃ n, τ n = t

/-- `τ` enumerates decreasingly all the switching times of `u` in `(a, b)`, and `τ n → a`. -/
def IsSwitchingSeqOutOf (u : ℝ → Fin 3 → ℝ) (a b : ℝ) (τ : ℕ → ℝ) : Prop :=
  StrictAnti τ ∧ (∀ n, τ n ∈ Ioo a b) ∧ Tendsto τ atTop (𝓝 a) ∧
    ∀ t ∈ Ioo a b, IsSwitchingTime u t ↔ ∃ n, τ n = t

/-- **A chattering arc into the singular locus** (the configuration of Theorem 16.4.1,
TeX 12840–12846, normalized by `λ_cost = -1`): an extremal lifted trajectory on `[a, b]`
(`IsExtremalOn`) whose lift meets the singular locus at `b` ("a cluster point on the exceptional
divisor … reached in finite time") and nowhere on `[a, b)` ("the switching points themselves are
not on the exceptional divisor"), bang-bang with finitely many switches on every compact
subinterval of `(a, b)`, with switching times `τ n ↑ b`. -/
def IsChatteringArcInto (a b : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ) :
    Prop :=
  IsExtremalOn a b u g X Λ₁ ΛR (-1) ∧ (g b, Λ₁ b, X b, ΛR b) ∈ singularLocus ∧
    (∀ t ∈ Ico a b, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus) ∧
    (∀ α β, a < α → β < b → IsFiniteBangBang α β u) ∧ IsSwitchingSeqInto u a b τ

/-- **A chattering arc out of the singular locus**: the time reversal of `IsChatteringArcInto`, an
extremal on `[a, b]` (`λ_cost = -1`) whose lift meets the singular locus at `a` and nowhere on
`(a, b]`, locally finitely bang-bang on `(a, b)`, with switching times `τ n ↓ a`. -/
def IsChatteringArcOutOf (a b : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ) :
    Prop :=
  IsExtremalOn a b u g X Λ₁ ΛR (-1) ∧ (g a, Λ₁ a, X a, ΛR a) ∈ singularLocus ∧
    (∀ t ∈ Ioc a b, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus) ∧
    (∀ α β, a < α → β < b → IsFiniteBangBang α β u) ∧ IsSwitchingSeqOutOf u a b τ

/-- The angular components `ξ_n = ang ẑ(q_n)` of the switching points `q_n = (X, Λ₁, Λ_R)(τ_n)`
(TeX 12868–12872: `z_k = r^k ξ_k`, `φ(ξ) = 1`). -/
noncomputable def switchAng (X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ) (n : ℕ) : Fin 3 → ℂ :=
  ang (fullerCoords (phaseAt X Λ₁ ΛR (τ n)))

/-- The orbit `{ξ, ζ ξ, ζ² ξ}` of `ξ` under the diagonal action of `V_T`. -/
def vtOrbit (ξ : Fin 3 → ℂ) : Set (Fin 3 → ℂ) := {η | ∃ v ∈ VT, η = v • ξ}

/-- `ξ_n → ξ` modulo `V_T`: the distance from `ξ_n` to the orbit of `ξ` tends to `0` (convergence
of the classes in `Ξ/V_T`). -/
def TendstoModVT (ξs : ℕ → Fin 3 → ℂ) (ξ : Fin 3 → ℂ) : Prop :=
  Tendsto (fun n ↦ Metric.infDist (ξs n) (vtOrbit ξ)) atTop (𝓝 0)

/-- The cluster classes of a sequence `ξ_n`: the classes in `Ξ_{𝒲,0}/V_T` of its cluster points that
lie in the Fuller section (`sectionZero`: on the walls, with `H_F⁺ = 0`). For the switching points,
every cluster point is of this kind (`mapClusterPt_switchAng_mem_sectionZero`). -/
def switchClusterSet (ξs : ℕ → Fin 3 → ℂ) : Set XiW0Quot :=
  {x | ∃ ξ ∈ sectionZero, classOf ξ = x ∧ MapClusterPt ξ atTop ξs}

/-- **The switching sequence exists** (TeX 12820–12825, 12997–13000): an extremal on `[a, b]`
(`λ_cost = -1`) whose lift meets the singular locus at `b` and nowhere on `(a, b)`, locally finitely
bang-bang on `(a, b)`, is a chattering arc into `b` on `[a', b]` for **every** `a' ∈ (a, b)`: its
switching times accumulate at `b` ("A trajectory cannot reach the singular locus with finitely many
switches by Lemma 8.3.4", TeX 12815–12816), and those in `(a', b)` (finitely many in each
`(a', β]`, `β < b`) form an increasing sequence tending to `b`. (The lift may meet the singular
locus at `a`, as in the assembly of Theorem 16.3.1, where `a` is the last meeting before the
chattering time.) -/
theorem exists_isChatteringArcInto {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (hext : IsExtremalOn a b u g X Λ₁ ΛR (-1)) (hb : (g b, Λ₁ b, X b, ΛR b) ∈ singularLocus)
    (hoff : ∀ t ∈ Ioo a b, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus)
    (hbb : ∀ α β, a < α → β < b → IsFiniteBangBang α β u) :
    ∀ a' ∈ Ioo a b, ∃ τ : ℕ → ℝ, IsChatteringArcInto a' b u g X Λ₁ ΛR τ := by
  sorry

/-- **The switching points in Fuller coordinates** (TeX 12856–12872): along a chattering arc into
`b`, every phase point on `[a, b]` is a phase point of the blow-up (`det X = 1`, `det Λ₁ = 9/4`,
`⟨X, Λ_R⟩ = 0`, on the sheets of the singular locus); the lift at `b` is the singular point
`(J, -(3/2) J, 0)`; the switching points have nonzero Fuller coordinates tending to `0`, and their
angular components lie on the compact weighted sphere `Ξ`. -/
theorem IsChatteringArcInto.switchPoints {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) :
    (∀ t ∈ Icc a b, IsBlowupPhasePt (phaseAt X Λ₁ ΛR t)) ∧
      phaseAt X Λ₁ ΛR b = singularPhasePt ∧
      (∀ n, fullerCoords (phaseAt X Λ₁ ΛR (τ n)) ≠ 0) ∧
      Tendsto (fun n ↦ fullerCoords (phaseAt X Λ₁ ΛR (τ n))) atTop (𝓝 0) ∧
      ∀ n, switchAng X Λ₁ ΛR τ n ∈ Xi := by
  sorry

/-- The reversed control `t ↦ u(a + b - t)` with the vertices relabelled by the time reversal
(`e₂ ↔ e₃`): `Z_{u'} = -D Z_u D`. -/
def reverseControl (a b : ℝ) (u : ℝ → Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  fun j ↦ u (a + b - t) (vertexSwap j)

/-- **Time reversal of chattering arcs** (Remark 10.2.3 for triangular control; "by time reversal",
TeX 11898, 12000–12013): the time reversal `t ↦ a + b - t` of a chattering arc out of `a`, with the
phase points reversed by `M ↦ -D M D` (`matTau`), `g ↦ D g D` and the controls relabelled
(`reverseControl`), is a chattering arc into `b` with the switching times `a + b - τ n`. -/
theorem IsChatteringArcOutOf.reverse {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcOutOf a b u g X Λ₁ ΛR τ) :
    IsChatteringArcInto a b (reverseControl a b u) (fun t ↦ diagD * g (a + b - t) * diagD)
      (fun t ↦ matTau (X (a + b - t))) (fun t ↦ matTau (Λ₁ (a + b - t)))
      (fun t ↦ matTau (ΛR (a + b - t))) (fun n ↦ a + b - τ n) := by
  sorry

/-- **Convergence modulo `V_T` from the cluster points** (compactness of `Ξ`; the step "the set
of cluster points … `q_in` is the only cluster point" of TeX 13006–13014): if `ξ_n ∈ Ξ` and every
cluster point of `ξ_n` lies in the Fuller section with class `q_in`, then `ξ_n → ang(τ q_out)`
(the representative of `q_in`) modulo `V_T`. -/
theorem tendstoModVT_of_forall_mapClusterPt {ξs : ℕ → Fin 3 → ℂ} (hΞ : ∀ n, ξs n ∈ Xi)
    (hcl : ∀ ξ, MapClusterPt ξ atTop ξs → ξ ∈ sectionZero ∧ classOf ξ = qIn0) :
    TendstoModVT ξs (ang (tau qOutCart)) := by
  sorry

end SmoothedPolygons
