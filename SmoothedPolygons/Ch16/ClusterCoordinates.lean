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

## Proofs

`exists_isChatteringArcInto`: the switching times in `(a, b)` are locally finite in `(a, b)`: a
switching time lies in the exceptional set of `IsFiniteBangBang` on any compact subinterval around
it (`l6e_not_isSwitchingTime`), so those in `(a', β]`, `β < b`, are finitely many
(`l6e_finite_switch`; switches may accumulate at `a`, so `a' > a` is needed). Every `(c, b)`
contains one (`l6e_exists_switch`): otherwise the control would be a.e. one vertex there (the
argument of `l3m_local_vertex` of `SmoothedPolygons/Ch16/MahlerFirst.lean`, private there and
repeated as `l6e_local_vertex`, with `exists_ae_eq_vertex_of_locally`) and Lemma 8.3.4
(`lemma8_3_4`) would keep the lift off the singular locus at `b`. The switching times in `(a', b)`
are then enumerated increasingly, each term the least switching time after the previous one
(`l6e_enum`).

`switchPoints`: the star conditions give `X₁₂ < 0 < X₂₁` (`l6e_star_sheet`); `det Λ₁` is a
constant of motion (`l6e_det_Λ₁_const`: the derivative `tr(adj(Λ₁)[Λ₁, X])` of `det Λ₁` vanishes),
equal to `det(-(3/2) J) = 9/4` at `b`; the sheet `(Λ₁)₂₁ < (Λ₁)₁₂` holds at `b` and the difference
`(Λ₁)₁₂ - (Λ₁)₂₁` never vanishes on `{det = 9/4, tr = 0}`, so it holds on `[a, b]` (intermediate
value theorem). The singular point has Fuller coordinates `0`, and only it
(`fullerCoords_eq_zero_iff`), and `fullerCoords` is continuous
(`continuous_fullerCoords_phaseOfFuller`).

`reverse`: the state–costate system is reversible (`l6e_isStateCostateSolution_reverse`, the
computation behind `iso_vertexFlow_reinTau`, done for measurable controls in the integral form):
with `s = T - t`, `g ↦ DgD` and `M ↦ -DMD` on `X, Λ₁, Λ_R`, every equation transforms by
`(-DAD)(-DBD) = -(-D(AB)D)`, `⟨-DAD, -DBD⟩ = ⟨A, B⟩`, `-DJD = J` and `-D Z_u D = Z_{u ∘ τ}`
(`e₂ ↔ e₃`); the Hamiltonian is unchanged, the integral equations reverse by the substitution
`σ ↦ T - σ` (`l6e_isIntegralCurve_reverse`) and the almost-everywhere conditions by the
measure-preserving reflection. The switching times, finite bang-bang control and the singular
locus are reflected likewise.

`tendstoModVT_of_forall_mapClusterPt`: every cluster point lies in the orbit of `ang (τ q_out)`
(`mk_eq_mk_iff_exists_mem_VT`); a subsequence staying away from the orbit would have a cluster
point (compactness of `Ξ`, `l6e_isCompact_Xi`) at positive distance from it.
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

/-! ### Helpers: switching times of locally finite bang-bang controls -/

/-- The vertices of `U_T` are distinct. -/
private lemma l6e_vertex_inj {i j : Fin 3} (h : vertex i = vertex j) : i = j := by
  by_contra hij
  have := congrFun h i
  simp [vertex, hij] at this

/-- A property holding almost everywhere on a nonempty open interval holds at some point of it. -/
private lemma l6e_exists_mem_of_ae {P : ℝ → Prop} {c d : ℝ} (hcd : c < d)
    (h : ∀ᵐ t, t ∈ Ioo c d → P t) : ∃ t ∈ Ioo c d, P t := by
  by_contra hcon
  push Not at hcon
  have h0 : volume (Ioo c d) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with t ht hmem
    exact hcon t hmem (ht hmem)
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  linarith

/-- A time near which the control is almost everywhere one vertex is not a switching time. -/
private lemma l6e_not_isSwitchingTime {u : ℝ → Fin 3 → ℝ} {t ε : ℝ} {i : Fin 3} (hε : 0 < ε)
    (h : ∀ᵐ τ, τ ∈ Ioo (t - ε) (t + ε) → u τ = vertex i) : ¬ IsSwitchingTime u t := by
  rintro ⟨i₁, j₁, hij, ε₁, hε₁, h1, h2⟩
  have hm1 := min_le_left ε ε₁
  have hm2 := min_le_right ε ε₁
  have hδ : 0 < min ε ε₁ := lt_min hε hε₁
  obtain ⟨s, -, hs1, hs2⟩ := l6e_exists_mem_of_ae
    (P := fun s ↦ u s = vertex i ∧ u s = vertex i₁) (by linarith : t - min ε ε₁ < t) (by
      filter_upwards [h, h1] with s hs hs1 hsI
      exact ⟨hs ⟨by linarith [hsI.1], by linarith [hsI.2]⟩,
        hs1 ⟨by linarith [hsI.1], hsI.2⟩⟩)
  obtain ⟨s', -, hs'1, hs'2⟩ := l6e_exists_mem_of_ae
    (P := fun s ↦ u s = vertex i ∧ u s = vertex j₁) (by linarith : t < t + min ε ε₁) (by
      filter_upwards [h, h2] with s hs hs2 hsI
      exact ⟨hs ⟨by linarith [hsI.1], by linarith [hsI.2]⟩,
        hs2 ⟨hsI.1, by linarith [hsI.2]⟩⟩)
  exact hij ((l6e_vertex_inj (hs1.symm.trans hs2)).symm.trans
    (l6e_vertex_inj (hs'1.symm.trans hs'2)))

/-- **A time inside an interval of finite bang-bang control that is not a switching time has a
neighbourhood on which the control is one vertex** (the argument of `l3m_local_vertex` of
`SmoothedPolygons/Ch16/MahlerFirst.lean`, which is private there). -/
private lemma l6e_local_vertex {u : ℝ → Fin 3 → ℝ} {α β t : ℝ} (hbb : IsFiniteBangBang α β u)
    (ht : t ∈ Ioo α β) (hsw : ¬ IsSwitchingTime u t) :
    ∃ i : Fin 3, ∃ η > 0, ∀ᵐ τ, τ ∈ Ioo (t - η) (t + η) → u τ = vertex i := by
  obtain ⟨S, hS⟩ := hbb
  have hfin : ((S.erase t : Finset ℝ) : Set ℝ)ᶜ ∈ 𝓝 t :=
    (S.erase t).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.mem_nhds_iff.1 hfin
  set ρ := min ρ₀ (min (t - α) (β - t)) with hρ
  have hρ1 : ρ ≤ ρ₀ := min_le_left _ _
  have hρ2 : ρ ≤ t - α := (min_le_right _ _).trans (min_le_left _ _)
  have hρ3 : ρ ≤ β - t := (min_le_right _ _).trans (min_le_right _ _)
  have hρpos : 0 < ρ := lt_min hρ₀ (lt_min (by linarith [ht.1]) (by linarith [ht.2]))
  have hloc : ∀ s ∈ Ioo (t - ρ) (t + ρ), s ≠ t →
      ∃ i : Fin 3, ∃ η > 0, ∀ᵐ τ, τ ∈ Ioo (s - η) (s + η) → u τ = vertex i := by
    intro s hs hst
    refine hS s ⟨by linarith [hs.1], by linarith [hs.2]⟩ fun hsS ↦ ?_
    have hsb : s ∈ Metric.ball t ρ₀ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    exact hball hsb (by simp [hsS, hst])
  obtain ⟨i, hi⟩ := exists_ae_eq_vertex_of_locally (α := t - ρ) (β := t) fun s hs ↦
    hloc s ⟨hs.1, by linarith [hs.2]⟩ hs.2.ne
  obtain ⟨j, hj⟩ := exists_ae_eq_vertex_of_locally (α := t) (β := t + ρ) fun s hs ↦
    hloc s ⟨by linarith [hs.1], hs.2⟩ hs.1.ne'
  obtain rfl : i = j := by
    by_contra hij
    exact hsw ⟨i, j, hij, ρ, hρpos, hi, hj⟩
  refine ⟨i, ρ, hρpos, ?_⟩
  have hne : ∀ᵐ τ : ℝ, τ ≠ t := by
    rw [ae_iff]
    simp
  filter_upwards [hi, hj, hne] with τ h1 h2 h3 hτ
  rcases lt_or_gt_of_ne h3 with h | h
  · exact h1 ⟨hτ.1, h⟩
  · exact h2 ⟨h, hτ.2⟩

/-- **Switching times accumulate at a meeting with the singular locus** ("A trajectory cannot
reach the singular locus with finitely many switches by Lemma 8.3.4", TeX 12815–12816): if the
control is finitely bang-bang on compact subintervals of `(a, b)` and the lift meets `𝒮_sing` at
`b`, every `(c, b)` with `c ∈ (a, b)` contains a switching time. Otherwise the control would be
a.e. one vertex on `(c, b)` (`l6e_local_vertex`, `exists_ae_eq_vertex_of_locally`), and
Lemma 8.3.4 (`lemma8_3_4`) on `[c, b]` keeps the lift off `𝒮_sing` at `b`. -/
private lemma l6e_exists_switch {a b lam : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (hext : IsExtremalOn a b u g X Λ₁ ΛR lam) (hb : (g b, Λ₁ b, X b, ΛR b) ∈ singularLocus)
    (hbb : ∀ α β, a < α → β < b → IsFiniteBangBang α β u) {c : ℝ} (hc : c ∈ Ioo a b) :
    ∃ s ∈ Ioo c b, IsSwitchingTime u s := by
  by_contra hcon
  push Not at hcon
  have hloc : ∀ t ∈ Ioo c b,
      ∃ i : Fin 3, ∃ η > 0, ∀ᵐ τ, τ ∈ Ioo (t - η) (t + η) → u τ = vertex i := fun t ht ↦
    l6e_local_vertex (hbb ((c + t) / 2) ((t + b) / 2) (by linarith [hc.1, ht.1])
      (by linarith [ht.2])) ⟨by linarith [ht.1], by linarith [ht.2]⟩ (hcon t ht)
  obtain ⟨i, hi⟩ := exists_ae_eq_vertex_of_locally hloc
  exact lemma8_3_4 (hext.mono hc.1.le hc.2 le_rfl) hi b ⟨hc.2.le, le_rfl⟩ hb

/-- The switching times in `(a', b)` up to `β < b` are finitely many: they lie in the exceptional
set of the finite bang-bang control on `((a + a')/2, (β + b)/2)` (`l6e_not_isSwitchingTime`). -/
private lemma l6e_finite_switch {a a' b β : ℝ} {u : ℝ → Fin 3 → ℝ} (ha' : a < a') (hβ : β < b)
    (hbb : ∀ α β, a < α → β < b → IsFiniteBangBang α β u) :
    {t | t ∈ Ioo a' b ∧ IsSwitchingTime u t ∧ t ≤ β}.Finite := by
  obtain ⟨S, hS⟩ := hbb ((a + a') / 2) ((β + b) / 2) (by linarith) (by linarith)
  refine S.finite_toSet.subset fun t ht ↦ ?_
  obtain ⟨htI, hsw, htβ⟩ := ht
  by_contra hns
  obtain ⟨i, ε, hε, hi⟩ := hS t ⟨by linarith [htI.1], by linarith⟩ fun h ↦ hns h
  exact l6e_not_isSwitchingTime hε hi hsw

/-- **Increasing enumeration of a set accumulating only at `b`**: a set `S ⊆ (x₀, b)` with
finitely many points below each `β < b` and points arbitrarily close to `b` is the range of a
strictly increasing sequence tending to `b` (each term is the least point of `S` after the
previous one). -/
private lemma l6e_enum {S : Set ℝ} {x₀ b : ℝ} (hS : S ⊆ Ioo x₀ b)
    (hfin : ∀ β < b, (S ∩ Iic β).Finite) (hacc : ∀ c < b, ∃ s ∈ S, c < s) :
    ∃ τ : ℕ → ℝ, StrictMono τ ∧ (∀ n, τ n ∈ S) ∧ Tendsto τ atTop (𝓝 b) ∧
      ∀ t ∈ S, ∃ n, τ n = t := by
  -- the least point of `S` after `x`
  have hleast : ∀ x, x < b → ∃ m, IsLeast (S ∩ Ioi x) m := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := hacc x hx
    have hF : (S ∩ Ioi x ∩ Iic s).Finite :=
      (hfin s (hS hs).2).subset fun y hy ↦ ⟨hy.1.1, hy.2⟩
    obtain ⟨m, hm, hmin⟩ := Set.exists_min_image _ id hF ⟨s, ⟨hs, hxs⟩, le_rfl⟩
    refine ⟨m, hm.1, fun y hy ↦ ?_⟩
    rcases le_or_gt y s with hys | hys
    · exact hmin y ⟨hy, hys⟩
    · exact hm.2.trans hys.le
  choose! nxt hnxt using hleast
  have hx₀ : x₀ < b := by
    obtain ⟨s, hs, -⟩ := hacc (b - 1) (by linarith)
    exact (hS hs).1.trans (hS hs).2
  let τ : ℕ → ℝ := fun n ↦ Nat.rec (nxt x₀) (fun _ y ↦ nxt y) n
  have hτ0 : τ 0 = nxt x₀ := rfl
  have hτs : ∀ n, τ (n + 1) = nxt (τ n) := fun n ↦ rfl
  have hmem : ∀ n, τ n ∈ S := by
    intro n
    induction n with
    | zero => exact (hnxt x₀ hx₀).1.1
    | succ n ih => rw [hτs]; exact (hnxt (τ n) (hS ih).2).1.1
  have hlt : ∀ n, τ n < τ (n + 1) := fun n ↦ by
    rw [hτs]; exact (hnxt (τ n) (hS (hmem n)).2).1.2
  have hmono : StrictMono τ := strictMono_nat_of_lt_succ hlt
  have hfinpre : ∀ c < b, {n | τ n ≤ c}.Finite := fun c hc ↦
    ((hfin c hc).preimage hmono.injective.injOn).subset fun n hn ↦ ⟨hmem n, hn⟩
  have hlim : Tendsto τ atTop (𝓝 b) := by
    refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦
      Eventually.of_forall fun n ↦ (hS (hmem n)).2.trans hc⟩
    rw [← Nat.cofinite_eq_atTop]
    exact Filter.eventually_cofinite.2 ((hfinpre c hc).subset fun n hn ↦ not_lt.1 hn)
  refine ⟨τ, hmono, hmem, hlim, fun t ht ↦ ?_⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n, t < τ n := (hlim.eventually (lt_mem_nhds (hS ht).2)).exists
  by_contra hcon
  push Not at hcon
  -- if `t` is never hit, every term stays below `t`
  have hbelow : ∀ n, τ n < t := by
    intro n
    induction n with
    | zero => exact lt_of_le_of_ne ((hnxt x₀ hx₀).2 ⟨ht, (hS ht).1⟩) (hcon 0)
    | succ n ih =>
      refine lt_of_le_of_ne ?_ (hcon (n + 1))
      rw [hτs]
      exact (hnxt (τ n) (hS (hmem n)).2).2 ⟨ht, ih⟩
  exact absurd hn₀ (not_lt.2 (hbelow n₀).le)

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
  intro a' ha'
  obtain ⟨τ, hmono, hτS, hlim, hhit⟩ := l6e_enum (S := {t | t ∈ Ioo a' b ∧ IsSwitchingTime u t})
    (x₀ := a') (b := b) (fun t ht ↦ ht.1)
    (fun β hβ ↦ (l6e_finite_switch ha'.1 hβ hbb).subset fun t ht ↦ ⟨ht.1.1, ht.1.2, ht.2⟩)
    (fun c hc ↦ by
      obtain ⟨s, hs, hsw⟩ := l6e_exists_switch hext hb hbb (c := max c a')
        ⟨lt_max_of_lt_right ha'.1, max_lt hc ha'.2⟩
      exact ⟨s, ⟨⟨(le_max_right c a').trans_lt hs.1, hs.2⟩, hsw⟩,
        (le_max_left c a').trans_lt hs.1⟩)
  refine ⟨τ, hext.mono ha'.1.le ha'.2 le_rfl, hb, fun t ht ↦ hoff t ⟨ha'.1.trans_le ht.1, ht.2⟩,
    fun α β hα hβ ↦ hbb α β (ha'.1.trans hα) hβ, hmono, fun n ↦ (hτS n).1, hlim,
    fun t ht ↦ ⟨fun hsw ↦ hhit t ⟨ht, hsw⟩, ?_⟩⟩
  rintro ⟨n, rfl⟩
  exact (hτS n).2

/-! ### Helpers: the phase points of an extremal with `λ_cost = -1` -/

/-- A star state has `X₁₂ < 0 < X₂₁` (the sum of `ρ₀, ρ₁ > 0` gives `X₂₁ > 0`, and `ρ₂ > 0` gives
`3 X₁₂ + X₂₁ < 0`). -/
private lemma l6e_star_sheet {X : Mat2} (h : IsStarState X) : X 0 1 < X 1 0 := by
  obtain ⟨-, -, h0, h1, h2⟩ := h
  have hs3 : 0 < √3 := by positivity
  simp only [ρ₀, ρ₁, ρ₂] at h0 h1 h2
  have h0' := (div_pos_iff_of_pos_right hs3).1 h0
  have h1' := (div_pos_iff_of_pos_right hs3).1 h1
  have h2' := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * √3)).1 h2
  linarith

/-- **`det Λ₁` is a constant of motion** (`Λ₁' = [Λ₁, X]`): along an extremal on `[a, b]`,
`det Λ₁(t) = det Λ₁(a)`. The derivative of `det Λ₁` is `tr(adj(Λ₁) [Λ₁, X]) = 0`. -/
private lemma l6e_det_Λ₁_const {a b lam : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (hext : IsExtremalOn a b u g X Λ₁ ΛR lam) : ∀ t ∈ Icc a b, (Λ₁ t).det = (Λ₁ a).det := by
  have hXI := hext.1.2.2.2.2.2
  have hI1 := hext.2.2.2.1
  have hXc := Matrix.continuousOn_of_eq_add_integral hXI
  have h1c := Matrix.continuousOn_of_eq_add_integral hI1
  have hd : ∀ s ∈ Icc 0 (b - a),
      HasDerivWithinAt (fun s ↦ (Λ₁ (a + s)).det) 0 (Icc 0 (b - a)) s := by
    intro s hs
    have := (Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hI1 hs
      (((h1c.mul hXc).sub (hXc.mul h1c)) s hs)).det_fin_two
    convert this using 1
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hconst := constant_of_has_deriv_right_zero (fun s hs ↦ (hd s hs).continuousWithinAt)
    fun s hs ↦ (hd s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1))
  intro t ht
  have := hconst (t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp only [add_sub_cancel, add_zero] at this
  exact this

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
  obtain ⟨hext, hb, hoff, -, -, hτI, hlim, -⟩ := h
  have hab : a < b := by have := hext.1.1; linarith
  have hbI : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  obtain ⟨-, h1b, hXb, hRb⟩ := (hext.mem_singularLocus_iff hbI).1 hb
  -- the pointwise conditions of the extremal at `t ∈ [a, b]`
  have hpt : ∀ t ∈ Icc a b, IsStarState (X t) ∧ (Λ₁ t).trace = 0 ∧ (ΛR t).trace = 0 ∧
      traceForm (ΛR t) (X t) = 0 := by
    intro t ht
    have ht' : t - a ∈ Icc 0 (b - a) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have e : a + (t - a) = t := by ring
    have h1 := (hext.1.2.2.2.1 (t - a) ht').2
    have h2 := hext.2.2.1 (t - a) ht'
    simp only [e] at h1 h2
    exact ⟨h1, h2.1, h2.2.1, h2.2.2.1⟩
  -- `det Λ₁ = det((3/2) λ_cost J) = 9/4`, its value at `b`
  have hdet : ∀ t ∈ Icc a b, (Λ₁ t).det = 9 / 4 := by
    have hdb : (Λ₁ b).det = 9 / 4 := by
      rw [h1b, Matrix.det_fin_two]
      simp [J]
      norm_num
    intro t ht
    rw [l6e_det_Λ₁_const hext t ht, ← l6e_det_Λ₁_const hext b hbI, hdb]
  -- the sheet `(Λ₁)₂₁ < (Λ₁)₁₂` of `{det = 9/4}`, by continuity from `b`
  have hsheet : ∀ t ∈ Icc a b, Λ₁ t 1 0 < Λ₁ t 0 1 := by
    have hne : ∀ t ∈ Icc a b, Λ₁ t 0 1 - Λ₁ t 1 0 ≠ 0 := by
      intro t ht h0
      have hd := hdet t ht
      have htr := (hpt t ht).2.1
      rw [Matrix.det_fin_two] at hd
      rw [Matrix.trace_fin_two] at htr
      have e1 : Λ₁ t 0 1 = Λ₁ t 1 0 := by linarith
      have e2 : Λ₁ t 1 1 = -Λ₁ t 0 0 := by linarith
      rw [e1, e2] at hd
      nlinarith [sq_nonneg (Λ₁ t 0 0), sq_nonneg (Λ₁ t 1 0)]
    have hc : ContinuousOn (fun t ↦ Λ₁ t 0 1 - Λ₁ t 1 0) (Icc a b) := by
      have h1c : ContinuousOn Λ₁ (Icc a b) :=
        (continuous_fst.comp continuous_snd).comp_continuousOn hext.continuousOn_lift
      exact ((continuous_id.matrix_elem 0 1).comp_continuousOn h1c).sub
        ((continuous_id.matrix_elem 1 0).comp_continuousOn h1c)
    have hpos : 0 < Λ₁ b 0 1 - Λ₁ b 1 0 := by
      rw [h1b]
      norm_num [J]
    intro t ht
    by_contra hle
    push Not at hle
    obtain ⟨c, hc', hc0⟩ := intermediate_value_Icc ht.2 (hc.mono (Icc_subset_Icc_left ht.1))
      ⟨by linarith, hpos.le⟩
    exact hne c ⟨ht.1.trans hc'.1, hc'.2⟩ hc0
  have hblow : ∀ t ∈ Icc a b, IsBlowupPhasePt (phaseAt X Λ₁ ΛR t) := by
    intro t ht
    obtain ⟨hstar, h1, h2, h3⟩ := hpt t ht
    exact ⟨hstar.1, h1, h2, hstar.2.1, hdet t ht,
      by rw [traceForm, Matrix.trace_mul_comm]; exact h3, l6e_star_sheet hstar, hsheet t ht⟩
  have hsingb : phaseAt X Λ₁ ΛR b = singularPhasePt := by
    simp only [phaseAt, singularPhasePt, hXb, h1b, hRb]
    norm_num
  have hne : ∀ n, fullerCoords (phaseAt X Λ₁ ΛR (τ n)) ≠ 0 := by
    intro n h0
    have hmem : τ n ∈ Icc a b := ⟨(hτI n).1.le, (hτI n).2.le⟩
    have hq := (fullerCoords_eq_zero_iff (hblow _ hmem)).1 h0
    simp only [phaseAt, singularPhasePt, Prod.mk.injEq] at hq
    obtain ⟨hX, h1, hR⟩ := hq
    exact hoff (τ n) ⟨(hτI n).1.le, (hτI n).2⟩ ((hext.mem_singularLocus_iff hmem).2
      ⟨by norm_num, by rw [h1]; norm_num, hX, hR⟩)
  refine ⟨hblow, hsingb, hne, ?_, fun n ↦ ang_mem_Xi (hne n)⟩
  have hcont : ContinuousWithinAt (phaseAt X Λ₁ ΛR) (Icc a b) b := by
    have hm : Continuous fun p : Mat2 × Mat2 × Mat2 × Mat2 ↦ (p.2.2.1, p.2.1, p.2.2.2) := by
      fun_prop
    exact hm.continuousAt.comp_continuousWithinAt (hext.continuousOn_lift b hbI)
  have hτlim : Tendsto τ atTop (𝓝[Icc a b] b) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n ↦ ⟨(hτI n).1.le, (hτI n).2.le⟩⟩
  have h0 : fullerCoords (phaseAt X Λ₁ ΛR b) = 0 :=
    (fullerCoords_eq_zero_iff (hblow b hbI)).2 hsingb
  have := ((continuous_fullerCoords_phaseOfFuller.1.continuousAt.comp_continuousWithinAt
    hcont).tendsto).comp hτlim
  have h0' : (fullerCoords ∘ phaseAt X Λ₁ ΛR) b = 0 := h0
  rw [h0'] at this
  exact this

/-! ### Helpers: the time reversal `M ↦ -D M D` -/

private lemma l6e_matTau_apply (M : Mat2) (i j : Fin 2) :
    matTau M i j = (if i = j then -1 else 1) * M i j := by
  fin_cases i <;> fin_cases j <;> simp [matTau]

private lemma l6e_diagD_conj_apply (M : Mat2) (i j : Fin 2) :
    (diagD * M * diagD) i j = (if i = j then 1 else -1) * M i j := by
  fin_cases i <;> fin_cases j <;>
    simp [diagD, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private lemma l6e_matTau_add (A B : Mat2) : matTau (A + B) = matTau A + matTau B := by
  ext i j; simp only [l6e_matTau_apply, Matrix.add_apply]; ring

private lemma l6e_matTau_sub (A B : Mat2) : matTau (A - B) = matTau A - matTau B := by
  ext i j; simp only [l6e_matTau_apply, Matrix.sub_apply]; ring

private lemma l6e_matTau_neg (A : Mat2) : matTau (-A) = -matTau A := by
  ext i j; simp only [l6e_matTau_apply, Matrix.neg_apply]; ring

private lemma l6e_matTau_smul (c : ℝ) (A : Mat2) : matTau (c • A) = c • matTau A := by
  ext i j; simp only [l6e_matTau_apply, Matrix.smul_apply, smul_eq_mul]; ring

private lemma l6e_matTau_zero : matTau 0 = 0 := by
  ext i j; simp [l6e_matTau_apply]

private lemma l6e_matTau_J : matTau J = J := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matTau, J]

private lemma l6e_matTau_matTau (A : Mat2) : matTau (matTau A) = A := by
  ext i j; simp only [l6e_matTau_apply]; split_ifs <;> ring

/-- `(-DAD)(-DBD) = DABD = -(-DABD)`. -/
private lemma l6e_matTau_mul (A B : Mat2) : matTau A * matTau B = -matTau (A * B) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matTau, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

private lemma l6e_matTau_comm (A B : Mat2) :
    matTau A * matTau B - matTau B * matTau A = -matTau (A * B - B * A) := by
  rw [l6e_matTau_mul, l6e_matTau_mul, l6e_matTau_sub]; abel

private lemma l6e_traceForm_matTau (A B : Mat2) :
    traceForm (matTau A) (matTau B) = traceForm A B := by
  simp only [traceForm, Matrix.trace_fin_two, matTau, Matrix.mul_apply, Fin.sum_univ_two]
  simp

private lemma l6e_matTau_combo (A B C : Mat2) (c : ℝ) :
    -matTau A - c • -matTau B + -matTau C = -matTau (A - c • B + C) := by
  rw [l6e_matTau_add, l6e_matTau_sub, l6e_matTau_smul, smul_neg]
  abel

private lemma l6e_trace_matTau (A : Mat2) : (matTau A).trace = -A.trace := by
  simp only [Matrix.trace_fin_two, matTau]
  simp
  ring

private lemma l6e_det_diagD_conj (A : Mat2) : (diagD * A * diagD).det = A.det := by
  simp only [Matrix.det_fin_two, l6e_diagD_conj_apply]
  simp

private lemma l6e_vertexSwap_vertexSwap (j : Fin 3) : vertexSwap (vertexSwap j) = j := by
  fin_cases j <;> rfl

private lemma l6e_vertexSwap_inj {i j : Fin 3} (h : vertexSwap i = vertexSwap j) : i = j := by
  rw [← l6e_vertexSwap_vertexSwap i, h, l6e_vertexSwap_vertexSwap]

/-- `-D Z_u D = Z_{u ∘ τ}` (`e₂ ↔ e₃`). -/
private lemma l6e_controlMatrix_swap (v : Fin 3 → ℝ) :
    controlMatrix (fun j ↦ v (vertexSwap j)) = matTau (controlMatrix v) := by
  have h0 : vertexSwap 0 = 0 := rfl
  have h1 : vertexSwap 1 = 2 := rfl
  have h2 : vertexSwap 2 = 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;> simp [controlMatrix, matTau, h0, h1, h2] <;> ring

private lemma l6e_controlP_swap (v : Fin 3 → ℝ) (X : Mat2) :
    controlP (fun j ↦ v (vertexSwap j)) (matTau X) = matTau (controlP v X) := by
  rw [controlP, controlP, l6e_controlMatrix_swap, l6e_traceForm_matTau, l6e_matTau_smul]

private lemma l6e_hamiltonian_swap (lam : ℝ) (Λ₁ ΛR X : Mat2) (v : Fin 3 → ℝ) :
    hamiltonian lam (matTau Λ₁) (matTau ΛR) (matTau X) (fun j ↦ v (vertexSwap j)) =
      hamiltonian lam Λ₁ ΛR X v := by
  have e : matTau Λ₁ - (3 / 2 * lam) • J = matTau (Λ₁ - (3 / 2 * lam) • J) := by
    rw [l6e_matTau_sub, l6e_matTau_smul, l6e_matTau_J]
  rw [hamiltonian, hamiltonian, l6e_controlMatrix_swap, e, l6e_traceForm_matTau,
    l6e_traceForm_matTau, l6e_traceForm_matTau]

private lemma l6e_swap_mem_controlSimplex {v : Fin 3 → ℝ} (h : v ∈ controlSimplex) :
    (fun j ↦ v (vertexSwap j)) ∈ controlSimplex := by
  obtain ⟨hb, hs⟩ := h
  refine ⟨fun i ↦ hb (vertexSwap i), ?_⟩
  have h0 : vertexSwap 0 = 0 := rfl
  have h1 : vertexSwap 1 = 2 := rfl
  have h2 : vertexSwap 2 = 1 := rfl
  simp only [h0, h1, h2]
  linarith

private lemma l6e_isStarState_matTau {X : Mat2} (h : IsStarState X) : IsStarState (matTau X) := by
  obtain ⟨htr, hdet, h0, h1, h2⟩ := h
  refine ⟨by rw [l6e_trace_matTau, htr, neg_zero], ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two] at hdet ⊢
    simp only [matTau]
    simp
    linarith
  · have e : ρ₀ (matTau X) = ρ₁ X := by
      simp only [ρ₀, ρ₁, matTau]
      simp
      ring
    rw [e]; exact h1
  · have e : ρ₁ (matTau X) = ρ₀ X := by
      simp only [ρ₀, ρ₁, matTau]
      simp
    rw [e]; exact h0
  · have e : ρ₂ (matTau X) = ρ₂ X := by
      simp only [ρ₂, matTau]
      simp
    rw [e]; exact h2

/-- `u = e_i ⇒ u ∘ τ = e_{τ i}`. -/
private lemma l6e_vertex_swap (i : Fin 3) :
    (fun j ↦ vertex i (vertexSwap j)) = vertex (vertexSwap i) := by
  funext j
  have h0 : vertexSwap 0 = 0 := rfl
  have h1 : vertexSwap 1 = 2 := rfl
  have h2 : vertexSwap 2 = 1 := rfl
  fin_cases i <;> fin_cases j <;> simp [vertex, h0, h1, h2]

/-- **Time reversal of a Carathéodory solution**: if `F' = V` on `[0, T]`, then
`G(t) = k F(T - t)` (entrywise, constant factors `k`) solves `G' = W` with `W(t) = -k V(T - t)`
(substitution `s = T - t` in the integral). -/
private lemma l6e_isIntegralCurve_reverse {F V G W : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (k : Fin 2 → Fin 2 → ℝ) (h : IsIntegralCurve F V T)
    (hG : ∀ t i j, G t i j = k i j * F (T - t) i j)
    (hW : ∀ t i j, W t i j = -(k i j * V (T - t) i j)) : IsIntegralCurve G W T := by
  intro i j
  obtain ⟨hint, heq⟩ := h i j
  have hWij : (fun s ↦ W s i j) = fun s ↦ -(k i j * V (T - s) i j) := funext fun s ↦ hW s i j
  have hint' : IntervalIntegrable (fun s ↦ V (T - s) i j) volume 0 T := by
    have := hint.comp_sub_left T
    simp only [sub_zero, sub_self] at this
    exact this.symm
  refine ⟨by rw [hWij]; exact (hint'.const_mul (k i j)).neg, fun t ht ↦ ?_⟩
  have hsub : ∀ {c d : ℝ}, 0 ≤ c → c ≤ d → d ≤ T →
      IntervalIntegrable (fun σ ↦ V σ i j) volume c d := fun hc hcd hd ↦
    hint.mono_set (by rw [uIcc_of_le hcd, uIcc_of_le hT]; exact Icc_subset_Icc hc hd)
  rw [hG, hG, hWij, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun s ↦ V s i j), heq (T - t)
      ⟨by linarith [ht.2], by linarith [ht.1]⟩, sub_zero, heq T ⟨hT, le_rfl⟩,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hsub (c := 0) (d := T - t) le_rfl (by linarith [ht.2]) (by linarith [ht.1]))
      (hsub (c := T - t) (d := T) (by linarith [ht.2]) (by linarith [ht.1]) le_rfl)]
  ring

/-- The reversal of a `τ`-type variable (`X`, `Λ₁`, `Λ_R`): `M(t) = -D F(T - t) D`. -/
private lemma l6e_isIntegralCurve_matTau {F V W : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (h : IsIntegralCurve F V T) (hW : ∀ t, W t = -matTau (V (T - t))) :
    IsIntegralCurve (fun t ↦ matTau (F (T - t))) W T :=
  l6e_isIntegralCurve_reverse hT (fun i j ↦ if i = j then -1 else 1) h
    (fun t i j ↦ l6e_matTau_apply _ i j) fun t i j ↦ by
      rw [hW, Matrix.neg_apply, l6e_matTau_apply]

/-- The reversal of the state `g`: `g(t) = D g(T - t) D`. -/
private lemma l6e_isIntegralCurve_diagD {F V W : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (h : IsIntegralCurve F V T) (hW : ∀ t, W t = -(diagD * V (T - t) * diagD)) :
    IsIntegralCurve (fun t ↦ diagD * F (T - t) * diagD) W T :=
  l6e_isIntegralCurve_reverse hT (fun i j ↦ if i = j then 1 else -1) h
    (fun t i j ↦ l6e_diagD_conj_apply _ i j) fun t i j ↦ by
      rw [hW, Matrix.neg_apply, l6e_diagD_conj_apply]

/-- **The state–costate system is reversible** (Remark 10.2.3; the computation of
`iso_vertexFlow_reinTau` for measurable controls in the integral form): a solution on `[0, T]`,
reversed in time by `t ↦ T - t`, with `g ↦ D g D`, `M ↦ -D M D` on `X, Λ₁, Λ_R` and the controls
relabelled `e₂ ↔ e₃`, is a solution on `[0, T]` with the same `λ_cost`. The equations transform
by `-DAD · -DBD = -(-DABD)`, `⟨-DAD, -DBD⟩ = ⟨A, B⟩`, `-DJD = J` and `-D Z_u D = Z_{u ∘ τ}`; the
Hamiltonian is unchanged, and the relabelling permutes `U_T`. -/
private lemma l6e_isStateCostateSolution_reverse {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsStateCostateSolution T u g X Λ₁ ΛR lam) :
    IsStateCostateSolution T (fun t j ↦ u (T - t) (vertexSwap j))
      (fun t ↦ diagD * g (T - t) * diagD) (fun t ↦ matTau (X (T - t)))
      (fun t ↦ matTau (Λ₁ (T - t))) (fun t ↦ matTau (ΛR (T - t))) lam := by
  obtain ⟨⟨hT, hum, huU, hst, hgI, hXI⟩, hlam, hpt, hI1, hIR, hmax⟩ := h
  have hmem : ∀ t ∈ Icc 0 T, T - t ∈ Icc 0 T := fun t ht ↦
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hinj : ∀ M : Mat2, matTau M = 0 → M = 0 := fun M h0 ↦ by
    rw [← l6e_matTau_matTau M, h0, l6e_matTau_zero]
  refine ⟨⟨hT, ?_, fun t ht ↦ l6e_swap_mem_controlSimplex (huU _ (hmem t ht)), fun t ht ↦ ?_,
    ?_, ?_⟩, hlam, fun t ht ↦ ?_, ?_, ?_, ?_⟩
  · exact measurable_pi_iff.2 fun j ↦
      (measurable_pi_apply (vertexSwap j)).comp (hum.comp (measurable_const.sub measurable_id))
  · obtain ⟨hdet, hstar⟩ := hst _ (hmem t ht)
    exact ⟨by rw [l6e_det_diagD_conj, hdet], l6e_isStarState_matTau hstar⟩
  · refine l6e_isIntegralCurve_diagD hT.le hgI fun t ↦ ?_
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matTau, diagD, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring
  · refine l6e_isIntegralCurve_matTau hT.le hXI fun t ↦ ?_
    simp only [l6e_controlP_swap, l6e_matTau_comm]
  · obtain ⟨h1, h2, h3, h4⟩ := hpt _ (hmem t ht)
    refine ⟨by rw [l6e_trace_matTau, h1, neg_zero], by rw [l6e_trace_matTau, h2, neg_zero],
      by rw [l6e_traceForm_matTau, h3], ?_⟩
    rcases h4 with h4 | h4 | h4
    · exact Or.inl h4
    · exact Or.inr (Or.inl fun h0 ↦ h4 (hinj _ h0))
    · exact Or.inr (Or.inr fun h0 ↦ h4 (hinj _ h0))
  · exact l6e_isIntegralCurve_matTau hT.le hI1 fun t ↦ l6e_matTau_comm _ _
  · refine l6e_isIntegralCurve_matTau hT.le hIR fun t ↦ ?_
    have e : -matTau (Λ₁ (T - t)) + (3 / 2 * lam) • J =
        matTau (-Λ₁ (T - t) + (3 / 2 * lam) • J) := by
      rw [l6e_matTau_add, l6e_matTau_neg, l6e_matTau_smul, l6e_matTau_J]
    dsimp only
    rw [l6e_controlP_swap, e, l6e_traceForm_matTau, l6e_matTau_comm, l6e_matTau_comm,
      l6e_matTau_comm]
    exact l6e_matTau_combo _ _ _ _
  · have hae := (Measure.measurePreserving_sub_left volume T).quasiMeasurePreserving.ae hmax
    filter_upwards [hae] with t ht htI
    obtain ⟨hH, hM⟩ := ht ⟨by linarith [htI.2], by linarith [htI.1]⟩
    refine ⟨by rw [l6e_hamiltonian_swap]; exact hH, fun v hv ↦ ?_⟩
    have hv' := hM (fun j ↦ v (vertexSwap j)) (l6e_swap_mem_controlSimplex hv)
    rw [← l6e_hamiltonian_swap] at hv'
    simp only [l6e_vertexSwap_vertexSwap] at hv'
    rw [l6e_hamiltonian_swap]
    exact hv'

/-- The reversed control `t ↦ u(a + b - t)` with the vertices relabelled by the time reversal
(`e₂ ↔ e₃`): `Z_{u'} = -D Z_u D`. -/
def reverseControl (a b : ℝ) (u : ℝ → Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  fun j ↦ u (a + b - t) (vertexSwap j)

/-- The reversal of the control is an involution. -/
private lemma l6e_reverseControl_reverseControl (a b : ℝ) (u : ℝ → Fin 3 → ℝ) :
    reverseControl a b (reverseControl a b u) = u := by
  funext t j
  simp only [reverseControl, l6e_vertexSwap_vertexSwap, sub_sub_cancel]

/-- The switching times of the reversed control are the reflections of those of the control:
the vertices `e_i, e_j` on the two sides of `s` become `e_{τ j}, e_{τ i}` on the two sides of
`a + b - s`. -/
private lemma l6e_isSwitchingTime_reverse {u : ℝ → Fin 3 → ℝ} {a b s : ℝ}
    (h : IsSwitchingTime u s) : IsSwitchingTime (reverseControl a b u) (a + b - s) := by
  obtain ⟨i, j, hij, ε, hε, hl, hr⟩ := h
  have hmp := (Measure.measurePreserving_sub_left volume (a + b)).quasiMeasurePreserving
  refine ⟨vertexSwap j, vertexSwap i, fun h ↦ hij (l6e_vertexSwap_inj h).symm, ε, hε, ?_, ?_⟩
  · filter_upwards [hmp.ae hr] with t ht htI
    have hu := ht ⟨by linarith [htI.2], by linarith [htI.1]⟩
    change (fun k ↦ u (a + b - t) (vertexSwap k)) = _
    rw [hu]
    exact l6e_vertex_swap j
  · filter_upwards [hmp.ae hl] with t ht htI
    have hu := ht ⟨by linarith [htI.2], by linarith [htI.1]⟩
    change (fun k ↦ u (a + b - t) (vertexSwap k)) = _
    rw [hu]
    exact l6e_vertex_swap i

private lemma l6e_isSwitchingTime_reverse_iff {u : ℝ → Fin 3 → ℝ} {a b t : ℝ} :
    IsSwitchingTime (reverseControl a b u) t ↔ IsSwitchingTime u (a + b - t) := by
  constructor
  · intro h
    have := l6e_isSwitchingTime_reverse (a := a) (b := b) h
    rwa [l6e_reverseControl_reverseControl] at this
  · intro h
    have := l6e_isSwitchingTime_reverse (a := a) (b := b) h
    rwa [sub_sub_cancel] at this

/-- Finite bang-bang control is preserved by the reversal (the exceptional set is reflected). -/
private lemma l6e_isFiniteBangBang_reverse {u : ℝ → Fin 3 → ℝ} {a b α β : ℝ}
    (h : IsFiniteBangBang (a + b - β) (a + b - α) u) :
    IsFiniteBangBang α β (reverseControl a b u) := by
  obtain ⟨S, hS⟩ := h
  classical
  refine ⟨S.image (fun x ↦ a + b - x), fun t ht htS ↦ ?_⟩
  have hs : a + b - t ∈ Ioo (a + b - β) (a + b - α) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hsS : a + b - t ∉ S := fun h ↦ htS (Finset.mem_image.2 ⟨_, h, by ring⟩)
  obtain ⟨i, ε, hε, hi⟩ := hS _ hs hsS
  have hmp := (Measure.measurePreserving_sub_left volume (a + b)).quasiMeasurePreserving
  refine ⟨vertexSwap i, ε, hε, ?_⟩
  filter_upwards [hmp.ae hi] with σ hσ hσI
  have hu := hσ ⟨by linarith [hσI.2], by linarith [hσI.1]⟩
  change (fun k ↦ u (a + b - σ) (vertexSwap k)) = _
  rw [hu]
  exact l6e_vertex_swap i

/-- The singular locus is invariant under the time reversal (`-DJD = J`, `det(DgD) = det g`). -/
private lemma l6e_mem_singularLocus_reverse {g Λ₁ X ΛR : Mat2} :
    (diagD * g * diagD, matTau Λ₁, matTau X, matTau ΛR) ∈ singularLocus ↔
      (g, Λ₁, X, ΛR) ∈ singularLocus := by
  have key : ∀ M N : Mat2, matTau M = matTau N → M = N := fun M N h ↦ by
    rw [← l6e_matTau_matTau M, h, l6e_matTau_matTau]
  have hJ : ∀ c : ℝ, matTau (c • J) = c • J := fun c ↦ by rw [l6e_matTau_smul, l6e_matTau_J]
  simp only [singularLocus, mem_ofPred_eq, l6e_det_diagD_conj]
  constructor
  · rintro ⟨μ, hμ, hdet, h1, hX, hR⟩
    exact ⟨μ, hμ, hdet, key _ _ (h1.trans (hJ _).symm), key _ _ (hX.trans l6e_matTau_J.symm),
      key _ _ (hR.trans l6e_matTau_zero.symm)⟩
  · rintro ⟨μ, hμ, hdet, h1, hX, hR⟩
    exact ⟨μ, hμ, hdet, by rw [h1, hJ], by rw [hX, l6e_matTau_J], by rw [hR, l6e_matTau_zero]⟩

/-- **Time reversal of chattering arcs** (Remark 10.2.3 for triangular control; "by time reversal",
TeX 11898, 12000–12013): the time reversal `t ↦ a + b - t` of a chattering arc out of `a`, with the
phase points reversed by `M ↦ -D M D` (`matTau`), `g ↦ D g D` and the controls relabelled
(`reverseControl`), is a chattering arc into `b` with the switching times `a + b - τ n`. -/
theorem IsChatteringArcOutOf.reverse {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcOutOf a b u g X Λ₁ ΛR τ) :
    IsChatteringArcInto a b (reverseControl a b u) (fun t ↦ diagD * g (a + b - t) * diagD)
      (fun t ↦ matTau (X (a + b - t))) (fun t ↦ matTau (Λ₁ (a + b - t)))
      (fun t ↦ matTau (ΛR (a + b - t))) (fun n ↦ a + b - τ n) := by
  obtain ⟨hext, ha, hoff, hbb, hmono, hτI, hlim, hsw⟩ := h
  have e : ∀ t, a + b - (a + t) = a + (b - a - t) := fun t ↦ by ring
  refine ⟨?_, ?_, fun t ht ↦ ?_, fun α β hα hβ ↦
    l6e_isFiniteBangBang_reverse (hbb _ _ (by linarith) (by linarith)), fun m n hmn ↦ ?_,
    fun n ↦ ⟨by linarith [(hτI n).2], by linarith [(hτI n).1]⟩, ?_, fun t ht ↦ ?_⟩
  · have := l6e_isStateCostateSolution_reverse hext
    unfold IsExtremalOn reverseControl
    simp only [e]
    exact this
  · simp only [show a + b - b = a by ring]
    exact l6e_mem_singularLocus_reverse.2 ha
  · simp only [l6e_mem_singularLocus_reverse]
    exact hoff _ ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · have := hmono hmn
    dsimp only
    linarith
  · have := (tendsto_const_nhds (x := a + b)).sub hlim
    rwa [show a + b - a = b by ring] at this
  · rw [l6e_isSwitchingTime_reverse_iff, hsw _ ⟨by linarith [ht.2], by linarith [ht.1]⟩]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by linarith⟩

/-- `Ξ` is closed (`φ` is continuous). -/
private lemma l6e_isClosed_Xi : IsClosed Xi := isClosed_eq continuous_weightedNorm continuous_const

/-- `Ξ` is compact: closed and bounded (`|ξ_j| ≤ 1`, since `|ξ₁|⁶ + |ξ₂|³ + |ξ₃|² = 1`). -/
private lemma l6e_isCompact_Xi : IsCompact Xi := by
  refine Metric.isCompact_of_isClosed_isBounded l6e_isClosed_Xi
    ((Metric.isBounded_closedBall (x := (0 : Fin 3 → ℂ)) (r := 1)).subset fun ξ hξ ↦ ?_)
  have h1 : weightedNorm ξ = 1 := hξ
  have h6 : ‖ξ 0‖ ^ 6 + ‖ξ 1‖ ^ 3 + ‖ξ 2‖ ^ 2 = 1 := by
    have : weightedNorm ξ ^ 6 = ‖ξ 0‖ ^ 6 + ‖ξ 1‖ ^ 3 + ‖ξ 2‖ ^ 2 := by
      unfold weightedNorm
      rw [show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.rpow_inv_natCast_pow (by positivity) (by norm_num)
    rw [← this, h1, one_pow]
  have a0 := pow_nonneg (norm_nonneg (ξ 0)) 6
  have a1 := pow_nonneg (norm_nonneg (ξ 1)) 3
  have a2 := pow_nonneg (norm_nonneg (ξ 2)) 2
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  have b0 : ‖ξ 0‖ ≤ 1 :=
    (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num : 6 ≠ 0)).1 (by linarith)
  have b1 : ‖ξ 1‖ ≤ 1 :=
    (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num : 3 ≠ 0)).1 (by linarith)
  have b2 : ‖ξ 2‖ ≤ 1 :=
    (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num : 2 ≠ 0)).1 (by linarith)
  intro j
  fin_cases j
  exacts [b0, b1, b2]

/-- **Convergence modulo `V_T` from the cluster points** (compactness of `Ξ`; the step "the set
of cluster points … `q_in` is the only cluster point" of TeX 13006–13014): if `ξ_n ∈ Ξ` and every
cluster point of `ξ_n` lies in the Fuller section with class `q_in`, then `ξ_n → ang(τ q_out)`
(the representative of `q_in`) modulo `V_T`. -/
theorem tendstoModVT_of_forall_mapClusterPt {ξs : ℕ → Fin 3 → ℂ} (hΞ : ∀ n, ξs n ∈ Xi)
    (hcl : ∀ ξ, MapClusterPt ξ atTop ξs → ξ ∈ sectionZero ∧ classOf ξ = qIn0) :
    TendstoModVT ξs (ang (tau qOutCart)) := by
  -- the cluster points lie in the orbit of `ang (τ q_out)`
  have horb : ∀ ξ, MapClusterPt ξ atTop ξs → ξ ∈ vtOrbit (ang (tau qOutCart)) := by
    intro ξ hξ
    obtain ⟨hs, hc⟩ := hcl ξ hξ
    have hXi : ξ ∈ Xi := l6e_isClosed_Xi.mem_of_mapClusterPt hξ (Eventually.of_forall hΞ)
    unfold classOf at hc
    rw [dite_eq_left hs] at hc
    have hc' := congrArg Subtype.val hc
    simp only [qIn0, qIn] at hc'
    obtain ⟨v, hv, hveq⟩ := mk_eq_mk_iff_exists_mem_VT.1 hc'
    refine ⟨v, hv, ?_⟩
    rw [← ang_of_mem_Xi hXi]
    exact hveq
  -- a subsequence staying `c` away from the orbit has a cluster point (compactness of `Ξ`)
  unfold TendstoModVT
  refine tendsto_order.2 ⟨fun c hc ↦ Eventually.of_forall fun n ↦ hc.trans_le Metric.infDist_nonneg,
    fun c hc ↦ ?_⟩
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨φ, hφ, hφc⟩ := extraction_of_frequently_atTop hcon
  obtain ⟨ξ, -, ψ, hψ, hlimξ⟩ := l6e_isCompact_Xi.tendsto_subseq fun n ↦ hΞ (φ n)
  have hcl' : MapClusterPt ξ atTop ξs :=
    MapClusterPt.of_comp (φ := φ ∘ ψ) (hφ.comp hψ).tendsto_atTop hlimξ.mapClusterPt
  have h0 : Metric.infDist ξ (vtOrbit (ang (tau qOutCart))) = 0 :=
    Metric.infDist_zero_of_mem (horb ξ hcl')
  have hcont := ((Metric.continuous_infDist_pt (vtOrbit (ang (tau qOutCart)))).tendsto ξ).comp
    hlimξ
  rw [h0] at hcont
  obtain ⟨n, hn⟩ := (hcont.eventually (gt_mem_nhds hc)).exists
  exact hφc (ψ n) hn

end SmoothedPolygons
