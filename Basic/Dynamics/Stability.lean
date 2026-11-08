module

public import Mathlib.Dynamics.FixedPoints.Topology
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Stability of fixed points of maps

Lyapunov stability, asymptotic stability and instability of a fixed point `x₀` of a map
`f : X → X` of a topological space (a discrete-time dynamical system), as they are used for the
Fuller–Poincaré map in Hales–Vajjha, *Packings of Smoothed Polygons*, Lemma 13.5.5
(TeX 11433–11453):

* `Function.IsLyapunovStable f x₀`: every neighborhood `U` of `x₀` contains a neighborhood `V` of
  `x₀` whose forward orbits stay in `U`;
* `Function.IsAsymptoticallyStable f x₀`: `x₀` is a Lyapunov stable fixed point that attracts
  every point of some neighborhood;
* `Function.IsUnstable f x₀`: `x₀` is a fixed point that is not Lyapunov stable.

Results:

* `Function.IsAsymptoticallyStable.of_conj`: asymptotic stability is a local notion, invariant
  under conjugation by an open partial homeomorphism (a chart) near the fixed point;
* `Function.IsAsymptoticallyStable.isUnstable_of_involutive`: time reversal. If `σ` is a
  continuous involution such that `σ ∘ f` is an involution near `x₀` and near `σ x₀` (so that `f`
  near `σ x₀` is conjugate by `σ` to the inverse of `f` near `x₀`), and `x₀` is asymptotically
  stable and not isolated, then `σ x₀` is an unstable fixed point.

Mathlib has no notion of stability of fixed points (checked: no `Lyapunov`, `IsAsymptoticallyStable`
or attractor for maps); these are standard definitions.
-/

@[expose] public section

open Filter Topology Set

namespace Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `x₀` is a **Lyapunov stable** point of `f`: every neighborhood `U` of `x₀` contains a
neighborhood `V` of `x₀` such that `fⁿ(x) ∈ U` for all `x ∈ V` and all `n ≥ 0`. -/
def IsLyapunovStable (f : X → X) (x₀ : X) : Prop :=
  ∀ U ∈ 𝓝 x₀, ∃ V ∈ 𝓝 x₀, ∀ x ∈ V, ∀ n : ℕ, f^[n] x ∈ U

/-- `x₀` is a (locally) **asymptotically stable** fixed point of `f`: it is fixed, Lyapunov
stable, and attracting (`fⁿ(x) → x₀` for every `x` in some neighborhood of `x₀`). -/
def IsAsymptoticallyStable (f : X → X) (x₀ : X) : Prop :=
  IsFixedPt f x₀ ∧ IsLyapunovStable f x₀ ∧
    ∃ V ∈ 𝓝 x₀, ∀ x ∈ V, Tendsto (fun n : ℕ ↦ f^[n] x) atTop (𝓝 x₀)

/-- `x₀` is an **unstable** fixed point of `f`: it is fixed and not Lyapunov stable. -/
def IsUnstable (f : X → X) (x₀ : X) : Prop :=
  IsFixedPt f x₀ ∧ ¬ IsLyapunovStable f x₀

/-- The orbits of a conjugacy: if `f` is conjugate by the chart `e` to `g` near `x₀` and `e x₀` is a
Lyapunov stable point of `g`, then every neighborhood `U` of `x₀` contains a neighborhood `V`
whose `f`-orbits stay in `U ∩ e.source` and are carried by `e` to the `g`-orbits. -/
private lemma l4a_exists_orbit_conj {f : X → X} {g : Y → Y} {x₀ : X}
    (e : OpenPartialHomeomorph X Y) (hx₀ : x₀ ∈ e.source)
    (hconj : ∀ᶠ x in 𝓝 x₀, f x ∈ e.source ∧ e (f x) = g (e x))
    (hg : IsLyapunovStable g (e x₀)) {U : Set X} (hU : U ∈ 𝓝 x₀) :
    ∃ V ∈ 𝓝 x₀, ∀ x ∈ V, ∀ n : ℕ, f^[n] x ∈ U ∩ e.source ∧ e (f^[n] x) = g^[n] (e x) := by
  set W := (U ∩ e.source) ∩ {x | f x ∈ e.source ∧ e (f x) = g (e x)} with hWdef
  have hW : W ∈ 𝓝 x₀ := inter_mem (inter_mem hU (e.open_source.mem_nhds hx₀)) hconj
  obtain ⟨V', hV', hV'g⟩ := hg _ (e.image_mem_nhds hx₀ hW)
  refine ⟨W ∩ e ⁻¹' V', inter_mem hW (e.continuousAt hx₀ hV'), ?_⟩
  rintro x ⟨hxW, hxV⟩
  have key : ∀ n : ℕ, f^[n] x ∈ W ∧ e (f^[n] x) = g^[n] (e x) := by
    intro n
    induction n with
    | zero => exact ⟨hxW, rfl⟩
    | succ n ih =>
      obtain ⟨⟨-, hfs, hfe⟩, he⟩ := ih
      have h1 : e (f^[n + 1] x) = g^[n + 1] (e x) := by
        rw [iterate_succ_apply', iterate_succ_apply', hfe, he]
      obtain ⟨u, hu, hue⟩ := hV'g (e x) hxV (n + 1)
      have hu' : u = f^[n + 1] x :=
        e.injOn hu.1.2 (by rw [iterate_succ_apply']; exact hfs) (by rw [hue, h1])
      exact ⟨hu' ▸ hu, h1⟩
  exact fun n ↦ ⟨(key n).1.1, (key n).2⟩

/-- **Asymptotic stability is invariant under a local conjugacy.** Let `e` be an open partial
homeomorphism (a chart) with `x₀` in its source, and suppose that near `x₀` the map `f` is
conjugate by `e` to `g`: `f x` lies in the source of `e` and `e (f x) = g (e x)`. If `e x₀` is an
asymptotically stable fixed point of `g`, then `x₀` is an asymptotically stable fixed point of `f`.

Proof: `f x₀ = x₀` because `e` is injective on its source. Given a neighborhood `U` of `x₀`,
shrink it into the conjugacy neighborhood `W ⊆ e.source`; `e '' U` is a neighborhood of `e x₀`;
stability of `g` gives `V'` whose `g`-orbits stay in `e '' U`, and on `e ⁻¹' V' ∩ U` one shows by
induction on `n` that `fⁿ x ∈ U` and `e (fⁿ x) = gⁿ (e x)`. Attraction transfers through the
continuity of `e.symm` at `e x₀`. -/
theorem IsAsymptoticallyStable.of_conj {f : X → X} {g : Y → Y} {x₀ : X}
    (e : OpenPartialHomeomorph X Y) (hx₀ : x₀ ∈ e.source)
    (hconj : ∀ᶠ x in 𝓝 x₀, f x ∈ e.source ∧ e (f x) = g (e x))
    (hg : IsAsymptoticallyStable g (e x₀)) : IsAsymptoticallyStable f x₀ := by
  obtain ⟨hfix, hstab, V₀, hV₀, hattr⟩ := hg
  have hfx₀ : f x₀ = x₀ := by
    obtain ⟨h1, h2⟩ := hconj.self_of_nhds
    exact e.injOn h1 hx₀ (by rw [h2, hfix.eq])
  refine ⟨hfx₀, fun U hU ↦ ?_, ?_⟩
  · obtain ⟨V, hV, hVU⟩ := l4a_exists_orbit_conj e hx₀ hconj hstab hU
    exact ⟨V, hV, fun x hx n ↦ (hVU x hx n).1.1⟩
  · obtain ⟨V, hV, hVU⟩ :=
      l4a_exists_orbit_conj e hx₀ hconj hstab (e.open_source.mem_nhds hx₀)
    refine ⟨V ∩ e ⁻¹' V₀, inter_mem hV (e.continuousAt hx₀ hV₀), fun x hx ↦ ?_⟩
    have h1 : Tendsto (fun n : ℕ ↦ e (f^[n] x)) atTop (𝓝 (e x₀)) := by
      simpa only [(hVU x hx.1 _).2] using hattr (e x) hx.2
    have h2 := (e.continuousAt_symm (e.map_source hx₀)).tendsto.comp h1
    rw [e.left_inv hx₀] at h2
    exact h2.congr fun n ↦ e.left_inv (hVU x hx.1 n).1.2

/-- **Time reversal turns an asymptotically stable fixed point into an unstable one.** Let `σ` be
a continuous involution of a locally compact Hausdorff space and `x₀` an asymptotically stable
fixed point of `f`, not isolated, with `f` continuous near `x₀`. Suppose that `σ ∘ f` is an
involution near `x₀` and near `σ x₀`. Then `σ x₀` is an unstable fixed point of `f`.

(In the application, `f` is the Fuller–Poincaré map and `σ` the time reversal `τ`:
`τ ∘ F ∘ τ = F⁻¹`, Lemmas 13.2.3 and 13.2.5 of Hales–Vajjha.)

Proof: `σ x₀` is fixed (`(σ f)(σ f) x₀ = x₀` and `f x₀ = x₀`). Suppose it were Lyapunov stable;
conjugating by `σ`, `h = σ f σ` is Lyapunov stable at `x₀`, and `f (h y) = y` near `x₀` (from the
involution near `σ x₀`). Take a compact neighborhood `K₁` of `x₀` whose `f`-orbits stay in a
neighborhood `K` on which `f` is continuous and which lies in the basin of `x₀`; take `y ≠ x₀`
whose `h`-orbit `yₙ = hⁿ y` stays in `K₁` and where `f ∘ h = id`, so that `y = fⁿ (yₙ)` for all
`n`. A cluster point `p` of `(yₙ)` lies in `K₁`, so `f^m p` is in a neighborhood `O'` of `x₀`
whose orbits stay in a neighborhood `O` of `x₀` not containing `y`; by continuity `f^m yₙ ∈ O'`
for some `n ≥ m`, hence `y = f^(n - m) (f^m yₙ) ∈ O`, a contradiction. -/
theorem IsAsymptoticallyStable.isUnstable_of_involutive [T2Space X] [LocallyCompactSpace X]
    {f σ : X → X} {x₀ : X} (hf : IsAsymptoticallyStable f x₀)
    (hcont : ∀ᶠ x in 𝓝 x₀, ContinuousAt f x) (hσ : Continuous σ) (hσσ : Involutive σ)
    (h₀ : ∀ᶠ x in 𝓝 x₀, σ (f (σ (f x))) = x)
    (h₁ : ∀ᶠ y in 𝓝 (σ x₀), σ (f (σ (f y))) = y) (hne : (𝓝[≠] x₀).NeBot) :
    IsUnstable f (σ x₀) := by
  obtain ⟨hfix, hstab, B, hB, hattr⟩ := hf
  -- `σ x₀` is fixed.
  have hfix' : IsFixedPt f (σ x₀) := by
    have h := congrArg σ h₀.self_of_nhds
    rwa [hfix.eq, hσσ] at h
  refine ⟨hfix', fun hst ↦ ?_⟩
  -- `h = σ f σ` is Lyapunov stable at `x₀`, and `f ∘ h = id` near `x₀`.
  set h : X → X := σ ∘ f ∘ σ with hh
  have hiter : ∀ (n : ℕ) (y : X), h^[n] y = σ (f^[n] (σ y)) := by
    intro n
    induction n with
    | zero => exact fun y ↦ (hσσ y).symm
    | succ n ih =>
      intro y
      rw [iterate_succ_apply', ih, iterate_succ_apply']
      simp only [hh, comp_apply, hσσ _]
  have hhstab : IsLyapunovStable h x₀ := by
    intro U hU
    obtain ⟨V, hV, hVU⟩ := hst _ (hσ.continuousAt.preimage_mem_nhds (by rwa [hσσ]))
    exact ⟨σ ⁻¹' V, hσ.continuousAt.preimage_mem_nhds hV, fun y hy n ↦ by
      rw [hiter]; exact hVU _ hy n⟩
  have hA : ∀ᶠ y in 𝓝 x₀, f (h y) = y := by
    filter_upwards [hσ.continuousAt.eventually_mem h₁] with y hy
    have hy' := congrArg σ hy
    simp only [hσσ _] at hy'
    simpa only [hh, comp_apply] using hy'
  -- A compact neighborhood `K₁` of `x₀` whose `f`-orbits stay in the basin and in the set where
  -- `f` is continuous.
  obtain ⟨V₁, hV₁, hV₁orb⟩ := hstab _ (inter_mem hB hcont)
  obtain ⟨K₁, hK₁, hK₁V, hK₁c⟩ := local_compact_nhds hV₁
  -- A point `y ≠ x₀` whose `h`-orbit stays in `K₁` and in the set where `f ∘ h = id`.
  obtain ⟨W, hW, hWorb⟩ := hhstab _ (inter_mem hK₁ hA)
  obtain ⟨y, hyW, hyne⟩ : (W ∩ {x₀}ᶜ).Nonempty := nonempty_of_mem (f := 𝓝[≠] x₀)
    (inter_mem (mem_nhdsWithin_of_mem_nhds hW) self_mem_nhdsWithin)
  set u : ℕ → X := fun n ↦ h^[n] y with hu_def
  have hu : ∀ n, u n ∈ K₁ ∧ f (h (u n)) = u n := hWorb y hyW
  have hyu : ∀ n, f^[n] (u n) = y := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [hu_def] at ih hu ⊢
      rw [iterate_succ_apply' h, iterate_succ_apply, (hu n).2, ih]
  -- A cluster point `p ∈ K₁` of the orbit `(u n)`.
  obtain ⟨p, hpK, hp⟩ :=
    hK₁c.exists_mapClusterPt (f := atTop) (u := u) (tendsto_principal.2
      (Eventually.of_forall fun n ↦ (hu n).1))
  have hp1 := hV₁orb p (hK₁V hpK)
  -- A neighborhood `O'` of `x₀` whose `f`-orbits avoid `y`.
  obtain ⟨O', hO', hO'orb⟩ :=
    hstab _ (isOpen_compl_singleton.mem_nhds (mem_compl_singleton_iff.2 (Ne.symm hyne)))
  obtain ⟨m, hm⟩ := ((hattr p (hp1 0).1).eventually (interior_mem_nhds.2 hO')).exists
  have hcont_iter : ∀ k : ℕ, ContinuousAt f^[k] p := by
    intro k
    induction k with
    | zero => exact continuousAt_id
    | succ k ih => rw [iterate_succ']; exact ContinuousAt.comp (hp1 k).2 ih
  have hnb : f^[m] ⁻¹' interior O' ∈ 𝓝 p :=
    (hcont_iter m).preimage_mem_nhds (isOpen_interior.mem_nhds hm)
  obtain ⟨n, hmn, hn⟩ := (hp.frequently hnb).forall_exists_of_atTop m
  have hy : f^[n - m] (f^[m] (u n)) = y := by
    rw [← iterate_add_apply, Nat.sub_add_cancel hmn, hyu]
  have := hO'orb _ (interior_subset hn) (n - m)
  rw [hy] at this
  exact this rfl

end Function
