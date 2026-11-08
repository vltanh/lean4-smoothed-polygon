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
  sorry

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
whose `h`-orbit `yₙ = hⁿ y` stays in `K₁`, so that `y = fⁿ (yₙ)` for all `n`. A cluster point `p`
of `(yₙ)` lies in `K₁`, so `f^m p` is in a neighborhood `O'` of `x₀` whose orbits stay in a
neighborhood `O` of `x₀` not containing `y`; by continuity `f^m yₙ ∈ O'` for some `n ≥ m`, hence
`y = f^(n - m) (f^m yₙ) ∈ O`, a contradiction. -/
theorem IsAsymptoticallyStable.isUnstable_of_involutive [T2Space X] [LocallyCompactSpace X]
    {f σ : X → X} {x₀ : X} (hf : IsAsymptoticallyStable f x₀)
    (hcont : ∀ᶠ x in 𝓝 x₀, ContinuousAt f x) (hσ : Continuous σ) (hσσ : Involutive σ)
    (h₀ : ∀ᶠ x in 𝓝 x₀, σ (f (σ (f x))) = x)
    (h₁ : ∀ᶠ y in 𝓝 (σ x₀), σ (f (σ (f y))) = y) (hne : (𝓝[≠] x₀).NeBot) :
    IsUnstable f (σ x₀) := by
  sorry

end Function
