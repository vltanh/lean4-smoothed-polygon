module

public import External.NoetherSussmann
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# §9.1: the book's definitions of symmetries, and the Noether–Sussmann theorem as printed

Definitions 9.1.1–9.1.3 and the Noether–Sussmann theorem (Theorem 9.1.4) of Hales–Vajjha,
*Packings of Smoothed Polygons*, §9.1 (TeX 7812–7880), quoted from Sussmann (bibliography entry
`sussman`; `External/NoetherSussmann.lean`).

* **Definition 9.1.1** (`def:symmetry`, TeX 7822–7830), as printed: a symmetry of
  `𝒬 = (M, U, f, φ)` is a diffeomorphism `ψ : V₁ → V₂` between open subsets of `M` such that for
  every `u ∈ U` there are `u₁, u₂ ∈ U` with `dψ(q)(f_u(q)) = f_{u₁}(ψ(q))` and
  `dψ(q)(f_{u₂}(q)) = f_u(ψ(q))` for all `q ∈ V₁` (`IsSymmetryAsPrinted`). Sussmann's
  condition (ii), `φ_{u₁} ∘ ψ = φ_u` and `φ_u ∘ ψ = φ_{u₂}`, is missing.
* **Definition 9.1.2** (`def:infinitesimal-symmetry`, TeX 7836–7843), as printed: an infinitesimal
  group of symmetries is a smooth action `τ : 𝔤 → Γ^∞(TM)` every `exp(tτ(X))` of which is a
  symmetry in the sense of Definition 9.1.1 (`IsInfinitesimalGroupOfSymmetriesAsPrinted`).
* **Definition 9.1.3** (`def:momentum-map`, TeX 7850–7860): `𝐉^τ(q, p)(X) = ⟨p, τ(X)(q)⟩`. This is
  Sussmann's momentum map, `Pontryagin.momentumMap` of the OptimalControl package; no new
  definition.
* **Theorem 9.1.4** (Noether–Sussmann, TeX 7871–7880), as printed, is **false**
  (`noetherSussmann_false_as_printed`). Sussmann's theorem, with (ii), is
  `External.noether_sussmann`; Theorem 9.1.6 is proved from it, not from the printed statement.

## Readings

The objects are read in the coordinates of the OptimalControl package (its readings S1–S8, module
docstring of `OptimalControl.Pontryagin.Noether`): `M` is an open subset `Ω` of a
finite-dimensional real normed space `E`, "diffeomorphism" and "smooth" are read as `C¹` in the
definitions (S2), the flow `exp(tY)` is `Pontryagin.flowMap Y Ω t` on its domain
`Pontryagin.flowDomain Y Ω t` (S3), and the "smooth action" `τ` is a linear map with
`τ⁅X, X'⁆ = [τ X, τ X']` (S8). The two definitions below differ from the package's
`Pontryagin.IsSymmetry` and `Pontryagin.IsInfinitesimalGroupOfSymmetries` only in the missing
condition (ii). "Let `G` be a Lie group with Lie algebra `𝔤`" (TeX 7823) plays no role in the
definitions and is dropped: `𝔤` is any real Lie algebra.

The refuted claim assumes, besides the `C¹` regularity, the book's smoothness: `f(·, u)` smooth
(§6.2, TeX 4686–4692), `τ(X)` a smooth vector field and `exp(tτ(X))` a diffeomorphism
(Definition 9.1.2, TeX 7838–7840; Definition 9.1.1), each as `ContDiffOn ℝ ⊤`, and likewise for
the cost `φ(·, u)`. In Mathlib's scale `⊤ = ω` is analyticity, which implies `C^k` for every `k`
and `C^∞` (`ContDiffOn.of_le`): the hypotheses of the refuted claim imply the book's, so the
printed theorem implies the refuted claim, and the refutation refutes the printed theorem whatever
"smooth" means. The counterexample's data are affine and its flows are translations of `ℝ`.
-/

@[expose] public section

open MeasureTheory Set

namespace SmoothedPolygons

open Pontryagin ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Definition 9.1.1 as printed** (`def:symmetry`, TeX 7822–7830): a symmetry of the optimal
control system `(Ω, U, f, φ)` is a diffeomorphism `ψ : V₁ → V₂` between open subsets of `Ω` (read
as `C¹`: `ψ` maps `V₁` bijectively onto `V₂`, is `C¹` on `V₁`, and its inverse is `C¹` on `V₂`)
such that for every `u ∈ U` there exist `u₁, u₂ ∈ U` for which `dψ(q)(f_u(q)) = f_{u₁}(ψ(q))` and
`dψ(q)(f_{u₂}(q)) = f_u(ψ(q))` for all `q ∈ V₁`. The cost `φ` does not enter: Sussmann's
condition (ii) (`Pontryagin.PermutesFamily`) is not in the book. -/
structure IsSymmetryAsPrinted (f : E → V → E) (Ω : Set E) (U : Set V) (ψ : E → E)
    (V₁ V₂ : Set E) : Prop where
  isOpen_left : IsOpen V₁
  isOpen_right : IsOpen V₂
  left_subset : V₁ ⊆ Ω
  right_subset : V₂ ⊆ Ω
  bijOn : BijOn ψ V₁ V₂
  contDiffOn : ContDiffOn ℝ 1 ψ V₁
  contDiffOn_invFunOn : ContDiffOn ℝ 1 (Function.invFunOn ψ V₁) V₂
  permutes : ∀ u ∈ U, ∃ u₁ ∈ U, ∃ u₂ ∈ U, ∀ q ∈ V₁,
    fderiv ℝ ψ q (f q u) = f (ψ q) u₁ ∧ fderiv ℝ ψ q (f q u₂) = f (ψ q) u

/-- **Definition 9.1.2 as printed** (`def:infinitesimal-symmetry`, TeX 7836–7843): an
infinitesimal group of symmetries of `(Ω, U, f, φ)` is a smooth action `τ : 𝔤 → Γ^∞(TM)` of the
Lie algebra `𝔤` (read as in the package: linear, `τ⁅X, X'⁆ = [τ X, τ X']` on `Ω`, each `τ(X)` of
class `C¹` on `Ω`) such that every diffeomorphism `exp(tτ(X))` is a symmetry in the sense of
Definition 9.1.1 as printed (`IsSymmetryAsPrinted`). -/
structure IsInfinitesimalGroupOfSymmetriesAsPrinted {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (f : E → V → E) (Ω : Set E) (U : Set V) (τ : L →ₗ[ℝ] E → E) : Prop where
  map_lie : ∀ X X' : L, ∀ x ∈ Ω, τ ⁅X, X'⁆ x = VectorField.lieBracket ℝ (τ X) (τ X') x
  contDiffOn : ∀ X : L, ContDiffOn ℝ 1 (τ X) Ω
  isSymmetry : ∀ (X : L) (t : ℝ), IsSymmetryAsPrinted f Ω U (flowMap (τ X) Ω t)
    (flowDomain (τ X) Ω t) (flowDomain (τ X) Ω (-t))

/-- `r ↦ x + r a` is the integral curve of the constant field `a` on `ℝ` from `x`. -/
private lemma isIntegralCurveIn_const (a x s : ℝ) :
    IsIntegralCurveIn (fun _ ↦ a) univ x s (fun r ↦ x + r * a) := by
  refine ⟨by fun_prop, intervalIntegrable_const, fun r _ ↦ ?_, fun _ _ ↦ mem_univ _⟩
  simp

/-- The time-`s` map of the constant field `a` on `ℝ` is the translation by `s a`. -/
private lemma flowMap_const (a s : ℝ) : flowMap (fun _ ↦ a) univ s = fun x ↦ x + s * a :=
  funext fun x ↦ flowMap_eq_of_isIntegralCurveIn isOpen_univ contDiffOn_const
    (isIntegralCurveIn_const a x s)

/-- The flow of a constant field on `ℝ` is defined everywhere. -/
private lemma flowDomain_const (a s : ℝ) : flowDomain (fun _ ↦ a) univ s = univ :=
  eq_univ_of_forall fun x ↦ ⟨_, isIntegralCurveIn_const a x s⟩

/-- The inverse of the translation by `c` is the translation by `-c`. -/
private lemma invFunOn_add_const (c : ℝ) :
    Function.invFunOn (fun x ↦ x + c) univ = fun y ↦ y - c := by
  funext y
  have := Function.invFunOn_eq (f := fun x : ℝ ↦ x + c) (s := univ) ⟨y - c, mem_univ _, by ring⟩
  linarith

/-- **The Noether–Sussmann theorem as printed is false** (Theorem 9.1.4, `thm:noether-sussmann`,
label of this formalization; unlabelled, TeX 7871–7880, with Definitions 9.1.1–9.1.3 as
printed). The printed statement: for an optimal control system `𝒬 = (M, U, f, φ)` with the
regularity of §6.2 (here: `Ω` open, `U` compact, `f` and `φ` of class `C¹` in the sense of
`ControlSystem.IsC1On`, and `f(·, u)`, `φ(·, u)` smooth) and a cost `φ` independent of the
control (TeX 7816–7818), an infinitesimal group of symmetries `τ`
(Definition 9.1.2 as printed, with smooth fields `τ(X)` and smooth flows `exp(tτ(X))` with smooth
inverses) and a lifted controlled trajectory `p` satisfying the Pontryagin maximum principle (here
all the conclusions of `External.pontryagin_maximum_principle` for a problem with fixed endpoints,
for which transversality is empty: `ν ≤ 0`, `p` Lipschitz, `(ν, p(t)) ≠ 0`, the adjoint equation,
the maximum condition, `H = 0` almost everywhere), the momentum map `𝐉^τ` is constant along `p`.
"Smooth" is `ContDiffOn ℝ ⊤`, analytic, which implies `C^∞` (module docstring). It fails already
on `M = ℝ`.

Counterexample: `U = [-1, 1]`, `f(x, u) = u`, `φ(x, u) = x`, the Lie algebra `ℝ` acting by
`τ(a) = a ∂ₓ` (flows `x ↦ x + at`, which satisfy Definition 9.1.1 as printed with `u₁ = u₂ = u`,
since `f` does not depend on `x`; they do not preserve the cost, against Sussmann's (ii)). On
`[0, 2]`, `q(t) = |1 - t|` with `ũ(t) = -1` for `t ≤ 1` and `1` for `t > 1`, `ν = -1` and
`p(t) = (t - 1) dx`: `ṗ = -ν ∂ₓφ = 1`, the maximum of `H = p u + ν x` over `u ∈ [-1, 1]` is
attained at `u = ũ(t)`, and `H = (t - 1) ũ(t) - |1 - t| = 0`. The momentum
`𝐉^τ(q(t), p(t))(1) = p(t)(1) = t - 1` is not constant. (The pair is optimal for the cost
`∫₀² x dt` with `x(0) = x(2) = 1`: `x(t) ≥ |1 - t|` for every admissible `x`. In Sussmann's
convention, `c = 1`, `ζ(t) = 1 - t`.)

Proof: `L = ℝ` with the commutator bracket (`LieRing.ofAssociativeRing`,
`LieAlgebra.ofAssociativeAlgebra`: `⁅a, b⁆ = 0`), `Ω = univ`, `τ(a) = fun _ ↦ a`.
1. `f`, `φ` are affine: `C¹` and analytic; `[-1, 1]` is compact.
2. The flow of the constant field `a` on `ℝ` is `x ↦ x + ta` on `flowDomain = univ`
   (`Pontryagin.flowMap_eq_of_isIntegralCurveIn` with the curve `r ↦ x + ra`), with inverse
   `y ↦ y - ta`; `fderiv` of a translation is the identity, so `u₁ = u₂ = u` work; the bracket of
   the constant fields and `τ⁅a, b⁆ = τ 0` are `0`.
3. `ũ` is measurable and monotone, hence integrable; `q(t) = 1 + ∫₀ᵗ ũ` by splitting at `1`.
4. The adjoint integrand is `p(r) ∘ 0 + (-1) • id = -id`, so `p(t) = p(2) + ∫ₜ² (-id)`; `p` is
   `1`-Lipschitz; `(ν, p(t)) ≠ 0` since `ν = -1`.
5. `H(u) = (t - 1) u - |1 - t| ≤ 0 = H(ũ(t))` for `u ∈ [-1, 1]`, at every `t`.
6. At `t = 2`: `𝐉^τ(q(2), p(2))(1) = 1 ≠ -1 = 𝐉^τ(q(0), p(0))(1)`. -/
theorem noetherSussmann_false_as_printed :
    ¬ ∀ (L : Type) [LieRing L] [LieAlgebra ℝ L] (Ω U : Set ℝ) (f φ : ℝ → ℝ → ℝ)
      (τ : L →ₗ[ℝ] ℝ → ℝ), IsOpen Ω → IsCompact U → IsC1On f Ω U → IsC1On φ Ω U →
      (∀ u ∈ U, ContDiffOn ℝ ⊤ (f · u) Ω) → (∀ u ∈ U, ContDiffOn ℝ ⊤ (φ · u) Ω) →
      (∀ x u v, φ x u = φ x v) → IsInfinitesimalGroupOfSymmetriesAsPrinted f Ω U τ →
      (∀ X : L, ContDiffOn ℝ ⊤ (τ X) Ω) →
      (∀ (X : L) (t : ℝ), ContDiffOn ℝ ⊤ (flowMap (τ X) Ω t) (flowDomain (τ X) Ω t) ∧
        ContDiffOn ℝ ⊤ (Function.invFunOn (flowMap (τ X) Ω t) (flowDomain (τ X) Ω t))
          (flowDomain (τ X) Ω (-t))) →
      ∀ (T ν : ℝ) (ũ q : ℝ → ℝ) (p : ℝ → StrongDual ℝ ℝ),
        IsAdmissibleIn f Ω U (q 0) T ũ q → ν ≤ 0 → (∃ K, LipschitzOnWith K p (Icc 0 T)) →
        (∀ t ∈ Icc 0 T, (ν, p t) ≠ 0) → IsAdjoint f φ ν ũ q T p → IsMaximal f φ ν U ũ q T p →
        (∀ᵐ t ∂(volume.restrict (Icc 0 T)), controlHamiltonian f φ ν (q t) (p t) (ũ t) = 0) →
        ∀ t ∈ Icc 0 T, momentumMap τ (q t) (p t) = momentumMap τ (q 0) (p 0) := by
  intro H
  let instL : LieRing ℝ := LieRing.ofAssociativeRing
  let instA : LieAlgebra ℝ ℝ := LieAlgebra.ofAssociativeAlgebra
  -- the system: `ẋ = u`, `u ∈ [-1, 1]`, cost `x`; the Lie algebra `ℝ` acts by translations
  let f : ℝ → ℝ → ℝ := fun _ u ↦ u
  let φ : ℝ → ℝ → ℝ := fun x _ ↦ x
  let τ : ℝ →ₗ[ℝ] ℝ → ℝ := LinearMap.smulRight LinearMap.id (fun _ ↦ (1 : ℝ))
  have hτ : ∀ a, τ a = fun _ ↦ a := fun a ↦ by funext x; simp [τ]
  -- the pair `q(t) = |1 - t|`, `ũ(t) = -1` for `t ≤ 1` and `1` for `t > 1`, `p(t) = (t - 1) dx`
  let ũ : ℝ → ℝ := fun t ↦ if t ≤ 1 then -1 else 1
  let q : ℝ → ℝ := fun t ↦ |1 - t|
  let p : ℝ → StrongDual ℝ ℝ := fun t ↦ (t - 1) • ContinuousLinearMap.id ℝ ℝ
  have hfd : ∀ x u, fderiv ℝ (f · u) x = 0 := fun x u ↦ fderiv_const_apply u
  have hφd : ∀ x u, fderiv ℝ (φ · u) x = ContinuousLinearMap.id ℝ ℝ := fun x u ↦ fderiv_id
  -- the regularity of the system
  have hf1 : IsC1On f univ (Icc (-1) 1) :=
    ⟨continuous_snd.continuousOn, fun _ _ _ _ ↦ differentiableAt_const _,
      continuousOn_const.congr fun x _ ↦ hfd x.1 x.2⟩
  have hφ1 : IsC1On φ univ (Icc (-1) 1) :=
    ⟨continuous_fst.continuousOn, fun _ _ _ _ ↦ differentiableAt_fun_id,
      continuousOn_const.congr fun x _ ↦ hφd x.1 x.2⟩
  -- the translations are symmetries in the sense of Definition 9.1.1 as printed
  have hsymm : IsInfinitesimalGroupOfSymmetriesAsPrinted f univ (Icc (-1) 1) τ := by
    refine ⟨fun X X' x _ ↦ ?_, fun X ↦ ?_, fun X t ↦ ?_⟩
    · have : ⁅X, X'⁆ = 0 := by rw [Ring.lie_def, mul_comm, sub_self]
      rw [this, map_zero, hτ, hτ]
      simp [VectorField.lieBracket]
    · rw [hτ]
      exact contDiffOn_const
    · rw [hτ, flowMap_const, flowDomain_const, flowDomain_const]
      refine ⟨isOpen_univ, isOpen_univ, subset_rfl, subset_rfl,
        Set.bijOn_univ.2 (Equiv.addRight (t * X)).bijective, by fun_prop,
        by rw [invFunOn_add_const]; fun_prop,
        fun u hu ↦ ⟨u, hu, u, hu, fun y _ ↦ ?_⟩⟩
      simp [f]
  -- the pair `(ũ, q)`
  have hũ_mono : Monotone ũ := fun a b hab ↦ by
    simp only [ũ]
    split_ifs <;> linarith
  have hũU : ∀ t, ũ t ∈ Icc (-1 : ℝ) 1 := fun t ↦ by
    simp only [ũ]
    split_ifs <;> norm_num
  have hint : ∀ a b, IntervalIntegrable ũ volume a b := fun a b ↦ hũ_mono.intervalIntegrable
  have hconst : ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Ioc a b, ũ s = c) → ∫ s in a..b, ũ s = (b - a) * c := by
    intro a b c hab hc
    rw [intervalIntegral.integral_congr_ae (g := fun _ ↦ c)
      (Filter.Eventually.of_forall fun s hs ↦ hc s (by rwa [uIoc_of_le hab] at hs))]
    simp
  have hq : ∀ t ∈ Icc (0 : ℝ) 2, q t = q 0 + ∫ s in (0 : ℝ)..t, ũ s := by
    intro t ⟨ht0, ht2⟩
    rcases le_or_gt t 1 with ht1 | ht1
    · rw [hconst 0 t (-1) ht0 fun s hs ↦ ite_eq_left (hs.2.trans ht1)]
      simp only [q, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)]
      norm_num
      ring
    · rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 1) (hint 1 t),
        hconst 0 1 (-1) zero_le_one fun s hs ↦ ite_eq_left hs.2,
        hconst 1 t 1 ht1.le fun s hs ↦ ite_eq_right (not_le.2 hs.1)]
      simp only [q, abs_of_neg (by linarith : 1 - t < 0)]
      norm_num
  have hadm : IsAdmissibleIn f univ (Icc (-1) 1) (q 0) 2 ũ q :=
    ⟨⟨Measurable.ite measurableSet_Iic measurable_const measurable_const, fun t _ ↦ hũU t,
      (by fun_prop : Continuous q).continuousOn, hint 0 2, hq⟩, fun _ _ ↦ mem_univ _⟩
  -- the costate `p(t) = (t - 1) dx` with `ν = -1`: `ṗ = -ν ∂ₓφ = dx`
  have hadj_int : ∀ r, (p r).comp (linearization f ũ q r) + (-1 : ℝ) • fderiv ℝ (φ · (ũ r)) (q r) =
      -ContinuousLinearMap.id ℝ ℝ := fun r ↦ by
    simp only [linearization, hfd, hφd, ContinuousLinearMap.comp_zero, zero_add, neg_one_smul]
  have hadj : IsAdjoint f φ (-1) ũ q 2 p := by
    refine ⟨?_, fun t _ ↦ ?_⟩
    · simp_rw [hadj_int]
      exact intervalIntegrable_const
    · simp_rw [hadj_int, intervalIntegral.integral_const]
      ext
      simp [p]
  have hlip : LipschitzWith 1 p := LipschitzWith.of_dist_le_mul fun t s ↦ by
    have hps : p t - p s = (t - s) • ContinuousLinearMap.id ℝ ℝ := by
      ext
      simp [p]
    rw [dist_eq_norm, hps, norm_smul, ContinuousLinearMap.norm_id, mul_one, NNReal.coe_one,
      one_mul, Real.dist_eq, Real.norm_eq_abs]
  have hnontriv : ∀ t ∈ Icc (0 : ℝ) 2, ((-1 : ℝ), p t) ≠ 0 := fun t _ h ↦ by
    have := congrArg Prod.fst h
    norm_num at this
  -- the maximum condition and `H = 0`: `H(u) = (t - 1) u - |1 - t|`
  have hH : ∀ t u, controlHamiltonian f φ (-1) (q t) (p t) u = (t - 1) * u - |1 - t| := by
    intro t u
    simp [controlHamiltonian, f, φ, p, q]
    ring
  have hmax : IsMaximal f φ (-1) (Icc (-1) 1) ũ q 2 p :=
    Filter.Eventually.of_forall fun t u hu ↦ by
      rw [hH, hH]
      simp only [ũ]
      split_ifs with ht
      · nlinarith [hu.1]
      · nlinarith [hu.2]
  have hzero : ∀ t, controlHamiltonian f φ (-1) (q t) (p t) (ũ t) = 0 := fun t ↦ by
    rw [hH]
    simp only [ũ]
    split_ifs with ht
    · rw [abs_of_nonneg (by linarith)]
      ring
    · rw [abs_of_neg (by linarith)]
      ring
  -- the printed theorem would make `𝐉^τ(q(t), p(t))(1) = p(t)(1) = t - 1` constant
  have h := @H ℝ instL instA univ (Icc (-1) 1) f φ τ isOpen_univ isCompact_Icc hf1 hφ1
    (fun _ _ ↦ contDiffOn_const) (fun _ _ ↦ by fun_prop) (fun _ _ _ ↦ rfl) hsymm
    (fun X ↦ by rw [hτ]; exact contDiffOn_const)
    (fun X t ↦ by
      rw [hτ, flowMap_const, flowDomain_const, flowDomain_const, invFunOn_add_const]
      exact ⟨by fun_prop, by fun_prop⟩)
    2 (-1) ũ q p hadm (by norm_num) ⟨1, hlip.lipschitzOnWith⟩ hnontriv hadj hmax
    (Filter.Eventually.of_forall hzero) 2 ⟨zero_le_two, le_rfl⟩
  have h1 := LinearMap.congr_fun h 1
  simp [momentumMap_apply, momentum, hτ, p] at h1


end SmoothedPolygons
