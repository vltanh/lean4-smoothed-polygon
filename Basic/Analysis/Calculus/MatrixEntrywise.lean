module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.UniformSpace.Matrix

/-!
# Entrywise calculus for matrix-valued functions of a real variable

Mathlib puts no canonical norm on `Matrix m n 𝕜`: several norms are available as local instances
(`Matrix.Norms.Elementwise`, `Matrix.Norms.Frobenius`, `Matrix.Norms.Operator`), all equivalent in
finite dimension. To state results about derivatives and Lipschitz continuity of matrix-valued
curves without choosing a norm, we phrase them entry by entry. For finite index types these
notions agree with the corresponding notions for any norm on the matrices. In fact Mathlib defines
`HasDerivAt` for functions with values in any topological vector space, so it applies to
`ℝ → Matrix m n 𝕜` with the product topology, and `Matrix.hasDerivAtEntrywise_iff_hasDerivAt`
identifies it with `HasDerivAtEntrywise`; with a local norm instance such as
`open scoped Matrix.Norms.Operator` (under which square matrices form a Banach algebra) one gets
the same `HasDerivAt` up to unfolding of instances, which is how the lemmas about inverses (here)
and exponentials (in `Basic.Analysis.Calculus.MatrixEntrywiseExp`) are proved.

Throughout, `𝕜` is a nontrivially normed field which is a normed `ℝ`-algebra (in practice `ℝ` or
`ℂ`), `f g : ℝ → Matrix m n 𝕜` are curves and `f' g'` are matrices.

## Definitions

* `Matrix.HasDerivAtEntrywise f f' t`: every entry `f · i j` has derivative `f' i j` at `t`.
* `Matrix.HasDerivWithinAtEntrywise f f' s t`: the same within the set `s`.
* `Matrix.derivEntrywise f t`: the matrix of the derivatives `deriv (f · i j) t`.
* `Matrix.LipschitzOnEntrywise f s`: every entry of the real matrix-valued `f` is Lipschitz on
  `s`.

## API

Continuity, entry by entry (the topology on `Matrix m n R` is the product topology):
`Matrix.continuousAt_iff_entrywise`, `Matrix.continuousWithinAt_iff_entrywise`,
`Matrix.continuousOn_iff_entrywise`, `Matrix.continuous_iff_entrywise`.

General facts, each for `HasDerivAtEntrywise` and `HasDerivWithinAtEntrywise`:
* `HasDerivAtEntrywise.hasDerivWithinAtEntrywise`, `HasDerivWithinAtEntrywise.hasDerivAtEntrywise`
  (within a neighbourhood), `Matrix.hasDerivWithinAtEntrywise_univ`;
* `HasDerivWithinAtEntrywise.mono`, `HasDerivWithinAtEntrywise.mono_of_mem_nhdsWithin`;
* `congr_of_eventuallyEq`, `HasDerivWithinAtEntrywise.congr`,
  `HasDerivWithinAtEntrywise.congr_of_mem`, `congr_deriv`;
* `HasDerivAtEntrywise.unique`, `HasDerivWithinAtEntrywise.unique` (given
  `UniqueDiffWithinAt ℝ s t`), `HasDerivAtEntrywise.derivEntrywise`;
* `HasDerivAtEntrywise.continuousAt`, `HasDerivWithinAtEntrywise.continuousWithinAt`,
  `HasDerivWithinAtEntrywise.continuousOn`;
* `Matrix.hasDerivAtEntrywise_fin_two_iff`, `Matrix.hasDerivWithinAtEntrywise_fin_two_iff`: the
  four entries of a `2 × 2` matrix.

Algebra of entrywise derivatives, each for `HasDerivAtEntrywise` and `HasDerivWithinAtEntrywise`
(the `Within` names are the same with `HasDerivWithinAtEntrywise` in place of
`HasDerivAtEntrywise`):
* `Matrix.hasDerivAtEntrywise_const`: a constant curve has derivative `0`;
* `add`, `sub`, `neg`, `add_const`, `const_add`, `sub_const`, `const_sub`, `sum`;
* `const_smul`: `(c • f)' = c • f'` for a constant scalar `c`;
* `smul`: `(c • f)' = c t • f' + c' • f t` for a scalar function `c` (with values in `ℝ`, `𝕜`,
  or any normed algebra acting on `𝕜`);
* `Matrix.hasDerivAtEntrywise_smul_const`, `Matrix.hasDerivWithinAtEntrywise_smul_const`:
  `(c • M)' = c' • M` for a scalar function `c` and a constant matrix `M`;
* `mul`: the product rule `(f * g)' = f' * g t + f t * g'`, and `mul_const`, `const_mul`
  (so `(P * f * Q)' = P * f' * Q` is `(hf.const_mul P).mul_const Q`);
* `transpose`;
* `scomp`: the chain rule `(f ∘ h)' = h' • f' (h t)` for a real function `h`;
* `mulVec`, `mulVec_const`, `vecMul`, `const_vecMul`: derivatives of `f s *ᵥ x s`, `f s *ᵥ v`,
  `x s ᵥ* f s`, `v ᵥ* f s` as `HasDerivAt` (or `HasDerivWithinAt`) of vector-valued functions
  (`m → 𝕜` carries the product topology; for finite `m` this is the sup norm topology);
* `trace`: `(tr f)' = tr f'` (a scalar `HasDerivAt`);
* `det_fin_two`: for `2 × 2` matrices,
  `(det f)' = f' 0 0 * f 1 1 + f 0 0 * f' 1 1 - (f' 0 1 * f 1 0 + f 0 1 * f' 1 0)`;
* `inv` (for `𝕜` complete, any size, `det (f t)` a unit): `(f⁻¹)' = -(f⁻¹ * f' * f⁻¹)`.

Comparison with `HasDerivAt` for the product topology on matrices (equivalently, for any norm on
matrices; apply with `exact`/`.1`/`.2` rather than `rw` under a local norm instance), for finite
column index type: `Matrix.hasDerivAtEntrywise_iff_hasDerivAt`,
`Matrix.hasDerivWithinAtEntrywise_iff_hasDerivWithinAt` and the aliases
`HasDerivAtEntrywise.hasDerivAt`, `HasDerivAt.hasDerivAtEntrywise`,
`HasDerivWithinAtEntrywise.hasDerivWithinAt`, `HasDerivWithinAt.hasDerivWithinAtEntrywise`.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace Matrix

variable {m n : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]

/-- The matrix-valued function `f` has derivative `f'` at `t`, entry by entry. -/
def HasDerivAtEntrywise (f : ℝ → Matrix m n 𝕜) (f' : Matrix m n 𝕜) (t : ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun s ↦ f s i j) (f' i j) t

/-- The matrix-valued function `f` has derivative `f'` at `t` within the set `s`, entry by
entry. -/
def HasDerivWithinAtEntrywise (f : ℝ → Matrix m n 𝕜) (f' : Matrix m n 𝕜) (s : Set ℝ) (t : ℝ) :
    Prop :=
  ∀ i j, HasDerivWithinAt (fun s ↦ f s i j) (f' i j) s t

/-- The entrywise derivative of a matrix-valued function (zero in the entries where the entry is
not differentiable, as for `deriv`). -/
noncomputable def derivEntrywise (f : ℝ → Matrix m n 𝕜) (t : ℝ) : Matrix m n 𝕜 :=
  Matrix.of fun i j ↦ deriv (fun s ↦ f s i j) t

/-- Every entry of the real matrix-valued function `f` is Lipschitz on `s`. -/
def LipschitzOnEntrywise (f : ℝ → Matrix m n ℝ) (s : Set ℝ) : Prop :=
  ∀ i j, ∃ C, LipschitzOnWith C (fun t ↦ f t i j) s

/-! ### Continuity, entry by entry -/

section Continuity

variable {X R : Type*} [TopologicalSpace X] [TopologicalSpace R] {f : X → Matrix m n R}
  {s : Set X} {x : X}

theorem continuousAt_iff_entrywise :
    ContinuousAt f x ↔ ∀ i j, ContinuousAt (fun y ↦ f y i j) x :=
  continuousAt_pi.trans <| forall_congr' fun _ ↦ continuousAt_pi

theorem continuousWithinAt_iff_entrywise :
    ContinuousWithinAt f s x ↔ ∀ i j, ContinuousWithinAt (fun y ↦ f y i j) s x :=
  continuousWithinAt_pi.trans <| forall_congr' fun _ ↦ continuousWithinAt_pi

theorem continuousOn_iff_entrywise :
    ContinuousOn f s ↔ ∀ i j, ContinuousOn (fun y ↦ f y i j) s :=
  continuousOn_pi.trans <| forall_congr' fun _ ↦ continuousOn_pi

theorem continuous_iff_entrywise : Continuous f ↔ ∀ i j, Continuous fun y ↦ f y i j :=
  continuous_pi_iff.trans <| forall_congr' fun _ ↦ continuous_pi_iff

end Continuity

/-! ### General facts -/

section General

variable {f g : ℝ → Matrix m n 𝕜} {f' g' : Matrix m n 𝕜} {s u : Set ℝ} {t : ℝ}

theorem HasDerivAtEntrywise.hasDerivWithinAtEntrywise (h : HasDerivAtEntrywise f f' t) :
    HasDerivWithinAtEntrywise f f' s t :=
  fun i j ↦ (h i j).hasDerivWithinAt

theorem HasDerivWithinAtEntrywise.hasDerivAtEntrywise (h : HasDerivWithinAtEntrywise f f' s t)
    (hs : s ∈ 𝓝 t) : HasDerivAtEntrywise f f' t :=
  fun i j ↦ (h i j).hasDerivAt hs

@[simp]
theorem hasDerivWithinAtEntrywise_univ :
    HasDerivWithinAtEntrywise f f' univ t ↔ HasDerivAtEntrywise f f' t :=
  forall_congr' fun _ ↦ forall_congr' fun _ ↦ hasDerivWithinAt_univ

theorem HasDerivWithinAtEntrywise.mono (h : HasDerivWithinAtEntrywise f f' s t) (hus : u ⊆ s) :
    HasDerivWithinAtEntrywise f f' u t :=
  fun i j ↦ (h i j).mono hus

theorem HasDerivWithinAtEntrywise.mono_of_mem_nhdsWithin (h : HasDerivWithinAtEntrywise f f' s t)
    (hs : s ∈ 𝓝[u] t) : HasDerivWithinAtEntrywise f f' u t :=
  fun i j ↦ (h i j).mono_of_mem_nhdsWithin hs

theorem HasDerivAtEntrywise.congr_of_eventuallyEq (h : HasDerivAtEntrywise f f' t)
    (hg : g =ᶠ[𝓝 t] f) : HasDerivAtEntrywise g f' t :=
  fun i j ↦ (h i j).congr_of_eventuallyEq (hg.mono fun _ hx ↦ congrArg (· i j) hx)

theorem HasDerivWithinAtEntrywise.congr_of_eventuallyEq (h : HasDerivWithinAtEntrywise f f' s t)
    (hg : g =ᶠ[𝓝[s] t] f) (ht : g t = f t) : HasDerivWithinAtEntrywise g f' s t :=
  fun i j ↦ (h i j).congr_of_eventuallyEq (hg.mono fun _ hx ↦ congrArg (· i j) hx)
    (congrArg (· i j) ht)

theorem HasDerivWithinAtEntrywise.congr (h : HasDerivWithinAtEntrywise f f' s t)
    (hs : ∀ x ∈ s, g x = f x) (ht : g t = f t) : HasDerivWithinAtEntrywise g f' s t :=
  fun i j ↦ (h i j).congr (fun x hx ↦ congrArg (· i j) (hs x hx)) (congrArg (· i j) ht)

theorem HasDerivWithinAtEntrywise.congr_of_mem (h : HasDerivWithinAtEntrywise f f' s t)
    (hs : ∀ x ∈ s, g x = f x) (ht : t ∈ s) : HasDerivWithinAtEntrywise g f' s t :=
  h.congr hs (hs t ht)

theorem HasDerivAtEntrywise.congr_deriv (h : HasDerivAtEntrywise f f' t) (h' : f' = g') :
    HasDerivAtEntrywise f g' t :=
  h' ▸ h

theorem HasDerivWithinAtEntrywise.congr_deriv (h : HasDerivWithinAtEntrywise f f' s t)
    (h' : f' = g') : HasDerivWithinAtEntrywise f g' s t :=
  h' ▸ h

/-- Entrywise derivatives are unique. -/
theorem HasDerivAtEntrywise.unique (h₀ : HasDerivAtEntrywise f f' t)
    (h₁ : HasDerivAtEntrywise f g' t) : f' = g' :=
  ext fun i j ↦ (h₀ i j).unique (h₁ i j)

/-- Entrywise derivatives within a set of unique differentiability are unique. -/
theorem HasDerivWithinAtEntrywise.unique (hs : UniqueDiffWithinAt ℝ s t)
    (h₀ : HasDerivWithinAtEntrywise f f' s t) (h₁ : HasDerivWithinAtEntrywise f g' s t) :
    f' = g' :=
  ext fun i j ↦ hs.eq_deriv s (h₀ i j) (h₁ i j)

theorem HasDerivAtEntrywise.derivEntrywise (h : HasDerivAtEntrywise f f' t) :
    derivEntrywise f t = f' :=
  ext fun i j ↦ (h i j).deriv

theorem HasDerivAtEntrywise.continuousAt (h : HasDerivAtEntrywise f f' t) : ContinuousAt f t :=
  continuousAt_iff_entrywise.2 fun i j ↦ (h i j).continuousAt

theorem HasDerivWithinAtEntrywise.continuousWithinAt (h : HasDerivWithinAtEntrywise f f' s t) :
    ContinuousWithinAt f s t :=
  continuousWithinAt_iff_entrywise.2 fun i j ↦ (h i j).continuousWithinAt

theorem HasDerivWithinAtEntrywise.continuousOn {F' : ℝ → Matrix m n 𝕜}
    (h : ∀ x ∈ s, HasDerivWithinAtEntrywise f (F' x) s x) : ContinuousOn f s :=
  fun x hx ↦ (h x hx).continuousWithinAt

/-- A curve of `2 × 2` matrices has an entrywise derivative iff its four entries do. -/
theorem hasDerivAtEntrywise_fin_two_iff {f : ℝ → Matrix (Fin 2) (Fin 2) 𝕜}
    {f' : Matrix (Fin 2) (Fin 2) 𝕜} :
    HasDerivAtEntrywise f f' t ↔
      HasDerivAt (fun s ↦ f s 0 0) (f' 0 0) t ∧ HasDerivAt (fun s ↦ f s 0 1) (f' 0 1) t ∧
        HasDerivAt (fun s ↦ f s 1 0) (f' 1 0) t ∧ HasDerivAt (fun s ↦ f s 1 1) (f' 1 1) t := by
  simp only [HasDerivAtEntrywise, Fin.forall_fin_two, and_assoc]

/-- A curve of `2 × 2` matrices has an entrywise derivative within `s` iff its four entries do. -/
theorem hasDerivWithinAtEntrywise_fin_two_iff {f : ℝ → Matrix (Fin 2) (Fin 2) 𝕜}
    {f' : Matrix (Fin 2) (Fin 2) 𝕜} :
    HasDerivWithinAtEntrywise f f' s t ↔
      HasDerivWithinAt (fun s ↦ f s 0 0) (f' 0 0) s t ∧
        HasDerivWithinAt (fun s ↦ f s 0 1) (f' 0 1) s t ∧
        HasDerivWithinAt (fun s ↦ f s 1 0) (f' 1 0) s t ∧
        HasDerivWithinAt (fun s ↦ f s 1 1) (f' 1 1) s t := by
  simp only [HasDerivWithinAtEntrywise, Fin.forall_fin_two, and_assoc]

end General

/-! ### Algebra of entrywise derivatives -/

section Algebra

variable {l p : Type*} {f g : ℝ → Matrix m n 𝕜} {f' g' : Matrix m n 𝕜} {s : Set ℝ} {t : ℝ}

theorem hasDerivAtEntrywise_const (c : Matrix m n 𝕜) (t : ℝ) :
    HasDerivAtEntrywise (fun _ ↦ c) 0 t :=
  fun _ _ ↦ hasDerivAt_const _ _

theorem hasDerivWithinAtEntrywise_const (c : Matrix m n 𝕜) (s : Set ℝ) (t : ℝ) :
    HasDerivWithinAtEntrywise (fun _ ↦ c) 0 s t :=
  fun _ _ ↦ hasDerivWithinAt_const _ _ _

theorem HasDerivAtEntrywise.add (hf : HasDerivAtEntrywise f f' t)
    (hg : HasDerivAtEntrywise g g' t) : HasDerivAtEntrywise (fun x ↦ f x + g x) (f' + g') t :=
  fun i j ↦ (hf i j).add (hg i j)

theorem HasDerivWithinAtEntrywise.add (hf : HasDerivWithinAtEntrywise f f' s t)
    (hg : HasDerivWithinAtEntrywise g g' s t) :
    HasDerivWithinAtEntrywise (fun x ↦ f x + g x) (f' + g') s t :=
  fun i j ↦ (hf i j).add (hg i j)

theorem HasDerivAtEntrywise.sub (hf : HasDerivAtEntrywise f f' t)
    (hg : HasDerivAtEntrywise g g' t) : HasDerivAtEntrywise (fun x ↦ f x - g x) (f' - g') t :=
  fun i j ↦ (hf i j).sub (hg i j)

theorem HasDerivWithinAtEntrywise.sub (hf : HasDerivWithinAtEntrywise f f' s t)
    (hg : HasDerivWithinAtEntrywise g g' s t) :
    HasDerivWithinAtEntrywise (fun x ↦ f x - g x) (f' - g') s t :=
  fun i j ↦ (hf i j).sub (hg i j)

theorem HasDerivAtEntrywise.neg (hf : HasDerivAtEntrywise f f' t) :
    HasDerivAtEntrywise (fun x ↦ -f x) (-f') t :=
  fun i j ↦ (hf i j).neg

theorem HasDerivWithinAtEntrywise.neg (hf : HasDerivWithinAtEntrywise f f' s t) :
    HasDerivWithinAtEntrywise (fun x ↦ -f x) (-f') s t :=
  fun i j ↦ (hf i j).neg

theorem HasDerivAtEntrywise.add_const (hf : HasDerivAtEntrywise f f' t) (c : Matrix m n 𝕜) :
    HasDerivAtEntrywise (fun x ↦ f x + c) f' t := by
  simpa using hf.add (hasDerivAtEntrywise_const c t)

theorem HasDerivWithinAtEntrywise.add_const (hf : HasDerivWithinAtEntrywise f f' s t)
    (c : Matrix m n 𝕜) : HasDerivWithinAtEntrywise (fun x ↦ f x + c) f' s t := by
  simpa using hf.add (hasDerivWithinAtEntrywise_const c s t)

theorem HasDerivAtEntrywise.const_add (c : Matrix m n 𝕜) (hf : HasDerivAtEntrywise f f' t) :
    HasDerivAtEntrywise (fun x ↦ c + f x) f' t := by
  simpa using (hasDerivAtEntrywise_const c t).add hf

theorem HasDerivWithinAtEntrywise.const_add (c : Matrix m n 𝕜)
    (hf : HasDerivWithinAtEntrywise f f' s t) :
    HasDerivWithinAtEntrywise (fun x ↦ c + f x) f' s t := by
  simpa using (hasDerivWithinAtEntrywise_const c s t).add hf

theorem HasDerivAtEntrywise.sub_const (hf : HasDerivAtEntrywise f f' t) (c : Matrix m n 𝕜) :
    HasDerivAtEntrywise (fun x ↦ f x - c) f' t := by
  simpa using hf.sub (hasDerivAtEntrywise_const c t)

theorem HasDerivWithinAtEntrywise.sub_const (hf : HasDerivWithinAtEntrywise f f' s t)
    (c : Matrix m n 𝕜) : HasDerivWithinAtEntrywise (fun x ↦ f x - c) f' s t := by
  simpa using hf.sub (hasDerivWithinAtEntrywise_const c s t)

theorem HasDerivAtEntrywise.const_sub (c : Matrix m n 𝕜) (hf : HasDerivAtEntrywise f f' t) :
    HasDerivAtEntrywise (fun x ↦ c - f x) (-f') t := by
  simpa using (hasDerivAtEntrywise_const c t).sub hf

theorem HasDerivWithinAtEntrywise.const_sub (c : Matrix m n 𝕜)
    (hf : HasDerivWithinAtEntrywise f f' s t) :
    HasDerivWithinAtEntrywise (fun x ↦ c - f x) (-f') s t := by
  simpa using (hasDerivWithinAtEntrywise_const c s t).sub hf

theorem HasDerivAtEntrywise.sum {ι : Type*} {u : Finset ι} {F : ι → ℝ → Matrix m n 𝕜}
    {F' : ι → Matrix m n 𝕜} (h : ∀ k ∈ u, HasDerivAtEntrywise (F k) (F' k) t) :
    HasDerivAtEntrywise (fun x ↦ ∑ k ∈ u, F k x) (∑ k ∈ u, F' k) t := by
  intro i j
  simpa only [Matrix.sum_apply] using HasDerivAt.fun_sum fun k hk ↦ h k hk i j

theorem HasDerivWithinAtEntrywise.sum {ι : Type*} {u : Finset ι} {F : ι → ℝ → Matrix m n 𝕜}
    {F' : ι → Matrix m n 𝕜} (h : ∀ k ∈ u, HasDerivWithinAtEntrywise (F k) (F' k) s t) :
    HasDerivWithinAtEntrywise (fun x ↦ ∑ k ∈ u, F k x) (∑ k ∈ u, F' k) s t := by
  intro i j
  simpa only [Matrix.sum_apply] using HasDerivWithinAt.fun_sum fun k hk ↦ h k hk i j

section SMul

variable {R : Type*} [Semiring R] [Module R 𝕜] [SMulCommClass ℝ R 𝕜] [ContinuousConstSMul R 𝕜]

/-- Derivative of a constant scalar times a matrix curve. -/
theorem HasDerivAtEntrywise.const_smul (c : R) (hf : HasDerivAtEntrywise f f' t) :
    HasDerivAtEntrywise (fun x ↦ c • f x) (c • f') t :=
  fun i j ↦ (hf i j).fun_const_smul c

/-- Derivative of a constant scalar times a matrix curve. -/
theorem HasDerivWithinAtEntrywise.const_smul (c : R) (hf : HasDerivWithinAtEntrywise f f' s t) :
    HasDerivWithinAtEntrywise (fun x ↦ c • f x) (c • f') s t :=
  fun i j ↦ (hf i j).fun_const_smul c

end SMul

section SMulFun

variable {𝕜' : Type*} [NormedRing 𝕜'] [NormedAlgebra ℝ 𝕜'] [Module 𝕜' 𝕜] [IsBoundedSMul 𝕜' 𝕜]
  [IsScalarTower ℝ 𝕜' 𝕜] {c : ℝ → 𝕜'} {c' : 𝕜'}

/-- Derivative of a scalar function times a matrix curve: `(c • f)' = c t • f' + c' • f t`. -/
theorem HasDerivAtEntrywise.smul (hc : HasDerivAt c c' t) (hf : HasDerivAtEntrywise f f' t) :
    HasDerivAtEntrywise (fun x ↦ c x • f x) (c t • f' + c' • f t) t :=
  fun i j ↦ hc.fun_smul (hf i j)

/-- Derivative of a scalar function times a matrix curve: `(c • f)' = c t • f' + c' • f t`. -/
theorem HasDerivWithinAtEntrywise.smul (hc : HasDerivWithinAt c c' s t)
    (hf : HasDerivWithinAtEntrywise f f' s t) :
    HasDerivWithinAtEntrywise (fun x ↦ c x • f x) (c t • f' + c' • f t) s t :=
  fun i j ↦ hc.fun_smul (hf i j)

/-- Derivative of a scalar function times a constant matrix. -/
theorem hasDerivAtEntrywise_smul_const (hc : HasDerivAt c c' t) (M : Matrix m n 𝕜) :
    HasDerivAtEntrywise (fun x ↦ c x • M) (c' • M) t :=
  fun i j ↦ hc.smul_const (M i j)

/-- Derivative of a scalar function times a constant matrix. -/
theorem hasDerivWithinAtEntrywise_smul_const (hc : HasDerivWithinAt c c' s t)
    (M : Matrix m n 𝕜) : HasDerivWithinAtEntrywise (fun x ↦ c x • M) (c' • M) s t :=
  fun i j ↦ hc.smul_const (M i j)

end SMulFun

/-- The product rule for matrix products: `(f * g)' = f' * g t + f t * g'`. -/
theorem HasDerivAtEntrywise.mul [Fintype n] {g : ℝ → Matrix n p 𝕜} {g' : Matrix n p 𝕜}
    (hf : HasDerivAtEntrywise f f' t) (hg : HasDerivAtEntrywise g g' t) :
    HasDerivAtEntrywise (fun x ↦ f x * g x) (f' * g t + f t * g') t := by
  intro i j
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using
    HasDerivAt.fun_sum (u := Finset.univ) fun k _ ↦ (hf i k).fun_mul (hg k j)

/-- The product rule for matrix products: `(f * g)' = f' * g t + f t * g'`. -/
theorem HasDerivWithinAtEntrywise.mul [Fintype n] {g : ℝ → Matrix n p 𝕜} {g' : Matrix n p 𝕜}
    (hf : HasDerivWithinAtEntrywise f f' s t) (hg : HasDerivWithinAtEntrywise g g' s t) :
    HasDerivWithinAtEntrywise (fun x ↦ f x * g x) (f' * g t + f t * g') s t := by
  intro i j
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using
    HasDerivWithinAt.fun_sum (u := Finset.univ) fun k _ ↦ (hf i k).fun_mul (hg k j)

theorem HasDerivAtEntrywise.mul_const [Fintype n] (hf : HasDerivAtEntrywise f f' t)
    (B : Matrix n p 𝕜) : HasDerivAtEntrywise (fun x ↦ f x * B) (f' * B) t := by
  simpa using hf.mul (hasDerivAtEntrywise_const B t)

theorem HasDerivWithinAtEntrywise.mul_const [Fintype n] (hf : HasDerivWithinAtEntrywise f f' s t)
    (B : Matrix n p 𝕜) : HasDerivWithinAtEntrywise (fun x ↦ f x * B) (f' * B) s t := by
  simpa using hf.mul (hasDerivWithinAtEntrywise_const B s t)

theorem HasDerivAtEntrywise.const_mul [Fintype m] (A : Matrix l m 𝕜)
    (hf : HasDerivAtEntrywise f f' t) : HasDerivAtEntrywise (fun x ↦ A * f x) (A * f') t := by
  simpa using (hasDerivAtEntrywise_const A t).mul hf

theorem HasDerivWithinAtEntrywise.const_mul [Fintype m] (A : Matrix l m 𝕜)
    (hf : HasDerivWithinAtEntrywise f f' s t) :
    HasDerivWithinAtEntrywise (fun x ↦ A * f x) (A * f') s t := by
  simpa using (hasDerivWithinAtEntrywise_const A s t).mul hf

theorem HasDerivAtEntrywise.transpose (hf : HasDerivAtEntrywise f f' t) :
    HasDerivAtEntrywise (fun x ↦ (f x)ᵀ) f'ᵀ t :=
  fun i j ↦ hf j i

theorem HasDerivWithinAtEntrywise.transpose (hf : HasDerivWithinAtEntrywise f f' s t) :
    HasDerivWithinAtEntrywise (fun x ↦ (f x)ᵀ) f'ᵀ s t :=
  fun i j ↦ hf j i

/-- The chain rule for a reparametrization `f ∘ h` of a matrix curve. -/
theorem HasDerivAtEntrywise.scomp {h : ℝ → ℝ} {h' : ℝ} (hf : HasDerivAtEntrywise f f' (h t))
    (hh : HasDerivAt h h' t) : HasDerivAtEntrywise (fun x ↦ f (h x)) (h' • f') t :=
  fun i j ↦ (hf i j).scomp t hh

/-- The chain rule for a reparametrization `f ∘ h` of a matrix curve. -/
theorem HasDerivWithinAtEntrywise.scomp {h : ℝ → ℝ} {h' : ℝ} {s' : Set ℝ}
    (hf : HasDerivWithinAtEntrywise f f' s' (h t)) (hh : HasDerivWithinAt h h' s t)
    (hst : MapsTo h s s') : HasDerivWithinAtEntrywise (fun x ↦ f (h x)) (h' • f') s t :=
  fun i j ↦ (hf i j).scomp t hh hst

section MulVec

/-- Derivative of a matrix curve applied to a vector curve (vectors carry the sup norm). -/
theorem HasDerivAtEntrywise.mulVec [Fintype n] {x : ℝ → n → 𝕜} {x' : n → 𝕜}
    (hf : HasDerivAtEntrywise f f' t) (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s ↦ f s *ᵥ x s) (f' *ᵥ x t + f t *ᵥ x') t := by
  refine hasDerivAt_pi.2 fun i ↦ ?_
  simpa only [Matrix.mulVec, dotProduct, Pi.add_apply, Finset.sum_add_distrib] using
    HasDerivAt.fun_sum (u := Finset.univ) fun k _ ↦ (hf i k).fun_mul (hasDerivAt_pi.1 hx k)

/-- Derivative of a matrix curve applied to a vector curve (vectors carry the sup norm). -/
theorem HasDerivWithinAtEntrywise.mulVec [Fintype n] {x : ℝ → n → 𝕜} {x' : n → 𝕜}
    (hf : HasDerivWithinAtEntrywise f f' s t) (hx : HasDerivWithinAt x x' s t) :
    HasDerivWithinAt (fun s ↦ f s *ᵥ x s) (f' *ᵥ x t + f t *ᵥ x') s t := by
  refine hasDerivWithinAt_pi.2 fun i ↦ ?_
  simpa only [Matrix.mulVec, dotProduct, Pi.add_apply, Finset.sum_add_distrib] using
    HasDerivWithinAt.fun_sum (u := Finset.univ) fun k _ ↦
      (hf i k).fun_mul (hasDerivWithinAt_pi.1 hx k)

/-- Derivative of a matrix curve applied to a fixed vector (vectors carry the sup norm). -/
theorem HasDerivAtEntrywise.mulVec_const [Fintype n] (hf : HasDerivAtEntrywise f f' t) (v : n → 𝕜) :
    HasDerivAt (fun s ↦ f s *ᵥ v) (f' *ᵥ v) t := by
  simpa using hf.mulVec (hasDerivAt_const t v)

/-- Derivative of a matrix curve applied to a fixed vector (vectors carry the sup norm). -/
theorem HasDerivWithinAtEntrywise.mulVec_const [Fintype n] (hf : HasDerivWithinAtEntrywise f f' s t)
    (v : n → 𝕜) : HasDerivWithinAt (fun s ↦ f s *ᵥ v) (f' *ᵥ v) s t := by
  simpa using hf.mulVec (hasDerivWithinAt_const t s v)

/-- Derivative of a vector curve times a matrix curve (vectors carry the sup norm). -/
theorem HasDerivAtEntrywise.vecMul [Fintype m] {x : ℝ → m → 𝕜} {x' : m → 𝕜} (hx : HasDerivAt x x' t)
    (hf : HasDerivAtEntrywise f f' t) :
    HasDerivAt (fun s ↦ x s ᵥ* f s) (x' ᵥ* f t + x t ᵥ* f') t := by
  refine hasDerivAt_pi.2 fun j ↦ ?_
  simpa only [Matrix.vecMul, dotProduct, Pi.add_apply, Finset.sum_add_distrib] using
    HasDerivAt.fun_sum (u := Finset.univ) fun k _ ↦ (hasDerivAt_pi.1 hx k).fun_mul (hf k j)

/-- Derivative of a vector curve times a matrix curve (vectors carry the sup norm). -/
theorem HasDerivWithinAtEntrywise.vecMul [Fintype m] {x : ℝ → m → 𝕜} {x' : m → 𝕜}
    (hx : HasDerivWithinAt x x' s t) (hf : HasDerivWithinAtEntrywise f f' s t) :
    HasDerivWithinAt (fun s ↦ x s ᵥ* f s) (x' ᵥ* f t + x t ᵥ* f') s t := by
  refine hasDerivWithinAt_pi.2 fun j ↦ ?_
  simpa only [Matrix.vecMul, dotProduct, Pi.add_apply, Finset.sum_add_distrib] using
    HasDerivWithinAt.fun_sum (u := Finset.univ) fun k _ ↦
      (hasDerivWithinAt_pi.1 hx k).fun_mul (hf k j)

/-- Derivative of a fixed vector times a matrix curve (vectors carry the sup norm). -/
theorem HasDerivAtEntrywise.const_vecMul [Fintype m] (v : m → 𝕜) (hf : HasDerivAtEntrywise f f' t) :
    HasDerivAt (fun s ↦ v ᵥ* f s) (v ᵥ* f') t := by
  simpa using HasDerivAtEntrywise.vecMul (hasDerivAt_const t v) hf

/-- Derivative of a fixed vector times a matrix curve (vectors carry the sup norm). -/
theorem HasDerivWithinAtEntrywise.const_vecMul [Fintype m] (v : m → 𝕜)
    (hf : HasDerivWithinAtEntrywise f f' s t) :
    HasDerivWithinAt (fun s ↦ v ᵥ* f s) (v ᵥ* f') s t := by
  simpa using HasDerivWithinAtEntrywise.vecMul (hasDerivWithinAt_const t s v) hf

end MulVec

section Square

variable {f : ℝ → Matrix n n 𝕜} {f' : Matrix n n 𝕜}

/-- The derivative of the trace is the trace of the derivative. -/
theorem HasDerivAtEntrywise.trace [Fintype n] (hf : HasDerivAtEntrywise f f' t) :
    HasDerivAt (fun x ↦ (f x).trace) f'.trace t := by
  simpa only [Matrix.trace, Matrix.diag_apply] using
    HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hf i i

/-- The derivative of the trace is the trace of the derivative. -/
theorem HasDerivWithinAtEntrywise.trace [Fintype n] (hf : HasDerivWithinAtEntrywise f f' s t) :
    HasDerivWithinAt (fun x ↦ (f x).trace) f'.trace s t := by
  simpa only [Matrix.trace, Matrix.diag_apply] using
    HasDerivWithinAt.fun_sum (u := Finset.univ) fun i _ ↦ hf i i

end Square

section FinTwo

variable {f : ℝ → Matrix (Fin 2) (Fin 2) 𝕜} {f' : Matrix (Fin 2) (Fin 2) 𝕜}

/-- The derivative of the determinant of a `2 × 2` matrix curve. -/
theorem HasDerivAtEntrywise.det_fin_two (hf : HasDerivAtEntrywise f f' t) :
    HasDerivAt (fun x ↦ (f x).det)
      (f' 0 0 * f t 1 1 + f t 0 0 * f' 1 1 - (f' 0 1 * f t 1 0 + f t 0 1 * f' 1 0)) t := by
  simpa only [Matrix.det_fin_two] using
    ((hf 0 0).fun_mul (hf 1 1)).fun_sub ((hf 0 1).fun_mul (hf 1 0))

/-- The derivative of the determinant of a `2 × 2` matrix curve. -/
theorem HasDerivWithinAtEntrywise.det_fin_two (hf : HasDerivWithinAtEntrywise f f' s t) :
    HasDerivWithinAt (fun x ↦ (f x).det)
      (f' 0 0 * f t 1 1 + f t 0 0 * f' 1 1 - (f' 0 1 * f t 1 0 + f t 0 1 * f' 1 0)) s t := by
  simpa only [Matrix.det_fin_two] using
    ((hf 0 0).fun_mul (hf 1 1)).fun_sub ((hf 0 1).fun_mul (hf 1 0))

end FinTwo

end Algebra

/-! ### Comparison with `HasDerivAt` for matrix-valued functions

In Mathlib, `HasDerivAt` is defined for functions with values in a topological vector space, so
it makes sense for `f : ℝ → Matrix m n 𝕜` with the product topology, without choosing a norm.
For any of the (equivalent) norms on matrices, e.g. with `open scoped Matrix.Norms.Operator`, the
resulting `HasDerivAt` agrees with this one up to unfolding of the instances, so the lemmas below
also apply there (with `exact` or `.1`/`.2`, not with `rw`). -/

section TVS

variable [Finite n] {f : ℝ → Matrix m n 𝕜} {f' : Matrix m n 𝕜} {s : Set ℝ} {t : ℝ}

/-- An entrywise derivative within a set is the same as a derivative within that set for the
product topology on matrices. -/
theorem hasDerivWithinAtEntrywise_iff_hasDerivWithinAt :
    HasDerivWithinAtEntrywise f f' s t ↔ HasDerivWithinAt f f' s t :=
  have := Fintype.ofFinite n
  (hasDerivWithinAt_pi.trans (forall_congr' fun _ ↦ hasDerivWithinAt_pi)).symm

/-- An entrywise derivative is the same as a derivative for the product topology on
matrices. -/
theorem hasDerivAtEntrywise_iff_hasDerivAt :
    HasDerivAtEntrywise f f' t ↔ HasDerivAt f f' t :=
  have := Fintype.ofFinite n
  (hasDerivAt_pi.trans (forall_congr' fun _ ↦ hasDerivAt_pi)).symm

alias ⟨HasDerivWithinAtEntrywise.hasDerivWithinAt,
  _root_.HasDerivWithinAt.hasDerivWithinAtEntrywise⟩ :=
  hasDerivWithinAtEntrywise_iff_hasDerivWithinAt

alias ⟨HasDerivAtEntrywise.hasDerivAt, _root_.HasDerivAt.hasDerivAtEntrywise⟩ :=
  hasDerivAtEntrywise_iff_hasDerivAt

end TVS

/-! ### Derivative of the inverse -/

section Inverse

variable [Fintype n] [DecidableEq n] [CompleteSpace 𝕜] {f : ℝ → Matrix n n 𝕜}
  {f' : Matrix n n 𝕜} {s : Set ℝ} {t : ℝ}

/-- The derivative of the inverse of an invertible matrix curve: `(f⁻¹)' = -(f⁻¹ * f' * f⁻¹)`. -/
theorem HasDerivWithinAtEntrywise.inv (hf : HasDerivWithinAtEntrywise f f' s t)
    (hdet : IsUnit (f t).det) :
    HasDerivWithinAtEntrywise (fun x ↦ (f x)⁻¹) (-((f t)⁻¹ * f' * (f t)⁻¹)) s t := by
  open scoped Matrix.Norms.Operator in
  -- the uniform structure of the operator norm is the product one, but only up to unfolding
  have : @CompleteSpace (Matrix n n 𝕜) PseudoMetricSpace.toUniformSpace := by
    exact inferInstanceAs (CompleteSpace (Matrix n n 𝕜))
  obtain ⟨u, hu⟩ := (isUnit_iff_isUnit_det (f t)).2 hdet
  have hl : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n 𝕜) (f t)⁻¹ (f t)⁻¹) (f t) := by
    simpa only [coe_units_inv, hu] using hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have h := hl.comp_hasDerivWithinAt t hf.hasDerivWithinAt
  have e : (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n 𝕜) (f t)⁻¹ (f t)⁻¹) f' =
      -((f t)⁻¹ * f' * (f t)⁻¹) := rfl
  simp only [Function.comp_def, ← nonsing_inv_eq_ringInverse, e] at h
  exact h.hasDerivWithinAtEntrywise

/-- The derivative of the inverse of an invertible matrix curve: `(f⁻¹)' = -(f⁻¹ * f' * f⁻¹)`. -/
theorem HasDerivAtEntrywise.inv (hf : HasDerivAtEntrywise f f' t) (hdet : IsUnit (f t).det) :
    HasDerivAtEntrywise (fun x ↦ (f x)⁻¹) (-((f t)⁻¹ * f' * (f t)⁻¹)) t :=
  hasDerivWithinAtEntrywise_univ.1 (hf.hasDerivWithinAtEntrywise.inv hdet)

end Inverse

end Matrix
