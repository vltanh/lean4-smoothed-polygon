module

public import SmoothedPolygons.Ch6.Existence
public import SmoothedPolygons.Ch2.Boundary
public import SmoothedPolygons.Ch2.Density

/-!
# The minimizer of the control problem and Reinhardt's `K_min`

§6.1 says (TeX 4569–4572) "Recall that Reinhardt has proved the existence of an optimal solution to
the Reinhardt problem", and the later chapters identify the global minimizer of the control
problem with Reinhardt's minimizer `K_min` (a centrally symmetric convex disk of least greatest
packing density, `IsWorstDisk`): Proposition 8.1.3 speaks of "the global solution of the
Reinhardt problem" (TeX 6786), and Theorem 16.3.1 (`thm:mahler`, TeX 12789–12795) concludes from
"the global minimizer of the Reinhardt optimal control problem is a bang-bang solution with
finitely many switches" that "the minimizer `K_min` of the Reinhardt problem is a finite-sided
smoothed polygon". The book does not prove the identification; Chapters 2–3 derive the control
problem from `K_min` (Problem 3.6.2: "The convex disks in `𝔎_bal` in circle representation arise
via the following optimal control problem"). Inventory, Part I §3.5, item 5.

What the later chapters need:

* `exists_isReinhardtMinimizer_of_isWorstDisk`: after a linear normalization, every `K_min` is the
  disk of a global minimizer of Problem 3.6.2 (so the second sentence of Theorem 16.3.1 follows
  from the first);
* `isWorstDisk_of_isReinhardtMinimizer`: conversely, the disk bounded by a global minimizer is a
  `K_min`, and `δ_min = cost/√12`.

Both rest on `exists_isReinhardtAdmissible_of_isWorstDisk` (the inventory's step B1): every
`K_min`, after a linear normalization, is a balanced disk in circle representation whose boundary
trajectory, parameterized with `det X = 1`, is admissible.

## Proofs (to be written)

* `exists_isReinhardtAdmissible_of_isWorstDisk` (B1), assembling the formalized results of
  Chapters 2–3, each of which takes the multi-curve as a hypothesis: Reinhardt's existence of
  `K_min` and its continuous multi-curve of critical-hexagon midpoints (Lemma 2.2.7, `lemma2_2_7`);
  the linear normalization to circle representation (worst disks and critical hexagons are
  invariant under orientation-preserving linear maps, `bdy_isWorstLatticeDisk_image`,
  `bdy_isLeastAreaHexagon_image`); regularity and Lipschitz tangents (Lemmas 2.4.2, 2.4.3,
  Corollary 2.4.4); the star and curvature conditions (Lemmas 2.4.5, 2.4.6), so `(K, σ)` is a
  balanced pair; `X = g⁻¹g'` (Theorem 3.1.4) satisfies the star inequalities (Corollary 3.1.6), and
  the reparameterization with `det X = 1` is Lipschitz (Proposition 3.1.9); the control `u` with
  `X' = [Z_u, X]/⟨Z_u, X⟩` (Lemma 3.3.1, Theorem 3.4.2); the boundary conditions `g(0) = I`,
  `g(t_f) = R`, `X(t_f) = R⁻¹X(0)R` (§3.5); the area formula `eqn_cost`. Size: 1,000–2,500 lines;
  it may be split (normalization and balanced pair; the control and the boundary conditions).
* `exists_isReinhardtMinimizer_of_isWorstDisk`: the trajectory of B1 is admissible with cost
  `area(K) = √12 δ_min` (E12, `greatestPackingDensity_of_isBalancedPair`; `δ` is invariant under
  linear maps); a competitor cheaper than the smoothed octagon bounds a balanced disk of area its
  cost (`isWindingOne_of_reinhardtCost_lt`, `exists_isBalancedPair_of_isReinhardtAdmissible`), whose
  density is at least `δ_min`; and `δ_min ≤ δ_oct`. Size: 150–300 lines.
* `isWorstDisk_of_isReinhardtMinimizer`: `area(K) = cost = min ≤ √12 δ_min` by comparison with the
  trajectory of a `K_min` (`rein_exists_worst`, `ch2_isWorstLatticeDisk_iff_isWorstDisk`, B1), and
  `δ(K) = area(K)/√12 ≥ δ_min`. Size: 100–200 lines.

This module is the bridge to Chapters 8 and 16 (Layer 3); it does not enter the existence proof.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix

/-- **Step B1: a worst disk gives an admissible trajectory.** For every `K_min` (a centrally
symmetric convex disk of least greatest packing density), some linear image `A K_min`,
`det A > 0`, is a balanced disk in circle representation whose multi-curve `σ_j = g s_j*`, with
`σ_j(t + t_f) = σ_{j+1}(t)`, comes from an admissible trajectory `(g, X)` of Problem 3.6.2 of cost
`area(A K_min)` (Chapters 2–3; Problem 3.6.2, "The convex disks in `𝔎_bal` in circle
representation arise via the following optimal control problem"). -/
theorem exists_isReinhardtAdmissible_of_isWorstDisk {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) :
    ∃ (A : Mat2) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2),
      0 < A.det ∧ IsBalancedPair ((fun v ↦ A *ᵥ v) '' K) σ T ∧ IsCircleRepresentation σ ∧
      (∀ j t, σ j t = g t *ᵥ sixthRoot j) ∧ (∀ j t, σ j (t + T) = σ (j + 1) t) ∧
      IsReinhardtAdmissible T u g X ∧
      volume ((fun v ↦ A *ᵥ v) '' K) = ENNReal.ofReal (reinhardtCost T X) := by
  sorry

/-- **Every `K_min` is the disk of a global minimizer of the control problem**
(`sec:existence-opt-control:kmin`, label of this formalization; the identification
used by Theorem 16.3.1, TeX 12793–12795, and by Proposition 8.1.3, TeX 6786): some linear image
`A K_min`, `det A > 0`, is a balanced disk in circle representation whose boundary trajectory is a
global minimizer of Problem 3.6.2. -/
theorem exists_isReinhardtMinimizer_of_isWorstDisk {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) :
    ∃ (A : Mat2) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2),
      0 < A.det ∧ IsBalancedPair ((fun v ↦ A *ᵥ v) '' K) σ T ∧ IsCircleRepresentation σ ∧
      (∀ j t, σ j t = g t *ᵥ sixthRoot j) ∧ (∀ j t, σ j (t + T) = σ (j + 1) t) ∧
      IsReinhardtMinimizer T u g X := by
  sorry

/-- **The disk of a global minimizer is a `K_min`** (`sec:existence-opt-control:kmin`, label of this
formalization; TeX 4569–4572): if `(g, X)` is a global
minimizer of Problem 3.6.2 on `[0, T]` and `(K, σ)` a balanced pair in circle representation with
`σ_j = g s_j*` on `[0, T]` and `σ_j(t + T) = σ_{j+1}(t)`, then `K` is a centrally symmetric convex
disk of least greatest packing density, and `δ_min = cost/√12`. -/
theorem isWorstDisk_of_isReinhardtMinimizer {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtMinimizer T u g X) {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hKσ : IsBalancedPair K σ T) (hcirc : IsCircleRepresentation σ)
    (hg : ∀ j, ∀ t ∈ Icc 0 T, σ j t = g t *ᵥ sixthRoot j)
    (hshift : ∀ j t, σ j (t + T) = σ (j + 1) t) :
    IsWorstDisk K ∧ minimaxDensity = reinhardtCost T X / √12 := by
  sorry

end SmoothedPolygons
