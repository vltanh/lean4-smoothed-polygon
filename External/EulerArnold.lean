module

public import Basic.Analysis.Calculus.MatrixEntrywise
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The Euler–Arnold equation for left-invariant Hamiltonians on matrix groups

Cited in the proof of Proposition 6.5.1 of Hales–Vajjha, *Packings of Smoothed Polygons*, from
R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, Birkhäuser, 1997:
for a left-invariant Hamiltonian on the cotangent bundle of a Lie group `G`, the left-trivialized
momentum `μ ∈ 𝔤*` of a solution of Hamilton's equations satisfies the Euler–Arnold equation
`μ' = ad*_{δh/δμ} μ`.

Here `G` is an open subgroup of `GL_n(ℝ)` inside `Matrix n n ℝ`, with canonical coordinates
`(g, p)` on `T*G = G × Matrix n n ℝ`, the covector `p` acting on a tangent vector `v` by `tr(p v)`.
Gradients are taken for the same pairing: `D` is the gradient of `F` at `A` if
`d/ds F(A + sW)|₀ = tr(D W)` for every `W`. Hamilton's equations for `H(g, p)` read
`g' = ∂H/∂p`, `p' = -∂H/∂g`. A Hamiltonian `H(g, p) = h(p g)` is left-invariant
(`H(kg, p k⁻¹) = H(g, p)`), and `μ = p g` is its left-trivialized momentum (`tr(p · g W) = tr(μ W)`
for `W` in the Lie algebra). The Euler–Arnold equation is then `μ' = μ D - D μ` with `D = δh/δμ`,
which is `ad*_D μ` when `𝔤*` is identified with matrices by the trace pairing.
-/

@[expose] public section

namespace External

open Matrix

variable {n : Type*} [Fintype n]

/-- `D` is the gradient of `F` at `A` for the trace pairing: the directional derivative of `F` at
`A` in every direction `W` exists and equals `tr(D W)`. -/
def HasTraceGradient (F : Matrix n n ℝ → ℝ) (A D : Matrix n n ℝ) : Prop :=
  ∀ W : Matrix n n ℝ, HasDerivAt (fun s : ℝ ↦ F (A + s • W)) (D * W).trace 0

/-- The gradient for the trace pairing is unique: the pairing `(D, W) ↦ tr(D W)` is
nondegenerate. -/
theorem HasTraceGradient.unique {F : Matrix n n ℝ → ℝ} {A D D' : Matrix n n ℝ}
    (h : HasTraceGradient F A D) (h' : HasTraceGradient F A D') : D = D' := by
  classical
  have key : ∀ W : Matrix n n ℝ, (D * W).trace = (D' * W).trace := fun W ↦
    (h W).unique (h' W)
  ext i j
  simpa [Matrix.trace_mul_single] using key (Matrix.single j i 1)

/-- The gradient of `q ↦ h(q k)` at `p` is `k D`, where `D` is the gradient of `h` at `p k`. -/
theorem HasTraceGradient.comp_mul_right {h : Matrix n n ℝ → ℝ} {p k D : Matrix n n ℝ}
    (hD : HasTraceGradient h (p * k) D) : HasTraceGradient (fun q ↦ h (q * k)) p (k * D) := by
  intro W
  have e : (fun s : ℝ ↦ h ((p + s • W) * k)) = fun s ↦ h (p * k + s • (W * k)) := by
    funext s
    rw [Matrix.add_mul, Matrix.smul_mul]
  rw [e, Matrix.mul_assoc, Matrix.trace_mul_comm k]
  simpa [Matrix.mul_assoc] using hD (W * k)

/-- The gradient of `k ↦ h(p k)` at `g` is `D p`, where `D` is the gradient of `h` at `p g`. -/
theorem HasTraceGradient.comp_mul_left {h : Matrix n n ℝ → ℝ} {p g D : Matrix n n ℝ}
    (hD : HasTraceGradient h (p * g) D) : HasTraceGradient (fun k ↦ h (p * k)) g (D * p) := by
  intro W
  have e : (fun s : ℝ ↦ h (p * (g + s • W))) = fun s ↦ h (p * g + s • (p * W)) := by
    funext s
    rw [Matrix.mul_add, Matrix.mul_smul]
  rw [e, Matrix.mul_assoc]
  exact hD (p * W)

/-- **The Euler–Arnold equation** (Cushman–Bates). Let `H(g, p) = h(p g)` be a left-invariant
Hamiltonian on `T*G`, `G ⊆ GL_n(ℝ)`, and let `(g, p)` satisfy Hamilton's equations
`g' = ∂H/∂p`, `p' = -∂H/∂g` at time `t`. If `h` has gradient `D` at `μ(t) = p(t) g(t)`, then the
left-trivialized momentum `μ = p g` satisfies `μ' = μ D - D μ` at `t`. -/
theorem euler_arnold (h : Matrix n n ℝ → ℝ) (g p : ℝ → Matrix n n ℝ) (t : ℝ)
    (g' p' D : Matrix n n ℝ) (hg : HasDerivAtEntrywise g g' t) (hp : HasDerivAtEntrywise p p' t)
    (hD : HasTraceGradient h (p t * g t) D)
    (hHp : HasTraceGradient (fun q ↦ h (q * g t)) (p t) g')
    (hHg : HasTraceGradient (fun k ↦ h (p t * k)) (g t) (-p')) :
    HasDerivAtEntrywise (fun s ↦ p s * g s) (p t * g t * D - D * (p t * g t)) t := by
  have hg' : g' = g t * D := hHp.unique hD.comp_mul_right
  have hp' : p' = -(D * p t) := by
    rw [← neg_neg p', hHg.unique hD.comp_mul_left]
  refine (hp.mul hg).congr_deriv ?_
  rw [hg', hp']
  noncomm_ring

end External
