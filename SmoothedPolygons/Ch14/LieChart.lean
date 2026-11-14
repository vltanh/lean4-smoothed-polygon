module

public import SmoothedPolygons.Ch7.Isolated.Defs
public import SmoothedPolygons.Ch8.Defs
public import SmoothedPolygons.Ch13.FixedPoints

/-!
# Chapter 14: Lie algebra coordinates and hyperboloid coordinates near the singular locus (§14.1)

§14.1 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Lie Algebra Coordinates",
TeX 11500–11602), with the coordinates of Chapters 10–11 that Chapters 14 and 16 use to compare the
Reinhardt system near the singular locus with the Fuller system.

The setting is the normalized one of Chapters 11–16 (TeX 11484–11486, 12856–12858): `λ_cost = -1`,
`d₁ = 3/2` (`det Λ₁ = 9/4`), `ε = 1`, `ρ = 2` (triangular control). A phase point is a triple
`q = (X, Λ₁, Λ_R)` (`iso_PhasePt`); the extremal flow with a vertex control `e_m` is the closed form
`iso_vertexFlow m` of Chapter 7 (`λ_cost = -1`); the switching functions are
`switchingFn i j Λ_R X = χ_ij` (`χ_ij = H(e_i) - H(e_j)`; indices `0, 1, 2` for `e₁, e₂, e₃`).
At the singular locus `q = (J, -(3/2) J, 0)` (Definition 8.2.4 with `λ_cost = -1`).

## Contents

* **The Lie algebra chart** (14.1.1)–(14.1.3): `X = J + r X̃`, `Λ₁ = -(3/2) J + r² Λ̃₁`,
  `Λ_R = r³ Λ̃_R` with `x̃₁₁ = 1`, in the coordinates `(r, x̃)`, `x̃ = (x̃₂₁, ℓ̃₁₁, ℓ̃₂₁)`:
  `lieX` (the displayed matrix at TeX 11582, which is `X`, not `X̃`: REPORT.md, E81), `lieΛ₁` (from
  `det Λ₁ = 9/4`, `tr Λ₁ = 0`), `lieΛR` (the solution of the linear system (14.1.3)
  `⟨X, Λ_R⟩ = H(Z₀₁₀, X, Λ₁, Λ_R) = χ₂₃(X, Λ_R) = 0`, by the dual basis of `(X, Z₀₁₀, Z₀₀₁)` for
  the trace form, `sl2Dual`), `lieChart`, its inverse `lieChartInv` and the domain `H*`
  (`lieChartDomain`, with `r > 0`). The running claims of TeX 11575–11602: `lieChart_spec`,
  `lieChart_lieChartInv` (uniqueness: "always a full rank system", true on `H*`),
  `lieX_starBoundary_iff` (the boundary `x = 1/√3` of `𝔥*` in the chart),
  `lieChartInv_lieChart`, `isBigO_lieΛR` (the orders `O(r⁴)`, `O(r³)` of the entries of `Λ_R`).
* **Hyperboloid coordinates** (Lemma 10.1.1, (10.1.2) `eqn:st-costate-hyperboloid`, (11.2.4)
  `eqn:wbc-to-z`): the off-diagonal entry `cayleyZ M = (b + c)/2 + ia` of the Cayley transform of
  `M = [[a, b], [c, -a]]` (`lemma10_1_1`, with the matrix `cayleyA` of Appendix A.4); the
  Fuller coordinates `ẑ = (w/ρ, -ib/(2ρ), c/(6ρ))` of a phase point
  (`fullerCoords`), with `w = cayleyZ X`, `b = cayleyZ Λ₁ / d₁`, `c = cayleyZ Λ_R`; the inverse map
  `phaseOfFuller` (the hyperboloid form (10.1.2) with `d₁ = 3/2`, `ε = 1`); the phase points of the
  blow-up (`IsBlowupPhasePt`: the constraints `det X = 1`, `det Λ₁ = 9/4`, `⟨X, Λ_R⟩ = 0` and the
  sheets of the singular locus).
* **Symmetries**: the rotation `Ad_R` is multiplication by `ζ² = ζ⁻¹` in Fuller coordinates
  (`fullerCoords_adR`); the time reversal of Remark 10.2.3 (`eqn:wbc-reverse`), on phase points
  `reinTau (X, Λ₁, Λ_R) = (-DXD, -DΛ₁D, -DΛ_RD)`, `D = diag(1, -1)`, is the Fuller `τ`
  (`fullerCoords_reinTau`) and reverses the vertex flows, exchanging `e₂` and `e₃`
  (`iso_vertexFlow_reinTau`). The mirrored chart at `q_in` (E87) is `lieChartIn = reinTau ∘
  lieChart`.

## Proofs

Everything here is exact algebra on `2 × 2` matrices (`ext`, `simp`, `field_simp`, `ring`,
`Real.sq_sqrt`). The linear system (14.1.3) is solved in closed form: for traceless `X` with
`X₂₁ ≠ 0`, `Λ_R = h K(X)` with `h = ⟨Λ₁ + (3/2) J, X⟩` and `K(X)` the matrix `X` with its `(1, 2)`
entry changed so that `⟨X, K⟩ = 0` (`lieΛRShape`, `lieΛR_eq_reducedHam_smul`); the system has full
rank exactly when `X₂₁ ≠ 0` (its determinant is `-(8/(3√3)) X₂₁`, and `X₂₁ = 1 + r x̃₂₁ ≥ √3 r > 0`
on `H*`). This gives `lieChart_spec`, the uniqueness in `lieChart_lieChartInv` and the orders in
`isBigO_lieΛR` (`h = r³ g(r)` with `g` continuous at `0`), shorter than the dual-basis identities of
`sl2Dual`. `IsBlowupPhasePt` and `phaseOfFuller`: `det X = 1` reads `t² - |w|² = 1` for the Cayley
coordinates `(t, w)`, and the sheet `X₁₂ < X₂₁` fixes `t = -⟨w⟩`; likewise `t = (3/2) ⟨b⟩` for
`Λ₁`; the diagonal of `Λ_R` is fixed by `⟨X, Λ_R⟩ = 0`. `Ad_R` is computed entrywise with
`ζ² = -1/2 - i√3/2`. `fullerCoords_adR` assumes the three entries of the phase point traceless (the
book's phase points lie in `sl₂(ℝ)`): `cayleyZ` reads only the entries `M₁₁, M₁₂, M₂₁`, and without
the traces the identity fails at `q = (1, 0, 0)` (`l6b_not_fullerCoords_adR`). The reversal of the
flows is the uniqueness of the closed forms: `exp(s (-DAD)) = D exp(-s A) D`,
`D Z_{e₂} D = -Z_{e₃}`, `D J D = -J`, and the substitution `s ↦ -s` in the integrals of `iso_vfC`,
`iso_vfΛR`.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology Asymptotics
open TriFuller

/-! ### Linear algebra in `𝔰𝔩₂(ℝ)` -/

/-- The traceless matrix `Λ` with `⟨Λ, M_i⟩ = c_i` (`i = 1, 2, 3`) for the trace form, when
`M₁, M₂, M₃ ∈ 𝔰𝔩₂(ℝ)` are linearly independent: the dual basis `[M₂, M₃]/T`, `[M₃, M₁]/T`,
`[M₁, M₂]/T`, `T = ⟨M₁, [M₂, M₃]⟩`. -/
noncomputable def sl2Dual (M₁ M₂ M₃ : Mat2) (c₁ c₂ c₃ : ℝ) : Mat2 :=
  (traceForm M₁ (M₂ * M₃ - M₃ * M₂))⁻¹ •
    (c₁ • (M₂ * M₃ - M₃ * M₂) + c₂ • (M₃ * M₁ - M₁ * M₃) + c₃ • (M₁ * M₂ - M₂ * M₁))

/-! ### The Lie algebra chart (14.1.1)–(14.1.3) -/

/-- The state `X = J + r X̃` with `x̃₁₁ = 1` (TeX 11576–11583):
`X = [[r, -(1 + r²)/(1 + r x̃₂₁)], [1 + r x̃₂₁, -r]]`, determined by `det X = 1`. The book labels
this matrix `X̃` (E81); it is `X`. -/
noncomputable def lieX (r x21 : ℝ) : Mat2 :=
  !![r, -(1 + r ^ 2) / (1 + r * x21); 1 + r * x21, -r]

/-- The costate `Λ₁ = -(3/2) J + r² Λ̃₁` with `Λ̃₁ = [[ℓ̃₁₁, ℓ̃₁₂], [ℓ̃₂₁, -ℓ̃₁₁]]`, `ℓ̃₁₂`
determined by `det Λ₁ = 9/4` (TeX 11585–11587; requires `ℓ̃₂₁ r² < 3/2`). -/
noncomputable def lieΛ₁ (r l11 l21 : ℝ) : Mat2 :=
  !![r ^ 2 * l11, (9 / 4 + r ^ 4 * l11 ^ 2) / (3 / 2 - r ^ 2 * l21);
    -(3 / 2) + r ^ 2 * l21, -(r ^ 2 * l11)]

/-- The control-independent part `⟨Λ₁ + (3/2) J, X⟩` of the Hamiltonian with `λ_cost = -1`. -/
noncomputable def reducedHam (Λ₁ X : Mat2) : ℝ := traceForm (Λ₁ + (3 / 2 : ℝ) • J) X

/-- The costate `Λ_R`: the unique solution in `𝔰𝔩₂(ℝ)` of the linear system (14.1.3)
`eqn:LambdaR-linear`, `⟨X, Λ_R⟩ = H(Z₀₁₀, X, Λ₁, Λ_R) = χ₂₃(X, Λ_R) = 0` (TeX 11590–11593): with
`h = ⟨Λ₁ + (3/2) J, X⟩`, the conditions are `⟨Λ_R, X⟩ = 0`, `⟨Λ_R, Z₀₁₀⟩ = ⟨X, Z₀₁₀⟩ h` and
`⟨Λ_R, Z₀₀₁⟩ = ⟨X, Z₀₀₁⟩ h`. -/
noncomputable def lieΛR (X Λ₁ : Mat2) : Mat2 :=
  sl2Dual X (controlMatrix (vertex 1)) (controlMatrix (vertex 2)) 0
    (traceForm X (controlMatrix (vertex 1)) * reducedHam Λ₁ X)
    (traceForm X (controlMatrix (vertex 2)) * reducedHam Λ₁ X)

/-- **The Lie algebra chart** (14.1.1)–(14.1.3) (`eqn:Xtilde`, `eqn:LambdaR-linear`): the phase
point `(X, Λ₁, Λ_R)` with coordinates `p = (r, x̃)`, `x̃ = (x̃₂₁, ℓ̃₁₁, ℓ̃₂₁)` (`p.2 0 = x̃₂₁`,
`p.2 1 = ℓ̃₁₁`, `p.2 2 = ℓ̃₂₁`), normalized by `x̃₁₁ = 1`. It lies on the wall `χ₂₃ = 0` between the
controls `Z₀₁₀ = e₂` and `Z₀₀₁ = e₃` ("Up to rotational symmetry, we can assume that the trajectory
starts at the wall `χ₂₃ = 0`", TeX 11553–11555). -/
noncomputable def lieChart (p : ℝ × (Fin 3 → ℝ)) : iso_PhasePt :=
  (lieX p.1 (p.2 0), lieΛ₁ p.1 (p.2 1) (p.2 2),
    lieΛR (lieX p.1 (p.2 0)) (lieΛ₁ p.1 (p.2 1) (p.2 2)))

/-- The inverse of the chart: `r = X₁₁`, `x̃₂₁ = (X₂₁ - 1)/r`, `ℓ̃₁₁ = (Λ₁)₁₁/r²`,
`ℓ̃₂₁ = ((Λ₁)₂₁ + 3/2)/r²` ("we must take the reciprocal of the `(1, 1)` matrix coefficient",
TeX 11849–11851). -/
noncomputable def lieChartInv (q : iso_PhasePt) : ℝ × (Fin 3 → ℝ) :=
  (q.1 0 0, ![(q.1 1 0 - 1) / q.1 0 0, q.2.1 0 0 / q.1 0 0 ^ 2, (q.2.1 1 0 + 3 / 2) / q.1 0 0 ^ 2])

/-- The domain `H*` of the chart, with `r > 0` (TeX 11557–11570, (14.1.2)
`eqn:coord-restriction`): `0 < r`, `x̃₂₁ > x̃*₂₁(r) = √3 - 1/r` and `ℓ̃₂₁ r² < 3/2`. (`H*` imposes
only the boundary `x = 1/√3` of the star domain, E81.) -/
def lieChartDomain : Set (ℝ × (Fin 3 → ℝ)) :=
  {p | 0 < p.1 ∧ √3 - 1 / p.1 < p.2 0 ∧ p.2 2 * p.1 ^ 2 < 3 / 2}

/-! ### Hyperboloid coordinates and the Fuller coordinates (Lemma 10.1.1, (11.2.4)) -/

/-- **Lemma 10.1.1** (`lem:hyperboloid-coords`, TeX 8420–8429): the Cayley transform of
`[[a, b], [c, -a]] ∈ 𝔰𝔩₂(ℝ)` is `[[it, z], [z̄, -it]] ∈ 𝔰𝔲(1, 1)` with `z = (b + c)/2 + ia` and
`t = (b - c)/2`; `cayleyZ` is its off-diagonal entry `z`. -/
noncomputable def cayleyZ (M : Mat2) : ℂ := ⟨(M 0 1 + M 1 0) / 2, M 0 0⟩

/-- The matrix `A = (1/√2) [[1, i], [i, 1]] ∈ SL₂(ℂ)` of the Cayley transform
`Cayley(X) = A⁻¹ X A` (Appendix A.4, TeX 13318–13326). -/
noncomputable def cayleyA : Matrix (Fin 2) (Fin 2) ℂ := ((√2 : ℝ) : ℂ)⁻¹ • !![1, I; I, 1]

/-- `A⁻¹ = (1/√2) [[1, -i], [-i, 1]]` (`det A = 1`). -/
private theorem l6b_cayleyA_inv :
    cayleyA⁻¹ = ((√2 : ℝ) : ℂ)⁻¹ • !![1, -I; -I, 1] := by
  apply Matrix.inv_eq_left_inv
  have h2 : ((√2 : ℝ) : ℂ)⁻¹ * ((√2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  rw [cayleyA, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h2]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring_nf

/-- **Lemma 10.1.1** (`lem:hyperboloid-coords`, TeX 8420–8429): the Cayley transform
`A⁻¹ M A` of `M = [[a, b], [c, -a]] ∈ 𝔰𝔩₂(ℝ)` is `[[it, z], [z̄, -it]] ∈ 𝔰𝔲(1, 1)` with
`z = (b + c)/2 + ia = cayleyZ M` and `t = (b - c)/2`. ("This is an easy calculation":
`A⁻¹ = (1/√2) [[1, -i], [-i, 1]]`, multiply out.) -/
theorem lemma10_1_1 (M : Mat2) (hM : M.trace = 0) :
    cayleyA⁻¹ * M.map (fun x : ℝ ↦ (x : ℂ)) * cayleyA =
      !![I * (((M 0 1 - M 1 0) / 2 : ℝ) : ℂ), cayleyZ M;
        starRingEnd ℂ (cayleyZ M), -(I * (((M 0 1 - M 1 0) / 2 : ℝ) : ℂ))] := by
  have h2 : ((√2 : ℝ) : ℂ)⁻¹ * ((√2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  have h11 : M 1 1 = -M 0 0 := by rw [Matrix.trace_fin_two] at hM; linarith
  have hmap : M.map (fun x : ℝ ↦ (x : ℂ)) = !![(M 0 0 : ℂ), M 0 1; M 1 0, -(M 0 0 : ℂ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h11]
  rw [l6b_cayleyA_inv, cayleyA, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h2,
    hmap, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [cayleyZ] <;> ring

/-- **The Fuller coordinates of a phase point** (TeX 11616–11630, 12860–12866): the hyperboloid
coordinates `w = cayleyZ X`, `b = cayleyZ Λ₁ / d₁`, `c = cayleyZ Λ_R` ((10.1.2), `d₁ = 3/2`),
rescaled by (11.2.4) `eqn:wbc-to-z` with `ρ = 2`: `ẑ₁ = w/ρ`, `ẑ₂ = -ib/(2ρ)`, `ẑ₃ = c/(6ρ)`. It
vanishes at the singular locus `(J, -(3/2) J, 0)`. -/
noncomputable def fullerCoords (q : iso_PhasePt) : Fin 3 → ℂ :=
  ![cayleyZ q.1 / 2, -I * cayleyZ q.2.1 / 6, cayleyZ q.2.2 / 12]

/-- `⟨w⟩ = √(1 + |w|²)` (the notation `⟨·⟩ = ⟨·⟩₁` of Chapter 10, TeX 8445–8449). -/
noncomputable def jbr (w : ℂ) : ℝ := √(1 + ‖w‖ ^ 2)

/-- **The phase point with given Fuller coordinates**: the hyperboloid form (10.1.2)
`eqn:st-costate-hyperboloid` (TeX 8474–8480) with `d₁ = 3/2`, `ε = 1`, and the inverse of (11.2.4):
`w = 2 z₁`, `b = 4i z₂`, `c = 12 z₃`, `X = [[-i⟨w⟩, w], [w̄, i⟨w⟩]]`,
`Λ₁ = d₁ [[i⟨b⟩, b], [b̄, -i⟨b⟩]]`, `Λ_R = [[-i RR(c, w)/⟨w⟩, c], [c̄, i RR(c, w)/⟨w⟩]]` in
`𝔰𝔲(1, 1)`, transported back to `𝔰𝔩₂(ℝ)` by the inverse Cayley transform. -/
noncomputable def phaseOfFuller (z : Fin 3 → ℂ) : iso_PhasePt :=
  (!![(2 * z 0).im, (2 * z 0).re - jbr (2 * z 0); (2 * z 0).re + jbr (2 * z 0), -(2 * z 0).im],
    !![(6 * I * z 1).im, (6 * I * z 1).re + 3 / 2 * jbr (4 * I * z 1);
      (6 * I * z 1).re - 3 / 2 * jbr (4 * I * z 1), -(6 * I * z 1).im],
    !![(12 * z 2).im, (12 * z 2).re - RR (2 * z 0) (12 * z 2) / jbr (2 * z 0);
      (12 * z 2).re + RR (2 * z 0) (12 * z 2) / jbr (2 * z 0), -(12 * z 2).im])

/-- **The phase points of the blow-up** (TeX 11510–11512, 12856–12872): traceless `X, Λ₁, Λ_R`
with `det X = 1`, `det Λ₁ = d₁² = 9/4` and `⟨X, Λ_R⟩ = 0`, on the sheets of the two hyperboloids
that contain the singular locus `(J, -(3/2) J, 0)`: `X₁₂ < X₂₁` (the Cayley coordinate
`t = (X₁₂ - X₂₁)/2` is `-⟨w⟩`, as for `X = J`; the sign convention on the orbit `𝒪_J`,
TeX 8489–8491)
and `(Λ₁)₂₁ < (Λ₁)₁₂` (`t = d₁⟨b⟩ > 0`, the sign of `⟨J, Λ₁⟩` at the singular locus, TeX
11190–11196). -/
def IsBlowupPhasePt (q : iso_PhasePt) : Prop :=
  q.1.trace = 0 ∧ q.2.1.trace = 0 ∧ q.2.2.trace = 0 ∧ q.1.det = 1 ∧ q.2.1.det = 9 / 4 ∧
    traceForm q.1 q.2.2 = 0 ∧ q.1 0 1 < q.1 1 0 ∧ q.2.1 1 0 < q.2.1 0 1

/-- The point of the singular locus in the normalized phase space: `(J, -(3/2) J, 0)`. -/
noncomputable def singularPhasePt : iso_PhasePt := (J, (-(3 / 2) : ℝ) • J, 0)

/-! ### The symmetries -/

/-- The time reversal on `𝔰𝔩₂(ℝ)`: `M ↦ -D M D` with `D = diag(1, -1)`,
`[[a, b], [c, -a]] ↦ [[-a, b], [c, a]]` (the Cayley coordinate `z ↦ z̄`, `t ↦ t`). -/
def matTau (M : Mat2) : Mat2 := !![-M 0 0, M 0 1; M 1 0, -M 1 1]

/-- The matrix `D = diag(1, -1)` of the time reversal (`D g D` reverses the state `g`). -/
def diagD : Mat2 := !![1, 0; 0, -1]

/-- The time reversal of phase points (Remark 10.2.3, `eqn:wbc-reverse`, TeX 8672–8682, in
`𝔰𝔩₂(ℝ)`): `M ↦ -D M D` with `D = diag(1, -1)`, `[[a, b], [c, -a]] ↦ [[-a, b], [c, a]]`, on each
of `X, Λ₁, Λ_R`. In hyperboloid coordinates it is complex conjugation of `(w, b, c)`. -/
noncomputable def reinTau (q : iso_PhasePt) : iso_PhasePt :=
  (matTau q.1, matTau q.2.1, matTau q.2.2)

/-- The relabelling of the vertices under the time reversal: `e₁ ↦ e₁`, `e₂ ↔ e₃`
(`-D Z_{e₂} D = Z_{e₃}`, `-D Z_{e₁} D = Z_{e₁}`). -/
def vertexSwap (m : Fin 3) : Fin 3 := ![0, 2, 1] m

/-- **The mirrored chart at `q_in`** (Remark 14.3.4, E87): `(r, x̃) ↦ τ(lieChart (r, x̃))`. The
chart (14.1.1)–(14.1.2) normalizes `x̃₁₁ = 1`, so `Im ẑ₁ > 0`, while `q_in = τ(q_out)` has
`Im z₁ < 0`; the mirrored chart normalizes `x̃₁₁ = -1`. -/
noncomputable def lieChartIn (p : ℝ × (Fin 3 → ℝ)) : iso_PhasePt := reinTau (lieChart p)

/-- The inverse of the mirrored chart. -/
noncomputable def lieChartInInv (q : iso_PhasePt) : ℝ × (Fin 3 → ℝ) := lieChartInv (reinTau q)

/-! ### The chart: the solution of (14.1.3)

With `h = ⟨Λ₁ + (3/2) J, X⟩`, the three equations (14.1.3) for a traceless `Λ_R` read
`⟨Λ_R, X⟩ = 0`, `⟨Λ_R, Z_{e₂}⟩ = h ⟨X, Z_{e₂}⟩`, `⟨Λ_R, Z_{e₃}⟩ = h ⟨X, Z_{e₃}⟩`. The matrices
`Z_{e₂}, Z_{e₃}` have zero `(2, 1)` entry, so the last two only see the diagonal and the `(2, 1)`
entry of `Λ_R`: they force `(Λ_R)₁₁ = h X₁₁`, `(Λ_R)₂₁ = h X₂₁`, and the first fixes `(Λ_R)₁₂`
when `X₂₁ ≠ 0`. Hence `Λ_R = h K(X)` (`lieΛR_eq_reducedHam_smul`), which gives the full rank claim,
the uniqueness and the orders `O(r³)`, `O(r⁴)` at once (`h = O(r³)` on the chart). -/

private theorem l6b_controlMatrix_vertex1 :
    controlMatrix (vertex 1) = !![1 / √3, -2 / 3; 0, -1 / √3] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [controlMatrix, vertex]

private theorem l6b_controlMatrix_vertex2 :
    controlMatrix (vertex 2) = !![-1 / √3, -2 / 3; 0, 1 / √3] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [controlMatrix, vertex]

/-- The solution of (14.1.3): `Λ_R = h K` with `K` the matrix `X` with its `(1, 2)` entry changed
so that `⟨X, K⟩ = 0`. -/
noncomputable def lieΛRShape (X : Mat2) : Mat2 :=
  !![X 0 0, -2 * X 0 0 ^ 2 / X 1 0 - X 0 1; X 1 0, -X 0 0]

/-- **The solution of (14.1.3) in closed form**: for traceless `X` with `X₂₁ ≠ 0` (the system is
of full rank exactly then: its determinant is `-(8/(3√3)) X₂₁`), `Λ_R = h K(X)` with
`h = ⟨Λ₁ + (3/2) J, X⟩`. -/
theorem lieΛR_eq_reducedHam_smul (X Λ₁ : Mat2) (hX : X 1 1 = -X 0 0) (hc : X 1 0 ≠ 0) :
    lieΛR X Λ₁ = reducedHam Λ₁ X • lieΛRShape X := by
  unfold lieΛR sl2Dual lieΛRShape
  generalize reducedHam Λ₁ X = h
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  rw [l6b_controlMatrix_vertex1, l6b_controlMatrix_vertex2, Matrix.eta_fin_two X, hX]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [traceForm, Matrix.trace_fin_two] <;> field_simp <;> ring_nf

/-- `⟨X, Z_{e₂}⟩ = -(2/√3) ρ₁(X)` for traceless `X`. -/
private theorem l6b_traceForm_vertex1 (X : Mat2) (hX : X 1 1 = -X 0 0) :
    traceForm X (controlMatrix (vertex 1)) = -(2 / 3) * (X 1 0 - √3 * X 0 0) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  rw [l6b_controlMatrix_vertex1, traceForm, Matrix.eta_fin_two X, hX]
  simp [Matrix.trace_fin_two]
  field_simp
  linear_combination (-2 * X 0 0) * h3

/-- `⟨X, Z_{e₃}⟩ = -(2/√3) ρ₀(X)` for traceless `X`. -/
private theorem l6b_traceForm_vertex2 (X : Mat2) (hX : X 1 1 = -X 0 0) :
    traceForm X (controlMatrix (vertex 2)) = -(2 / 3) * (X 1 0 + √3 * X 0 0) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  rw [l6b_controlMatrix_vertex2, traceForm, Matrix.eta_fin_two X, hX]
  simp [Matrix.trace_fin_two]
  field_simp
  linear_combination (2 * X 0 0) * h3

/-- `K` and `X` agree off the `(1, 2)` entry, which `⟨·, Z⟩` ignores when `Z₂₁ = 0`. -/
private theorem l6b_traceForm_K (X Z : Mat2) (hX : X 1 1 = -X 0 0) (hZ : Z 1 0 = 0) :
    traceForm (lieΛRShape X) Z = traceForm X Z := by
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp [lieΛRShape, hZ, hX]

private theorem l6b_traceForm_X_K (X : Mat2) (hX : X 1 1 = -X 0 0) (hc : X 1 0 ≠ 0) :
    traceForm X (lieΛRShape X) = 0 := by
  simp [traceForm, lieΛRShape, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hX]
  field_simp
  ring

private theorem l6b_trace_K (X : Mat2) : (lieΛRShape X).trace = 0 := by
  simp [lieΛRShape, Matrix.trace_fin_two]

private theorem l6b_traceForm_comm (A B : Mat2) : traceForm A B = traceForm B A := by
  rw [traceForm, traceForm, Matrix.trace_mul_comm]

private theorem l6b_reducedHam_eq (Λ₁ X : Mat2) :
    traceForm (Λ₁ - (3 / 2 * -1 : ℝ) • J) X = reducedHam Λ₁ X := by
  rw [reducedHam]; congr 1; rw [show (3 / 2 * -1 : ℝ) = -(3 / 2) by norm_num, neg_smul,
    sub_neg_eq_add]

/-- The section conditions for `Λ_R = h K`. -/
private theorem l6b_section_of_K (X Λ₁ : Mat2) (hX : X 1 1 = -X 0 0)
    (h1 : traceForm X (controlMatrix (vertex 1)) ≠ 0)
    (h2 : traceForm X (controlMatrix (vertex 2)) ≠ 0) :
    hamiltonian (-1) Λ₁ (reducedHam Λ₁ X • lieΛRShape X) X (vertex 1) = 0 ∧
      switchingFn 1 2 (reducedHam Λ₁ X • lieΛRShape X) X = 0 := by
  have hz1 : controlMatrix (vertex 1) 1 0 = 0 := by simp [controlMatrix, vertex]
  have hz2 : controlMatrix (vertex 2) 1 0 = 0 := by simp [controlMatrix, vertex]
  have k1 := l6b_traceForm_K X _ hX hz1
  have k2 := l6b_traceForm_K X _ hX hz2
  constructor
  · rw [hamiltonian, l6b_reducedHam_eq Λ₁, traceForm, Matrix.smul_mul, Matrix.trace_smul,
      ← traceForm, k1, smul_eq_mul, mul_div_assoc, div_self h1, mul_one, sub_self]
  · rw [switchingFn, controlP, controlP, traceForm, Matrix.smul_mul, Matrix.trace_smul,
      Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.trace_smul, ← traceForm, ← traceForm, k1, k2, l6b_traceForm_comm _ X,
      l6b_traceForm_comm _ X]
    simp only [smul_eq_mul]
    rw [inv_mul_cancel₀ h1, inv_mul_cancel₀ h2, sub_self, mul_zero]

private theorem l6b_lieX_11 (r x21 : ℝ) : lieX r x21 1 1 = -lieX r x21 0 0 := by simp [lieX]

/-! ### The chart: the running claims of §14.1 -/

/-- **The chart lies on the Poincaré section** (`eqn:Xtilde`, TeX 11575–11602): for `(r, x̃) ∈ H*`,
the phase point `lieChart (r, x̃)` is a phase point of the blow-up (`det X = 1`, `det Λ₁ = 9/4`,
`⟨X, Λ_R⟩ = 0`), satisfies (14.1.3) (`H(Z₀₁₀) = 0`, `χ₂₃ = 0`), has `X = J + rX̃` with `x̃₁₁ = 1`
and `X₂₁ = 1 + r x̃₂₁ ≥ √3 r > 0` ("Hence, we may invert `1 + r x̃₂₁`"), and `lieChartInv` recovers
`(r, x̃)`. -/
theorem lieChart_spec {p : ℝ × (Fin 3 → ℝ)} (hp : p ∈ lieChartDomain) :
    IsBlowupPhasePt (lieChart p) ∧
      hamiltonian (-1) (lieChart p).2.1 (lieChart p).2.2 (lieChart p).1 (vertex 1) = 0 ∧
      switchingFn 1 2 (lieChart p).2.2 (lieChart p).1 = 0 ∧ (lieChart p).1 0 0 = p.1 ∧
      √3 * p.1 ≤ (lieChart p).1 1 0 ∧ lieChartInv (lieChart p) = p := by
  obtain ⟨r, x⟩ := p
  obtain ⟨hr, hx0, hx2⟩ := hp
  simp only at hr hx0 hx2
  have h3 : 0 < √3 := by positivity
  have hc : √3 * r < 1 + r * x 0 := by
    have := mul_lt_mul_of_pos_left hx0 hr
    rw [mul_sub, mul_one_div_cancel hr.ne'] at this
    linarith
  have hc0 : 0 < 1 + r * x 0 := by nlinarith
  have hd : 0 < 3 / 2 - r ^ 2 * x 2 := by linarith
  set X := lieX r (x 0) with hXdef
  set L := lieΛ₁ r (x 1) (x 2) with hLdef
  have hX11 : X 1 1 = -X 0 0 := l6b_lieX_11 _ _
  have hX00 : X 0 0 = r := by simp [hXdef, lieX]
  have hX10 : X 1 0 = 1 + r * x 0 := by simp [hXdef, lieX]
  have hX01 : X 0 1 = -(1 + r ^ 2) / (1 + r * x 0) := by simp [hXdef, lieX]
  have hR : lieΛR X L = reducedHam L X • lieΛRShape X :=
    lieΛR_eq_reducedHam_smul X L hX11 (by rw [hX10]; exact hc0.ne')
  have hlc : lieChart (r, x) = (X, L, reducedHam L X • lieΛRShape X) := by
    rw [← hR]; rfl
  have t1 : traceForm X (controlMatrix (vertex 1)) ≠ 0 := by
    rw [l6b_traceForm_vertex1 X hX11, hX10, hX00]
    have : 0 < 1 + r * x 0 - √3 * r := by linarith
    intro h; nlinarith
  have t2 : traceForm X (controlMatrix (vertex 2)) ≠ 0 := by
    rw [l6b_traceForm_vertex2 X hX11, hX10, hX00]
    have : 0 < 1 + r * x 0 + √3 * r := by nlinarith
    intro h; nlinarith
  obtain ⟨hH, hχ⟩ := l6b_section_of_K X L hX11 t1 t2
  rw [hlc]
  have hd' : 3 / 2 - r ^ 2 * x 2 ≠ 0 := hd.ne'
  have hc0' : 1 + r * x 0 ≠ 0 := hc0.ne'
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hH, hχ, hX00,
    by change √3 * r ≤ X 1 0; rw [hX10]; exact hc.le, ?_⟩
  · simp [hXdef, lieX, Matrix.trace_fin_two]
  · simp [hLdef, lieΛ₁, Matrix.trace_fin_two]
  · rw [Matrix.trace_smul, l6b_trace_K, smul_zero]
  · change X.det = 1
    rw [Matrix.det_fin_two, hX11, hX00, hX10, hX01]
    field_simp
    ring
  · simp only [hLdef, lieΛ₁, Matrix.det_fin_two_of]
    linear_combination div_mul_cancel₀ (9 / 4 + r ^ 4 * x 1 ^ 2) hd'
  · rw [traceForm, Matrix.mul_smul, Matrix.trace_smul, ← traceForm,
      l6b_traceForm_X_K X hX11 (by rw [hX10]; exact hc0.ne'), smul_zero]
  · change X 0 1 < X 1 0
    rw [hX01, hX10]
    have : -(1 + r ^ 2) / (1 + r * x 0) < 0 :=
      div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hc0
    linarith
  · change L 1 0 < L 0 1
    simp only [hLdef, lieΛ₁, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    have : 0 < (9 / 4 + r ^ 4 * x 1 ^ 2) / (3 / 2 - r ^ 2 * x 2) := by positivity
    linarith
  · change (X 0 0, ![(X 1 0 - 1) / X 0 0, L 0 0 / X 0 0 ^ 2, (L 1 0 + 3 / 2) / X 0 0 ^ 2]) = (r, x)
    rw [hX00, hX10]
    refine Prod.ext rfl ?_
    funext k
    fin_cases k <;> simp [hLdef, lieΛ₁] <;> field_simp

/-- **The boundary `x = 1/√3` of the star domain in the chart** (TeX 11561–11567): "Suppose
`Φ(z) = J + r X̃`, `z = x + iy ∈ 𝔥*`, with `x > 0`. We have `x̃₂₁ ≤ √3 - 1/r` if and only if
`x ≥ 1/√3`, which lies outside the star domain." (`Φ(z) = J + r X̃` with `x̃₁₁ = 1` means
`Φ(z) = lieX r x̃₂₁`, so `r = x/y` and `x̃₂₁ = (1 - y)/x`.) -/
theorem lieX_starBoundary_iff {x y r x21 : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : Φ x y = lieX r x21) : x21 ≤ √3 - 1 / r ↔ 1 / √3 ≤ x := by
  have e00 := congrFun (congrFun h 0) 0
  have e10 := congrFun (congrFun h 1) 0
  simp only [Φ, lieX, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e10
  have hr : 0 < r := by rw [← e00]; positivity
  have h3 : 0 < √3 := by positivity
  rw [← sub_nonneg, show √3 - 1 / r - x21 = (√3 * r - (1 + r * x21)) / r by field_simp; ring,
    ← e10, ← e00, div_nonneg_iff, div_le_iff₀ h3]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · rw [sub_nonneg, div_le_iff₀ hy, mul_div_assoc', div_mul_cancel₀ _ hy.ne'] at h1
      linarith
    · exfalso; have : 0 < x / y := by positivity
      linarith
  · intro h1
    left
    refine ⟨?_, by positivity⟩
    rw [sub_nonneg, div_le_iff₀ hy, mul_div_assoc', div_mul_cancel₀ _ hy.ne']
    linarith

/-- **Uniqueness of the chart** (`eqn:LambdaR-linear`, TeX 11584–11602: "`X` is determined uniquely
by `r` and `x̃₂₁` … `Λ₁` is uniquely determined … `Λ_R ∈ 𝔰𝔩₂` is uniquely determined … by the three
linear equations (14.1.3) (which is always a full rank system of linear equations for `Λ_R`) … In
summary, `(r, x̃) ∈ H*` with `r > 0` is a local coordinate for `(X, Λ₁, Λ_R)`"): a phase point of
the blow-up on the section (`H(Z₀₁₀) = 0`, `χ₂₃ = 0`), with `X` a star state and `r = X₁₁ > 0`, is
`lieChart` of its coordinates, which lie in `H*`. The full rank holds because the determinant of the
system is a nonzero multiple of `X₂₁ > 0`; the star condition makes the denominators `⟨X, Z_u⟩`
nonzero; `x̃₂₁ > √3 - 1/r` is the star condition `ρ₁(X) > 0` (`X₂₁ > √3 X₁₁`, i.e. `x < 1/√3`,
`lieX_starBoundary_iff`), and `ℓ̃₂₁ r² < 3/2` is `(Λ₁)₂₁ < 0` (from `det Λ₁ = 9/4` and the sheet
`(Λ₁)₂₁ < (Λ₁)₁₂`). -/
theorem lieChart_lieChartInv {q : iso_PhasePt} (hq : IsBlowupPhasePt q) (hX : IsStarState q.1)
    (hH : hamiltonian (-1) q.2.1 q.2.2 q.1 (vertex 1) = 0) (hχ : switchingFn 1 2 q.2.2 q.1 = 0)
    (hr : 0 < q.1 0 0) :
    lieChartInv q ∈ lieChartDomain ∧ lieChart (lieChartInv q) = q := by
  obtain ⟨X, L, Q⟩ := q
  obtain ⟨htX, htL, htQ, hdX, hdL, hXQ, hsX, hsL⟩ := hq
  obtain ⟨-, -, hρ₀, hρ₁, -⟩ := hX
  simp only at hr hH hχ htX htL htQ hdX hdL hXQ hsX hsL hρ₀ hρ₁
  rw [Matrix.trace_fin_two] at htX htL htQ
  rw [Matrix.det_fin_two] at hdX hdL
  have hX11 : X 1 1 = -X 0 0 := by linarith
  have hL11 : L 1 1 = -L 0 0 := by linarith
  have hQ11 : Q 1 1 = -Q 0 0 := by linarith
  have h3 : 0 < √3 := by positivity
  have hc : √3 * X 0 0 < X 1 0 := by
    rw [ρ₁, lt_div_iff₀ h3, zero_mul] at hρ₁; linarith
  have hc' : 0 < X 1 0 + √3 * X 0 0 := by
    rw [ρ₀, lt_div_iff₀ h3, zero_mul] at hρ₀; linarith
  have hc0 : 0 < X 1 0 := by nlinarith
  have hL10 : L 1 0 < 0 := by
    rw [hL11] at hdL
    by_contra hcon
    have hcon : 0 ≤ L 1 0 := not_lt.mp hcon
    nlinarith [mul_nonneg hcon (hcon.trans hsL.le), sq_nonneg (L 0 0)]
  set r := X 0 0 with hrdef
  constructor
  · refine ⟨hr, ?_, ?_⟩
    · change √3 - 1 / r < (X 1 0 - 1) / r
      rw [sub_div' hr.ne', div_lt_div_iff_of_pos_right hr]
      linarith
    · change (L 1 0 + 3 / 2) / r ^ 2 * r ^ 2 < 3 / 2
      rw [div_mul_cancel₀ _ (by positivity)]
      linarith
  · have eX : lieX r ((X 1 0 - 1) / r) = X := by
      have e01 : X 0 1 = -(1 + r ^ 2) / X 1 0 := by
        rw [eq_div_iff hc0.ne']; rw [hX11] at hdX; linarith
      have hx21 : 1 + r * ((X 1 0 - 1) / r) = X 1 0 := by rw [mul_div_cancel₀ _ hr.ne']; ring
      ext i j; fin_cases i <;> fin_cases j <;>
        simp only [lieX, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
          Fin.mk_one, Fin.isValue, hx21, e01, hX11]
      rfl
    have eL : lieΛ₁ r (L 0 0 / r ^ 2) ((L 1 0 + 3 / 2) / r ^ 2) = L := by
      have e01 : L 0 1 = (9 / 4 + L 0 0 ^ 2) / -L 1 0 := by
        rw [eq_div_iff (by linarith)]; rw [hL11] at hdL; linarith
      have hr2 : r ^ 2 ≠ 0 := by positivity
      have hl11 : r ^ 2 * (L 0 0 / r ^ 2) = L 0 0 := mul_div_cancel₀ _ hr2
      have hl21 : r ^ 2 * ((L 1 0 + 3 / 2) / r ^ 2) = L 1 0 + 3 / 2 := mul_div_cancel₀ _ hr2
      have hl4 : r ^ 4 * (L 0 0 / r ^ 2) ^ 2 = L 0 0 ^ 2 := by
        rw [show r ^ 4 * (L 0 0 / r ^ 2) ^ 2 = (r ^ 2 * (L 0 0 / r ^ 2)) ^ 2 by ring, hl11]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp only [lieΛ₁, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
          Fin.mk_one, Fin.isValue, hl11, hl21, hl4, e01, hL11] <;> ring
    change (lieX r ((X 1 0 - 1) / r), lieΛ₁ r (L 0 0 / r ^ 2) ((L 1 0 + 3 / 2) / r ^ 2),
      lieΛR (lieX r ((X 1 0 - 1) / r)) (lieΛ₁ r (L 0 0 / r ^ 2) ((L 1 0 + 3 / 2) / r ^ 2))) =
      (X, L, Q)
    rw [eX, eL, lieΛR_eq_reducedHam_smul X L hX11 hc0.ne']
    congr 2
    set h := reducedHam L X with hh
    have t1 : traceForm X (controlMatrix (vertex 1)) ≠ 0 := by
      rw [l6b_traceForm_vertex1 X hX11]; intro h0; nlinarith
    have t2 : traceForm X (controlMatrix (vertex 2)) ≠ 0 := by
      rw [l6b_traceForm_vertex2 X hX11]; intro h0; nlinarith
    have q1 : traceForm Q (controlMatrix (vertex 1)) =
        h * traceForm X (controlMatrix (vertex 1)) := by
      rw [hamiltonian, l6b_reducedHam_eq, ← hh, sub_eq_zero, eq_div_iff t1] at hH
      exact hH.symm
    have q2 : traceForm Q (controlMatrix (vertex 2)) =
        h * traceForm X (controlMatrix (vertex 2)) := by
      rw [switchingFn, controlP, controlP, traceForm, Matrix.mul_sub, Matrix.trace_sub,
        Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, ← traceForm,
        ← traceForm, l6b_traceForm_comm (controlMatrix _) X, l6b_traceForm_comm (controlMatrix _) X,
        q1, smul_eq_mul, smul_eq_mul, sub_eq_zero, ← mul_assoc, mul_comm _ h, mul_assoc,
        inv_mul_cancel₀ t1, mul_one, inv_mul_eq_iff_eq_mul₀ t2] at hχ
      rw [hχ]; ring
    rw [l6b_traceForm_vertex1 Q hQ11, l6b_traceForm_vertex1 X hX11] at q1
    rw [l6b_traceForm_vertex2 Q hQ11, l6b_traceForm_vertex2 X hX11] at q2
    have hQ10 : Q 1 0 = h * X 1 0 := by linarith
    have hQ00 : Q 0 0 = h * X 0 0 := by
      have : √3 * (Q 0 0 - h * X 0 0) = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 h3.ne'
      · linarith
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at hXQ
    rw [hX11, hQ11] at hXQ
    have hQ01 : Q 0 1 = h * (-2 * X 0 0 ^ 2 / X 1 0 - X 0 1) := by
      field_simp
      rw [hQ00, hQ10] at hXQ
      linarith
    ext i j; fin_cases i <;> fin_cases j <;> simp [lieΛRShape, hQ00, hQ01, hQ10, hQ11]

/-- **The orders of `Λ_R`** (TeX 11594–11596): for fixed `x̃`, as `r → 0⁺`, the diagonal entries
of `Λ_R(r, x̃)` are `O(r⁴)` and the off-diagonal entries `O(r³)` (so `Λ̃_R = Λ_R/r³` has a limit
with zero diagonal). -/
theorem isBigO_lieΛR (x : Fin 3 → ℝ) :
    (fun r ↦ (lieChart (r, x)).2.2 0 0) =O[𝓝[>] 0] (fun r ↦ r ^ 4) ∧
      (fun r ↦ (lieChart (r, x)).2.2 0 1) =O[𝓝[>] 0] (fun r ↦ r ^ 3) ∧
      (fun r ↦ (lieChart (r, x)).2.2 1 0) =O[𝓝[>] 0] (fun r ↦ r ^ 3) := by
  set c : ℝ → ℝ := fun r ↦ 1 + r * x 0 with hcdef
  set d : ℝ → ℝ := fun r ↦ 3 / 2 - r ^ 2 * x 2 with hddef
  set g : ℝ → ℝ := fun r ↦ 2 * x 1 + (r * x 1 ^ 2 * c r ^ 2 +
    3 / 2 * x 2 * (2 * x 0 + r * x 0 ^ 2 - r) + r * x 2 ^ 2 * (1 + r ^ 2)) / (d r * c r)
    with hgdef
  have hc : Continuous c := by fun_prop
  have hd : Continuous d := by fun_prop
  have hc0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), c r ≠ 0 :=
    nhdsWithin_le_nhds (hc.continuousAt.eventually_ne (by simp [hcdef]))
  have hd0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), d r ≠ 0 :=
    nhdsWithin_le_nhds (hd.continuousAt.eventually_ne (by simp [hddef]))
  have hgc : ContinuousAt g 0 := by
    have h0 : d 0 * c 0 ≠ 0 := by simp [hcdef, hddef]
    exact continuousAt_const.add ((by fun_prop : Continuous fun r : ℝ ↦ r * x 1 ^ 2 * c r ^ 2 +
      3 / 2 * x 2 * (2 * x 0 + r * x 0 ^ 2 - r) + r * x 2 ^ 2 * (1 + r ^ 2)).continuousAt.div
      (hd.mul hc).continuousAt h0)
  have hh : ∀ r, c r ≠ 0 → d r ≠ 0 →
      reducedHam (lieΛ₁ r (x 1) (x 2)) (lieX r (x 0)) = r ^ 3 * g r := by
    intro r hcr hdr
    simp only [hcdef, hddef] at hcr hdr
    have hdr2 : 3 - r ^ 2 * 2 * x 2 ≠ 0 := fun h ↦ hdr (by linarith)
    simp only [reducedHam, traceForm, lieΛ₁, lieX, J, hgdef, hcdef, hddef, Matrix.trace_fin_two,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, smul_eq_mul]
    field_simp
    ring
  have hent : ∀ r, c r ≠ 0 → d r ≠ 0 →
      (lieChart (r, x)).2.2 = (r ^ 3 * g r) • lieΛRShape (lieX r (x 0)) := by
    intro r hcr hdr
    change lieΛR (lieX r (x 0)) (lieΛ₁ r (x 1) (x 2)) = _
    rw [lieΛR_eq_reducedHam_smul _ _ (l6b_lieX_11 _ _) (by simpa [lieX] using hcr), hh r hcr hdr]
  have hO : ∀ (k : ℕ) (φ : ℝ → ℝ), ContinuousAt φ 0 →
      (fun r ↦ r ^ k * (g r * φ r)) =O[𝓝[>] 0] (fun r ↦ r ^ k) := by
    intro k φ hφ
    have h1 : g =O[𝓝[>] 0] (fun _ ↦ (1 : ℝ)) :=
      (hgc.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ
    have h2 : φ =O[𝓝[>] 0] (fun _ ↦ (1 : ℝ)) :=
      (hφ.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ
    simpa using (isBigO_refl (fun r : ℝ ↦ r ^ k) (𝓝[>] 0)).mul (h1.mul h2)
  refine ⟨?_, ?_, ?_⟩
  · refine (hO 4 (fun _ ↦ 1) continuousAt_const).congr' ?_ EventuallyEq.rfl
    filter_upwards [hc0, hd0] with r hcr hdr
    rw [hent r hcr hdr]
    simp [lieΛRShape, lieX]
    ring
  · refine (hO 3 (fun r ↦ (1 - r ^ 2) / c r) ?_).congr' ?_ EventuallyEq.rfl
    · exact (by fun_prop : Continuous fun r : ℝ ↦ 1 - r ^ 2).continuousAt.div hc.continuousAt
        (by simp [hcdef])
    filter_upwards [hc0, hd0] with r hcr hdr
    rw [hent r hcr hdr]
    simp only [hcdef] at hcr
    simp [lieΛRShape, lieX, hcdef]
    field_simp
    ring
  · refine (hO 3 c hc.continuousAt).congr' ?_ EventuallyEq.rfl
    filter_upwards [hc0, hd0] with r hcr hdr
    rw [hent r hcr hdr]
    simp [lieΛRShape, lieX, hcdef]
    ring

/-! ### Hyperboloid coordinates: the identification with `ℂ³` -/

theorem jbr_sq (w : ℂ) : jbr w ^ 2 = 1 + w.re ^ 2 + w.im ^ 2 := by
  rw [jbr, Real.sq_sqrt (by positivity), Complex.sq_norm, Complex.normSq_apply]; ring

theorem jbr_pos (w : ℂ) : 0 < jbr w := Real.sqrt_pos.2 (by positivity)

private theorem l6b_jbr_eq {w : ℂ} {v : ℝ} (hv : 0 < v) (h : v ^ 2 = 1 + w.re ^ 2 + w.im ^ 2) :
    jbr w = v := by
  rw [jbr, Real.sqrt_eq_iff_mul_self_eq_of_pos hv, Complex.sq_norm, Complex.normSq_apply]
  linear_combination h

theorem cayleyZ_eq (M : Mat2) :
    cayleyZ M = (((M 0 1 + M 1 0) / 2 : ℝ) : ℂ) + ((M 0 0 : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [cayleyZ]

/-- The Fuller coordinates of `phaseOfFuller z` are `z`. -/
theorem fullerCoords_phaseOfFuller (z : Fin 3 → ℂ) : fullerCoords (phaseOfFuller z) = z := by
  ext k; fin_cases k <;> apply Complex.ext <;>
    simp [fullerCoords, phaseOfFuller, cayleyZ]

/-- `phaseOfFuller z` is a phase point of the blow-up (the form (10.1.2) "ensures that the
constraints `det(X) = 1` and `⟨X, Λ_R⟩ = 0` are satisfied", TeX 8481–8483). -/
theorem isBlowupPhasePt_phaseOfFuller (z : Fin 3 → ℂ) : IsBlowupPhasePt (phaseOfFuller z) := by
  have h0 := jbr_sq (2 * z 0)
  have h1 := jbr_sq (4 * I * z 1)
  have p0 := jbr_pos (2 * z 0)
  have p1 := jbr_pos (4 * I * z 1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [phaseOfFuller, Matrix.trace_fin_two]
  · simp [phaseOfFuller, Matrix.trace_fin_two]
  · simp [phaseOfFuller, Matrix.trace_fin_two]
  · simp only [phaseOfFuller, Matrix.det_fin_two_of]
    linear_combination h0
  · simp only [phaseOfFuller, Matrix.det_fin_two_of]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at h1 ⊢
    norm_num at h1 ⊢
    linear_combination (9 / 4 : ℝ) * h1
  · simp only [phaseOfFuller, traceForm, Matrix.trace_fin_two, Matrix.mul_fin_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, RR_eq_re_mul_add_im_mul]
    field_simp
    ring
  · simp [phaseOfFuller]; linarith
  · simp [phaseOfFuller]; linarith

/-- **The Fuller coordinates are coordinates on the blow-up phase points**: a phase point of the
blow-up is `phaseOfFuller` of its Fuller coordinates (the hyperboloid parametrization (10.1.2),
TeX 8484–8491). -/
theorem phaseOfFuller_fullerCoords {q : iso_PhasePt} (hq : IsBlowupPhasePt q) :
    phaseOfFuller (fullerCoords q) = q := by
  obtain ⟨X, L, Q⟩ := q
  obtain ⟨hX, hL, hQ, hdX, hdL, hXQ, hsX, hsL⟩ := hq
  simp only [Matrix.trace_fin_two] at hX hL hQ
  simp only [Matrix.det_fin_two] at hdX hdL
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at hXQ
  have e0 : 2 * fullerCoords (X, L, Q) 0 = cayleyZ X := by
    simp [fullerCoords]; ring
  have e1 : 6 * I * fullerCoords (X, L, Q) 1 = cayleyZ L := by
    simp only [fullerCoords, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring_nf; rw [I_sq]; ring
  have e1' : 4 * I * fullerCoords (X, L, Q) 1 = ((2 / 3 : ℝ) : ℂ) * cayleyZ L := by
    simp only [fullerCoords, Matrix.cons_val_one, Matrix.cons_val_zero]
    push_cast
    ring_nf; rw [I_sq]; ring
  have e2 : 12 * fullerCoords (X, L, Q) 2 = cayleyZ Q := by
    simp [fullerCoords]; ring
  have jX : jbr (cayleyZ X) = (X 1 0 - X 0 1) / 2 := by
    apply l6b_jbr_eq (by linarith)
    simp only [cayleyZ]
    linear_combination hdX - X 0 0 * hX
  have jL : jbr (((2 / 3 : ℝ) : ℂ) * cayleyZ L) = (L 0 1 - L 1 0) / 3 := by
    apply l6b_jbr_eq (by linarith)
    simp only [cayleyZ, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    linear_combination (4 / 9 : ℝ) * hdL - (4 / 9 * L 0 0) * hL
  have hRR : RR (cayleyZ X) (cayleyZ Q) / ((X 1 0 - X 0 1) / 2) = (Q 1 0 - Q 0 1) / 2 := by
    rw [div_eq_iff (by linarith), RR_eq_re_mul_add_im_mul]
    simp only [cayleyZ]
    have hX11 : X 1 1 = -X 0 0 := by linarith
    have hQ11 : Q 1 1 = -Q 0 0 := by linarith
    rw [hX11, hQ11] at hXQ
    linear_combination (1 / 2 : ℝ) * hXQ
  simp only [phaseOfFuller, e0, e1, e1', e2, jX, jL, hRR, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [cayleyZ] <;>
    linarith

/-- "At the singular locus, we have `w = b = c = 0`" (TeX 11182–11183): a phase point of the blow-up
has Fuller coordinates `0` exactly at the singular locus `(J, -(3/2) J, 0)`. -/
theorem fullerCoords_eq_zero_iff {q : iso_PhasePt} (hq : IsBlowupPhasePt q) :
    fullerCoords q = 0 ↔ q = singularPhasePt := by
  constructor
  · intro h
    rw [← phaseOfFuller_fullerCoords hq, h]
    have hj : jbr 0 = 1 := by simp [jbr]
    simp only [phaseOfFuller, Pi.zero_apply, mul_zero, hj, singularPhasePt, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [J, RR]
  · rintro rfl
    ext k; fin_cases k <;> apply Complex.ext <;> simp [fullerCoords, singularPhasePt, cayleyZ, J]

/-- `fullerCoords` is continuous, and `phaseOfFuller` is continuous (indeed real analytic). -/
theorem continuous_fullerCoords_phaseOfFuller :
    Continuous fullerCoords ∧ Continuous phaseOfFuller := by
  have hc : Continuous cayleyZ := by
    have : cayleyZ = fun M : Mat2 ↦
        (((M 0 1 + M 1 0) / 2 : ℝ) : ℂ) + ((M 0 0 : ℝ) : ℂ) * I := funext cayleyZ_eq
    rw [this]
    have h : ∀ i j : Fin 2, Continuous fun M : Mat2 ↦ M i j :=
      fun i j ↦ continuous_id.matrix_elem i j
    fun_prop
  have hj : Continuous jbr := by
    unfold jbr; fun_prop
  constructor
  · refine continuous_pi fun k ↦ ?_
    fin_cases k
    · exact (hc.comp continuous_fst).div_const _
    · exact (continuous_const.mul (hc.comp (continuous_fst.comp continuous_snd))).div_const _
    · exact (hc.comp (continuous_snd.comp continuous_snd)).div_const _
  · have h0 : Continuous fun z : Fin 3 → ℂ ↦ z 0 := continuous_apply 0
    have h1 : Continuous fun z : Fin 3 → ℂ ↦ z 1 := continuous_apply 1
    have h2 : Continuous fun z : Fin 3 → ℂ ↦ z 2 := continuous_apply 2
    have hRR : Continuous fun p : ℂ × ℂ ↦ RR p.1 p.2 := by
      simp only [RR_eq_re_mul_add_im_mul]; fun_prop
    have hR : Continuous fun z : Fin 3 → ℂ ↦ RR (2 * z 0) (12 * z 2) / jbr (2 * z 0) := by
      refine Continuous.div (hRR.comp (f := fun z : Fin 3 → ℂ ↦ (2 * z 0, 12 * z 2))
        (by fun_prop)) (hj.comp (f := fun z : Fin 3 → ℂ ↦ 2 * z 0) (by fun_prop)) ?_
      intro z; exact (jbr_pos _).ne'
    have hj0 : Continuous fun z : Fin 3 → ℂ ↦ jbr (2 * z 0) := hj.comp (by fun_prop)
    have hj1 : Continuous fun z : Fin 3 → ℂ ↦ jbr (4 * I * z 1) := hj.comp (by fun_prop)
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_) <;>
      refine continuous_matrix fun i j ↦ ?_ <;> fin_cases i <;> fin_cases j <;>
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one] <;> fun_prop

/-! ### The time reversal: matrix algebra

`matTau M = -D M D` with `D = diag(1, -1)`, `D² = 1`: conjugation by `D` is an algebra
automorphism commuting with `exp`, and `matTau` is minus it, so it reverses commutators
(`τ[A, B] = -[τA, τB]`) and preserves the trace form. -/

private theorem l6b_matTau_eq (M : Mat2) : matTau M = -(diagD * M * diagD) := by
  rw [Matrix.eta_fin_two M]
  ext i j; fin_cases i <;> fin_cases j <;> simp [matTau, diagD]

private theorem l6b_diagD_mul_self : diagD * diagD = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diagD]

private theorem l6b_diagD_inv : diagD⁻¹ = diagD := Matrix.inv_eq_left_inv l6b_diagD_mul_self

theorem matTau_matTau (M : Mat2) : matTau (matTau M) = M := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matTau]

theorem matTau_add (A B : Mat2) : matTau (A + B) = matTau A + matTau B := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matTau] <;> ring

theorem matTau_sub (A B : Mat2) : matTau (A - B) = matTau A - matTau B := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matTau] <;> ring

theorem matTau_smul (c : ℝ) (A : Mat2) : matTau (c • A) = c • matTau A := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matTau]

theorem matTau_J : matTau J = J := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matTau, J]

theorem traceForm_matTau (A B : Mat2) : traceForm (matTau A) (matTau B) = traceForm A B := by
  simp [traceForm, matTau, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

theorem trace_matTau (A : Mat2) : (matTau A).trace = -A.trace := by
  simp [matTau, Matrix.trace, Fin.sum_univ_two]; ring

private theorem l6b_det_matTau (A : Mat2) : (matTau A).det = A.det := by
  simp [matTau, Matrix.det_fin_two]

theorem vertexSwap_vertexSwap (m : Fin 3) : vertexSwap (vertexSwap m) = m := by
  fin_cases m <;> rfl

private theorem l6b_matTau_controlMatrix_vertex (m : Fin 3) :
    matTau (controlMatrix (vertex (vertexSwap m))) = controlMatrix (vertex m) := by
  fin_cases m <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [matTau, controlMatrix, vertex, vertexSwap] <;> ring

private theorem l6b_controlP_matTau (m : Fin 3) (X : Mat2) :
    controlP (vertex m) (matTau X) = matTau (controlP (vertex (vertexSwap m)) X) := by
  rw [controlP, controlP, matTau_smul, l6b_matTau_controlMatrix_vertex,
    ← l6b_matTau_controlMatrix_vertex m, traceForm_matTau]

private theorem l6b_cayleyZ_matTau (M : Mat2) : cayleyZ (matTau M) = starRingEnd ℂ (cayleyZ M) := by
  apply Complex.ext <;> simp [cayleyZ, matTau]

/-- The time reversal `M ↦ -D M D` preserves the star states (it exchanges `ρ₀` and `ρ₁`). -/
theorem isStarState_matTau {X : Mat2} (h : IsStarState X) : IsStarState (matTau X) := by
  obtain ⟨htr, hdet, h0, h1, h2⟩ := h
  refine ⟨by rw [trace_matTau, htr, neg_zero], ?_, ?_, ?_, ?_⟩
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

/-- Conjugation by `D = diag(1, -1)`. -/
private def l6b_conjD (A : Mat2) : Mat2 := diagD * A * diagD

private theorem l6b_matTau_eq_neg_conjD (A : Mat2) : matTau A = -l6b_conjD A := by
  rw [l6b_matTau_eq, l6b_conjD]

private theorem l6b_conjD_mul (A B : Mat2) : l6b_conjD (A * B) = l6b_conjD A * l6b_conjD B := by
  simp only [l6b_conjD, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc diagD diagD, l6b_diagD_mul_self, Matrix.one_mul]

private theorem l6b_conjD_add (A B : Mat2) : l6b_conjD (A + B) = l6b_conjD A + l6b_conjD B := by
  simp only [l6b_conjD, Matrix.mul_add, Matrix.add_mul]

private theorem l6b_conjD_sub (A B : Mat2) : l6b_conjD (A - B) = l6b_conjD A - l6b_conjD B := by
  simp only [l6b_conjD, Matrix.mul_sub, Matrix.sub_mul]

private theorem l6b_conjD_neg (A : Mat2) : l6b_conjD (-A) = -l6b_conjD A := by
  simp only [l6b_conjD, Matrix.mul_neg, Matrix.neg_mul]

private theorem l6b_conjD_smul (c : ℝ) (A : Mat2) : l6b_conjD (c • A) = c • l6b_conjD A := by
  simp only [l6b_conjD, Matrix.mul_smul, Matrix.smul_mul]

private theorem l6b_conjD_J : l6b_conjD J = -J := by
  rw [← neg_neg (l6b_conjD J), ← l6b_matTau_eq_neg_conjD, matTau_J]

private theorem l6b_conjD_inv (A : Mat2) : (l6b_conjD A)⁻¹ = l6b_conjD A⁻¹ := by
  simp only [l6b_conjD, Matrix.mul_inv_rev, l6b_diagD_inv, Matrix.mul_assoc]

private theorem l6b_isUnit_diagD : IsUnit diagD :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (by simp [diagD, Matrix.det_fin_two])

private theorem l6b_exp_smul_matTau (s : ℝ) (A : Mat2) :
    NormedSpace.exp (s • matTau A) = l6b_conjD (NormedSpace.exp ((-s) • A)) := by
  have h : s • matTau A = diagD * ((-s) • A) * diagD⁻¹ := by
    rw [l6b_diagD_inv, l6b_matTau_eq_neg_conjD, l6b_conjD, Matrix.mul_smul, Matrix.smul_mul,
      neg_smul, smul_neg]
  rw [h, Matrix.exp_conj _ _ l6b_isUnit_diagD, l6b_diagD_inv, l6b_conjD]

private theorem l6b_traceForm_conjD (A B : Mat2) :
    traceForm (l6b_conjD A) (l6b_conjD B) = traceForm A B := by
  have := traceForm_matTau A B
  rwa [l6b_matTau_eq_neg_conjD, l6b_matTau_eq_neg_conjD, traceForm, neg_mul_neg] at this

private theorem l6b_conjD_apply (A : Mat2) (i j : Fin 2) :
    l6b_conjD A i j = ![1, -1] i * ![1, -1] j * A i j := by
  rw [Matrix.eta_fin_two A]
  fin_cases i <;> fin_cases j <;> simp [l6b_conjD, diagD]

private theorem l6b_integral_conjD_comp_neg (B : ℝ → Mat2) (t : ℝ) :
    (Matrix.of fun i j ↦ ∫ s in (0 : ℝ)..t, l6b_conjD (B (-s)) i j) =
      -l6b_conjD (Matrix.of fun i j ↦ ∫ s in (0 : ℝ)..(-t), B s i j) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.neg_apply, l6b_conjD_apply,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_neg (fun s ↦ B s i j),
    neg_zero]
  rw [intervalIntegral.integral_symm]
  ring

private theorem l6b_integral_comp_neg' (f : ℝ → ℝ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, f (-s) = -∫ s in (0 : ℝ)..(-t), f s := by
  rw [intervalIntegral.integral_comp_neg, neg_zero, intervalIntegral.integral_symm]

private theorem l6b_matTau_comm (A B : Mat2) :
    matTau A * matTau B - matTau B * matTau A = l6b_conjD (A * B - B * A) := by
  simp only [l6b_matTau_eq_neg_conjD, neg_mul_neg, l6b_conjD_sub, l6b_conjD_mul]

private theorem l6b_conj_final (E₁ E₂ A K N : Mat2) (c : ℝ) :
    l6b_conjD E₁ * (-l6b_conjD A - (-c) • l6b_conjD K - -l6b_conjD N) * l6b_conjD E₂ =
      matTau (E₁ * (A - c • K - N) * E₂) := by
  simp only [l6b_matTau_eq_neg_conjD, l6b_conjD_mul, l6b_conjD_sub, l6b_conjD_smul, neg_smul,
    sub_neg_eq_add, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, smul_mul_assoc,
    mul_smul_comm]
  abel

/-! ### The rotation `Ad_R` in Cayley coordinates

`fullerCoords_adR` needs the entries of the phase point traceless: otherwise it fails
(`l6b_not_fullerCoords_adR`, with `q = (1, 0, 0)`: `cayleyZ 1 = i` is fixed by `Ad_R`). -/

private theorem l6b_cayleyZ_adR (M : Mat2) (hM : M.trace = 0) :
    cayleyZ (R * M * R⁻¹) = ζ ^ 2 * cayleyZ M := by
  have h11 : M 1 1 = -M 0 0 := by rw [Matrix.trace_fin_two] at hM; linarith
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [poly_R_inv, Matrix.eta_fin_two M, h11]
  apply Complex.ext
  · simp [cayleyZ, R, Complex.mul_re, ζ_sq_re, ζ_sq_im]
    linear_combination (-(1 / 8) * (M 0 1 + M 1 0)) * h3
  · simp [cayleyZ, R, Complex.mul_im, ζ_sq_re, ζ_sq_im]
    linear_combination (-(1 / 4) * M 0 0) * h3

private theorem l6b_cayleyZ_adRinv (M : Mat2) (hM : M.trace = 0) :
    cayleyZ (R⁻¹ * M * R) = ζ * cayleyZ M := by
  have h11 : M 1 1 = -M 0 0 := by rw [Matrix.trace_fin_two] at hM; linarith
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [poly_R_inv, Matrix.eta_fin_two M, h11]
  apply Complex.ext
  · simp [cayleyZ, R, Complex.mul_re, ζ_re, ζ_im]
    linear_combination (-(1 / 8) * (M 0 1 + M 1 0)) * h3
  · simp [cayleyZ, R, Complex.mul_im, ζ_re, ζ_im]
    linear_combination (-(1 / 4) * M 0 0) * h3

/-- `Ad_R` and `Ad_{R⁻¹}` in Fuller coordinates, for traceless entries (the proof of
`fullerCoords_adR`; without the traces the identity fails, `l6b_not_fullerCoords_adR`). -/
private theorem l6b_fullerCoords_adR (q : iso_PhasePt) (h1 : q.1.trace = 0) (h2 : q.2.1.trace = 0)
    (h3 : q.2.2.trace = 0) :
    fullerCoords (iso_adR q) = ζ ^ 2 • fullerCoords q ∧
      fullerCoords (iso_adRinvPow 1 q) = ζ • fullerCoords q := by
  constructor
  · ext k; fin_cases k <;>
      simp [fullerCoords, iso_adR, l6b_cayleyZ_adR _ h1, l6b_cayleyZ_adR _ h2,
        l6b_cayleyZ_adR _ h3] <;> ring
  · ext k; fin_cases k <;>
      simp [fullerCoords, iso_adRinvPow, l6b_cayleyZ_adRinv _ h1, l6b_cayleyZ_adRinv _ h2,
        l6b_cayleyZ_adRinv _ h3] <;> ring

/-- `fullerCoords_adR` fails for phase points with non-traceless entries: `q = (1, 0, 0)`. -/
private theorem l6b_not_fullerCoords_adR :
    ¬ ∀ q : iso_PhasePt, fullerCoords (iso_adR q) = ζ ^ 2 • fullerCoords q := by
  intro h
  have := congrFun (h (1, 0, 0)) 0
  have hR : R * 1 * R⁻¹ = 1 := by rw [Matrix.mul_one, poly_R_mul_inv]
  simp only [fullerCoords, iso_adR, hR, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul] at this
  have hc : cayleyZ 1 = I := by apply Complex.ext <;> simp [cayleyZ]
  rw [hc] at this
  have := congrArg Complex.im this
  simp [Complex.mul_im, ζ_sq_re, ζ_sq_im] at this
  norm_num at this

/-! ### The symmetries in Fuller coordinates -/

/-- **The cyclic symmetry**: "In Lie algebra coordinates, the rotational group action by the cyclic
group of order three is the action by powers of `Ad_R`" (TeX 11548–11550). In Fuller coordinates
`Ad_R` is multiplication by `ζ² = ζ⁻¹` and `Ad_{R⁻¹}` by `ζ` (the action of `V_T`). The book's
phase points lie in `sl₂(ℝ)`; the hypotheses that the three entries are traceless make that
explicit (`cayleyZ` reads only three entries, so without them the identity fails, e.g. at
`q = (1, 0, 0)`: `l6b_not_fullerCoords_adR`). -/
theorem fullerCoords_adR (q : iso_PhasePt) (h1 : q.1.trace = 0) (h2 : q.2.1.trace = 0)
    (h3 : q.2.2.trace = 0) :
    fullerCoords (iso_adR q) = ζ ^ 2 • fullerCoords q ∧
      fullerCoords (iso_adRinvPow 1 q) = ζ • fullerCoords q :=
  l6b_fullerCoords_adR q h1 h2 h3

/-- **The time reversal in Fuller coordinates** (Remark 10.2.3 and (11.2.4)): conjugating
`(w, b, c)` is `τ(z₁, z₂, z₃) = (z̄₁, -z̄₂, z̄₃)` of Chapter 13. -/
theorem fullerCoords_reinTau (q : iso_PhasePt) :
    fullerCoords (reinTau q) = tau (fullerCoords q) := by
  ext k
  fin_cases k <;>
    simp [fullerCoords, reinTau, tau, l6b_cayleyZ_matTau, map_div₀, map_ofNat]; ring

/-- `reinTau` is an involution, preserves the phase points of the blow-up and the singular point,
and conjugates `Ad_R` to `Ad_{R⁻¹}`. -/
theorem reinTau_spec :
    (∀ q, reinTau (reinTau q) = q) ∧ (∀ q, IsBlowupPhasePt q → IsBlowupPhasePt (reinTau q)) ∧
      reinTau singularPhasePt = singularPhasePt ∧
      ∀ q, reinTau (iso_adR q) = iso_adRinvPow 1 (reinTau q) := by
  refine ⟨fun q ↦ ?_, fun q hq ↦ ?_, ?_, fun q ↦ ?_⟩
  · simp [reinTau, matTau_matTau]
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [reinTau, trace_matTau, l6b_det_matTau, traceForm_matTau] <;>
      simp_all [matTau]
  · simp only [reinTau, singularPhasePt, matTau_J, matTau_smul, Prod.mk.injEq, true_and]
    ext i j; fin_cases i <;> fin_cases j <;> simp [matTau]
  · have key : ∀ M : Mat2, matTau (R * M * R⁻¹) = R⁻¹ * matTau M * R := by
      intro M
      rw [poly_R_inv, Matrix.eta_fin_two M]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [matTau, R] <;> ring
    simp [reinTau, iso_adR, iso_adRinvPow, key]

/-- **Time reversal of the vertex flows** (Remark 10.2.3 for triangular control; the Reinhardt
analogue of Lemma 13.2.3): the flow with the control `e_m` from `τ(q)` is the time reversal of the
flow with the control `τ(e_m)` (`e₂ ↔ e₃`) from `q`:
`iso_vertexFlow m (τ q) t = τ (iso_vertexFlow (vertexSwap m) q (-t))` (an identity of the closed
forms, for every `q`: `⟨Z_{e_m}, -DXD⟩ = ⟨Z_{τ e_m}, X⟩`, so both sides use the same scalar in
`P = Z/⟨Z, X₀⟩`; checked numerically against the ODE). -/
theorem iso_vertexFlow_reinTau (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    iso_vertexFlow m (reinTau q) t = reinTau (iso_vertexFlow (vertexSwap m) q (-t)) := by
  obtain ⟨X, Λ₁, ΛR⟩ := q
  set P := iso_vfP (vertexSwap m) (X, Λ₁, ΛR) with hPdef
  set τq : iso_PhasePt := (matTau X, matTau Λ₁, matTau ΛR) with hτq
  have hτ : reinTau (X, Λ₁, ΛR) = τq := rfl
  rw [hτ]
  have hP : iso_vfP m τq = matTau P := l6b_controlP_matTau m X
  have hG : ∀ s, iso_vfG m τq s = l6b_conjD (iso_vfG (vertexSwap m) (X, Λ₁, ΛR) (-s)) := by
    intro s
    rw [iso_vfG, iso_vfG, constControlG, constControlG, hP]
    change NormedSpace.exp (s • (matTau X + matTau P)) * NormedSpace.exp ((-s) • matTau P) = _
    rw [← matTau_add, l6b_exp_smul_matTau, l6b_exp_smul_matTau, neg_neg, l6b_conjD_mul]
  have hΛ₁ : ∀ s, iso_vfΛ₁ m τq s = matTau (iso_vfΛ₁ (vertexSwap m) (X, Λ₁, ΛR) (-s)) := by
    intro s
    rw [iso_vfΛ₁, hG, l6b_conjD_inv]
    change l6b_conjD _ * matTau Λ₁ * l6b_conjD _ = _
    rw [l6b_matTau_eq_neg_conjD, l6b_matTau_eq_neg_conjD, mul_neg, neg_mul, ← l6b_conjD_mul,
      ← l6b_conjD_mul]
    rfl
  have hM : ∀ s, iso_vfM m τq s = matTau (iso_vfM (vertexSwap m) (X, Λ₁, ΛR) (-s)) := by
    intro s
    have hJ : matTau (iso_vfΛ₁ (vertexSwap m) (X, Λ₁, ΛR) (-s)) + (3 / 2 : ℝ) • J =
        -l6b_conjD (iso_vfΛ₁ (vertexSwap m) (X, Λ₁, ΛR) (-s) + (3 / 2 : ℝ) • J) := by
      rw [l6b_matTau_eq_neg_conjD, l6b_conjD_add, l6b_conjD_smul, l6b_conjD_J, smul_neg,
        neg_add, neg_neg]
    rw [iso_vfM, iso_vfM, hΛ₁, hP, hJ, l6b_exp_smul_matTau, l6b_exp_smul_matTau, neg_neg,
      l6b_matTau_eq_neg_conjD, mul_neg, neg_mul, l6b_conjD_mul, l6b_conjD_mul]
  have hC : ∀ σ, iso_vfC m τq σ = iso_vfC (vertexSwap m) (X, Λ₁, ΛR) (-σ) := by
    intro σ
    have hint : ∀ s, traceForm (iso_vfM m τq s) (τq.1 * iso_vfP m τq - iso_vfP m τq * τq.1) =
        -traceForm (iso_vfM (vertexSwap m) (X, Λ₁, ΛR) (-s)) (X * P - P * X) := by
      intro s
      rw [hM, hP]
      change traceForm _ (matTau X * matTau P - matTau P * matTau X) = _
      rw [l6b_matTau_comm, l6b_matTau_eq_neg_conjD (iso_vfM _ _ _), traceForm, Matrix.neg_mul,
        Matrix.trace_neg, ← traceForm, l6b_traceForm_conjD]
    rw [iso_vfC, iso_vfC]
    simp only [hint, intervalIntegral.integral_neg]
    rw [hP]
    rw [l6b_integral_comp_neg' (fun s ↦ traceForm (iso_vfM (vertexSwap m) (X, Λ₁, ΛR) s)
      (X * P - P * X)) σ]
    change traceForm (matTau ΛR) (matTau P) - _ = _
    rw [traceForm_matTau, neg_neg]
  have hτ1 : τq.1 = matTau X := rfl
  have hX : iso_vfX m τq t = matTau (iso_vfX (vertexSwap m) (X, Λ₁, ΛR) (-t)) := by
    rw [iso_vfX, constControlX, hP, hτ1, l6b_exp_smul_matTau, l6b_exp_smul_matTau,
      l6b_matTau_eq_neg_conjD X, mul_neg, neg_mul, ← l6b_conjD_mul, ← l6b_conjD_mul,
      ← l6b_matTau_eq_neg_conjD]
    rfl
  have hint2 : (Matrix.of fun i j ↦ ∫ s in (0 : ℝ)..t,
      (iso_vfM m τq s * τq.1 - τq.1 * iso_vfM m τq s) i j) =
      -l6b_conjD (Matrix.of fun i j ↦ ∫ s in (0 : ℝ)..(-t),
        (iso_vfM (vertexSwap m) (X, Λ₁, ΛR) s * X - X * iso_vfM (vertexSwap m) (X, Λ₁, ΛR) s)
          i j) := by
    simp only [hM, hτ1, l6b_matTau_comm]
    exact l6b_integral_conjD_comp_neg (fun s ↦
      iso_vfM (vertexSwap m) (X, Λ₁, ΛR) s * X - X * iso_vfM (vertexSwap m) (X, Λ₁, ΛR) s) t
  have hΛR : iso_vfΛR m τq t = matTau (iso_vfΛR (vertexSwap m) (X, Λ₁, ΛR) (-t)) := by
    rw [iso_vfΛR, hint2]
    simp only [hC]
    rw [l6b_integral_comp_neg' (fun σ ↦ iso_vfC (vertexSwap m) (X, Λ₁, ΛR) σ) t, hP, hτ1]
    change NormedSpace.exp (t • matTau P) *
      (matTau ΛR - _ • (matTau P * matTau X - matTau X * matTau P) - _) *
        NormedSpace.exp ((-t) • matTau P) = _
    rw [l6b_matTau_comm, l6b_exp_smul_matTau, l6b_exp_smul_matTau, l6b_matTau_eq_neg_conjD ΛR,
      l6b_conj_final]
    rfl
  change (iso_vfX m τq t, iso_vfΛ₁ m τq t, iso_vfΛR m τq t) =
    (matTau (iso_vfX (vertexSwap m) (X, Λ₁, ΛR) (-t)),
      matTau (iso_vfΛ₁ (vertexSwap m) (X, Λ₁, ΛR) (-t)),
      matTau (iso_vfΛR (vertexSwap m) (X, Λ₁, ΛR) (-t)))
  rw [hX, hΛ₁, hΛR]

/-- The time reversal exchanges the switching functions as the controls: `χ_ij(τ q) = χ_{τi,τj}(q)`
(`-D Z_{e_m} D = Z_{e_{vertexSwap m}}`, `⟨-DAD, -DBD⟩ = ⟨A, B⟩`), and preserves the Hamiltonians
the same way. -/
theorem switchingFn_reinTau (i j : Fin 3) (q : iso_PhasePt) :
    switchingFn i j (reinTau q).2.2 (reinTau q).1 =
      switchingFn (vertexSwap i) (vertexSwap j) q.2.2 q.1 ∧
    hamiltonian (-1) (reinTau q).2.1 (reinTau q).2.2 (reinTau q).1 (vertex i) =
      hamiltonian (-1) q.2.1 q.2.2 q.1 (vertex (vertexSwap i)) := by
  constructor
  · simp only [switchingFn, reinTau, l6b_controlP_matTau, ← matTau_sub, traceForm_matTau]
  · have h : matTau q.2.1 - (3 / 2 * -1 : ℝ) • J = matTau (q.2.1 - (3 / 2 * -1 : ℝ) • J) := by
      rw [matTau_sub, matTau_smul, matTau_J]
    simp only [hamiltonian, reinTau]
    rw [h, ← l6b_matTau_controlMatrix_vertex i, traceForm_matTau, traceForm_matTau,
      traceForm_matTau]

/-! ### The time reversal on the chart

`τ(lieChart(r, x̃)) = lieChart(-r, σ x̃)` with `σ(x̃₂₁, ℓ̃₁₁, ℓ̃₂₁) = (-x̃₂₁, -ℓ̃₁₁, ℓ̃₂₁)`:
entrywise for `X` and `Λ₁`; for `Λ_R`, `τ` fixes `J` and the trace form and exchanges `Z_{e₂}`
and `Z_{e₃}`, so it maps the solution of (14.1.3) to the solution of (14.1.3) (`τ[A, B] = [τB, τA]`
in the dual basis `sl2Dual`). So the mirrored chart is the chart at the reflected coordinates, and
the Reinhardt–Poincaré map moving backwards in time near `q_out` is the forward one at the reflected
point (Lemma 14.3.1, Step 10). -/

/-- The reflection of the chart coordinates by the time reversal,
`(r, x̃₂₁, ℓ̃₁₁, ℓ̃₂₁) ↦ (-r, -x̃₂₁, -ℓ̃₁₁, ℓ̃₂₁)` (`lieChart_chartReflect`). -/
noncomputable def chartReflect (p : ℝ × (Fin 3 → ℝ)) : ℝ × (Fin 3 → ℝ) :=
  (-p.1, ![-p.2 0, -p.2 1, p.2 2])

theorem chartReflect_chartReflect (p : ℝ × (Fin 3 → ℝ)) : chartReflect (chartReflect p) = p := by
  obtain ⟨r, x⟩ := p
  simp only [chartReflect, neg_neg, Prod.mk.injEq, true_and]
  funext i
  fin_cases i <;> simp

private theorem l6s_matTau_lieX (r x : ℝ) : matTau (lieX r x) = lieX (-r) (-x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matTau, lieX]

private theorem l6s_matTau_lieΛ₁ (r l m : ℝ) : matTau (lieΛ₁ r l m) = lieΛ₁ (-r) (-l) m := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matTau, lieΛ₁, show (-r) ^ 4 = r ^ 4 by ring]

private theorem l6s_matTau_bracket (A B : Mat2) :
    matTau (A * B - B * A) = matTau B * matTau A - matTau A * matTau B := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matTau, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

private theorem l6s_matTau_sl2Dual (M₁ M₂ M₃ : Mat2) (c₁ c₂ c₃ : ℝ) :
    matTau (sl2Dual M₁ M₂ M₃ c₁ c₂ c₃) =
      sl2Dual (matTau M₁) (matTau M₃) (matTau M₂) c₁ c₃ c₂ := by
  have hT : traceForm (matTau M₁) (matTau M₃ * matTau M₂ - matTau M₂ * matTau M₃) =
      traceForm M₁ (M₂ * M₃ - M₃ * M₂) := by
    rw [← l6s_matTau_bracket, traceForm_matTau]
  simp only [sl2Dual, hT, matTau_smul, matTau_add, l6s_matTau_bracket]
  congr 1
  abel

private theorem l6s_reducedHam_matTau (Λ₁ X : Mat2) :
    reducedHam (matTau Λ₁) (matTau X) = reducedHam Λ₁ X := by
  have h : matTau Λ₁ + (3 / 2 : ℝ) • J = matTau (Λ₁ + (3 / 2 : ℝ) • J) := by
    rw [matTau_add, matTau_smul, matTau_J]
  rw [reducedHam, reducedHam, h, traceForm_matTau]

private theorem l6s_lieΛR_matTau (X Λ₁ : Mat2) :
    lieΛR (matTau X) (matTau Λ₁) = matTau (lieΛR X Λ₁) := by
  have e1 : matTau (controlMatrix (vertex 2)) = controlMatrix (vertex 1) :=
    l6b_matTau_controlMatrix_vertex 1
  have e2 : matTau (controlMatrix (vertex 1)) = controlMatrix (vertex 2) :=
    l6b_matTau_controlMatrix_vertex 2
  have t1 : traceForm (matTau X) (controlMatrix (vertex 1)) =
      traceForm X (controlMatrix (vertex 2)) := by rw [← e1, traceForm_matTau]
  have t2 : traceForm (matTau X) (controlMatrix (vertex 2)) =
      traceForm X (controlMatrix (vertex 1)) := by rw [← e2, traceForm_matTau]
  rw [lieΛR, lieΛR, l6s_matTau_sl2Dual, e1, e2, l6s_reducedHam_matTau, t1, t2]

/-- **The time reversal on the chart**: `τ(lieChart(r, x̃)) = lieChart(-r, σ x̃)`
(`lieChartIn = lieChart ∘ chartReflect`). -/
theorem lieChart_chartReflect (p : ℝ × (Fin 3 → ℝ)) :
    lieChart (chartReflect p) = reinTau (lieChart p) := by
  obtain ⟨r, x⟩ := p
  simp only [lieChart, chartReflect, reinTau, l6s_matTau_lieX, l6s_matTau_lieΛ₁,
    ← l6s_lieΛR_matTau]
  simp

/-- The inverse of the chart commutes with the time reversal:
`lieChartInv (τ q) = σ (lieChartInv q)` (`lieChartInInv = chartReflect ∘ lieChartInv`). -/
theorem lieChartInv_reinTau (q : iso_PhasePt) :
    lieChartInv (reinTau q) = chartReflect (lieChartInv q) := by
  refine Prod.ext (by simp [lieChartInv, reinTau, chartReflect, matTau]) ?_
  funext i
  fin_cases i <;> simp [lieChartInv, reinTau, chartReflect, matTau, div_neg, neg_div]

/-- `lieChartInv` recovers the chart coordinates for every `r ≠ 0` (on `H*`: `lieChart_spec`). -/
theorem lieChartInv_lieChart_of_ne {p : ℝ × (Fin 3 → ℝ)} (hp : p.1 ≠ 0) :
    lieChartInv (lieChart p) = p := by
  obtain ⟨r, x⟩ := p
  simp only at hp
  refine Prod.ext (by simp [lieChartInv, lieChart, lieX]) ?_
  funext i
  fin_cases i <;> simp [lieChartInv, lieChart, lieX, lieΛ₁] <;> field_simp

end SmoothedPolygons
