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
  `lieX` (the displayed matrix at TeX 11582, which is `X`, not `X̃`: G14.1), `lieΛ₁` (from
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
  (`iso_vertexFlow_reinTau`). The mirrored chart at `q_in` (G14.9) is `lieChartIn = reinTau ∘
  lieChart`.

## Proofs (plan)

Everything here is exact algebra on `2 × 2` matrices (`ext`, `simp`, `field_simp`, `ring`,
`Real.sq_sqrt`). `sl2Dual`: for traceless `M₁, M₂, M₃`, `⟨[M₂, M₃], M₂⟩ = ⟨[M₂, M₃], M₃⟩ = 0`
and `⟨[M₂, M₃], M₁⟩` is the (cyclic) triple product, so `sl2Dual` takes the prescribed values.
For `M₁ = X`, `M₂ = Z₀₁₀`, `M₃ = Z₀₀₁` the triple product is `-(8/(3√3)) X₂₁`, nonzero when
`X₂₁ = 1 + r x̃₂₁ ≥ √3 r > 0` (on `H*`). `IsBlowupPhasePt` and `phaseOfFuller`: `det X = 1` reads
`t² - |w|² = 1` for the Cayley coordinates `(t, w)`, and the sheet `X₁₂ < X₂₁` fixes `t = -⟨w⟩`;
likewise `t = (3/2) ⟨b⟩` for `Λ₁`; the diagonal of `Λ_R` is fixed by `⟨X, Λ_R⟩ = 0`. `Ad_R` is
conjugation by `diag(e^{-iπ/3}, e^{iπ/3})` after the Cayley transform. The reversal of the flows is
the uniqueness of the closed forms: `-D exp(A) D = ...`, `D Z_{e₂} D = -Z_{e₃}`, `D J D = -J`, and
the substitution `s ↦ -s` in the integrals of `iso_vfC`, `iso_vfΛR`. Size: 500–900 lines.
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
this matrix `X̃` (G14.1); it is `X`. -/
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
only the boundary `x = 1/√3` of the star domain, G14.3.) -/
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

/-- **Lemma 10.1.1** (`lem:hyperboloid-coords`, TeX 8420–8429): the Cayley transform
`A⁻¹ M A` of `M = [[a, b], [c, -a]] ∈ 𝔰𝔩₂(ℝ)` is `[[it, z], [z̄, -it]] ∈ 𝔰𝔲(1, 1)` with
`z = (b + c)/2 + ia = cayleyZ M` and `t = (b - c)/2`. ("This is an easy calculation":
`A⁻¹ = (1/√2) [[1, -i], [-i, 1]]`, multiply out.) -/
theorem lemma10_1_1 (M : Mat2) (hM : M.trace = 0) :
    cayleyA⁻¹ * M.map (fun x : ℝ ↦ (x : ℂ)) * cayleyA =
      !![I * (((M 0 1 - M 1 0) / 2 : ℝ) : ℂ), cayleyZ M;
        starRingEnd ℂ (cayleyZ M), -(I * (((M 0 1 - M 1 0) / 2 : ℝ) : ℂ))] := by
  sorry

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

/-- **The mirrored chart at `q_in`** (Remark 14.3.4, G14.9): `(r, x̃) ↦ τ(lieChart (r, x̃))`. The
chart (14.1.1)–(14.1.2) normalizes `x̃₁₁ = 1`, so `Im ẑ₁ > 0`, while `q_in = τ(q_out)` has
`Im z₁ < 0`; the mirrored chart normalizes `x̃₁₁ = -1`. -/
noncomputable def lieChartIn (p : ℝ × (Fin 3 → ℝ)) : iso_PhasePt := reinTau (lieChart p)

/-- The inverse of the mirrored chart. -/
noncomputable def lieChartInInv (q : iso_PhasePt) : ℝ × (Fin 3 → ℝ) := lieChartInv (reinTau q)

/-! ### The chart: the running claims of §14.1 -/

/-- **The chart lies on the Poincaré section** (TeX 11575–11602): for `(r, x̃) ∈ H*`, the phase
point `lieChart (r, x̃)` is a phase point of the blow-up (`det X = 1`, `det Λ₁ = 9/4`,
`⟨X, Λ_R⟩ = 0`), satisfies (14.1.3) (`H(Z₀₁₀) = 0`, `χ₂₃ = 0`), has `X = J + rX̃` with `x̃₁₁ = 1`
and `X₂₁ = 1 + r x̃₂₁ ≥ √3 r > 0` ("Hence, we may invert `1 + r x̃₂₁`"), and
`lieChartInv` recovers `(r, x̃)`. -/
theorem lieChart_spec {p : ℝ × (Fin 3 → ℝ)} (hp : p ∈ lieChartDomain) :
    IsBlowupPhasePt (lieChart p) ∧
      hamiltonian (-1) (lieChart p).2.1 (lieChart p).2.2 (lieChart p).1 (vertex 1) = 0 ∧
      switchingFn 1 2 (lieChart p).2.2 (lieChart p).1 = 0 ∧ (lieChart p).1 0 0 = p.1 ∧
      √3 * p.1 ≤ (lieChart p).1 1 0 ∧ lieChartInv (lieChart p) = p := by
  sorry

/-- **The boundary `x = 1/√3` of the star domain in the chart** (TeX 11561–11567): "Suppose
`Φ(z) = J + r X̃`, `z = x + iy ∈ 𝔥*`, with `x > 0`. We have `x̃₂₁ ≤ √3 - 1/r` if and only if
`x ≥ 1/√3`, which lies outside the star domain." (`Φ(z) = J + r X̃` with `x̃₁₁ = 1` means
`Φ(z) = lieX r x̃₂₁`, so `r = x/y` and `x̃₂₁ = (1 - y)/x`.) -/
theorem lieX_starBoundary_iff {x y r x21 : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : Φ x y = lieX r x21) : x21 ≤ √3 - 1 / r ↔ 1 / √3 ≤ x := by
  sorry

/-- **Uniqueness of the chart** (TeX 11584–11602: "`X` is determined uniquely by `r` and
`x̃₂₁` … `Λ₁` is uniquely determined … `Λ_R ∈ 𝔰𝔩₂` is uniquely determined … by the three linear
equations (14.1.3) (which is always a full rank system of linear equations for `Λ_R`) … In
summary, `(r, x̃) ∈ H*` with `r > 0` is a local coordinate for `(X, Λ₁, Λ_R)`"): a phase point of
the blow-up on the section (`H(Z₀₁₀) = 0`, `χ₂₃ = 0`), with `X` a star state and `r = X₁₁ > 0`,
is `lieChart` of its coordinates, which lie in `H*`. The full rank holds because the determinant
of the system is a nonzero multiple of `X₂₁ > 0`; the star condition makes the denominators
`⟨X, Z_u⟩` nonzero; `x̃₂₁ > √3 - 1/r` is the star condition `ρ₁(X) > 0` (`X₂₁ > √3 X₁₁`, i.e.
`x < 1/√3`, `lieX_starBoundary_iff`), and `ℓ̃₂₁ r² < 3/2` is `(Λ₁)₂₁ < 0` (from `det Λ₁ = 9/4`
and the sheet `(Λ₁)₂₁ < (Λ₁)₁₂`). -/
theorem lieChart_lieChartInv {q : iso_PhasePt} (hq : IsBlowupPhasePt q) (hX : IsStarState q.1)
    (hH : hamiltonian (-1) q.2.1 q.2.2 q.1 (vertex 1) = 0) (hχ : switchingFn 1 2 q.2.2 q.1 = 0)
    (hr : 0 < q.1 0 0) :
    lieChartInv q ∈ lieChartDomain ∧ lieChart (lieChartInv q) = q := by
  sorry

/-- **The orders of `Λ_R`** (TeX 11594–11596): for fixed `x̃`, as `r → 0⁺`, the diagonal entries
of `Λ_R(r, x̃)` are `O(r⁴)` and the off-diagonal entries `O(r³)` (so `Λ̃_R = Λ_R/r³` has a limit
with zero diagonal). -/
theorem isBigO_lieΛR (x : Fin 3 → ℝ) :
    (fun r ↦ (lieChart (r, x)).2.2 0 0) =O[𝓝[>] 0] (fun r ↦ r ^ 4) ∧
      (fun r ↦ (lieChart (r, x)).2.2 0 1) =O[𝓝[>] 0] (fun r ↦ r ^ 3) ∧
      (fun r ↦ (lieChart (r, x)).2.2 1 0) =O[𝓝[>] 0] (fun r ↦ r ^ 3) := by
  sorry

/-! ### Hyperboloid coordinates: the identification with `ℂ³` -/

/-- The Fuller coordinates of `phaseOfFuller z` are `z`. -/
theorem fullerCoords_phaseOfFuller (z : Fin 3 → ℂ) : fullerCoords (phaseOfFuller z) = z := by
  sorry

/-- `phaseOfFuller z` is a phase point of the blow-up (the form (10.1.2) "ensures that the
constraints `det(X) = 1` and `⟨X, Λ_R⟩ = 0` are satisfied", TeX 8481–8483). -/
theorem isBlowupPhasePt_phaseOfFuller (z : Fin 3 → ℂ) : IsBlowupPhasePt (phaseOfFuller z) := by
  sorry

/-- **The Fuller coordinates are coordinates on the blow-up phase points**: a phase point of the
blow-up is `phaseOfFuller` of its Fuller coordinates (the hyperboloid parametrization (10.1.2),
TeX 8484–8491). -/
theorem phaseOfFuller_fullerCoords {q : iso_PhasePt} (hq : IsBlowupPhasePt q) :
    phaseOfFuller (fullerCoords q) = q := by
  sorry

/-- "At the singular locus, we have `w = b = c = 0`" (TeX 11182–11183): a phase point of the blow-up
has Fuller coordinates `0` exactly at the singular locus `(J, -(3/2) J, 0)`. -/
theorem fullerCoords_eq_zero_iff {q : iso_PhasePt} (hq : IsBlowupPhasePt q) :
    fullerCoords q = 0 ↔ q = singularPhasePt := by
  sorry

/-- `fullerCoords` is continuous, and `phaseOfFuller` is continuous (indeed real analytic). -/
theorem continuous_fullerCoords_phaseOfFuller :
    Continuous fullerCoords ∧ Continuous phaseOfFuller := by
  sorry

/-! ### The symmetries in Fuller coordinates -/

/-- **The cyclic symmetry**: "In Lie algebra coordinates, the rotational group action by the cyclic
group of order three is the action by powers of `Ad_R`" (TeX 11548–11550). In Fuller coordinates
`Ad_R` is multiplication by `ζ² = ζ⁻¹` and `Ad_{R⁻¹}` by `ζ` (the action of `V_T`). -/
theorem fullerCoords_adR (q : iso_PhasePt) :
    fullerCoords (iso_adR q) = ζ ^ 2 • fullerCoords q ∧
      fullerCoords (iso_adRinvPow 1 q) = ζ • fullerCoords q := by
  sorry

/-- **The time reversal in Fuller coordinates** (Remark 10.2.3 and (11.2.4)): conjugating
`(w, b, c)` is `τ(z₁, z₂, z₃) = (z̄₁, -z̄₂, z̄₃)` of Chapter 13. -/
theorem fullerCoords_reinTau (q : iso_PhasePt) :
    fullerCoords (reinTau q) = tau (fullerCoords q) := by
  sorry

/-- `reinTau` is an involution, preserves the phase points of the blow-up and the singular point,
and conjugates `Ad_R` to `Ad_{R⁻¹}`. -/
theorem reinTau_spec :
    (∀ q, reinTau (reinTau q) = q) ∧ (∀ q, IsBlowupPhasePt q → IsBlowupPhasePt (reinTau q)) ∧
      reinTau singularPhasePt = singularPhasePt ∧
      ∀ q, reinTau (iso_adR q) = iso_adRinvPow 1 (reinTau q) := by
  sorry

/-- **Time reversal of the vertex flows** (Remark 10.2.3 for triangular control; the Reinhardt
analogue of Lemma 13.2.3): the flow with the control `e_m` from `τ(q)` is the time reversal of the
flow with the control `τ(e_m)` (`e₂ ↔ e₃`) from `q`:
`iso_vertexFlow m (τ q) t = τ (iso_vertexFlow (vertexSwap m) q (-t))` (an identity of the closed
forms, for every `q`: `⟨Z_{e_m}, -DXD⟩ = ⟨Z_{τ e_m}, X⟩`, so both sides use the same scalar in
`P = Z/⟨Z, X₀⟩`; checked numerically against the ODE). -/
theorem iso_vertexFlow_reinTau (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    iso_vertexFlow m (reinTau q) t = reinTau (iso_vertexFlow (vertexSwap m) q (-t)) := by
  sorry

/-- The time reversal exchanges the switching functions as the controls: `χ_ij(τ q) = χ_{τi,τj}(q)`
(`-D Z_{e_m} D = Z_{e_{vertexSwap m}}`, `⟨-DAD, -DBD⟩ = ⟨A, B⟩`), and preserves the Hamiltonians
the same way. -/
theorem switchingFn_reinTau (i j : Fin 3) (q : iso_PhasePt) :
    switchingFn i j (reinTau q).2.2 (reinTau q).1 =
      switchingFn (vertexSwap i) (vertexSwap j) q.2.2 q.1 ∧
    hamiltonian (-1) (reinTau q).2.1 (reinTau q).2.2 (reinTau q).1 (vertex i) =
      hamiltonian (-1) q.2.1 q.2.2 q.1 (vertex (vertexSwap i)) := by
  sorry

end SmoothedPolygons
