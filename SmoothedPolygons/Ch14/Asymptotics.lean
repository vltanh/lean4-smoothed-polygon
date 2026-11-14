module

public import SmoothedPolygons.Ch14.LieChart
public import SmoothedPolygons.Ch15.CellCoordinates

/-!
# Chapter 14: asymptotics near the singular locus (§14.2)

§14.2 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Asymptotics", `sec:asymptotic`,
TeX 11606–11758): the leading terms of the Reinhardt system in the Lie algebra chart are the Fuller
system.

* `zhat p = fullerCoords (lieChart p)`: the Fuller coordinates `ẑ(r, x̃)` of the chart
  (TeX 11616–11630), and their expansions (TeX 11631–11645, `zhat_isBigO`);
* `fullerOfChart x̃ = z(x̃)`: the limit `lim_{r→0} (ẑ₁/r, ẑ₂/r², ẑ₃/r³)` (TeX 11646–11650: "This
  limit exists and is nonzero", `tendsto_zhat_div`), which is
  `((x̃₂₁ + i)/2, (ℓ̃₁₁ - i ℓ̃₂₁)/6, (ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁)/6)`; its angular component `ξ(x̃)`
  (`xiOfChart`);
* the asymptotic relation between the Hamiltonians, `H(Z_{e_j}, X, Λ₁, Λ_R) = 24 r³ H_F(z(x̃),
  ζ^{j-1}) + O(r⁴)` (TeX 11652–11658, `hamiltonian_lieChart_isBigO`), and
  `H_F(z(x̃), ζ) = H_F(z(x̃), ζ²) = 0` (TeX 11663–11666, `ham_fullerOfChart`);
* the inverse `fullerChartInv` of `x̃ ↦ z(x̃)` up to the virial group (Remark 14.2.1's formula), and
  `x̃_out = fullerChartInv qOutCart` (`xTildeOut`; Remark 14.2.1, `remark14_2_1`);
* the first control `e₂` for small `r` (TeX 11706–11718, `eventually_firstControl_lieChart`);
* Lemma 14.2.3 (`lem:Lie-Fuller`, `lemma14_2_3`) and Lemma 14.2.4 (`lem:chi-asymptotic`,
  `lemma14_2_4`), with the companion formula for `χ₂₃` ("Similar formulas hold for the other
  switching functions", `lemma14_2_4_chi23`), which the proof of Lemma 14.3.1 needs (G14.5).

The Fuller control `ζ^{j-1}` corresponds to the Reinhardt vertex `e_j` (TeX 11655–11657), so the
vertex `vertex m` (`e_{m+1}`) corresponds to `ζ ^ m`. In the book's normalization the switching
function from `ζ` to `1` is `RR(ζ - 1, z₃)` (without the factor `1/√3` of Chapter 13's
`switchingFunction`), and `24 = 6ρ²`.

## Restatements

* `z(x̃)` is defined by its explicit value, and `tendsto_zhat_div` states that it is the book's
  limit (the book's definition); `ẑ₃`'s expansion is stated with the `r`-dependent
  `ℓ̃_R = Λ_R/r³` as printed.
* Lemma 14.2.3 is printed "for each `s` such that `r(s) < 1`"; for fixed `s` the condition holds
  for all small `r₀` (the chart coordinate along the flow tends to `0`), so it is dropped. The
  `O`-constants depend on `s` and `x̃⁰`, as printed; the uniformity the proof of Lemma 14.3.1
  needs (G14.4) is provided there by analyticity (`analyticAt_rescaledChi`,
  `SmoothedPolygons/Ch14/AnalyticExtension.lean`).
* "`ξ(x̃) ∈ Ξ_{𝒲,0}`" (TeX 11612–11649) holds only when `ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁ ≤ 0` (a slip; see
  `xiOfChart`).
* Remark 14.2.1 prints `x̃_out ≈ (-2.39, -4.90, -1.12)`; the exact value is
  `(-2.388856…, -4.902232…, -1.126400…)`, so the third entry is `-1.13` to two decimals (a
  truncation); `remark14_2_1` states the enclosure `|x̃_out - (-2.39, -4.90, -1.12)| < 0.01`
  together with the exact identity `z(x̃_out) = λ · q_out`, `λ = 1/(2 Im q_out,₁)`, and
  `z(x̃_out) ∈ sectionZero` (so `classOf (z(x̃_out)) = q_out` is meaningful: `classOf` takes the
  junk value `q_out` off the section).

## Proofs (plan)

The static statements are exact algebra: `ẑ₁ = (X₁₂ + X₂₁)/4 + i X₁₁/2` with `X₁₁ = r`,
`X₂₁ = 1 + r x̃₂₁`, `X₁₂ = -(1 + r²)/(1 + r x̃₂₁)`; `ẑ₂ = -i((Λ₁)₁₂ + (Λ₁)₂₁)/12 + (Λ₁)₁₁/6` with
`(Λ₁)₁₂ = -(3/2) + r²(ℓ̃₂₁ + O(r²))` from `det Λ₁ = 9/4`; and `ẑ₃ = h/12 + O(r⁴)` with
`h = ⟨Λ₁ + (3/2) J, X⟩ = r³ · 2(ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁) + O(r⁴)` (the term `r² ⟨Λ̃₁, J⟩` is `O(r⁴)`
because `det Λ₁ = 9/4`), and `Λ_R = h [[0, 1], [1, 0]] + O(r⁴)` (the dual-basis formula with
`X = J + O(r)`). The Hamiltonian: `H(Z_{e_j}) = h - ⟨Λ_R, Z_{e_j}⟩/⟨X, Z_{e_j}⟩` with
`⟨J, Z_{e_j}⟩ = -2/3` and `⟨Λ_R, Z_{e_j}⟩ = (4/3) RR(ζ^{j-1}, cayleyZ Λ_R) + O(r⁴)`.
Lemmas 14.2.3–14.2.4: "Use the explicit solutions on both sides and expand as a series in `r₀`"
(TeX 11738–11740, 11757): the vertex flow is in closed form (`iso_vertexFlow`: matrix exponentials
of `t P`, `P = Z_{e₂}/⟨Z_{e₂}, X₀⟩`, and quadratures), and with `t = s r₀` every entry is a
convergent power series in `r₀` whose coefficients are polynomials in `s`; the Fuller flow
(13.2.2) is the leading term. Checked numerically (double precision, `r₀ = 10⁻², 3·10⁻³, 10⁻³`,
`s = 1, 5, 8.84`): the remainders divided by `r₀^{k+1}` are bounded. Size: 1,200–2,500 lines.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology Asymptotics
open TriFuller

/-- The Fuller coordinates `ẑ(r, x̃)` of the chart point (TeX 11616–11630). -/
noncomputable def zhat (p : ℝ × (Fin 3 → ℝ)) : Fin 3 → ℂ := fullerCoords (lieChart p)

/-- `z(x̃) = lim_{r → 0} (ẑ₁/r, ẑ₂/r², ẑ₃/r³)` (TeX 11646–11650), explicitly
`((x̃₂₁ + i x̃₁₁)/2, (ℓ̃₁₁ - i ℓ̃₂₁)/6, (ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁)/6)` with `x̃₁₁ = 1` (`tendsto_zhat_div`).
Its third coordinate is real; it lies on the wall `𝒲₀ = ℝ_{≤0}` when `ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁ ≤ 0`. -/
noncomputable def fullerOfChart (x : Fin 3 → ℝ) : Fin 3 → ℂ :=
  ![((x 0 : ℂ) + I) / 2, ((x 1 : ℂ) - (x 2 : ℂ) * I) / 6, (((x 1 + x 2 * x 0) / 6 : ℝ) : ℂ)]

/-- `ξ(x̃)`: the angular component of `z(x̃)` (TeX 11646–11649). The book writes
"`ξ(x̃) ∈ Ξ_{𝒲,0}`" for every `x̃ ∈ ℝ³` (TeX 11612–11649); this holds only when
`ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁ ≤ 0`: the third coordinate `(ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁)/6` of `z(x̃)` is real, and lies on
the walls `𝒲` only when it is `≤ 0` (`H_F(z(x̃), ζ) = H_F(z(x̃), ζ²) = 0` always, but
`H_F⁺ = 0` also needs `H_F(z(x̃), 1) ≤ 0`, the same sign condition). A slip, with one reading:
the chart is used near `x̃_out`, where `ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁ ≈ -2.21 < 0`. -/
noncomputable def xiOfChart (x : Fin 3 → ℝ) : Fin 3 → ℂ := ang (fullerOfChart x)

/-- The chart coordinates of a point `z` of the Fuller section with `Im z₁ > 0`: after the virial
rescaling by `λ = 1/(2 Im z₁)` (which makes `Im z₁ = 1/2`, the normalization `x̃₁₁ = 1`),
`x̃ = (Re z₁/Im z₁, 3 Re z₂/(2 (Im z₁)²), -3 Im z₂/(2 (Im z₁)²))` (the formula of Remark 14.2.1,
TeX 11671–11677). -/
noncomputable def fullerChartInv (z : Fin 3 → ℂ) : Fin 3 → ℝ :=
  ![(z 0).re / (z 0).im, 3 * (z 1).re / (2 * (z 0).im ^ 2), -(3 * (z 1).im) / (2 * (z 0).im ^ 2)]

/-- `x̃_out`, the chart coordinates of the outward fixed point `q_out` (Remark 14.2.1). -/
noncomputable def xTildeOut : Fin 3 → ℝ := fullerChartInv qOutCart

/-- **The expansions of `ẑ`** (TeX 11631–11645, "A calculation gives"): for fixed `x̃`, as
`r → 0⁺`, `ẑ₁ = (r/2)(x̃₂₁ + i x̃₁₁) + O(r²)` (`x̃₁₁ = 1`), `ẑ₂ = (r²/3!)(ℓ̃₁₁ - i ℓ̃₂₁) + O(r³)`
and `ẑ₃ = (r³/4!)(ℓ̃_{R12} + ℓ̃_{R21}) + O(r⁴)`, where `r³ ℓ̃_R = Λ_R(r, x̃)`. -/
theorem zhat_isBigO (x : Fin 3 → ℝ) :
    (fun r : ℝ ↦ zhat (r, x) 0 - (r : ℂ) / 2 * ((x 0 : ℂ) + I)) =O[𝓝[>] 0] (fun r ↦ r ^ 2) ∧
      (fun r : ℝ ↦ zhat (r, x) 1 - (r : ℂ) ^ 2 / 6 * ((x 1 : ℂ) - (x 2 : ℂ) * I))
        =O[𝓝[>] 0] (fun r ↦ r ^ 3) ∧
      (fun r : ℝ ↦ zhat (r, x) 2 -
          (((lieChart (r, x)).2.2 0 1 + (lieChart (r, x)).2.2 1 0) / 24 : ℝ))
        =O[𝓝[>] 0] (fun r ↦ r ^ 4) := by
  sorry

/-- **The limit `z(x̃)` exists and is nonzero** (TeX 11646–11650): `(ẑ₁/r, ẑ₂/r², ẑ₃/r³) → z(x̃)`
as `r → 0⁺`, and `z(x̃) ≠ 0`. -/
theorem tendsto_zhat_div (x : Fin 3 → ℝ) :
    Tendsto (fun r : ℝ ↦ ![zhat (r, x) 0 / r, zhat (r, x) 1 / r ^ 2, zhat (r, x) 2 / r ^ 3])
      (𝓝[>] 0) (𝓝 (fullerOfChart x)) ∧ fullerOfChart x ≠ 0 := by
  sorry

/-- **The Reinhardt Hamiltonians are asymptotically the Fuller Hamiltonians** (TeX 11651–11658):
`H(Z_u, X(r, x̃), Λ₁(r, x̃), Λ_R(r, x̃)) = 24 r³ H_F(ũ, z(x̃)) + O(r⁴)`, with the vertex `e_{m+1}`
corresponding to `ζ^m` (`24 = 6ρ²`; the book writes `H_F(ũ, z)`, Chapter 13 writes `H_F(z, u)`,
G14.13). -/
theorem hamiltonian_lieChart_isBigO (x : Fin 3 → ℝ) (m : Fin 3) :
    (fun r : ℝ ↦ hamiltonian (-1) (lieChart (r, x)).2.1 (lieChart (r, x)).2.2 (lieChart (r, x)).1
        (vertex m) - 24 * r ^ 3 * ham (fullerOfChart x) (ζ ^ (m : ℕ)))
      =O[𝓝[>] 0] (fun r ↦ r ^ 4) := by
  sorry

/-- "The equations (14.1.3) imply `H_F(z(x̃), ζ) = H_F(z(x̃), ζ²) = 0`" (TeX 11663–11666). -/
theorem ham_fullerOfChart (x : Fin 3 → ℝ) :
    ham (fullerOfChart x) ζ = 0 ∧ ham (fullerOfChart x) (ζ ^ 2) = 0 := by
  sorry

/-- `fullerChartInv` inverts `fullerOfChart`, and is invariant under the virial rescalings
(`r > 0`): `fullerChartInv (scale r z) = fullerChartInv z`. For a point `z` with `Im z₁ > 0`, real
`z₃` and `H_F(z, ζ) = 0`, `fullerOfChart (fullerChartInv z)` is the rescaling of `z` by
`1/(2 Im z₁)`. -/
theorem fullerChartInv_spec :
    (∀ x, fullerChartInv (fullerOfChart x) = x) ∧
      (∀ z (r : ℝ), 0 < r → fullerChartInv (scale r z) = fullerChartInv z) ∧
      ∀ z : Fin 3 → ℂ, 0 < (z 0).im → (z 2).im = 0 → ham z ζ = 0 →
        fullerOfChart (fullerChartInv z) = scale (2 * (z 0).im)⁻¹ z := by
  sorry

/-- **Remark 14.2.1** (TeX 11668–11679): with `z_{out,i} = x_i + i y_i` (the representative
(13.5.1) of `q_out`), `x̃_out = (x₁/y₁, 3x₂/(2y₁²), -3y₂/(2y₁²)) ≈ (-2.39, -4.90, -1.12)`, and
`ξ(x̃_out)` is the outward fixed point `q_out` modulo the virial group: `z(x̃_out)` is the virial
rescaling of `q_out` by `1/(2 y₁)`, and it lies in the Fuller section (`sectionZero`: on the walls,
with `H_F⁺ = 0`), so its class in `Ξ_{𝒲,0}/V_T` is `q_out`. (The exact value is
`(-2.388856…, -4.902232…, -1.126400…)`; see the module docstring.) -/
theorem remark14_2_1 :
    |xTildeOut 0 - (-2.39)| < 0.01 ∧ |xTildeOut 1 - (-4.90)| < 0.01 ∧
      |xTildeOut 2 - (-1.12)| < 0.01 ∧
      fullerOfChart xTildeOut = scale (2 * (qOutCart 0).im)⁻¹ qOutCart ∧
      VirialEquiv qOutCart (fullerOfChart xTildeOut) ∧ fullerOfChart xTildeOut ∈ sectionZero := by
  sorry

/-- **The first control is `e₂`** (TeX 11706–11718): "For a given `x̃`, the first control of
`(X(r, x̃), Λ₁(r, x̃), Λ_R(r, x̃))` is `u = e₂` for all sufficiently small `r > 0`, provided we
assume `ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁ < 0` and `ℓ̃₂₁ < 0`" (equivalently `x₃ < 0` and `y₂ > 0` for `z(x̃)`):
the constant control `e₂` maximizes the Hamiltonian along its own flow on some `[0, ε]`. -/
theorem eventually_firstControl_lieChart {x : Fin 3 → ℝ} (h₁ : x 1 + x 2 * x 0 < 0)
    (h₂ : x 2 < 0) :
    ∀ᶠ r in 𝓝[>] 0, ∃ ε > 0, ∀ t ∈ Icc 0 ε, ∀ v ∈ controlSimplex,
      hamiltonian (-1) (iso_vertexFlow 1 (lieChart (r, x)) t).2.1
          (iso_vertexFlow 1 (lieChart (r, x)) t).2.2 (iso_vertexFlow 1 (lieChart (r, x)) t).1 v ≤
        hamiltonian (-1) (iso_vertexFlow 1 (lieChart (r, x)) t).2.1
          (iso_vertexFlow 1 (lieChart (r, x)) t).2.2 (iso_vertexFlow 1 (lieChart (r, x)) t).1
          (vertex 1) := by
  sorry

/-- **Lemma 14.2.3** (`lem:Lie-Fuller`, TeX 11720–11736). Let `(X, Λ₁, Λ_R)` solve the Reinhardt
ODE with constant control `Z₀₁₀ = e₂` from the chart point `(r₀, x̃⁰)`, in rescaled time
`s = t/r₀`, and let `z(s)` solve the Fuller ODE with constant control `ζ` from `z(x̃⁰)`. Then for
each `s`, as `r₀ → 0⁺`, `ẑ_k(X(s r₀), Λ₁(s r₀), Λ_R(s r₀)) = z_k(s) r₀^k + O(r₀^{k+1})`,
`k = 1, 2, 3` ("the leading term of the solutions of the Reinhardt and Fuller systems are in
agreement"; index `k` is `Fin 3` here, `k = 0` for `z₁`). -/
theorem lemma14_2_3 (x : Fin 3 → ℝ) (s : ℝ) (k : Fin 3) :
    (fun r₀ : ℝ ↦ fullerCoords (iso_vertexFlow 1 (lieChart (r₀, x)) (s * r₀)) k -
        (r₀ : ℂ) ^ (k.val + 1) * flow s (fullerOfChart x) ζ k)
      =O[𝓝[>] 0] (fun r₀ ↦ r₀ ^ (k.val + 2)) := by
  sorry

/-- **Lemma 14.2.4** (`lem:chi-asymptotic`, (14.2.1) `eqn:cubic-sr3`, TeX 11743–11752): with the
setup of Lemma 14.2.3, `χ₂₁(X(s r₀), Λ₁(s r₀), Λ_R(s r₀)) = 24 r₀³ RR(ζ - 1, z₃(s)) + O(r₀⁴)`. The
right side is the Fuller switching function for the transition `ζ → 1`. -/
theorem lemma14_2_4 (x : Fin 3 → ℝ) (s : ℝ) :
    (fun r₀ : ℝ ↦ switchingFn 1 0 (iso_vertexFlow 1 (lieChart (r₀, x)) (s * r₀)).2.2
        (iso_vertexFlow 1 (lieChart (r₀, x)) (s * r₀)).1 -
        24 * r₀ ^ 3 * RR (ζ - 1) (flow s (fullerOfChart x) ζ 2))
      =O[𝓝[>] 0] (fun r₀ ↦ r₀ ^ 4) := by
  sorry

/-- **The companion of Lemma 14.2.4 for `χ₂₃`** ("Similar formulas hold for the other switching
functions", TeX 11754–11755): `χ₂₃(X(s r₀), Λ₁(s r₀), Λ_R(s r₀)) = 24 r₀³ RR(ζ - ζ², z₃(s)) +
O(r₀⁴)`, the Fuller switching function for `ζ → ζ²`. -/
theorem lemma14_2_4_chi23 (x : Fin 3 → ℝ) (s : ℝ) :
    (fun r₀ : ℝ ↦ switchingFn 1 2 (iso_vertexFlow 1 (lieChart (r₀, x)) (s * r₀)).2.2
        (iso_vertexFlow 1 (lieChart (r₀, x)) (s * r₀)).1 -
        24 * r₀ ^ 3 * RR (ζ - ζ ^ 2) (flow s (fullerOfChart x) ζ 2))
      =O[𝓝[>] 0] (fun r₀ ↦ r₀ ^ 4) := by
  sorry

end SmoothedPolygons
