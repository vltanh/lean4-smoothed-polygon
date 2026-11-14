module

public import SmoothedPolygons.Ch14.LieChart
public import SmoothedPolygons.Ch15.CellCoordinates
public import SmoothedPolygons.Ch14.L6cAsymptoticsFlow

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

## Proofs

All statements are proved, with no `sorry` and no dependence on the unproved statements of
`LieChart.lean` (the chart is used through its definitions only). The helpers are in
`SmoothedPolygons/Ch14/L6cAsymptoticsFlow.lean`; matrix norms are the `L^∞` operator norm.

* **The chart in closed form** (TeX 11576–11602, 11631–11645, "A calculation gives"):
  `X = J + r X̃(r)`, `Λ₁ = -(3/2) J + r² Λ̃₁(r)` (with `ℓ̃₁₂` from `det Λ₁ = 9/4`), and the
  dual-basis formula gives exactly `Λ_R = h N(r)` with `h = ⟨Λ₁ + (3/2) J, X⟩ = r³ h̃(r)` (the
  term `r² ⟨Λ̃₁, J⟩` is `O(r⁴)` because `det Λ₁ = 9/4`) and
  `N = [[r, (1 - r²)/(1 + r x̃₂₁)], [1 + r x̃₂₁, -r]]`. The scaled matrices are rational in `r`
  and regular at `0`; differentiability at `r = 0` gives the expansions (`zhat_isBigO`,
  `tendsto_zhat_div`). The same closed form gives `H(Z₀₁₀) = χ₂₃ = 0` on the chart
  (`l6c_chart_section`, (14.1.3)).
* **Lemmas 14.2.3–14.2.4** (TeX 11720–11758). With `X = J + A`, `Λ₁ = -(3/2) J + B`, `Λ_R = C`
  and the weights `(A, B, C, t) ~ (r₀, r₀², r₀³, r₀)`, the extremal equations along `e₂` (with
  the constant `P = Z_{e₂}/⟨Z_{e₂}, X₀⟩`) have the leading part `A' = [P₀, J]`,
  `B' = -(3/2) [J, A]`, `C' = [J, B]`, whose solution `XF, BF, CF` from the leading terms of the
  chart is a matrix polynomial in `(r₀, t)`. In Cayley coordinates it is the Fuller flow
  (13.2.2) with control `ζ` (`cayleyZ [J, M] = -2i cayleyZ M`, `cayleyZ [P₀, J]/2 = -iζ`:
  `l6c_cayleyZ_XF`, `l6c_cayleyZ_BF`, `l6c_cayleyZ_CF`). The errors `X - XF`, `Λ₁ + (3/2) J - BF`,
  `Λ_R - CF` satisfy, for `|t| ≤ S r₀`, linear differential inequalities
  `‖E'‖ ≤ K ‖E‖ + O(r₀^k)` with initial errors `O(r₀²)`, `O(r₀³)`, `O(r₀⁴)`; three Grönwall steps
  give `O(r₀²)`, `O(r₀³)`, `O(r₀⁴)` uniformly (`l6c_flow_estimates`). Lemma 14.2.3 follows by
  `cayleyZ`; Lemma 14.2.4 and the companion for `χ₂₃` follow from `P_{e_k}(X) = P_{e_k}(J) + O(r₀)`
  and `⟨M, P_{e_k}(J)⟩ = -2 RR(ζ^k, cayleyZ M)` for symmetric traceless `M`
  (`l6c_switching_estimate`, for every pair of vertices).
  *Departure from the paper:* the book expands the closed-form solutions (matrix exponentials and
  quadratures) on both sides as series in `r₀`. Expanding the quadratures of `iso_vertexFlow` to
  order `r₀⁴` with a uniform remainder is heavy in Lean; the Grönwall comparison of the two ODEs
  gives the same leading terms with a remainder bound. The closed forms are still used where the
  book uses them on the static side (the chart).
* **The Hamiltonians** (TeX 11651–11666): on the chart `H(e₂) = 0`, so
  `H(e_{m+1}) = χ_{m+1,2}`, and the switching estimate at `s = 0` gives
  `24 r³ RR(ζ^m - ζ, z₃) = 24 r³ H_F(z(x̃), ζ^m)` (as `H_F(z(x̃), ζ) = 0`).
* **The first control** (TeX 11706–11718): at `t = 0`, `χ₂₁ = 24 r³ RR(ζ - 1, z₃) + O(r⁴)` with
  `RR(ζ - 1, z₃) = -(3/2) z₃ > 0`, and `χ₂₃ = 0` with
  `χ₂₃'(0) = -4√3 ℓ̃₂₁ r² + O(r³) > 0` (`l6c_eventually_chi23Deriv_pos`); by continuity in `t`,
  `e₂` beats `e₁` and `e₃` on some `[0, ε]`, and the maximum over the simplex is at a vertex
  (`l6c_hamiltonian_le_of_vertices`, as `poly_hamiltonian_le_of_vertices`, with `⟨X, Z_{e_m}⟩ < 0`
  in place of the star condition).
* **Remark 14.2.1**: `fullerChartInv` inverts `fullerOfChart` on the normalized points (where
  `H_F(z, ζ) = 0` fixes `z₃`), `H_F(q_out, ζ) = 0` comes from `H_F⁺(q_out) = 0` and `z₃ < 0`, and
  the three enclosures are polynomial inequalities in `r_scale` and `√3`, checked with
  `rScale_fine_bounds` and one bound per monomial.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology Asymptotics
open TriFuller
open scoped Matrix.Norms.Operator

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

/-! ### The Fuller flow as the leading term (helpers) -/

/-- The leading terms of `X` are the Fuller `z₁`: `cayleyZ(XF(r, s r))/2 = r z₁(s)`. -/
theorem l6c_cayleyZ_XF (x : Fin 3 → ℝ) (r s : ℝ) :
    cayleyZ (l6c_XF x r (s * r)) / 2 = (r : ℂ) * flow s (fullerOfChart x) ζ 0 := by
  rw [l6c_XF_eq]
  apply Complex.ext <;> simp [cayleyZ, flow, fullerOfChart, ζ_re, ζ_im] <;> ring

/-- The leading terms of `Λ₁` are the Fuller `z₂`: `-i cayleyZ(BF(r, s r))/6 = r² z₂(s)`. -/
theorem l6c_cayleyZ_BF (x : Fin 3 → ℝ) (r s : ℝ) :
    -I * cayleyZ (l6c_BF x r (s * r)) / 6 = (r : ℂ) ^ 2 * flow s (fullerOfChart x) ζ 1 := by
  rw [l6c_BF, l6c_br_P0_J, l6c_At, l6c_Bt]
  simp only [l6c_br_J_of]
  apply Complex.ext <;> simp [cayleyZ, flow, fullerOfChart, ζ_re, ζ_im, ← Complex.ofReal_pow] <;>
    ring

/-- The leading terms of `Λ_R` are the Fuller `z₃`: `cayleyZ(CF(r, s r))/12 = r³ z₃(s)`. -/
theorem l6c_cayleyZ_CF (x : Fin 3 → ℝ) (r s : ℝ) :
    cayleyZ (l6c_CF x r (s * r)) / 12 = (r : ℂ) ^ 3 * flow s (fullerOfChart x) ζ 2 := by
  rw [l6c_CF, l6c_br_P0_J, l6c_At, l6c_Bt, l6c_Ct]
  simp only [l6c_br_J_of]
  apply Complex.ext <;> simp [cayleyZ, flow, fullerOfChart, ζ_re, ζ_im, ← Complex.ofReal_pow] <;>
    ring

/-- The error in `ẑ₁` is the Cayley coordinate of the error in `X`. -/
theorem l6c_fullerCoords_sub_XF (q : iso_PhasePt) (x : Fin 3 → ℝ) (r s : ℝ) :
    fullerCoords q 0 - (r : ℂ) * flow s (fullerOfChart x) ζ 0 =
      cayleyZ (q.1 - l6c_XF x r (s * r)) / 2 := by
  rw [l6c_cayleyZ_sub, sub_div, l6c_cayleyZ_XF]; rfl

/-- The error in `ẑ₂` is the Cayley coordinate of the error in `Λ₁`. -/
theorem l6c_fullerCoords_sub_BF (q : iso_PhasePt) (x : Fin 3 → ℝ) (r s : ℝ) :
    fullerCoords q 1 - (r : ℂ) ^ 2 * flow s (fullerOfChart x) ζ 1 =
      -I * cayleyZ (q.2.1 + (3 / 2 : ℝ) • J - l6c_BF x r (s * r)) / 6 := by
  rw [l6c_cayleyZ_sub, l6c_cayleyZ_add, l6c_cayleyZ_smul, l6c_cayleyZ_J, ← l6c_cayleyZ_BF]
  simp only [fullerCoords, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

/-- The error in `ẑ₃` is the Cayley coordinate of the error in `Λ_R`. -/
theorem l6c_fullerCoords_sub_CF (q : iso_PhasePt) (x : Fin 3 → ℝ) (r s : ℝ) :
    fullerCoords q 2 - (r : ℂ) ^ 3 * flow s (fullerOfChart x) ζ 2 =
      cayleyZ (q.2.2 - l6c_CF x r (s * r)) / 12 := by
  rw [l6c_cayleyZ_sub, sub_div, l6c_cayleyZ_CF]; rfl

/-- The content of Lemma 14.2.3 (`lemma14_2_3`), proved here so that the expansions of `ẑ`
(its case `s = 0`) can use it: `ẑ_k(flow(s r₀)) - r₀^k z_k(s) = O(r₀^{k+1})`, from
`l6c_flow_estimates` and `cayleyZ`. -/
theorem l6c_fullerCoords_flow_isBigO (x : Fin 3 → ℝ) (s : ℝ) (k : Fin 3) :
    (fun r₀ : ℝ ↦ fullerCoords (iso_vertexFlow 1 (lieChart (r₀, x)) (s * r₀)) k -
        (r₀ : ℂ) ^ (k.val + 1) * flow s (fullerOfChart x) ζ k)
      =O[𝓝[>] 0] (fun r₀ ↦ r₀ ^ (k.val + 2)) := by
  obtain ⟨C, hC⟩ := l6c_flow_estimates x (abs_nonneg s)
  refine IsBigO.of_bound C ((hC.and eventually_mem_nhdsWithin).mono fun r ⟨h, hr⟩ ↦ ?_)
  have hr0 : (0 : ℝ) < r := hr
  obtain ⟨h1, h2, h3⟩ := h (s * r) (by rw [abs_mul, abs_of_pos hr0])
  rw [Real.norm_eq_abs, abs_of_pos (pow_pos hr0 _)]
  set q := iso_vertexFlow 1 (lieChart (r, x)) (s * r)
  fin_cases k
  · simp only [Fin.zero_eta, zero_add, pow_one]
    rw [l6c_fullerCoords_sub_XF, norm_div, Complex.norm_ofNat]
    have := l6c_norm_cayleyZ (q.1 - l6c_XF x r (s * r))
    linarith
  · simp only [Fin.mk_one, Nat.reduceAdd]
    rw [l6c_fullerCoords_sub_BF, norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_ofNat]
    have := l6c_norm_cayleyZ (q.2.1 + (3 / 2 : ℝ) • J - l6c_BF x r (s * r))
    have h0 := norm_nonneg (q.2.1 + (3 / 2 : ℝ) • J - l6c_BF x r (s * r))
    linarith
  · simp only [Fin.reduceFinMk, Nat.reduceAdd]
    rw [l6c_fullerCoords_sub_CF, norm_div, Complex.norm_ofNat]
    have := l6c_norm_cayleyZ (q.2.2 - l6c_CF x r (s * r))
    have h0 := norm_nonneg (q.2.2 - l6c_CF x r (s * r))
    linarith

/-- The leading term of the switching functions: `⟨CF, P_{e_j}(J) - P_{e_i}(J)⟩ =
24 r³ RR(ζ^i - ζ^j, z₃(s))`. -/
theorem l6c_traceForm_CF (x : Fin 3 → ℝ) (r s : ℝ) (i j : Fin 3) :
    traceForm (l6c_CF x r (s * r)) (controlP (vertex j) J - controlP (vertex i) J) =
      24 * r ^ 3 * RR (ζ ^ (i : ℕ) - ζ ^ (j : ℕ)) (flow s (fullerOfChart x) ζ 2) := by
  obtain ⟨h1, h2⟩ := l6c_CF_symm x r (s * r)
  have hc : cayleyZ (l6c_CF x r (s * r)) =
      ((12 * r ^ 3 : ℝ) : ℂ) * flow s (fullerOfChart x) ζ 2 := by
    have := l6c_cayleyZ_CF x r s
    push_cast
    linear_combination 12 * this
  rw [l6c_traceForm_sub_right, l6c_traceForm_controlP_J j h1 h2, l6c_traceForm_controlP_J i h1 h2,
    hc, RR_ofReal_mul_right, RR_ofReal_mul_right, l6c_RR_sub_left]
  ring

/-- **The switching functions along the rescaled flow** (Lemma 14.2.4 and its companions):
`χ_ij(X(s r), Λ_R(s r)) = 24 r³ RR(ζ^i - ζ^j, z₃(s)) + O(r⁴)`. -/
theorem l6c_switching_estimate (x : Fin 3 → ℝ) (s : ℝ) (i j : Fin 3) :
    (fun r : ℝ ↦ switchingFn i j (iso_vertexFlow 1 (lieChart (r, x)) (s * r)).2.2
        (iso_vertexFlow 1 (lieChart (r, x)) (s * r)).1 -
        24 * r ^ 3 * RR (ζ ^ (i : ℕ) - ζ ^ (j : ℕ)) (flow s (fullerOfChart x) ζ 2))
      =O[𝓝[>] 0] (fun r ↦ r ^ 4) := by
  obtain ⟨C, hC⟩ := l6c_flow_estimates x (abs_nonneg s)
  set S := |s|
  set a := ‖l6c_At x‖ + S * ‖l6c_br l6c_P0 J‖
  set c := ‖l6c_Ct x‖ + S * ‖l6c_br J (l6c_Bt x)‖ +
      3 / 4 * S ^ 2 * ‖l6c_br J (l6c_br J (l6c_At x))‖ +
      1 / 4 * S ^ 3 * ‖l6c_br J (l6c_br J (l6c_br l6c_P0 J))‖
  set D := |C| + a
  set Zi := ‖controlMatrix (vertex i)‖
  set Zj := ‖controlMatrix (vertex j)‖
  have ha : 0 ≤ a := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hD : 0 ≤ D := by positivity
  set δ := min 1 (1 / (6 * (Zi + Zj) * D + 1))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  refine IsBigO.of_bound (2 * c * (9 * Zi ^ 2 + 9 * Zj ^ 2) * D +
      2 * |C| * (‖controlP (vertex j) J‖ + ‖controlP (vertex i) J‖ +
        (9 * Zi ^ 2 + 9 * Zj ^ 2) * D))
    ((hC.and (show ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 δ from Ioo_mem_nhdsGT hδ)).mono
      fun r ⟨h, hr⟩ ↦ ?_)
  have hr0 : 0 < r := hr.1
  have hr1 : r ≤ 1 := hr.2.le.trans (min_le_left _ _)
  have hrδ : r * (6 * (Zi + Zj) * D + 1) ≤ 1 := by
    have := hr.2.le.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at this
  obtain ⟨h1, -, h3⟩ := h (s * r) (by rw [abs_mul, abs_of_pos hr0])
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hr0 _)]
  set q := iso_vertexFlow 1 (lieChart (r, x)) (s * r)
  have hXJ : ‖q.1 - J‖ ≤ D * r := by
    have h2 := l6c_norm_XF_sub_J x hr0.le (show |s * r| ≤ S * r by rw [abs_mul, abs_of_pos hr0])
    calc ‖q.1 - J‖ ≤ ‖q.1 - l6c_XF x r (s * r)‖ + ‖l6c_XF x r (s * r) - J‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ |C| * r ^ 2 + a * r := add_le_add (h1.trans (by gcongr; exact le_abs_self _)) h2
      _ ≤ D * r := by
          have : r ^ 2 ≤ r := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left this (abs_nonneg C)]
  have hsmall : ∀ k : Fin 3, ‖controlMatrix (vertex k)‖ ≤ Zi + Zj →
      2 * ‖controlMatrix (vertex k)‖ * ‖q.1 - J‖ ≤ 1 / 3 := by
    intro k hk
    calc 2 * ‖controlMatrix (vertex k)‖ * ‖q.1 - J‖ ≤ 2 * (Zi + Zj) * (D * r) := by gcongr
      _ ≤ 1 / 3 := by nlinarith
  have hPi := l6c_controlP_sub_le i (hsmall i (by simp [Zi, Zj]))
  have hPj := l6c_controlP_sub_le j (hsmall j (by simp [Zi, Zj]))
  set dPi := controlP (vertex i) q.1 - controlP (vertex i) J
  set dPj := controlP (vertex j) q.1 - controlP (vertex j) J
  have hdi : ‖dPi‖ ≤ 9 * Zi ^ 2 * (D * r) := hPi.trans (by gcongr)
  have hdj : ‖dPj‖ ≤ 9 * Zj ^ 2 * (D * r) := hPj.trans (by gcongr)
  have hCF := l6c_norm_CF x hr0.le (show |s * r| ≤ S * r by rw [abs_mul, abs_of_pos hr0])
  have e : switchingFn i j q.2.2 q.1 -
      24 * r ^ 3 * RR (ζ ^ (i : ℕ) - ζ ^ (j : ℕ)) (flow s (fullerOfChart x) ζ 2) =
      traceForm (l6c_CF x r (s * r)) (dPj - dPi) +
        traceForm (q.2.2 - l6c_CF x r (s * r))
          (controlP (vertex j) q.1 - controlP (vertex i) q.1) := by
    rw [← l6c_traceForm_CF x r s i j, switchingFn]
    simp only [dPi, dPj, traceForm, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
    ring
  rw [e]
  have hA := l6c_abs_traceForm (l6c_CF x r (s * r)) (dPj - dPi)
  have hB := l6c_abs_traceForm (q.2.2 - l6c_CF x r (s * r))
    (controlP (vertex j) q.1 - controlP (vertex i) q.1)
  have hd1 : ‖dPj - dPi‖ ≤ (9 * Zi ^ 2 + 9 * Zj ^ 2) * D * r := by
    have := norm_sub_le dPj dPi
    nlinarith
  have hd2 : ‖controlP (vertex j) q.1 - controlP (vertex i) q.1‖ ≤
      ‖controlP (vertex j) J‖ + ‖controlP (vertex i) J‖ + (9 * Zi ^ 2 + 9 * Zj ^ 2) * D := by
    have e2 : controlP (vertex j) q.1 - controlP (vertex i) q.1 =
        (controlP (vertex j) J - controlP (vertex i) J) + (dPj - dPi) := by
      simp only [dPi, dPj]; abel
    rw [e2]
    have := norm_add_le (controlP (vertex j) J - controlP (vertex i) J) (dPj - dPi)
    have := norm_sub_le (controlP (vertex j) J) (controlP (vertex i) J)
    have : (9 * Zi ^ 2 + 9 * Zj ^ 2) * D * r ≤ (9 * Zi ^ 2 + 9 * Zj ^ 2) * D :=
      mul_le_of_le_one_right (by positivity) hr1
    linarith
  have hE : ‖q.2.2 - l6c_CF x r (s * r)‖ ≤ |C| * r ^ 4 :=
    h3.trans (by gcongr; exact le_abs_self _)
  calc |traceForm (l6c_CF x r (s * r)) (dPj - dPi) + traceForm (q.2.2 - l6c_CF x r (s * r))
        (controlP (vertex j) q.1 - controlP (vertex i) q.1)|
      ≤ |traceForm (l6c_CF x r (s * r)) (dPj - dPi)| + |traceForm (q.2.2 - l6c_CF x r (s * r))
        (controlP (vertex j) q.1 - controlP (vertex i) q.1)| := abs_add_le _ _
    _ ≤ 2 * (c * r ^ 3) * ((9 * Zi ^ 2 + 9 * Zj ^ 2) * D * r) +
        2 * (|C| * r ^ 4) * (‖controlP (vertex j) J‖ + ‖controlP (vertex i) J‖ +
          (9 * Zi ^ 2 + 9 * Zj ^ 2) * D) := by
        refine add_le_add (hA.trans ?_) (hB.trans ?_) <;> gcongr
    _ = _ := by ring

/-- `H_F(z(x̃), ζ) = H_F(z(x̃), ζ²) = 0` (the computation behind `ham_fullerOfChart`). -/
theorem l6c_ham_fullerOfChart (x : Fin 3 → ℝ) :
    ham (fullerOfChart x) ζ = 0 ∧ ham (fullerOfChart x) (ζ ^ 2) = 0 := by
  constructor <;>
  · simp [ham, fullerOfChart, RR_eq_re_mul_add_im_mul, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im]
    ring

/-! ### The statements of §14.2 -/

/-- **The expansions of `ẑ`** (TeX 11631–11645, "A calculation gives"): for fixed `x̃`, as
`r → 0⁺`, `ẑ₁ = (r/2)(x̃₂₁ + i x̃₁₁) + O(r²)` (`x̃₁₁ = 1`), `ẑ₂ = (r²/3!)(ℓ̃₁₁ - i ℓ̃₂₁) + O(r³)`
and `ẑ₃ = (r³/4!)(ℓ̃_{R12} + ℓ̃_{R21}) + O(r⁴)`, where `r³ ℓ̃_R = Λ_R(r, x̃)`.

Proof: the case `s = 0` of `l6c_fullerCoords_flow_isBigO` for `ẑ₁`, `ẑ₂` (at `t = 0` it only
uses the closed form of the chart); for `ẑ₃`, `ẑ₃ - (ℓ̃_{R12} + ℓ̃_{R21}) r³/24 = i (Λ_R)₁₁/12` and
`(Λ_R)₁₁ = r⁴ h̃(r)` (`l6c_static_C`). -/
theorem zhat_isBigO (x : Fin 3 → ℝ) :
    (fun r : ℝ ↦ zhat (r, x) 0 - (r : ℂ) / 2 * ((x 0 : ℂ) + I)) =O[𝓝[>] 0] (fun r ↦ r ^ 2) ∧
      (fun r : ℝ ↦ zhat (r, x) 1 - (r : ℂ) ^ 2 / 6 * ((x 1 : ℂ) - (x 2 : ℂ) * I))
        =O[𝓝[>] 0] (fun r ↦ r ^ 3) ∧
      (fun r : ℝ ↦ zhat (r, x) 2 -
          (((lieChart (r, x)).2.2 0 1 + (lieChart (r, x)).2.2 1 0) / 24 : ℝ))
        =O[𝓝[>] 0] (fun r ↦ r ^ 4) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := l6c_fullerCoords_flow_isBigO x 0 0
    simp only [zero_mul, ivf_vertexFlow_zero, flow_zero, Fin.val_zero, zero_add, pow_one] at h
    refine h.congr (fun r ↦ ?_) (fun r ↦ rfl)
    simp only [zhat, fullerOfChart, Matrix.cons_val_zero]
    ring
  · have h := l6c_fullerCoords_flow_isBigO x 0 1
    simp only [zero_mul, ivf_vertexFlow_zero, flow_zero, Fin.val_one, Nat.reduceAdd] at h
    refine h.congr (fun r ↦ ?_) (fun r ↦ rfl)
    simp only [zhat, fullerOfChart, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  · obtain ⟨C, hC⟩ := l6c_static_C x
    refine IsBigO.of_bound C ((hC.and eventually_mem_nhdsWithin).mono fun r ⟨h, hr⟩ ↦ ?_)
    have hr0 : (0 : ℝ) < r := hr
    have e : zhat (r, x) 2 - (((lieChart (r, x)).2.2 0 1 + (lieChart (r, x)).2.2 1 0) / 24 : ℝ) =
        I * (((lieChart (r, x)).2.2 - l6c_CF x r 0) 0 0 : ℝ) / 12 := by
      simp only [zhat, fullerCoords, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        Matrix.sub_apply, l6c_CF, l6c_Ct]
      apply Complex.ext <;> simp [cayleyZ] <;> ring
    rw [e, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_ofNat,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hr0 _)]
    have := l6c_abs_le_norm ((lieChart (r, x)).2.2 - l6c_CF x r 0) 0 0
    have h0 : 0 ≤ C * r ^ 4 := (norm_nonneg _).trans h
    linarith

/-- **The limit `z(x̃)` exists and is nonzero** (TeX 11646–11650): `(ẑ₁/r, ẑ₂/r², ẑ₃/r³) → z(x̃)`
as `r → 0⁺`, and `z(x̃) ≠ 0`.

Proof: `ẑ_k - r^k z_k(x̃) = O(r^{k+1})` (the case `s = 0` of `l6c_fullerCoords_flow_isBigO`), and
`Im z₁(x̃) = 1/2`. -/
theorem tendsto_zhat_div (x : Fin 3 → ℝ) :
    Tendsto (fun r : ℝ ↦ ![zhat (r, x) 0 / r, zhat (r, x) 1 / r ^ 2, zhat (r, x) 2 / r ^ 3])
      (𝓝[>] 0) (𝓝 (fullerOfChart x)) ∧ fullerOfChart x ≠ 0 := by
  refine ⟨tendsto_pi_nhds.2 fun k ↦ ?_, fun h ↦ ?_⟩
  · have h := l6c_fullerCoords_flow_isBigO x 0 k
    simp only [zero_mul, ivf_vertexFlow_zero, flow_zero] at h
    obtain ⟨C, hC⟩ := h.bound
    -- `zhat k / r^(k+1) - z k` is `O(r)`
    have key : Tendsto (fun r : ℝ ↦ zhat (r, x) k / (r : ℂ) ^ (k.val + 1) - fullerOfChart x k)
        (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' ((hC.and eventually_mem_nhdsWithin).mono fun r ⟨h, hr⟩ ↦ ?_)
        (?_ : Tendsto (fun r : ℝ ↦ C * r) (𝓝[>] 0) (𝓝 0))
      · have hr0 : (0 : ℝ) < r := hr
        have hr' : (r : ℂ) ^ (k.val + 1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hr0.ne')
        have e : zhat (r, x) k / (r : ℂ) ^ (k.val + 1) - fullerOfChart x k =
            (zhat (r, x) k - (r : ℂ) ^ (k.val + 1) * fullerOfChart x k) /
              (r : ℂ) ^ (k.val + 1) := by
          field_simp
        rw [e, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
          div_le_iff₀ (pow_pos hr0 _)]
        rw [Real.norm_eq_abs, abs_of_pos (pow_pos hr0 _)] at h
        calc _ ≤ C * r ^ (k.val + 2) := h
          _ = C * r * r ^ (k.val + 1) := by ring
      · have : Tendsto (fun r : ℝ ↦ C * r) (𝓝 0) (𝓝 (C * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
    have key' := key.add_const (fullerOfChart x k)
    rw [zero_add] at key'
    refine key'.congr' (Eventually.of_forall fun r ↦ ?_)
    fin_cases k <;> simp
  · have := congrFun h 0
    have h2 := congrArg Complex.im this
    simp [fullerOfChart] at h2

/-- **The Reinhardt Hamiltonians are asymptotically the Fuller Hamiltonians** (TeX 11651–11658):
`H(Z_u, X(r, x̃), Λ₁(r, x̃), Λ_R(r, x̃)) = 24 r³ H_F(ũ, z(x̃)) + O(r⁴)`, with the vertex `e_{m+1}`
corresponding to `ζ^m` (`24 = 6ρ²`; the book writes `H_F(ũ, z)`, Chapter 13 writes `H_F(z, u)`,
G14.13).

Proof: on the chart `H(Z₀₁₀) = 0` (`l6c_chart_section`), so `H(e_{m+1}) = χ_{m+1,2}`; the case
`s = 0` of `l6c_switching_estimate` gives `24 r³ RR(ζ^m - ζ, z₃) = 24 r³ H_F(z(x̃), ζ^m)`. -/
theorem hamiltonian_lieChart_isBigO (x : Fin 3 → ℝ) (m : Fin 3) :
    (fun r : ℝ ↦ hamiltonian (-1) (lieChart (r, x)).2.1 (lieChart (r, x)).2.2 (lieChart (r, x)).1
        (vertex m) - 24 * r ^ 3 * ham (fullerOfChart x) (ζ ^ (m : ℕ)))
      =O[𝓝[>] 0] (fun r ↦ r ^ 4) := by
  have h := l6c_switching_estimate x 0 m 1
  simp only [zero_mul, ivf_vertexFlow_zero, flow_zero] at h
  refine h.congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [l6c_eventually_chart x, l6c_eventually_traceForm_lt x 1,
    l6c_eventually_traceForm_lt x 2] with r ⟨_, _, h1, h2⟩ h3 h4
  obtain ⟨hH, -⟩ := l6c_chart_section h1 h2 (ne_of_lt (by linarith)) (ne_of_lt (by linarith))
  have hsub := poly_hamiltonian_sub (-1) (lieChart (r, x)).2.1 (lieChart (r, x)).2.2
    (lieChart (r, x)).1 m 1
  have hF : ham (fullerOfChart x) (ζ ^ (m : ℕ)) =
      RR (ζ ^ (m : ℕ) - ζ ^ ((1 : Fin 3) : ℕ)) (fullerOfChart x 2) := by
    have := (l6c_ham_fullerOfChart x).1
    simp only [ham] at this ⊢
    rw [l6c_RR_sub_left, Fin.val_one, pow_one]
    linarith
  rw [hF]
  linarith

/-- "The equations (14.1.3) imply `H_F(z(x̃), ζ) = H_F(z(x̃), ζ²) = 0`" (TeX 11663–11666). -/
theorem ham_fullerOfChart (x : Fin 3 → ℝ) :
    ham (fullerOfChart x) ζ = 0 ∧ ham (fullerOfChart x) (ζ ^ 2) = 0 := by
  exact l6c_ham_fullerOfChart x

/-- `fullerChartInv` inverts `fullerOfChart`, and is invariant under the virial rescalings
(`r > 0`): `fullerChartInv (scale r z) = fullerChartInv z`. For a point `z` with `Im z₁ > 0`, real
`z₃` and `H_F(z, ζ) = 0`, `fullerOfChart (fullerChartInv z)` is the rescaling of `z` by
`1/(2 Im z₁)`. -/
theorem fullerChartInv_spec :
    (∀ x, fullerChartInv (fullerOfChart x) = x) ∧
      (∀ z (r : ℝ), 0 < r → fullerChartInv (scale r z) = fullerChartInv z) ∧
      ∀ z : Fin 3 → ℂ, 0 < (z 0).im → (z 2).im = 0 → ham z ζ = 0 →
        fullerOfChart (fullerChartInv z) = scale (2 * (z 0).im)⁻¹ z := by
  refine ⟨fun x ↦ ?_, fun z r hr ↦ ?_, fun z hz0 hz2 hH ↦ ?_⟩
  · funext k
    fin_cases k <;> simp [fullerChartInv, fullerOfChart] <;> ring
  · have hr0 : r ≠ 0 := hr.ne'
    funext k
    fin_cases k
    · simp only [fullerChartInv, scale, Fin.zero_eta, Matrix.cons_val_zero, Complex.re_ofReal_mul,
        Complex.im_ofReal_mul]
      exact mul_div_mul_left _ _ hr0
    · simp only [fullerChartInv, scale, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
      rw [show 3 * (r ^ 2 * (z 1).re) / (2 * (r * (z 0).im) ^ 2) =
        r ^ 2 * (3 * (z 1).re) / (r ^ 2 * (2 * (z 0).im ^ 2)) by ring]
      exact mul_div_mul_left _ _ (pow_ne_zero 2 hr0)
    · simp only [fullerChartInv, scale, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← Complex.ofReal_pow, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
      rw [show -(3 * (r ^ 2 * (z 1).im)) / (2 * (r * (z 0).im) ^ 2) =
        r ^ 2 * (-(3 * (z 1).im)) / (r ^ 2 * (2 * (z 0).im ^ 2)) by ring]
      exact mul_div_mul_left _ _ (pow_ne_zero 2 hr0)
  · have hy : (z 0).im ≠ 0 := hz0.ne'
    have hH' : (z 2).re = 2 * ((z 0).im * (z 1).re - (z 0).re * (z 1).im) := by
      simp only [ham, RR_eq_re_mul_add_im_mul, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, ζ_re, ζ_im, hz2] at hH
      linarith
    have hc : (2 * (z 0).im)⁻¹ * (z 0).im = 1 / 2 := by field_simp
    generalize hcdef : (2 * (z 0).im)⁻¹ = c at hc
    have hc' : c = 1 / (2 * (z 0).im) := by rw [← hcdef]; ring
    funext k
    fin_cases k <;> apply Complex.ext <;>
      simp only [fullerChartInv, fullerOfChart, scale, ← Complex.ofReal_pow, Fin.zero_eta,
        Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, 
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.div_ofNat_re, Complex.div_ofNat_im, hz2] <;>
      rw [hc'] <;> field_simp <;> ring_nf
    · rw [hH']; ring

/-- The enclosures of Remark 14.2.1. With `r = r_scale`, the coordinates of `x̃_out` are
`-√3 (1 + r)/(r - 1)`, `-(3√3/2) (r² + r + 1)(r + 1)/((r² - r + 1)(r - 1))` and
`-(3/2) (r⁴ - 3r³ - 2r² - 3r + 1)(1 + r)²/((r⁴ + r³ + r + 1)(r - 1)²)`; they are bounded with the
fine enclosures of `r_scale` (`rScale_fine_bounds`) and `√3`, each monomial separately. -/
theorem l6c_xTildeOut_bounds :
    |xTildeOut 0 - (-2.39)| < 0.01 ∧ |xTildeOut 1 - (-4.90)| < 0.01 ∧
      |xTildeOut 2 - (-1.12)| < 0.01 := by
  obtain ⟨h0r, h0i, h1r, h1i⟩ := l6c_qOutCart_coords
  obtain ⟨hr1, hr2⟩ := rScale_fine_bounds
  obtain ⟨hs1, hs2⟩ := l6c_sqrt3_fine
  have hs0 : 0 < √3 := by positivity
  set r := rScale
  set s := √3
  have hr0 : 0 < r := by linarith
  have hs2' : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ha : (0 : ℝ) ≤ 6.2741673995248239329 := by norm_num
  have hsa : (0 : ℝ) ≤ 1.7320508075 := by norm_num
  have p : ∀ n : ℕ, n ≠ 0 → (6.2741673995248239329 : ℝ) ^ n < r ^ n ∧
      r ^ n < (6.2741673995248239330 : ℝ) ^ n := fun n hn ↦
    ⟨pow_lt_pow_left₀ hr1 ha hn, pow_lt_pow_left₀ hr2 hr0.le hn⟩
  have q : ∀ n : ℕ, n ≠ 0 → (1.7320508075 : ℝ) * 6.2741673995248239329 ^ n < s * r ^ n ∧
      s * r ^ n < (1.7320508076 : ℝ) * 6.2741673995248239330 ^ n := fun n hn ↦
    ⟨mul_lt_mul'' hs1 (p n hn).1 hsa (pow_nonneg ha n),
      mul_lt_mul'' hs2 (p n hn).2 hs0.le (pow_nonneg hr0.le n)⟩
  obtain ⟨p1, p1'⟩ := p 1 one_ne_zero
  obtain ⟨p2, p2'⟩ := p 2 two_ne_zero
  obtain ⟨p3, p3'⟩ := p 3 (by norm_num)
  obtain ⟨p4, p4'⟩ := p 4 (by norm_num)
  obtain ⟨p5, p5'⟩ := p 5 (by norm_num)
  obtain ⟨p6, p6'⟩ := p 6 (by norm_num)
  obtain ⟨q1, q1'⟩ := q 1 one_ne_zero
  obtain ⟨q2, q2'⟩ := q 2 two_ne_zero
  obtain ⟨q3, q3'⟩ := q 3 (by norm_num)
  simp only [pow_one] at p1 p1' q1 q1'
  simp only [xTildeOut, fullerChartInv, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h0r, h0i, h1r, h1i]
  have h1 : r - 1 ≠ 0 := by linarith
  have h1' : -1 + r ≠ 0 := by linarith
  have h4 : 1 + r ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_lt]
    have e : -1 / ((-1 + r) / (s * (1 + r))) = -(s * (1 + r)) / (r - 1) := by
      field_simp; ring
    rw [e]
    constructor
    · rw [lt_sub_iff_add_lt, lt_div_iff₀ (by linarith)]; linarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ (by linarith)]; linarith
  · rw [abs_lt]
    have h2 : r ^ 2 - r + 1 ≠ 0 := by nlinarith
    have h3 : 1 + r ^ 3 ≠ 0 := by positivity
    have e : 3 * -((-1 + r ^ 3) / (s * (1 + r ^ 3))) / (2 * ((-1 + r) / (s * (1 + r))) ^ 2) =
        -(3 / 2 * s * ((r ^ 2 + r + 1) * (r + 1))) / ((r ^ 2 - r + 1) * (r - 1)) := by
      rw [div_eq_div_iff (by positivity) (mul_ne_zero h2 h1)]
      field_simp
      ring_nf
    rw [e]
    have hd : 0 < (r ^ 2 - r + 1) * (r - 1) := by nlinarith
    constructor
    · rw [lt_sub_iff_add_lt, lt_div_iff₀ hd]; ring_nf; linarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hd]; ring_nf; linarith
  · rw [abs_lt]
    have h3 : 1 + r + r ^ 3 + r ^ 4 ≠ 0 := by positivity
    have e : -(3 * ((1 - 3 * r - 2 * r ^ 2 - 3 * r ^ 3 + r ^ 4) /
          (3 * (1 + r + r ^ 3 + r ^ 4)))) / (2 * ((-1 + r) / (s * (1 + r))) ^ 2) =
        -(3 / 2 * (r ^ 4 - 3 * r ^ 3 - 2 * r ^ 2 - 3 * r + 1) * (1 + r) ^ 2) /
          ((r ^ 4 + r ^ 3 + r + 1) * (r - 1) ^ 2) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      field_simp
      ring_nf
      rw [hs2']
      ring
    rw [e]
    have hd : 0 < (r ^ 4 + r ^ 3 + r + 1) * (r - 1) ^ 2 := by
      have : 0 < r - 1 := by linarith
      positivity
    constructor
    · rw [lt_sub_iff_add_lt, lt_div_iff₀ hd]; ring_nf; linarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hd]; ring_nf; linarith

/-- **Remark 14.2.1** (TeX 11668–11679): with `z_{out,i} = x_i + i y_i` (the representative
(13.5.1) of `q_out`), `x̃_out = (x₁/y₁, 3x₂/(2y₁²), -3y₂/(2y₁²)) ≈ (-2.39, -4.90, -1.12)`, and
`ξ(x̃_out)` is the outward fixed point `q_out` modulo the virial group: `z(x̃_out)` is the virial
rescaling of `q_out` by `1/(2 y₁)`, and it lies in the Fuller section (`sectionZero`: on the walls,
with `H_F⁺ = 0`), so its class in `Ξ_{𝒲,0}/V_T` is `q_out`. (The exact value is
`(-2.388856…, -4.902232…, -1.126400…)`; see the module docstring.)

Proof: the enclosures are `l6c_xTildeOut_bounds`; `H_F(q_out, ζ) = 0` (`l6c_ham_qOutCart`) and
`fullerChartInv_spec` give the identity; `H_F` scales by `λ³` under the virial rescaling. -/
theorem remark14_2_1 :
    |xTildeOut 0 - (-2.39)| < 0.01 ∧ |xTildeOut 1 - (-4.90)| < 0.01 ∧
      |xTildeOut 2 - (-1.12)| < 0.01 ∧
      fullerOfChart xTildeOut = scale (2 * (qOutCart 0).im)⁻¹ qOutCart ∧
      VirialEquiv qOutCart (fullerOfChart xTildeOut) ∧ fullerOfChart xTildeOut ∈ sectionZero := by
  obtain ⟨b0, b1, b2⟩ := l6c_xTildeOut_bounds
  have hq0 := qOutCart_signs.1
  obtain ⟨-, hq2, hq2'⟩ := qOutCart_normalization
  obtain ⟨hζ, hζ2, h1⟩ := l6c_ham_qOutCart
  have hid : fullerOfChart xTildeOut = scale (2 * (qOutCart 0).im)⁻¹ qOutCart :=
    fullerChartInv_spec.2.2 qOutCart hq0 hq2 hζ
  set c := (2 * (qOutCart 0).im)⁻¹
  have hc : 0 < c := by positivity
  refine ⟨b0, b1, b2, hid, ⟨c, hc, 1, one_mem_VT, by rw [hid, one_smul]⟩, ?_⟩
  rw [hid]
  have hsc : ∀ u, ham (scale c qOutCart) u = c ^ 3 * ham qOutCart u := fun u ↦ by
    simpa using ham_smul_scale (v := 1) (by simp) c qOutCart u
  refine ⟨scale_ne_zero hc qOutCart_ne_zero, ?_, ?_⟩
  · refine Set.mem_union_left _ (Set.mem_union_left _ ⟨c ^ 3 * (qOutCart 2).re,
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hq2'.le, ?_⟩)
    apply Complex.ext <;> simp [scale, hq2, ← Complex.ofReal_pow]
  · rw [hamMax, hsc, hsc, hsc, hζ, hζ2, mul_zero, max_self]
    exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos (by positivity) h1.le)

/-- **The first control is `e₂`** (TeX 11706–11718): "For a given `x̃`, the first control of
`(X(r, x̃), Λ₁(r, x̃), Λ_R(r, x̃))` is `u = e₂` for all sufficiently small `r > 0`, provided we
assume `ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁ < 0` and `ℓ̃₂₁ < 0`" (equivalently `x₃ < 0` and `y₂ > 0` for `z(x̃)`):
the constant control `e₂` maximizes the Hamiltonian along its own flow on some `[0, ε]`.

Proof: at `t = 0`, `χ₂₁ = 24 r³ RR(ζ - 1, z₃) + O(r⁴) > 0` (`RR(ζ - 1, z₃) = -(3/2) z₃ > 0`),
`χ₂₃ = 0` and `χ₂₃'(0) = -4√3 ℓ̃₂₁ r² + O(r³) > 0` (`l6c_eventually_chi23Deriv_pos`); by
continuity `e₂` beats `e₁` and `e₃` on some `[0, ε]`, and the maximum over `U_T` is at a vertex
(`l6c_hamiltonian_le_of_vertices`, with `⟨X, Z_{e_m}⟩ < 0` near `X = J`). -/
theorem eventually_firstControl_lieChart {x : Fin 3 → ℝ} (h₁ : x 1 + x 2 * x 0 < 0)
    (h₂ : x 2 < 0) :
    ∀ᶠ r in 𝓝[>] 0, ∃ ε > 0, ∀ t ∈ Icc 0 ε, ∀ v ∈ controlSimplex,
      hamiltonian (-1) (iso_vertexFlow 1 (lieChart (r, x)) t).2.1
          (iso_vertexFlow 1 (lieChart (r, x)) t).2.2 (iso_vertexFlow 1 (lieChart (r, x)) t).1 v ≤
        hamiltonian (-1) (iso_vertexFlow 1 (lieChart (r, x)) t).2.1
          (iso_vertexFlow 1 (lieChart (r, x)) t).2.2 (iso_vertexFlow 1 (lieChart (r, x)) t).1
          (vertex 1) := by
  -- (A) `χ₂₁ > 0` on the chart for small `r` (`H_F(z, ζ) - H_F(z, 1) = -(3/2) z₃ > 0`)
  have hA : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      0 < switchingFn 1 0 (lieChart (r, x)).2.2 (lieChart (r, x)).1 := by
    have h := l6c_switching_estimate x 0 1 0
    simp only [zero_mul, ivf_vertexFlow_zero, flow_zero] at h
    obtain ⟨C, hC⟩ := h.bound
    set κ := RR (ζ ^ ((1 : Fin 3) : ℕ) - ζ ^ ((0 : Fin 3) : ℕ)) (fullerOfChart x 2)
    have hκ : κ = -(x 1 + x 2 * x 0) / 4 := by
      simp [κ, RR_eq_re_mul_add_im_mul, fullerOfChart, ζ_re, ζ_im]
      ring
    have hκ0 : 0 < κ := by rw [hκ]; linarith
    filter_upwards [hC, eventually_mem_nhdsWithin,
      (show ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 (12 * κ / (|C| + 1)) from
        Ioo_mem_nhdsGT (by positivity))] with r hr hr0 hr1
    have hr0' : (0 : ℝ) < r := hr0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hr0' 4)] at hr
    have hrC : r * (|C| + 1) ≤ 12 * κ := by
      have := hr1.2.le
      rwa [le_div_iff₀ (by positivity)] at this
    have h1 := (abs_le.1 hr).1
    have h3 : 0 < r ^ 3 := by positivity
    have h4 : C * r ^ 4 ≤ |C| * r ^ 4 := by gcongr; exact le_abs_self _
    have h5 : r ^ 3 * (r * (|C| + 1)) ≤ r ^ 3 * (12 * κ) := mul_le_mul_of_nonneg_left hrC h3.le
    nlinarith
  filter_upwards [hA, l6c_eventually_chi23Deriv_pos x h₂, l6c_eventually_traceForm_lt x 0,
    l6c_eventually_traceForm_lt x 1, l6c_eventually_traceForm_lt x 2, l6c_eventually_chart x]
    with r hA hB hd0 hd1 hd2 ⟨hr0, hr1, hc1, hc2⟩
  set q := lieChart (r, x)
  have hsymm : ∀ A B : Mat2, traceForm A B = traceForm B A := fun A B ↦ Matrix.trace_mul_comm A B
  have hd : ∀ m : Fin 3, traceForm q.1 (controlMatrix (vertex m)) < -(1 / 3) := by
    intro m; fin_cases m
    · exact hd0
    · exact hd1
    · exact hd2
  have hd' : ∀ m : Fin 3, traceForm (controlMatrix (vertex m)) q.1 ≠ 0 := fun m ↦ by
    rw [hsymm]; exact (hd m).trans (by norm_num) |>.ne
  -- the flow is continuous
  have hXc : Continuous fun t ↦ (iso_vertexFlow 1 q t).1 := ivf_vfX_continuous 1 q
  have hRc : Continuous fun t ↦ (iso_vertexFlow 1 q t).2.2 :=
    continuous_iff_continuousAt.2 fun t ↦ (l6c_hasDerivAt_flowΛR q t).continuousAt
  have h0q := ivf_vertexFlow_zero 1 q
  -- (B) `χ₂₃(0) = 0`, `χ₂₃'(0) > 0`
  have hf := l6c_hasDerivAt_chi23 q (hd' 2)
  have hf0 : switchingFn 1 2 (iso_vertexFlow 1 q 0).2.2 (iso_vertexFlow 1 q 0).1 = 0 := by
    rw [h0q]
    exact (l6c_chart_section hc1 hc2 (hd 1 |>.trans (by norm_num) |>.ne)
      (hd 2 |>.trans (by norm_num) |>.ne)).2
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hf).eventually (lt_mem_nhds hB)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < switchingFn 1 2 (iso_vertexFlow 1 q t).2.2 (iso_vertexFlow 1 q t).1 := by
    filter_upwards [hslope.filter_mono (nhdsWithin_mono _
      (show Ioi (0 : ℝ) ⊆ {0}ᶜ from fun t ht ↦ ne_of_gt ht)),
      eventually_mem_nhdsWithin] with t ht ht0
    rw [slope_def_field, hf0, sub_zero, sub_zero] at ht
    exact (div_pos_iff_of_pos_right ht0).1 ht
  obtain ⟨δ', hδ', hδ''⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hpos
  -- (C) continuity of `χ₂₁` and `⟨X, Z_m⟩` at `t = 0`
  have hg : ContinuousAt (fun t ↦ switchingFn 1 0 (iso_vertexFlow 1 q t).2.2
      (iso_vertexFlow 1 q t).1) 0 :=
    l6c_continuousAt_switchingFn hRc hXc 1 0 (by rw [h0q]; exact hd' 1) (by rw [h0q]; exact hd' 0)
  have hdc : ∀ m : Fin 3, ContinuousAt (fun t ↦ traceForm (iso_vertexFlow 1 q t).1
      (controlMatrix (vertex m))) 0 := fun m ↦
    ((hXc.matrix_mul continuous_const).matrix_trace).continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < switchingFn 1 0 (iso_vertexFlow 1 q t).2.2
      (iso_vertexFlow 1 q t).1 ∧ ∀ m : Fin 3, traceForm (iso_vertexFlow 1 q t).1
        (controlMatrix (vertex m)) < 0 := by
    refine (hg.eventually (lt_mem_nhds (by simp only [h0q]; exact hA))).and ?_
    have : ∀ m : Fin 3, ∀ᶠ t in 𝓝 (0 : ℝ), traceForm (iso_vertexFlow 1 q t).1
        (controlMatrix (vertex m)) < 0 := fun m ↦
      (hdc m).eventually (gt_mem_nhds (by simp only [h0q]; exact (hd m).trans (by norm_num)))
    filter_upwards [this 0, this 1, this 2] with t h0 h1 h2 m
    fin_cases m
    · exact h0
    · exact h1
    · exact h2
  obtain ⟨δ, hδ, hδ2⟩ := Metric.eventually_nhds_iff.1 hev
  have hδ'0 : 0 < δ' := hδ'
  refine ⟨min δ δ' / 2, div_pos (lt_min hδ hδ'0) two_pos, fun t ht v hv ↦ ?_⟩
  have htδ : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2, min_le_left δ δ']
  obtain ⟨hgt, hdt⟩ := hδ2 htδ
  refine l6c_hamiltonian_le_of_vertices (-1) _ _ _ hdt _ (fun m ↦ ?_) v hv
  fin_cases m
  · have := poly_hamiltonian_sub (-1) (iso_vertexFlow 1 q t).2.1 (iso_vertexFlow 1 q t).2.2
      (iso_vertexFlow 1 q t).1 1 0
    simp only [Fin.zero_eta]
    linarith
  · exact le_rfl
  · have := poly_hamiltonian_sub (-1) (iso_vertexFlow 1 q t).2.1 (iso_vertexFlow 1 q t).2.2
      (iso_vertexFlow 1 q t).1 1 2
    have hχ : 0 ≤ switchingFn 1 2 (iso_vertexFlow 1 q t).2.2 (iso_vertexFlow 1 q t).1 := by
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h, hf0]
      · exact (hδ'' ⟨h, by linarith [ht.2, min_le_right δ δ']⟩).le
    simp only [Fin.reduceFinMk]
    linarith

/-- **Lemma 14.2.3** (`lem:Lie-Fuller`, TeX 11720–11736). Let `(X, Λ₁, Λ_R)` solve the Reinhardt
ODE with constant control `Z₀₁₀ = e₂` from the chart point `(r₀, x̃⁰)`, in rescaled time
`s = t/r₀`, and let `z(s)` solve the Fuller ODE with constant control `ζ` from `z(x̃⁰)`. Then for
each `s`, as `r₀ → 0⁺`, `ẑ_k(X(s r₀), Λ₁(s r₀), Λ_R(s r₀)) = z_k(s) r₀^k + O(r₀^{k+1})`,
`k = 1, 2, 3` ("the leading term of the solutions of the Reinhardt and Fuller systems are in
agreement"; index `k` is `Fin 3` here, `k = 0` for `z₁`).

Proof: `l6c_fullerCoords_flow_isBigO`: the Grönwall comparison `l6c_flow_estimates` of the
`e₂`-flow with the leading chain `XF, BF, CF`, whose Cayley coordinates are the Fuller flow.
Departure from the paper: the book expands the explicit solutions as series in `r₀`; see the
module docstring. -/
theorem lemma14_2_3 (x : Fin 3 → ℝ) (s : ℝ) (k : Fin 3) :
    (fun r₀ : ℝ ↦ fullerCoords (iso_vertexFlow 1 (lieChart (r₀, x)) (s * r₀)) k -
        (r₀ : ℂ) ^ (k.val + 1) * flow s (fullerOfChart x) ζ k)
      =O[𝓝[>] 0] (fun r₀ ↦ r₀ ^ (k.val + 2)) := by
  exact l6c_fullerCoords_flow_isBigO x s k

/-- **Lemma 14.2.4** (`lem:chi-asymptotic`, (14.2.1) `eqn:cubic-sr3`, TeX 11743–11752): with the
setup of Lemma 14.2.3, `χ₂₁(X(s r₀), Λ₁(s r₀), Λ_R(s r₀)) = 24 r₀³ RR(ζ - 1, z₃(s)) + O(r₀⁴)`. The
right side is the Fuller switching function for the transition `ζ → 1`.

Proof: `l6c_switching_estimate` with `(i, j) = (e₂, e₁)`. -/
theorem lemma14_2_4 (x : Fin 3 → ℝ) (s : ℝ) :
    (fun r₀ : ℝ ↦ switchingFn 1 0 (iso_vertexFlow 1 (lieChart (r₀, x)) (s * r₀)).2.2
        (iso_vertexFlow 1 (lieChart (r₀, x)) (s * r₀)).1 -
        24 * r₀ ^ 3 * RR (ζ - 1) (flow s (fullerOfChart x) ζ 2))
      =O[𝓝[>] 0] (fun r₀ ↦ r₀ ^ 4) := by
  simpa using l6c_switching_estimate x s 1 0

/-- **The companion of Lemma 14.2.4 for `χ₂₃`** ("Similar formulas hold for the other switching
functions", TeX 11754–11755): `χ₂₃(X(s r₀), Λ₁(s r₀), Λ_R(s r₀)) = 24 r₀³ RR(ζ - ζ², z₃(s)) +
O(r₀⁴)`, the Fuller switching function for `ζ → ζ²`.

Proof: `l6c_switching_estimate` with `(i, j) = (e₂, e₃)`. -/
theorem lemma14_2_4_chi23 (x : Fin 3 → ℝ) (s : ℝ) :
    (fun r₀ : ℝ ↦ switchingFn 1 2 (iso_vertexFlow 1 (lieChart (r₀, x)) (s * r₀)).2.2
        (iso_vertexFlow 1 (lieChart (r₀, x)) (s * r₀)).1 -
        24 * r₀ ^ 3 * RR (ζ - ζ ^ 2) (flow s (fullerOfChart x) ζ 2))
      =O[𝓝[>] 0] (fun r₀ ↦ r₀ ^ 4) := by
  simpa using l6c_switching_estimate x s 1 2

end SmoothedPolygons
