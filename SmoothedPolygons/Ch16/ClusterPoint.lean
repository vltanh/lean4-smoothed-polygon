module

public import SmoothedPolygons.Ch16.ReinhardtShadowing
public import SmoothedPolygons.Ch16.SwitchStructure
public import SmoothedPolygons.Ch16.NextSwitch
public import Basic.Dynamics.HyperbolicBox

/-!
# Chapter 16: Theorem 16.4.1, the cluster point theorem (§16.4.3)

Theorem 16.4.1 (`thm:no-chatter`) of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX
12840–12846, proof 12989–13056): "If the sequence of switching points of a Pontryagin extremal
Reinhardt trajectory has a cluster point on the exceptional divisor of the blow-up, reached in
finite time, and if the switching points themselves are not on the exceptional divisor, then that
cluster point is the fixed point `q_in` and the switching points lie on the stable curve
`W^s(q_in)`."

Formal statement (`theorem16_4_1`): for a chattering arc into the singular locus
(`IsChatteringArcInto`, `λ_cost = -1`), (i) the angular components of the switching points converge
to `q_in` modulo `V_T` (the cluster point is `q_in`, and it is the only one), and (ii) for every
analytic extension `e` of the Reinhardt–Poincaré map at `q_out` (Lemma 14.3.1) and every
neighborhood `U` of the fixed point, eventually each switching point, rotated onto the section
`χ₂₃ = 0`, is the point `lieChartIn p` of the mirrored chart at `q_in` (Remark 14.3.4) with `p` on
the local unstable manifold of `e`, which is the local stable curve `W^s(q_in)` of `e⁻¹`, the
Reinhardt–Poincaré map in the mirrored chart (`remark14_3_4`; a `C^∞` curve, `theorem14_3_3`).
`theorem16_4_1_reverse` is the time reversal (switching points emanating from the divisor converge
to `q_out` backward and lie on `W^u(q_out)`), which the proof of Theorem 14.4.1 needs (REPORT.md,
E88).

## The book's proof (TeX 12991–13056), and this proof

The book: (a) a periodic set of switching points does not approach the divisor, so the switching
sequence is injective; (b) if `q_in` is a cluster point, the switching points lie on `W^s(q_in)`
and, by an `ε` versus `ε/r_scale` argument with the finite time, `q_in` is the only cluster point;
(c) `q_out` is not a cluster point, since otherwise the switching points would lie on
`W^s(q_out)`, which is contained in the divisor; (d) each cluster point is assigned to a part
`𝒟_i` through a subsequence in `𝒟_i^R`; (e) by the upper triangular structure of Table 16.1, a
cluster point in a part gives one in a smaller part, ending in `𝒟_out^R`; (f) a cluster point in
`𝒟_out^R` makes `q_out` a cluster point ("the dynamics are analytic on `𝒟_out^R`, and the set of
cluster points being closed"), against (c).

Gaps (REPORT.md, E90, E91): (b)'s `ε/r_scale` argument is unclear; (c) uses `W^s(q_out) ⊆ divisor`
globally, while Theorem 14.3.3 is local; (d)–(e) need the Reinhardt parts and branch maps of
§16.4.2 (unproved, E90) and ignore the diagonal rows of Table 16.1; (f) "analytic on
`𝒟_out^R`" is not established (Lemma 14.3.1 is local at the fixed point). Repair (along the book's
lines, with an ω-limit and hyperbolic-box argument):

1. (a) holds by construction: `τ` is strictly increasing (`IsSwitchingSeqInto`); the switching
   points have Fuller coordinates `→ 0`, `≠ 0` (`IsChatteringArcInto.switchPoints`).
2. `Ω = switchClusterSet` is nonempty (compactness of `Ξ`) and lies in `Ξ_{𝒲,0}/V_T`
   (`mapClusterPt_switchAng_mem_sectionZero`).
3. (c), local form: `q_out ∉ Ω` (`qOut0_not_mem_switchClusterSet`). Near `q_out`, rotated
   switching points with small `r` are chart points (`tendsto_lieChartInv_phaseOfFuller`,
   `lieChart_lieChartInv`; the section conditions `H(e₂) = H(e₃) = 0` hold because the two
   vertices of a switch maximize `H` with value `0` and `H(e₁) < 0` near the ray of `q_out`, by the
   uniform limit `tendstoUniformlyOn_rescaledHam`), and consecutive ones follow `e`
   (`IsChatteringArcInto.eventually_follows_out`:
   `IsChatteringArcInto.next_switchPoint_eq_reinPoincare` with
   `eventually_isSwitch_reinSwitchTime` and the switching structure at the chart point,
   `eventually_switchStructure`, see below); `e` fixes `(0, x̃_out)`, leaves `r = 0`
   invariant, expands transversally by `r_scale > 1` and contracts along the divisor (the
   derivative facts `hasStrictFDerivAt_extension`, not the stable manifold theorem), so the
   hyperbolic box (`Function.not_mapClusterPt_of_transverse_expansion`, with `W` the neighbourhood
   on which the chart sequence follows `e`) excludes `(0, x̃_out)` as a cluster point of the chart
   sequence, whose `r` tends to `0`. The chart sequence is built by choice (`lieChartInv` ignores
   `z₃` and the section conditions): the chart point in `W₀` of some rotation of `q_n` if there is
   one, else a junk point `(1/(n+1), x̃_out + 2)` outside the box. The representative is unique: two
   rotations of a phase point both on the section near `q_out` coincide, since `Ad_{R⁻¹}` and
   `Ad_{R⁻²}` would move the negative value of `H(e₁)` to `e₂` or `e₃` (`l6h_rep_unique`). No
   stable manifold theorem is used in steps 1–4, which give the first part of the theorem
   (`tendstoModVT_switchAng_of_clusterSetForwardInvariant`), the only part the assembly of
   Theorem 16.3.1 uses. The "stable curve" of step 5 is the local unstable set of `e`, by
   definition, and Theorem 14.3.3 (via Theorem A.3.1) adds that it is a `C^∞` curve; step 5 uses
   only the conjugacy `F_in = e⁻¹` of `remark14_3_4`, but at the level of declarations it depends on
   Theorem A.3.1 through `remark14_3_4`, whose unstable-curve clause is proved with it.
4. (d)–(f) replaced: `Ω` is forward invariant under `F_ang` (`ClusterSetForwardInvariant`, E90); a
   point `ω ≠ q_in` of `Ω` has `F^k(ω) → q_out` (Theorem 16.1.1, `theorem16_1_1`, with the three
   named numerical facts of Layer 5), so `q_out ∈ Ω` (closed: the image of the compact set of
   cluster points under the continuous class map): impossible by step 3. Hence `Ω = {q_in}`, and
   the angular components converge to `q_in` modulo `V_T` (`tendstoModVT_of_forall_mapClusterPt`).
5. (b), the stable curve: near `q_in`, the switching points rotated to the nearest point of the
   `V_T`-orbit of `ang q_in` are points of the mirrored chart
   (`tendsto_lieChartInInv_phaseOfFuller`)
   converging to `(0, x̃_out)`, and consecutive ones satisfy `e(p_{n+1}) = p_n`
   (`IsChatteringArcInto.eventually_follows_in`, `remark14_3_4`, the uniqueness of the
   representative, and the continuity of `e⁻¹` at the fixed point, which keeps
   `reinChartMapIn p_n = e⁻¹ p_n` in the region where the representative is unique); so
   `(p_n, p_{n+1}, …)` is a backward `e`-orbit in `U` tending to the fixed point, and `p_n` lies in
   the local unstable set of `e` (by definition).

**The switching structure at a chart point** (the book's own claim, stated without proof: "the
first control … is `u = e₂` for all sufficiently small `r > 0`", TeX 11706–11718, and "These
functions give the value of the Reinhardt–Poincaré map", TeX 11835–11836; proved here, E83): the
claim of `eventually_follows_out` needs which control an extremal uses right **after** the switching
point `lieChart p`, while `eventually_isSwitch_reinSwitchTime` describes only the flow with the
control `e₂`. Two exact computations on the section `Λ_R = h K(X)` decide it
(`SmoothedPolygons/Ch16/SwitchStructure.lean`): `H(e₁) = 6h/(3 + 3a² - c²)` with
`h = r³ G(r, x̃)`, `G(0, x̃) = 2(ℓ̃₁₁ + ℓ̃₂₁ x̃₂₁) < 0` at `x̃_out`, so `e₁` is not a maximizer; and
the slope of `χ₃₂` along the fields of `e₂` and `e₃` is `4√3 (c h + (Λ₁)₂₁ + 3/2)/(c² - 3a²)`
`= 4√3 r² (c r G + ℓ̃₂₁)/(c² - 3r²) < 0` (`ℓ̃₂₁ < 0` at `x̃_out`), so `e₃` would leave the maximum
at once. Hence the control after the switch is `e₂`, the extremal is the `e₂`-flow
(`iso_arc_eq_vertexFlow` for `IsExtremalOn`), and the next switch is at `t_sw` exactly
(`SmoothedPolygons/Ch16/NextSwitch.lean`). At `q_in` the same facts are transported by the
time reversal (`iso_vertexFlow_reinTau`, `switchingFn_reinTau`): the `e₃`-flow from `τ q` is the
reversed `e₂`-flow from `q`, as the review asks (`F_in = τ F⁻¹ τ`), with no estimate at `q_in`.

Departure from the paper: steps 3–5 replace (b)–(f) as described (forced by the gaps of E90 and
E91); the descent through Table 16.1 on Reinhardt parts is replaced by Theorem 16.1.1 applied to
the cluster set, which is the book's "Repeating the argument of Theorem 16.1.1" done once on the
Fuller side.
Size: about 1,000 lines here and in the two helper files.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology
open TriFuller


/-! ### Helpers: the chart coordinates of `phaseOfFuller (scale r ξ)` in closed form -/

/-- The chart coordinates of the phase point with Fuller coordinates `scale r ξ` (`r ≠ 0`), in a
form continuous at `r = 0` (`⟨w⟩ - 1 = |w|²/(⟨w⟩ + 1)`). -/
private noncomputable def l6h_chartG (p : ℝ × (Fin 3 → ℂ)) : ℝ × (Fin 3 → ℝ) :=
  (2 * p.1 * (p.2 0).im,
    ![((p.2 0).re + 2 * p.1 * ((p.2 0).re ^ 2 + (p.2 0).im ^ 2) /
        (jbr (2 * ((p.1 : ℂ) * p.2 0)) + 1)) / (p.2 0).im,
      3 * (p.2 1).re / (2 * (p.2 0).im ^ 2),
      (-6 * (p.2 1).im - 24 * p.1 ^ 2 * ((p.2 1).re ^ 2 + (p.2 1).im ^ 2) /
        (jbr (4 * I * ((p.1 : ℂ) ^ 2 * p.2 1)) + 1)) / (4 * (p.2 0).im ^ 2)])

private lemma l6h_lieChartInv_eq {r : ℝ} (hr : r ≠ 0) {ξ : Fin 3 → ℂ} (hξ : (ξ 0).im ≠ 0) :
    lieChartInv (phaseOfFuller (scale r ξ)) = l6h_chartG (r, ξ) := by
  have j0 := jbr_sq (2 * ((r : ℂ) * ξ 0))
  have j1 := jbr_sq (4 * I * ((r : ℂ) ^ 2 * ξ 1))
  have p0 := jbr_pos (2 * ((r : ℂ) * ξ 0))
  have p1 := jbr_pos (4 * I * ((r : ℂ) ^ 2 * ξ 1))
  have e2 : ((r : ℂ) ^ 2) = ((r ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e2] at j1 p1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.re_ofNat, Complex.im_ofNat] at j0 j1
  simp only [lieChartInv, phaseOfFuller, scale, l6h_chartG, e2, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  generalize jbr (2 * ((r : ℂ) * ξ 0)) = J0 at *
  generalize jbr (4 * I * (((r ^ 2 : ℝ) : ℂ) * ξ 1)) = J1 at *
  have q0 : J0 + 1 ≠ 0 := by linarith
  have q1 : J1 + 1 ≠ 0 := by linarith
  refine Prod.ext ?_ (funext fun i ↦ ?_)
  · simp; ring
  · fin_cases i
    · simp
      field_simp
      linear_combination j0
    · simp
      field_simp
      ring
    · simp
      field_simp
      linear_combination (-12) * j1

private lemma l6h_continuousAt_chartG {ξ : Fin 3 → ℂ} (hξ : (ξ 0).im ≠ 0) :
    ContinuousAt l6h_chartG (0, ξ) := by
  have hj : Continuous jbr := by unfold jbr; fun_prop
  have hj0 : Continuous fun p : ℝ × (Fin 3 → ℂ) ↦ jbr (2 * ((p.1 : ℂ) * p.2 0)) + 1 :=
    (hj.comp (by fun_prop)).add continuous_const
  have hj1 : Continuous fun p : ℝ × (Fin 3 → ℂ) ↦ jbr (4 * I * ((p.1 : ℂ) ^ 2 * p.2 1)) + 1 :=
    (hj.comp (by fun_prop)).add continuous_const
  have hpos : ∀ w, jbr w + 1 ≠ 0 := fun w ↦ by linarith [jbr_pos w]
  have him : ContinuousAt (fun p : ℝ × (Fin 3 → ℂ) ↦ (p.2 0).im) (0, ξ) := by fun_prop
  have hre : ∀ k : Fin 3, Continuous fun p : ℝ × (Fin 3 → ℂ) ↦ (p.2 k).re := fun k ↦ by fun_prop
  have him' : ∀ k : Fin 3, Continuous fun p : ℝ × (Fin 3 → ℂ) ↦ (p.2 k).im := fun k ↦ by fun_prop
  refine ContinuousAt.prodMk (by fun_prop) (continuousAt_pi.2 fun i ↦ ?_)
  fin_cases i
  · exact ((hre 0).continuousAt.add ((((continuous_const.mul continuous_fst).mul
      (((hre 0).pow 2).add ((him' 0).pow 2))).div hj0 fun p ↦ hpos _).continuousAt)).div him hξ
  · exact ((continuous_const.mul (hre 1)).continuousAt).div (continuousAt_const.mul (him.pow 2))
      (by simpa using hξ)
  · exact (((continuous_const.mul (him' 1)).sub (((continuous_const.mul
      (continuous_fst.pow 2)).mul (((hre 1).pow 2).add ((him' 1).pow 2))).div hj1
        fun p ↦ hpos _)).continuousAt).div (continuousAt_const.mul (him.pow 2))
      (by simpa using hξ)

private lemma l6h_chartG_zero (ξ : Fin 3 → ℂ) :
    l6h_chartG (0, ξ) = (0, fullerChartInv ξ) := by
  refine Prod.ext (by simp [l6h_chartG]) (funext fun i ↦ ?_)
  fin_cases i <;> simp [l6h_chartG, fullerChartInv]; ring

private lemma l6h_continuous_tau : Continuous tau := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i
  · exact Complex.continuous_conj.comp (continuous_apply 0)
  · exact (Complex.continuous_conj.comp (continuous_apply 1)).neg
  · exact Complex.continuous_conj.comp (continuous_apply 2)

/-- The time reversal of phase points is `τ` in Fuller coordinates. -/
private lemma l6h_reinTau_phaseOfFuller (z : Fin 3 → ℂ) :
    reinTau (phaseOfFuller z) = phaseOfFuller (tau z) := by
  have hb := reinTau_spec.2.1 _ (isBlowupPhasePt_phaseOfFuller z)
  rw [← phaseOfFuller_fullerCoords hb, fullerCoords_reinTau, fullerCoords_phaseOfFuller]

/-- **The chart covers the switching points near `q_out`**: for `ξ` with `Im ξ₁ > 0` (as `q_out`'s
representatives on `𝒲₀`), the chart coordinates of the phase point with Fuller coordinates
`(r ξ'₁, r² ξ'₂, r³ ξ'₃)` tend to `(0, fullerChartInv ξ)` as `r → 0⁺`, `ξ' → ξ` (the change of chart
between the coordinates of §16.4.1 and the chart of §14.1, which the book does not give:
`r_chart = X₁₁ = 2 r Im ξ'₁`, `x̃₂₁ = (X₂₁ - 1)/X₁₁ → Re ξ₁/Im ξ₁`, …). -/
theorem tendsto_lieChartInv_phaseOfFuller {ξ : Fin 3 → ℂ} (hξ : 0 < (ξ 0).im) :
    Tendsto (fun p : ℝ × (Fin 3 → ℂ) ↦ lieChartInv (phaseOfFuller (scale p.1 p.2)))
      (𝓝[{p | 0 < p.1}] (0, ξ)) (𝓝 (0, fullerChartInv ξ)) := by
  rw [← l6h_chartG_zero]
  refine ((l6h_continuousAt_chartG hξ.ne').tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  have hc : ContinuousAt (fun p : ℝ × (Fin 3 → ℂ) ↦ (p.2 0).im) (0, ξ) := by fun_prop
  have him : ∀ᶠ p in 𝓝[{p : ℝ × (Fin 3 → ℂ) | 0 < p.1}] ((0 : ℝ), ξ), (p.2 0).im ≠ 0 :=
    nhdsWithin_le_nhds (hc.eventually_ne hξ.ne')
  filter_upwards [him, self_mem_nhdsWithin] with p hp hp1
  exact (l6h_lieChartInv_eq (ne_of_gt hp1) hp).symm

/-- **The mirrored chart covers the switching points near `q_in`**: for `Im ξ₁ < 0` (as `q_in`'s
representatives), the mirrored chart coordinates tend to `(0, fullerChartInv (τ ξ))`. -/
theorem tendsto_lieChartInInv_phaseOfFuller {ξ : Fin 3 → ℂ} (hξ : (ξ 0).im < 0) :
    Tendsto (fun p : ℝ × (Fin 3 → ℂ) ↦ lieChartInInv (phaseOfFuller (scale p.1 p.2)))
      (𝓝[{p | 0 < p.1}] (0, ξ)) (𝓝 (0, fullerChartInv (tau ξ))) := by
  have hτξ : 0 < (tau ξ 0).im := by simp [tau]; linarith
  have hmap : Tendsto (fun p : ℝ × (Fin 3 → ℂ) ↦ (p.1, tau p.2)) (𝓝[{p | 0 < p.1}] (0, ξ))
      (𝓝[{p | 0 < p.1}] (0, tau ξ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_fst.prodMk (l6h_continuous_tau.comp continuous_snd)).tendsto'
        _ _ rfl).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with p hp using hp
  refine ((tendsto_lieChartInv_phaseOfFuller hτξ).comp hmap).congr fun p ↦ ?_
  simp only [Function.comp, lieChartInInv]
  rw [l6h_reinTau_phaseOfFuller, tau_scale]

/-- **Near `q_out`, consecutive switching points follow the extended map** (Lemma 14.3.1: "These
functions give the value of the Reinhardt–Poincaré map", TeX 11838): along a chattering arc, if the
`n`-th switching point, rotated by `Ad_{R⁻ᵏ}`, is the chart point `lieChart p` with `p` near
`(0, x̃_out)` and `r > 0`, then the next one, rotated by `Ad_{R^{-(k+1)}}`, is `lieChart (e p)`:
the extremal follows the control `e₂` (rotated) from the `n`-th switching point, the unique optimal
control (`eventually_isSwitch_reinSwitchTime`), and switches next at `reinSwitchTime`.

Proof: `IsChatteringArcInto.next_switchPoint_eq_reinPoincare`. That the control after the switching
point is `e₂` is not in `eventually_isSwitch_reinSwitchTime` (which describes only the `e₂`-flow):
it comes from the switching structure at the chart point, `eventually_switchStructure`
(`H(e₁) < 0 = H(e₂)`, and `H(e₃) < H(e₂)` right after along the `e₃`-flow). -/
theorem IsChatteringArcInto.eventually_follows_out {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ)
    {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) :
    ∃ W ∈ 𝓝 chartPtOut, ∀ (n k : ℕ) (p : ℝ × (Fin 3 → ℝ)), p ∈ W → 0 < p.1 →
      iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = lieChart p →
        0 < (e p).1 ∧ iso_adRinvPow (k + 1) (phaseAt X Λ₁ ΛR (τ (n + 1))) = lieChart (e p) := by
  obtain ⟨hsrc, -, -, -, hpos, -⟩ := he
  have hsrc' : ∀ᶠ p in 𝓝[{p : ℝ × (Fin 3 → ℝ) | 0 < p.1}] chartPtOut, p ∈ e.source :=
    nhdsWithin_le_nhds (e.open_source.mem_nhds hsrc)
  obtain ⟨W, hW, hWsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1
    (eventually_isSwitch_reinSwitchTime.and (eventually_switchStructure.and hsrc'))
  refine ⟨W, hW, fun n k p hpW hp0 hq ↦ ?_⟩
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨-, hstruct⟩, hpe⟩ := hWsub ⟨hpW, hp0⟩
  obtain ⟨hH0, hH1, -, hε⟩ := hstruct (lieChart p) (Or.inl rfl)
  have hnext := IsChatteringArcInto.next_switchPoint_eq_reinPoincare h n k hq (by rw [hH1]; exact
      hH0) hε h1 h2 h3
  rw [hpos p hpe hp0]
  exact ⟨h4.1, by rw [hnext, h5]⟩

/-- **Near `q_in`, consecutive switching points follow the inverse of the extended map** (Remark
14.3.4 in the mirrored chart): if the `n`-th switching point, rotated by `Ad_{R⁻ᵏ}`, is
`lieChartIn p` with `p` near `(0, x̃_out)` and `r > 0`, then the next one, rotated by
`Ad_{R^{-(k+1)}}`, is `lieChartIn p'` with `p' = reinChartMapIn p`, `r > 0` and `e p' = p`.

Proof: through `F_in = τ F⁻¹ τ` (`remark14_3_4`), not by direct estimates at `q_in`, where the
switching functions have near-degenerate pairs of roots (see the module docstring of
`SmoothedPolygons/Ch14/FixedPointManifolds.lean`): `remark14_3_4` gives the `e₂`-flow from
`lieChartIn p` and `e (reinChartMapIn p) = p`; the switching structure at `lieChartIn p` itself
(`eventually_switchStructure`) is that of `lieChart p` transported by the time reversal
(`iso_vertexFlow_reinTau`, `switchingFn_reinTau`: the `e₃`-flow from `τ q` is the reversed
`e₂`-flow from `q`); then `IsChatteringArcInto.next_switchPoint_eq_reinPoincare`. -/
theorem IsChatteringArcInto.eventually_follows_in {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ)
    {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) :
    ∃ W ∈ 𝓝 chartPtOut, ∀ (n k : ℕ) (p : ℝ × (Fin 3 → ℝ)), p ∈ W → 0 < p.1 →
      iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = lieChartIn p →
        0 < (reinChartMapIn p).1 ∧ e (reinChartMapIn p) = p ∧
          iso_adRinvPow (k + 1) (phaseAt X Λ₁ ΛR (τ (n + 1))) = lieChartIn (reinChartMapIn p) := by
  obtain ⟨W, hW, hWsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1
    ((remark14_3_4 he).2.1.and eventually_switchStructure)
  refine ⟨W, hW, fun n k p hpW hp0 hq ↦ ?_⟩
  obtain ⟨⟨h1, h2, h3, h4, h5, -, h6⟩, ⟨-, hstruct⟩⟩ := hWsub ⟨hpW, hp0⟩
  obtain ⟨hH0, hH1, -, hε⟩ := hstruct (lieChartIn p) (Or.inr rfl)
  have hnext := IsChatteringArcInto.next_switchPoint_eq_reinPoincare h n k hq (by rw [hH1]; exact
      hH0) hε h1 h2 h3
  exact ⟨h4, h6, by rw [hnext, h5]⟩

/-! ### Helpers: rotations of the switching points -/

private lemma l6h_trace_conj_pow (k : ℕ) (M : Mat2) (h : M.trace = 0) :
    (R⁻¹ ^ k * M * R ^ k).trace = 0 := by
  rw [poly_trace_conj (poly_Rpow_mul_Rinvpow k), h]

/-- `Ad_{R⁻ᵏ}` is multiplication by `ζᵏ` in Fuller coordinates (`fullerCoords_adR`). -/
private lemma l6h_fullerCoords_adRinvPow (k : ℕ) {q : iso_PhasePt} (h1 : q.1.trace = 0)
    (h2 : q.2.1.trace = 0) (h3 : q.2.2.trace = 0) :
    fullerCoords (iso_adRinvPow k q) = ζ ^ k • fullerCoords q := by
  induction k with
  | zero => rw [irt_adRinvPow_zero, pow_zero, one_smul]
  | succ k ih =>
    have e : iso_adRinvPow (k + 1) q = iso_adRinvPow 1 (iso_adRinvPow k q) := by
      rw [irt_adRinvPow_add, add_comm]
    rw [e, (fullerCoords_adR _ (l6h_trace_conj_pow k _ h1) (l6h_trace_conj_pow k _ h2)
      (l6h_trace_conj_pow k _ h3)).2, ih, smul_smul, ← pow_succ']

/-- The Hamiltonians relabel under `Ad_{R⁻ᵏ}`: `H(e_{m+k})(Ad_{R⁻ᵏ} q) = H(e_m)(q)`. -/
private lemma l6h_phaseHam_adRinvPow (k : ℕ) (q : iso_PhasePt) (m : Fin 3) :
    phaseHam (iso_adRinvPow k q) (vertex (m + ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩)) =
      phaseHam q (vertex m) :=
  poly_hamiltonian_conj (poly_Rpow_mul_Rinvpow k) (poly_conj_pow_J k)
    (by rw [ivf_conj_pow_controlMatrix, iso_rotControl_vertex]) (-1) q.2.1 q.2.2 q.1

/-- `Ad_{R⁻ᵏ}` preserves the phase points of the blow-up (it fixes `J`). -/
private lemma l6h_isBlowupPhasePt_adRinvPow (k : ℕ) {q : iso_PhasePt} (hq : IsBlowupPhasePt q) :
    IsBlowupPhasePt (iso_adRinvPow k q) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hq
  have hC := poly_Rpow_mul_Rinvpow k
  have hs : ∀ M : Mat2, M 0 1 - M 1 0 = traceForm M J := fun M ↦ by
    simp [traceForm, J, Matrix.trace_fin_two, Matrix.mul_apply]; ring
  have key : ∀ M : Mat2,
      (R⁻¹ ^ k * M * R ^ k) 0 1 - (R⁻¹ ^ k * M * R ^ k) 1 0 = M 0 1 - M 1 0 := by
    intro M
    rw [hs, hs]
    conv_lhs => rw [← poly_conj_pow_J k]
    exact poly_traceForm_conj hC M J
  refine ⟨(poly_trace_conj hC _).trans h1, (poly_trace_conj hC _).trans h2,
    (poly_trace_conj hC _).trans h3, (poly_det_conj hC _).trans h4, (poly_det_conj hC _).trans h5,
    (poly_traceForm_conj hC _ _).trans h6, ?_, ?_⟩
  · have := key q.1; change (R⁻¹ ^ k * q.1 * R ^ k) 0 1 < (R⁻¹ ^ k * q.1 * R ^ k) 1 0
    linarith
  · have := key q.2.1; change (R⁻¹ ^ k * q.2.1 * R ^ k) 1 0 < (R⁻¹ ^ k * q.2.1 * R ^ k) 0 1
    linarith

/-- **The rotation of a point of the section is unique**: two rotations `Ad_{R^{-k₁}} q`,
`Ad_{R^{-k₂}} q` of the same phase point, the first with `H(e₁) < 0` and the second with
`H(e₂) = H(e₃) = 0`, coincide (a rotation by `Ad_{R⁻¹}` or `Ad_{R⁻²}` would move the negative
value of `H(e₁)` to `e₂` or `e₃`, `l6h_phaseHam_adRinvPow`). -/
private lemma l6h_rep_unique {q q₁ q₂ : iso_PhasePt} {k₁ k₂ : ℕ}
    (h₁ : iso_adRinvPow k₁ q = q₁) (h₂ : iso_adRinvPow k₂ q = q₂)
    (hq₁ : phaseHam q₁ (vertex 0) < 0)
    (hq₂ : phaseHam q₂ (vertex 1) = 0 ∧ phaseHam q₂ (vertex 2) = 0) : q₁ = q₂ := by
  obtain ⟨j, hj3, hrot⟩ : ∃ j, j < 3 ∧ iso_adRinvPow j q₁ = q₂ := by
    refine ⟨(k₂ + 2 * k₁) % 3, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [← h₁, irt_adRinvPow_add, irt_adRinvPow_mod, ← h₂, irt_adRinvPow_mod k₂]
    congr 1
    omega
  interval_cases j
  · rwa [irt_adRinvPow_zero] at hrot
  · have hH := l6h_phaseHam_adRinvPow 1 q₁ 0
    rw [hrot] at hH
    have e : (0 : Fin 3) + ⟨1 % 3, Nat.mod_lt _ (by norm_num)⟩ = 1 := rfl
    rw [e, hq₂.1] at hH
    linarith
  · have hH := l6h_phaseHam_adRinvPow 2 q₁ 0
    rw [hrot] at hH
    have e : (0 : Fin 3) + ⟨2 % 3, Nat.mod_lt _ (by norm_num)⟩ = 2 := rfl
    rw [e, hq₂.2] at hH
    linarith

/-- **A switching point whose rotation has `H(e₁) < 0` lies, rotated, on the section**: the two
vertices of the switch maximize `H` with value `0`
(`IsExtremalOn.exists_phaseHam_eq_zero_of_isSwitchingTime`), and neither is `e₁`. -/
private lemma l6h_switch_section {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n k : ℕ)
    (h0 : phaseHam (iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n))) (vertex 0) < 0) :
    phaseHam (iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n))) (vertex 1) = 0 ∧
      phaseHam (iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n))) (vertex 2) = 0 := by
  obtain ⟨hext, -, -, -, -, hτI, -, hsw⟩ := h
  obtain ⟨i, j, hij, -, hi, hj⟩ := IsExtremalOn.exists_phaseHam_eq_zero_of_isSwitchingTime hext
      (hτI n) ((hsw _ (hτI n)).2 ⟨n, rfl⟩)
  have hi' := l6h_phaseHam_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) i
  have hj' := l6h_phaseHam_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) j
  rw [hi] at hi'
  rw [hj] at hj'
  have hne : i + ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩ ≠ j + ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩ :=
    fun h' ↦ hij (add_right_cancel h')
  generalize i + ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩ = i' at hi' hne
  generalize j + ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩ = j' at hj' hne
  generalize iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = q at hi' hj' h0 ⊢
  fin_cases i' <;> fin_cases j' <;> simp_all

/-- `φ(z_n) → 0⁺` along the switching points. -/
private lemma l6h_tendsto_radius {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) :
    Tendsto (fun n ↦ weightedNorm (fullerCoords (phaseAt X Λ₁ ΛR (τ n)))) atTop (𝓝[>] 0) := by
  obtain ⟨-, -, hne, hlim, -⟩ := h.switchPoints
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n ↦ weightedNorm_pos (hne n)⟩
  have := (continuous_weightedNorm.tendsto 0).comp hlim
  rwa [weightedNorm_zero] at this

/-- **The rotated switching points in Fuller coordinates**: `Ad_{R⁻ᵏ}(q_n)` is a phase point of the
blow-up with a star state, `phaseOfFuller (scale ρ_n (ζᵏ ξ_n))`, `ρ_n = φ(ẑ(q_n))`. -/
private lemma l6h_rot_point {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n k : ℕ) :
    IsBlowupPhasePt (iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n))) ∧
      IsStarState (iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n))).1 ∧
      iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) =
        phaseOfFuller (scale (weightedNorm (fullerCoords (phaseAt X Λ₁ ΛR (τ n))))
          (ζ ^ k • switchAng X Λ₁ ΛR τ n)) := by
  obtain ⟨hblow, -, hne, -, -⟩ := h.switchPoints
  have hτI := (h.2.2.2.2.2.1 n)
  have hmem : τ n ∈ Icc a b := ⟨hτI.1.le, hτI.2.le⟩
  have hb := hblow _ hmem
  have hb' := l6h_isBlowupPhasePt_adRinvPow k hb
  have hst : IsStarState (X (τ n)) := by
    have := (h.1.1.2.2.2.1 (τ n - a) ⟨by linarith [hτI.1], by linarith [hτI.2]⟩).2
    simpa using this
  refine ⟨hb', poly_isStarState_conj_pow k hst, ?_⟩
  rw [← phaseOfFuller_fullerCoords hb', l6h_fullerCoords_adRinvPow k hb.1 hb.2.1 hb.2.2.1,
    switchAng, scale_smul, scale_weightedNorm_ang (hne n)]

/-- The first chart coordinate of `phaseOfFuller (scale r ξ)` is `2 r Im ξ₁`. -/
private lemma l6h_phaseOfFuller_scale_00 (r : ℝ) (ξ : Fin 3 → ℂ) :
    (phaseOfFuller (scale r ξ)).1 0 0 = 2 * r * (ξ 0).im := by
  simp [phaseOfFuller, scale]; ring

/-- `fullerChartInv` is invariant under the virial rescalings. -/
private lemma l6h_fullerChartInv_scale {c : ℝ} (hc : c ≠ 0) (z : Fin 3 → ℂ) :
    fullerChartInv (scale c z) = fullerChartInv z := by
  funext i
  fin_cases i <;> simp [fullerChartInv, scale]
  · by_cases h : (z 0).im = 0
    · simp [h]
    · field_simp
  · by_cases h : (z 0).im = 0
    · simp [h]
    · field_simp
  · by_cases h : (z 0).im = 0
    · simp [h]
    · field_simp

/-- `H_F(q_out, 1) < 0`, and the angular components of `q_out` and `q_in`: `Im ξ₁` has the sign
of `±1`, `H_F(·, 1) < 0`, and their chart coordinates are `x̃_out`. -/
private lemma l6h_qOut_facts :
    0 < (ang qOutCart 0).im ∧ ham (ang qOutCart) 1 < 0 ∧ (ang (tau qOutCart) 0).im < 0 ∧
      ham (ang (tau qOutCart)) 1 < 0 ∧ fullerChartInv (ang qOutCart) = xTildeOut ∧
      fullerChartInv (tau (ang (tau qOutCart))) = xTildeOut := by
  obtain ⟨hq0, -, -⟩ := qOutCart_signs
  obtain ⟨-, him2, hre2⟩ := qOutCart_normalization
  have hc := inv_pos.2 (weightedNorm_pos qOutCart_ne_zero)
  have hc' := inv_pos.2 (weightedNorm_pos tau_qOutCart_ne_zero)
  have hscale : ∀ (c : ℝ) z (u : ℂ), ham (scale c z) u = c ^ 3 * ham z u := by
    intro c z u
    have := ham_smul_scale (v := 1) (by simp) c z u
    simpa using this
  have h1 : ham qOutCart 1 < 0 := by
    have hH := hamMax_qOutCart
    have hd : ham qOutCart 1 - ham qOutCart ζ = 3 / 2 * (qOutCart 2).re := by
      simp only [ham, RR_eq_re_mul_add_im_mul, ζ_re, ζ_im, him2, Complex.one_re, Complex.one_im]
      ring
    have hle : ham qOutCart ζ ≤ 0 := by
      rw [← hH, hamMax]; exact (le_max_left _ _).trans (le_max_right _ _)
    linarith
  have hang : ang qOutCart = scale (weightedNorm qOutCart)⁻¹ qOutCart := rfl
  have hτang : tau (ang (tau qOutCart)) = ang qOutCart := by rw [tau_ang, tau_tau]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hang]; simpa [scale] using mul_pos hc hq0
  · rw [hang, hscale]; exact mul_neg_of_pos_of_neg (by positivity) h1
  · have : (ang (tau qOutCart) 0).im = -(tau (ang (tau qOutCart)) 0).im := by simp [tau]
    rw [this, hτang, hang]; simpa [scale] using mul_pos hc hq0
  · rw [← tau_ang, ham_tau, map_one, hang, hscale]
    exact mul_neg_of_pos_of_neg (by positivity) h1
  · rw [hang, l6h_fullerChartInv_scale hc.ne']; rfl
  · rw [hτang, hang, l6h_fullerChartInv_scale hc.ne']; rfl

/-- **`H(e₁) < 0` near the rays of `q_out` and `q_in`** (the rescaled Hamiltonians converge to
`24 H_F` uniformly, `tendstoUniformlyOn_rescaledHam`): if `ρ_m → 0⁺` and `y_m → ξ` with
`H_F(ξ, 1) < 0`, then eventually `H(e₁) < 0` at `phaseOfFuller (scale ρ_m y_m)`. -/
private lemma l6h_eventually_ham0_neg {ξ : Fin 3 → ℂ} (hneg : ham ξ 1 < 0) {ρ : ℕ → ℝ}
    {y : ℕ → Fin 3 → ℂ} (hρ : Tendsto ρ atTop (𝓝[>] 0)) (hy : Tendsto y atTop (𝓝 ξ)) :
    ∀ᶠ m in atTop, phaseHam (phaseOfFuller (scale (ρ m) (y m))) (vertex 0) < 0 := by
  set L := 24 * ham ξ 1 with hL
  have hL0 : L < 0 := by rw [hL]; linarith
  have hU := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_rescaledHam (isCompact_closedBall ξ 1)) (-L / 4) (by linarith)
  have hU' := hρ.eventually hU
  have hv0 : simplexToUT (vertex 0) = 1 := by
    simp [simplexToUT, Fin.sum_univ_three, vertex]
  have hham : Continuous fun w : Fin 3 → ℂ ↦ 24 * ham w 1 := by
    unfold ham; simp only [RR]; fun_prop
  have h1 : ∀ᶠ m in atTop, 24 * ham (y m) 1 < 3 * L / 4 :=
    (hham.tendsto ξ |>.comp hy).eventually (gt_mem_nhds (by linarith))
  have h2 : ∀ᶠ m in atTop, y m ∈ Metric.closedBall ξ 1 :=
    hy.eventually (Metric.closedBall_mem_nhds ξ one_pos)
  have h3 : ∀ᶠ m in atTop, 0 < ρ m := hρ.eventually self_mem_nhdsWithin
  filter_upwards [hU', h1, h2, h3] with m hm h1m h2m h3m
  have := hm (vertex 0, y m) ⟨poly_vertex_mem 0, h2m⟩
  simp only [hv0, Real.dist_eq] at this
  have hlt : phaseHam (phaseOfFuller (scale (ρ m) (y m))) (vertex 0) / ρ m ^ 3 < 0 := by
    have := (abs_lt.1 this); linarith
  have hp : 0 < ρ m ^ 3 := by positivity
  have := (div_lt_iff₀ hp).1 hlt
  simpa using this

/-- **The rotated switching points near `q_out` are chart points**: if the angular components,
rotated by `ζ^{k_m}`, tend to `ang q_out` along `φ m → ∞`, then the chart coordinates
`p_m = lieChartInv (Ad_{R^{-k_m}} q_{φ m})` tend to `(0, x̃_out)`
(`tendsto_lieChartInv_phaseOfFuller`)
and eventually `r > 0` and `lieChart p_m = Ad_{R^{-k_m}} q_{φ m}` (the section conditions hold:
`H(e₁) < 0` there, `l6h_eventually_ham0_neg`, `l6h_switch_section`; `lieChart_lieChartInv`). -/
private lemma l6h_tendsto_chart_out {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) {φ k : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop)
    (hy : Tendsto (fun m ↦ ζ ^ k m • switchAng X Λ₁ ΛR τ (φ m)) atTop (𝓝 (ang qOutCart))) :
    Tendsto (fun m ↦ lieChartInv (iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m))))) atTop
        (𝓝 chartPtOut) ∧
      ∀ᶠ m in atTop, 0 < (lieChartInv (iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m))))).1 ∧
        phaseHam (iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m)))) (vertex 0) < 0 ∧
        lieChart (lieChartInv (iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m))))) =
          iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m))) := by
  obtain ⟨hIm, hham, -, -, hx, -⟩ := l6h_qOut_facts
  set ρ : ℕ → ℝ := fun m ↦ weightedNorm (fullerCoords (phaseAt X Λ₁ ΛR (τ (φ m)))) with hρdef
  set y : ℕ → Fin 3 → ℂ := fun m ↦ ζ ^ k m • switchAng X Λ₁ ΛR τ (φ m) with hydef
  have hρ : Tendsto ρ atTop (𝓝[>] 0) := (l6h_tendsto_radius h).comp hφ
  have hq : ∀ m, iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m))) =
      phaseOfFuller (scale (ρ m) (y m)) := fun m ↦ (l6h_rot_point h (φ m) (k m)).2.2
  have hpair : Tendsto (fun m ↦ (ρ m, y m)) atTop
      (𝓝[{p : ℝ × (Fin 3 → ℂ) | 0 < p.1}] ((0 : ℝ), ang qOutCart)) :=
    tendsto_nhdsWithin_iff.2 ⟨(hρ.mono_right nhdsWithin_le_nhds).prodMk_nhds hy,
      hρ.eventually self_mem_nhdsWithin⟩
  have hlim := (tendsto_lieChartInv_phaseOfFuller hIm).comp hpair
  rw [hx] at hlim
  refine ⟨by simp only [hq]; exact hlim, ?_⟩
  have hIm' : ∀ᶠ m in atTop, 0 < (y m 0).im :=
    ((Complex.continuous_im.comp (continuous_apply 0)).tendsto _ |>.comp hy).eventually
      (lt_mem_nhds hIm)
  filter_upwards [hIm', l6h_eventually_ham0_neg hham hρ hy,
    hρ.eventually self_mem_nhdsWithin] with m h1 h2 h3
  have h3 : 0 < ρ m := h3
  rw [← hq] at h2
  obtain ⟨hb, hst, -⟩ := l6h_rot_point h (φ m) (k m)
  obtain ⟨hH1, hH2⟩ := l6h_switch_section h (φ m) (k m) h2
  have hr : 0 < (iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m)))).1 0 0 := by
    rw [hq, l6h_phaseOfFuller_scale_00]; positivity
  have hχ : switchingFn 1 2 (iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m)))).2.2
      (iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m)))).1 = 0 := by
    have := poly_hamiltonian_sub (-1) (iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m)))).2.1
      (iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m)))).2.2
      (iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m)))).1 1 2
    simp only [phaseHam] at hH1 hH2
    linarith
  exact ⟨hr, h2, (lieChart_lieChartInv hb hst hH1 hχ hr).2⟩

/-- **The rotated switching points near `q_in` are points of the mirrored chart**: as
`l6h_tendsto_chart_out`, with `ang q_in = ang (τ q_out)` and `lieChartIn = reinTau ∘ lieChart`
(`tendsto_lieChartInInv_phaseOfFuller`). -/
private lemma l6h_tendsto_chart_in {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) {φ k : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop)
    (hy : Tendsto (fun m ↦ ζ ^ k m • switchAng X Λ₁ ΛR τ (φ m)) atTop
      (𝓝 (ang (tau qOutCart)))) :
    Tendsto (fun m ↦ lieChartInInv (iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m))))) atTop
        (𝓝 chartPtOut) ∧
      ∀ᶠ m in atTop, 0 < (lieChartInInv (iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m))))).1 ∧
        phaseHam (iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m)))) (vertex 0) < 0 ∧
        lieChartIn (lieChartInInv (iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m))))) =
          iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m))) := by
  obtain ⟨-, -, hIm, hham, -, hx⟩ := l6h_qOut_facts
  set ρ : ℕ → ℝ := fun m ↦ weightedNorm (fullerCoords (phaseAt X Λ₁ ΛR (τ (φ m)))) with hρdef
  set y : ℕ → Fin 3 → ℂ := fun m ↦ ζ ^ k m • switchAng X Λ₁ ΛR τ (φ m) with hydef
  have hρ : Tendsto ρ atTop (𝓝[>] 0) := (l6h_tendsto_radius h).comp hφ
  have hq : ∀ m, iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m))) =
      phaseOfFuller (scale (ρ m) (y m)) := fun m ↦ (l6h_rot_point h (φ m) (k m)).2.2
  have hpair : Tendsto (fun m ↦ (ρ m, y m)) atTop
      (𝓝[{p : ℝ × (Fin 3 → ℂ) | 0 < p.1}] ((0 : ℝ), ang (tau qOutCart))) :=
    tendsto_nhdsWithin_iff.2 ⟨(hρ.mono_right nhdsWithin_le_nhds).prodMk_nhds hy,
      hρ.eventually self_mem_nhdsWithin⟩
  have hlim := (tendsto_lieChartInInv_phaseOfFuller hIm).comp hpair
  rw [hx] at hlim
  refine ⟨by simp only [hq]; exact hlim, ?_⟩
  have hIm' : ∀ᶠ m in atTop, (y m 0).im < 0 :=
    ((Complex.continuous_im.comp (continuous_apply 0)).tendsto _ |>.comp hy).eventually
      (gt_mem_nhds hIm)
  filter_upwards [hIm', l6h_eventually_ham0_neg hham hρ hy,
    hρ.eventually self_mem_nhdsWithin] with m h1 h2 h3
  have h3 : 0 < ρ m := h3
  rw [← hq] at h2
  set q := iso_adRinvPow (k m) (phaseAt X Λ₁ ΛR (τ (φ m))) with hqdef
  obtain ⟨hb, hst, -⟩ := l6h_rot_point h (φ m) (k m)
  obtain ⟨hH1, hH2⟩ := l6h_switch_section h (φ m) (k m) h2
  have hτH : ∀ i : Fin 3, phaseHam (reinTau q) (vertex i) = phaseHam q (vertex (vertexSwap i)) :=
    fun i ↦ (switchingFn_reinTau i 0 q).2
  have hr : 0 < (reinTau q).1 0 0 := by
    change 0 < -(q.1 0 0)
    rw [hqdef, hq, l6h_phaseOfFuller_scale_00]
    nlinarith
  have hH1' : hamiltonian (-1) (reinTau q).2.1 (reinTau q).2.2 (reinTau q).1 (vertex 1) = 0 := by
    have := hτH 1; simp only [phaseHam] at this hH2; rw [this]; exact hH2
  have hχ : switchingFn 1 2 (reinTau q).2.2 (reinTau q).1 = 0 := by
    rw [(switchingFn_reinTau 1 2 q).1]
    change switchingFn 2 1 q.2.2 q.1 = 0
    have := poly_hamiltonian_sub (-1) q.2.1 q.2.2 q.1 2 1
    simp only [phaseHam] at hH1 hH2
    linarith
  have hrep := (lieChart_lieChartInv (reinTau_spec.2.1 q hb) (isStarState_matTau hst) hH1' hχ
    hr).2
  refine ⟨hr, h2, ?_⟩
  change reinTau (lieChart (lieChartInv (reinTau q))) = q
  rw [hrep, reinTau_spec.1]

/-- **`q_out` is not a cluster point** (TeX 13015–13026, claim (c) of the proof, repaired by the
hyperbolic box, E91): along a chattering arc into the singular locus, `q_out` is not a cluster
class of the switching points.

Proof. Fix an extension `e` (`lemma14_3_1`) and the neighborhood `W₀` of
`eventually_follows_out`; choose a smaller neighborhood `W₁` with `e(W₁) ⊆ W₀`, on which every
rotated switching point whose chart coordinates lie in `W₀` is a genuine chart point
(`lieChart_lieChartInv`; `lieChartInv` alone ignores `z₃` and the section conditions, so the
representation must be checked). Build the chart sequence **by choice**: `p_n = lieChartInv
(Ad_{R^{-k}} q_n)` for a rotation `k` that makes `q_n` a chart point in `W₀`, if there is one,
and otherwise a junk point `(1/(n+1), x̃_out + 2)` outside `W₁`. Then `(p n).1 → 0` (`X → J` along
the arc), and on `W₁`, `(p n).1 > 0` and `p (n + 1) = e (p n)` (`eventually_follows_out`, with
`e (p n) ∈ W₀` and the uniqueness of the chart representative, `l6h_rep_unique`). If
`q_out ∈ Ω`, infinitely many rotated switching points have Fuller classes
near `q_out` and small `r`, so their chart coordinates tend to `(0, x̃_out)`
(`tendsto_lieChartInv_phaseOfFuller`) and `(0, x̃_out)` is a cluster point of `p`, against
`Function.not_mapClusterPt_of_transverse_expansion` applied with `W = W₁` and the derivative facts
of `hasStrictFDerivAt_extension` (`∂_r e₁ = r_scale > 1`, the zero block, the Fuller block with
eigenvalues of modulus `< 1/10`, `e (0, x̃) = (0, fullerChartMap x̃)` near `x̃_out`). -/
theorem qOut0_not_mem_switchClusterSet {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) :
    qOut0 ∉ switchClusterSet (switchAng X Λ₁ ΛR τ) := by
  rintro ⟨ξ, hξs, hξc, hξcl⟩
  obtain ⟨e, he⟩ := lemma14_3_1
  obtain ⟨W₀, hW₀, hfol⟩ := h.eventually_follows_out he
  obtain ⟨Ws, hWs, hWsub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.1 eventually_switchStructure
  have hsrc := he.1
  have hfix := he.2.1
  set q : ℕ → iso_PhasePt := fun n ↦ phaseAt X Λ₁ ΛR (τ n) with hqdef
  -- the region where the switching structure holds, and the uniqueness of the representative
  set W₀' := W₀ ∩ Ws with hW₀'
  have hW₀'n : W₀' ∈ 𝓝 chartPtOut := inter_mem hW₀ hWs
  have hgood : ∀ p ∈ W₀', 0 < p.1 → p ∈ lieChartDomain ∧ phaseHam (lieChart p) (vertex 0) < 0 ∧
      phaseHam (lieChart p) (vertex 1) = 0 ∧ phaseHam (lieChart p) (vertex 2) = 0 := by
    intro p hp hp0
    obtain ⟨hdom, hst⟩ := hWsub ⟨hp.2, hp0⟩
    obtain ⟨a1, a2, a3, -⟩ := hst (lieChart p) (Or.inl rfl)
    exact ⟨hdom, a1, a2, a3⟩
  have huniq : ∀ (n k₁ k₂ : ℕ) (p₁ p₂ : ℝ × (Fin 3 → ℝ)), p₁ ∈ W₀' → 0 < p₁.1 → p₂ ∈ W₀' →
      0 < p₂.1 → iso_adRinvPow k₁ (q n) = lieChart p₁ → iso_adRinvPow k₂ (q n) = lieChart p₂ →
        p₁ = p₂ := by
    intro n k₁ k₂ p₁ p₂ h1 h1' h2 h2' e1 e2
    obtain ⟨d1, a1, -, -⟩ := hgood p₁ h1 h1'
    obtain ⟨d2, -, b2, b3⟩ := hgood p₂ h2 h2'
    have := l6h_rep_unique e1 e2 a1 ⟨b2, b3⟩
    rw [← (lieChart_spec d1).2.2.2.2.2, this, (lieChart_spec d2).2.2.2.2.2]
  -- the box neighbourhood `W₁`: inside `W₀'`, mapped into `W₀'` by `e`, and off the junk points
  have hpre : e ⁻¹' W₀' ∈ 𝓝 chartPtOut :=
    (e.continuousAt hsrc).preimage_mem_nhds (by rw [hfix]; exact hW₀'n)
  set W₁ := W₀' ∩ e ⁻¹' W₀' ∩ {p : ℝ × (Fin 3 → ℝ) | dist p.2 xTildeOut < 1} with hW₁
  have hW₁n : W₁ ∈ 𝓝 chartPtOut :=
    inter_mem (inter_mem hW₀'n hpre) ((isOpen_lt (continuous_snd.dist continuous_const)
      continuous_const).mem_nhds (by simp [chartPtOut]))
  set xfar : Fin 3 → ℝ := fun i ↦ xTildeOut i + 2 with hxfar
  have hfar : ∀ n : ℕ, ((1 / ((n : ℝ) + 1), xfar) : ℝ × (Fin 3 → ℝ)) ∉ W₁ := by
    intro n hn
    have := (dist_pi_lt_iff one_pos).1 hn.2 0
    simp [hxfar] at this
  -- **the chart sequence, by choice**: the representative in `W₀'` if there is one, else junk
  have hchoice : ∀ n, ∃ p : ℝ × (Fin 3 → ℝ),
      (∃ k, p ∈ W₀' ∧ 0 < p.1 ∧ iso_adRinvPow k (q n) = lieChart p) ∨
      ((¬ ∃ k, ∃ p' ∈ W₀', 0 < p'.1 ∧ iso_adRinvPow k (q n) = lieChart p') ∧
        p = (1 / ((n : ℝ) + 1), xfar)) := by
    intro n
    by_cases hex : ∃ k, ∃ p' ∈ W₀', 0 < p'.1 ∧ iso_adRinvPow k (q n) = lieChart p'
    · obtain ⟨k, p', hp', hp0, hk⟩ := hex
      exact ⟨p', Or.inl ⟨k, hp', hp0, hk⟩⟩
    · exact ⟨_, Or.inr ⟨hex, rfl⟩⟩
  choose p hp using hchoice
  -- on `W₁` the sequence follows `e` (`eventually_follows_out` and the uniqueness)
  have hfollow : ∀ n, p n ∈ W₁ → 0 < (p n).1 ∧ p (n + 1) = e (p n) := by
    intro n hn
    rcases hp n with ⟨k, hpW, hp0, hk⟩ | ⟨-, hjunk⟩
    · obtain ⟨he0, hek⟩ := hfol n k (p n) hpW.1 hp0 hk
      have heW : e (p n) ∈ W₀' := hn.1.2
      refine ⟨hp0, ?_⟩
      rcases hp (n + 1) with ⟨k', hpW', hp0', hk'⟩ | ⟨hno, -⟩
      · exact huniq (n + 1) k' (k + 1) _ _ hpW' hp0' heW he0 hk' hek
      · exact absurd ⟨k + 1, e (p n), heW, he0, hek⟩ hno
    · exact absurd (hjunk ▸ hn) (hfar n)
  -- `r → 0` along the sequence (`X → J`)
  have hr0 : Tendsto (fun n ↦ (p n).1) atTop (𝓝 0) := by
    obtain ⟨hblow, -, -, hlim, -⟩ := h.switchPoints
    have hq : ∀ n, q n = phaseOfFuller (fullerCoords (q n)) := fun n ↦
      (phaseOfFuller_fullerCoords (hblow _ ⟨(h.2.2.2.2.2.1 n).1.le,
        (h.2.2.2.2.2.1 n).2.le⟩)).symm
    have hq0 : phaseOfFuller 0 = singularPhasePt :=
      (fullerCoords_eq_zero_iff (isBlowupPhasePt_phaseOfFuller 0)).1
        (fullerCoords_phaseOfFuller 0)
    have hql : Tendsto q atTop (𝓝 singularPhasePt) := by
      rw [← hq0]
      have := (continuous_fullerCoords_phaseOfFuller.2.tendsto 0).comp hlim
      exact this.congr fun n ↦ (hq n).symm
    set f : ℕ → ℕ → ℝ := fun j n ↦ (iso_adRinvPow j (q n)).1 0 0 with hfdef
    have hf : ∀ j, Tendsto (f j) atTop (𝓝 0) := by
      intro j
      have hc : Continuous fun q : iso_PhasePt ↦ (iso_adRinvPow j q).1 0 0 :=
        (continuous_id.matrix_elem 0 0).comp (continuous_fst.comp (irt_continuous_adRinvPow j))
      have := (hc.tendsto _).comp hql
      have e0 : (iso_adRinvPow j singularPhasePt).1 0 0 = 0 := by
        change (R⁻¹ ^ j * J * R ^ j) 0 0 = 0
        rw [poly_conj_pow_J]; simp [J]
      rwa [e0] at this
    have hbound : ∀ n, |(p n).1| ≤ |f 0 n| + |f 1 n| + |f 2 n| + 1 / ((n : ℝ) + 1) := by
      intro n
      have hn0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
      rcases hp n with ⟨k, hpW, hp0, hk⟩ | ⟨-, hjunk⟩
      · have e1 : (p n).1 = f (k % 3) n := by
          rw [hfdef]; dsimp only
          rw [← irt_adRinvPow_mod, hk, (lieChart_spec (hgood _ hpW hp0).1).2.2.2.1]
        have hk3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
        rw [e1]
        interval_cases (k % 3) <;>
          linarith [abs_nonneg (f 0 n), abs_nonneg (f 1 n), abs_nonneg (f 2 n)]
      · rw [hjunk, abs_of_nonneg hn0]
        linarith [abs_nonneg (f 0 n), abs_nonneg (f 1 n), abs_nonneg (f 2 n)]
    have hg : Tendsto (fun n : ℕ ↦ |f 0 n| + |f 1 n| + |f 2 n| + 1 / ((n : ℝ) + 1)) atTop
        (𝓝 0) := by
      have := ((((hf 0).abs.add (hf 1).abs).add (hf 2).abs).add
        tendsto_one_div_add_atTop_nhds_zero_nat)
      simpa using this
    exact squeeze_zero_norm (fun n ↦ by rw [Real.norm_eq_abs]; exact hbound n) hg
  -- **`(0, x̃_out)` is a cluster point** of the chart sequence
  have hcl : MapClusterPt chartPtOut atTop p := by
    have hXi : ξ ∈ Xi := (isClosed_eq continuous_weightedNorm continuous_const).mem_of_mapClusterPt
      hξcl (Eventually.of_forall h.switchPoints.2.2.2.2)
    obtain ⟨hqs, hqc, -, -⟩ := classOf_qOutCart
    obtain ⟨v, hv, r, hr, hξeq⟩ := (classOf_eq_classOf_iff hqs hξs).1 (hqc.trans hξc.symm)
    have hξv : ξ = v • ang qOutCart := by
      rw [← ang_of_mem_Xi hXi, hξeq, (weightedNorm_ang_smul_scale qOutCart_ne_zero hr hv).2]
    obtain ⟨kk, hkk⟩ : ∃ kk : ℕ, ζ ^ kk * v = 1 := by
      rcases hv with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨2, by rw [← pow_succ, ζ_pow_three]⟩
      · exact ⟨1, by rw [pow_one, ← pow_succ', ζ_pow_three]⟩
    obtain ⟨ψ, hψ, hψl⟩ := hξcl.tendsto_subseq
    have hy : Tendsto (fun m ↦ ζ ^ (fun _ : ℕ ↦ kk) m • switchAng X Λ₁ ΛR τ (ψ m)) atTop
        (𝓝 (ang qOutCart)) := by
      have := (tendsto_const_nhds (x := ζ ^ kk)).smul hψl
      rwa [hξv, smul_smul, hkk, one_smul] at this
    obtain ⟨hlim, hev⟩ := l6h_tendsto_chart_out h hψ.tendsto_atTop hy
    have hev2 := hlim.eventually hW₀'n
    have heq : ∀ᶠ m in atTop,
        p (ψ m) = lieChartInv (iso_adRinvPow kk (phaseAt X Λ₁ ΛR (τ (ψ m)))) := by
      filter_upwards [hev, hev2] with m hm hW
      obtain ⟨hr0, -, hrep⟩ := hm
      rcases hp (ψ m) with ⟨k', hpW', hp0', hk'⟩ | ⟨hno, -⟩
      · exact huniq (ψ m) k' kk _ _ hpW' hp0' hW hr0 hk' hrep.symm
      · exact absurd ⟨kk, _, hW, hr0, hrep.symm⟩ hno
    exact MapClusterPt.of_comp hψ.tendsto_atTop
      (hlim.congr' (heq.mono fun m hm ↦ hm.symm)).mapClusterPt
  -- **the hyperbolic box** at `(0, x̃_out)` (the derivative facts only)
  obtain ⟨hF, hF1, -, hFD, hF2⟩ := hasStrictFDerivAt_extension he
  obtain ⟨D, hD, hDμ⟩ := hasFDerivAt_fullerChartMap
  have hinv : ∀ᶠ x in 𝓝 xTildeOut, (e ((0 : ℝ), x)).1 = 0 := by
    have hc : ContinuousAt (fun x : Fin 3 → ℝ ↦ ((0 : ℝ), x)) xTildeOut := by fun_prop
    filter_upwards [hc.preimage_mem_nhds (e.open_source.mem_nhds hsrc)] with x hx
    rw [he.2.2.2.2.2 _ hx rfl]
  have hexp : 1 < (fderiv ℝ e chartPtOut ((1 : ℝ), (0 : Fin 3 → ℝ))).1 := by
    rw [hF1]; linarith [rScale_bounds.1]
  have hblock : (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ) ∘L fderiv ℝ e chartPtOut ∘L
      ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ)) = D := by
    rw [← hD.fderiv]
    ext v : 1
    exact hF2 v
  exact Function.not_mapClusterPt_of_transverse_expansion (x₀ := xTildeOut) hF hfix hinv hexp
    (fun μ hμ ↦ by rw [hblock] at hμ; linarith [hDμ μ hμ]) W₁ hW₁n p hr0 hfollow hcl

/-! ### Helpers for the assembly -/

/-- **The cluster set is closed** (it is the image of the compact set of cluster points, which lie
in the section, `mapClusterPt_switchAng_mem_sectionZero`, under the continuous class map). -/
private lemma l6h_isClosed_switchClusterSet {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) :
    IsClosed (switchClusterSet (switchAng X Λ₁ ΛR τ)) := by
  have : T2Space XiWQuot := compact_t2_isClosed_XiWQuot.2.1
  set C := {ξ | MapClusterPt ξ atTop (switchAng X Λ₁ ΛR τ)} with hC
  have hCsub : C ⊆ Xi := fun ξ hξ ↦
    (isClosed_eq continuous_weightedNorm continuous_const).mem_of_mapClusterPt hξ
      (Eventually.of_forall h.switchPoints.2.2.2.2)
  have hCc : IsCompact C := isCompact_Xi.of_isClosed_subset isClosed_setOfPred_clusterPt hCsub
  have hCs : C ⊆ sectionZero := fun ξ hξ ↦ mapClusterPt_switchAng_mem_sectionZero h hξ
  have heq : switchClusterSet (switchAng X Λ₁ ΛR τ) = classOf '' C := by
    ext x
    constructor
    · rintro ⟨ξ, -, rfl, hξ⟩; exact ⟨ξ, hξ, rfl⟩
    · rintro ⟨ξ, hξ, rfl⟩; exact ⟨ξ, hCs hξ, rfl, hξ⟩
  rw [heq]
  exact (hCc.image_of_continuousOn (continuousOn_classOf.mono hCs)).isClosed

/-- The mirrored chart is injective on `H*`. -/
private lemma l6h_lieChartIn_inj {p₁ p₂ : ℝ × (Fin 3 → ℝ)} (h₁ : p₁ ∈ lieChartDomain)
    (h₂ : p₂ ∈ lieChartDomain) (h : lieChartIn p₁ = lieChartIn p₂) : p₁ = p₂ := by
  have : lieChart p₁ = lieChart p₂ := by
    rw [← reinTau_spec.1 (lieChart p₁), ← reinTau_spec.1 (lieChart p₂)]
    exact congrArg reinTau h
  rw [← (lieChart_spec h₁).2.2.2.2.2, this, (lieChart_spec h₂).2.2.2.2.2]

/-- **Theorem 16.4.1, first part** (`thm:no-chatter`: the cluster point is `q_in`), conditional on
`ClusterSetForwardInvariant` and the three named numerical facts of Theorem 16.1.1: `Ω` is closed
and forward invariant; a class `ω ≠ q_in` of `Ω` has `F^k ω → q_out` (Theorem 16.1.1), so
`q_out ∈ Ω`, against the hyperbolic box (`qOut0_not_mem_switchClusterSet`); hence every cluster
point is `q_in` and the angular components converge to `q_in` modulo `V_T`. (This part does not
use Remark 14.3.4; it is the part the assembly of Theorem 16.3.1 uses.) -/
theorem tendstoModVT_switchAng_of_clusterSetForwardInvariant (h₁ : DOutContracts)
    (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims) (hN5 : ClusterSetForwardInvariant) {a b : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}
    (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) :
    TendstoModVT (switchAng X Λ₁ ΛR τ) (ang (tau qOutCart)) := by
  set ξs := switchAng X Λ₁ ΛR τ with hξs
  refine tendstoModVT_of_forall_mapClusterPt h.switchPoints.2.2.2.2 fun ξ hξ ↦ ?_
  have hsec := mapClusterPt_switchAng_mem_sectionZero h hξ
  refine ⟨hsec, ?_⟩
  by_contra hne
  have hΩ : classOf ξ ∈ switchClusterSet ξs := ⟨ξ, hsec, rfl, hξ⟩
  have hit : ∀ k, poincareAngZero^[k] (classOf ξ) ∈ switchClusterSet ξs :=
    fun k ↦ (hN5 a b u g X Λ₁ ΛR τ h).iterate k hΩ
  exact qOut0_not_mem_switchClusterSet h ((l6h_isClosed_switchClusterSet h).mem_of_tendsto
    (theorem16_1_1 h₁ h₂ h₃ _ hne) (Eventually.of_forall hit))

/-- **Theorem 16.4.1, conditional on the forward invariance of the cluster set**
(`ClusterSetForwardInvariant`) and on the three named numerical facts of Theorem 16.1.1. See
`theorem16_4_1`. -/
theorem theorem16_4_1_of_clusterSetForwardInvariant (h₁ : DOutContracts)
    (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims) (hN5 : ClusterSetForwardInvariant)
    {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}
    (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) :
    TendstoModVT (switchAng X Λ₁ ΛR τ) (ang (tau qOutCart)) ∧
      ∀ e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)),
        IsReinhardtPoincareExtension e → ∀ U ∈ 𝓝 chartPtOut, ∀ᶠ n in atTop,
          ∃ k : ℕ, ∃ p ∈ Function.localUnstableSet e chartPtOut U, 0 < p.1 ∧
            iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = lieChartIn p := by
  set ξs := switchAng X Λ₁ ΛR τ with hξs
  set ξin := ang (tau qOutCart) with hξin
  have hmod : TendstoModVT ξs ξin := tendstoModVT_switchAng_of_clusterSetForwardInvariant h₁ h₂ h₃
      hN5 h
  refine ⟨hmod, fun e he U hU ↦ ?_⟩
  -- **(2) the stable curve**: rotations `ζ^{k_n}` bringing `ξ_n` to `ang q_in`
  have hO : ξin ∈ vtOrbit ξin := ⟨1, one_mem_VT, (one_smul _ _).symm⟩
  have hk : ∀ n, ∃ k : ℕ, dist (ζ ^ k • ξs n) ξin <
      Metric.infDist (ξs n) (vtOrbit ξin) + 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, ⟨v, hv, rfl⟩, hy⟩ := (Metric.infDist_lt_iff ⟨_, hO⟩).1
      (lt_add_of_pos_right (Metric.infDist (ξs n) (vtOrbit ξin)) (by positivity :
        (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    obtain ⟨kk, hkk⟩ : ∃ kk : ℕ, ζ ^ kk * v = 1 := by
      rcases hv with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨2, by rw [← pow_succ, ζ_pow_three]⟩
      · exact ⟨1, by rw [pow_one, ← pow_succ', ζ_pow_three]⟩
    refine ⟨kk, ?_⟩
    have hn : ‖ζ ^ kk‖ = 1 := by rw [norm_pow, norm_ζ, one_pow]
    calc dist (ζ ^ kk • ξs n) ξin = dist (ζ ^ kk • ξs n) (ζ ^ kk • (v • ξin)) := by
          rw [smul_smul, hkk, one_smul]
      _ = dist (ξs n) (v • ξin) := by rw [dist_smul₀, hn, one_mul]
      _ < _ := hy
  choose k hk using hk
  have hy : Tendsto (fun n ↦ ζ ^ k n • ξs n) atTop (𝓝 ξin) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n ↦ dist_nonneg)
      (fun n ↦ (hk n).le) ?_)
    simpa using hmod.add tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨hlim, hev⟩ := l6h_tendsto_chart_in h (φ := id) tendsto_id hy
  set p : ℕ → ℝ × (Fin 3 → ℝ) := fun n ↦
    lieChartInInv (iso_adRinvPow (k n) (phaseAt X Λ₁ ΛR (τ n))) with hpdef
  -- the neighbourhoods: `eventually_follows_in`, the switching structure, Remark 14.3.4
  obtain ⟨Wi, hWi, hfol⟩ := h.eventually_follows_in he
  obtain ⟨Ws, hWs, hWsub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.1 eventually_switchStructure
  obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (remark14_3_4 he).2.1
  have hsrc := he.1
  have hfix := he.2.1
  have htgt : chartPtOut ∈ e.target := hfix ▸ e.map_source hsrc
  have hsymm : e.symm chartPtOut = chartPtOut := by
    rw [← hfix, e.left_inv hsrc, hfix]
  have hpre : e.symm ⁻¹' Ws ∈ 𝓝 chartPtOut :=
    (e.continuousAt_symm htgt).preimage_mem_nhds (by rw [hsymm]; exact hWs)
  have hgood : ∀ p ∈ Ws, 0 < p.1 → p ∈ lieChartDomain ∧
      phaseHam (lieChartIn p) (vertex 0) < 0 ∧ phaseHam (lieChartIn p) (vertex 1) = 0 ∧
        phaseHam (lieChartIn p) (vertex 2) = 0 := by
    intro p hp hp0
    obtain ⟨hdom, hst⟩ := hWsub ⟨hp, hp0⟩
    obtain ⟨a1, a2, a3, -⟩ := hst (lieChartIn p) (Or.inr rfl)
    exact ⟨hdom, a1, a2, a3⟩
  have hall : ∀ᶠ n in atTop, (p n ∈ Wi ∧ p n ∈ Ws ∧ p n ∈ V ∧ p n ∈ e.symm ⁻¹' Ws ∧ p n ∈ U) ∧
      0 < (p n).1 ∧ lieChartIn (p n) = iso_adRinvPow (k n) (phaseAt X Λ₁ ΛR (τ n)) := by
    filter_upwards [hlim.eventually (inter_mem hWi (inter_mem hWs (inter_mem hV
      (inter_mem hpre hU)))), hev] with n h1 h2
    exact ⟨⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2⟩, h2.1, h2.2.2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hall
  -- the switching points from `N` on form a backward orbit of `e`
  have hback : ∀ n ≥ N, e (p (n + 1)) = p n := by
    intro n hn
    obtain ⟨⟨hWin, hWsn, hVn, hpren, -⟩, hp0, hrep⟩ := hN n hn
    obtain ⟨⟨hWin', hWsn', -, -, -⟩, hp0', hrep'⟩ := hN (n + 1) (by omega)
    obtain ⟨hr1, he1, hnext⟩ := hfol n (k n) (p n) hWin hp0 hrep.symm
    obtain ⟨-, -, -, -, -, hsrc1, he1'⟩ := hVsub ⟨hVn, hp0⟩
    have hrcm : reinChartMapIn (p n) = e.symm (p n) :=
      calc reinChartMapIn (p n) = e.symm (e (reinChartMapIn (p n))) := (e.left_inv hsrc1).symm
        _ = e.symm (p n) := by rw [he1']
    have hWr : reinChartMapIn (p n) ∈ Ws := by rw [hrcm]; exact hpren
    obtain ⟨d1, a1, -, -⟩ := hgood _ hWsn' hp0'
    obtain ⟨d2, -, b2, b3⟩ := hgood _ hWr hr1
    have := l6h_rep_unique hrep'.symm hnext a1 ⟨b2, b3⟩
    rw [l6h_lieChartIn_inj d1 d2 this]
    exact he1
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨⟨-, -, -, -, hUn⟩, hp0, hrep⟩ := hN n hn
  refine ⟨k n, p n, ⟨fun i ↦ p (n + i), by simp, fun i ↦ ⟨(hN (n + i) (by omega)).1.2.2.2.2,
    by dsimp only; rw [← add_assoc]; exact hback (n + i) (by omega)⟩,
    ?_⟩, hp0, hrep.symm⟩
  exact hlim.comp (tendsto_atTop_atTop_of_monotone (fun i j hij ↦ by omega) fun i ↦
    ⟨i, by omega⟩)

/-- **Theorem 16.4.1** (`thm:no-chatter`, the cluster point theorem; TeX 12840–12846), with the
three named numerical facts of Theorem 16.1.1 as hypotheses. Let `(u, g, X, Λ₁, Λ_R)` be a
Pontryagin extremal Reinhardt trajectory on `[a, b]` (normalized by `λ_cost = -1`, which
Lemma 8.2.2 allows at the singular locus) whose sequence of switching points `τ n ↑ b` has a
cluster point on the exceptional divisor reached in finite time (the lift meets the singular locus
at `b`), the switching points themselves not being on the divisor (`IsChatteringArcInto`). Then:
* the cluster point is `q_in`: the angular components `ξ_n` of the switching points converge to
  `q_in` (represented by `ang(τ q_out)`) modulo `V_T`, so `q_in` is the only cluster point;
* the switching points lie on the stable curve `W^s(q_in)`: eventually each, rotated onto the
  section `χ₂₃ = 0`, is `lieChartIn p` with `p` on the local unstable manifold of the extended map
  `e` at `q_out`, which is the local stable manifold of the Reinhardt–Poincaré map `e⁻¹` at `q_in`
  in the mirrored chart (Remark 14.3.4), a `C^∞` curve (Theorem 14.3.3).

"A Pontryagin extremal Reinhardt trajectory" is read, through `IsChatteringArcInto`, as an
extremal that is finitely bang-bang on every compact subinterval of `(a, b)`: the same reading
of "a trajectory of the Reinhardt system" as in `Theorem14_4_1` (see
`SmoothedPolygons/Ch14/NoReturn.lean`). It is what the assembly of Theorem 16.3.1 supplies
(Theorem 8.3.2 away from the singular locus).

Proof: `theorem16_4_1_of_clusterSetForwardInvariant` with `clusterSetForwardInvariant`;
the steps are in the module docstring. -/
theorem theorem16_4_1 (h₁ : DOutContracts) (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims)
    {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}
    (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) :
    TendstoModVT (switchAng X Λ₁ ΛR τ) (ang (tau qOutCart)) ∧
      ∀ e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)),
        IsReinhardtPoincareExtension e → ∀ U ∈ 𝓝 chartPtOut, ∀ᶠ n in atTop,
          ∃ k : ℕ, ∃ p ∈ Function.localUnstableSet e chartPtOut U, 0 < p.1 ∧
            iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = lieChartIn p :=
  theorem16_4_1_of_clusterSetForwardInvariant h₁ h₂ h₃ clusterSetForwardInvariant h

/-- **Theorem 16.4.1, time reversed** (`thm:no-chatter`; the form used by the proof of Theorem
14.4.1, "All switches must be on the unstable curve", TeX 12004–12005; E88): for a chattering arc
out of the singular locus (switching times `τ n ↓ a`), the angular components of the switching
points converge to `q_out` modulo `V_T`, and eventually each switching point, rotated onto the
section `χ₂₃ = 0`, is `lieChart p` with `p` on the local unstable manifold of `e` (the unstable
curve `W^u(q_out)`).

Proof: `IsChatteringArcOutOf.reverse` and `theorem16_4_1`, with `fullerCoords_reinTau`
(`τ` maps `q_in` to `q_out`) and `lieChartIn = τ ∘ lieChart`. -/
theorem theorem16_4_1_reverse (h₁ : DOutContracts) (h₂ : CellTwoEntersDOut)
    (h₃ : BoxSubclaims) {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}
    (h : IsChatteringArcOutOf a b u g X Λ₁ ΛR τ) :
    TendstoModVT (switchAng X Λ₁ ΛR τ) (ang qOutCart) ∧
      ∀ e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)),
        IsReinhardtPoincareExtension e → ∀ U ∈ 𝓝 chartPtOut, ∀ᶠ n in atTop,
          ∃ k : ℕ, ∃ p ∈ Function.localUnstableSet e chartPtOut U, 0 < p.1 ∧
            iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = lieChart p := by
  obtain ⟨h1, h2⟩ := theorem16_4_1 h₁ h₂ h₃ h.reverse
  -- the reversed switching points are `τ` of the switching points
  have hpt : ∀ n, phaseAt (fun t ↦ matTau (X (a + b - t))) (fun t ↦ matTau (Λ₁ (a + b - t)))
      (fun t ↦ matTau (ΛR (a + b - t))) (a + b - τ n) = reinTau (phaseAt X Λ₁ ΛR (τ n)) := by
    intro n
    simp only [phaseAt, reinTau, show a + b - (a + b - τ n) = τ n by ring]
  have hang : ∀ n, switchAng (fun t ↦ matTau (X (a + b - t))) (fun t ↦ matTau (Λ₁ (a + b - t)))
      (fun t ↦ matTau (ΛR (a + b - t))) (fun n ↦ a + b - τ n) n =
        tau (switchAng X Λ₁ ΛR τ n) := by
    intro n
    simp only [switchAng]
    rw [hpt, fullerCoords_reinTau, tau_ang]
  -- `τ` is an isometry mapping the orbit of `ang q_out` to that of `ang q_in`
  have hc : ∀ (z w : Fin 3 → ℂ) (i : Fin 3), dist (tau z i) (tau w i) = dist (z i) (w i) := by
    intro z w i
    fin_cases i <;> simp [tau, dist_neg_neg, Complex.dist_conj_conj]
  have hle : ∀ z w : Fin 3 → ℂ, dist (tau z) (tau w) ≤ dist z w := fun z w ↦
    (dist_pi_le_iff dist_nonneg).2 fun i ↦ (hc z w i).le.trans (dist_le_pi_dist z w i)
  have hiso : Isometry tau := Isometry.of_dist_eq fun z w ↦ le_antisymm (hle z w) (by
    have := hle (tau z) (tau w); rwa [tau_tau, tau_tau] at this)
  have horb : vtOrbit (ang (tau qOutCart)) = tau '' vtOrbit (ang qOutCart) := by
    have hτv : ∀ (v : ℂ) (w : Fin 3 → ℂ), tau (v • w) = starRingEnd ℂ v • tau w := by
      intro v w
      ext i; fin_cases i <;> simp [tau]
    ext η
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨starRingEnd ℂ v • ang qOutCart, ⟨starRingEnd ℂ v, ?_, rfl⟩, ?_⟩
      · rcases hv with rfl | rfl | rfl
        · simp [VT]
        · rw [conj_ζ]; exact ζ_sq_mem_VT
        · rw [conj_ζ_sq]; exact ζ_mem_VT
      · rw [hτv, Complex.conj_conj, tau_ang]
    · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨starRingEnd ℂ v, ?_, by rw [hτv, tau_ang]⟩
      rcases hv with rfl | rfl | rfl
      · simp [VT]
      · rw [conj_ζ]; exact ζ_sq_mem_VT
      · rw [conj_ζ_sq]; exact ζ_mem_VT
  refine ⟨?_, fun e he U hU ↦ ?_⟩
  · have := h1
    unfold TendstoModVT at this ⊢
    simp only [hang, horb, Metric.infDist_image hiso] at this
    exact this
  · filter_upwards [h2 e he U hU] with n ⟨k, p, hp, hp0, hk⟩
    -- `Ad_{R⁻ᵏ} ∘ τ = τ ∘ Ad_{R^{-2k}}`
    have hrot : ∀ (j : ℕ) (q : iso_PhasePt),
        iso_adRinvPow j (reinTau q) = reinTau (iso_adRinvPow (2 * j) q) := by
      have hadR : ∀ q, iso_adR q = iso_adRinvPow 2 q := by
        intro q
        have := congrArg (iso_adRinvPow 2) (irt_adRinvPow_one_adR q)
        rwa [irt_adRinvPow_add, show 2 + 1 = 3 * 1 by norm_num, irt_adRinvPow_three_mul] at this
      intro j
      induction j with
      | zero => intro q; simp [irt_adRinvPow_zero]
      | succ j ih =>
        intro q
        rw [show j + 1 = 1 + j by ring, ← irt_adRinvPow_add, ih, ← reinTau_spec.2.2.2, hadR,
          irt_adRinvPow_add]
        congr 2
        ring
    refine ⟨2 * k, p, hp, hp0, ?_⟩
    rw [hpt, hrot] at hk
    rw [← reinTau_spec.1 (iso_adRinvPow (2 * k) (phaseAt X Λ₁ ΛR (τ n))), hk]
    exact reinTau_spec.1 _

end SmoothedPolygons
