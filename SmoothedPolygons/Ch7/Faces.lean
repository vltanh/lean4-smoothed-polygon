module

public import SmoothedPolygons.Ch3.ControlSets
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Topology.Defs.Basic

/-!
# The partition of the cotangent space by faces of the control set (§7.3)
-/

@[expose] public section

namespace SmoothedPolygons

/-- The trace form `u ↦ ⟨A, Z_u⟩` is linear in the control. -/
private theorem traceForm_controlMatrix_add (A : Mat2) (u v : Fin 3 → ℝ) (s t : ℝ) :
    traceForm A (controlMatrix (s • u + t • v)) =
      s * traceForm A (controlMatrix u) + t * traceForm A (controlMatrix v) := by
  simp only [traceForm, controlMatrix, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The trace form `u ↦ ⟨A, Z_u⟩` is continuous in the control. -/
private theorem continuous_traceForm_controlMatrix (A : Mat2) :
    Continuous fun u ↦ traceForm A (controlMatrix u) := by
  simp only [traceForm, controlMatrix, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  fun_prop

/-- The difference of the values of a ratio `(at + b)/(ct + d)` of affine functions at two
parameters `s, t`: its sign is the sign of `(ad - bc)(t - s)` when the denominators have the same
sign, so the ratio is monotonic, strictly unless `ad - bc = 0`. (The book reads this off the
derivative `(ad - bc)/(ct + d)²`; the difference quotient gives the same conclusion without the mean
value theorem.) -/
private theorem ratio_sub (α β γ δ s t : ℝ) (hs : γ * s + δ ≠ 0) (ht : γ * t + δ ≠ 0) :
    (α * t + β) / (γ * t + δ) - (α * s + β) / (γ * s + δ) =
      (α * δ - β * γ) * (t - s) / ((γ * t + δ) * (γ * s + δ)) := by
  rw [div_sub_div _ _ ht hs, div_eq_div_iff (mul_ne_zero ht hs) (mul_ne_zero ht hs)]
  ring

/-- **Lemma 7.3.1** (`lem:control-face-lemma`). Let the control set `U` be a compact convex set in
the affine plane `u₀ + u₁ + u₂ = 1`. At each point `(g, X, Λ₁, Λ_R)` of the cotangent space (with
`⟨X, Z_u⟩ ≠ 0` on `U`, as on the state space), the set of controls `u ∈ U` maximizing the
Hamiltonian `H(Λ₁, Λ_R, X; Z_u)` is a face of `U`: a nonempty convex subset `F` such that
`tx + (1-t)y ∈ F` with `x, y ∈ U`, `t ∈ (0, 1)` implies `x, y ∈ F`. -/
theorem lemma7_3_1 (U : Set (Fin 3 → ℝ)) (hU : IsCompact U) (hconv : Convex ℝ U)
    (hne : U.Nonempty) (lam : ℝ) (Λ₁ ΛR X : Mat2)
    (hden : ∀ u ∈ U, traceForm X (controlMatrix u) ≠ 0) :
    {u ∈ U | ∀ v ∈ U, hamiltonian lam Λ₁ ΛR X v ≤ hamiltonian lam Λ₁ ΛR X u}.Nonempty ∧
      Convex ℝ {u ∈ U | ∀ v ∈ U, hamiltonian lam Λ₁ ΛR X v ≤ hamiltonian lam Λ₁ ΛR X u} ∧
      IsExtreme ℝ U {u ∈ U | ∀ v ∈ U, hamiltonian lam Λ₁ ΛR X v ≤ hamiltonian lam Λ₁ ΛR X u} := by
  set H := hamiltonian lam Λ₁ ΛR X with hHdef
  set N : (Fin 3 → ℝ) → ℝ := fun u ↦ traceForm ΛR (controlMatrix u) with hN
  set D : (Fin 3 → ℝ) → ℝ := fun u ↦ traceForm X (controlMatrix u) with hD
  set K := traceForm (Λ₁ - (3 / 2 * lam) • J) X
  have hH : ∀ u, H u = K - N u / D u := fun u ↦ rfl
  -- the denominator `⟨X, Z_u⟩` is affine in `u` and nonzero on the convex set `U`, so it has a
  -- constant sign on `U`
  have hsign : ∀ u ∈ U, ∀ v ∈ U, 0 < D u * D v := by
    intro u hu v hv
    have hu0 : D u ≠ 0 := hden u hu
    have hv0 : D v ≠ 0 := hden v hv
    by_contra hneg
    have hlt : D u * D v < 0 := lt_of_le_of_ne (not_lt.1 hneg) (mul_ne_zero hu0 hv0)
    have hne' : D u - D v ≠ 0 := fun h ↦ by
      rw [sub_eq_zero.1 h] at hlt; nlinarith
    have hθ : 0 ≤ D u / (D u - D v) ∧ D u / (D u - D v) ≤ 1 := by
      rcases lt_or_gt_of_ne hu0 with h | h
      · have hv : 0 < D v := by nlinarith
        refine ⟨div_nonneg_of_nonpos h.le (by linarith), (div_le_one_of_neg (by linarith)).2
          (by linarith)⟩
      · have hv : D v < 0 := by nlinarith
        exact ⟨div_nonneg h.le (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩
    have hw := hconv hu hv (sub_nonneg.2 hθ.2) hθ.1 (by ring)
    apply hden _ hw
    rw [traceForm_controlMatrix_add]
    change (1 - D u / (D u - D v)) * D u + D u / (D u - D v) * D v = 0
    field_simp
    ring
  -- along a segment `t x₁ + (1 - t) x₂` of `U`, the control-dependent part of the Hamiltonian is a
  -- ratio `(at + b)/(ct + d)` with nonzero denominator; it is monotonic
  have hmono : ∀ x₁ ∈ U, ∀ x₂ ∈ U, ∃ k : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∃ q : ℝ, 0 < q ∧
        H (t • x₁ + (1 - t) • x₂) - H (s • x₁ + (1 - s) • x₂) = k * (t - s) * q := by
    intro x₁ h₁ x₂ h₂
    have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x₁ + (1 - t) • x₂ ∈ U := fun t ht ↦
      hconv h₁ h₂ ht.1 (sub_nonneg.2 ht.2) (by ring)
    have hDt : ∀ t : ℝ, D (t • x₁ + (1 - t) • x₂) = (D x₁ - D x₂) * t + D x₂ := fun t ↦ by
      simp only [hD]; rw [traceForm_controlMatrix_add]; ring
    have hNt : ∀ t : ℝ, -N (t • x₁ + (1 - t) • x₂) = (N x₂ - N x₁) * t + -N x₂ := fun t ↦ by
      simp only [hN]; rw [traceForm_controlMatrix_add]; ring
    refine ⟨(N x₂ - N x₁) * D x₂ - -N x₂ * (D x₁ - D x₂), fun s hs t ht ↦ ?_⟩
    have hps := hsign _ (hseg t ht) _ (hseg s hs)
    rw [hDt, hDt] at hps
    refine ⟨(((D x₁ - D x₂) * t + D x₂) * ((D x₁ - D x₂) * s + D x₂))⁻¹, inv_pos.2 hps, ?_⟩
    have e : H (t • x₁ + (1 - t) • x₂) - H (s • x₁ + (1 - s) • x₂) =
        -N (t • x₁ + (1 - t) • x₂) / D (t • x₁ + (1 - t) • x₂) -
          -N (s • x₁ + (1 - s) • x₂) / D (s • x₁ + (1 - s) • x₂) := by
      rw [hH, hH]; ring
    rw [e, hNt, hNt, hDt, hDt, ratio_sub _ _ _ _ _ _ (right_ne_zero_of_mul hps.ne')
      (left_ne_zero_of_mul hps.ne'), div_eq_mul_inv]
  -- the endpoints of a segment are `x₁` (`t = 1`) and `x₂` (`t = 0`)
  have hw1 : ∀ x₁ x₂ : Fin 3 → ℝ, (1 : ℝ) • x₁ + (1 - 1 : ℝ) • x₂ = x₁ := fun _ _ ↦ by simp
  have hw0 : ∀ x₁ x₂ : Fin 3 → ℝ, (0 : ℝ) • x₁ + (1 - 0 : ℝ) • x₂ = x₂ := fun _ _ ↦ by simp
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.2 zero_le_one
  have h11 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.2 zero_le_one
  refine ⟨?_, ?_, ⟨fun u hu ↦ hu.1, ?_⟩⟩
  · -- nonempty: `U` is compact and `H` is continuous on `U`
    have hc : ContinuousOn H U := by
      exact continuousOn_const.sub ((continuous_traceForm_controlMatrix ΛR).continuousOn.div
        (continuous_traceForm_controlMatrix X).continuousOn hden)
    obtain ⟨u, hu, hmax⟩ := hU.exists_isMaxOn hne hc
    exact ⟨u, hu, fun v hv ↦ hmax hv⟩
  · -- convex: `H` is monotonic along a segment between two maximizers, hence constant
    intro u hu v hv a b ha hb hab
    refine ⟨hconv hu.1 hv.1 ha hb hab, fun w hw ↦ (hu.2 w hw).trans (le_of_eq ?_)⟩
    obtain ⟨k, hk⟩ := hmono u hu.1 v hv.1
    obtain ⟨q, hq, h⟩ := hk 0 h01 1 h11
    rw [hw1, hw0, le_antisymm (hu.2 v hv.1) (hv.2 u hu.1), sub_self, sub_zero, mul_one] at h
    have hk0 : k = 0 := by
      rcases mul_eq_zero.1 h.symm with h | h
      · exact h
      · exact absurd h hq.ne'
    have ha' : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha, by linarith⟩
    obtain ⟨q', -, h'⟩ := hk 0 h01 a ha'
    rw [hk0, zero_mul, zero_mul, hw0, sub_eq_zero, show 1 - a = b by linarith] at h'
    rw [h', le_antisymm (hu.2 v hv.1) (hv.2 u hu.1)]
  · -- extreme: if an internal point of a segment is a maximizer, so are the endpoints
    intro x₁ h₁ x₂ h₂ z hz hzseg
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hzseg
    refine ⟨h₁, fun w hw ↦ (hz.2 w hw).trans (le_of_eq ?_)⟩
    obtain ⟨k, hk⟩ := hmono x₁ h₁ x₂ h₂
    have ha' : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha.le, by linarith⟩
    have hb' : 1 - a = b := by linarith
    obtain ⟨q₁, hq₁, e₁⟩ := hk a ha' 1 h11
    obtain ⟨q₀, hq₀, e₀⟩ := hk a ha' 0 h01
    rw [hw1, hb'] at e₁
    rw [hw0, hb'] at e₀
    have i₁ := hz.2 x₁ h₁
    have i₀ := hz.2 x₂ h₂
    have hk1 : k * ((1 - a) * q₁) ≤ 0 := by nlinarith
    have hk0 : k * (a * q₀) ≥ 0 := by nlinarith
    have hpos1 : 0 < (1 - a) * q₁ := mul_pos (by linarith) hq₁
    have hpos0 : 0 < a * q₀ := mul_pos ha hq₀
    have hk : k = 0 := le_antisymm (nonpos_of_mul_nonpos_left hk1 hpos1)
      (nonneg_of_mul_nonneg_left hk0 hpos0)
    rw [hk] at e₁
    linarith

end SmoothedPolygons
