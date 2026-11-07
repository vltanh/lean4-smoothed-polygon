module

public import SmoothedPolygons.Ch7.Isolated.IpcOctagon

/-!
# Theorem 7.7.1, step 4 (helper): the algebra of the direct calculation

With `ℓ` an independent variable, the basis vectors `iso_sectionBasis` decompose along the vector
field `ipc_Vq`, the tangent `ipc_Fam` of the family of fixed points and the costate directions
`ipc_w0`, …, `ipc_w3` (`ipc_basis_decomp`); and the image of each basis vector, computed from the
pieces of `SmoothedPolygons.Ch7.Isolated.IpcOctagon`, is the corresponding column of
`iso_sectionMatrix` (`ipc_column`). Both are identities of rational functions in `(y₀, ℓ, √3)`.
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- Substitute back `D = 3ℓy² + ℓ + 3y² - 3` (after `field_simp`), then normalize. -/
macro "ipc_ringD" hD:ident : tactic =>
  `(tactic| (
    subst $hD:ident
    ipc_ring))

lemma ipc_basis_decomp0 (y L : ℝ) (hy : 0 < y) :
    iso_sectionBasis y L 0 = ipc_Vq y L + (-(√3 * y ^ 2)) • ipc_Fam y L + ipc_w0 y L := by
  have h3 : (0 : ℝ) < √3 := by positivity
  funext k
  fin_cases k <;> simp [iso_sectionBasis, ipc_Vq, ipc_Fam, ipc_w0] <;> field_simp <;> ipc_ring

lemma ipc_basis_decomp1 (y L : ℝ) (hy : 0 < y) :
    iso_sectionBasis y L 1 = (-(√3 / 3)) • ipc_Fam y L + ipc_w1 y L := by
  have h3 : (0 : ℝ) < √3 := by positivity
  funext k
  fin_cases k <;> simp [iso_sectionBasis, ipc_Fam, ipc_w1] <;> field_simp <;> ipc_ring

lemma ipc_basis_decomp2 (y L : ℝ) : iso_sectionBasis y L 2 = ipc_w2 y L := by
  funext k
  fin_cases k <;> simp [iso_sectionBasis, ipc_w2]

lemma ipc_basis_decomp3 (y L : ℝ) : iso_sectionBasis y L 3 = ipc_w3 y L := by
  funext k
  fin_cases k <;> simp [iso_sectionBasis, ipc_w3]

/-- The slope `-iso_chi32Slope` of `χ₃₁` at `t_sw`, with `ℓ` free. -/
noncomputable def ipc_G01 (y L : ℝ) : ℝ :=
  2 * √3 * (3 * L * y ^ 2 + L + 3 * y ^ 2 - 3) / (3 * y ^ 2)

lemma ipc_G01_eq (y : ℝ) : ipc_G01 y (ellSw y) = -iso_chi32Slope y := by
  simp only [ipc_G01, iso_chi32Slope]
  ring

/-- The image of `w` (costate directions) under the derivative of the Poincaré map. -/
noncomputable def ipc_Dw (y L : ℝ) (w : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ipc_linVec y L (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) -
    (ipc_Glin y L (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) / ipc_G01 y L) • ipc_Ft y L

lemma ipc_column0_0 (y L : ℝ) (hy : 0 < y) (hD : 3 * L * y ^ 2 + L + 3 * y ^ 2 - 3 ≠ 0)
    (k : Fin 9) (hk : 0 ≤ k.val ∧ k.val < 3) :
    ((-(√3 * y ^ 2)) • ipc_Fam y L + ipc_Dw y L (ipc_w0 y L)) k =
      (∑ i, iso_sectionMatrix (y ^ 2) L i 0 • iso_sectionBasis y L i) k := by
  have h3 : (0 : ℝ) < √3 := by positivity
  obtain ⟨D, hDdef⟩ : ∃ D, D = 3 * L * y ^ 2 + L + 3 * y ^ 2 - 3 := ⟨_, rfl⟩
  have hD' : D ≠ 0 := hDdef ▸ hD
  simp only [ipc_Dw, ipc_G01, iso_sectionMatrix, Finset.sum_apply, Fin.sum_univ_four,
    Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [← hDdef]
  fin_cases k <;> simp at hk <;>
    simp [ipc_linVec, ipc_Glin, ipc_w0, ipc_Ft, ipc_Fam, iso_sectionBasis] <;>
    field_simp <;> ipc_ringD hDdef

lemma ipc_column0_3 (y L : ℝ) (hy : 0 < y) (hD : 3 * L * y ^ 2 + L + 3 * y ^ 2 - 3 ≠ 0)
    (k : Fin 9) (hk : 3 ≤ k.val ∧ k.val < 6) :
    ((-(√3 * y ^ 2)) • ipc_Fam y L + ipc_Dw y L (ipc_w0 y L)) k =
      (∑ i, iso_sectionMatrix (y ^ 2) L i 0 • iso_sectionBasis y L i) k := by
  have h3 : (0 : ℝ) < √3 := by positivity
  obtain ⟨D, hDdef⟩ : ∃ D, D = 3 * L * y ^ 2 + L + 3 * y ^ 2 - 3 := ⟨_, rfl⟩
  have hD' : D ≠ 0 := hDdef ▸ hD
  simp only [ipc_Dw, ipc_G01, iso_sectionMatrix, Finset.sum_apply, Fin.sum_univ_four,
    Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [← hDdef]
  fin_cases k <;> simp at hk <;>
    simp [ipc_linVec, ipc_Glin, ipc_w0, ipc_Ft, ipc_Fam, iso_sectionBasis] <;>
    field_simp <;> ipc_ringD hDdef

lemma ipc_column0_6 (y L : ℝ) (hy : 0 < y) (hD : 3 * L * y ^ 2 + L + 3 * y ^ 2 - 3 ≠ 0)
    (k : Fin 9) (hk : 6 ≤ k.val ∧ k.val < 9) :
    ((-(√3 * y ^ 2)) • ipc_Fam y L + ipc_Dw y L (ipc_w0 y L)) k =
      (∑ i, iso_sectionMatrix (y ^ 2) L i 0 • iso_sectionBasis y L i) k := by
  have h3 : (0 : ℝ) < √3 := by positivity
  obtain ⟨D, hDdef⟩ : ∃ D, D = 3 * L * y ^ 2 + L + 3 * y ^ 2 - 3 := ⟨_, rfl⟩
  have hD' : D ≠ 0 := hDdef ▸ hD
  simp only [ipc_Dw, ipc_G01, iso_sectionMatrix, Finset.sum_apply, Fin.sum_univ_four,
    Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [← hDdef]
  fin_cases k <;> simp at hk <;>
    simp [ipc_linVec, ipc_Glin, ipc_w0, ipc_Ft, ipc_Fam, iso_sectionBasis] <;>
    field_simp <;> ipc_ringD hDdef

lemma ipc_column0 (y L : ℝ) (hy : 0 < y) (hD : 3 * L * y ^ 2 + L + 3 * y ^ 2 - 3 ≠ 0) :
    (-(√3 * y ^ 2)) • ipc_Fam y L + ipc_Dw y L (ipc_w0 y L) =
      ∑ i, iso_sectionMatrix (y ^ 2) L i 0 • iso_sectionBasis y L i := by
  funext k
  rcases lt_or_ge k.val 3 with h | h
  · exact ipc_column0_0 y L hy hD k ⟨Nat.zero_le _, h⟩
  rcases lt_or_ge k.val 6 with h' | h'
  · exact ipc_column0_3 y L hy hD k ⟨h, h'⟩
  · exact ipc_column0_6 y L hy hD k ⟨h', k.isLt⟩

lemma ipc_column1 (y L : ℝ) (hy : 0 < y) (hD : 3 * L * y ^ 2 + L + 3 * y ^ 2 - 3 ≠ 0) :
    (-(√3 / 3)) • ipc_Fam y L + ipc_Dw y L (ipc_w1 y L) =
      ∑ i, iso_sectionMatrix (y ^ 2) L i 1 • iso_sectionBasis y L i := by
  have h3 : (0 : ℝ) < √3 := by positivity
  obtain ⟨D, hDdef⟩ : ∃ D, D = 3 * L * y ^ 2 + L + 3 * y ^ 2 - 3 := ⟨_, rfl⟩
  have hD' : D ≠ 0 := hDdef ▸ hD
  funext k
  simp only [ipc_Dw, ipc_G01, iso_sectionMatrix, Finset.sum_apply, Fin.sum_univ_four,
    Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [← hDdef]
  fin_cases k <;>
    simp [ipc_linVec, ipc_Glin, ipc_w1, ipc_Ft, ipc_Fam, iso_sectionBasis] <;>
    field_simp <;> ipc_ringD hDdef

lemma ipc_column2 (y L : ℝ) (hy : 0 < y) (hD : 3 * L * y ^ 2 + L + 3 * y ^ 2 - 3 ≠ 0) :
    ipc_Dw y L (ipc_w2 y L) =
      ∑ i, iso_sectionMatrix (y ^ 2) L i 2 • iso_sectionBasis y L i := by
  have h3 : (0 : ℝ) < √3 := by positivity
  obtain ⟨D, hDdef⟩ : ∃ D, D = 3 * L * y ^ 2 + L + 3 * y ^ 2 - 3 := ⟨_, rfl⟩
  have hD' : D ≠ 0 := hDdef ▸ hD
  funext k
  simp only [ipc_Dw, ipc_G01, iso_sectionMatrix, Finset.sum_apply, Fin.sum_univ_four,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hDdef]
  fin_cases k <;>
    simp [ipc_linVec, ipc_Glin, ipc_w2, ipc_Ft, iso_sectionBasis] <;>
    field_simp <;> ipc_ringD hDdef

lemma ipc_column3 (y L : ℝ) (hy : 0 < y) (hD : 3 * L * y ^ 2 + L + 3 * y ^ 2 - 3 ≠ 0) :
    ipc_Dw y L (ipc_w3 y L) =
      ∑ i, iso_sectionMatrix (y ^ 2) L i 3 • iso_sectionBasis y L i := by
  have h3 : (0 : ℝ) < √3 := by positivity
  obtain ⟨D, hDdef⟩ : ∃ D, D = 3 * L * y ^ 2 + L + 3 * y ^ 2 - 3 := ⟨_, rfl⟩
  have hD' : D ≠ 0 := hDdef ▸ hD
  funext k
  simp only [ipc_Dw, ipc_G01, iso_sectionMatrix, Finset.sum_apply, Fin.sum_univ_four,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hDdef]
  fin_cases k <;>
    simp [ipc_linVec, ipc_Glin, ipc_w3, ipc_Ft, iso_sectionBasis] <;>
    field_simp <;> ipc_ringD hDdef

end SmoothedPolygons
