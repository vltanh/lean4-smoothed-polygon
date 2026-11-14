module

public import SmoothedPolygons.Ch16.Certificates.ContractionBoxData

/-!
# The contraction on `B`: the kernel check

The Bool-valued checks of `SmoothedPolygons/Ch16/Certificates/ContractionBoxData.lean` evaluate to
`true`, by `decide +kernel`: the kernel reduces the checks, with no compiled code and no extra
axiom (`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`). One declaration per
box of the `3 × 3 × 6` subdivision keeps the kernel's caches, and the memory, small. 
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.ContractionBox

theorem checkBox_0_0_0 : checkBox 0 0 0 (certs.getD (boxIndex 0 0 0) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_0_1 : checkBox 0 0 1 (certs.getD (boxIndex 0 0 1) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_0_2 : checkBox 0 0 2 (certs.getD (boxIndex 0 0 2) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_0_3 : checkBox 0 0 3 (certs.getD (boxIndex 0 0 3) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_0_4 : checkBox 0 0 4 (certs.getD (boxIndex 0 0 4) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_0_5 : checkBox 0 0 5 (certs.getD (boxIndex 0 0 5) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_1_0 : checkBox 0 1 0 (certs.getD (boxIndex 0 1 0) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_1_1 : checkBox 0 1 1 (certs.getD (boxIndex 0 1 1) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_1_2 : checkBox 0 1 2 (certs.getD (boxIndex 0 1 2) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_1_3 : checkBox 0 1 3 (certs.getD (boxIndex 0 1 3) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_1_4 : checkBox 0 1 4 (certs.getD (boxIndex 0 1 4) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_1_5 : checkBox 0 1 5 (certs.getD (boxIndex 0 1 5) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_2_0 : checkBox 0 2 0 (certs.getD (boxIndex 0 2 0) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_2_1 : checkBox 0 2 1 (certs.getD (boxIndex 0 2 1) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_2_2 : checkBox 0 2 2 (certs.getD (boxIndex 0 2 2) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_2_3 : checkBox 0 2 3 (certs.getD (boxIndex 0 2 3) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_2_4 : checkBox 0 2 4 (certs.getD (boxIndex 0 2 4) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_0_2_5 : checkBox 0 2 5 (certs.getD (boxIndex 0 2 5) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_0_0 : checkBox 1 0 0 (certs.getD (boxIndex 1 0 0) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_0_1 : checkBox 1 0 1 (certs.getD (boxIndex 1 0 1) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_0_2 : checkBox 1 0 2 (certs.getD (boxIndex 1 0 2) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_0_3 : checkBox 1 0 3 (certs.getD (boxIndex 1 0 3) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_0_4 : checkBox 1 0 4 (certs.getD (boxIndex 1 0 4) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_0_5 : checkBox 1 0 5 (certs.getD (boxIndex 1 0 5) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_1_0 : checkBox 1 1 0 (certs.getD (boxIndex 1 1 0) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_1_1 : checkBox 1 1 1 (certs.getD (boxIndex 1 1 1) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_1_2 : checkBox 1 1 2 (certs.getD (boxIndex 1 1 2) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_1_3 : checkBox 1 1 3 (certs.getD (boxIndex 1 1 3) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_1_4 : checkBox 1 1 4 (certs.getD (boxIndex 1 1 4) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_1_5 : checkBox 1 1 5 (certs.getD (boxIndex 1 1 5) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_2_0 : checkBox 1 2 0 (certs.getD (boxIndex 1 2 0) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_2_1 : checkBox 1 2 1 (certs.getD (boxIndex 1 2 1) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_2_2 : checkBox 1 2 2 (certs.getD (boxIndex 1 2 2) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_2_3 : checkBox 1 2 3 (certs.getD (boxIndex 1 2 3) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_2_4 : checkBox 1 2 4 (certs.getD (boxIndex 1 2 4) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_1_2_5 : checkBox 1 2 5 (certs.getD (boxIndex 1 2 5) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_0_0 : checkBox 2 0 0 (certs.getD (boxIndex 2 0 0) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_0_1 : checkBox 2 0 1 (certs.getD (boxIndex 2 0 1) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_0_2 : checkBox 2 0 2 (certs.getD (boxIndex 2 0 2) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_0_3 : checkBox 2 0 3 (certs.getD (boxIndex 2 0 3) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_0_4 : checkBox 2 0 4 (certs.getD (boxIndex 2 0 4) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_0_5 : checkBox 2 0 5 (certs.getD (boxIndex 2 0 5) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_1_0 : checkBox 2 1 0 (certs.getD (boxIndex 2 1 0) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_1_1 : checkBox 2 1 1 (certs.getD (boxIndex 2 1 1) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_1_2 : checkBox 2 1 2 (certs.getD (boxIndex 2 1 2) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_1_3 : checkBox 2 1 3 (certs.getD (boxIndex 2 1 3) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_1_4 : checkBox 2 1 4 (certs.getD (boxIndex 2 1 4) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_1_5 : checkBox 2 1 5 (certs.getD (boxIndex 2 1 5) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_2_0 : checkBox 2 2 0 (certs.getD (boxIndex 2 2 0) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_2_1 : checkBox 2 2 1 (certs.getD (boxIndex 2 2 1) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_2_2 : checkBox 2 2 2 (certs.getD (boxIndex 2 2 2) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_2_3 : checkBox 2 2 3 (certs.getD (boxIndex 2 2 3) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_2_4 : checkBox 2 2 4 (certs.getD (boxIndex 2 2 4) ⟨0, 0⟩) = true := by
  decide +kernel

theorem checkBox_2_2_5 : checkBox 2 2 5 (certs.getD (boxIndex 2 2 5) ⟨0, 0⟩) = true := by
  decide +kernel

/-- Every box passes its check. -/
theorem checkBox_all {m₀ m₁ m₂ : ℕ} (h₀ : m₀ < 3) (h₁ : m₁ < 3) (h₂ : m₂ < 6) :
    checkBox m₀ m₁ m₂ (certs.getD (boxIndex m₀ m₁ m₂) ⟨0, 0⟩) = true := by
  interval_cases m₀ <;> interval_cases m₁ <;> interval_cases m₂
  exacts [checkBox_0_0_0,
    checkBox_0_0_1,
    checkBox_0_0_2,
    checkBox_0_0_3,
    checkBox_0_0_4,
    checkBox_0_0_5,
    checkBox_0_1_0,
    checkBox_0_1_1,
    checkBox_0_1_2,
    checkBox_0_1_3,
    checkBox_0_1_4,
    checkBox_0_1_5,
    checkBox_0_2_0,
    checkBox_0_2_1,
    checkBox_0_2_2,
    checkBox_0_2_3,
    checkBox_0_2_4,
    checkBox_0_2_5,
    checkBox_1_0_0,
    checkBox_1_0_1,
    checkBox_1_0_2,
    checkBox_1_0_3,
    checkBox_1_0_4,
    checkBox_1_0_5,
    checkBox_1_1_0,
    checkBox_1_1_1,
    checkBox_1_1_2,
    checkBox_1_1_3,
    checkBox_1_1_4,
    checkBox_1_1_5,
    checkBox_1_2_0,
    checkBox_1_2_1,
    checkBox_1_2_2,
    checkBox_1_2_3,
    checkBox_1_2_4,
    checkBox_1_2_5,
    checkBox_2_0_0,
    checkBox_2_0_1,
    checkBox_2_0_2,
    checkBox_2_0_3,
    checkBox_2_0_4,
    checkBox_2_0_5,
    checkBox_2_1_0,
    checkBox_2_1_1,
    checkBox_2_1_2,
    checkBox_2_1_3,
    checkBox_2_1_4,
    checkBox_2_1_5,
    checkBox_2_2_0,
    checkBox_2_2_1,
    checkBox_2_2_2,
    checkBox_2_2_3,
    checkBox_2_2_4,
    checkBox_2_2_5]

theorem checkCenter_eq_true : checkCenter = true := by decide +kernel

theorem checkRows_eq_true : checkRows = true := by decide +kernel

end SmoothedPolygons.TriFuller.ContractionBox
