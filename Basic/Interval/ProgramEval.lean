module

public import Basic.Interval.Program

/-!
# Unfolding the real value of a straight-line program one instruction at a time

For a well-formed program (every instruction refers to earlier results only, `wf`), the real
result `i` is the value of the instruction `i` on the real results of the whole program
(`getR_evalR_eq`). This turns the value of a concrete program into closed formulas by rewriting one
index at a time, the lookup `lookup prog i = some op` being checked by `rfl`.
-/

@[expose] public section

namespace DyadicInterval

/-- The indices of the earlier results that an instruction reads. -/
def Op.args : Op → List ℕ
  | .var _ => []
  | .const _ => []
  | .pi => []
  | .add i j => [i, j]
  | .sub i j => [i, j]
  | .mul i j => [i, j]
  | .div i j => [i, j]
  | .neg i => [i]
  | .sq i => [i]
  | .sqrt i => [i]
  | .sin i => [i]
  | .cos i => [i]
  | .arctan i => [i]

/-- A program is well formed if every instruction reads earlier results only. -/
def wf (prog : List Op) : Bool :=
  (List.range prog.length).all fun i ↦ match lookup prog i with
    | some op => op.args.all (· < i)
    | none => true

/-- The value of an instruction depends only on the results it reads. -/
theorem Op.evalR_congr (x : ℕ → ℝ) {v w : List ℝ} (op : Op)
    (h : ∀ j ∈ op.args, getR v j = getR w j) : op.evalR x v = op.evalR x w := by
  cases op <;> simp_all [Op.evalR, Op.args]

theorem wf_append {prog : List Op} {op : Op} (h : wf (prog ++ [op]) = true) :
    wf prog = true ∧ ∀ j ∈ op.args, j < prog.length := by
  unfold wf at h ⊢
  rw [List.all_eq_true] at h ⊢
  constructor
  · intro i hi
    have hi' : i < prog.length := List.mem_range.1 hi
    have := h i (List.mem_range.2 (by simp; omega))
    rwa [lookup_append_lt _ hi'] at this
  · intro j hj
    have := h prog.length (List.mem_range.2 (by simp))
    rw [lookup_append_length] at this
    simp only [List.all_eq_true, decide_eq_true_eq] at this
    exact this j hj

theorem getR_append_lt {l : List ℝ} {i : ℕ} (a : ℝ) (h : i < l.length) :
    getR (l ++ [a]) i = getR l i := by
  rw [getR, getR, lookup_append_lt _ h]

/-- **The real result `i` is its instruction applied to the results of the program.** -/
theorem getR_evalR_eq (x : ℕ → ℝ) :
    ∀ {prog : List Op}, wf prog = true → ∀ {i : ℕ} {op : Op}, lookup prog i = some op →
      getR (evalR x prog) i = op.evalR x (evalR x prog) := by
  intro prog
  induction prog using List.reverseRecOn with
  | nil => intro _ i op h; simp [lookup] at h
  | append_singleton prog op' ih =>
    intro hwf i op h
    obtain ⟨hwf', hargs⟩ := wf_append hwf
    have hlen := length_evalR x prog
    have hi := lt_length_of_lookup h
    simp only [List.length_append, List.length_singleton] at hi
    rw [evalR_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [lookup_append_lt _ hi] at h
      rw [getR_append_lt _ (hlen ▸ hi), ih hwf' h]
      -- the arguments of `op` are earlier than `i`
      have hwfi : ∀ j ∈ op.args, j < i := by
        unfold wf at hwf'
        have := (List.all_eq_true.1 hwf') i (List.mem_range.2 hi)
        rw [h] at this
        simpa using this
      exact Op.evalR_congr x _ fun j hj ↦
        (getR_append_lt _ (hlen ▸ (hwfi j hj).trans hi)).symm
    · rw [lookup_append_length] at h
      cases h
      rw [getR, ← hlen, lookup_append_length, Option.getD_some]
      exact Op.evalR_congr x _ fun j hj ↦ (getR_append_lt _ (hlen ▸ hargs j hj)).symm

theorem length_evalI {p : ℕ} {env : List DyadicInterval} :
    ∀ {prog : List Op} {L : List DyadicInterval}, evalI p env prog = some L →
      L.length = prog.length := by
  intro prog
  induction prog using List.reverseRecOn with
  | nil => intro L h; cases h; rfl
  | append_singleton prog op ih =>
    intro L h
    rw [evalI_append, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h⟩ := h
    obtain ⟨I, -, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [ih hv]

theorem length_evalDual {p : ℕ} {env denv : List DyadicInterval} :
    ∀ {prog : List Op} {L : List (DyadicInterval × DyadicInterval)},
      evalDual p env denv prog = some L → L.length = prog.length := by
  intro prog
  induction prog using List.reverseRecOn with
  | nil => intro L h; cases h; rfl
  | append_singleton prog op ih =>
    intro L h
    rw [evalDual_append, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h⟩ := h
    obtain ⟨I, -, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [ih hv]

theorem exists_lookup {α : Type*} {l : List α} {i : ℕ} (h : i < l.length) :
    ∃ a, lookup l i = some a := by
  induction l generalizing i with
  | nil => simp at h
  | cons b l ih =>
    cases i with
    | zero => exact ⟨b, rfl⟩
    | succ i => exact ih (by simpa using h)

end DyadicInterval
