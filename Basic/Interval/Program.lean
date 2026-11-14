module

public import Basic.Interval.Elementary
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Straight-line programs over the reals, their interval evaluation and derivatives

A straight-line program is a list of instructions (`DyadicInterval.Op`), each computing a real
number from input variables, rational constants, `π`, and earlier results (referred to by their
index in the list) by `+`, `-`, `·`, `/`, `x²`, `√`, `sin`, `cos`, `arctan`. Shared
subexpressions are computed once.

* `evalR x prog`: the real values, for inputs `x : ℕ → ℝ`;
* `evalI p env prog`: interval enclosures for inputs enclosed by `env`, computable by the kernel;
  `none` if a division by an interval containing `0` occurs (`evalI_sound`);
* `evalDual p env denv prog`: forward-mode automatic differentiation in interval arithmetic: for a
  curve `s ↦ γ s` of inputs with `γ s₀ ∈ env` and `γ'(s₀) ∈ denv`, enclosures of the value and the
  derivative at `s₀` of `s ↦ evalR (γ s) prog` (`evalDual_sound`); the domain conditions of the
  derivative rules (nonzero denominators, positive arguments of `√`) are checked by the interval
  evaluation itself;
* `hasDerivAt_update_of_evalDual`: the partial derivative along the input variable `k`
  (`γ s = Function.update x k s`, `denv` the unit vector `seed p n k`);
* `exists_eq_mul_sub_of_hasDerivAt`: the mean value theorem in the form used with these
  enclosures, `f b - f a = d (b - a)` for some `d` with a property `P` that every derivative of `f`
  on `[a, b]` has.
-/

@[expose] public section

namespace DyadicInterval

/-! ### Lists -/

/-- The entry `i` of a list (structural recursion, for the kernel). -/
def lookup {α : Type*} : List α → ℕ → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, n + 1 => lookup l n

/-- The real entry `i` of a list, `0` out of range. -/
noncomputable def getR (l : List ℝ) (i : ℕ) : ℝ := (lookup l i).getD 0

theorem lookup_append_lt {α : Type*} {l : List α} {i : ℕ} (a : α) (h : i < l.length) :
    lookup (l ++ [a]) i = lookup l i := by
  induction l generalizing i with
  | nil => simp at h
  | cons b l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (by simpa using h)

theorem lookup_append_length {α : Type*} (l : List α) (a : α) :
    lookup (l ++ [a]) l.length = some a := by
  induction l with
  | nil => rfl
  | cons b l ih => exact ih

theorem lookup_append_gt {α : Type*} {l : List α} {i : ℕ} (a : α) (h : l.length < i) :
    lookup (l ++ [a]) i = none := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => simp at h
    | succ i => cases i <;> rfl
  | cons b l ih =>
    cases i with
    | zero => simp at h
    | succ i => exact ih (by simpa using h)

theorem lt_length_of_lookup {α : Type*} {l : List α} {i : ℕ} {a : α} (h : lookup l i = some a) :
    i < l.length := by
  induction l generalizing i with
  | nil => simp [lookup] at h
  | cons b l ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih h

/-! ### Programs -/

/-- An instruction of a straight-line program; the arguments `i`, `j` are indices of earlier
results. -/
inductive Op where
  /-- the input variable `k` -/
  | var (k : ℕ)
  /-- a rational constant -/
  | const (q : ℚ)
  /-- `π` -/
  | pi
  /-- `a + b` -/
  | add (i j : ℕ)
  /-- `a - b` -/
  | sub (i j : ℕ)
  /-- `a b` -/
  | mul (i j : ℕ)
  /-- `a / b` -/
  | div (i j : ℕ)
  /-- `-a` -/
  | neg (i : ℕ)
  /-- `a²` -/
  | sq (i : ℕ)
  /-- `√a` -/
  | sqrt (i : ℕ)
  /-- `sin a` -/
  | sin (i : ℕ)
  /-- `cos a` -/
  | cos (i : ℕ)
  /-- `arctan a` -/
  | arctan (i : ℕ)

/-- The real value of an instruction, given the inputs `x` and the earlier results `v`. -/
noncomputable def Op.evalR (x : ℕ → ℝ) (v : List ℝ) : Op → ℝ
  | .var k => x k
  | .const q => q
  | .pi => Real.pi
  | .add i j => getR v i + getR v j
  | .sub i j => getR v i - getR v j
  | .mul i j => getR v i * getR v j
  | .div i j => getR v i / getR v j
  | .neg i => -getR v i
  | .sq i => getR v i ^ 2
  | .sqrt i => Real.sqrt (getR v i)
  | .sin i => Real.sin (getR v i)
  | .cos i => Real.cos (getR v i)
  | .arctan i => Real.arctan (getR v i)

/-- The real values of all the instructions of a program. -/
noncomputable def evalR (x : ℕ → ℝ) (prog : List Op) : List ℝ :=
  prog.foldl (fun v op ↦ v ++ [op.evalR x v]) []

theorem evalR_append (x : ℕ → ℝ) (prog : List Op) (op : Op) :
    evalR x (prog ++ [op]) = evalR x prog ++ [op.evalR x (evalR x prog)] := by
  simp [evalR, List.foldl_append]

theorem length_evalR (x : ℕ → ℝ) (prog : List Op) : (evalR x prog).length = prog.length := by
  induction prog using List.reverseRecOn with
  | nil => rfl
  | append_singleton prog op ih => simp [evalR_append, ih]

/-! ### Interval evaluation -/

/-- The interval value of an instruction. -/
def Op.evalI (p : ℕ) (env v : List DyadicInterval) : Op → Option DyadicInterval
  | .var k => lookup env k
  | .const q => some (ofRat p q)
  | .pi => some (DyadicInterval.pi p)
  | .add i j => (lookup v i).bind fun a ↦ (lookup v j).map fun b ↦ DyadicInterval.add a b
  | .sub i j => (lookup v i).bind fun a ↦ (lookup v j).map fun b ↦ DyadicInterval.sub a b
  | .mul i j => (lookup v i).bind fun a ↦ (lookup v j).map fun b ↦ DyadicInterval.mul p a b
  | .div i j => (lookup v i).bind fun a ↦ (lookup v j).bind fun b ↦ div? p a b
  | .neg i => (lookup v i).map DyadicInterval.neg
  | .sq i => (lookup v i).map (DyadicInterval.sq p)
  | .sqrt i => (lookup v i).map (DyadicInterval.sqrt p)
  | .sin i => (lookup v i).map (DyadicInterval.sin p)
  | .cos i => (lookup v i).map (DyadicInterval.cos p)
  | .arctan i => (lookup v i).map (DyadicInterval.arctan p)

/-- The interval values of all the instructions of a program. -/
def evalI (p : ℕ) (env : List DyadicInterval) (prog : List Op) : Option (List DyadicInterval) :=
  prog.foldl (fun acc op ↦ acc.bind fun v ↦ (op.evalI p env v).map fun I ↦ v ++ [I]) (some [])

theorem evalI_append (p : ℕ) (env : List DyadicInterval) (prog : List Op) (op : Op) :
    evalI p env (prog ++ [op]) =
      (evalI p env prog).bind fun v ↦ (op.evalI p env v).map fun I ↦ v ++ [I] := by
  simp [evalI, List.foldl_append]

/-- Real values enclosed entry by entry by intervals. -/
def Encl (p : ℕ) (l : List ℝ) (L : List DyadicInterval) : Prop :=
  l.length = L.length ∧ ∀ i I, lookup L i = some I → Mem p I (getR l i)

theorem Encl.append {p : ℕ} {l : List ℝ} {L : List DyadicInterval} (h : Encl p l L) {a : ℝ}
    {I : DyadicInterval} (ha : Mem p I a) : Encl p (l ++ [a]) (L ++ [I]) := by
  refine ⟨by simp [h.1], fun i J hJ ↦ ?_⟩
  have hi := lt_length_of_lookup hJ
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
  · rw [lookup_append_lt _ hi] at hJ
    rw [getR, lookup_append_lt _ (h.1 ▸ hi)]
    exact h.2 i J hJ
  · rw [lookup_append_length] at hJ
    cases hJ
    rw [getR, ← h.1, lookup_append_length]
    exact ha

/-- The enclosure of one instruction. -/
theorem Op.evalI_sound {p : ℕ} {env : List DyadicInterval} {x : ℕ → ℝ}
    (henv : ∀ k I, lookup env k = some I → Mem p I (x k)) {l : List ℝ} {L : List DyadicInterval}
    (h : Encl p l L) (op : Op) {I : DyadicInterval} (hI : op.evalI p env L = some I) :
    Mem p I (op.evalR x l) := by
  cases op with
  | var k => exact henv k I hI
  | const q => cases hI; exact mem_ofRat p q
  | pi => cases hI; exact mem_pi p
  | add i j =>
    simp only [Op.evalI, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, b, hb, rfl⟩ := hI
    exact mem_add (h.2 i a ha) (h.2 j b hb)
  | sub i j =>
    simp only [Op.evalI, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, b, hb, rfl⟩ := hI
    exact mem_sub (h.2 i a ha) (h.2 j b hb)
  | mul i j =>
    simp only [Op.evalI, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, b, hb, rfl⟩ := hI
    exact mem_mul (h.2 i a ha) (h.2 j b hb)
  | div i j =>
    simp only [Op.evalI, Option.bind_eq_some_iff] at hI
    obtain ⟨a, ha, b, hb, hd⟩ := hI
    exact mem_div? hd (h.2 i a ha) (h.2 j b hb)
  | neg i =>
    simp only [Op.evalI, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, rfl⟩ := hI
    exact mem_neg (h.2 i a ha)
  | sq i =>
    simp only [Op.evalI, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, rfl⟩ := hI
    exact mem_sq (h.2 i a ha)
  | sqrt i =>
    simp only [Op.evalI, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, rfl⟩ := hI
    exact mem_sqrt (h.2 i a ha)
  | sin i =>
    simp only [Op.evalI, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, rfl⟩ := hI
    exact mem_sin (h.2 i a ha)
  | cos i =>
    simp only [Op.evalI, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, rfl⟩ := hI
    exact mem_cos (h.2 i a ha)
  | arctan i =>
    simp only [Op.evalI, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, rfl⟩ := hI
    exact mem_arctan (h.2 i a ha)

/-- **Soundness of the interval evaluation**: if the inputs lie in `env`, every result lies in its
interval. -/
theorem evalI_sound {p : ℕ} {env : List DyadicInterval} {x : ℕ → ℝ}
    (henv : ∀ k I, lookup env k = some I → Mem p I (x k)) :
    ∀ (prog : List Op) {L : List DyadicInterval}, evalI p env prog = some L →
      Encl p (evalR x prog) L := by
  intro prog
  induction prog using List.reverseRecOn with
  | nil =>
    intro L hL
    cases hL
    exact ⟨rfl, fun i I h ↦ by simp [lookup] at h⟩
  | append_singleton prog op ih =>
    intro L hL
    rw [evalI_append, Option.bind_eq_some_iff] at hL
    obtain ⟨v, hv, hL⟩ := hL
    rw [Option.map_eq_some_iff] at hL
    obtain ⟨I, hI, rfl⟩ := hL
    rw [evalR_append]
    have h := ih hv
    exact h.append (op.evalI_sound henv h hI)

/-- The interval of the result `i` of a program. -/
def valueAt (p : ℕ) (env : List DyadicInterval) (prog : List Op) (i : ℕ) :
    Option DyadicInterval :=
  (evalI p env prog).bind fun L ↦ lookup L i

theorem mem_valueAt {p : ℕ} {env : List DyadicInterval} {prog : List Op} {i : ℕ}
    {I : DyadicInterval} (h : valueAt p env prog i = some I) {x : ℕ → ℝ}
    (henv : ∀ k I, lookup env k = some I → Mem p I (x k)) : Mem p I (getR (evalR x prog) i) := by
  rw [valueAt, Option.bind_eq_some_iff] at h
  obtain ⟨L, hL, hI⟩ := h
  exact (evalI_sound henv prog hL).2 i I hI

/-! ### Forward-mode differentiation in interval arithmetic -/

/-- The point interval `[0, 0]`. -/
def zero : DyadicInterval := ⟨0, 0⟩

theorem mem_zero (p : ℕ) : Mem p zero 0 := by simp [Mem, zero]

/-- The interval value and derivative of an instruction (forward mode). -/
def Op.evalDual (p : ℕ) (env denv : List DyadicInterval)
    (v : List (DyadicInterval × DyadicInterval)) : Op → Option (DyadicInterval × DyadicInterval)
  | .var k => (lookup env k).bind fun a ↦ (lookup denv k).map fun a' ↦ (a, a')
  | .const q => some (ofRat p q, zero)
  | .pi => some (DyadicInterval.pi p, zero)
  | .add i j => (lookup v i).bind fun a ↦ (lookup v j).map fun b ↦
      (DyadicInterval.add a.1 b.1, DyadicInterval.add a.2 b.2)
  | .sub i j => (lookup v i).bind fun a ↦ (lookup v j).map fun b ↦
      (DyadicInterval.sub a.1 b.1, DyadicInterval.sub a.2 b.2)
  | .mul i j => (lookup v i).bind fun a ↦ (lookup v j).map fun b ↦
      (DyadicInterval.mul p a.1 b.1,
        DyadicInterval.add (DyadicInterval.mul p a.2 b.1) (DyadicInterval.mul p a.1 b.2))
  | .div i j => (lookup v i).bind fun a ↦ (lookup v j).bind fun b ↦ (div? p a.1 b.1).bind
      fun q ↦ (div? p (DyadicInterval.sub a.2 (DyadicInterval.mul p q b.2)) b.1).map
        fun d ↦ (q, d)
  | .neg i => (lookup v i).map fun a ↦ (DyadicInterval.neg a.1, DyadicInterval.neg a.2)
  | .sq i => (lookup v i).map fun a ↦
      (DyadicInterval.sq p a.1, smulNat 2 (DyadicInterval.mul p a.1 a.2))
  | .sqrt i => (lookup v i).bind fun a ↦
      (div? p a.2 (smulNat 2 (DyadicInterval.sqrt p a.1))).map
        fun d ↦ (DyadicInterval.sqrt p a.1, d)
  | .sin i => (lookup v i).map fun a ↦
      (DyadicInterval.sin p a.1, DyadicInterval.mul p (DyadicInterval.cos p a.1) a.2)
  | .cos i => (lookup v i).map fun a ↦
      (DyadicInterval.cos p a.1,
        DyadicInterval.neg (DyadicInterval.mul p (DyadicInterval.sin p a.1) a.2))
  | .arctan i => (lookup v i).bind fun a ↦
      (div? p a.2 (DyadicInterval.add (ofInt (scale p)) (DyadicInterval.sq p a.1))).map
        fun d ↦ (DyadicInterval.arctan p a.1, d)

/-- The interval values and derivatives of all the instructions of a program. -/
def evalDual (p : ℕ) (env denv : List DyadicInterval) (prog : List Op) :
    Option (List (DyadicInterval × DyadicInterval)) :=
  prog.foldl (fun acc op ↦ acc.bind fun v ↦ (op.evalDual p env denv v).map fun I ↦ v ++ [I])
    (some [])

theorem evalDual_append (p : ℕ) (env denv : List DyadicInterval) (prog : List Op) (op : Op) :
    evalDual p env denv (prog ++ [op]) =
      (evalDual p env denv prog).bind fun v ↦ (op.evalDual p env denv v).map fun I ↦ v ++ [I] := by
  simp [evalDual, List.foldl_append]

/-- The invariant of the differentiation: along the curve `s ↦ l s` of real lists, every entry
lies in its value interval at `s₀` and has a derivative at `s₀` in its derivative interval. -/
def DualEncl (p : ℕ) (l : ℝ → List ℝ) (s₀ : ℝ) (L : List (DyadicInterval × DyadicInterval)) :
    Prop :=
  (l s₀).length = L.length ∧ ∀ i I, lookup L i = some I →
    Mem p I.1 (getR (l s₀) i) ∧ ∃ d, HasDerivAt (fun s ↦ getR (l s) i) d s₀ ∧ Mem p I.2 d

/-- The derivative of one instruction along a curve. -/
theorem Op.evalDual_sound {p : ℕ} {env denv : List DyadicInterval} {γ : ℝ → ℕ → ℝ}
    {γ' : ℕ → ℝ} {s₀ : ℝ} (hγ : ∀ k, HasDerivAt (fun s ↦ γ s k) (γ' k) s₀)
    (henv : ∀ k I, lookup env k = some I → Mem p I (γ s₀ k))
    (hdenv : ∀ k I, lookup denv k = some I → Mem p I (γ' k)) {l : ℝ → List ℝ}
    {L : List (DyadicInterval × DyadicInterval)} (h : DualEncl p l s₀ L) (op : Op)
    {I : DyadicInterval × DyadicInterval} (hI : op.evalDual p env denv L = some I) :
    Mem p I.1 (op.evalR (γ s₀) (l s₀)) ∧
      ∃ d, HasDerivAt (fun s ↦ op.evalR (γ s) (l s)) d s₀ ∧ Mem p I.2 d := by
  cases op with
  | var k =>
    simp only [Op.evalDual, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, a', ha', rfl⟩ := hI
    exact ⟨henv k a ha, γ' k, hγ k, hdenv k a' ha'⟩
  | const q =>
    cases hI
    exact ⟨mem_ofRat p q, 0, hasDerivAt_const _ _, mem_zero p⟩
  | pi =>
    cases hI
    exact ⟨mem_pi p, 0, hasDerivAt_const _ _, mem_zero p⟩
  | add i j =>
    simp only [Op.evalDual, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, b, hb, rfl⟩ := hI
    obtain ⟨va, da, hda, hma⟩ := h.2 i a ha
    obtain ⟨vb, db, hdb, hmb⟩ := h.2 j b hb
    exact ⟨mem_add va vb, da + db, hda.add hdb, mem_add hma hmb⟩
  | sub i j =>
    simp only [Op.evalDual, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, b, hb, rfl⟩ := hI
    obtain ⟨va, da, hda, hma⟩ := h.2 i a ha
    obtain ⟨vb, db, hdb, hmb⟩ := h.2 j b hb
    exact ⟨mem_sub va vb, da - db, hda.sub hdb, mem_sub hma hmb⟩
  | mul i j =>
    simp only [Op.evalDual, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, b, hb, rfl⟩ := hI
    obtain ⟨va, da, hda, hma⟩ := h.2 i a ha
    obtain ⟨vb, db, hdb, hmb⟩ := h.2 j b hb
    exact ⟨mem_mul va vb, _, hda.mul hdb, mem_add (mem_mul hma vb) (mem_mul va hmb)⟩
  | div i j =>
    simp only [Op.evalDual, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, b, hb, q, hq, d, hd, rfl⟩ := hI
    obtain ⟨va, da, hda, hma⟩ := h.2 i a ha
    obtain ⟨vb, db, hdb, hmb⟩ := h.2 j b hb
    have hne : getR (l s₀) j ≠ 0 := by
      unfold div? at hq
      obtain ⟨K, hK, -⟩ := Option.map_eq_some_iff.1 hq
      exact ne_zero_of_inv? hK vb
    have hq' := mem_div? hq va vb
    refine ⟨hq', _, hda.div hdb hne, ?_⟩
    have e : (da * getR (l s₀) j - getR (l s₀) i * db) / getR (l s₀) j ^ 2 =
        (da - getR (l s₀) i / getR (l s₀) j * db) / getR (l s₀) j := by
      field_simp
    rw [e]
    exact mem_div? hd (mem_sub hma (mem_mul hq' hmb)) vb
  | neg i =>
    simp only [Op.evalDual, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, rfl⟩ := hI
    obtain ⟨va, da, hda, hma⟩ := h.2 i a ha
    exact ⟨mem_neg va, -da, hda.neg, mem_neg hma⟩
  | sq i =>
    simp only [Op.evalDual, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, rfl⟩ := hI
    obtain ⟨va, da, hda, hma⟩ := h.2 i a ha
    refine ⟨mem_sq va, _, hda.pow 2, ?_⟩
    have e : ((2 : ℕ) : ℝ) * getR (l s₀) i ^ (2 - 1) * da = (2 : ℕ) * (getR (l s₀) i * da) := by
      ring
    rw [e]
    exact mem_smulNat 2 (mem_mul va hma)
  | sqrt i =>
    simp only [Op.evalDual, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, d, hd, rfl⟩ := hI
    obtain ⟨va, da, hda, hma⟩ := h.2 i a ha
    have hs := mem_sqrt va
    have hne : getR (l s₀) i ≠ 0 := by
      intro h0
      unfold div? at hd
      obtain ⟨K, hK, -⟩ := Option.map_eq_some_iff.1 hd
      have := ne_zero_of_inv? hK (mem_smulNat 2 hs)
      rw [h0, Real.sqrt_zero, mul_zero] at this
      exact this rfl
    refine ⟨hs, _, hda.sqrt hne, ?_⟩
    exact_mod_cast mem_div? hd hma (mem_smulNat 2 hs)
  | sin i =>
    simp only [Op.evalDual, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, rfl⟩ := hI
    obtain ⟨va, da, hda, hma⟩ := h.2 i a ha
    exact ⟨mem_sin va, _, hda.sin, mem_mul (mem_cos va) hma⟩
  | cos i =>
    simp only [Op.evalDual, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, rfl⟩ := hI
    obtain ⟨va, da, hda, hma⟩ := h.2 i a ha
    refine ⟨mem_cos va, _, hda.cos, ?_⟩
    rw [neg_mul]
    exact mem_neg (mem_mul (mem_sin va) hma)
  | arctan i =>
    simp only [Op.evalDual, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hI
    obtain ⟨a, ha, d, hd, rfl⟩ := hI
    obtain ⟨va, da, hda, hma⟩ := h.2 i a ha
    refine ⟨mem_arctan va, _, hda.arctan, ?_⟩
    rw [one_div_mul_eq_div]
    exact mem_div? hd hma (mem_add (mem_one p) (mem_sq va))

/-- **Soundness of the differentiation**: for a curve of inputs `s ↦ γ s` with derivative `γ'` at
`s₀`, `γ s₀ ∈ env` and `γ' ∈ denv`, every result of the program has, as a function of `s`, a value
at `s₀` and a derivative at `s₀` in its intervals. -/
theorem evalDual_sound {p : ℕ} {env denv : List DyadicInterval} {γ : ℝ → ℕ → ℝ}
    {γ' : ℕ → ℝ} {s₀ : ℝ} (hγ : ∀ k, HasDerivAt (fun s ↦ γ s k) (γ' k) s₀)
    (henv : ∀ k I, lookup env k = some I → Mem p I (γ s₀ k))
    (hdenv : ∀ k I, lookup denv k = some I → Mem p I (γ' k)) :
    ∀ (prog : List Op) {L : List (DyadicInterval × DyadicInterval)},
      evalDual p env denv prog = some L → DualEncl p (fun s ↦ evalR (γ s) prog) s₀ L := by
  intro prog
  induction prog using List.reverseRecOn with
  | nil =>
    intro L hL
    cases hL
    exact ⟨rfl, fun i I h ↦ by simp [lookup] at h⟩
  | append_singleton prog op ih =>
    intro L hL
    rw [evalDual_append, Option.bind_eq_some_iff] at hL
    obtain ⟨v, hv, hL⟩ := hL
    rw [Option.map_eq_some_iff] at hL
    obtain ⟨I, hI, rfl⟩ := hL
    have h := ih hv
    obtain ⟨hv1, hd1⟩ := op.evalDual_sound hγ henv hdenv h hI
    refine ⟨by simp [evalR_append, h.1], fun i J hJ ↦ ?_⟩
    have hi := lt_length_of_lookup hJ
    simp only [List.length_append, List.length_singleton] at hi
    have hlen : ∀ s, (evalR (γ s) prog).length = v.length := fun s ↦ by
      rw [length_evalR, ← h.1, length_evalR]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [lookup_append_lt _ hi] at hJ
      have key : ∀ s (a : ℝ), lookup (evalR (γ s) prog ++ [a]) i = lookup (evalR (γ s) prog) i :=
        fun s a ↦ lookup_append_lt _ (by rw [hlen s]; exact hi)
      simp only [evalR_append, getR, key]
      exact h.2 i J hJ
    · rw [lookup_append_length] at hJ
      cases hJ
      have key : ∀ s (a : ℝ), lookup (evalR (γ s) prog ++ [a]) v.length = some a :=
        fun s a ↦ by rw [← hlen s]; exact lookup_append_length _ _
      simp only [evalR_append, getR, key, Option.getD_some]
      exact ⟨hv1, hd1⟩

/-- The interval value and derivative of the result `i` of a program. -/
def dualAt (p : ℕ) (env denv : List DyadicInterval) (prog : List Op) (i : ℕ) :
    Option (DyadicInterval × DyadicInterval) :=
  (evalDual p env denv prog).bind fun L ↦ lookup L i

/-- The unit vector `e_k` of length `n` as a list of point intervals (the seed of the partial
derivative along the input `k`). -/
def seed (p n k : ℕ) : List DyadicInterval :=
  (List.range n).map fun m ↦ if m = k then ofInt (scale p) else zero

theorem lookup_map {α β : Type*} (f : α → β) (l : List α) (i : ℕ) :
    lookup (l.map f) i = (lookup l i).map f := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih => cases i <;> simp [lookup, ih]

theorem lookup_range (n i : ℕ) : lookup (List.range n) i = if i < n then some i else none := by
  induction n with
  | zero => simp [lookup]
  | succ n ih =>
    rw [List.range_succ]
    rcases lt_trichotomy i n with h | rfl | h
    · rw [lookup_append_lt _ (by simpa using h), ih, ite_eq_left h, ite_eq_left (by omega)]
    · have := lookup_append_length (List.range i) i
      rw [List.length_range] at this
      rw [this]; simp
    · rw [lookup_append_gt _ (by simpa using h), ite_eq_right (by omega)]

/-- **Partial derivatives**: with the seed `e_k`, `dualAt` encloses the value of the result `i` at
`x` and its derivative in the input `k`. -/
theorem hasDerivAt_update_of_dualAt {p : ℕ} {env : List DyadicInterval} {n k : ℕ}
    {prog : List Op} {i : ℕ} {I : DyadicInterval × DyadicInterval}
    (h : dualAt p env (seed p n k) prog i = some I) {x : ℕ → ℝ}
    (henv : ∀ m J, lookup env m = some J → Mem p J (x m)) :
    Mem p I.1 (getR (evalR x prog) i) ∧
      ∃ d, HasDerivAt (fun s ↦ getR (evalR (Function.update x k s) prog) i) d (x k) ∧
        Mem p I.2 d := by
  rw [dualAt, Option.bind_eq_some_iff] at h
  obtain ⟨L, hL, hI⟩ := h
  have hγ : ∀ m, HasDerivAt (fun s ↦ Function.update x k s m) (if m = k then 1 else 0) (x k) := by
    intro m
    by_cases hm : m = k
    · subst hm
      simp only [Function.update_self, ite_true]
      exact hasDerivAt_id _
    · simp only [Function.update_of_ne hm, ite_eq_right hm]
      exact hasDerivAt_const _ _
  have henv' : ∀ m J, lookup env m = some J → Mem p J (Function.update x k (x k) m) := by
    intro m J hJ
    rw [Function.update_eq_self]
    exact henv m J hJ
  have hdenv : ∀ m J, lookup (seed p n k) m = some J → Mem p J (if m = k then 1 else 0) := by
    intro m J hJ
    rw [seed, lookup_map, lookup_range] at hJ
    split_ifs at hJ with h1
    · simp only [Option.map_some, Option.some.injEq] at hJ
      subst hJ
      split_ifs with h2
      · exact mem_one p
      · exact mem_zero p
    · simp at hJ
  have := (evalDual_sound hγ henv' hdenv prog hL).2 i I hI
  simp only [Function.update_eq_self] at this
  exact this

/-! ### The mean value theorem for enclosed derivatives -/

/-- If at every point of `[a, b]` (either order) `f` has a derivative with a property `P`, then
`f b - f a = d (b - a)` for some `d` with `P d`. -/
theorem exists_eq_mul_sub_of_hasDerivAt {f : ℝ → ℝ} {a b : ℝ} {P : ℝ → Prop}
    (h : ∀ s ∈ Set.uIcc a b, ∃ d, HasDerivAt f d s ∧ P d) :
    ∃ d, P d ∧ f b - f a = d * (b - a) := by
  -- the case `a < b`
  have key : ∀ a b : ℝ, a < b → (∀ s ∈ Set.Icc a b, ∃ d, HasDerivAt f d s ∧ P d) →
      ∃ d, P d ∧ f b - f a = d * (b - a) := by
    intro a b hab h
    have hd : ∀ s ∈ Set.Icc a b, HasDerivAt f (deriv f s) s := fun s hs ↦ by
      obtain ⟨d, hd, -⟩ := h s hs
      rwa [hd.deriv]
    have hc : ContinuousOn f (Set.Icc a b) := fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt
    obtain ⟨c, hc', hcd⟩ := exists_hasDerivAt_eq_slope f (deriv f) hab hc
      (fun s hs ↦ hd s (Set.Ioo_subset_Icc_self hs))
    obtain ⟨d, hd', hP⟩ := h c (Set.Ioo_subset_Icc_self hc')
    refine ⟨d, hP, ?_⟩
    rw [← hd'.deriv, hcd]
    field_simp [(sub_pos.2 hab).ne']
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact key a b hab fun s hs ↦ h s (Set.Icc_subset_uIcc hs)
  · obtain ⟨d, -, hP⟩ := h a (by simp)
    exact ⟨d, hP, by ring⟩
  · obtain ⟨d, hP, e⟩ := key b a hab fun s hs ↦ h s (Set.Icc_subset_uIcc' hs)
    exact ⟨d, hP, by linarith⟩

end DyadicInterval
