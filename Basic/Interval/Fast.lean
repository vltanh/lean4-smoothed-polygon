module

public import Basic.Interval.ProgramEval

/-!
# A faster kernel evaluator for straight-line programs

The evaluators `evalI` and `evalDual` of `Basic/Interval/Program.lean` keep the results in a list
in program order, append each new result at the end (`v ++ [I]`, linear in the length) and read an
operand `i` by walking `i` steps from the front; every step goes through `Option.bind`. In the
kernel the list operations dominate the arithmetic (`notes/lp/measurements.txt`). The evaluators
here compute the same enclosures of the same real semantics (`evalR`, `getR`):

* the results are kept **most recent first** (`::`, constant time); the operand `i` of the
  instruction `n` is read `n - 1 - i` steps back (`nth`), a short distance for the local operands
  of a straight-line program;
* **no `Option`**: every operation is total and the domain conditions (a divisor interval not
  containing `0`, for `/`, and in the derivatives of `√` and `arctan`) are collected in one Boolean
  flag; the results are sound when the flag is `true` (`runT_sound`, `runV_sound`);
* **vector-mode differentiation** (`runV`): the value of each instruction is computed once
  together with its derivatives in `m` directions (along `m` curves of inputs through the same
  point), instead of one pass per direction.

The programs must be well formed (`wfFrom 0 prog`: every instruction reads earlier results only),
which the kernel checks once per program.
-/

@[expose] public section

namespace DyadicInterval

/-! ### Lists read from the front -/

/-- The entry `n` of a list, `d` out of range (structural recursion, for the kernel). -/
def nth {α : Type*} : List α → ℕ → α → α
  | [], _, d => d
  | a :: _, 0, _ => a
  | _ :: l, n + 1, d => nth l n d

@[simp] theorem nth_cons_zero {α : Type*} (a : α) (l : List α) (d : α) : nth (a :: l) 0 d = a :=
  rfl

@[simp] theorem nth_cons_succ {α : Type*} (a : α) (l : List α) (n : ℕ) (d : α) :
    nth (a :: l) (n + 1) d = nth l n d := rfl

theorem nth_map {α β : Type*} (f : α → β) {l : List α} {n : ℕ} (h : n < l.length) (d : α)
    (d' : β) : nth (l.map f) n d' = f (nth l n d) := by
  induction l generalizing n with
  | nil => simp at h
  | cons a l ih => cases n <;> simp_all [nth]

theorem nth_zipWith {α β γ : Type*} (f : α → β → γ) {l : List α} {l' : List β} {n : ℕ}
    (h : n < l.length) (h' : n < l'.length) (d : α) (d' : β) (d'' : γ) :
    nth (List.zipWith f l l') n d'' = f (nth l n d) (nth l' n d') := by
  induction l generalizing l' n with
  | nil => simp at h
  | cons a l ih =>
    cases l' with
    | nil => simp at h'
    | cons b l' => cases n <;> simp_all [nth]

theorem nth_replicate {α : Type*} {m n : ℕ} (h : n < m) (a d : α) :
    nth (List.replicate m a) n d = a := by
  induction m generalizing n with
  | zero => omega
  | succ m ih => cases n <;> simp_all [List.replicate_succ]

/-! ### Total interval operations with a domain flag -/

/-- The divisor test: every point of `I` is nonzero. -/
def nz (I : DyadicInterval) : Bool := decide (0 < I.lo) || decide (I.hi < 0)

/-- The reciprocal, rounded outward; meaningful when `nz I`. -/
def invT (p : ℕ) (I : DyadicInterval) : DyadicInterval :=
  if 0 < I.lo then invPos p I else neg (invPos p (neg I))

theorem mem_invT {p : ℕ} {I : DyadicInterval} (h : nz I = true) {x : ℝ} (hx : Mem p I x) :
    Mem p (invT p I) x⁻¹ := by
  have h' : inv? p I = some (invT p I) := by
    unfold nz at h
    unfold inv? invT
    split_ifs with h1 h2
    · rfl
    · rfl
    · simp_all
  exact mem_inv? h' hx

theorem ne_zero_of_nz {p : ℕ} {I : DyadicInterval} (h : nz I = true) {x : ℝ} (hx : Mem p I x) :
    x ≠ 0 := by
  have h' : inv? p I = some (invT p I) := by
    unfold nz at h
    unfold inv? invT
    split_ifs with h1 h2
    · rfl
    · rfl
    · simp_all
  exact ne_zero_of_inv? h' hx

/-- The quotient, rounded outward; meaningful when `nz J`. -/
def divT (p : ℕ) (I J : DyadicInterval) : DyadicInterval := mul p I (invT p J)

theorem mem_divT {p : ℕ} {I J : DyadicInterval} (h : nz J = true) {x y : ℝ} (hx : Mem p I x)
    (hy : Mem p J y) : Mem p (divT p I J) (x / y) := by
  rw [div_eq_mul_inv]; exact mem_mul hx (mem_invT h hy)

/-- The interval `[1, 1]`. -/
def one (p : ℕ) : DyadicInterval := ofInt (scale p)

/-! ### Well-formed programs -/

/-- The instructions of `ops`, the first at position `n`, read earlier results only. -/
def wfFrom : ℕ → List Op → Bool
  | _, [] => true
  | n, op :: ops => op.args.all (· < n) && wfFrom (n + 1) ops

theorem wfFrom_cons {n : ℕ} {op : Op} {ops : List Op} (h : wfFrom n (op :: ops) = true) :
    (∀ j ∈ op.args, j < n) ∧ wfFrom (n + 1) ops = true := by
  simp only [wfFrom, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h

/-! ### The real semantics, one instruction at a time -/

/-- One step of the real evaluation `evalR`. -/
noncomputable def stepR (x : ℕ → ℝ) (v : List ℝ) (op : Op) : List ℝ := v ++ [op.evalR x v]

theorem evalR_eq_foldl (x : ℕ → ℝ) (prog : List Op) : evalR x prog = prog.foldl (stepR x) [] :=
  rfl

/-- The invariant of the reversed store: `st` holds enclosures of the entries of `l`, the last
first. -/
def REncl (p : ℕ) (l : List ℝ) (st : List DyadicInterval) : Prop :=
  st.length = l.length ∧ ∀ i < l.length, Mem p (nth st (l.length - 1 - i) zero) (getR l i)

theorem REncl.cons {p : ℕ} {l : List ℝ} {st : List DyadicInterval} (h : REncl p l st) {a : ℝ}
    {A : DyadicInterval} (ha : Mem p A a) : REncl p (l ++ [a]) (A :: st) := by
  refine ⟨by simp [h.1], fun i hi ↦ ?_⟩
  simp only [List.length_append, List.length_singleton] at hi ⊢
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
  · have e : l.length + 1 - 1 - i = (l.length - 1 - i) + 1 := by omega
    rw [e, nth_cons_succ, getR_append_lt _ hi]
    exact h.2 i hi
  · rw [show l.length + 1 - 1 - l.length = 0 by omega, nth_cons_zero, getR,
      lookup_append_length, Option.getD_some]
    exact ha

/-! ### Interval evaluation -/

/-- Read the operand `i` of the instruction at position `n` from the reversed store. -/
def rget (st : List DyadicInterval) (n i : ℕ) : DyadicInterval := nth st (n - 1 - i) zero

/-- The interval value of an instruction at position `n`. -/
def Op.valT (p : ℕ) (env st : List DyadicInterval) (n : ℕ) : Op → DyadicInterval
  | .var k => nth env k zero
  | .const q => ofRat p q
  | .pi => DyadicInterval.pi p
  | .add i j => DyadicInterval.add (rget st n i) (rget st n j)
  | .sub i j => DyadicInterval.sub (rget st n i) (rget st n j)
  | .mul i j => DyadicInterval.mul p (rget st n i) (rget st n j)
  | .div i j => divT p (rget st n i) (rget st n j)
  | .neg i => DyadicInterval.neg (rget st n i)
  | .sq i => DyadicInterval.sq p (rget st n i)
  | .sqrt i => DyadicInterval.sqrt p (rget st n i)
  | .sin i => DyadicInterval.sin p (rget st n i)
  | .cos i => DyadicInterval.cos p (rget st n i)
  | .arctan i => DyadicInterval.arctan p (rget st n i)

/-- The domain condition of an instruction (a divisor interval not containing `0`). -/
def Op.okT (st : List DyadicInterval) (n : ℕ) : Op → Bool
  | .div _ j => nz (rget st n j)
  | _ => true

/-- Run the instructions `ops`, the first at position `n`, on the reversed store `st`. -/
def runT (p : ℕ) (env : List DyadicInterval) :
    List Op → List DyadicInterval → ℕ → Bool → List DyadicInterval × Bool
  | [], st, _, ok => (st, ok)
  | op :: ops, st, n, ok => runT p env ops (op.valT p env st n :: st) (n + 1) (op.okT st n && ok)

/-- The interval evaluation of a program: its results, the last first, and the domain flag. -/
def evalT (p : ℕ) (env : List DyadicInterval) (prog : List Op) : List DyadicInterval × Bool :=
  runT p env prog [] 0 true

/-- The enclosure of the result `i` of a program of length `n` from its reversed results. -/
def resT (st : List DyadicInterval) (n i : ℕ) : DyadicInterval := nth st (n - 1 - i) zero

theorem Op.valT_sound {p : ℕ} {env : List DyadicInterval} {x : ℕ → ℝ}
    (henv : ∀ k, Mem p (nth env k zero) (x k)) {l : List ℝ} {st : List DyadicInterval}
    (h : REncl p l st) (op : Op) (hargs : ∀ j ∈ op.args, j < l.length)
    (hok : op.okT st l.length = true) : Mem p (op.valT p env st l.length) (op.evalR x l) := by
  have g : ∀ i, i < l.length → Mem p (rget st l.length i) (getR l i) := fun i hi ↦ h.2 i hi
  have a1 : ∀ {i j : ℕ}, i < l.length → j < l.length →
      Mem p (rget st l.length i) (getR l i) ∧ Mem p (rget st l.length j) (getR l j) :=
    fun hi hj ↦ ⟨g _ hi, g _ hj⟩
  cases op with
  | var k => exact henv k
  | const q => exact mem_ofRat p q
  | pi => exact mem_pi p
  | add i j =>
    obtain ⟨u, v⟩ := a1 (hargs i (by simp [Op.args])) (hargs j (by simp [Op.args]))
    exact mem_add u v
  | sub i j =>
    obtain ⟨u, v⟩ := a1 (hargs i (by simp [Op.args])) (hargs j (by simp [Op.args]))
    exact mem_sub u v
  | mul i j =>
    obtain ⟨u, v⟩ := a1 (hargs i (by simp [Op.args])) (hargs j (by simp [Op.args]))
    exact mem_mul u v
  | div i j =>
    obtain ⟨u, v⟩ := a1 (hargs i (by simp [Op.args])) (hargs j (by simp [Op.args]))
    exact mem_divT hok u v
  | neg i => exact mem_neg (g i (hargs i (by simp [Op.args])))
  | sq i => exact mem_sq (g i (hargs i (by simp [Op.args])))
  | sqrt i => exact mem_sqrt (g i (hargs i (by simp [Op.args])))
  | sin i => exact mem_sin (g i (hargs i (by simp [Op.args])))
  | cos i => exact mem_cos (g i (hargs i (by simp [Op.args])))
  | arctan i => exact mem_arctan (g i (hargs i (by simp [Op.args])))

theorem runT_ok {p : ℕ} {env : List DyadicInterval} :
    ∀ (ops : List Op) (st : List DyadicInterval) (n : ℕ) (ok : Bool),
      (runT p env ops st n ok).2 = true → ok = true
  | [], _, _, _, h => h
  | op :: ops, st, n, ok, h => by
    have := runT_ok ops _ _ _ h
    simp only [Bool.and_eq_true] at this
    exact this.2

theorem runT_sound {p : ℕ} {env : List DyadicInterval} {x : ℕ → ℝ}
    (henv : ∀ k, Mem p (nth env k zero) (x k)) :
    ∀ (ops : List Op) (l : List ℝ) (st : List DyadicInterval) (ok : Bool),
      wfFrom l.length ops = true → REncl p l st → (runT p env ops st l.length ok).2 = true →
      REncl p (ops.foldl (stepR x) l) (runT p env ops st l.length ok).1
  | [], _, _, _, _, h, _ => h
  | op :: ops, l, st, ok, hwf, h, hok => by
    obtain ⟨hargs, hwf'⟩ := wfFrom_cons hwf
    have hok' := runT_ok ops _ _ _ hok
    simp only [Bool.and_eq_true] at hok'
    have h1 := h.cons (Op.valT_sound henv h op hargs hok'.1)
    have hlen : (l ++ [op.evalR x l]).length = l.length + 1 := by simp
    have := runT_sound henv ops (l ++ [op.evalR x l]) _ (op.okT st l.length && ok)
      (hlen ▸ hwf') h1 (hlen ▸ hok)
    rw [hlen] at this
    exact this

/-- **Soundness of the fast interval evaluation**: for a well-formed program, inputs enclosed by
`env` and a `true` domain flag, every result `i` lies in `resT st n i`. -/
theorem evalT_sound {p : ℕ} {env : List DyadicInterval} {x : ℕ → ℝ}
    (henv : ∀ k, Mem p (nth env k zero) (x k)) {prog : List Op} (hwf : wfFrom 0 prog = true)
    (hok : (evalT p env prog).2 = true) :
    ∀ i < prog.length, Mem p (resT (evalT p env prog).1 prog.length i) (getR (evalR x prog) i) := by
  have h := runT_sound henv prog [] [] true hwf ⟨rfl, fun i hi ↦ by simp at hi⟩ hok
  intro i hi
  have hl : (evalR x prog).length = prog.length := length_evalR x prog
  have := h.2 i (by rw [← evalR_eq_foldl, hl]; exact hi)
  rw [← evalR_eq_foldl, hl] at this
  exact this

/-! ### Vector-mode differentiation -/

/-- A value with its derivatives in the `m` directions. -/
abbrev DualV := DyadicInterval × List DyadicInterval

/-- The zero vector of length `m`. -/
def zeros (m : ℕ) : List DyadicInterval := List.replicate m zero

/-- Read the operand `i` of the instruction at position `n` from the reversed store. -/
def rgetV (st : List DualV) (n i : ℕ) : DualV := nth st (n - 1 - i) (zero, [])

/-- The interval value and derivatives of an instruction at position `n` (`denv k`: the
derivatives of the input `k`). -/
def Op.valV (p m : ℕ) (env : List DyadicInterval) (denv : List (List DyadicInterval))
    (st : List DualV) (n : ℕ) : Op → DualV
  | .var k => (nth env k zero, nth denv k (zeros m))
  | .const q => (ofRat p q, zeros m)
  | .pi => (DyadicInterval.pi p, zeros m)
  | .add i j =>
    let a := rgetV st n i
    let b := rgetV st n j
    (DyadicInterval.add a.1 b.1, List.zipWith DyadicInterval.add a.2 b.2)
  | .sub i j =>
    let a := rgetV st n i
    let b := rgetV st n j
    (DyadicInterval.sub a.1 b.1, List.zipWith DyadicInterval.sub a.2 b.2)
  | .mul i j =>
    let a := rgetV st n i
    let b := rgetV st n j
    (DyadicInterval.mul p a.1 b.1,
      List.zipWith (fun u v ↦ DyadicInterval.add (DyadicInterval.mul p u b.1)
        (DyadicInterval.mul p a.1 v)) a.2 b.2)
  | .div i j =>
    let a := rgetV st n i
    let b := rgetV st n j
    let q := divT p a.1 b.1
    let r := invT p b.1
    (q, List.zipWith (fun u v ↦ DyadicInterval.mul p (DyadicInterval.sub u
      (DyadicInterval.mul p q v)) r) a.2 b.2)
  | .neg i =>
    let a := rgetV st n i
    (DyadicInterval.neg a.1, a.2.map DyadicInterval.neg)
  | .sq i =>
    let a := rgetV st n i
    (DyadicInterval.sq p a.1, a.2.map fun u ↦ smulNat 2 (DyadicInterval.mul p a.1 u))
  | .sqrt i =>
    let a := rgetV st n i
    let s := DyadicInterval.sqrt p a.1
    let r := invT p (smulNat 2 s)
    (s, a.2.map fun u ↦ DyadicInterval.mul p u r)
  | .sin i =>
    let a := rgetV st n i
    let c := DyadicInterval.cos p a.1
    (DyadicInterval.sin p a.1, a.2.map fun u ↦ DyadicInterval.mul p c u)
  | .cos i =>
    let a := rgetV st n i
    let s := DyadicInterval.sin p a.1
    (DyadicInterval.cos p a.1, a.2.map fun u ↦ DyadicInterval.neg (DyadicInterval.mul p s u))
  | .arctan i =>
    let a := rgetV st n i
    let r := invT p (DyadicInterval.add (one p) (DyadicInterval.sq p a.1))
    (DyadicInterval.arctan p a.1, a.2.map fun u ↦ DyadicInterval.mul p u r)

/-- The domain conditions of an instruction for the derivatives. -/
def Op.okV (p : ℕ) (st : List DualV) (n : ℕ) : Op → Bool
  | .div _ j => nz (rgetV st n j).1
  | .sqrt i => nz (smulNat 2 (DyadicInterval.sqrt p (rgetV st n i).1))
  | .arctan i => nz (DyadicInterval.add (one p) (DyadicInterval.sq p (rgetV st n i).1))
  | _ => true

/-- Run the instructions `ops`, the first at position `n`, with derivatives. -/
def runV (p m : ℕ) (env : List DyadicInterval) (denv : List (List DyadicInterval)) :
    List Op → List DualV → ℕ → Bool → List DualV × Bool
  | [], st, _, ok => (st, ok)
  | op :: ops, st, n, ok =>
    runV p m env denv ops (op.valV p m env denv st n :: st) (n + 1) (op.okV p st n && ok)

/-- The interval values and derivatives of a program: the results, the last first, and the domain
flag. -/
def evalV (p m : ℕ) (env : List DyadicInterval) (denv : List (List DyadicInterval))
    (prog : List Op) : List DualV × Bool :=
  runV p m env denv prog [] 0 true

/-- The enclosure of the value and derivatives of the result `i` of a program of length `n`. -/
def resV (st : List DualV) (n i : ℕ) : DualV := nth st (n - 1 - i) (zero, [])

/-- The facts on one entry: the value (`l` the real results at the base point), `m` derivatives,
and the derivative of the entry `i` along the curve `j` (the real results `L j s`) at `s₀ j`. -/
def DFact (p m : ℕ) (L : ℕ → ℝ → List ℝ) (s₀ : ℕ → ℝ) (l : List ℝ) (a : DualV) (i : ℕ) : Prop :=
  Mem p a.1 (getR l i) ∧ a.2.length = m ∧
    ∀ j < m, ∃ d, HasDerivAt (fun s ↦ getR (L j s) i) d (s₀ j) ∧ Mem p (nth a.2 j zero) d

/-- The invariant of the store along `m` curves of real results `L j` through `l` at `s₀`. -/
def VEncl (p m : ℕ) (L : ℕ → ℝ → List ℝ) (s₀ : ℕ → ℝ) (l : List ℝ) (st : List DualV) : Prop :=
  st.length = l.length ∧ (∀ j s, (L j s).length = l.length) ∧ (∀ j < m, L j (s₀ j) = l) ∧
    ∀ i < l.length, DFact p m L s₀ l (nth st (l.length - 1 - i) (zero, [])) i

theorem hasDerivAt_getR_append {L : ℝ → List ℝ} {n i : ℕ} (hL : ∀ s, (L s).length = n)
    (hi : i < n) (f : ℝ → ℝ) {d s₀ : ℝ} (h : HasDerivAt (fun s ↦ getR (L s) i) d s₀) :
    HasDerivAt (fun s ↦ getR (L s ++ [f s]) i) d s₀ := by
  have e : (fun s ↦ getR (L s ++ [f s]) i) = fun s ↦ getR (L s) i := by
    funext s; exact getR_append_lt _ (by rw [hL s]; exact hi)
  rw [e]; exact h

theorem getR_append_length' {l : List ℝ} {n : ℕ} (h : l.length = n) (a : ℝ) :
    getR (l ++ [a]) n = a := by
  rw [getR, ← h, lookup_append_length, Option.getD_some]

theorem VEncl.cons {p m : ℕ} {L : ℕ → ℝ → List ℝ} {s₀ : ℕ → ℝ} {l : List ℝ} {st : List DualV}
    (h : VEncl p m L s₀ l st) (F : ℕ → ℝ → ℝ) {a : ℝ} {A : DualV} (hA : Mem p A.1 a)
    (hF : ∀ j < m, F j (s₀ j) = a) (hAl : A.2.length = m)
    (hAd : ∀ j < m, ∃ d, HasDerivAt (F j) d (s₀ j) ∧ Mem p (nth A.2 j zero) d) :
    VEncl p m (fun j s ↦ L j s ++ [F j s]) s₀ (l ++ [a]) (A :: st) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by simp [h1], fun j s ↦ by simp [h2 j s], fun j hj ↦ ?_, fun i hi ↦ ?_⟩
  · change L j (s₀ j) ++ [F j (s₀ j)] = l ++ [a]
    rw [h3 j hj, hF j hj]
  simp only [List.length_append, List.length_singleton] at hi ⊢
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
  · have e : l.length + 1 - 1 - i = (l.length - 1 - i) + 1 := by omega
    rw [e, nth_cons_succ]
    obtain ⟨v1, v2, v3⟩ := h4 i hi
    refine ⟨by rw [getR_append_lt _ hi]; exact v1, v2, fun j hj ↦ ?_⟩
    obtain ⟨d, hd, hm⟩ := v3 j hj
    exact ⟨d, hasDerivAt_getR_append (h2 j) hi _ hd, hm⟩
  · rw [show l.length + 1 - 1 - l.length = 0 by omega, nth_cons_zero]
    refine ⟨by rw [getR_append_length' rfl]; exact hA, hAl, fun j hj ↦ ?_⟩
    obtain ⟨d, hd, hm⟩ := hAd j hj
    refine ⟨d, ?_, hm⟩
    have e : (fun s ↦ getR (L j s ++ [F j s]) l.length) = F j := by
      funext s; exact getR_append_length' (h2 j s) _
    rw [e]; exact hd

/-- The facts on the operand `i` of an instruction: the value and, along each curve `j`, the
derivative, with the value of the curve at `s₀`. -/
theorem VEncl.operand {p m : ℕ} {L : ℕ → ℝ → List ℝ} {s₀ : ℕ → ℝ} {l : List ℝ}
    {st : List DualV}
    (h : VEncl p m L s₀ l st) {i : ℕ} (hi : i < l.length) :
    Mem p (rgetV st l.length i).1 (getR l i) ∧ (rgetV st l.length i).2.length = m ∧
      ∀ j < m, getR (L j (s₀ j)) i = getR l i ∧
        ∃ d, HasDerivAt (fun s ↦ getR (L j s) i) d (s₀ j) ∧
          Mem p (nth (rgetV st l.length i).2 j zero) d := by
  obtain ⟨v1, v2, v3⟩ := h.2.2.2 i hi
  exact ⟨v1, v2, fun j hj ↦ ⟨by rw [h.2.2.1 j hj], v3 j hj⟩⟩

/-- The facts on the result of an instruction. -/
def VResult (p m : ℕ) (L : ℕ → ℝ → List ℝ) (γ : ℕ → ℝ → ℕ → ℝ) (s₀ : ℕ → ℝ) (a : ℝ) (op : Op)
    (A : DualV) : Prop :=
  Mem p A.1 a ∧ A.2.length = m ∧
    ∀ j < m, ∃ d, HasDerivAt (fun s ↦ op.evalR (γ j s) (L j s)) d (s₀ j) ∧
      Mem p (nth A.2 j zero) d

/-- A unary operation with a derivative rule. -/
theorem vresult_unary {p m : ℕ} {L : ℕ → ℝ → List ℝ} {γ : ℕ → ℝ → ℕ → ℝ} {s₀ : ℕ → ℝ}
    {l : List ℝ} {st : List DualV} (h : VEncl p m L s₀ l st) {i : ℕ} (hi : i < l.length)
    (op : Op) (f : ℝ → ℝ) (hop : ∀ x v, op.evalR x v = f (getR v i)) {V : DyadicInterval}
    (G : DyadicInterval → DyadicInterval) (hV : Mem p V (f (getR l i)))
    (hder : ∀ j < m, ∀ d, HasDerivAt (fun s ↦ getR (L j s) i) d (s₀ j) → ∀ U, Mem p U d →
      ∃ e, HasDerivAt (fun s ↦ f (getR (L j s) i)) e (s₀ j) ∧ Mem p (G U) e) :
    VResult p m L γ s₀ (f (getR l i)) op (V, (rgetV st l.length i).2.map G) := by
  obtain ⟨-, hl, hd⟩ := h.operand hi
  refine ⟨hV, by simp [hl], fun j hj ↦ ?_⟩
  obtain ⟨-, d, hd1, hd2⟩ := hd j hj
  obtain ⟨e, he1, he2⟩ := hder j hj d hd1 _ hd2
  refine ⟨e, ?_, ?_⟩
  · simp only [hop]; exact he1
  · rw [nth_map G (by rw [hl]; exact hj) zero zero]; exact he2

/-- A binary operation with a derivative rule. -/
theorem vresult_binary {p m : ℕ} {L : ℕ → ℝ → List ℝ} {γ : ℕ → ℝ → ℕ → ℝ} {s₀ : ℕ → ℝ}
    {l : List ℝ} {st : List DualV} (h : VEncl p m L s₀ l st) {i k : ℕ} (hi : i < l.length)
    (hk : k < l.length) (op : Op) (f : ℝ → ℝ → ℝ) (hop : ∀ x v, op.evalR x v = f (getR v i)
      (getR v k)) {V : DyadicInterval} (G : DyadicInterval → DyadicInterval → DyadicInterval)
    (hV : Mem p V (f (getR l i) (getR l k)))
    (hder : ∀ j < m, ∀ d d', HasDerivAt (fun s ↦ getR (L j s) i) d (s₀ j) →
      HasDerivAt (fun s ↦ getR (L j s) k) d' (s₀ j) → ∀ U U', Mem p U d → Mem p U' d' →
      ∃ e, HasDerivAt (fun s ↦ f (getR (L j s) i) (getR (L j s) k)) e (s₀ j) ∧
        Mem p (G U U') e) :
    VResult p m L γ s₀ (f (getR l i) (getR l k)) op
      (V, List.zipWith G (rgetV st l.length i).2 (rgetV st l.length k).2) := by
  obtain ⟨-, hl, hd⟩ := h.operand hi
  obtain ⟨-, hl', hd'⟩ := h.operand hk
  refine ⟨hV, by simp [hl, hl'], fun j hj ↦ ?_⟩
  obtain ⟨-, d, hd1, hd2⟩ := hd j hj
  obtain ⟨-, d', hd1', hd2'⟩ := hd' j hj
  obtain ⟨e, he1, he2⟩ := hder j hj d d' hd1 hd1' _ _ hd2 hd2'
  refine ⟨e, ?_, ?_⟩
  · simp only [hop]; exact he1
  · rw [nth_zipWith G (by rw [hl]; exact hj) (by rw [hl']; exact hj) zero zero zero]; exact he2

/-- The derivative of one instruction along the curves. -/
theorem Op.valV_sound {p m : ℕ} {env : List DyadicInterval} {denv : List (List DyadicInterval)}
    {γ : ℕ → ℝ → ℕ → ℝ} {γ' : ℕ → ℕ → ℝ} {s₀ : ℕ → ℝ} {x : ℕ → ℝ}
    (hγ : ∀ j < m, ∀ k, HasDerivAt (fun s ↦ γ j s k) (γ' j k) (s₀ j))
    (henv : ∀ k, Mem p (nth env k zero) (x k))
    (hdenv : ∀ k, (nth denv k (zeros m)).length = m ∧
      ∀ j < m, Mem p (nth (nth denv k (zeros m)) j zero) (γ' j k))
    {L : ℕ → ℝ → List ℝ} {l : List ℝ} {st : List DualV} (h : VEncl p m L s₀ l st) (op : Op)
    (hargs : ∀ j ∈ op.args, j < l.length) (hok : op.okV p st l.length = true) :
    VResult p m L γ s₀ (op.evalR x l) op (op.valV p m env denv st l.length) := by
  have val : ∀ {i}, i < l.length → ∀ j < m, getR (L j (s₀ j)) i = getR l i :=
    fun hi j hj ↦ ((h.operand hi).2.2 j hj).1
  have hz : ∀ j < m, nth (zeros m) j zero = zero := fun j hj ↦ nth_replicate hj _ _
  cases op with
  | var k => exact ⟨henv k, (hdenv k).1, fun j hj ↦ ⟨γ' j k, hγ j hj k, (hdenv k).2 j hj⟩⟩
  | const q =>
    refine ⟨mem_ofRat p q, List.length_replicate .., fun j hj ↦ ⟨0, hasDerivAt_const _ _, ?_⟩⟩
    exact (hz j hj).symm ▸ mem_zero p
  | pi =>
    refine ⟨mem_pi p, List.length_replicate .., fun j hj ↦ ⟨0, hasDerivAt_const _ _, ?_⟩⟩
    exact (hz j hj).symm ▸ mem_zero p
  | add i k =>
    have hi := hargs i (by simp [Op.args])
    have hk := hargs k (by simp [Op.args])
    exact vresult_binary h hi hk _ (· + ·) (fun _ _ ↦ rfl) _
      (mem_add (h.operand hi).1 (h.operand hk).1)
      fun j hj d d' hd hd' U U' hU hU' ↦ ⟨_, hd.add hd', mem_add hU hU'⟩
  | sub i k =>
    have hi := hargs i (by simp [Op.args])
    have hk := hargs k (by simp [Op.args])
    exact vresult_binary h hi hk _ (· - ·) (fun _ _ ↦ rfl) _
      (mem_sub (h.operand hi).1 (h.operand hk).1)
      fun j hj d d' hd hd' U U' hU hU' ↦ ⟨_, hd.sub hd', mem_sub hU hU'⟩
  | mul i k =>
    have hi := hargs i (by simp [Op.args])
    have hk := hargs k (by simp [Op.args])
    refine vresult_binary h hi hk _ (· * ·) (fun _ _ ↦ rfl) _
      (mem_mul (h.operand hi).1 (h.operand hk).1)
      fun j hj d d' hd hd' U U' hU hU' ↦ ?_
    have e := hd.mul hd'
    simp only [val hi j hj, val hk j hj] at e
    exact ⟨_, e, mem_add (mem_mul hU (h.operand hk).1) (mem_mul (h.operand hi).1 hU')⟩
  | div i k =>
    have hi := hargs i (by simp [Op.args])
    have hk := hargs k (by simp [Op.args])
    have hq := mem_divT hok (h.operand hi).1 (h.operand hk).1
    refine vresult_binary h hi hk _ (· / ·) (fun _ _ ↦ rfl) _ hq
      fun j hj d d' hd hd' U U' hU hU' ↦ ?_
    have hne : getR (L j (s₀ j)) k ≠ 0 := by
      rw [val hk j hj]; exact ne_zero_of_nz hok (h.operand hk).1
    have e := hd.div hd' hne
    simp only [val hi j hj, val hk j hj] at e hne
    refine ⟨_, e, ?_⟩
    have e2 : (d * getR l k - getR l i * d') / getR l k ^ 2 =
        (d - getR l i / getR l k * d') * (getR l k)⁻¹ := by
      field_simp
    rw [e2]
    exact mem_mul (mem_sub hU (mem_mul hq hU')) (mem_invT hok (h.operand hk).1)
  | neg i =>
    have hi := hargs i (by simp [Op.args])
    exact vresult_unary h hi _ (fun a ↦ -a) (fun _ _ ↦ rfl) _ (mem_neg (h.operand hi).1)
      fun j hj d hd U hU ↦ ⟨_, hd.neg, mem_neg hU⟩
  | sq i =>
    have hi := hargs i (by simp [Op.args])
    refine vresult_unary h hi _ (fun a ↦ a ^ 2) (fun _ _ ↦ rfl) _ (mem_sq (h.operand hi).1)
      fun j hj d hd U hU ↦ ?_
    have e := hd.pow 2
    simp only [val hi j hj] at e
    refine ⟨_, e, ?_⟩
    have e2 : ((2 : ℕ) : ℝ) * getR l i ^ (2 - 1) * d = (2 : ℕ) * (getR l i * d) := by ring
    rw [e2]
    exact mem_smulNat 2 (mem_mul (h.operand hi).1 hU)
  | sqrt i =>
    have hi := hargs i (by simp [Op.args])
    have hs := mem_sqrt (h.operand hi).1
    have h2s := mem_smulNat 2 hs
    refine vresult_unary h hi _ (fun a ↦ Real.sqrt a) (fun _ _ ↦ rfl) _ hs
      fun j hj d hd U hU ↦ ?_
    have hne : getR (L j (s₀ j)) i ≠ 0 := by
      rw [val hi j hj]
      intro h0
      have := ne_zero_of_nz hok h2s
      rw [h0, Real.sqrt_zero, mul_zero] at this
      exact this rfl
    have e := hd.sqrt hne
    simp only [val hi j hj] at e
    refine ⟨_, e, ?_⟩
    have e2 : d / (2 * Real.sqrt (getR l i)) = d * (((2 : ℕ) : ℝ) * Real.sqrt (getR l i))⁻¹ := by
      push_cast; rw [div_eq_mul_inv]
    rw [e2]
    exact mem_mul hU (mem_invT hok h2s)
  | sin i =>
    have hi := hargs i (by simp [Op.args])
    refine vresult_unary h hi _ (fun a ↦ Real.sin a) (fun _ _ ↦ rfl) _ (mem_sin (h.operand hi).1)
      fun j hj d hd U hU ↦ ?_
    have e := hd.sin
    simp only [val hi j hj] at e
    exact ⟨_, e, mem_mul (mem_cos (h.operand hi).1) hU⟩
  | cos i =>
    have hi := hargs i (by simp [Op.args])
    refine vresult_unary h hi _ (fun a ↦ Real.cos a) (fun _ _ ↦ rfl) _ (mem_cos (h.operand hi).1)
      fun j hj d hd U hU ↦ ?_
    have e := hd.cos
    simp only [val hi j hj] at e
    refine ⟨_, e, ?_⟩
    rw [neg_mul]
    exact mem_neg (mem_mul (mem_sin (h.operand hi).1) hU)
  | arctan i =>
    have hi := hargs i (by simp [Op.args])
    refine vresult_unary h hi _ (fun a ↦ Real.arctan a) (fun _ _ ↦ rfl) _
      (mem_arctan (h.operand hi).1) fun j hj d hd U hU ↦ ?_
    have e := hd.arctan
    simp only [val hi j hj] at e
    refine ⟨_, e, ?_⟩
    have e2 : 1 / (1 + getR l i ^ 2) * d = d * (1 + getR l i ^ 2)⁻¹ := by ring
    rw [e2]
    exact mem_mul hU (mem_invT hok (mem_add (mem_one p) (mem_sq (h.operand hi).1)))

theorem runV_ok {p m : ℕ} {env : List DyadicInterval} {denv : List (List DyadicInterval)} :
    ∀ (ops : List Op) (st : List DualV) (n : ℕ) (ok : Bool),
      (runV p m env denv ops st n ok).2 = true → ok = true
  | [], _, _, _, h => h
  | op :: ops, st, n, ok, h => by
    have := runV_ok ops _ _ _ h
    simp only [Bool.and_eq_true] at this
    exact this.2

theorem runV_sound {p m : ℕ} {env : List DyadicInterval} {denv : List (List DyadicInterval)}
    {γ : ℕ → ℝ → ℕ → ℝ} {γ' : ℕ → ℕ → ℝ} {s₀ : ℕ → ℝ} {x : ℕ → ℝ}
    (hx : ∀ j < m, γ j (s₀ j) = x)
    (hγ : ∀ j < m, ∀ k, HasDerivAt (fun s ↦ γ j s k) (γ' j k) (s₀ j))
    (henv : ∀ k, Mem p (nth env k zero) (x k))
    (hdenv : ∀ k, (nth denv k (zeros m)).length = m ∧
      ∀ j < m, Mem p (nth (nth denv k (zeros m)) j zero) (γ' j k)) :
    ∀ (ops : List Op) (L : ℕ → ℝ → List ℝ) (l : List ℝ) (st : List DualV) (ok : Bool),
      wfFrom l.length ops = true → VEncl p m L s₀ l st →
      (runV p m env denv ops st l.length ok).2 = true →
      VEncl p m (fun j s ↦ ops.foldl (stepR (γ j s)) (L j s)) s₀ (ops.foldl (stepR x) l)
        (runV p m env denv ops st l.length ok).1
  | [], _, _, _, _, _, h, _ => h
  | op :: ops, L, l, st, ok, hwf, h, hok => by
    obtain ⟨hargs, hwf'⟩ := wfFrom_cons hwf
    have hok' := runV_ok ops _ _ _ hok
    simp only [Bool.and_eq_true] at hok'
    obtain ⟨r1, r2, r3⟩ := Op.valV_sound hγ henv hdenv h op hargs hok'.1
    have hF : ∀ j < m, op.evalR (γ j (s₀ j)) (L j (s₀ j)) = op.evalR x l := by
      intro j hj; rw [hx j hj, h.2.2.1 j hj]
    have h1 := h.cons (fun j s ↦ op.evalR (γ j s) (L j s)) r1 hF r2 r3
    have hlen : (l ++ [op.evalR x l]).length = l.length + 1 := by simp
    have := runV_sound hx hγ henv hdenv ops _ (l ++ [op.evalR x l]) _ (op.okV p st l.length && ok)
      (hlen ▸ hwf') h1 (hlen ▸ hok)
    rw [hlen] at this
    exact this

/-- **Soundness of the vector-mode differentiation**: for a well-formed program, `m` curves
`s ↦ γ j s` of inputs through `x` at `s₀ j` with derivatives `γ' j` enclosed by `denv`, inputs `x`
enclosed by `env` and a `true` domain flag, the entry `i` of the results encloses the value of the
result `i` at `x` and, for `j < m`, its derivative at `s₀ j` along the curve `j`. -/
theorem evalV_sound {p m : ℕ} {env : List DyadicInterval} {denv : List (List DyadicInterval)}
    {γ : ℕ → ℝ → ℕ → ℝ} {γ' : ℕ → ℕ → ℝ} {s₀ : ℕ → ℝ} {x : ℕ → ℝ}
    (hx : ∀ j < m, γ j (s₀ j) = x)
    (hγ : ∀ j < m, ∀ k, HasDerivAt (fun s ↦ γ j s k) (γ' j k) (s₀ j))
    (henv : ∀ k, Mem p (nth env k zero) (x k))
    (hdenv : ∀ k, (nth denv k (zeros m)).length = m ∧
      ∀ j < m, Mem p (nth (nth denv k (zeros m)) j zero) (γ' j k))
    {prog : List Op} (hwf : wfFrom 0 prog = true) (hok : (evalV p m env denv prog).2 = true) :
    ∀ i < prog.length,
      Mem p (resV (evalV p m env denv prog).1 prog.length i).1 (getR (evalR x prog) i) ∧
      (resV (evalV p m env denv prog).1 prog.length i).2.length = m ∧
      ∀ j < m, ∃ d, HasDerivAt (fun s ↦ getR (evalR (γ j s) prog) i) d (s₀ j) ∧
        Mem p (nth (resV (evalV p m env denv prog).1 prog.length i).2 j zero) d := by
  have h0 : VEncl p m (fun _ _ ↦ []) s₀ [] [] :=
    ⟨rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun i hi ↦ by simp at hi⟩
  have h := runV_sound hx hγ henv hdenv prog _ [] [] true hwf h0 hok
  intro i hi
  have hl : (evalR x prog).length = prog.length := length_evalR x prog
  obtain ⟨v1, v2, v3⟩ := h.2.2.2 i (by rw [← evalR_eq_foldl, hl]; exact hi)
  rw [← evalR_eq_foldl, hl] at v1 v2 v3
  exact ⟨v1, v2, v3⟩

/-- The unit vectors `e_k` of `ℝᵐ` (`k < n`) as derivative seeds: the input `k` moves along the
direction `k`. -/
def seedV (p n m : ℕ) : List (List DyadicInterval) :=
  (List.range n).map fun k ↦ (List.range m).map fun j ↦ if j = k then one p else zero

theorem nth_range_map {α : Type*} (f : ℕ → α) {n k : ℕ} (h : k < n) (d : α) :
    nth ((List.range n).map f) k d = f k := by
  rw [nth_map f (by simpa using h) 0 d]
  congr 1
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · have e : ∀ (l : List ℕ) (a : ℕ) (i : ℕ), i < l.length → nth (l ++ [a]) i 0 = nth l i 0 := by
        intro l a i hi
        induction l generalizing i with
        | nil => simp at hi
        | cons b l ih' => cases i <;> simp_all [nth]
      rw [e _ _ _ (by simpa using h), ih h]
    · have e : ∀ (l : List ℕ) (a : ℕ), nth (l ++ [a]) l.length 0 = a := by
        intro l a
        induction l with
        | nil => rfl
        | cons b l ih' => simpa [nth] using ih'
      have := e (List.range k) k
      rwa [List.length_range] at this

/-- **Partial derivatives in vector mode**: with the seeds `seedV p n m` (`n` inputs, the first
`m` of them moved), the entry `i` encloses the value of the result `i` at `x` and, for `j < m`,
its derivative in the input `j`. -/
theorem hasDerivAt_update_of_evalV {p n m : ℕ} {env : List DyadicInterval} {x : ℕ → ℝ}
    (hmn : m ≤ n) (henv : ∀ k, Mem p (nth env k zero) (x k)) {prog : List Op}
    (hwf : wfFrom 0 prog = true)
    (hok : (evalV p m env (seedV p n m) prog).2 = true) :
    ∀ i < prog.length,
      Mem p (resV (evalV p m env (seedV p n m) prog).1 prog.length i).1
        (getR (evalR x prog) i) ∧
      (resV (evalV p m env (seedV p n m) prog).1 prog.length i).2.length = m ∧
      ∀ j < m, ∃ d, HasDerivAt (fun s ↦ getR (evalR (Function.update x j s) prog) i) d (x j) ∧
        Mem p (nth (resV (evalV p m env (seedV p n m) prog).1 prog.length i).2 j zero) d := by
  have hγ : ∀ j < m, ∀ k, HasDerivAt (fun s ↦ Function.update x j s k)
      (if k = j then 1 else 0) (x j) := by
    intro j _ k
    by_cases hk : k = j
    · subst hk
      simp only [Function.update_self, ite_true]
      exact hasDerivAt_id _
    · simp only [Function.update_of_ne hk, ite_eq_right hk]
      exact hasDerivAt_const _ _
  refine evalV_sound (γ := fun j s ↦ Function.update x j s) (s₀ := fun j ↦ x j)
    (fun j _ ↦ Function.update_eq_self _ _) hγ henv (fun k ↦ ?_) hwf hok
  by_cases hk : k < n
  · rw [seedV, nth_range_map _ hk]
    refine ⟨by simp, fun j hj ↦ ?_⟩
    rw [nth_range_map _ hj]
    by_cases hjk : j = k
    · subst hjk; simp only [ite_true]; exact mem_one p
    · simp only [hjk, ite_false, Ne.symm hjk]; exact mem_zero p
  · have hnil : nth (seedV p n m) k (zeros m) = zeros m := by
      have e : ∀ (l : List (List DyadicInterval)) (i : ℕ), l.length ≤ i →
          nth l i (zeros m) = zeros m := by
        intro l i hi
        induction l generalizing i with
        | nil => rfl
        | cons b l ih' => cases i <;> simp_all [nth]
      exact e _ _ (by simp [seedV]; omega)
    rw [hnil]
    refine ⟨by simp [zeros], fun j hj ↦ ?_⟩
    rw [zeros, nth_replicate hj, ite_eq_right (by omega)]
    exact mem_zero p

end DyadicInterval
