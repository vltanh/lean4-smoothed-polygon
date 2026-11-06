module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Algebra.Order.Round
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Critical lattices in the plane

Mahler's compactness theorem (Mahler 1946; see Cassels, *An Introduction to the Geometry of
Numbers*, V.4), in the plane and in the form of the existence of critical lattices. Let `U ⊆ ℝ²`
be an open set containing the origin, and call a lattice `L ⊆ ℝ²` `U`-admissible if `0` is its
only point in `U`. If some lattice is `U`-admissible, then among the `U`-admissible lattices there
is one of least covolume (`PlaneLattice.exists_admissible_covolume_le`).

The plane is `Fin 2 → ℝ`; the lemmas use the Euclidean quantities `|x|² = x₀² + x₁²`,
`⟨u, v⟩ = u₀ v₀ + u₁ v₁` and `det(u, v) = u₀ v₁ - u₁ v₀` in coordinates.

## Proof

* Reduced bases (`PlaneLattice.exists_reduced_basis`, Lagrange–Gauss): take `u ∈ L` nonzero of
  least `|u|`, and `v ∈ L` of least `|v|` among the lattice points off the line `ℝu` (both exist
  since `L` is discrete and spans the plane). Comparing `v` with `v ± u` gives
  `2|⟨u, v⟩| ≤ |u|²`, and `|u| ≤ |v|`. They form a basis: a point `x = αu + βv` of `L` reduced to
  `|α|, |β| ≤ 1/2` by integer combinations of `u` and `v` would otherwise be a lattice point off
  `ℝu` shorter than `v`, or a nonzero lattice point shorter than `u`. By Lagrange's identity
  `det(u, v)² + ⟨u, v⟩² = |u|²|v|²`, so `det(u, v)² ≥ 3/4 |u|²|v|²`.
* Compactness: a ball `|x|² < r` lies in `U`, so every admissible lattice has `|u|² ≥ r`. Take
  admissible lattices `L_n` with covolumes decreasing to the infimum `d`, and reduced bases
  `u_n, v_n`. Then `|u_n|² ≤ |v_n|² ≤ (4/3) det(L₀)²/r` and `det(u_n, v_n)² ≥ (3/4) r²`, so a
  subsequence of `(u_n, v_n)` converges to some `(u, v)` with `|det(u, v)| = d > 0`.
* The lattice `L = ℤu + ℤv` has covolume `d` and is admissible: if `m u + n v ≠ 0` were in the
  open set `U`, so would be `m u_n + n v_n ≠ 0` for large `n` in the subsequence.
-/

@[expose] public section

namespace PlaneLattice

open Set Filter Topology

/-- The determinant `det(u, v) = u₀ v₁ - u₁ v₀`. -/
private def cr (u v : Fin 2 → ℝ) : ℝ := u 0 * v 1 - u 1 * v 0

/-- The squared Euclidean norm `|x|² = x₀² + x₁²`. -/
private def nsq (x : Fin 2 → ℝ) : ℝ := x 0 ^ 2 + x 1 ^ 2

/-- The Euclidean inner product `⟨u, v⟩ = u₀ v₀ + u₁ v₁`. -/
private def ip (u v : Fin 2 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1

private lemma nsq_nonneg (x : Fin 2 → ℝ) : 0 ≤ nsq x := by
  unfold nsq; positivity

private lemma nsq_pos {x : Fin 2 → ℝ} (hx : x ≠ 0) : 0 < nsq x := by
  unfold nsq
  by_contra h
  apply hx
  ext i
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- Lagrange's identity in the plane. -/
private lemma cr_sq_add_ip_sq (u v : Fin 2 → ℝ) : cr u v ^ 2 + ip u v ^ 2 = nsq u * nsq v := by
  unfold cr ip nsq; ring

private lemma ne_zero_of_cr_ne_zero {u v : Fin 2 → ℝ} (h : cr u v ≠ 0) : v ≠ 0 := by
  rintro rfl; simp [cr] at h

/-- Cramer's rule. -/
private lemma eq_comb {u v : Fin 2 → ℝ} (h : cr u v ≠ 0) (x : Fin 2 → ℝ) :
    x = (cr x v / cr u v) • u + (cr u x / cr u v) • v := by
  ext i
  fin_cases i <;> simp <;> field_simp <;> simp only [cr] <;> ring

/-- The points of `ℤa + ℤb`. -/
lemma mem_span_pair_iff {a b x : Fin 2 → ℝ} :
    x ∈ Submodule.span ℤ {a, b} ↔ ∃ m n : ℤ, (m : ℝ) • a + (n : ℝ) • b = x := by
  rw [Submodule.mem_span_pair]
  simp only [← Int.cast_smul_eq_zsmul ℝ]

private lemma linearIndependent_real {a b : Fin 2 → ℝ} (h : cr a b ≠ 0) :
    LinearIndependent ℝ ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrFun hst 0
  have h1 := congrFun hst 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 h1
  simp only [cr] at h
  constructor
  · have : s * (a 0 * b 1 - a 1 * b 0) = 0 := by linear_combination b 1 * h0 - b 0 * h1
    exact (mul_eq_zero.1 this).resolve_right h
  · have : t * (a 0 * b 1 - a 1 * b 0) = 0 := by linear_combination a 0 * h1 - a 1 * h0
    exact (mul_eq_zero.1 this).resolve_right h

private lemma linearIndependent_int {a b : Fin 2 → ℝ} (h : cr a b ≠ 0) :
    LinearIndependent ℤ ![a, b] :=
  (linearIndependent_real h).restrict_scalars' ℤ

private lemma range_pair (a b : Fin 2 → ℝ) : Set.range ![a, b] = {a, b} := by
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union]

/-- Two independent vectors span a lattice. -/
lemma discreteTopology_span_pair {a b : Fin 2 → ℝ} (h : a 0 * b 1 - a 1 * b 0 ≠ 0) :
    DiscreteTopology (Submodule.span ℤ {a, b}) ∧
      Submodule.span ℝ (Submodule.span ℤ {a, b} : Set (Fin 2 → ℝ)) = ⊤ := by
  have hli := linearIndependent_real (a := a) (b := b) h
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ (Fin 2 → ℝ) := by simp
  let bR : Module.Basis (Fin 2) ℝ (Fin 2 → ℝ) := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbR : Submodule.span ℤ (Set.range bR) = Submodule.span ℤ {a, b} := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank, range_pair]
  rw [← hbR]
  exact ⟨inferInstance, IsZLattice.span_top⟩

/-- The covolume of the lattice `ℤa + ℤb` is `|det(a, b)|`. -/
lemma covolume_span_pair {a b : Fin 2 → ℝ} (h : a 0 * b 1 - a 1 * b 0 ≠ 0) :
    ZLattice.covolume (Submodule.span ℤ {a, b}) = |a 0 * b 1 - a 1 * b 0| := by
  obtain ⟨hd, hs⟩ := discreteTopology_span_pair h
  have : IsZLattice ℝ (Submodule.span ℤ {a, b}) := ⟨hs⟩
  have hli := linearIndependent_int (a := a) (b := b) h
  have heq : Submodule.span ℤ (Set.range ![a, b]) = Submodule.span ℤ {a, b} := by
    rw [range_pair]
  let bas : Module.Basis (Fin 2) ℤ (Submodule.span ℤ {a, b}) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ heq)
  have hb : (Subtype.val ∘ ⇑bas) = ![a, b] := by
    ext i : 1
    simp [bas, Module.Basis.span_apply]
  rw [ZLattice.covolume_eq_det _ bas, hb, Matrix.det_fin_two]
  simp

private lemma isBounded_nsq_le (R : ℝ) : Bornology.IsBounded {x : Fin 2 → ℝ | nsq x ≤ R} := by
  refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := |R| + 1)).subset
    fun x hx ↦ ?_
  simp only [mem_ofPred_eq, nsq] at hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i <;> simp <;>
    nlinarith [sq_abs (x 0), sq_abs (x 1), abs_nonneg (x 0), abs_nonneg (x 1), le_abs_self R,
      abs_nonneg R, sq_nonneg (x 0), sq_nonneg (x 1)]

private lemma continuous_nsq : Continuous nsq := by
  unfold nsq; fun_prop

private lemma isCompact_nsq_le (R : ℝ) : IsCompact {x : Fin 2 → ℝ | nsq x ≤ R} :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_nsq continuous_const)
    (isBounded_nsq_le R)

/-- A discrete set of the plane has finitely many points in a disk. -/
private lemma finite_nsq_le (L : Submodule ℤ (Fin 2 → ℝ)) [DiscreteTopology L] (R : ℝ) :
    {x | x ∈ L ∧ nsq x ≤ R}.Finite := by
  have H : IsClosed (L : Set (Fin 2 → ℝ)) := L.toAddSubgroup.isClosed_of_discreteTopology
  refine (Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete (isBounded_nsq_le R)
    H).subset ?_
  rintro x ⟨hxL, hx⟩
  exact ⟨hx, hxL⟩

/-- Among the points of a discrete submodule `L` with a property `P`, if there is one, some point
has the least `|·|²`. -/
private lemma exists_min_nsq (L : Submodule ℤ (Fin 2 → ℝ)) [DiscreteTopology L]
    (P : (Fin 2 → ℝ) → Prop) {x₀ : Fin 2 → ℝ} (hx₀ : x₀ ∈ L) (hP : P x₀) :
    ∃ u ∈ L, P u ∧ ∀ x ∈ L, P x → nsq u ≤ nsq x := by
  obtain ⟨u, ⟨⟨huL, -⟩, hPu⟩, hmin⟩ := Set.exists_min_image
    ({x | x ∈ L ∧ nsq x ≤ nsq x₀} ∩ {x | P x}) nsq ((finite_nsq_le L _).inter_of_left _)
    ⟨x₀, ⟨hx₀, le_rfl⟩, hP⟩
  refine ⟨u, huL, hPu, fun x hxL hPx ↦ ?_⟩
  rcases le_total (nsq x) (nsq x₀) with h | h
  · exact hmin x ⟨⟨hxL, h⟩, hPx⟩
  · exact (hmin x₀ ⟨⟨hx₀, le_rfl⟩, hP⟩).trans h

/-- **Reduced bases** (Lagrange–Gauss). Every lattice of the plane has a basis `u, v` such that
`u` is a shortest nonzero lattice vector, `|u| ≤ |v|` and `2|⟨u, v⟩| ≤ |u|²`. -/
lemma exists_reduced_basis (L : Submodule ℤ (Fin 2 → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∃ u v : Fin 2 → ℝ, Submodule.span ℤ {u, v} = L ∧ u 0 * v 1 - u 1 * v 0 ≠ 0 ∧
      (∀ x ∈ L, x ≠ 0 → u 0 ^ 2 + u 1 ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2) ∧
      u 0 ^ 2 + u 1 ^ 2 ≤ v 0 ^ 2 + v 1 ^ 2 ∧
      2 * |u 0 * v 0 + u 1 * v 1| ≤ u 0 ^ 2 + u 1 ^ 2 := by
  have hspan : Submodule.span ℝ (L : Set (Fin 2 → ℝ)) = ⊤ := IsZLattice.span_top
  -- a functional vanishing on `L` vanishes
  have hfun : ∀ φ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ, (∀ x ∈ L, φ x = 0) → φ = 0 := by
    intro φ hφ
    have : Submodule.span ℝ (L : Set (Fin 2 → ℝ)) ≤ LinearMap.ker φ :=
      Submodule.span_le.2 fun x hx ↦ hφ x hx
    rw [hspan, top_le_iff, LinearMap.ker_eq_top] at this
    exact this
  -- a nonzero lattice point, and a shortest one `u`
  obtain ⟨x₀, hx₀L, hx₀⟩ : ∃ x ∈ L, x ≠ 0 := by
    by_contra! h
    have h0 := hfun (LinearMap.proj 0) fun x hx ↦ by simp [h x hx]
    have := LinearMap.congr_fun h0 (Pi.single 0 1)
    simp at this
  obtain ⟨u, huL, hu0, humin⟩ := exists_min_nsq L (fun x ↦ x ≠ 0) hx₀L hx₀
  -- a lattice point off the line `ℝu`, and a shortest one `v`
  obtain ⟨x₁, hx₁L, hx₁⟩ : ∃ x ∈ L, cr u x ≠ 0 := by
    by_contra! h
    let φ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := u 0 • LinearMap.proj 1 - u 1 • LinearMap.proj 0
    have h0 := hfun φ fun x hx ↦ by simpa [φ, cr, mul_comm] using h x hx
    have := LinearMap.congr_fun h0 ![-u 1, u 0]
    simp [φ] at this
    exact hu0 (by
      have hpos := nsq_pos hu0
      simp only [nsq] at hpos
      nlinarith)
  obtain ⟨v, hvL, hv0, hvmin⟩ := exists_min_nsq L (fun x ↦ cr u x ≠ 0) hx₁L hx₁
  have hvne : v ≠ 0 := ne_zero_of_cr_ne_zero hv0
  have huv : nsq u ≤ nsq v := humin v hvL hvne
  -- `v ± u` are off the line `ℝu`, so `2|⟨u, v⟩| ≤ |u|²`
  have hp := hvmin (v + u) (L.add_mem hvL huL) (by
    have : cr u (v + u) = cr u v := by simp only [cr, Pi.add_apply]; ring
    rwa [this])
  have hm := hvmin (v - u) (L.sub_mem hvL huL) (by
    have : cr u (v - u) = cr u v := by simp only [cr, Pi.sub_apply]; ring
    rwa [this])
  have hip : 2 * |ip u v| ≤ nsq u := by
    have ep : nsq (v + u) = nsq v + 2 * ip u v + nsq u := by
      simp only [nsq, ip, Pi.add_apply]; ring
    have em : nsq (v - u) = nsq v - 2 * ip u v + nsq u := by
      simp only [nsq, ip, Pi.sub_apply]; ring
    rw [ep] at hp
    rw [em] at hm
    have : |ip u v| ≤ nsq u / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hupos := nsq_pos hu0
  have hvpos := nsq_pos hvne
  refine ⟨u, v, le_antisymm ?_ fun x hxL ↦ ?_, hv0, fun x hx hx0 ↦ humin x hx hx0, huv, hip⟩
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨huL, hvL⟩
  -- reduce `x = α u + β v` to `y = a u + b v` with `|a|, |b| ≤ 1/2`
  set α := cr x v / cr u v
  set β := cr u x / cr u v
  have hx := eq_comb hv0 x
  set a := α - round α with ha
  set b := β - round β with hb
  have ha2 : |a| ≤ 1 / 2 := abs_sub_round α
  have hb2 : |b| ≤ 1 / 2 := abs_sub_round β
  set y := x - (((round α : ℤ) : ℝ) • u + ((round β : ℤ) : ℝ) • v) with hy
  have hyL : y ∈ L := by
    refine L.sub_mem hxL (L.add_mem ?_ ?_)
    · rw [Int.cast_smul_eq_zsmul]; exact L.smul_mem _ huL
    · rw [Int.cast_smul_eq_zsmul]; exact L.smul_mem _ hvL
  have hyab : y = a • u + b • v := by
    rw [hy, ha, hb]
    conv_lhs => rw [hx]
    module
  have hnsq : nsq y = a ^ 2 * nsq u + 2 * (a * b) * ip u v + b ^ 2 * nsq v := by
    rw [hyab]; simp only [nsq, ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hab : |a * b| ≤ 1 / 4 := by
    rw [abs_mul]
    nlinarith [abs_nonneg a, abs_nonneg b]
  have ha2' : a ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs a, abs_nonneg a]
  have hb2' : b ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs b, abs_nonneg b]
  have hmid : 2 * (a * b) * ip u v ≤ nsq u / 4 := by
    have := abs_mul (a * b) (ip u v)
    have h1 : |a * b * ip u v| ≤ 1 / 4 * |ip u v| :=
      by rw [this]; exact mul_le_mul_of_nonneg_right hab (abs_nonneg _)
    have h2 := le_abs_self (a * b * ip u v)
    nlinarith
  -- `b = 0`: otherwise `y` is a lattice point off `ℝu` shorter than `v`
  have hb0 : b = 0 := by
    by_contra hb0
    have hcr : cr u y ≠ 0 := by
      rw [hyab]
      have : cr u (a • u + b • v) = b * cr u v := by
        simp only [cr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]
      exact mul_ne_zero hb0 hv0
    have := hvmin y hyL hcr
    nlinarith [mul_le_mul_of_nonneg_right ha2' hupos.le, mul_le_mul_of_nonneg_right hb2' hvpos.le]
  -- `a = 0`: otherwise `y` is a nonzero lattice point shorter than `u`
  have ha0 : a = 0 := by
    by_contra ha0
    have hy0 : y ≠ 0 := by
      rw [hyab, hb0, zero_smul, add_zero]
      exact smul_ne_zero ha0 hu0
    have := humin y hyL hy0
    rw [hnsq, hb0] at this
    nlinarith [mul_le_mul_of_nonneg_right ha2' hupos.le]
  have hy0 : y = 0 := by rw [hyab, ha0, hb0, zero_smul, zero_smul, add_zero]
  rw [mem_span_pair_iff]
  exact ⟨round α, round β, (sub_eq_zero.1 hy0).symm⟩

/-- **Existence of critical lattices in the plane** (Mahler's compactness theorem). Let `U` be an
open set of the plane containing the origin. If some lattice `L₀` is `U`-admissible (`0` is its
only point in `U`), then some `U`-admissible lattice has the least covolume among the
`U`-admissible lattices. -/
theorem exists_admissible_covolume_le {U : Set (Fin 2 → ℝ)} (hU : IsOpen U)
    (h0 : (0 : Fin 2 → ℝ) ∈ U) {L₀ : Submodule ℤ (Fin 2 → ℝ)} (hL₀d : DiscreteTopology L₀)
    (hL₀s : Submodule.span ℝ (L₀ : Set (Fin 2 → ℝ)) = ⊤) (hL₀ : ∀ x ∈ L₀, x ∈ U → x = 0) :
    ∃ L : Submodule ℤ (Fin 2 → ℝ), DiscreteTopology L ∧
      Submodule.span ℝ (L : Set (Fin 2 → ℝ)) = ⊤ ∧ (∀ x ∈ L, x ∈ U → x = 0) ∧
      ∀ L' : Submodule ℤ (Fin 2 → ℝ), DiscreteTopology L' →
        Submodule.span ℝ (L' : Set (Fin 2 → ℝ)) = ⊤ → (∀ x ∈ L', x ∈ U → x = 0) →
          ZLattice.covolume L ≤ ZLattice.covolume L' := by
  -- a disk `|x|² < r` around the origin lies in `U`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  set r := ε ^ 2 with hr
  have hrpos : 0 < r := by positivity
  have hdisk : ∀ x, nsq x < r → x ∈ U := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hε]
    intro i
    rw [Real.norm_eq_abs]
    simp only [nsq, hr] at hx
    fin_cases i <;> simp <;>
      nlinarith [sq_abs (x 0), sq_abs (x 1), abs_nonneg (x 0), abs_nonneg (x 1), sq_nonneg (x 0),
        sq_nonneg (x 1)]
  -- the covolumes of the admissible lattices, and a minimizing sequence
  set S := {c | ∃ L : Submodule ℤ (Fin 2 → ℝ), DiscreteTopology L ∧
    Submodule.span ℝ (L : Set (Fin 2 → ℝ)) = ⊤ ∧ (∀ x ∈ L, x ∈ U → x = 0) ∧
      ZLattice.covolume L = c} with hSdef
  have hSne : S.Nonempty := ⟨_, L₀, hL₀d, hL₀s, hL₀, rfl⟩
  have hSb : BddBelow S := ⟨0, fun _ ⟨_, _, _, _, hc⟩ ↦ hc ▸ ENNReal.toReal_nonneg⟩
  obtain ⟨c, hc_anti, hc_tend, hcS⟩ := exists_seq_tendsto_sInf hSne hSb
  choose L hLd hLs hLadm hLc using hcS
  have hLz : ∀ n, @IsZLattice ℝ _ _ _ _ (L n) (hLd n) := fun n ↦
    @IsZLattice.mk _ _ _ _ _ _ _ (hLs n)
  choose u v hspan hcr humin huv hip using fun n ↦ @exists_reduced_basis (L n) (hLd n) (hLz n)
  -- bounds on the reduced bases
  have hcn : ∀ n, |cr (u n) (v n)| = c n := by
    intro n
    rw [← hLc n, ← hspan n, covolume_span_pair (hcr n)]
    rfl
  have hur : ∀ n, r ≤ nsq (u n) := by
    intro n
    by_contra h
    push Not at h
    have hu0 : u n ≠ 0 := by
      intro h'
      apply hcr n
      simp [h']
    have huL : u n ∈ L n := hspan n ▸ Submodule.subset_span (by simp)
    exact hu0 (hLadm n _ huL (hdisk _ h))
  have hlag : ∀ n, 3 * (nsq (u n) * nsq (v n)) ≤ 4 * cr (u n) (v n) ^ 2 := by
    intro n
    have h1 := cr_sq_add_ip_sq (u n) (v n)
    have h2 : 4 * ip (u n) (v n) ^ 2 ≤ nsq (u n) ^ 2 := by
      have := hip n
      have h3 := abs_nonneg (ip (u n) (v n))
      have h4 : 2 * |ip (u n) (v n)| ≤ nsq (u n) := this
      nlinarith [sq_abs (ip (u n) (v n))]
    have h5 : nsq (u n) ^ 2 ≤ nsq (u n) * nsq (v n) := by
      rw [sq]; exact mul_le_mul_of_nonneg_left (huv n) (nsq_nonneg _)
    linarith
  set M := 4 * c 0 ^ 2 / (3 * r) with hM
  have hvM : ∀ n, nsq (v n) ≤ M := by
    intro n
    have hc0 : c n ≤ c 0 := hc_anti (Nat.zero_le n)
    have hcn0 : 0 ≤ c n := by rw [← hcn n]; exact abs_nonneg _
    have hsq : cr (u n) (v n) ^ 2 ≤ c 0 ^ 2 := by
      rw [← sq_abs, hcn n]; exact pow_le_pow_left₀ hcn0 hc0 2
    rw [hM, le_div_iff₀ (by positivity)]
    have := hlag n
    have := hur n
    have := nsq_nonneg (v n)
    nlinarith [mul_le_mul_of_nonneg_right (hur n) (nsq_nonneg (v n))]
  have huM : ∀ n, nsq (u n) ≤ M := fun n ↦ (huv n).trans (hvM n)
  have hcr_low : ∀ n, 3 * r ^ 2 ≤ 4 * cr (u n) (v n) ^ 2 := by
    intro n
    have := hlag n
    have h1 := hur n
    have h2 : r ≤ nsq (v n) := h1.trans (huv n)
    nlinarith [mul_le_mul h1 h2 hrpos.le (nsq_nonneg _)]
  -- a convergent subsequence of the bases
  obtain ⟨⟨u', v'⟩, -, φ, hφ, hlim⟩ := (isCompact_nsq_le M).prod (isCompact_nsq_le M)
    |>.tendsto_subseq (x := fun n ↦ (u n, v n)) fun n ↦ ⟨huM n, hvM n⟩
  have hu' : Tendsto (fun n ↦ u (φ n)) atTop (𝓝 u') := (continuous_fst.tendsto _).comp hlim
  have hv' : Tendsto (fun n ↦ v (φ n)) atTop (𝓝 v') := (continuous_snd.tendsto _).comp hlim
  have hcr' : Tendsto (fun n ↦ cr (u (φ n)) (v (φ n))) atTop (𝓝 (cr u' v')) := by
    simp only [cr]
    exact ((tendsto_pi_nhds.1 hu' 0).mul (tendsto_pi_nhds.1 hv' 1)).sub
      ((tendsto_pi_nhds.1 hu' 1).mul (tendsto_pi_nhds.1 hv' 0))
  have hd : |cr u' v'| = sInf S := by
    refine tendsto_nhds_unique (hcr'.abs) ?_
    simp only [hcn]
    exact hc_tend.comp hφ.tendsto_atTop
  have hcr0 : cr u' v' ≠ 0 := by
    have : 3 * r ^ 2 ≤ 4 * cr u' v' ^ 2 :=
      ge_of_tendsto ((hcr'.pow 2).const_mul 4) (Eventually.of_forall fun n ↦ hcr_low (φ n))
    intro h
    rw [h] at this
    nlinarith
  -- the limit lattice
  obtain ⟨hd', hs'⟩ := discreteTopology_span_pair (a := u') (b := v') hcr0
  refine ⟨Submodule.span ℤ {u', v'}, hd', hs', ?_, fun L' hL'd hL's hL' ↦ ?_⟩
  · -- it is admissible: `U` is open
    intro x hx hxU
    obtain ⟨m, n, rfl⟩ := mem_span_pair_iff.1 hx
    have hT : Tendsto (fun k ↦ (m : ℝ) • u (φ k) + (n : ℝ) • v (φ k)) atTop
        (𝓝 ((m : ℝ) • u' + (n : ℝ) • v')) :=
      (hu'.const_smul _).add (hv'.const_smul _)
    obtain ⟨k, hk⟩ := (hT.eventually (hU.mem_nhds hxU)).exists
    have hmem : (m : ℝ) • u (φ k) + (n : ℝ) • v (φ k) ∈ L (φ k) := by
      rw [← hspan (φ k)]
      exact mem_span_pair_iff.2 ⟨m, n, rfl⟩
    have h0k := hLadm (φ k) _ hmem hk
    have hcrk := hcr (φ k)
    have e0 := congrFun h0k 0
    have e1 := congrFun h0k 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e0 e1
    have hm : (m : ℝ) = 0 := by
      have : (m : ℝ) * (u (φ k) 0 * v (φ k) 1 - u (φ k) 1 * v (φ k) 0) = 0 := by
        linear_combination v (φ k) 1 * e0 - v (φ k) 0 * e1
      exact (mul_eq_zero.1 this).resolve_right hcrk
    have hn : (n : ℝ) = 0 := by
      have : (n : ℝ) * (u (φ k) 0 * v (φ k) 1 - u (φ k) 1 * v (φ k) 0) = 0 := by
        linear_combination u (φ k) 0 * e1 - u (φ k) 1 * e0
      exact (mul_eq_zero.1 this).resolve_right hcrk
    rw [hm, hn, zero_smul, zero_smul, add_zero]
  · -- it has the least covolume
    rw [covolume_span_pair hcr0]
    change |cr u' v'| ≤ _
    rw [hd]
    exact csInf_le hSb ⟨L', hL'd, hL's, hL', rfl⟩

end PlaneLattice
