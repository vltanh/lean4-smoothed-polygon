module

public import Basic.Interval.Program

/-!
# The contraction on `B`: programs, certificate data and the Bool-valued check

Data for `SmoothedPolygons/Ch16/Certificates/ContractionBox.lean`: the straight-line programs of
the first switch on the box `B = [0.25, 0.29] × [0.15, 0.19] × [2.85, 2.98]` of cell coordinates
`(r₂, ψ, θ₂)`, the subdivision of `B` into `3 × 3 × 6` boxes with an enclosure `[tl, th]` of the
switching time on each, the bounds `L` on the entries of the Jacobian of the map in coordinates,
and the Bool-valued checks `checkBox`, `checkCenter`, `checkRows` (evaluated by the kernel in
`SmoothedPolygons/Ch16/Certificates/ContractionBoxCheck.lean`; their soundness is in
`SmoothedPolygons/Ch16/Certificates/ContractionBox.lean`). The data were produced by the scripts in
`notes/lp/py/` (`gencert.py`) and are only checked, never trusted.

* `progA` computes, from `(r₂, ψ, θ₂)`, with `r₁ = 1 - r₂`, `φ₁ = θ₂ - ψ + 2π/3` and
  `φ₂ = θ₂ + 2π/3` (the arguments of `ζ z₁`, `ζ z₂` at the cell point), the coefficients
  `x₁ + i y₁ = r₁ e^{iφ₁} = ζ z₁`, `x₂ + i y₂ = r₂ e^{iφ₂} = ζ z₂` and `κ = r₁ r₂ sin ψ`
  (`ζ z₃ = κ - i √3 κ`).
* `progB` computes from them and the time `t` the real and imaginary parts `U_k + i V_k` of
  `ζ z_k(t)` along the constant control `ζ` (`ω = -iζ² = -√3/2 + i/2`), the switching function
  `D = V₂ = Im (ζ z₃(t))` (the control `1` beats `ζ` iff `D > 0`), and the cell coordinates
  `G₀ = 4b/(a + √(a² + 4b))²`, `G₁ = arctan (V₁/U₁) - arctan (V₀/U₀)`, `G₂ = arctan (V₁/U₁) + π`
  of the image, `a = |ζ z₁(t)|`, `b = |ζ z₂(t)|`.
* `progD` computes `D` in Horner form.

On a box `B_k × [tl, th]` the check verifies: `D < 0` on `B_k × [0, tl]`, `D > 0` on
`B_k × {th}`; on each of `nPieces` pieces of `[tl, th]`: `U₀, U₁, U₂ < 0 < V₀, V₁, G₁`, and
enclosures of the partial derivatives of `D`, `G₀`, `G₁`, `G₂` in `(r₂, ψ, θ₂, t)` (forward-mode
differentiation, through `progA` for the cell coordinates); `∂_t D > 0`; and the entries
`∂_j G_i - ∂_t G_i ∂_j D / ∂_t D` of the Jacobian of `g` bounded by `L_{ij}`, with the
derivatives taken anywhere in `B_k × [tl, th]` (hulls over the pieces). At the center `c` of `B`:
a tight enclosure of the switching time and of `g(c)`, with `g(c) ± Σ_j L_{ij} |p_j - c_j| ⊆ B`;
and `Σ_j L_{ij} ≤ 1/2`.
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.ContractionBox

open DyadicInterval

/-- The working precision: endpoints are multiples of `2⁻³⁰`. -/
abbrev prec : ℕ := 30

/-- Inputs `0, 1, 2` = `r₂, ψ, θ₂`. Results `16, 17, 18, 19, 21` = `x₁ = r₁ cos φ₁`,
`y₁ = r₁ sin φ₁`, `x₂ = r₂ cos φ₂`, `y₂ = r₂ sin φ₂`, `κ = r₁ r₂ sin ψ`. -/
def progA : List Op :=
  [.var 0, .var 1, .var 2, .pi, .const (2 / 3), .mul 4 3, .sub 2 1, .add 6 5, .add 2 5,
    .cos 7, .sin 7, .cos 8, .sin 8, .sin 1, .const 1, .sub 14 0, .mul 15 9, .mul 15 10,
    .mul 0 11, .mul 0 12, .mul 15 0, .mul 20 13]

/-- The results of `progA` fed to `progB` as its inputs `0, …, 4`. -/
def aOut : List ℕ := [16, 17, 18, 19, 21]

/-- Inputs `0, …, 5` = `x₁, y₁, x₂, y₂, κ, t`. Results: `13, 15` = `U₀, V₀`; `22, 25` = `U₁, V₁`;
`37, 41` = `U₂, V₂ = D`; `45` = `a`; `49` = `b`; `56` = `G₀`; `61` = `G₁`; `63` = `G₂`. -/
def progB : List Op :=
  [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5,
    .const 3, .sqrt 6, .sq 5, .mul 8 5, .mul 7 5, .const (1 / 2), .mul 11 10, .sub 0 12,
    .mul 11 5, .add 1 14, .mul 0 5, .mul 1 5, .mul 7 8, .const (1 / 4), .mul 19 18, .add 2 16,
    .sub 21 20, .mul 19 8, .add 3 17, .add 24 23, .mul 2 5, .mul 3 5, .mul 11 8, .mul 0 28,
    .mul 1 28, .mul 7 9, .const (1 / 12), .mul 32 31, .mul 32 9, .add 4 26, .add 35 29,
    .sub 36 33, .mul 7 4, .sub 27 38, .add 39 30, .add 40 34,
    .sq 13, .sq 15, .add 42 43, .sqrt 44, .sq 22, .sq 25, .add 46 47, .sqrt 48,
    .const 4, .mul 50 49, .add 44 51, .sqrt 52, .add 45 53, .sq 54, .div 51 55,
    .div 25 22, .arctan 57, .div 15 13, .arctan 59, .sub 58 60, .pi, .add 58 62]

/-- `D = t (y₂ + t (y₁/2 + t/12)) - √3 κ` in Horner form (result `17`), on the inputs of
`progB`. -/
def progD : List Op :=
  [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5,
    .const 3, .sqrt 6, .mul 7 4, .const (1 / 12), .mul 9 5, .const (1 / 2), .mul 11 1,
    .add 12 10, .mul 13 5, .add 3 14, .mul 15 5, .sub 16 8]

/-- The results whose derivatives are bounded: `D`, `G₀`, `G₁`, `G₂`. -/
def outs : List ℕ := [41, 56, 61, 63]

/-- The interval `[a, b]` at the working precision. -/
def ival (a b : ℚ) : DyadicInterval := ⟨(ofRat prec a).lo, (ofRat prec b).hi⟩

/-- The box `B`: lower corner. -/
def bLo : List ℚ := [1 / 4, 3 / 20, 57 / 20]

/-- The box `B`: upper corner. -/
def bHi : List ℚ := [29 / 100, 19 / 100, 149 / 50]

/-- The subdivision of `B`. -/
def nGrid : List ℕ := [3, 3, 6]

/-- The grid points `lo_i + m (hi_i - lo_i)/n_i`. -/
def gridPt (i m : ℕ) : ℚ :=
  bLo.getD i 0 + m * (bHi.getD i 0 - bLo.getD i 0) / (nGrid.getD i 1 : ℚ)

/-- The inputs of `progA` on the box with index `(m₀, m₁, m₂)`. -/
def boxEnv (m₀ m₁ m₂ : ℕ) : List DyadicInterval :=
  [ival (gridPt 0 m₀) (gridPt 0 (m₀ + 1)), ival (gridPt 1 m₁) (gridPt 1 (m₁ + 1)),
    ival (gridPt 2 m₂) (gridPt 2 (m₂ + 1))]

/-- The inputs of `progB`: the results `aOut` of `progA`, and the time interval `T`. -/
def envB (LA : List DyadicInterval) (T : DyadicInterval) : List DyadicInterval :=
  aOut.map (fun i ↦ (lookup LA i).getD zero) ++ [T]

/-- The derivative seeds of `progB` along an input of `progA`: the derivatives of the results
`aOut` of `progA`, and `0` for the time. -/
def denvB (DA : List (DyadicInterval × DyadicInterval)) : List DyadicInterval :=
  aOut.map (fun i ↦ ((lookup DA i).getD (zero, zero)).2) ++ [zero]

/-- The derivative seeds of `progB` in the direction `j` (`0, 1, 2`: the cell coordinates through
`progA`; `3`: the time). -/
def dens (DAs : List (List (DyadicInterval × DyadicInterval))) (j : ℕ) : List DyadicInterval :=
  if j < 3 then denvB (DAs.getD j []) else seed prec 6 5

/-- `D < 0` on the box times `[a, b]`. -/
def negOn (LA : List DyadicInterval) (a b : ℚ) : Bool :=
  match valueAt prec (envB LA (ival a b)) progD 17 with
  | some I => hiNeg I
  | none => false

/-- `D > 0` on the box times `{a}`. -/
def posAt (LA : List DyadicInterval) (a : ℚ) : Bool :=
  match valueAt prec (envB LA (ival a a)) progD 17 with
  | some I => loPos I
  | none => false

/-- The number of pieces of `[tl, th]` for the derivative bounds. -/
def nPieces : ℕ := 3

/-- The pieces of `[tl, th]`. -/
def piece (tl th : ℚ) (m : ℕ) : DyadicInterval :=
  ival (tl + m * (th - tl) / nPieces) (tl + (m + 1) * (th - tl) / nPieces)

/-- The derivative pass of `progB` on one piece, in the direction `j`. -/
def dualB (LA : List DyadicInterval) (DAs : List (List (DyadicInterval × DyadicInterval)))
    (T : DyadicInterval) (j : ℕ) : Option (List (DyadicInterval × DyadicInterval)) :=
  evalDual prec (envB LA T) (dens DAs j) progB

/-- The value of the result `o` on one piece (from the derivative pass in the time direction,
which computes the values too). -/
def pv (LA : List DyadicInterval) (DAs : List (List (DyadicInterval × DyadicInterval)))
    (T : DyadicInterval) (o : ℕ) : Option DyadicInterval :=
  ((dualB LA DAs T 3).bind fun L ↦ lookup L o).map Prod.fst

/-- The value checks on one piece: `U₀, U₁, U₂ < 0 < V₀, V₁, G₁`. -/
def valuesOk (LA : List DyadicInterval) (DAs : List (List (DyadicInterval × DyadicInterval)))
    (T : DyadicInterval) : Bool :=
  (pv LA DAs T 13).any hiNeg && (pv LA DAs T 15).any loPos && (pv LA DAs T 22).any hiNeg &&
    (pv LA DAs T 25).any loPos && (pv LA DAs T 37).any hiNeg && (pv LA DAs T 61).any loPos

/-- The derivative of the result `o` in the direction `j` on one piece. -/
def pd (LA : List DyadicInterval) (DAs : List (List (DyadicInterval × DyadicInterval)))
    (T : DyadicInterval) (j o : ℕ) : Option DyadicInterval :=
  ((dualB LA DAs T j).bind fun L ↦ lookup L o).map Prod.snd

/-- The hull of a list of optional intervals (`none` if one is missing). -/
def hullAll : List (Option DyadicInterval) → Option DyadicInterval
  | [] => none
  | [a] => a
  | a :: l => match a, hullAll l with
    | some I, some J => some (hull I J)
    | _, _ => none

/-- The derivative of the result `o` in the direction `j` on the box times `[tl, th]`. -/
def hd (LA : List DyadicInterval) (DAs : List (List (DyadicInterval × DyadicInterval)))
    (tl th : ℚ) (j o : ℕ) : Option DyadicInterval :=
  hullAll ((List.range nPieces).map fun m ↦ pd LA DAs (piece tl th m) j o)

/-- The entry `(i, j)` of the Jacobian of `g`: `∂_j G_i - ∂_t G_i ∂_j D / ∂_t D`. -/
def combo (LA : List DyadicInterval) (DAs : List (List (DyadicInterval × DyadicInterval)))
    (tl th : ℚ) (i j : ℕ) : Option DyadicInterval :=
  (hd LA DAs tl th j (outs.getD (i + 1) 0)).bind fun Q ↦
    (hd LA DAs tl th 3 (outs.getD (i + 1) 0)).bind fun Qt ↦
      (hd LA DAs tl th j 41).bind fun P ↦
        (hd LA DAs tl th 3 41).bind fun Pt ↦
          (div? prec (DyadicInterval.mul prec Qt P) Pt).map fun R ↦ DyadicInterval.sub Q R

/-- The bounds `L_{ij}` on the entries of the Jacobian. -/
def lBound : List (List ℚ) :=
  [[89 / 1000, 42 / 1000, 48 / 1000], [117 / 1000, 59 / 1000, 75 / 1000],
    [222 / 1000, 124 / 1000, 138 / 1000]]

/-- The certificate of one box: an enclosure `[tl, th]` of the switching time. -/
structure BoxCert where
  /-- the lower end of the enclosure of the switching time -/
  tl : ℚ
  /-- the upper end -/
  th : ℚ

/-- The checks on one box, given the results `LA` of `progA` and its derivatives `DAs`. -/
def checkBoxWith (LA : List DyadicInterval) (DAs : List (List (DyadicInterval × DyadicInterval)))
    (c : BoxCert) : Bool :=
  (decide (0 < c.tl) && decide (c.tl < c.th) && negOn LA 0 c.tl && posAt LA c.th) &&
    ((List.range nPieces).all fun m ↦ valuesOk LA DAs (piece c.tl c.th m)) &&
    (match hd LA DAs c.tl c.th 3 41 with
      | some Pt => loPos Pt
      | none => false) &&
    ([0, 1, 2].all fun i ↦ [0, 1, 2].all fun j ↦
      match combo LA DAs c.tl c.th i j with
      | some I => magLe prec I ((lBound.getD i []).getD j 0)
      | none => false)

/-- The check of one box. -/
def checkBox (m₀ m₁ m₂ : ℕ) (c : BoxCert) : Bool :=
  match evalI prec (boxEnv m₀ m₁ m₂) progA, evalDual prec (boxEnv m₀ m₁ m₂) (seed prec 3 0) progA,
    evalDual prec (boxEnv m₀ m₁ m₂) (seed prec 3 1) progA,
    evalDual prec (boxEnv m₀ m₁ m₂) (seed prec 3 2) progA with
  | some LA, some D₀, some D₁, some D₂ => checkBoxWith LA [D₀, D₁, D₂] c
  | _, _, _, _ => false

set_option maxRecDepth 10000 in
/-- The certificates of the boxes, in the lexicographic order of `(m₀, m₁, m₂)`. -/
def certs : List BoxCert := [
  ⟨2557/512, 20979/4096⟩,
  ⟨326451/65536, 335037/65536⟩,
  ⟨325469/65536, 167135/32768⟩,
  ⟨1267/256, 83341/16384⟩,
  ⟨323099/65536, 332319/65536⟩,
  ⟨20107/4096, 2587/512⟩,
  ⟨327751/65536, 167997/32768⟩,
  ⟨326981/65536, 167721/32768⟩,
  ⟨326073/65536, 10461/2048⟩,
  ⟨162515/32768, 166961/32768⟩,
  ⟨80963/16384, 332953/65536⟩,
  ⟨161269/32768, 331845/65536⟩,
  ⟨10255/2048, 336277/65536⟩,
  ⟨40933/8192, 335801/65536⟩,
  ⟨326631/65536, 167593/32768⟩,
  ⟨162831/32768, 10451/2048⟩,
  ⟨162279/32768, 333539/65536⟩,
  ⟨161659/32768, 332507/65536⟩,
  ⟨81133/16384, 166429/32768⟩,
  ⟨323693/65536, 41529/8192⟩,
  ⟨10085/2048, 331469/65536⟩,
  ⟨321613/65536, 330569/65536⟩,
  ⟨320373/65536, 329533/65536⟩,
  ⟨39875/8192, 41045/8192⟩,
  ⟨40623/8192, 83297/16384⟩,
  ⟨324217/65536, 83159/16384⟩,
  ⟨323317/65536, 331947/65536⟩,
  ⟨161141/32768, 331121/65536⟩,
  ⟨160557/32768, 165079/32768⟩,
  ⟨319813/65536, 329059/65536⟩,
  ⟨325391/65536, 333471/65536⟩,
  ⟨324697/65536, 332993/65536⟩,
  ⟨80967/16384, 166189/32768⟩,
  ⟨161453/32768, 165813/32768⟩,
  ⟨160905/32768, 165369/32768⟩,
  ⟨320581/65536, 20607/4096⟩,
  ⟨80451/16384, 165043/32768⟩,
  ⟨320971/65536, 164731/32768⟩,
  ⟨320005/65536, 164351/32768⟩,
  ⟨79727/16384, 2561/512⟩,
  ⟨19855/4096, 81695/16384⟩,
  ⟨158161/32768, 162809/32768⟩,
  ⟨80563/16384, 330415/65536⟩,
  ⟨321489/65536, 329863/65536⟩,
  ⟨160297/32768, 41147/8192⟩,
  ⟨19973/4096, 164177/32768⟩,
  ⟨318411/65536, 327397/65536⟩,
  ⟨158561/32768, 326307/65536⟩,
  ⟨10083/2048, 82675/16384⟩,
  ⟨80491/16384, 82555/16384⟩,
  ⟨80285/16384, 82401/16384⟩,
  ⟨40023/8192, 328855/65536⟩,
  ⟨319097/65536, 163985/32768⟩,
  ⟨317879/65536, 40869/8192⟩]

/-- The index of the box `(m₀, m₁, m₂)` in `certs`. -/
def boxIndex (m₀ m₁ m₂ : ℕ) : ℕ := (m₀ * nGrid.getD 1 1 + m₁) * nGrid.getD 2 1 + m₂

/-- The center `c` of `B`. -/
def cPt : List ℚ := [27 / 100, 17 / 100, 583 / 200]

/-- The box containing the center. -/
def cBox : ℕ × ℕ × ℕ := (1, 1, 2)

/-- A tight enclosure of the switching time at the center. -/
def cCert : BoxCert := ⟨83768915 / 16777216, 41884475 / 8388608⟩

/-- The half-widths of `B`. -/
def bRad (j : ℕ) : ℚ := (bHi.getD j 0 - bLo.getD j 0) / 2

/-- The bound `Σ_j L_{ij} |p_j - c_j| ≤ Σ_j L_{ij} r_j` on `B`. -/
def spread (i : ℕ) : ℚ := ((List.range 3).map fun j ↦ (lBound.getD i []).getD j 0 * bRad j).sum

/-- The check at the center: `c ∈ B_{cBox}`, `[tl, th]` inside the enclosure of that box, the sign
of `D` at its ends, and `G_i(c) ± Σ_j L_{ij} r_j ⊆ [lo_i, hi_i]`. -/
def checkCenter : Bool :=
  let k := boxIndex cBox.1 cBox.2.1 cBox.2.2
  let ck := certs.getD k ⟨0, 0⟩
  ((List.range 3).all fun j ↦ decide (bLo.getD j 0 + bRad j = cPt.getD j 0)) &&
  decide (gridPt 0 cBox.1 ≤ cPt.getD 0 0 ∧ cPt.getD 0 0 ≤ gridPt 0 (cBox.1 + 1)) &&
  decide (gridPt 1 cBox.2.1 ≤ cPt.getD 1 0 ∧ cPt.getD 1 0 ≤ gridPt 1 (cBox.2.1 + 1)) &&
  decide (gridPt 2 cBox.2.2 ≤ cPt.getD 2 0 ∧ cPt.getD 2 0 ≤ gridPt 2 (cBox.2.2 + 1)) &&
  decide (ck.tl ≤ cCert.tl ∧ cCert.tl < cCert.th ∧ cCert.th ≤ ck.th) &&
  match evalI prec [ival (cPt.getD 0 0) (cPt.getD 0 0), ival (cPt.getD 1 0) (cPt.getD 1 0),
      ival (cPt.getD 2 0) (cPt.getD 2 0)] progA with
  | none => false
  | some LA =>
    negOn LA cCert.tl cCert.tl && posAt LA cCert.th &&
    ([0, 1, 2].all fun i ↦
      match valueAt prec (envB LA (ival cCert.tl cCert.th)) progB (outs.getD (i + 1) 0) with
      | some I => decide (bLo.getD i 0 ≤ (I.lo : ℚ) / 2 ^ prec - spread i ∧
          (I.hi : ℚ) / 2 ^ prec + spread i ≤ bHi.getD i 0)
      | none => false)

/-- The row sums of `L`: `Σ_j L_{ij} ≤ 1/2`. -/
def checkRows : Bool :=
  [0, 1, 2].all fun i ↦
    decide (((List.range 3).map fun j ↦ (lBound.getD i []).getD j 0).sum ≤ 1 / 2)

end SmoothedPolygons.TriFuller.ContractionBox
