module

public import Basic.Interval.Fast

/-!
# `F(𝒟₀₀) ⊆ 𝒟₀₀`: the interval check and its certificate tree

Data for `SmoothedPolygons/Ch16/Certificates/DOutMapsTo.lean` (soundness and the theorem). The box
`𝒟₀₀` of cell coordinates `(r₂, ψ, θ₂) ∈ [0, 1] × [0, π/3] × [π - 1.1, π]` is described by the
rational coordinates `(r₂, a, b)`, `a = tan (ψ/2)`, `b = tan ((π - θ₂)/2)`, which cover it by the
box `[0, 1] × [0, 37/64] × [0, 5/8]` (`root`); all the trigonometric functions of the switching
problem are rational functions of `a`, `b` (`cos ψ = 2/(1 + a²) - 1`, `sin ψ = 2a/(1 + a²)`, the
same for `β = π - θ₂`, and the angle addition formulas), so the check needs no `sin`, `cos` or
`arctan` enclosure.

On a box `X` (`Box3`, endpoints at the precision `2⁻³⁰`) the check `leafOK` computes enclosures
of the coefficients `x₁ + i y₁ = ζ z₁`, `x₂ + i y₂ = ζ z₂`, `κ = r₁ r₂ sin ψ` (`coeffsI`) and,
for a time bracket `[tl, th]`:
* `D(th) > 0`, and `D(tl) < 0` unless `tl = 0`, for the switching cubic
  `D(t) = t (y₂ + t (y₁/2 + t/12)) - √3 κ` (`dI`);
* on `[tl, th]` (halved `d` times): `C₂ < 0` and `C₁ < 0` (`condI`), where
  `C₂ = v₁ + √3 u₁`, `C₁ = U₀ (v₁ - √3 u₁) - V₀ (u₁ + √3 v₁)`, `U₀ + i V₀ = ζ z₁(t)` and
  `(u₁, v₁)` is `ζ z₂(t) = (U₁, V₁)` (`mode = false`) or `(U₁, V₁)/t` computed through
  `D(t) = 0` (`mode = true`, for the boxes near `r₂ = 0`, `θ₂ - ψ = π/3`, where `t → 0`).
The tree `tree` of midpoint splits (`checkTree`) was produced by `notes/cv/py/dout.py`, which uses
the same interval operations; it is only checked, never trusted.
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.DOutMaps

open DyadicInterval

/-- The working precision: endpoints are multiples of `2⁻³⁰`. -/
abbrev prec : ℕ := 30

/-- An enclosure of `√3`. -/
def s3I : DyadicInterval := ⟨1859775393, 1859775394⟩

/-- `(cos (2 arctan a), sin (2 arctan a)) = ((1 - a²)/(1 + a²), 2a/(1 + a²))`. -/
def trigI (A : DyadicInterval) : DyadicInterval × DyadicInterval :=
  let ia := invT prec (add (one prec) (sq prec A))
  (sub (smulNat 2 ia) (one prec), smulNat 2 (mul prec A ia))

/-- Enclosures of the coefficients of the switching problem. -/
structure Coeffs where
  /-- `r₁ = 1 - r₂` -/
  r1 : DyadicInterval
  /-- `sin ψ` -/
  sa : DyadicInterval
  /-- `cos φ₂`, `φ₂ = θ₂ + 2π/3` -/
  c2 : DyadicInterval
  /-- `sin φ₂` -/
  s2 : DyadicInterval
  /-- `x₁ = r₁ cos φ₁`, `φ₁ = θ₂ - ψ + 2π/3` -/
  x1 : DyadicInterval
  /-- `y₁ = r₁ sin φ₁` -/
  y1 : DyadicInterval
  /-- `x₂ = r₂ cos φ₂` -/
  x2 : DyadicInterval
  /-- `y₂ = r₂ sin φ₂` -/
  y2 : DyadicInterval
  /-- `κ = r₁ r₂ sin ψ` -/
  k : DyadicInterval

/-- The coefficients on the box `R × A × B` of `(r₂, a, b)`: with `γ = ψ + β`,
`cos φ₁ = (cos γ - √3 sin γ)/2`, `sin φ₁ = -(√3 cos γ + sin γ)/2`, and the same for `φ₂` with
`β`. -/
def coeffsI (R A B : DyadicInterval) : Coeffs :=
  let ca := (trigI A).1
  let sa := (trigI A).2
  let cb := (trigI B).1
  let sb := (trigI B).2
  let cg := sub (mul prec cb ca) (mul prec sb sa)
  let sg := add (mul prec sb ca) (mul prec cb sa)
  let r1 := sub (one prec) R
  let c1 := divNat (sub cg (mul prec s3I sg)) 2
  let s1 := neg (divNat (add (mul prec s3I cg) sg) 2)
  let c2 := divNat (sub cb (mul prec s3I sb)) 2
  let s2 := neg (divNat (add (mul prec s3I cb) sb) 2)
  ⟨r1, sa, c2, s2, mul prec r1 c1, mul prec r1 s1, mul prec R c2, mul prec R s2,
    mul prec (mul prec r1 R) sa⟩

/-- The switching cubic `D(t) = t (y₂ + t (y₁/2 + t/12)) - √3 κ`. -/
def dI (c : Coeffs) (T : DyadicInterval) : DyadicInterval :=
  sub (mul prec T (add c.y2 (mul prec T (add (divNat c.y1 2) (divNat T 12)))))
    (mul prec s3I c.k)

/-- The conditions `C₁ < 0`, `C₂ < 0` on a time interval `T`. -/
def condI (c : Coeffs) (T : DyadicInterval) (mode : Bool) : Bool :=
  let U0 := sub c.x1 (divNat (mul prec s3I T) 2)
  let V0 := add c.y1 (divNat T 2)
  let den := sub (mul prec (mul prec s3I c.r1) c.sa) (mul prec c.s2 T)
  let TR := mul prec T (divT prec (add (divNat T 12) (divNat c.y1 2)) den)
  let u1 := if mode then add (mul prec TR c.c2) (sub c.x1 (divNat (mul prec s3I T) 4))
    else add c.x2 (mul prec T (sub c.x1 (divNat (mul prec s3I T) 4)))
  let v1 := if mode then add (mul prec TR c.s2) (add c.y1 (divNat T 4))
    else add c.y2 (mul prec T (add c.y1 (divNat T 4)))
  (!mode || nz den) && hiNeg (add v1 (mul prec s3I u1)) &&
    hiNeg (sub (mul prec U0 (sub v1 (mul prec s3I u1))) (mul prec V0 (add u1 (mul prec s3I v1))))

/-- The conditions on `[tl, th]` halved `d` times. -/
def piecesOK (c : Coeffs) (mode : Bool) : ℕ → ℤ → ℤ → Bool
  | 0, tl, th => condI c ⟨tl, th⟩ mode
  | d + 1, tl, th => piecesOK c mode d tl ((tl + th) / 2) && piecesOK c mode d ((tl + th) / 2) th

/-- A box of the coordinates `(r₂, a, b)`. -/
structure Box3 where
  /-- the `r₂`-interval -/
  r : DyadicInterval
  /-- the `a`-interval -/
  a : DyadicInterval
  /-- the `b`-interval -/
  b : DyadicInterval

/-- The check of a leaf box with the bracket `[tl, th]`. -/
def leafOK (X : Box3) (tl th : ℤ) (mode : Bool) (d : ℕ) : Bool :=
  let c := coeffsI X.r X.a X.b
  nz (add (one prec) (sq prec X.a)) && nz (add (one prec) (sq prec X.b)) &&
    decide (0 ≤ tl) && decide (tl ≤ th) && loPos (dI c ⟨th, th⟩) &&
    (decide (tl = 0) || hiNeg (dI c ⟨tl, tl⟩)) && piecesOK c mode d tl th

/-- The lower half of an interval. -/
def lowerHalf (I : DyadicInterval) : DyadicInterval := ⟨I.lo, (I.lo + I.hi) / 2⟩

/-- The upper half of an interval. -/
def upperHalf (I : DyadicInterval) : DyadicInterval := ⟨(I.lo + I.hi) / 2, I.hi⟩

/-- The half of a box below the midpoint of the coordinate `k`. -/
def Box3.lower (X : Box3) : ℕ → Box3
  | 0 => ⟨lowerHalf X.r, X.a, X.b⟩
  | 1 => ⟨X.r, lowerHalf X.a, X.b⟩
  | _ => ⟨X.r, X.a, lowerHalf X.b⟩

/-- The half of a box above the midpoint of the coordinate `k`. -/
def Box3.upper (X : Box3) : ℕ → Box3
  | 0 => ⟨upperHalf X.r, X.a, X.b⟩
  | 1 => ⟨X.r, upperHalf X.a, X.b⟩
  | _ => ⟨X.r, X.a, upperHalf X.b⟩

/-- A certificate: a tree of midpoint splits with a time bracket, a mode and a number of halvings
of the bracket at each leaf. -/
inductive Tree where
  /-- a leaf -/
  | leaf (tl th : ℤ) (mode : Bool) (d : ℕ)
  /-- a split at the midpoint of the coordinate `k` -/
  | node (k : ℕ) (l r : Tree)

/-- The check of a certificate tree on a box. -/
def checkTree : Box3 → Tree → Bool
  | X, .leaf tl th mode d => leafOK X tl th mode d
  | X, .node k l r => checkTree (X.lower k) l && checkTree (X.upper k) r

/-- The root box `[0, 1] × [0, 37/64] × [0, 5/8]`. -/
def root : Box3 := ⟨⟨0, 1073741824⟩, ⟨0, 620756992⟩, ⟨0, 671088640⟩⟩

/-! ### The certificate (generated) -/

/-- The certificate on the box `(((root.lower 0).lower 2).lower 1)` (39 leaves). -/
def tree_0l_2l_1l : Tree :=
  .node 0 (.node 2 (.node 1 (.node 0 (.node 2 (.leaf 4404805632 7256457216 false 2) (.node 1 (.leaf
    4807180288 7223017472 false 1) (.leaf 4815241216 7488995328 false 1))) (.node 2 (.leaf
    4133486592 6663749632 false 1) (.leaf 4173053952 7033012224 true 1))) (.node 0 (.node 2 (.node 1
    (.leaf 4834426880 7445774336 false 1) (.node 0 (.leaf 5112725504 7440973824 false 0) (.leaf
    4944510976 7120175104 false 0))) (.node 1 (.node 0 (.leaf 5057314816 7491092480 false 0) (.leaf
    4895506432 7170785280 false 0)) (.node 0 (.leaf 4856365056 7476838400 false 1) (.leaf 4722819072
    7161610240 false 1)))) (.node 2 (.leaf 4155867136 7214530560 false 2) (.leaf 3990700032
    7375699968 false 2)))) (.node 1 (.node 0 (.node 2 (.node 1 (.leaf 4831444992 7482540032 false 1)
    (.node 0 (.leaf 5046845440 7494778880 false 0) (.leaf 4882382848 7175438336 false 0))) (.node 1
    (.node 0 (.leaf 5083561984 7452377088 false 0) (.leaf 4907712512 7134494720 false 0)) (.node 0
    (.leaf 4821123072 7460044800 false 1) (.leaf 4679811072 7145930752 false 1)))) (.node 2 (.leaf
    4116365312 7248527360 true 1) (.leaf 3974676480 7310901248 false 2))) (.node 0 (.node 2 (.node 1
    (.node 0 (.leaf 4809818112 7490011136 false 1) (.leaf 4677713920 7175241728 false 1)) (.leaf
    4182081536 7485603840 false 1)) (.node 1 (.leaf 4159782912 7464779776 false 1) (.leaf 3742433280
    7217594368 true 1))) (.node 2 (.leaf 3741892608 7382269952 false 2) (.leaf 3429302272 7242563584
    false 2))))) (.node 2 (.node 1 (.node 0 (.leaf 3651239936 6502891520 false 2) (.leaf 3513729024
    5951930368 false 2)) (.node 0 (.leaf 3582820352 6953025536 true 2) (.leaf 3492954112 6320668672
    false 2))) (.node 1 (.node 0 (.leaf 3522772992 7003652096 true 2) (.leaf 3436806144 6384533504
    false 2)) (.node 0 (.node 2 (.leaf 3673505792 6753615872 false 2) (.leaf 3443294208 6646579200
    false 2)) (.leaf 3218243584 6495141888 true 2))))

/-- The certificate on the box `(((root.lower 0).lower 2).upper 1)` (41 leaves). -/
def tree_0l_2l_1u : Tree :=
  .node 0 (.node 2 (.node 1 (.node 0 (.node 2 (.node 1 (.node 0 (.leaf 4954193920 7422328832 false
    0) (.leaf 4808851456 7106641920 false 0)) (.leaf 4404903936 7413743616 false 1)) (.node 1 (.leaf
    4267343872 7467466752 false 1) (.leaf 3941253120 7220707328 false 1))) (.node 2 (.leaf
    3917660160 7289946112 false 2) (.leaf 3581624320 7253016576 false 2))) (.node 0 (.node 2 (.node
    1 (.leaf 4130373632 7181189120 false 1) (.leaf 3815538688 6869991424 false 1)) (.node 1 (.leaf
    3571433472 6885064704 true 1) (.leaf 3173810176 6482886656 true 1))) (.node 2 (.leaf 3523674112
    6963003392 false 2) (.leaf 3075260416 6757941248 false 2)))) (.node 1 (.node 0 (.node 2 (.node 1
    (.leaf 3806855168 7234191360 true 1) (.leaf 3382444032 6884147200 true 1)) (.node 1 (.leaf
    3267870720 6863388672 true 1) (.leaf 2756640768 6424084480 false 2))) (.node 2 (.leaf 3188752384
    7072727040 true 2) (.node 1 (.leaf 3382083584 6400262144 true 1) (.leaf 3046326272 6047432704
    true 1)))) (.node 0 (.node 2 (.node 1 (.leaf 2927083520 6458195968 false 2) (.leaf 2457026560
    5979979776 false 2)) (.node 1 (.leaf 2227732480 5924093952 true 2) (.leaf 1697333248 5388337152
    true 2))) (.node 2 (.leaf 2612264960 6430883840 true 2) (.node 1 (.leaf 2722185216 5648187392
    true 1) (.leaf 2425569280 5224153088 true 1)))))) (.node 2 (.node 1 (.node 0 (.node 2 (.leaf
    3800350720 6658228224 false 1) (.leaf 3571744768 6649905152 false 2)) (.leaf 3350691840
    6362955776 false 2)) (.node 0 (.node 2 (.leaf 3529424896 6405783552 true 1) (.leaf 3221487616
    6263144448 false 2)) (.leaf 3149086720 6133792768 false 2))) (.node 1 (.node 0 (.node 2 (.leaf
    3293986816 6518390784 false 2) (.leaf 2988883968 6276792320 false 2)) (.node 2 (.leaf 3353165824
    6010322944 true 1) (.leaf 3131686912 5830868992 true 1))) (.node 0 (.node 2 (.leaf 2892709888
    6016106496 false 2) (.leaf 2567487488 5682479104 true 2)) (.node 2 (.leaf 3072704512 5634179072
    true 1) (.leaf 2828730368 5385011200 false 2)))))

/-- The certificate on the box `(((root.lower 0).upper 2).lower 1)` (43 leaves). -/
def tree_0l_2u_1l : Tree :=
  .node 0 (.node 2 (.node 1 (.node 0 (.node 2 (.node 1 (.leaf 4562321408 7515914240 false 1) (.leaf
    4202463232 7407091712 false 1)) (.node 1 (.leaf 4303208448 7319666688 false 1) (.leaf 3840049152
    7099940864 false 1))) (.node 2 (.leaf 3763355648 7230996480 false 2) (.leaf 3499589632
    7027425280 false 2))) (.node 0 (.node 2 (.node 1 (.leaf 3754573824 7171211264 true 1) (.leaf
    3239018496 6822002688 false 2)) (.node 1 (.leaf 3297148928 6763003904 false 2) (.leaf 2697150464
    6325977088 false 2))) (.node 2 (.leaf 3075784704 6974046208 true 2) (.node 1 (.leaf 3338715136
    6291996672 false 1) (.leaf 2938224640 5942181888 true 1))))) (.node 1 (.node 0 (.node 2 (.leaf
    3211689984 7307968512 true 2) (.node 1 (.leaf 3631906816 6619512832 false 1) (.leaf 3001892864
    6212927488 false 2))) (.node 2 (.leaf 3200352256 6723338240 false 2) (.leaf 2880978944
    6343344128 false 2))) (.node 0 (.node 2 (.node 1 (.leaf 2809610240 6268305408 false 2) (.leaf
    2139504640 5759090688 true 2)) (.node 1 (.leaf 2310881280 5715329024 false 2) (.node 0 (.leaf
    1697873920 4966219776 true 2) (.leaf 2045820928 4873879552 false 2)))) (.node 2 (.node 1 (.leaf
    2966634496 5872107520 true 1) (.leaf 2545451008 5467111424 false 2)) (.node 1 (.leaf 2594701312
    5402329088 false 2) (.leaf 2176204800 4957569024 false 2)))))) (.node 2 (.node 1 (.node 0 (.node
    2 (.leaf 3648995328 6618349568 true 1) (.leaf 3436281856 6445334528 false 2)) (.leaf 3149135872
    6360678400 false 2)) (.node 0 (.node 2 (.leaf 3176071168 6428590080 false 2) (.leaf 2889596928
    6120128512 false 2)) (.node 2 (.leaf 3240787968 5931188224 true 1) (.leaf 3016720384 5682921472
    false 2)))) (.node 1 (.node 0 (.node 2 (.leaf 3191504896 6185451520 false 2) (.leaf 2927312896
    5859852288 false 2)) (.node 2 (.leaf 3184427008 5697060864 false 1) (.leaf 2964013056 5421809664
    false 1))) (.node 0 (.node 2 (.leaf 2599632896 5744214016 false 2) (.node 1 (.leaf 2763243520
    5118509056 false 1) (.leaf 2474672128 4778508288 false 1))) (.node 2 (.leaf 2781970432
    5376180224 false 2) (.leaf 2546401280 5030133760 false 2)))))

/-- The certificate on the box `(((root.lower 0).upper 2).upper 1)` (81 leaves). -/
def tree_0l_2u_1u : Tree :=
  .node 0 (.node 2 (.node 1 (.node 0 (.node 2 (.node 1 (.leaf 2678030336 6379438080 false 2) (.leaf
    2093252608 5867601920 true 2)) (.node 1 (.leaf 2063810560 5811535872 true 2) (.node 0 (.leaf
    1520844800 5039980544 true 2) (.leaf 2008154112 4968497152 false 2)))) (.node 2 (.node 1 (.leaf
    2965225472 6002130944 true 1) (.leaf 2610823168 5594218496 false 2)) (.node 1 (.leaf 2551152640
    5532745728 false 2) (.leaf 2204467200 5087100928 false 2)))) (.node 0 (.node 2 (.node 1 (.node 0
    (.leaf 1611448320 5101633536 true 2) (.leaf 2098659328 5032148992 false 2)) (.node 0 (.node 2
    (.leaf 1575452672 4311367680 true 1) (.leaf 1173504000 3956047872 true 2)) (.leaf 1733787648
    4502994944 false 2))) (.node 1 (.node 0 (.node 2 (.leaf 1427030016 4206493696 false 2) (.leaf
    1051918336 3855532032 true 2)) (.leaf 1620115456 4424007680 true 2)) (.node 0 (.node 2 (.leaf
    775831552 3600465920 true 2) (.leaf 385269760 3250126848 true 2)) (.leaf 1335230464 3885826048
    true 2)))) (.node 2 (.node 1 (.leaf 2291499008 5156110336 false 2) (.leaf 2019606528 4709990400
    false 2)) (.node 1 (.leaf 1915076608 4629200896 false 2) (.leaf 1686192128 4181278720 false
    2))))) (.node 1 (.node 0 (.node 2 (.node 1 (.node 0 (.leaf 1551482880 4993662976 true 2) (.leaf
    1989689344 4914511872 false 2)) (.node 0 (.node 2 (.leaf 1390673920 4133847040 false 2) (.leaf
    1045250048 3791372288 true 2)) (.leaf 1564934144 4360634368 true 2))) (.node 1 (.node 0 (.node 2
    (.leaf 1465352192 4097589248 false 2) (.leaf 1150369792 3767402496 false 2)) (.leaf 1567703040
    4315627520 true 2)) (.node 0 (.node 2 (.leaf 707002368 3453026304 true 2) (.leaf 377602048
    3123003392 true 2)) (.leaf 1231912960 3753541632 true 2)))) (.node 2 (.node 1 (.leaf 2165538816
    5019615232 false 2) (.leaf 1851293696 4554670080 false 2)) (.node 1 (.leaf 1827799040 4489363456
    false 2) (.leaf 1563082752 4024041472 true 2)))) (.node 0 (.node 2 (.node 1 (.node 0 (.node 2
    (.leaf 683130880 3506995200 true 2) (.leaf 322846720 3165814784 true 2)) (.leaf 1263353856
    3808821248 true 2)) (.node 0 (.node 2 (.node 1 (.leaf 547340288 2725412864 true 1) (.leaf
    218054656 2455781376 true 2)) (.node 1 (.leaf 178061312 2415542272 true 2) (.leaf 0 2164916224
    true 2))) (.leaf 1053671424 3287433216 true 2))) (.node 1 (.node 0 (.node 2 (.node 1 (.leaf
    519995392 2667266048 true 1) (.leaf 165249024 2386558976 true 2)) (.node 1 (.leaf 179486720
    2368913408 true 2) (.leaf 0 2107883520 true 2))) (.leaf 1009123328 3219308544 true 2)) (.node 0
    (.node 2 (.leaf 0 2289893376 true 2) (.leaf 0 2019819520 true 2)) (.leaf 871235584 2741862400
    true 2)))) (.node 2 (.node 1 (.leaf 1608876032 4096770048 true 2) (.leaf 1402732544 3667116032
    true 2)) (.node 1 (.leaf 1345847296 3585605632 true 2) (.leaf 1192460288 3192225792 true 2))))))
    (.node 2 (.node 1 (.node 0 (.node 2 (.leaf 2677915648 5944754176 true 2) (.node 1 (.leaf
    2810396672 5277253632 false 1) (.leaf 2564718592 4934369280 true 1))) (.node 2 (.leaf 2893922304
    5573312512 false 2) (.leaf 2653274112 5256986624 false 2))) (.node 0 (.node 2 (.leaf 2265595904
    5285019648 true 2) (.node 1 (.leaf 2349465600 4582670336 true 1) (.leaf 2166767616 4238262272
    true 1))) (.node 2 (.leaf 2586345472 5078450176 false 2) (.leaf 2341781504 4734320640 false
    2)))) (.node 1 (.node 0 (.node 2 (.node 1 (.leaf 2505195520 4857856000 true 1) (.leaf 2273902592
    4502142976 true 1)) (.node 1 (.leaf 2223800320 4421713920 true 1) (.leaf 2016509952 4067246080
    true 1))) (.node 2 (.leaf 2420162560 4902010880 false 2) (.leaf 2190360576 4527456256 false 2)))
    (.node 0 (.node 2 (.node 1 (.leaf 2080620544 4151558144 true 1) (.leaf 1893449728 3820339200
    true 1)) (.node 1 (.leaf 1820327936 3731095552 true 1) (.leaf 1664647168 3424485376 true 1)))
    (.node 2 (.leaf 2093760512 4371939328 false 2) (.leaf 1880014848 4008443904 true 2)))))

/-- The certificate on the box `(((root.upper 0).lower 2).lower 1)` (10 leaves). -/
def tree_0u_2l_1l : Tree :=
  .node 0 (.node 2 (.node 1 (.node 0 (.leaf 3399974912 5456592896 false 1) (.leaf 3305472000
    5016535040 false 1)) (.node 0 (.leaf 3407167488 5746458624 false 2) (.leaf 3323854848 5230510080
    false 1))) (.node 1 (.node 0 (.leaf 3366027264 5827559424 false 2) (.leaf 3307175936 5333565440
    false 1)) (.node 0 (.leaf 3236397056 5925519360 false 2) (.leaf 3240247296 5415043072 false
    1)))) (.node 2 (.leaf 2925363200 5055299584 false 2) (.leaf 2977284096 5327863808 false 2))

/-- The certificate on the box `(((root.upper 0).lower 2).upper 1)` (9 leaves). -/
def tree_0u_2l_1u : Tree :=
  .node 0 (.node 2 (.node 1 (.node 0 (.leaf 3325984768 5792071680 false 2) (.leaf 3284713472
    5274746880 false 1)) (.leaf 2928754688 5889949696 true 2)) (.node 1 (.node 0 (.leaf 3056779264
    5796151296 false 2) (.leaf 3135979520 5338513408 false 1)) (.node 0 (.leaf 2871328768 5499338752
    false 2) (.leaf 3020537856 5143527424 false 1)))) (.node 2 (.leaf 2925363200 5215813632 false 2)
    (.leaf 2977284096 5348048896 false 2))

/-- The certificate on the box `(((root.upper 0).upper 2).lower 1)` (11 leaves). -/
def tree_0u_2u_1l : Tree :=
  .node 0 (.node 2 (.node 1 (.node 0 (.leaf 3143614464 5814255616 false 2) (.leaf 3139010560
    5329780736 false 1)) (.node 0 (.leaf 2920022016 5740888064 false 2) (.leaf 3011264512 5294030848
    false 2))) (.node 1 (.node 0 (.leaf 2806644736 5489819648 false 2) (.leaf 2860089344 5065670656
    false 2)) (.node 0 (.node 2 (.leaf 2917875712 5041487872 false 1) (.leaf 2719645696 4760371200
    false 1)) (.leaf 2701393920 4940120064 false 2)))) (.node 2 (.leaf 2899476480 5314134016 false
    2) (.leaf 2726772736 5070094336 false 2))

/-- The certificate on the box `(((root.upper 0).upper 2).upper 1)` (14 leaves). -/
def tree_0u_2u_1u : Tree :=
  .node 0 (.node 2 (.node 1 (.node 0 (.leaf 2690859008 5478973440 true 2) (.leaf 2868887552
    5126193152 false 2)) (.node 0 (.node 2 (.leaf 2831433728 4878090240 false 1) (.leaf 2625191936
    4612407296 false 1)) (.leaf 2696839168 4872568832 false 2))) (.node 1 (.node 0 (.node 2 (.leaf
    2664103936 4707385344 false 1) (.leaf 2458845184 4404920320 false 1)) (.leaf 2507276288
    4717150208 false 2)) (.node 0 (.node 2 (.leaf 2396913664 4324147200 true 1) (.leaf 2187395072
    4026859520 false 2)) (.leaf 2303442944 4443357184 false 2)))) (.node 2 (.leaf 2707832832
    5219352576 true 2) (.node 1 (.leaf 2636595200 4745232384 false 2) (.leaf 2449489920 4582195200
    false 2)))

/-- The certificate tree of `F(𝒟₀₀) ⊆ 𝒟₀₀` (248 leaves). -/
def tree : Tree :=
  .node 0 (.node 2 (.node 1 (tree_0l_2l_1l) (tree_0l_2l_1u)) (.node 1 (tree_0l_2u_1l)
    (tree_0l_2u_1u))) (.node 2 (.node 1 (tree_0u_2l_1l) (tree_0u_2l_1u)) (.node 1 (tree_0u_2u_1l)
    (tree_0u_2u_1u)))

end SmoothedPolygons.TriFuller.DOutMaps
