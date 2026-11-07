module

public meta import Lean.Elab.Command
public meta import Lean.DocString
-- One `import all` line per module of the libraries, so that proofs are visible to the dependency
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find SmoothedPolygons External Basic -name '*.lean' | sort |
--     sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all Basic.Algebra.Module.ZLattice.PlaneCritical
import all Basic.Analysis.Calculus.MatrixEntrywise
import all Basic.Analysis.Calculus.MatrixEntrywiseExp
import all Basic.Analysis.Calculus.MatrixFTC
import all Basic.Analysis.Complex.UpperHalfPlane.GeneralizedCircle
import all Basic.Analysis.Convex.BoundaryArc
import all Basic.Analysis.Convex.CellDecomposition
import all Basic.Analysis.Convex.CellDecomposition.Defs
import all Basic.Analysis.Convex.CellDecomposition.HoleStructure
import all Basic.Analysis.Convex.CellDecomposition.MaximalCells
import all Basic.Analysis.Convex.CellDecomposition.PinwheelHoles
import all Basic.Analysis.Convex.CellDecomposition.PolygonOfFrontier
import all Basic.Analysis.Convex.CellDecomposition.PolygonSides
import all Basic.Analysis.Convex.CellDecomposition.SideCount
import all Basic.Analysis.Convex.CircumscribedPolygon
import all Basic.Analysis.Convex.HexagonLattice
import all Basic.Analysis.Convex.LatticePacking
import all Basic.Analysis.Convex.PolygonAngle
import all Basic.Analysis.Convex.StarCurve
import all Basic.Analysis.Convex.StarCurveConvex
import all Basic.Analysis.Convex.TietzeNakajima
import all External.EulerArnold
import all External.FejesToth
import all External.Filippov
import all External.Gruber
import all External.Mahler1946.TheoremC
import all External.Mahler1946.TheoremE
import all External.Mahler1947
import all External.MahlerIrreducible
import all External.MahlerIrreducible.Lemma3
import all External.MinkowskiMahler
import all External.Pontryagin
import all SmoothedPolygons.AppA.FunctionalDerivative
import all SmoothedPolygons.AppA.MatrixIdentities
import all SmoothedPolygons.AppA.Riemannian
import all SmoothedPolygons.Ch2.BalancedCircle
import all SmoothedPolygons.Ch2.BalancedDensity
import all SmoothedPolygons.Ch2.Boundary
import all SmoothedPolygons.Ch2.Density
import all SmoothedPolygons.Ch2.Hexagon
import all SmoothedPolygons.Ch2.Irreducible
import all SmoothedPolygons.Ch2.Mahler
import all SmoothedPolygons.Ch2.MultiCurve
import all SmoothedPolygons.Ch2.Reinhardt
import all SmoothedPolygons.Ch2.TilingCounterexample
import all SmoothedPolygons.Ch3.AreaFormula
import all SmoothedPolygons.Ch3.ControlProblem
import all SmoothedPolygons.Ch3.ControlSets
import all SmoothedPolygons.Ch3.CostFunctional
import all SmoothedPolygons.Ch3.HyperbolicArc
import all SmoothedPolygons.Ch3.Jacobi
import all SmoothedPolygons.Ch3.LieAlgebraDynamics
import all SmoothedPolygons.Ch3.StateDynamics
import all SmoothedPolygons.Ch4.AdjointOrbit
import all SmoothedPolygons.Ch4.IdealVertices
import all SmoothedPolygons.Ch4.StarDomain
import all SmoothedPolygons.Ch4.TerminalTime
import all SmoothedPolygons.Ch5.AreaBound
import all SmoothedPolygons.Ch5.Compactification
import all SmoothedPolygons.Ch5.EdgeBound
import all SmoothedPolygons.Ch5.Hexagon
import all SmoothedPolygons.Ch5.Monotonicity
import all SmoothedPolygons.Ch5.Recenter
import all SmoothedPolygons.Ch5.Theorem502
import all SmoothedPolygons.Ch6.AdmissibleDisk
import all SmoothedPolygons.Ch6.Existence
import all SmoothedPolygons.Ch6.HalfPlane
import all SmoothedPolygons.Ch6.Hamiltonian
import all SmoothedPolygons.Ch6.LeftInvariant
import all SmoothedPolygons.Ch6.MatrixCostate
import all SmoothedPolygons.Ch6.MatrixExtremal
import all SmoothedPolygons.Ch6.MatrixMinimizer
import all SmoothedPolygons.Ch6.MatrixSystem
import all SmoothedPolygons.Ch6.PeriodicExtension
import all SmoothedPolygons.Ch6.Winding
import all SmoothedPolygons.Ch6.WorstDisk
import all SmoothedPolygons.Ch7.ConstantControl
import all SmoothedPolygons.Ch7.DiscreteK
import all SmoothedPolygons.Ch7.Faces
import all SmoothedPolygons.Ch7.HMax
import all SmoothedPolygons.Ch7.HMaxInequality
import all SmoothedPolygons.Ch7.Isolated
import all SmoothedPolygons.Ch7.Isolated.Defs
import all SmoothedPolygons.Ch7.Isolated.FixedPoints
import all SmoothedPolygons.Ch7.Isolated.Hyperbolic
import all SmoothedPolygons.Ch7.Isolated.IpcAlgebra
import all SmoothedPolygons.Ch7.Isolated.IpcFlow
import all SmoothedPolygons.Ch7.Isolated.IpcOctagon
import all SmoothedPolygons.Ch7.Isolated.Poincare
import all SmoothedPolygons.Ch7.Isolated.Return
import all SmoothedPolygons.Ch7.Isolated.Switching
import all SmoothedPolygons.Ch7.Isolated.VertexFlow
import all SmoothedPolygons.Ch7.Polygon
import all SmoothedPolygons.Ch7.Remarks
import all SmoothedPolygons.Ch7.SmoothedPolygon
import all SmoothedPolygons.Ch7.SmoothedPolygonDisk
import all SmoothedPolygons.Ch7.StrongTransversality
import all SmoothedPolygons.Defs
import all Solution
-- The OptimalControl package needs no `import all`: the traversal stays inside the libraries,
-- and `collectAxioms` sees the axioms of the package's proofs (its `sorry`s too) without it.

/-!
# Axiom and dependency audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

For every numbered result of the paper, this prints the axioms it depends on and the results from
prior work (`External/`) that it uses, whether proved there or, in a conditional
formalization, assumed as hypotheses of its statement. It then checks every declaration
of the library and the theorems that Palomar's comparator checks. The run fails if any of them
depends on an axiom other than Lean's standard `propext`, `Classical.choice` and `Quot.sound` (a
`sorry` shows up as the axiom `sorryAx`). Its table of results is the source of the report's
dependency table.

It also writes the *route* of every numbered result to `.lake/route_deps.tsv`: the other
numbered results that its proof uses, found by following the proof through the library's helper
lemmas and stopping at numbered results, together with the TeX label that the result's docstring
names in backticks. `route_check.py` (in the skill's `scripts/`) compares these routes with the
results that the paper's proofs cite.

The library's modules are imported with `import all`, which makes the proofs of their theorems
available: the module system does not export them otherwise. The traversal tests membership in a
precomputed set of the library's constants; looking up each constant's module instead
(`Environment.getModuleIdxFor?`) makes the interpreted script take minutes.

To adapt: generate the `import all` lines, fill in the three lists, and set the libraries' root
names in `isLibraryModule`: the paper's library, `External`, the results it cites, and `Basic`,
the library of general mathematics.
Keep one `import all` line per module of the libraries, each on its own line: a module that is
missing is still imported through the others, but without its proofs, and the audit then misses the
axioms and the routes inside them. The CI template checks the list.
-/

open Lean Elab Command

namespace Audit

/-- The results from prior work, with a short label: the theorems proved in `External/`
or, when general, in `Basic/`, and, in a conditional formalization, the propositions assumed as
hypotheses. The traversal
stops at them. -/
meta def externalResults : List (String × Name) :=
  [("Euler–Arnold (Cushman–Bates)", ``External.euler_arnold),
   ("Fejes Tóth 1950", ``External.fejes_toth),
   ("Gruber, Cor. 30.1", ``External.gruber_corollary_30_1),
   ("Minkowski 1907, Mahler 1946", ``External.minkowski_mahler),
   ("Mahler 1947", ``External.mahler_1947),
   ("Mahler 1947, Lemma 3", ``External.mahler_irreducible),
   ("Mahler 1947, Lemma 3 (full)", ``External.mahler_irreducible_iff),
   ("Filippov (Agrachev–Sachkov, Th. 10.1)", ``External.filippov),
   ("Pontryagin maximum principle (Agrachev–Sachkov, Ch. 12)",
     ``External.pontryagin_maximum_principle)]

/-- The numbered results of the paper, in the order of the paper. -/
meta def paperResults : List (String × Name) :=
  [("Def 2.1.2", ``SmoothedPolygons.definition2_1_2),
   ("Thm 2.1.3", ``SmoothedPolygons.theorem2_1_3),
   ("Lemma 2.2.1", ``SmoothedPolygons.lemma2_2_1),
   ("Thm 2.2.2", ``SmoothedPolygons.theorem2_2_2),
   ("Remark 2.2.4", ``SmoothedPolygons.remark2_2_4),
   ("Lemma 2.2.5", ``SmoothedPolygons.lemma2_2_5),
   ("Lemma 2.2.6", ``SmoothedPolygons.lemma2_2_6),
   ("Lemma 2.2.7", ``SmoothedPolygons.lemma2_2_7),
   ("Def 2.3.2", ``SmoothedPolygons.definition2_3_2),
   ("Def 2.3.5 ≡ Mahler's (remark)", ``SmoothedPolygons.isIrreducible_iff_mahlerIrreducible),
   ("Thm 2.3.6", ``SmoothedPolygons.theorem2_3_6),
   ("Thm 2.3.7", ``SmoothedPolygons.theorem2_3_7),
   ("Thm 2.3.9", ``SmoothedPolygons.theorem2_3_9),
   ("Cor 2.3.10", ``SmoothedPolygons.corollary2_3_10),
   ("Lemma 2.4.2", ``SmoothedPolygons.lemma2_4_2),
   ("Lemma 2.4.3", ``SmoothedPolygons.lemma2_4_3),
   ("Cor 2.4.4", ``SmoothedPolygons.corollary2_4_4),
   ("Lemma 2.4.5", ``SmoothedPolygons.lemma2_4_5),
   ("Lemma 2.4.6", ``SmoothedPolygons.lemma2_4_6),
   ("δ = area/√12 (balanced disks)",
     ``SmoothedPolygons.greatestPackingDensity_of_isBalancedPair),
   ("Thm 3.1.1", ``SmoothedPolygons.theorem3_1_1),
   ("Thm 3.1.4 (1,2)", ``SmoothedPolygons.theorem3_1_4),
   ("Thm 3.1.4 (3)", ``SmoothedPolygons.theorem3_1_4_lipschitz),
   ("Def 3.1.5", ``SmoothedPolygons.definition3_1_5),
   ("Cor 3.1.6", ``SmoothedPolygons.corollary3_1_6),
   ("Lemma 3.1.8", ``SmoothedPolygons.lemma3_1_8),
   ("Prop 3.1.9", ``SmoothedPolygons.proposition3_1_9),
   ("Cor 3.1.10", ``SmoothedPolygons.corollary3_1_10),
   ("Cor 3.1.11", ``SmoothedPolygons.corollary3_1_11),
   ("Lemma 3.1.12", ``SmoothedPolygons.lemma3_1_12),
   ("Lemma 3.1.12 (adj)", ``SmoothedPolygons.lemma3_1_12_adjugate),
   ("Lemma 3.2.1", ``SmoothedPolygons.lemma3_2_1),
   ("Lemma 3.2.2", ``SmoothedPolygons.lemma3_2_2),
   ("eqn:cost (§3.2)", ``SmoothedPolygons.eqn_cost),
   ("Lemma 3.3.1", ``SmoothedPolygons.lemma3_3_1),
   ("Lemma 3.3.4", ``SmoothedPolygons.lemma3_3_4),
   ("Lemma 3.4.1", ``SmoothedPolygons.lemma3_4_1),
   ("Thm 3.4.2", ``SmoothedPolygons.theorem3_4_2),
   ("Prop 3.6.1", ``SmoothedPolygons.proposition3_6_1),
   ("Problem 3.6.2 converse (E15, winding one)",
     ``SmoothedPolygons.exists_isBalancedPair_of_isReinhardtAdmissible),
   ("Lemma 4.1.1", ``SmoothedPolygons.lemma4_1_1),
   ("Lemma 4.2.1", ``SmoothedPolygons.lemma4_2_1),
   ("Lemma 4.2.3", ``SmoothedPolygons.lemma4_2_3),
   ("Lemma 4.2.4", ``SmoothedPolygons.lemma4_2_4),
   ("Lemma 4.3.1", ``SmoothedPolygons.lemma4_3_1),
   ("Thm 4.4.1", ``SmoothedPolygons.theorem4_4_1),
   ("Lemma 4.5.2", ``SmoothedPolygons.lemma4_5_2),
   ("§4.6 R, S on ideal vertices", ``SmoothedPolygons.dihedral_smul_idealVertices),
   ("§4.6 Dih permutes ideal vertices", ``SmoothedPolygons.dihedral_permutes_idealVertices),
   ("Def 5.0.1: 𝔥** compact", ``SmoothedPolygons.isCompact_truncatedStarDomain),
   ("Thm 5.0.2", ``SmoothedPolygons.theorem5_0_2),
   ("Lemma 5.0.3", ``SmoothedPolygons.lemma5_0_3),
   ("Lemma 5.0.4", ``SmoothedPolygons.lemma5_0_4),
   ("Lemma 5.0.5", ``SmoothedPolygons.lemma5_0_5),
   ("Thm 5.0.6", ``SmoothedPolygons.theorem5_0_6),
   ("Lemma 5.0.7 (1)", ``SmoothedPolygons.lemma5_0_7_1),
   ("Lemma 5.0.7 (2)", ``SmoothedPolygons.lemma5_0_7_2),
   ("Lemma 5.0.7 (3)", ``SmoothedPolygons.lemma5_0_7_3),
   ("Lemma 5.0.7 (4)", ``SmoothedPolygons.lemma5_0_7_4),
   ("§6.1 existence of a minimizer", ``SmoothedPolygons.exists_isReinhardtMinimizer),
   ("§6.1 K_min is a minimizer", ``SmoothedPolygons.exists_isReinhardtMinimizer_of_isWorstDisk),
   ("§6.1 a minimizer is K_min", ``SmoothedPolygons.isWorstDisk_of_isReinhardtMinimizer),
   ("§6.1-6.2 a minimizer exists, is an extremal and a K_min",
     ``SmoothedPolygons.exists_isReinhardtMinimizer_isPontryaginExtremal_isWorstDisk),
   ("Lemma 6.1.2", ``SmoothedPolygons.lemma6_1_2),
   ("§6.2 minimizers are extremals",
     ``SmoothedPolygons.exists_isPontryaginExtremal_of_isReinhardtMinimizer),
   ("Prop 6.4.1", ``SmoothedPolygons.proposition6_4_1),
   ("Prop 6.5.1", ``SmoothedPolygons.proposition6_5_1),
   ("Cor 6.5.3", ``SmoothedPolygons.corollary6_5_3),
   ("Cor 6.5.4", ``SmoothedPolygons.corollary6_5_4),
   ("Remark 6.6.1", ``SmoothedPolygons.remark6_6_1),
   ("Remark 6.6.1 (Λ₁)", ``SmoothedPolygons.remark6_6_1_lambda1),
   ("Lemma 6.8.1", ``SmoothedPolygons.lemma6_8_1),
   ("Thm 6.8.2", ``SmoothedPolygons.theorem6_8_2),
   ("Thm 6.8.3", ``SmoothedPolygons.theorem6_8_3),
   ("Lemma 7.1.1", ``SmoothedPolygons.lemma7_1_1),
   ("Lemma 7.1.2", ``SmoothedPolygons.lemma7_1_2),
   ("Lemma 7.1.3", ``SmoothedPolygons.lemma7_1_3),
   ("Lemma 7.2.1", ``SmoothedPolygons.lemma7_2_1),
   ("Lemma 7.3.1", ``SmoothedPolygons.lemma7_3_1),
   ("Thm 7.5.1", ``SmoothedPolygons.theorem7_5_1),
   ("Remark 7.5.2", ``SmoothedPolygons.remark7_5_2),
   ("Lemma 7.5.3", ``SmoothedPolygons.lemma7_5_3),
   ("Lemma 7.5.5", ``SmoothedPolygons.lemma7_5_5),
   ("Example (octagon)", ``SmoothedPolygons.example7_5_smoothedOctagon),
   ("Thm 7.5.6", ``SmoothedPolygons.theorem7_5_6),
   ("Thm 7.7.1", ``SmoothedPolygons.theorem7_7_1),
   ("Remark 7.6.4", ``SmoothedPolygons.remark7_6_4),
   ("Prop A.6.1", ``SmoothedPolygons.propositionA_6_1),
   ("Prop A.6.2", ``SmoothedPolygons.propositionA_6_2),
   ("Prop A.6.3", ``SmoothedPolygons.propositionA_6_3),
   ("Lemma A.6.4", ``SmoothedPolygons.lemmaA_6_4),
   ("Lemma A.11.1", ``SmoothedPolygons.lemmaA_11_1)]

/-- The theorems that Palomar's comparator checks (`theorem_names` of `comparator.json`). -/
meta def solutionResults : List Name :=
  [``SmoothedPolygonsChallenge.smoothed_polygon_extremal,
   ``SmoothedPolygonsChallenge.smoothed_octagon_density]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the libraries: the paper's, `External` or `Basic`. -/
meta def isLibraryModule (m : Name) : Bool :=
  (`SmoothedPolygons).isPrefixOf m || (`External).isPrefixOf m || (`Basic).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.insert c
  return s

/-- The constants used by the type and the value of `c`. -/
meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- The external results reached from `root` through constants of the library, without looking
inside the proofs of the external results themselves. `deps` caches the constants of the library
that each constant uses, across calls. -/
meta def externalUses (env : Environment) (library : NameSet) (deps : NameMap (Array Name))
    (root : Name) :
    List Name × NameMap (Array Name) := Id.run do
  let externals := externalResults.map (·.2)
  let mut deps := deps
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut found : NameSet := {}
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      if c != root && externals.contains c then
        found := found.insert c
        continue
      let ds := match deps.find? c with
        | some ds => ds
        | none => (usedConstants env c).filter library.contains
      deps := deps.insert c ds
      for d in ds do
        if !visited.contains d then stack := d :: stack
  return (externalResults.filterMap fun (_, n) => if found.contains n then some n else none, deps)

/-- Where `#audit` writes the routes, relative to the project root (`.lake/` is not committed). -/
meta def routeFile : System.FilePath := ".lake/route_deps.tsv"

/-- The numbered results that the proof of `root` uses: those reached from it through constants
of the library, without looking inside the proofs of numbered results themselves. -/
meta def resultUses (env : Environment) (library results : NameSet) (root : Name) :
    Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := (usedConstants env root).toList
  let mut found : Array Name := #[]
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c || c == root then continue
      visited := visited.insert c
      if results.contains c then
        found := found.push c
        continue
      if !library.contains c then continue
      for d in usedConstants env c do
        if !visited.contains d then stack := d :: stack
  return found

/-- The code spans of the docstring of `c` that contain no space or comma: the candidates for its
TeX label. -/
meta def docLabels (env : Environment) (c : Name) : IO (Array String) := do
  let some doc ← findDocString? env c | return #[]
  let mut out : Array String := #[]
  let mut inside := false
  for part in doc.splitOn "`" do
    if inside && !part.isEmpty && !part.any (fun ch => ch.isWhitespace || ch == ',') then
      out := out.push part
    inside := !inside
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let library := libraryConstants env
  let mut deps : NameMap (Array Name) := {}
  let mut rows : Array String := #["| Result | Lean | Results from prior work used | Axioms |",
    "| --- | --- | --- | --- |"]
  for (label, n) in paperResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    let (uses, deps') := externalUses env library deps n
    deps := deps'
    let usesStr := if uses.isEmpty then "–" else ", ".intercalate (uses.map fun u => s!"`{u}`")
    let axStr := ", ".intercalate (axs.toList.map toString)
    rows := rows.push s!"| {label} | `{n}` | {usesStr} | {axStr} |"
  for n in solutionResults ++ externalResults.map (·.2) do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
  -- Every declaration of the library, including private and auxiliary ones.
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  -- The routes: for each numbered result, its docstring's labels and the results it uses.
  let results : NameSet := paperResults.foldl (fun s p => s.insert p.2) {}
  let mut routes : Array String := #[]
  for (label, n) in paperResults do
    let labels ← docLabels env n
    let uses := resultUses env library results n
    routes := routes.push (s!"{label}\t{n}\t{",".intercalate labels.toList}\t" ++
      ",".intercalate (uses.map toString).toList)
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile routeFile ("\n".intercalate routes.toList ++ "\n")
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
