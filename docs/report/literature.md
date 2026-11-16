# The paper in the literature

Part of the [audit report](../../REPORT.md).

Searched on 2026-11-05: web search, the arXiv API, zbMATH Open, OpenAlex, Semantic Scholar,
Crossref, GitHub, and the Isabelle AFP index. Google Scholar could not be queried.

## Before the paper

- K. Reinhardt, *Über die dichteste gitterförmige Lagerung kongruenter Bereiche in der Ebene und
  eine besondere Art konvexer Kurven*, Abh. Math. Sem. Univ. Hamburg 10 (1934) 216–230: the
  smoothed octagon, the existence of a minimizer and the structure results that Chapter 2 recalls.
  Published.
- K. Mahler, *On irreducible convex domains* and *On the area and the densest packing of convex
  domains*, Proc. KNAW 50 (1947) 98–107, 108–118, and *On the minimum determinant and the
  circumscribed hexagons of a convex domain*, Proc. KNAW 50 (1947) 692–703. Published.
  - The construction of the smoothed octagon and the remark the book calls Mahler's First
    conjecture.
  - The book cites the last two, and Proc. KNAW 49 (1946) 331–343.
- V. Ennola, *On the lattice constant of a symmetric convex domain*, J. London Math. Soc. 36 (1961)
  135–138, and P. P. Tammela, Izv. Vyssh. Uchebn. Zaved. Mat. 1970, no. 12, 103–107: lower bounds
  for the least packing density, Tammela's `0.892656…`. Published.
- F. L. Nazarov, Zap. Nauchn. Sem. LOMI 151 (1986) 104–114 (English: J. Soviet Math. 43 (1988)
  2687–2693): the smoothed octagon is a local minimum. Published.
- T. C. Hales, [*On the Reinhardt conjecture*](https://arxiv.org/abs/1103.4518), Vietnam J. Math.
  39 (2011) 287–307. Published.
  - The problem as a problem of Bolza; a minimizer has a `C¹` boundary with Lipschitz derivative;
    a piecewise analytic minimizer is a smoothed polygon.
  - Two conjectures (Five Link, Link Reduction, §7.6) that would reduce the problem for smoothed
    polygons to a finite-dimensional computation.
- T. C. Hales, [*The Reinhardt conjecture as an optimal control problem*](https://arxiv.org/abs/1703.01352),
  preprint (3 March 2017; version 1 only, no journal version):
  - the reformulation as an optimal control problem;
  - the claim that the smoothed octagon and the smoothed `(6k+2)`-gons are Pontryagin extremals
    with bang-bang control (Theorem 7.5.6 of the book, whose full write-up is the book);
  - the claim, in §4.5, that the smoothed octagon is isolated among extremals and a strict local
    minimum in a micro-local sense, by a sketch resting on interval-arithmetic computations (the
    "different proof" of Remark 7.7.2);
  - remarks on the smoothed `(6k−2)`-gons, which are the book's Remarks 7.6.2–7.6.3.
- K. Vajjha, [*On the Reinhardt Conjecture and Formal Foundations of Optimal Control*](https://arxiv.org/abs/2208.04443),
  PhD thesis, University of Pittsburgh (2022): the Hamiltonian structure and Lax equation, the
  compactness of the region of extremals, and the Fuller system near the singular locus.
- Earlier work the book does not cite:
  - Y. Kallus, [*Pessimal packing shapes*](https://arxiv.org/abs/1305.0289), Geom. Topol. 19
    (2015) 343–363 (the regular heptagon is a local pessimum for double-lattice packing);
  - C. A. Rogers, *The closest packing of convex two-dimensional domains*, Acta Math. 86 (1951)
    309–321.

## Concurrent work

No other paper on the Reinhardt problem appeared within a year of the book.

Undergraduate posters by L. Song and S. Sluis-Cremer, mentored by Hales, study the maximization of
the area over balanced disks.

- The posters: [github.com/lark-song/smoothed-decagon](https://github.com/lark-song/smoothed-decagon)
  (MAA MathFest, 4 August 2023; JMM, 5 January 2024). An April 2023 poster with N. MacLachlan
  states only conjectures.
- They state, without a published proof, that every smoothed `(6k−2)`-gon is a Pontryagin extremal
  of this maximization, as Hales's 2017 preprint and the book's Remark 7.6.3 suggest.
- Their area of the smoothed decagon, `3.22606`, does not match the book's `3.15` (TeX 6510–6533),
  which we reproduce (`3.150855`).

## Since the paper

The book is still an unrefereed preprint: only version 1 (7 May 2024) exists, with no journal
reference and no erratum.

- Hales's blog post (13 May 2024) states that the Reinhardt conjecture remains open.
- A Quanta Magazine article (28 June 2024) reports that the work had yet to be peer reviewed and
  that H. Cohn and G. Kuperberg, who read it informally, were confident in it.
- The Reinhardt conjecture, with its equality case, is proved in Lean in
  [vltanh/lean4-smoothed-octagon](https://github.com/vltanh/lean4-smoothed-octagon) (Palomar entry PALOMAR-2026-11-09-000008), by the same
  maintainer; it builds on this formalization and on OptimalControl (below).
- No paper claims progress on the conjecture otherwise. The only other claim we found is M. Ho's
  unreviewed Lean repository below (lower bound `0.8950112`, above Tammela's `0.892656`).
- OpenAlex lists one work citing the book (B. Grechuk, *One Hundred Open Problems*, in *Landscape
  of 21st Century Mathematics*, Springer 2026, pp. 565–607), which we did not read; Semantic
  Scholar lists none.
- Informal: J. Kim's expository notes on the book
  ([github.com/dylan0301/UnderstandingReinhardt](https://github.com/dylan0301/UnderstandingReinhardt),
  August 2026) include a chapter of open problems.

## Formalizations

- This is, to our knowledge, the first formalization of Theorems 7.5.6 and 7.7.1 and of the
  Hamiltonian part of the book (Chapters 6–8), and of Mahler's First conjecture, with no
  hypothesis. The search of 5 November found no formalization of Chapter 8 or of Theorem 16.3.1
  either.
  - The Hamiltonian part: costates, switching functions, Pontryagin extremals, the lift of a
    minimizer to an extremal, the edge control problem, singular subarcs and finite bang-bang
    control.
  - Its proof of N4, the fact that the book reads off a computation of the unstable curve for
    Theorem 14.4.1, is not the book's (E88). It rests on two things:
    - the exact structure of the Reinhardt flow along an `e₂`-arc: the state and the exit time in
      closed form, switching functions that are exponential sums with four terms, one step of the
      Reinhardt–Poincaré map as an explicit map of four parameters;
    - an explicit region that this step keeps until an arc leaves the star domain.
  - The state dynamics and the cost of Chapter 3 were formalized independently, three days
    earlier, in M. Ho's repository below.
- [vltanh/lean4-smoothed-octagon](https://github.com/vltanh/lean4-smoothed-octagon), by the same maintainer: a Lean 4 proof of the Reinhardt
  conjecture and its equality case (every centrally symmetric convex disk has greatest packing
  density at least that of the smoothed octagon, with equality exactly for its affine images),
  verified by Palomar (entry PALOMAR-2026-11-09-000008).
  - Its Challenge copies this formalization's packing definitions, and its proof uses the lift of
    a global minimizer to a Pontryagin extremal proved here and the maximum principle of
    OptimalControl.
- M. Ho, [github.com/sunfishho/reinhardt-density-bound](https://github.com/sunfishho/reinhardt-density-bound)
  (created 2 November 2026, three days before this search): an unreviewed, AI-assisted Lean 4
  development.
  - It claims the lower bound `0.8950112` for the packing density of every centrally symmetric
    convex disk, which would improve Tammela's `0.892656` (1970).
  - It has Lean proofs of results labelled after the book's Chapters 2, 3 and 5. Among them are the
    area identity of §3.2 (`FrameBoundary.cost_eq_area`, proved by a radial-sector area formula
    rather than Green's theorem) and the easy half of Theorem 2.2.2 (`packingDensity_ge_hexagon`).
  - Its README reports Comparator and NanoDa runs on 30 October 2026 and says that a clean
    `lake build` has not been validated.
  - It has no Hamiltonian or costate, and does not formalize Theorem 7.5.6.
  - This work did not consult or use it.
- The Pontryagin maximum principle has, to our knowledge, its first complete formal proof in the
  OptimalControl package that this formalization requires
  ([github.com/vltanh/lean4-optimal-control](https://github.com/vltanh/lean4-optimal-control),
  published 7 November 2026).
  - The proof covers free terminal time, an integral cost, mixed boundary conditions and strong
    local minimizers, by Agrachev and Sachkov's argument.
  - The earlier attempt in Lean,
    [willcforte/pontryagin-lean](https://github.com/willcforte/pontryagin-lean) (13 May 2026),
    states its key steps as axioms; this work does not use it.
  - Brouwer's fixed-point theorem, which the proof needs and Mathlib lacks, is proved in the
    FixedPoint package ([github.com/vltanh/lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point))
    by Milnor and Rogers' analytic argument.
  - Brouwer's theorem has earlier formal proofs, in Lean among other proof assistants; the
    FixedPoint proof was written without consulting them.
- The stable manifold theorem for maps has, to our knowledge, its first formal proof in the
  StableManifold package that this formalization requires
  ([github.com/vltanh/lean4-stable-manifold](https://github.com/vltanh/lean4-stable-manifold)).
  - The package's search of 14 November 2026 found none, in any system: Mathlib and its pull
    requests, GitHub, the Lean Zulip archive, the Isabelle AFP, Coq/Rocq, HOL Light, HOL4, Mizar,
    Metamath, ACL2 and PVS.
  - Concurrently, [TauCeti](https://github.com/TauCetiProject/TauCeti) (Lean 4, first committed on
    6 November 2026) proves the stable and unstable manifold theorem for an equilibrium of a `Cⁿ`
    vector field, that is, for flows rather than maps, by a Lyapunov–Perron contraction on bounded
    continuous curves.
  - The lean-eval benchmark states, without a public proof, the set-level part of the theorem for
    maps.
  - This work uses neither.
- Related formal developments: Green's theorem for elementary regions in Isabelle/HOL (Archive of
  Formal Proofs), and the Jordan curve theorem in HOL Light (Hales 2007).
- The classical results of Chapter 2 that this formalization proves have, as far as we found, no
  earlier formal proof (web search and the pinned Mathlib, 6 November 2026; Mathlib has
  Minkowski's convex body theorem and Blichfeldt's lemma, which the proofs use):
  - Fejes Tóth's theorem that lattice packings are densest for centrally symmetric disks;
  - Dowker's theorem on circumscribed polygons;
  - Minkowski's and Mahler's theorems on critical lattices and circumscribed hexagons;
  - the existence of critical lattices in the plane;
  - and the planar Tietze–Nakajima theorem.
