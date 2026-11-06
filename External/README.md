# External

The results that the book cites from other works and that the formalized part of it uses, each
stated in its source's terms and proved. Nothing here imports the paper's library; general
lemmas they need are in [`Basic/`](../Basic).

| File | Cited result | Source | Used by |
| --- | --- | --- | --- |
| `FejesToth.lean` | for a centrally symmetric convex disk, no packing of congruent copies is denser (even in upper density) than the best lattice packing ([`External.fejes_toth`](FejesToth.lean#L882)) | L. Fejes Tóth, *Some packing and covering theorems*, Acta Sci. Math. (Szeged) 12A (1950); proof through Dowker's theorem and Böröczky's cell lemma ([`Basic/Analysis/Convex/CircumscribedPolygon.lean`](../Basic/Analysis/Convex/CircumscribedPolygon.lean), [`Basic/Analysis/Convex/CellDecomposition/`](../Basic/Analysis/Convex/CellDecomposition)) | Theorem 2.1.3 |
| `Gruber.lean` | the upper and lower densities of a lattice arrangement of a convex body are `V(C)/d(L)` ([`External.gruber_corollary_30_1`](Gruber.lean#L320)) | P. M. Gruber, *Convex and Discrete Geometry*, Springer, 2007, Cor. 30.1 | Definition 2.1.2 |
| `MinkowskiMahler.lean` | a critical lattice has a basis and a third point on the boundary forming a parallelogram of area `Δ(K)`; conversely ([`External.minkowski_mahler`](MinkowskiMahler.lean#L964)) | H. Minkowski 1907; K. Mahler, Proc. KNAW 50 (1947), Lemma 2 | Theorem 2.3.6 |
| `Mahler1947.lean` | the hexagon of tac-lines at the boundary points of a critical lattice: unique tac-lines, area `4Δ(K)`, sides bisected, least area ([`External.mahler_1947`](Mahler1947.lean#L1700)) | K. Mahler, *On the minimum determinant and the circumscribed hexagons of a convex domain*, Proc. KNAW 50 (1947), Theorems 1, 2 | Theorem 2.3.7 |
| `MahlerIrreducible.lean` | in an irreducible domain every tac-line contains a point of a critical lattice ([`External.mahler_irreducible`](MahlerIrreducible.lean#L196)): a weak form of the "only if" half of Mahler's Lemma 3, all that is used | K. Mahler, Proc. KNAW 50 (1947), Lemma 3 | Lemma 2.2.5 |
| `EulerArnold.lean` | the Euler–Arnold equation `μ' = [μ, δh/δμ]` for the left-trivialized momentum `μ = pg` of a left-invariant Hamiltonian `H(g, p) = h(pg)` on the cotangent bundle of a matrix group ([`External.euler_arnold`](EulerArnold.lean#L72)) | R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, Birkhäuser, 1997 | Proposition 6.5.1 |
| `Filippov.lean` | for a control system `q' = f(q, u)` with compact control set and convex velocity sets, the attainable sets (at time `T` and up to time `T`) are compact, and optimal controls exist for integral costs, with fixed or free terminal time ([`External.filippov`](Filippov.lean#L149)) | A. A. Agrachev and Yu. L. Sachkov, *Control Theory from the Geometric Viewpoint*, Springer, 2004, Thm 10.1; measurable selection ([`Basic/MeasureTheory/MeasurableSelection.lean`](../Basic/MeasureTheory/MeasurableSelection.lean)) and compactness of trajectories ([`Basic/Analysis/ODE/ControlSystem.lean`](../Basic/Analysis/ODE/ControlSystem.lean)) | Theorem 6.1.1 (its application in §6.1 needs Chapter 5) |

Where a proof departs from its source's argument (for instance where the source quotes a lemma
from another paper), the file's docstring says so, and [`REPORT.md`](../REPORT.md), Section 7, lists it.

Other citations need no file here:

- The Pontryagin maximum principle (cited from Zelikin–Borisov) is not needed: a *Pontryagin
  extremal* is defined by the conditions that the principle lists ([`IsPontryaginExtremal`](../Challenge.lean#L171)), and
  Theorem 7.5.6 shows that the smoothed polygons satisfy them.
- Rademacher's theorem (Corollary 3.1.10) is in Mathlib (`LipschitzWith.ae_differentiableAt`), and
  so is the Blaschke selection theorem (Lemma 2.2.5).
- Shifrin's Proposition 3.8 (Lemma 2.4.6) is a theorem about smooth curves; the book applies it to
  curves that are only `C¹` with Lipschitz derivative, so the formalization proves Lemma 2.4.6
  directly (REPORT.md, E11).
- Hales 2011, Lemmas 11, 17 and 18 are recalled with their proofs in the book (Lemmas 2.4.2, 2.4.3).
