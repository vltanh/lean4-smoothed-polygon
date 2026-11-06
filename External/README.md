# External

The results that the book cites from other works and that the formalized part of it uses, each
stated in its source's terms and proved. Nothing here imports the paper's library.

| File | Cited result | Source | Used by |
| --- | --- | --- | --- |
| `EulerArnold.lean` | the Euler–Arnold equation `μ' = [μ, δh/δμ]` for the left-trivialized momentum `μ = pg` of a left-invariant Hamiltonian `H(g, p) = h(pg)` on the cotangent bundle of a matrix group ([`External.euler_arnold`](EulerArnold.lean#L72)) | R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, Birkhäuser, 1997 | Proposition 6.5.1 |

Other citations of the formalized chapters need no file here:

- The Pontryagin maximum principle (cited from Zelikin–Borisov) is not needed: a *Pontryagin
  extremal* is defined by the conditions that the principle lists ([`IsPontryaginExtremal`](../Challenge.lean#L162)), and
  Theorem 7.5.6 shows that the smoothed polygons satisfy them.
- Filippov's existence theorem (Theorem 6.1.1, cited from Zelikin–Borisov) is outside the scope.
- Rademacher's theorem (Corollary 3.1.10) is in Mathlib (`LipschitzWith.ae_differentiableAt`).
