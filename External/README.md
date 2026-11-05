# External

The results that the book cites from other works and that the formalized part of it uses.

The formalized chapters (3, 4, 6, 7 and Appendix A.6, A.11 of Hales–Vajjha, *Packings of
Smoothed Polygons*) assume no cited theorem:

- The Pontryagin maximum principle (cited from Zelikin–Borisov) is not needed: a *Pontryagin
  extremal* is defined by the conditions that the principle lists ([`IsPontryaginExtremal`](../Challenge.lean#L162)), and
  Theorem 7.5.6 shows that the smoothed polygons satisfy them.
- Filippov's existence theorem (Theorem 6.1.1, cited from Zelikin–Borisov) is outside the scope.
- The Euler–Arnold equations for left-invariant Hamiltonians (cited from Cushman–Bates in the proof
  of Proposition 6.5.1) are the form of the hypothesis of [`proposition6_5_1`](../SmoothedPolygons/Ch6/Hamiltonian.lean#L314): the proposition
  derives the costate equations from Hamilton's equations, which it takes as its premises.
- Rademacher's theorem (Corollary 3.1.10) is in Mathlib (`LipschitzWith.ae_differentiableAt`).

This directory therefore holds no Lean files.
