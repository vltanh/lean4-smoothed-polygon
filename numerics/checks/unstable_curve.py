"""Placeholder: the numerical fact behind Theorem 14.4.1, ``UnstableCurveLeavesStarDomain`` (N4),
``SmoothedPolygons/Ch14/UnstableCurve.lean``. **Not implemented.**

The statement (being written by another agent; read the Lean file for the current form):

    ∃ e, IsReinhardtPoincareExtension e ∧ ∃ U ∈ 𝓝 chartPtOut,
      ∀ p ∈ Function.localUnstableSet e chartPtOut U, 0 < p.1 → ReachesStarBoundary (lieChart p)

``ReachesStarBoundary q``: for some ``K`` the iterates ``q_j = reinPoincare^[j] q`` satisfy
``SwitchEntersE2 q_j`` (``j <= K``), ``ArcSwitchesToE1 q_j`` (``j < K``) and
``ArcLeavesStarDomain q_K`` (the ``e2``-arc leaves the star domain before its next switch).

This is a different dynamical system from the Fuller system of Chapters 13-16 (the Reinhardt system
of Chapters 7-12 in the chart of Chapter 14; arcs are closed-form ``e^{tP}``, ``e^{t(X0 + P)}``, the
switching functions are exponential polynomials), so nothing of ``boxmap`` applies. What a reference
computation should provide, following the module docstring of ``UnstableCurve.lean``:

1. ``W^u`` on a fundamental domain ``D = {r in [r0, e1(r0)]}`` (``r0 ~ 1e-3``) with rigorous error
   bounds: the Taylor data ``v = gamma'(0) ~ (-1.0777, -13.389, 3.9344)``,
   ``gamma''(0)/2 ~ (-2.56, -36.2, 7.7)``, and a validated tube (contraction ``~0.08`` per step).
2. Along each orbit from ``D``, per arc: the switching time and the slope ``N21'(t_sw)``, the exit
   time and ``rho2'(T)``, every margin of N4 (normalized by ``r^3``, ``r^2`` near the divisor), and
   the number ``K`` of arcs (2 or 3).
3. The threshold ``r* ~ 0.0650``: its parameter ``s*`` on ``D``, the end point
   ``(0.2098, -3.0326)`` of the curve of switching points, the slope ``dN21(T_exit)/ds`` at ``s*``,
   and below ``s*`` the ``eps``-expansion of the cusp arc with rigorous bounds.
4. A trapping region ``T`` (centre ``c(r)``, widths ``kappa(r)``), its forward-invariance margins,
   ``r'/r``, and bounds of ``DF`` on ``T``.
5. The coefficients ``c_mk(p)`` of ``N21``, ``N23``, ``rho0``, ``rho2`` on each arc and their sign
   patterns, to see whether a Descartes-type count certifies the zero counts.

The double-precision and mpmath models of ``notes/l7st/`` (not rigorous) are the starting point.
"""

STATUS = 'not implemented (placeholder)'

PLAN = [
    'unstable curve W^u on a fundamental domain, with a validated tube',
    'per-arc switching/exit times and the margins of N4 along the orbits from D',
    'the threshold r* (s*, end point (0.2098, -3.0326), slope, cusp-arc expansion)',
    'a trapping region and its invariance margins and DF bounds',
    'the exponential-polynomial coefficients of N21, N23, rho0, rho2 and their sign patterns',
]


def run():
    """returns the placeholder record (nothing is computed)"""
    return {'status': STATUS, 'lean': 'SmoothedPolygons/Ch14/UnstableCurve.lean',
            'statement': 'UnstableCurveLeavesStarDomain', 'plan': PLAN}
