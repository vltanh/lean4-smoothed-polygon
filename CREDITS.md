# Credits

How this formalization was made, from the run log and the session transcript.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the formalization, chose its scope (the
  smoothed-polygon core of the book) and made the two decisions it needed: proving Jacobi's
  formula by the Leibniz expansion instead of the book's argument, and proving Theorem 3.1.4(3)
  with the hypothesis that the tangents are Lipschitz (E13).
- **Formalization:** Claude Opus 5.5 (`claude-opus-5-5`) in Claude Code 2.1.318 (VS Code
  extension, Claude Agent SDK), in one session, with sub-agents of the same model. There was no
  earlier draft; the project was written from scratch.
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill
  (local copy dated 17 October 2026): inventory of the paper, statements reviewed against the TeX
  source before any proof, proofs that follow the book's, a route check of every proof against the
  results the book's proof cites, cleanup, an audit report checked by independent agents, and
  packaging for Palomar.
- **Review:** no person has reviewed the proofs. Independent agents checked the statements against
  the TeX source (before the proofs were written), compared the proofs with the book's (two
  agents), verified every finding of the report against the TeX source, and checked the report's
  account of the literature and its suggestions against the cited works.

## First formalization (5 November 2026)

How it was made:

- **Setup and inventory** (main session): the arXiv TeX source, the list of results, constants and
  citations, the routes of the book's proofs ([`docs/paper_routes.tsv`](docs/paper_routes.tsv)), the Lean project on
  Mathlib `v4.36.0-rc2`; one agent surveyed the literature.
- **Statements** (main session): every definition and in-scope result stated with `sorry`, and the
  Challenge; one agent reviewed them against the TeX source, and the baseline was committed after
  its corrections.
- **Proofs** (nine agents, coordinated by the main session): one agent built the entrywise
  calculus of matrix curves in [`Basic/`](Basic), one proved the inequality of Lemma 7.5.3, six proved the
  chapters in parallel (Appendix A with the algebraic parts of
  Chapters 3 and 4; the state dynamics and Jacobi's formula; the adjoint orbit and the half-plane;
  the Hamiltonian, constant control and faces; the smoothed polygons and Theorem 7.5.1; and the
  assembly of Lemma 7.5.5, Theorem 7.5.6, the smoothed octagon and Lemma 4.3.1), and one showed
  that balanced pairs exist (the unit disk). The main session wrote the
  explicit costate lift of Theorem 7.5.1 that the parallel work shared, integrated the results and
  ran the checks.
- **Verification:** the axiom audit, the route check and Palomar's Comparator (main session); two
  agents compared the proofs with the book's.
- **Cleanup** (main session): three rounds removing unused hypotheses, recorded in REPORT.md,
  Section 5.
- **Audit:** REPORT.md written by the main session; two agents checked it, one the findings against
  the TeX source, one the literature and the suggestions. Their corrections added two findings
  (E21, E26), withdrew two departures and corrected the account of related work. One more agent,
  started before the report was complete, explored follow-up directions.

Figures, from the start (5 November 2026, 14:06 CST) to the commit that completes REPORT.md
(17:20 CST), from the session transcript:

- elapsed time: 3.2 hours;
- sub-agents: 16, at most 9 running at once, 3 resumptions; their total working time 6.4 hours;
- tool calls: 1,363 by the sub-agents, 358 by the main session;
- tokens: sub-agents 2.16M output, 5.13M input (uncached input and cache writes), 259M cache
  reads; main session 0.59M output, 1.22M input, 144M cache reads;
- model calls: `claude-opus-5-5` only, 1,283 by the sub-agents and 322 by the main session.

The figures cover the work up to that commit. They leave out the exploration of follow-up
directions and the packaging that came after it, and they count only what the transcript records:
the time of the Lean builds is included in the elapsed time, not in the agents' working time.
Spending was not tracked.
