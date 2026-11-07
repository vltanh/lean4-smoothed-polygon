# Credits

How this formalization was made, from the run log and the session transcript.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the formalization, chose the scope of
  each round and made the decisions it needed. In the first round these were proving Jacobi's
  formula by the Leibniz expansion instead of the book's argument, and proving Theorem 3.1.4(3)
  with the hypothesis that the tangents are Lipschitz (E13). The later rounds' decisions are listed
  under each round below.
- **Formalization:** Claude Opus 5.5 (`claude-opus-5-5`) in Claude Code 2.1.318 (VS Code
  extension, Claude Agent SDK), in one session, with sub-agents of the same model. There was no
  earlier draft; the project was written from scratch.
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill
  (local copy dated 17 October 2026): inventory of the paper, statements reviewed against the TeX
  source before any proof, proofs that follow the book's, a route check of every proof against the
  results the book's proof cites, cleanup, an audit report checked by independent agents, and
  packaging for Palomar.
- **Review:** no person has reviewed the proofs. Independent agents checked the statements against
  the TeX source (before the proofs were written), compared the proofs with the book's (in
  every round), verified every finding of the report against the TeX source, and checked the report's
  account of the literature and its suggestions against the cited works.

## First round (5 November 2026)

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

## Second round (5–6 November 2026)

The user asked for the rest: the Euler–Arnold equation (the one cited result still taken as a
hypothesis), the area formula of §3.2, the identification of the octagon's cost/√12 with a packing
density, and all of Chapter 2 with every cited theorem it uses proved ("prove everything"). The
user decided four questions: to prove all cited theorems rather than assume them, to close the gap
in Lemma 2.2.5 by Mahler's lattice route, to prove Lemma 2.2.1 through a maximal packed body, and,
when an agent found Lemma 2.2.1 false as printed, to formalize its classical packing form.

How it was made:

- **Euler–Arnold and the area formula** (main session and three agents): the Euler–Arnold equation
  for matrix groups in [`External/`](External); two general results in [`Basic/`](Basic) (the area of a star-shaped
  region, by polar coordinates, and its convexity); the smoothed `(6k+2)`-gons as balanced disks
  whose area is their cost.
- **Chapter 2 statements** (one agent), reviewed against the TeX source by another before any
  proof; two corrections applied.
- **Proofs** (about twenty agents, at most seven at once, coordinated by the main session):
  Gruber's density formula; the density of balanced disks; the boundary of the minimizer (§2.4);
  Minkowski–Mahler and Theorem 2.3.9; Mahler's 1947 theorem; the existence of critical lattices;
  §2.2 (Reinhardt's lemmas, and Lemma 2.2.5 by Mahler's route); Fejes Tóth's theorem, through
  Dowker's theorem and Böröczky's cell lemma, split into parts proved in parallel (maximal cells,
  pinwheel holes, polygon recognition, the planar Tietze–Nakajima theorem, the side count by angle
  sums); the corrected Lemma 2.2.1, with a Lean refutation of its printed form.
- **Cleanup** (main session and one agent): unused hypotheses, linter warnings, one copy of the
  hexagon lemmas.
- **Audit**: REPORT.md extended by the main session; an independent agent checked the new findings
  against the TeX source, corrected several, and showed three departures to be unforced; those
  proofs were rewritten along the book by two agents.

Figures, from the start of the round (5 November 2026, 19:02 CST) to the commit that completes the
round's REPORT.md (6 November, 10:34 CST), from the session transcript:

- elapsed time: 15.5 hours, including the night, during which agents worked or the session waited;
- sub-agents: 25, at most 7 running at once, 6 resumptions; their total working time 16.1 hours;
- tool calls: 2,075 by the sub-agents, 219 by the main session;
- tokens: sub-agents 5.84M output, 11.79M input (uncached input and cache writes), 598M cache
  reads; main session 0.26M output, 1.20M input, 144M cache reads;
- model calls: `claude-opus-5-5` only, 1,996 by the sub-agents and 223 by the main session.

For the whole project (both rounds, to the same commit): 20.5 hours elapsed, 43 sub-agents (at most
9 at once), 24.3 hours of sub-agent work.

## Third round (6–7 November 2026)

The user asked to finish what the report still listed as not formalized within the formalized
chapters: the small results of the book (Lemma 3.1.8, Remarks 7.5.2 and 7.6.4, the dihedral action
of §4.6, the remark after Definition 2.3.5), the cited results (Filippov's theorem, Jurdjevic's
Definition 6.3.1 and Proposition 6.4.1, Mahler's Lemma 3 in full) and Theorem 7.7.1, whose proof the
book only sketches; the conjectural Remarks 7.6.1 and 7.6.3 were left out. The user decided four
questions: to add the regularity hypothesis without which Lemma 3.1.8 is false (E34); to state
Filippov's theorem with convex extended velocity sets, since the book's form is false for costs that
depend on the control (E35); to read Theorem 7.7.1 up to time translation, with terminal time near
`t_f` and costates up to a positive factor, since the literal statement is false (E32); and, once
the papers behind Mahler's Lemma 3 had been found, to follow Mahler's 1946 paper as well as his paper
A.

How it was made:

- **Statements** (two agents): the new statements, and a plan of Theorem 7.7.1's proof as a sequence
  of lemmas, with the Jacobian of the Poincaré map in closed form (computed with sympy). An
  independent agent reviewed them against the TeX source and the cited sources; it confirmed the
  three counterexamples and corrected Filippov's statement.
- **Proofs** (fifteen agents, at most eight at once, coordinated by the main session): Theorem 7.7.1
  split into modules proved in parallel (the vertex flow; the switching slopes; the Poincaré map and
  the book's "direct calculation"; the algebra of hyperbolicity; the switching structure of nearby
  extremals, the fixed points and the assembly); Lemma 3.1.8 and the remarks; Filippov's theorem,
  with a measurable selection theorem that Mathlib lacks; Mahler's Lemma 3, whose sources an agent
  found in Mahler's collected works, proved along them (paper A's lemmas with a theory of boundary
  arcs; the 1946 Theorems B–C and D–E, which turned up an error and gaps that were repaired; the
  integration).
- **Verification and cleanup** (main session): unused hypotheses of the plan's lemmas, duplicated
  helpers, the axiom audit, the route check and Comparator.
- **Audit:** an independent agent compared the round's proofs with the book's. It found that the
  proof of Lemma 3.1.8 departed from the book without need and that a departure in Theorem 7.7.1
  was not recorded; three agents rewrote Lemma 3.1.8 along the book, made Theorem 7.7.1 use
  Remark 7.5.2 and the eigenvalue comparison of Lemma 7.5.5 as the book does (recording the
  remaining departure), and proved that the hypotheses of Remark 7.6.4 can be met. Two agents
  updated REPORT.md, README.md and formalization.yaml.

A weekly usage limit stopped the two agents then running in the afternoon of 6 November; they
resumed the next morning.

Figures, from the start of the round (6 November 2026, 11:38 CST) to the commit that completes the
round's REPORT.md (7 November, 09:07 CST), from the session transcript:

- elapsed time: 21.5 hours, including about 15 hours during which the usage limit stopped the work;
- sub-agents: 22 (one of them started by another agent), at most 8 running at once, 5 resumptions;
  their total working time 10.7 hours;
- tool calls: 2,002 by the sub-agents, 146 by the main session;
- tokens: sub-agents 3.91M output, 9.93M input (uncached input and cache writes), 474M cache reads;
  main session 0.16M output, 0.55M input, 45M cache reads;
- model calls: `claude-opus-5-5` only, 1,840 by the sub-agents and 154 by the main session.

For the whole project (three rounds, to the same commit): 43.0 hours elapsed, 65 sub-agents (at
most 9 at once), 35.0 hours of sub-agent work, 5,721 tool calls by sub-agents and 766 by the main
session.
