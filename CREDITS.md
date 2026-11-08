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
  (local copy dated 17 October 2026; versions 3.0.1 to 3.2.5 of its repository in the fourth
  round, 3.3.0 and 3.4.0 in the seventh): inventory of the paper, statements reviewed against
  the TeX source before any proof, proofs that follow the book's, a route check of every proof
  against the results the book's proof cites, cleanup, an audit report checked by independent
  agents, and packaging for Palomar.
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

## Fourth round (7 November 2026)

The user asked for a plan to formalize the chapters the report listed as not formalized (Chapters
5 and 8–16), in layers that each end in a state that can be released, and for the first layer: the
Pontryagin maximum principle, which the book cites (from Agrachev and Sachkov) to show that a
minimizer of the Reinhardt problem lifts to a Pontryagin extremal (§6.2, §6.6). The user decided:
to prove the principle by Agrachev and Sachkov's own proof, which needs Brouwer's fixed-point
theorem; to write that theorem ourselves rather than adapt an existing Lean proof, as a separate
public package ([lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point)); to put the
general control theory in a second package
([lean4-optimal-control](https://github.com/vltanh/lean4-optimal-control)), published only once it
was proved; to redo the Reinhardt instance along the book's route once a first version, through an
Iwasawa chart, turned out to depart from the book without need; to prepare both packages for
Palomar, since neither result had been submitted; and, for the next layer, to prove that a
minimizer exists by the book's route (Chapter 5 and §6.1).

How it was made:

- **Plan** (seven agents): an inventory of Chapters 5 and 8–16 (one agent, with five helpers for
  the chapters), with the layers and the cited results each needs, and a plan for the first layer.
- **Brouwer's theorem** (two agents): the analytic proof of Milnor and Rogers, in its own package.
  A first agent had begun to adapt an existing Lean proof; it was stopped when the user chose to
  write our own.
- **Statements** (two agents): every statement of the layer, with `sorry`; an independent agent
  reviewed them against Agrachev and Sachkov's text and the book.
- **The maximum principle** (seven agents): one agent set up the optimal-control package; five
  proved its parts in parallel (Carathéodory equations; linear equations and the derivative of the
  flow; variations and needles; Lebesgue points, cones and Lemmas 12.1–12.2; the time change,
  Theorems 12.2–12.5 and the combined principle); one prepared it for publication.
- **The Reinhardt instance** (eight agents): a first version through an Iwasawa chart (two
  agents, in parallel with the package's five); after the independent comparison below, one agent
  designed and stated the book's route (the costate equations from Proposition 6.5.1, boundary
  conditions without the two redundant equations of E21), four proved its modules in parallel,
  and one switched the main theorem to it and removed the chart route.
- **Verification** (three agents): independent comparisons of the package's proofs with Agrachev
  and Sachkov's (two departures that were not forced were found and removed) and of the
  instance's proofs with the book's, twice: the chart route, which led to the rework, and the
  book's route, which confirmed it step by step and led the main session to record the change of
  state space as a departure and to correct four sentences of the documentation.
- **Packaging and audit** (three agents): Palomar files for each package (the main session added
  an earlier Lean proof of Brouwer's theorem that the list of related work had missed, and renamed
  modules that would have clashed with a dependent project's); REPORT.md, README.md and
  formalization.yaml.
- **Procedure:** during the round the main session also revised the skill (versions 3.0.1 to
  3.2.5), to state Palomar's rule on dependencies correctly and to add guidance on separate
  packages; eleven further sub-agents evaluated those revisions. They are counted in the figures
  below.

Figures, from the start of the round (7 November 2026, 09:08 CST) to just before the commit that
completes the round's REPORT.md (7 November, 14:41 CST), from the session transcript:

- elapsed time: 5.6 hours;
- sub-agents: 43 (32 on the formalization and its packages, 11 evaluating the skill; 5 started by
  another agent), at most 13 running at once (7 on the formalization), no resumptions; their total
  working time 12.4 hours (11.9 on the formalization);
- tool calls: 2,726 by the sub-agents, 377 by the main session;
- tokens: sub-agents 4.51M output, 10.82M input (uncached input and cache writes), 501M cache reads;
  main session 0.34M output, 0.77M input, 220M cache reads;
- model calls: `claude-opus-5-5` only, 2,470 by the sub-agents and 401 by the main session.

For the whole project (four rounds, to the same time): 48.6 hours elapsed, 108 sub-agents (97 on
the formalization; at most 13 at once), 47.4 hours of sub-agent work, 8,447 tool calls by
sub-agents and 1,146 by the main session.

## Fifth round (7 November 2026)

The user asked to continue with the plan's second layer: the existence of a global minimizer of the
Reinhardt control problem by the book's route (Chapter 5 and §6.1), which the user had chosen in
the fourth round over a shortcut through Reinhardt's K_min, and the identification of the
minimizers with K_min. No question needed the user's decision: an agent found that Problem 3.6.2
admits trajectories that wind several times, for which the converse the book uses in §6.1 is
false (E15), and a new lower bound on their cost (at least 7π/2) kept every statement and
definition as the book has it.

How it was made:

- **Statements** (two agents): every statement of the layer, with `sorry`, in seven modules for
  Chapter 5 and five for §6.1, the winding number, the converse of Problem 3.6.2 and K_min, and a
  general form of Filippov's theorem in the optimal-control package; an independent agent reviewed
  them against the TeX (all confirmed; four small fixes and the layer's combined statement).
- **Proofs** (ten agents, at most seven at once, one module each): the package's Filippov theorem
  with a closed state constraint; the winding lemmas; the converse; §6.1; Lemmas 5.0.3–5.0.5;
  Theorem 5.0.6; Lemma 5.0.7; Definition 5.0.1 and re-centering; the edge bound and Theorem 5.0.2;
  the identification with K_min (with the arclength parameterization and the existence of the
  reparameterization of §3.5, which the book takes for granted).
- **Verification and cleanup** (two agents): an independent comparison of the proofs with the
  book's (one departure that was not forced, in Lemma 5.0.7(4), was rewritten along the book's
  chain; three docstrings corrected; twelve gaps and errors of the book proposed as E-items), and a
  cleanup (redundant hypotheses, helper names, duplicates, the route review: every difference
  recorded or fixed).
- **Audit** (one agent): REPORT.md (E39–E47, E15 rewritten), README.md, formalization.yaml.

Figures, from the start of the round (7 November 2026, 14:52 CST) to the commit that completes the
round's REPORT.md (7 November, 17:18 CST), from the session transcript:

- elapsed time: 2.4 hours;
- sub-agents: 15, at most 7 running at once, no resumptions; their total working time 5.2 hours;
- tool calls: 1,243 by the sub-agents, 75 by the main session;
- tokens: sub-agents 2.00M output, 4.58M input (uncached input and cache writes), 277M cache reads;
  main session 0.07M output, 0.18M input, 25M cache reads;
- model calls: `claude-opus-5-5` only, 1,179 by the sub-agents and 77 by the main session.

For the whole project (five rounds, to the same commit): 51.2 hours elapsed, 123 sub-agents (112 on
the formalization and its packages; at most 13 at once), 52.6 hours of sub-agent work, 9,690 tool
calls by sub-agents and 1,258 by the main session.

## Sixth round (7 November 2026)

After publishing the second layer (with the user's approval), the round took the plan's third
layer: Chapter 8 (the edge control problems and the singular locus), Corollary A.1.3, and Theorem
16.3.1 (Mahler's First conjecture) conditional on one named hypothesis,
[`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107), which stands for Theorems 16.4.1 and 14.4.1 (Chapters 13–16, later
layers). The user decided two questions: Theorem 8.3.1, false as printed (two counterexamples,
checked independently), is formalized in its one-sided maximizer form; Theorem 8.2.7, whose proof
covers only one kind of singular subarc, is formalized in the authors' reading (singular includes
the edge problems), with the literal statement proved for normal lifts and left open for abnormal
ones. The statements of the fourth layer (Chapter 13) were also written and reviewed.

How it was made:

- **Statements** (two agents for the layer, one per restated theorem): every statement with
  `sorry`; an independent agent reviewed them, verified both counterexamples to Theorem 8.3.1 and
  narrowed the named hypothesis to edge extremals.
- **Proofs** (thirteen agents, at most nine at once): the edge problem and its maximum principle,
  Proposition 8.1.3 with the principle of optimality made precise, Theorem 8.1.4 and Lemma 8.1.5,
  the singular locus, the second variation of the circle, Theorems 8.2.7, 8.3.1–8.3.2 and Lemma
  8.3.4, smoothed polygons, and the assembly of Theorem 16.3.1.
- **Verification and cleanup** (four agents): an independent comparison with the book found the
  second variation's route an unforced departure (redone along the book: a fixed ψ in the book's
  time, with an exact cost formula), a skipped intermediate claim of Theorem 8.1.4 (restored) and a
  shortcut in Lemma 8.3.4 (replaced by the book's derivation); a cleanup renamed and merged
  helpers and recorded every route difference.
- **Audit** (one agent): REPORT.md (E48–E61; E21, E15 and E47 extended), README.md,
  formalization.yaml, with Theorem 16.3.1 marked as conditional throughout.
- **Fourth layer** (three agents): the statements of Chapter 13, an independent review (which
  recomputed the Jacobian at the outward fixed point to 38 digits) and its fixes.

Figures, from the end of the fifth round (7 November 2026, 17:18 CST) to just before the commit
that completes the round's REPORT.md (20:44 CST), from the session transcript:

- elapsed time: 3.4 hours (including the publication of the second layer);
- sub-agents: 22 (19 on the third layer, 3 on the fourth), at most 9 running at once, 2
  resumptions; their total working time 9.1 hours;
- tool calls: 1,836 by the sub-agents, 109 by the main session;
- tokens: sub-agents 3.58M output, 8.12M input (uncached input and cache writes), 413M cache reads;
  main session 0.10M output, 0.24M input, 62M cache reads;
- model calls: `claude-opus-5-5` only, 1,727 by the sub-agents and 116 by the main session.

For the whole project (six rounds, to the same time): 54.6 hours elapsed, 145 sub-agents (134 on
the formalization and its packages; at most 13 at once), 61.7 hours of sub-agent work, 11,528 tool
calls by sub-agents and 1,368 by the main session.

## Seventh round (7 November 2026)

After publishing the third layer (with the user's approval), the round proved the plan's fourth
layer, Chapter 13 (the triangular Fuller system), whose statements the sixth round had written. At
the user's request the main session also shortened the READMEs of this repository and of its two
packages, which had grown into long paragraphs, and moved their details to REPORT.md and the
packages' docs/ files.

How it was made:

- **Proofs** (ten agents, at most seven at once): linearized stability for maps (Basic/), the
  definitions and symmetries, the first control and switching time, the singular locus and the
  extremals, the weighted blow-up, the Fuller–Poincaré map, the R-scaling and the fixed points,
  the classification of fixed points (Lemma 13.5.2), the exact Jacobian at `q_out` with a
  certificate for its eigenvalues, and the assembly of Lemma 13.5.5.
- **Verification and cleanup** (two agents): an independent comparison with the book found no
  unforced departure and four docstrings that misdescribed the book; a cleanup renamed and merged
  helpers, fixed those docstrings and recorded every route difference.
- **Audit** (one agent): REPORT.md (E62–E69), README.md, formalization.yaml.
- **Packages** (one agent): the shorter READMEs of the two packages.
- **Fifth layer** (one agent, still running at the end of the round): the statements of Chapter 15
  and Theorem 16.1.1.
- **Procedure:** the main session also revised the skill (versions 3.3.0 and 3.4.0: a short README
  rewritten each round, and general guidance in place of rules tied to one project); ten further
  sub-agents evaluated the revision against the previous version. They are counted in the figures
  below.

Figures, from the end of the sixth round (7 November 2026, 20:44 CST) to just before the commit
that completes the round's REPORT.md (22:44 CST), from the session transcript:

- elapsed time: 2.0 hours (including the publication of the third layer);
- sub-agents: 26 (15 started on the formalization and its packages, 10 evaluating the skill, and
  one still running from the sixth round), at most 11 running at once, no resumptions; their total
  working time 6.5 hours (0.9 of them on the skill);
- tool calls: 1,339 by the sub-agents, 165 by the main session;
- tokens: sub-agents 2.50M output, 5.76M input (uncached input and cache writes), 254M cache reads;
  main session 0.13M output, 0.38M input, 127M cache reads;
- model calls: `claude-opus-5-5` only, 1,212 by the sub-agents and 167 by the main session.

For the whole project (seven rounds, to the same time): 56.6 hours elapsed, 170 sub-agents (149 on
the formalization and its packages; at most 13 at once), 68.1 hours of sub-agent work, 12,861 tool
calls by sub-agents and 1,529 by the main session.
