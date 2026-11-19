# numerics: a rigorous reference for the numerical facts of Chapters 13-16

A Python reference implementation of the Fuller-Poincaré map of Hales-Vajjha, *Packings of
Smoothed Polygons*, exactly as the Lean definitions say, and rigorous interval checks of the
numerical facts that the book takes from Mathematica plots. For N4 (Theorem 14.4.1) it does the
same with the Reinhardt system along `e2`-arcs ([N4 section](#n4-theorem-1441-unstablecurveleavesstardomain-ch14)).

**It is a reference.** The Lean proofs do not depend on it: nothing here is imported or trusted by
Lean, and none of its output is used by a Lean proof. It reproduces the book's numbers, gives the analytic proofs their
margins and regions, and is an independent check of the Lean statements.

## Layout

| file | contents |
| --- | --- |
| `iv.py` | interval arithmetic on floats with directed rounding (TwoSum, `fma`), exact at `0`; `sin`, `cos`, `atan`, `asin` from Arb at the endpoints of monotone pieces |
| `jet.py` | first-order jets over intervals (forward AD): mean value forms, Jacobian bounds |
| `fuller.py` | the map at a point, in Arb balls (200 bits): first control, first switching time, image, cell coordinates; every sign is decided or `Undecided` is raised |
| `cubic.py` | sign certificates for cubics with interval coefficients on time intervals |
| `boxmap.py` | one step on a box: switching windows, image enclosures; the blow-up charts `EdgeBox`, `SqrtBox` |
| `faces.py`, `edges.py` | face points whose first control is not the cell's (canonical representatives); when a box is replaced by a chart |
| `regions.py` | `basinA`, `basinB`, `cellBox`, the targets |
| `driver.py` | adaptive subdivision, in parallel |
| `reinhardt.py` | N4: the Reinhardt system along an `e2`-arc in closed form (exponential polynomials), the chart of Chapter 14, `Ad_{R^-1}`, the arc parameters by their Lean definitions; in mpmath or Arb balls |
| `arcmap.py` | N4: the arc parameters `(eps, Y, f0, q, p)`, the one-step map `ArcParams.step` and its closed forms, `G*` (`arcRegion`), the exit test |
| `checks/` | `dout.py`, `subclaims.py`, `cell_two.py`, `remark.py`, `common.py`; for N4 `unstable_curve.py`, `arc_invariant.py`, `arc_certificates.py` |
| `report.py`, `__main__.py` | the command line |
| `generators/` | `dout_contraction_bounds.py` (with `contraction_intervals.py`) generated the interval chain that once bounded the derivatives in the Lipschitz part of `DOutContracts`; the Lean proof now bounds them by hand (`SmoothedPolygons/Ch16/DOutDerivativeBounds.lean`), and the generator stays as a reference |

## Running

```sh
pip install --user python-flint            # python-flint 0.9 (Arb); numpy is used for root guesses
pip install --user mpmath sympy            # for N4 (mpmath 1.3, sympy 1.14)
python3 -m numerics selftest remark        # a few seconds
python3 -m numerics dout subclaims celltwo --jobs 12
python3 -m numerics all --quick            # without the certified-margin reruns
python3 -m numerics unstable --jobs 12     # N4 (its parts: wucurve, arcinv, arccert)
```

Results are written to `notes/ref/results.json` (`--out FILE`). `NUMERICS_JOBS` sets the number of
worker processes (default `min(10, cpus)`), `NUMERICS_PROGRESS=1` prints progress. Times with 12
processes: `selftest` and `remark` seconds, `subclaims` 2 min, `dout` about 40 min (22 of them for the
Lipschitz bound of the wider witnesses), `celltwo` 30 min (by its time limit), `unstable` 36 s.

## Results

Run of 2026-11-15 (`notes/ref/results.json`, logs `notes/ref/run_*.log`), 12 worker processes on a
shared 20-core machine (8 for `celltwo`). Margins: *sampled* is the smallest margin found by the point
evaluator on a grid of the closed domain refined by a local search (an upper bound of the true
minimum, with the point where it is attained); *certified* is a margin the box check proves (a lower
bound). Coordinates are `(r2, psi, theta2)`.

| Lean statement | result | boxes (leaves) | time | sampled min margin, at | certified |
| --- | --- | --- | --- | --- | --- |
| `DOutContracts`: `F(D00) ⊆ D00` | **proved** | 429 | 1 s | 0.6914 (`theta2' >= pi - 1.1`), the class `r2 = 1, theta2 = pi` | >= 0.622 |
| `DOutContracts`: the docstring's witnesses, `N = 2`, `κ = 1/2` | **proved** | see below | 14 min | see below | `κ = 0.36` |
| `BoxSubclaims` (seven boxes) | **proved** | 6,392 | 111 s | see below | > 0 |
| `CellTwoEntersDOut` | **not finished**: proved on 74.2% of the closed cell (volume) | 140,107 | 29 min (time limit 120 s per root box) | 0.789 on the grid; 0.373 in the unproved part; 1.1 - π/3 = 0.0528 is the infimum (a corner limit, earlier report) | > 0 where proved |
| `remark15_3_1`, `remark15_3_1_segment` | **true**: the 14 numerical claims, and the fixed points | (points) | < 1 s | | |
| `UnstableCurveLeavesStarDomain` (Ch14; proved in Lean without computation) | **true** on 500 orbits of `W^u`; (INV) true at 63,530 sampled switching points of `G*`; the identities of its proof hold exactly (see the N4 section) | 500 orbits (4,182 arcs); 68,875 points of `G*` | 36 s | exit arcs on `W^u`: `min F = 1.55e-4` at `r = 0.06497` (next to the threshold); (INV) `0.0417` at the corner `x = y = 1e-9` of `G*` | every sign on the 500 orbits (Arb) |

`DOutContracts`, the second conjunct, for three choices of witnesses (`B = Icc lo hi`; every stage is
one step `F(X) ⊆ Y` from all of `X`; `κ` bounds the sup-norm row sums of the Jacobian of the branch
`g` on `B`, through the implicit root):

| witnesses | stage | leaves | time | sampled min margin, at |
| --- | --- | --- | --- | --- |
| docstring: `B = [0.25,0.29]x[0.15,0.19]x[2.85,2.98]`, `N = 2` | `F(D00) ⊆ D'' = [0,0.28]x[0,0.2]x[2.72,pi]` | 324,105 | 603 s | 0.0060 (`r2' <= 0.28`) at `(1, 0, pi-1.1)` |
| | `F(D'') ⊆ B` | 22,026 | 32 s | 0.0069 at `(0.28, 0, pi)` |
| | `F(B) ⊆ B` | 101 | 0.1 s | 0.0167 at `(0.29, 0.15, 2.98)` |
| | `κ = 1/2`; certified `κ = 0.36` | 5,228; 165,778 | 6 s; 211 s | sampled max row sum 0.313 at `(0.29, 0.15, 2.98)` |
| wider: `B = [0.15,0.38]x[0.08,0.28]x[2.7,3.1]`, `N = 2` | `F(D00) ⊆ [0,0.4]x[0,0.4]x[2.5,pi]` | 7,971 | 19 s | 0.1263 (`r2' <= 0.4`) at `(0.587, 0, pi-1.1)` |
| | `F([0,0.4]x[0,0.4]x[2.5,pi]) ⊆ B` | 969 | 1 s | 0.0714 at `(0.4, 0, pi)` |
| | `F(B) ⊆ B` | 115 | 0.1 s | 0.0780 at `(0.38, 0.08, 3.1)` |
| | `κ = 1/2` | 971,460 | 22 min | sampled max row sum 0.405 at `(0.38, 0.08, 3.1)` |
| the Lean certificates' route (`Ch16/Certificates/DOutStep*`), `N = 3`, `X3 ⊆ B` of the docstring | `F(D00) ⊆ X1` | 8,293 | 22 s | 0.1263 at `(0.587, 0, pi-1.1)` |
| | `F(X1) ⊆ X2` | 2,377 | 3 s | 0.0393 at `(0.4, 0, pi)` |
| | `F(X2) ⊆ X3` | 2,628 | 4 s | 0.0102 at `(0.32, 0.100, 3.042)` |

The wider witnesses have margins five to twenty times larger at the three inclusions
(`0.126, 0.071, 0.078` against `0.006, 0.007, 0.017`), at the price of a smaller Lipschitz margin
(`0.095` against `0.187`): better for an analytic proof. `N = 1` is impossible for any `B` in the
open cell (`F(D00)` reaches `r2' -> 0`).

`BoxSubclaims` per box (the margin of the image in `{psi' <= a_i} ∪ {psi' <= a_{i+1}, theta2' >= b_j}`;
images in `cellTwoSet` need no margin):

| box | leaves | time | sampled min margin | at |
| --- | --- | --- | --- | --- |
| `D01` | 149 | 0.4 s | 0.1061 = 2.2 - 2π/3 | limit `r2 -> 0, psi -> π/3, theta2 -> 1.1` (`t_sw -> 0`) |
| `D02` | 607 | 5 s | 0.5236 = π/6 | `(1, 0, π/3+)` |
| `D10` | 145 | 0.4 s | 0.8532 | `(1, π/3, π - 1.1)` |
| `D11` | 279 | 2 s | 0.7433 | `(0.83, 2.094, 1.1)` |
| `D12` | 309 | 1 s | 0.9775 | `(0.51, 2.094, 0.451)` |
| `D20` | 1,639 | 32 s | 1.8960 | `(0.697, π, π - 1.1)` |
| `D21` | 3,264 | 67 s | 0.1486 | `(0.174245, π, 1.1)` (edge scan; the grid gives 0.176) |

`CellTwoEntersDOut`: the unproved 25.8% are boxes still open after 120 s per root box or failing at
depth 18 (`results.json`, `celltwo.failed clusters`), mostly near the faces `theta2 = -pi`
(change of representative into the first cell, stretching by about 30), `theta2 = 0`, `r2 = 0`,
`psi in {0, pi}`, and near surfaces where a switching cubic is nearly tangent to `0`. All 3,000 random
points of the unproved boxes reach `D00` within three steps (point evaluator); no counterexample was
found. More time per root (`cell_two.run(time_limit=...)`) proves more; a complete certificate
needs the asymptotic forms of the corner `r2 -> 0, psi -> pi, theta2 -> -pi/3` (margin `-> 0.0528`)
and of the faces above.

Remark 15.3.1 (`checks/remark.py`, Arb at 200 bits): `rScale = 6.27416739952482...`;
`pOut = (0.26794919243112270647, 0.17059350075774605669, 2.9157399978237336981)` with
`|r2 - (2 - √3)| < 1e-50`; `pIn = (0.2679..., 2.9709991528320471818, 0.22585265576605954036)`;
`F` fixes both (to `1e-57`); `Δ_{B,1}` at `0.26775`, `0.26777`: `8.846e-7`, `-1.700e-6`; the new first
control `ζ^2`, `1`; `Δ_{A,0}` at `0.26790`, `0.26791`: `-2.613e-11`, `2.007e-11`; `t_sw`:
`0.98433`, `0.82376`; `0.26791 < 2 - √3`. The Jacobian of `F` at `q_out` in cell coordinates has the
eigenvalues `0.00065, -0.008070, -0.07997` (Lemma 13.5.5). `t_sw(q_out) = 4.99939` for the
representative with `r1 + r2 = 1` (`7.40352` for `qOutCart`).

## The map, as in Lean

| Lean | here |
| --- | --- |
| `flow`, `ham`, `switchingFunction` (`Ch13/Defs.lean`) | `D_{u,v}(t) = RR(v - u, z3(t; z, u))`: `v` beats `u` at `t` iff `D_{u,v}(t) > 0` |
| `IsFirstControl`, `firstControl` | the `u` whose two cubics have a negative lowest nonzero coefficient (`fuller.first_control`); cross-checked against Lemma 13.2.6 (`lex_first_control`) |
| `firstSwitchTime` | `min_v inf {t > 0 : D_{u,v}(t) > 0}`: the first sign change, by root isolation on the monotone pieces; a tangency is not a switch |
| `poincare`, `poincareAngZero` | `F(z) = flow(t_sw)`; the class is that of `zeta^(-m) F(z)` (`m` the third control), with `x3 < 0` and first control `zeta^(-m) v` (`firstControl_poincare_ne`) |
| `cellPoint`, `cellCoords`, `cellBox`, `cellTwoDomain` | `fuller.cell_point`, `fuller.cell_coords`, `regions.py` |
| face points with another first control | `faces.py`: the class of a rotated representative on a face of the first cell with first control `zeta` |

## How a box is certified (`boxmap.step`)

For a box of a closed cell with control `u`, and its points whose first control is `u`:

1. `hi`: a time at which some control certainly beats `u` on the whole box, so `t_sw <= hi`.
2. A control `w` is excluded when, on `(0, hi]`, `D_w < 0` wherever the third cubic is `<= 0`; or,
   near `r2 = 0`, when in the time `s = t/r2` the other control certainly switches by `s = K`
   while `D_w < 0` on `(0, K]`.
3. For each remaining `w`: windows of `[lo_w, hi]` (`D_w < 0` on `(0, lo_w]`) where the enclosure
   of `D_w` contains `0`. The switch to `w` happens in a window, at a root of `D_w`.
4. The image: `w1 = z1(t)`, `w2 = z2(t)` rotated by `zeta^(-m)`; `r2' = 4|w2|/(|w1| + sqrt(|w1|^2 + 4|w2|))^2`,
   `theta2' = arg w2`, `psi' = arg(w2 conj w1)` and `sin psi' = -x3'/(2|w1||w2|)`. Near the faces:
   `w2/t`, `x3/t`, `w1/t`, `w1/r1` through the root equation, and cone bounds (a positive
   combination lies between its summands). A single remaining control: the image is in the open
   part of its cell (`x3 < 0`). Two: either can switch; at a tie `t_w = t_w'`, `z3(t_sw) = 0` and the
   image is a face class, represented by either formula.
5. Mean value form through the implicit root where `dD/dt > 0`: enclosures of the image and of its
   Jacobian.

Blow-up charts where the regular forms degenerate: `EdgeBox` near the edges `{r2 = 0, psi in {0, pi}}`
(`r2 = eps`, `alpha = eps kap` or the reverse, time `t/eps`), `SqrtBox` near `{r2 = 0, theta2 = 0}`
(`r2 = eps^2`, time `t/eps`).

Every "proved" is a proof modulo the correctness of this code and of python-flint: the interval
operations round outward, the transcendental functions come from Arb, and the facts used without
computation are theorems of the Lean development (the image lies on a wall, the first control changes
at the switch, the class is invariant under `V_T` and the rescalings, `cellClass_cellCoords`). Lean
checks none of it. `python3 -m numerics selftest` compares the semantic first control with Lemma
13.2.6 (2,000 points, faces included), the canonical face representatives with the honest map
(182 points), and the box enclosures with the point evaluator (1,483 points of random boxes of all
kinds): no disagreement.

## Where the regular box forms degenerate (what an analytic proof must treat)

| place | what happens | treatment here |
| --- | --- | --- |
| `D00`, `r2 -> 0`, `theta1 = theta2 - psi -> pi/3` | `t_sw -> 0`, `w2 -> 0`; image -> `(0, 0, pi)` | `D/t^2` monotone; `w2/t` with `r2/t` from `D = 0` |
| wrong-control parts of the face `r2 = 0` | `t_sw ~ sqrt(r2)` (switch to the eventual winner) | `w2/t` |
| edges `{r2 = 0, psi in {0, pi}}` (wrong sector) | `z2 ~ r2`, `z3 ~ r2 alpha`: the root equation degenerates | `EdgeBox` charts (`r2 = eps`, `alpha = eps kap` or the reverse; time `t/eps`) |
| corner `{r2 = 0, theta2 = 0}` | the switch to `zeta^2` (time `~ r2 theta2`) beats the switch to `1` (time `~ sqrt(r2)`) | `SqrtBox` (`r2 = eps^2`, time `t/eps`) |
| `r2 -> 1` with `t -> 0` | `w1 -> 0` | `w1/t`, `w1/r1` (`t/r1` from `D = 0`) |
| corners `(r2, psi, theta2) = (0, 0, pi/3)`, `(1, 0, pi/3)` of `D02` | sector boundary of the face `psi = 0`: `t_sw -> 0` at different rates | cone bounds: `w2 = r2 e^{i theta2} + t (...)`, `w1 = r1 e^{i theta1} + t (-iu)` are positive combinations |
| `D21` near `(0.17, pi, 1.1)` | the image passes near `r2' = 0` (`|w2| ~ 0.03`), its direction moves `~800` per radian of `alpha` | finer boxes, time windows cut into 32 pieces |
| `∂_res` (the two switching times coincide) | the target changes (smaller box / second cell); at the surface `z3(t_sw) = 0` | both branches; a tie is a face class with either formula's coordinates |
| near-tangency surfaces (`∂_B`-like) | a switching cubic touches `0` | windows from the parameter mean value form of `D` |
| second cell near `theta2 = -pi` | change of representative into the first cell near `theta2 = pi`, with stretching `~30` | images up to width `0.3`, cached dyadic boxes at the next step |

## Findings

* No disagreement with the Lean statements: the three named facts hold wherever they were checked
  (everywhere for `DOutContracts` and `BoxSubclaims`), with the margins of the earlier numerical report
  (`notes/briefs/l5_numerics_report.md`), which are reproduced to four digits (`0.6914`, `0.0060`,
  `0.0069`, `0.0167`, `0.313`; the seven `BoxSubclaims` margins).
* `DOutContracts` docstring: `F(B) ⊆ [0.26668, 0.26897] x [0.16801, 0.17253] x [2.90549, 2.92458]` and
  the margins agree; the sampled hull of `F(D00)` printed there is too small at `r2 -> 0` (the image
  reaches `r2' -> 0`, `psi' -> 0`, `theta2' -> pi`), as the earlier report said; the witnesses work, but
  with margins below `0.01` at two stages.
* `CellTwoEntersDOut` is the expensive fact: certified on 74% of the cell in 30 minutes with these
  forms; the earlier estimates (`10^5-10^6` boxes, asymptotic forms needed) are confirmed.
* The face points whose first control is not the cell's (Figure 15.1) map to points of the closed
  first cell with first control `zeta` (`faces.py`); in `D00` they all have representatives in `D00`
  itself.

## N4: Theorem 14.4.1 (`UnstableCurveLeavesStarDomain`, Ch14)

The book reads N4 off Figure 14.2, a Mathematica plot of the unstable curve `W^u(q_out)`. Lean
proves N4 without computation (`unstableCurveLeavesStarDomain`, through (INV), `Ch14/Arc*.lean`).
This is the reference for it. The dynamical system is the Reinhardt system in the chart of
Chapter 14, not the Fuller system, so `boxmap` plays no part: every `e2`-arc is a closed-form
exponential polynomial (`reinhardt.py`), and the Poincaré map is an explicit map of the arc
parameters (`arcmap.py`). The numbering is that of `docs/unstable-curve.pdf`. Run of 2026-11-18,
`--jobs 12`, 37 s; the results were written to
`notes/n4num/results.json` (log `notes/n4num/run_unstable.log`); the default `--out` merges them into
`notes/ref/results.json`.

| part | arithmetic | what is computed | result |
| --- | --- | --- | --- |
| 1 `checks/unstable_curve.py` (`wucurve`, 15 s) | mpmath, 110 digits (the curve), **Arb, 512 bits** (the orbits), mpmath, 60 digits (the threshold) | `W^u` by the graph transform and its Taylor data. 500 seeds on a fundamental domain `[1e-7, 6.27e-7)`, followed to the exit; per arc the switching time, the exit time `eps log Y`, the signs of `SwitchEntersE2`, `ArcSwitchesToE1`, `ArcLeavesStarDomain`, and `K`. The threshold `s*` by bisection | all 500 orbits switch cyclically and then exit, with every sign decided in balls. Rigorous for each seed phase point; the seeds lie on `W^u` only to about `1e-26` (not certified) |
| 2 `checks/arc_invariant.py` (`arcinv`, 20 s) | mpmath, 60 digits (sampled, not rigorous) | (INV) on 45,760 samples (a grid and random points, down to `r = 3e-10`, and to within `1e-10` to `3e-8` of the faces E, P1, P2, P4 of `G*` in the natural scales), both roots `q` of (3.1); the sharp form (Theorem 6.5), Lemmas 6.1 (ii), 6.2 and 6.3, `rel = 0` at the image; 400 images against the closed-form flow | 0 failures among 63,530 switching points: 57,811 images in `G*`, 7,621 exit, 1,902 both |
| 3 `checks/arc_certificates.py` (`arccert`, 1 s) | sympy, exact | 4 `linear_combination` cofactor identities read off the Lean source, `rel_eq`, and the identities of §6 of the note (the rearranged relation and `D` of Lemma 6.1, the closed forms of Lemma 6.2, `psi` of Lemma 6.3, the derivatives and `G(16/5)` of Lemma 6.4), some with the Lean definitions of `YNew`, `YNew'`, `pNew`, `psiE` | all hold |

The figure's numbers:

| quantity | book | here |
| --- | --- | --- |
| `x~21` at the fixed point | `-2.39` | `-2.388856` (`x~_out`) |
| end point of the curve of switching points | `(0.21, -3.03)` | `(0.209847, -3.033319)`, on the boundary `x~21 = sqrt3 - 1/r` |
| threshold: an arc from `r >= r*` exits before switching | "about 0.065" (TeX comment: `0.0641`) | `r* = 0.0649466`; the largest switching point has `r = 0.064764`, the smallest exit point `r = 0.064970` |
| `K` from `r in [1e-3, 6.21e-3)` | not stated (the Lean docstring: 2 or 3) | `K = 2` for 327 orbits, `K = 3` for 173 (`K = 7` or `8` from the seeds) |
| `v = gamma'(0)`, `gamma''(0)/2` | | `(-1.0777706, -13.389650, 3.9345535)`, `(-2.601, -35.98, 7.535)` |

Margins. On `W^u`, at `r < 0.01` in the natural scales: `f0/r^3 >= 6.63`, `p/r^2 >= 2.25`,
`-q/r^2 >= 9.6`, `-F(log Y) >= 0.1137`, `-f'(tau_sw)/r^2 >= 81`, `E/r >= 5.4`. On the exit arcs,
`min F on [0, log Y] = 1.55e-4`, attained next to the threshold. There the switch and the exit
coincide, and `F(log Y)` is linear in `log s` with slope `0.3731`. Below `s*` the next arc is a cusp
arc (`eps = 2.5e-4, 2.5e-9, 2.5e-17` at `s*(1 - delta)`, `delta = 1e-3, 1e-8, 1e-16`) and it exits.
Each exit arc is also covered by a Lean lemma: Proposition 4.4 (3) (451 of 500), Lemma 6.4 (440).
In (INV), the smallest `max(in, exit)` margin is `0.0417`, at the corner `x = y = 1e-9`,
`f0/y^3 = p/y^2 = 1e-8` (on the smaller root, `q = -1.5 y`). Where `psi(s) < 0`,
`Y_new >= 3.2853` (`>= 16/5`, Lemma 6.3). At the images, Lemma 6.2 holds with
`1 - 2 p_new/((2Y'_new - 1)(Y'_new - 2)) >= 0.784`, and Lemma 6.1 (ii) with
`(f0 - q(1 - 1/Y))/f0 >= 0.498`. The closed forms agree with `step` and with the flow to `1e-34`.

Findings: no disagreement with the Lean statements. At every sampled image of `G*`, `q_new` is the
larger root of `R = 0` (63,530 of 63,530, whichever root the point itself was on), as the review
found on 72 points (`ArcPoincareMap.lean`); the Lean proof does not need to know which. The
four-term normal form (Theorem 2.3), the section conditions at the images, the slope
`-2 sqrt3 p/(Y' - 1)` and Theorem 5.1 with `q_new = Phi(s)/(Y - s)^2` (computed here) all hold along the orbits within the balls (radii `<= 4e-65`).
