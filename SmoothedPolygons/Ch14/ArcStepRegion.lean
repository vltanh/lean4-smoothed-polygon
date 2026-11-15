module

public import SmoothedPolygons.Ch14.ArcStepClosed

/-!
# Chapter 14, N4: E at the image decides the next point (the proof of (INV), II)

`notes/inv/inv.md` Propositions 3 and 4: statements about real numbers only (no flows). With
`s = e^{τ_sw}` the switch of a point of `𝒢*` and `ψ(s)` the cubic of Corollary 1.2 (`psiE`,
`E_new_iff`):
* if `ψ(s) ≥ 0` (E holds at the image), then `Φ(s) ≤ 0`, i.e. P2 holds at the image
  (`Phi_nonpos`, Proposition 3), so the image is again in `𝒢*`;
* if `ψ(s) < 0` (E fails at the image), then `Y_new ≥ 16/5` (`YNew_ge`, Proposition 4), and the
  next arc exits (Lemma 6, `SmoothedPolygons/Ch14/ArcStepExit.lean`).
Part of the proof of (INV) (`arcRegionInvariant`, `SmoothedPolygons/Ch14/ArcRegionInvariant.lean`).

**Departure from the paper.** The book computes the unstable curve numerically (Figure 14.2,
TeX 11951–11991); the formalization proves N4 from (INV) by the exact structure of the arcs (see
`SmoothedPolygons/Ch14/ArcParams.lean`), and (INV) by the argument of `notes/inv/inv.md`.

## Notation

As in `SmoothedPolygons/Ch14/ArcStepClosed.lean`; inv.md's real variables `a, b, c` are written
`x = Y - 2`, `y = Y' - 2`, `z = s - Y + 1` here (the structure is `a`), and `σ = s - 1 = x + z`.
`φ(s) = (Y' - 1) s³ - (2Y' + 1) s² + (2Y + 1) s - (Y - 1)`,
`Q(s) = (2Y' - 1) s² - (YY' + Y' + 1) s + 2Y`. Every identity below is a polynomial identity
(`ring` or `linear_combination`), checked exactly in `notes/inv/verify.py` §3–§4,
`notes/n4rev/t8_inv_exact.py`, and as written here (with the certificate) in
`notes/n4s2/docs_check.py`.
-/

@[expose] public section

namespace SmoothedPolygons

namespace ArcParams

variable (a : ArcParams)

/-- **inv.md Proposition 3** (E at the image implies P2 at the image). Let `Y - 2 > 0`,
`Y' - 2 > 0`, E (`(Y - 1)(Y' - 2) ≤ Y - 2`), P1 and P2 and P4 in the weak form (`f₀ ≥ 0 ≥ q`,
`p ≥ 0`), the relation `R̃ = 0`, `Y - 1 ≤ s < Y`, `π(s) = s² - Y s + B ≥ 0` and `ψ(s) ≥ 0`. Then
`Φ(s) ≤ 0`; sharper, `(3 - xy) Φ(s) ≤ (s - 1) P₁ ≤ -(3/2)(s - 1) ψ(s) ≤ 0` with
`P₁ = (3 - xy) s Q(s) + s² y z (YY' - 1)`.

Route (inv.md §3; `x = Y - 2`, `y = Y' - 2`, `z = s - Y + 1`, `σ = s - 1 = x + z`):
1. **Range.** `x > 0`, `y > 0`, `(1 + x) y ≤ x` (E). From `ψ(s) + (Y - s)² = s (Y' s - 1)(2Y - 3s)`
   and `ψ(s) ≥ 0`, `s ≥ Y - 1 > 1`, `Y' s > 1`: `3s < 2Y`. With `s ≥ Y - 1`: `Y < 3`, so `x < 1`,
   and `z ≥ 0`, `x + 3z < 1` (`3z = 3s - 3Y + 3 < 3 - Y = 1 - x`): `(x, z)` lies in the triangle
   `T = {x ≥ 0, z ≥ 0, x + 3z ≤ 1}`. Also `s² - Y < x`, from `s² < 4Y²/9 ≤ 2(Y - 1)`
   (`(2Y - 3)(Y - 3) ≤ 0`), and `y ≤ x/(1 + x) < 1/2`, so `xy < 1/2` and `3 - xy > 0`;
   `YY' - 1 - (3 - xy) = 2x + 2y + 2xy ≥ 0`.
2. **The budget (2.3).** `R̃ = 0` (`relT`) rearranged:
   `2(YY' - 1) y (-q) = (Y'(f₀ - q) - Y p)² + 4p(-q) + 2(YY' - 1) x p + 2Y'(3 - xy) f₀`, hence
   `(YY' - 1) y (-q) ≥ (YY' - 1) x p + Y'(3 - xy) f₀`.
3. **Identities.** (3.1) `Φ(s) = (s - 1) φ(s) + Y' s² f₀ - (Y' s² - 1) q + s² (s² - Y) p`;
   (3.2) `s² - Y s + B = q + (s - 1) z`; (3.3) `φ(s) + z (Y' s² - 1) = s Q(s)`.
4. **The bound on `Φ`.** `(3 - xy)(s² - Y) p ≤ (3 - xy) x p ≤ (YY' - 1) x p` (step 1, `p ≥ 0`), so
   by step 2 `(3 - xy)(Y' s² f₀ + s²(s² - Y) p) ≤ s² (Y'(3 - xy) f₀ + (YY' - 1) x p)
   ≤ s² (YY' - 1) y (-q)`. By (3.2) and `π(s) ≥ 0`, `0 ≤ -q ≤ (s - 1) z`, and the coefficient
   `(3 - xy)(Y' s² - 1) + s² (YY' - 1) y` of `-q` is `≥ 0`. With (3.1) and (3.3):
   `(3 - xy) Φ(s) ≤ (s - 1)[(3 - xy)(φ(s) + z(Y' s² - 1)) + s² y z (YY' - 1)] = (s - 1) P₁`.
5. **(3.4)–(3.5).** In `(x, y, z)` (`Y = 2 + x`, `Y' = 2 + y`, `s = 1 + σ`):
   `Q = -y(1 + x) - σ(1 + 2x + xy - y) + (3 + 2y) σ²`, and
   `-P₁ = (3/2) ψ(s) + K`, `K = (3/2)(x + 2z)² + (y/2)(1 + σ) L₁ + y² (1 + σ)² L₂`,
   `L₁ = 2x³ + 4x²z - 5x² + 2xz² - 18xz - 9z² - 6z + 3`, `L₂ = x(x + z - 1) - 2z`
   (`P₁ = (3 - xy)(1 + σ) Q + (1 + σ)² y z ((2 + x)(2 + y) - 1)`; `ring`).
6. **`K ≥ 0`.** On `T`, `x + z ≤ 1`, so `L₂ ≤ 0`: `K = k₀ + k₁ y + k₂ y²` is concave in `y`
   (`k₂ = (1 + σ)² L₂ ≤ 0`). With `y₁ = x/(1 + x) > 0` and `0 ≤ y ≤ y₁`:
   `y₁ K(y) = (y₁ - y) K(0) + y K(y₁) + y₁ k₂ y (y - y₁)` (the last term `≥ 0`),
   `K(0) = (3/2)(x + 2z)² ≥ 0`, and `(1 + x)² K(y₁) = K̃(x, z)` with
   `K̃ = 2x⁶ + 6x⁵z + (1/2)x⁵ + 6x⁴z² - (13/2)x⁴z - (7/2)x⁴ + 2x³z³ - (25/2)x³z² - (41/2)x³z + x³
   - (11/2)x²z³ - 18x²z² - (7/2)x²z + (9/2)x² - (9/2)xz³ + (9/2)xz² + (9/2)xz + (3/2)x + 6z²`.
7. **The Bernstein certificate of `K̃ ≥ 0` on `T`.** With `λ₀ = 1 - x - 3z`, `λ₁ = x`, `λ₂ = 3z`
   (`λ₀ + λ₁ + λ₂ = 1`, all `≥ 0` on `T`), homogenized to degree 6,
   `K̃ = Σ_{i+j+k=6} c_{ijk} λ₀^i λ₁^j λ₂^k` with (`ijk:c_{ijk}`; the 2 missing ones, `600`, `501`,
   are `0`):
   `006:2/3, 015:6, 024:1069/54, 033:841/27, 042:479/18, 051:46/3, 060:6, 105:8/3, 114:68/3,
   123:1862/27, 132:883/9, 141:209/3, 150:22, 204:4, 213:100/3, 222:90, 231:302/3, 240:83/2,
   303:8/3, 312:145/6, 321:317/6, 330:34, 402:2/3, 411:9, 420:12, 510:3/2`.
   Lean: the expansion is `ring` (substitute `λ₀ + λ₁ + λ₂ = 1` by writing each degree-`< 6`
   monomial of `K̃` times `(λ₀ + λ₁ + λ₂)^{6 - deg}`), then `positivity`.
8. `(3 - xy) Φ(s) ≤ (s - 1) P₁ = -(s - 1)((3/2) ψ(s) + K) ≤ 0` and `3 - xy > 0`.
Margins (numerical, for orientation): `-P₁ ≥ 0.80 (x + y + z)` on the region; the bound is within
20% of `q_new` at images. -/
theorem Phi_nonpos (ha : 0 < a.Y - 2) (hb : 0 < a.Y' - 2) (hE : (a.Y - 1) * (a.Y' - 2) ≤ a.Y - 2)
    (h1 : 0 ≤ a.f0) (h2 : a.q ≤ 0) (h4 : 0 ≤ a.p) (hR : a.relT = 0) {s : ℝ}
    (hs1 : a.Y - 1 ≤ s) (hs2 : s < a.Y) (hpi : 0 ≤ s ^ 2 - a.Y * s + a.B)
    (hpsi : 0 ≤ a.psiE s) : a.Phi s ≤ 0 := by
  sorry

/-- **inv.md Proposition 4** (E fails at the image implies `Y_new ≥ 16/5`). If `Y > 2`, `Y' > 2`,
`Y - 1 ≤ s < Y` and `ψ(s) < 0`, then `Y_new = (Y' s² - 2s + Y)/(Y - s) ≥ 16/5`.

Route (inv.md §4; `x = Y - 2`, `y = Y' - 2`, `N_Y(s) = Y' s² - 2s + Y`). Suppose `Y_new(s) < 16/5`.
1. `Y_new` increases on `[1, Y)`: for `1 ≤ s' ≤ s < Y`,
   `N_Y(s)(Y - s') - N_Y(s')(Y - s) = (s - s')(Y'(Y(s + s') - s s') - Y)` and
   `Y'(Y(s + s') - s s') - Y ≥ Y(Y' s - 1) > 0` (`dY_new/ds = (Y' s(2Y - s) - Y)/(Y - s)²`).
2. `ψ'(s) = s(4YY' + 4 - 9Y' s)`: `ψ` increases on `(0, m]` and decreases on `[m, ∞)`,
   `m = (4YY' + 4)/(9Y')`, so on an interval `[s₁, s₂] ⊂ (0, ∞)`, `ψ ≥ min(ψ(s₁), ψ(s₂))`
   (algebraically: `ψ(u) - ψ(v) = (u - v)(-3Y'(u² + uv + v²) + (2YY' + 2)(u + v))`).
3. `χ(s) := Y' s² + (6/5) s - (11/5) Y = (Y - s)(Y_new(s) - 16/5)` increases on `(0, ∞)` and has
   one positive root `s_χ < Y` (`χ(0) < 0 < χ(Y)`); `χ(s) < 0`, so `Y - 1 ≤ s < s_χ`.
4. At `s_χ`: `Y_new = 16/5`, and E at the image reads `Y'_new ≤ 28/11`, i.e. `s_χ ≤ (17/28) Y`,
   i.e. `χ((17/28) Y) ≥ 0`; `χ((17/28) Y) = Y((289/784) YY' - 103/70)` and
   `YY' > 4 > 5768/1445 = (103/70)(784/289)`. So E holds at the image at `s_χ`, i.e.
   `ψ(s_χ) ≥ 0` (`E_new_iff`). (Directly:
   `ψ(s_χ) = (Y - s_χ)²((Y_new - 2) - (Y_new - 1)(Y'_new - 2))` with `Y_new = 16/5`.)
5. At `Y - 1`: `Y_new(Y - 1) = 2 + 3x + 2x² + y(1 + x)² ≤ Y_new(s) < 16/5` (step 1) forces
   `3x + 2x² < 6/5`, so `x < 1/3` (`3/3 + 2/9 = 11/9 > 6/5`), and
   `ψ(Y - 1) = x(2 - x - 2x²) + y(1 + x)²(1 - x) > 0`.
6. By step 2 on `[Y - 1, s_χ]`, `ψ(s) ≥ 0`: a contradiction.
Margin (numerical): the infimum of `Y_new` over `{ψ(s) < 0, s ≥ Y - 1}` is `3.21525` (Fuller corner
`Y = Y' = 2`, `s = (1 + √7)/3`); `16/5` is used because it exceeds the root `Y_* = 3.16258` of
`g(Y) = Y log Y - (Y - 1) - (Y - 1)²/Y` (Lemma 6). -/
theorem YNew_ge (hY : 2 < a.Y) (hY' : 2 < a.Y') {s : ℝ} (hs1 : a.Y - 1 ≤ s) (hs2 : s < a.Y)
    (hpsi : a.psiE s < 0) : 16 / 5 ≤ a.YNew s := by
  sorry

end ArcParams

end SmoothedPolygons
