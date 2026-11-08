/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import LeanPool.AaronsonAmbainis.Defs

/-!
# The statements of the chain, as propositions

The links of the proof are stated here as propositions. All of them except `RowBound` and
`MainTheoremImproved` are proved, with no hypothesis, in the directories `DetLow`, `DetBij`,
`TwoSided`, `Level`, `Average` and `Row` and in `MainTheorem.lean`; the proofs are assembled in
`Chain.lean`. Numbering refers to the paper.

* `DetInequality`       — the determinant inequality (Corollary 3.2)
* `AntipodalInequality` — the antipodal inequality (Theorem 4.3)
* `TwoSidedInequality`  — the two-sided inequality (Theorem 5.4)
* `IntegratedAllPairsInequality` — the integrated all-pairs inequality, for a real function with
                          a row at every point (Proposition 7.4)
* `ThirdMomentInequality` — the third-moment inequality (Theorem 7.6)
* `MeanIncrementBound`  — the bound for the mean absolute increments of a function with rows of
                          cost at most `K` (Theorem 7.10)
* `InfluenceBound`      — the bound for the influences of a function with rows of cost at most
                          `K` (Theorem 8.3)
* `SensitivityBound`    — the sensitivity of a bounded function of degree at most `d`, at every
                          point (Corollary 6.10)
* `MainTheorem`         — the main theorem (Theorem 1.1)
* `MeanIncrementDegreeBound` — the bound for the mean absolute increments of a bounded function
                          of degree at most `d` (Corollary 7.11)
* `RowBound`            — the row bound of Agarwal and Ben-David (Theorem 1.7 of
                          arXiv:2410.19062); it is not proved in this project and is used
                          only as a named hypothesis, never as an axiom
* `MainTheoremImproved` — the main theorem with the constant that `RowBound` gives
                          (Remark 8.4); it is proved from `RowBound`

The all-pairs inequality for Boolean functions (Proposition 5.2) is stated in
`AllPairsDefs.lean`, the two halves of the proof of the determinant inequality in `DetDefs.lean`,
and the links of the proof of the row bound (Theorem 6.8) in `RowDefs.lean`.

A row of a real function `f` at every point is given as a family `a : Cube ι → ι → ℝ` with
`0 ≤ a x j` and `|f x - f y| ≤ ∑_{j ∈ Δ(x,y)} a x j` for all `x`, `y`; its cost at `x` is
`∑_j a x j`. (This is Definition 2.3 of the paper, with `y = x^S` and `S = Δ(x,y)`.) The mean
absolute increment of `f` in the coordinate `j` is `L_j(f) = meanAbsIncr f j = E_x |f x - f (x^j)|`,
and `L(f) = ∑_j L_j(f)`.
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

/-- The determinant inequality (Corollary 3.2 of the paper).
For every Boolean `g`, all positive lengths `ℓ`, and every choice of
1-wings `A u` at the points `u` of `zone g`: if `d u` is at most the length of every
`G` disjoint from `A u` with `g ((antipode u)^G) = true`, then `∑_{u ∈ zone g} d u`
is at most `∑_j ℓ_j b_j(g)`.  (So `d u` may be taken to be the minimum `D_g(u, A u; ℓ)`.) -/
def DetInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (ℓ : ι → ℝ), (∀ j, 0 < ℓ j) →
  ∀ (A : Cube ι → Finset ι), (∀ u ∈ zone g, IsWing g u (A u)) →
  ∀ (d : Cube ι → ℝ),
    (∀ u ∈ zone g, ∀ G : Finset ι, Disjoint G (A u) →
        g (flipSet (antipode u) G) = true → d u ≤ ∑ j ∈ G, ℓ j) →
    ∑ u ∈ zone g, d u ≤ ∑ j, ℓ j * (bdry g j : ℝ)

/-- The antipodal inequality (the inequality of Theorem 4.3 of the paper).
For every Boolean `g`, all positive weights `w` and every row field `lam`:
`∑_{u ∈ zone g} 1 / (∑_j w_j lam^u_j lam^{ū}_j) ≤ ∑_j b_j(g) / w_j`.
(The reciprocal is `⁻¹`, with `0⁻¹ = 0` in Lean; that the denominators are positive is the other
assertion of Theorem 4.3 and is not part of this proposition.) -/
def AntipodalInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (w : ι → ℝ), (∀ j, 0 < w j) →
  ∀ (lam : Cube ι → ι → ℝ), (∀ x, IsRow g x (lam x)) →
    ∑ u ∈ zone g, (∑ j, w j * lam u j * lam (antipode u) j)⁻¹ ≤ ∑ j, (bdry g j : ℝ) / w j

/-- The two-sided inequality (the inequality of Theorem 5.4 of the paper).
For every Boolean `g` and every row field `lam`, with `v x = 1 / ‖lam x‖₁`:
`4 · E[v · 1_{g = true}] · E[v · 1_{g = false}] ≤ τ` whenever `τ ≥ 0` bounds all influences
`I_j(g)`. (In the paper `g` is not constant and `τ = max_j I_j(g)`.) -/
def TwoSidedInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (lam : Cube ι → ι → ℝ),
    (∀ x, IsRow g x (lam x)) →
  ∀ τ : ℝ, 0 ≤ τ → (∀ j, infl g j ≤ τ) →
    4 * ((∑ x ∈ univ.filter (fun x : Cube ι => g x = true), (∑ j, lam x j)⁻¹) / 2 ^ Fintype.card ι)
      * ((∑ x ∈ univ.filter (fun x : Cube ι => g x = false), (∑ j, lam x j)⁻¹) / 2 ^ Fintype.card ι)
      ≤ τ

/-- The integrated all-pairs inequality (the inequality of Proposition 7.4 of the paper). For a
real function `f` on the cube, a row `a x` of `f` at every point `x` and all positive weights `w`:
`∑_{(x,y) : f y < f x} (f x - f y)^3 / (6 s_xy) ≤ 4^(n-1) ∑_j L_j(f) / w_j`, where
`s_xy = ∑_{j ∈ Δ(x,y)} w_j a^x_j a^y_j` and `L_j(f) = meanAbsIncr f j = E_x |f x - f (x^j)|`.
(That the sums `s_xy` in the denominators are positive is the other assertion of
Proposition 7.4: `Level.pairSum_pos`. The exponent `n - 1` is a difference of natural numbers;
for `n = 0` it is `0`, and both sides of the inequality are `0`.) -/
def IntegratedAllPairsInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ),
    (∀ x j, 0 ≤ a x j) → (∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) →
  ∀ (w : ι → ℝ), (∀ j, 0 < w j) →
    ∑ x, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)
      ≤ 4 ^ (Fintype.card ι - 1) * ∑ j, meanAbsIncr f j / w j

/-- The third-moment inequality (the first inequality of Theorem 7.6 of the paper). If `f` has a
row of cost at most `K` at every point and `M ≥ 0` bounds all the mean absolute increments
`L_j(f) = meanAbsIncr f j`, then for every real `r`
`E[((f - r)⁺)^3] · Pr[f ≤ r] ≤ (3/2) K² M`. (The second inequality of Theorem 7.6, for `(r - f)⁺`
and `Pr[f ≥ r]`, is this one for `-f` and `-r`: `Level.thirdMoment_lower`.) -/
def ThirdMomentInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (K : ℝ) (a : Cube ι → ι → ℝ),
    (∀ x j, 0 ≤ a x j) → (∀ x, ∑ j, a x j ≤ K) →
    (∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) →
  ∀ (M : ℝ), 0 ≤ M → (∀ j, meanAbsIncr f j ≤ M) → ∀ r : ℝ,
    (∑ x, max (f x - r) 0 ^ 3) / 2 ^ Fintype.card ι
        * (((univ.filter (fun y : Cube ι => f y ≤ r)).card : ℝ) / 2 ^ Fintype.card ι)
      ≤ 3 / 2 * K ^ 2 * M

/-- The bound for the mean absolute increments (Theorem 7.10 of the paper). If `f` has a row of
cost at most `K` at every point and `Var(f) > 0`, then some coordinate `j` has
`Var(f)^3 ≤ 36 K^4 L_j(f)^2`, that is, `E_x |f(x) - f(x^j)| ≥ Var(f)^{3/2} / (6 K²)`. No bound on
the values of `f` is assumed. (The other assertions of Theorem 7.10, `n ≥ 1` and `K > 0`, hold
because the variance is positive; `K > 0` is `Level.cost_pos`. The statement of the paper with
all its assertions is `Bridge.MeanIncrementPrinted`.) -/
def MeanIncrementBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (K : ℝ) (a : Cube ι → ι → ℝ),
    (∀ x j, 0 ≤ a x j) → (∀ x, ∑ j, a x j ≤ K) →
    (∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) → 0 < variance f →
    ∃ j, variance f ^ 3 ≤ 36 * K ^ 4 * meanAbsIncr f j ^ 2

/-- The bound for the influences (Theorem 8.3 of the paper). If `f` has a row of cost at most `K`
at every point and `Var(f) > 0`, then some coordinate `j` has
`3 Var(f)^5 ≤ 3125 L(f)² K^4 Inf_j(f)^2`, where `L(f) = ∑_k L_k(f)` is the sum of the mean
absolute increments; that is, `Inf_j(f) ≥ (√15 / 125) Var(f)^{5/2} / (L(f) K²)`. No bound on the
values of `f` is assumed. (The other assertions of Theorem 8.3: `0 < L(f)` is
`Average.sum_meanAbsIncr_pos`, and `L(f) ≤ K` is `Level.sum_meanAbsIncr_le_cost`. The statement
of the paper with all its assertions is `Bridge.InfluencePrinted`.) -/
def InfluenceBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (K : ℝ) (a : Cube ι → ι → ℝ),
    (∀ x j, 0 ≤ a x j) → (∀ x, ∑ j, a x j ≤ K) →
    (∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) → 0 < variance f →
    ∃ j, 3 * variance f ^ 5 ≤ 3125 * (∑ k, meanAbsIncr f k) ^ 2 * K ^ 4 * inflR f j ^ 2

/-- The sensitivity bound at every point (Corollary 6.10 of the paper). If `|f| ≤ 1` and `f` has
degree at most `d`, then `∑_j |f(x) - f(x^j)| ≤ 4 d²` at every point `x`. (Consequently
`L(f) ≤ 4 d²`: `Level.sum_meanAbsIncr_le`.) -/
def SensitivityBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → ∀ x : Cube ι, ∑ j, |f x - f (flipSet x {j})| ≤ 4 * (d : ℝ) ^ 2

/-- The main theorem (Theorem 1.1 of the paper). Every `f` on the cube with `|f| ≤ 1`, degree at
most `d` and positive variance has a coordinate `j` with
`3 Var(f)^5 ≤ 50000 π^8 d^12 Inf_j(f)^2`, that is,
`Inf_j(f) ≥ (√15 / (500 π^4)) Var(f)^{5/2} / d^6`. (The paper assumes `n ≥ 1` and `d ≥ 1` in place
of positive variance; these hold when the variance is positive, and for variance `0` there is
nothing to prove.) -/
def MainTheorem : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → 0 < variance f →
    ∃ j, 3 * variance f ^ 5 ≤ 50000 * Real.pi ^ 8 * (d : ℝ) ^ 12 * inflR f j ^ 2

/-- The bound for the mean absolute increments of a bounded function of low degree
(Corollary 7.11 of the paper). Every `f` on the cube with `|f| ≤ 1`, degree at most `d` and
positive variance has a coordinate `j` with `Var(f)^3 ≤ 36 π^8 d^8 L_j(f)^2`, that is,
`E_x |f(x) - f(x^j)| ≥ Var(f)^{3/2} / (6 π^4 d^4)`. -/
def MeanIncrementDegreeBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → 0 < variance f →
    ∃ j, variance f ^ 3 ≤ 36 * Real.pi ^ 8 * (d : ℝ) ^ 8 * meanAbsIncr f j ^ 2

/-- The row bound of Agarwal and Ben-David (Theorem 1.7 of arXiv:2410.19062): every
`f : {0,1}^n → [0,1]` of degree at most `d` has weights `c x i` with
`∑_{i : x_i ≠ y_i} c x i ≥ |f x - f y|` for all `x, y` and `∑_i c x i ≤ (π²/4) d²` for all `x`.
(Nonnegativity of the weights is not required: it follows from the first condition
with `y = x^i`.) This proposition is not proved in the project; it occurs only as a
hypothesis. -/
def RowBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ),
    (∀ x, 0 ≤ f x ∧ f x ≤ 1) → HasDegreeLE f d →
    ∃ c : Cube ι → ι → ℝ,
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2)

/-- The main theorem with the constant that the row bound of Agarwal and Ben-David gives
(Remark 8.4 of the paper). Every `f` on the cube with `|f| ≤ 1`, degree at most `d` and positive
variance has a coordinate `j` with `3 Var(f)^5 ≤ 3125 π^8 d^12 Inf_j(f)^2`, that is,
`Inf_j(f) ≥ (√15 / (125 π^4)) Var(f)^{5/2} / d^6`. It is proved from the hypothesis `RowBound`. -/
def MainTheoremImproved : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → 0 < variance f →
    ∃ j, 3 * variance f ^ 5 ≤ 3125 * Real.pi ^ 8 * (d : ℝ) ^ 12 * inflR f j ^ 2

end AaronsonAmbainis
