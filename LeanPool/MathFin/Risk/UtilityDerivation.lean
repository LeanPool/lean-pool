/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Utility.VonNeumannMorgenstern
public import LeanPool.MathFin.Risk.AcceptanceSet
public import LeanPool.MathFin.Choice.Performance.Ratios

/-!
# Acceptance sets of an expected-utility agent: convex, not coherent

On a finite state space with probability vector `p`, an agent with utility `u` and wealth `W`
**accepts** a position `X` when it does not lower expected utility: `u(W) ≤ E[u(W + X)]`
(`acceptableUnderUtility`). The expectation is the von Neumann–Morgenstern expected utility
`expectedUtility` of `Choice/Utility/VonNeumannMorgenstern.lean`, taken over the outcome utilities
`i ↦ u(W + X i)`.

Two properties of the acceptance set follow from properties of `u`:

* a **concave** `u` makes it **convex** (`acceptableUnderUtility_convex`): a mixture of two
  acceptable positions is acceptable;
* an **increasing** `u` makes it closed under adding nonnegative cash
  (`acceptableUnderUtility_monotone_translation`).

A convex acceptance set gives a *convex* risk measure `ρ(X) = inf {m | X + m acceptable}`
(Föllmer and Schied, *Convex measures of risk and trading constraints*, Finance Stoch. 6 (2002),
429–447, whose case study is the shortfall risk of an expected-loss constraint). It does not give
a *coherent* one. The acceptance set of a coherent risk measure is a cone
(`IsCoherentRiskMeasure.cone`, `Risk/AcceptanceSet.lean`; a loss `L` is acceptable when
the position `−L` is), and a risk-averse utility's acceptance set need not be one:
`not_exists_isCoherentRiskMeasure_log_acceptance` exhibits a position that log utility accepts
while rejecting three times that position, so no coherent risk measure has that acceptance set.
Neither the construction of `ρ` from the acceptance set nor its convexity is formalized here.

The von Neumann–Morgenstern layer gives two more facts about acceptance:

* it depends on `u` only up to a positive affine map (`acceptableUnderUtility_affine_iff`, from
  `expectedUtility_affine`);
* a position acceptable under each of two probability vectors is acceptable under every mixture
  of them (`acceptableUnderUtility_mix`, from `expectedUtility_mix`).

Log utility at unit wealth is the Kelly criterion: a binary bet of fraction `f` at odds `b` is
acceptable exactly when its expected log-growth `kellyGrowth p b f`
(`Choice/Performance/Ratios.lean`) is
nonnegative (`acceptableUnderUtility_log_iff_kellyGrowth`). The counterexample above is a Kelly bet
on a fair coin at odds `2`: the fraction `1/4` has positive growth, the fraction `3/4` negative.

## Main definitions

* `acceptableUnderUtility`: a position `X` on a finite state space with probability vector `p`
  is acceptable under utility `u` at wealth `W` when `u(W) ≤ E[u(W + X)]`.

## Main results

* `acceptableUnderUtility_convex`, `acceptableUnderUtility_monotone_translation`,
  `acceptableUnderUtility_zero`.
* `acceptableUnderUtility_affine_iff`, `acceptableUnderUtility_mix`.
* `acceptableUnderUtility_log_iff_kellyGrowth`.
* `not_exists_isCoherentRiskMeasure_log_acceptance`: the log-utility acceptance set of the fair
  coin is the acceptance set of no coherent risk measure.

## References

* [P. Artzner et al., *Coherent measures of risk*][ArtznerDelbaenEberHeath1999]
* [H. Föllmer and A. Schied, *Convex measures of risk and trading constraints*][FollmerSchied2002]
* [J. L. Kelly, *A new interpretation of information rate*][Kelly1956]

## Tags

acceptance set, expected utility, convex risk measure, Föllmer-Schied, log utility, Kelly criterion,
risk aversion, MSC 91B16, MSC 91G70, JEL D81
-/

@[expose] public section

namespace MathFin

/-- A position `X : ι → ℝ` is **acceptable under utility `u` at wealth `W`** if its expected
utility is at least that of doing nothing: `u(W) ≤ E[u(W + X)]`, the expected utility
`expectedUtility s (fun i ↦ u (W + X i)) p` of the outcome utilities under the probability
vector `p`. -/
def acceptableUnderUtility {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (u : ℝ → ℝ) (W : ℝ) (X : ι → ℝ) : Prop :=
  u W ≤ expectedUtility s (fun i ↦ u (W + X i)) p

/-- **Concave utility gives a convex acceptance set**: if `u` is concave and `X`, `Y` are
acceptable, so is every convex combination `αX + (1 − α)Y`.

Pointwise concavity gives `α u(W + X) + (1 − α) u(W + Y) ≤ u(W + αX + (1 − α)Y)` in every state.
Taking expectations with `p ≥ 0` and using `u(W) ≤ E[u(W + X)]`, `u(W) ≤ E[u(W + Y)]` gives the
claim. A convex acceptance set is the acceptance set of a convex risk measure (not formalized
here); it need not be the acceptance set of a coherent one
(`not_exists_isCoherentRiskMeasure_log_acceptance`). -/
theorem acceptableUnderUtility_convex
    {ι : Type*} (s : Finset ι) (p : ι → ℝ) (u : ℝ → ℝ) (W : ℝ)
    (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (h_concave : ∀ x y : ℝ, ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      α * u x + (1 - α) * u y ≤ u (α * x + (1 - α) * y))
    {X Y : ι → ℝ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hX : acceptableUnderUtility s p u W X)
    (hY : acceptableUnderUtility s p u W Y) :
    acceptableUnderUtility s p u W (fun i ↦ α * X i + (1 - α) * Y i) := by
  simp only [acceptableUnderUtility, expectedUtility] at *
  have h_sum : ∑ i ∈ s, p i * (α * u (W + X i) + (1 - α) * u (W + Y i)) ≤
      ∑ i ∈ s, p i * u (W + (α * X i + (1 - α) * Y i)) :=
    Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left
      ((h_concave (W + X i) (W + Y i) α hα hα1).trans_eq (congrArg u (by ring))) (hp_nonneg i hi)
  have h_LHS : ∑ i ∈ s, p i * (α * u (W + X i) + (1 - α) * u (W + Y i)) =
      α * (∑ i ∈ s, p i * u (W + X i)) + (1 - α) * (∑ i ∈ s, p i * u (W + Y i)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [h_LHS] at h_sum
  linarith [mul_le_mul_of_nonneg_left hX hα, mul_le_mul_of_nonneg_left hY (sub_nonneg.2 hα1)]

/-- **Increasing utility: more cash stays acceptable**. If `u` is monotone and `X` is
acceptable, then `X + c` is acceptable for every `c ≥ 0`: in every state
`u(W + X) ≤ u(W + X + c)`, and expectations with `p ≥ 0` preserve the inequality. -/
theorem acceptableUnderUtility_monotone_translation
    {ι : Type*} (s : Finset ι) (p : ι → ℝ) (u : ℝ → ℝ) (W : ℝ)
    (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (h_mono : Monotone u)
    {X : ι → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hX : acceptableUnderUtility s p u W X) :
    acceptableUnderUtility s p u W (fun i ↦ X i + c) := by
  simp only [acceptableUnderUtility, expectedUtility] at *
  refine hX.trans (Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left ?_ (hp_nonneg i hi))
  exact h_mono (by linarith)

/-- **Doing nothing is acceptable**: for a probability vector, the zero position has expected
utility `u(W)`. -/
theorem acceptableUnderUtility_zero
    {ι : Type*} (s : Finset ι) (p : ι → ℝ) (u : ℝ → ℝ) (W : ℝ)
    (h_p_sum : ∑ i ∈ s, p i = 1) :
    acceptableUnderUtility s p u W (fun _ ↦ 0) := by
  simp only [acceptableUnderUtility, expectedUtility, add_zero]
  rw [← Finset.sum_mul, h_p_sum, one_mul]

/-- **Acceptance depends on the utility only up to a positive affine map**: for a probability
vector `p`, the utilities `u` and `a·u + b` with `a > 0` accept the same positions. This is the
cardinality of von Neumann–Morgenstern utility (`expectedUtility_affine`) read on acceptance
sets. -/
theorem acceptableUnderUtility_affine_iff {ι : Type*} (s : Finset ι) {p : ι → ℝ}
    (hp : ∑ i ∈ s, p i = 1) (u : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (b W : ℝ) (X : ι → ℝ) :
    acceptableUnderUtility s p (fun x ↦ a * u x + b) W X ↔
      acceptableUnderUtility s p u W X := by
  simp only [acceptableUnderUtility]
  rw [expectedUtility_affine s (fun i ↦ u (W + X i)) a b hp, add_le_add_iff_right,
    mul_le_mul_iff_of_pos_left ha]

/-- **Acceptance survives mixing the probability vectors**: a position acceptable under each of
the probability vectors `p` and `q` is acceptable under every mixture `mix α p q` with
`α ∈ [0, 1]`, because expected utility is affine in the mixture (`expectedUtility_mix`). -/
theorem acceptableUnderUtility_mix {ι : Type*} (s : Finset ι) {p q : ι → ℝ} (u : ℝ → ℝ)
    (W : ℝ) {X : ι → ℝ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hp : acceptableUnderUtility s p u W X) (hq : acceptableUnderUtility s q u W X) :
    acceptableUnderUtility s (mix α p q) u W X := by
  unfold acceptableUnderUtility at *
  rw [expectedUtility_mix]
  linarith [mul_le_mul_of_nonneg_left hp hα, mul_le_mul_of_nonneg_left hq (sub_nonneg.2 hα1)]

/-! ### Log utility and the Kelly criterion -/

/-- **A Kelly bet under log utility**: on two states, win (`0`, probability `p`) and lose (`1`),
betting the fraction `f` of unit wealth at odds `b` is the position `(f·b, −f)`. Under log utility
it is acceptable exactly when its expected log-growth `kellyGrowth p b f` is nonnegative. -/
theorem acceptableUnderUtility_log_iff_kellyGrowth (p b f : ℝ) :
    acceptableUnderUtility Finset.univ ![p, 1 - p] Real.log 1 ![f * b, -f] ↔
      0 ≤ kellyGrowth p b f := by
  have h : acceptableUnderUtility Finset.univ ![p, 1 - p] Real.log 1 ![f * b, -f] ↔
      0 ≤ p * Real.log (1 + f * b) + (1 - p) * Real.log (1 + -f) := by
    simp [acceptableUnderUtility, expectedUtility]
  rw [h, kellyGrowth, sub_eq_add_neg 1 f]

/-- On a fair coin at odds `2`, betting a quarter of wealth has positive expected log-growth:
`(log (3/2) + log (3/4))/2 = log (9/8)/2 > 0`. -/
lemma kellyGrowth_half_two_quarter_pos : 0 < kellyGrowth (1 / 2) 2 (1 / 4) := by
  have h := Real.log_mul (x := 3 / 2) (y := 3 / 4) (by norm_num) (by norm_num)
  rw [show (3 / 2 : ℝ) * (3 / 4) = 9 / 8 by norm_num] at h
  rw [kellyGrowth, show (1 : ℝ) + 1 / 4 * 2 = 3 / 2 by norm_num,
    show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num]
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 9 / 8)]

/-- On a fair coin at odds `2`, betting three quarters of wealth has negative expected
log-growth: `(log (5/2) + log (1/4))/2 = log (5/8)/2 < 0`. -/
lemma kellyGrowth_half_two_three_quarters_neg : kellyGrowth (1 / 2) 2 (3 / 4) < 0 := by
  have h := Real.log_mul (x := 5 / 2) (y := 1 / 4) (by norm_num) (by norm_num)
  rw [show (5 / 2 : ℝ) * (1 / 4) = 5 / 8 by norm_num] at h
  rw [kellyGrowth, show (1 : ℝ) + 3 / 4 * 2 = 5 / 2 by norm_num,
    show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num]
  linarith [Real.log_neg (by norm_num : (0 : ℝ) < 5 / 8) (by norm_num)]

/-- **The log-utility acceptance set is not a cone, so no coherent risk measure has it.** On a
fair coin at unit wealth, log utility accepts the Kelly bet `X = (1/2, −1/4)` (fraction `1/4` at
odds `2`, positive expected log-growth) and rejects `3X = (3/2, −3/4)` (fraction `3/4`, negative
growth). A loss `L` is acceptable when the position `−L` is. The acceptance set `{L | ρ L ≤ 0}` of
a coherent risk measure, for any finite measure on the two states, is closed under nonnegative
scaling (`IsCoherentRiskMeasure.cone`), so it is not the set of losses of acceptable positions.
Log utility is concave on positive wealth, and both positions keep wealth positive: risk aversion
makes an acceptance set convex (`acceptableUnderUtility_convex`), not a cone. -/
theorem not_exists_isCoherentRiskMeasure_log_acceptance :
    ¬∃ (P : MeasureTheory.Measure (Fin 2)) (_ : MeasureTheory.IsFiniteMeasure P)
        (ρ : (Fin 2 → ℝ) → ℝ),
      IsCoherentRiskMeasure P ρ ∧
      ∀ L, ρ L ≤ 0 ↔ acceptableUnderUtility Finset.univ ![1 / 2, 1 / 2] Real.log 1 (-L) := by
  rintro ⟨P, _, ρ, hρ, hA⟩
  rw [show (![1 / 2, 1 / 2] : Fin 2 → ℝ) = ![1 / 2, 1 - 1 / 2] by norm_num] at hA
  have hX : -(![1 / 4 * 2, -(1 / 4)] : Fin 2 → ℝ) ∈ {L : Fin 2 → ℝ | ρ L ≤ 0} :=
    (hA _).2 (by
      rw [neg_neg]
      exact (acceptableUnderUtility_log_iff_kellyGrowth _ _ _).2
        kellyGrowth_half_two_quarter_pos.le)
  have h3X : ρ ((3 : ℝ) • -(![1 / 4 * 2, -(1 / 4)] : Fin 2 → ℝ)) ≤ 0 := hρ.cone hX (by norm_num)
  have hv : -((3 : ℝ) • -(![1 / 4 * 2, -(1 / 4)] : Fin 2 → ℝ)) = ![3 / 4 * 2, -(3 / 4)] := by
    norm_num
  rw [hA, hv, acceptableUnderUtility_log_iff_kellyGrowth] at h3X
  exact absurd h3X (not_le.2 kellyGrowth_half_two_three_quarters_neg)

end MathFin
