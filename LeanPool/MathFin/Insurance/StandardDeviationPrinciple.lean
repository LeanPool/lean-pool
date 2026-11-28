/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Insurance.ActuarialInsurance
public import LeanPool.MathFin.Probability.Analysis.FiniteMeasureCauchySchwarz
public import LeanPool.MathFin.Risk.GaussianExpectedShortfall
public import LeanPool.MathFin.Risk.GaussianValueAtRisk

/-!
# The standard-deviation principle: everything but monotonicity

The **standard-deviation principle** prices a loss `X` with finite variance by
`ρ(X) = E[X] + k·sd(X)` for a loading `k ≥ 0` (`stdDevPrinciple`). It is the premium principle
`stdDevPremium` of `Insurance/ActuarialInsurance.lean` evaluated at the mean and standard deviation
of `X`, so a nonnegative loading prices at or above the mean (`integral_le_stdDevPrinciple`). It
satisfies three of the four coherence axioms of `Risk/ExpectedShortfall.lean`, and fails
the fourth (QRM Exercise Book, Exercises 2.19 and 8.11).

* **Translation invariance** (`stdDevPrinciple_add_const`): shifting by cash shifts the mean and
  leaves the standard deviation alone. The standard deviation alone is *not* translation
  invariant (`sqrt_variance_add_const`), which is why the mean term is there.
* **Positive homogeneity** (`stdDevPrinciple_const_mul`).
* **Subadditivity** (`stdDevPrinciple_add_le`): the standard deviation is subadditive because
  covariance obeys the Cauchy–Schwarz inequality `cov(X, Y) ≤ sd(X) sd(Y)`
  (`covariance_le_sqrt_mul_sqrt`, in `Probability/Analysis/FiniteMeasureCauchySchwarz.lean`).
* **Monotonicity fails** (`stdDevPrinciple_not_monotone`): a loss `B ≤ 0` that equals `−1` with a
  small probability `q` and `0` otherwise has `ρ(B) > 0 = ρ(0)` once `q(1 + k²) < k²`. Its rare
  gains inflate the standard deviation more than they lower the mean. This is the counterexample
  of QRM Exercise 8.11.

On Gaussian losses the two standard risk measures are standard-deviation principles. For
`X ~ N(m, v)` and `α ∈ (0, 1)`, `VaR_α(X)` is the principle with loading `Φ⁻¹(α)`
(`stdDevPrinciple_eq_valueAtRisk_of_hasLaw_gaussianReal`), and for `v ≠ 0` `ES_α(X)` is the
principle with loading `ϕ(Φ⁻¹(α))/(1 − α)`, where `ϕ` is the standard normal density
(`stdDevPrinciple_eq_expectedShortfall_of_hasLaw_gaussianReal`). Both follow from the Gaussian
closed forms `valueAtRisk_of_hasLaw_gaussianReal` and `expectedShortfall_of_hasLaw_gaussianReal`,
with the mean and variance of the law.

## Main definitions

* `stdDevPrinciple`: the standard-deviation principle `ρ(X) = E[X] + k·sd(X)` with loading `k`.

## Main results

* `stdDevPrinciple_add_const`, `stdDevPrinciple_const_mul`, `stdDevPrinciple_add_le`.
* `stdDevPrinciple_not_monotone`: the principle is not monotone: for a loading `k ≥ 0`, a loss
  `B ≤ 0` valued in `{−1, 0}` with `P{B = −1} = q`, `q (1 + k²) < k²`, has `ρ(0) < ρ(B)`.
* `integral_le_stdDevPrinciple`: a nonnegative loading prices at or above the mean.
* `stdDevPrinciple_eq_valueAtRisk_of_hasLaw_gaussianReal`,
  `stdDevPrinciple_eq_expectedShortfall_of_hasLaw_gaussianReal`: on Gaussian losses VaR and ES are
  standard-deviation principles, with loadings `Φ⁻¹(α)` and `ϕ(Φ⁻¹(α))/(1 − α)` (for ES, positive
  variance).

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Examples 2.11 and 2.14
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 8.11; Ex. 8.11, 2.19

## Tags

standard deviation principle, premium principle, mean plus standard deviation, monotonicity failure,
coherence axioms, safety loading, MSC 91G70, MSC 91G05, JEL G22, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → ℝ}

/-- The standard deviation is unchanged by a cash shift, so it is not translation invariant on
its own: `sd(X + m) = sd(X)`. -/
lemma sqrt_variance_add_const (hX : AEStronglyMeasurable X P) (m : ℝ) :
    √Var[fun ω ↦ X ω + m; P] = √Var[X; P] := by
  rw [variance_add_const hX]

/-- The **standard-deviation principle** with loading `k`: `ρ(X) = E[X] + k·sd(X)`, the premium
principle `stdDevPremium` at the mean and standard deviation of `X`. -/
noncomputable def stdDevPrinciple (k : ℝ) (X : Ω → ℝ) (P : Measure Ω) : ℝ :=
  stdDevPremium k P[X] √Var[X; P]

omit [IsProbabilityMeasure P] in
/-- **A nonnegative loading prices at or above the mean**: `E[X] ≤ E[X] + k·sd(X)` for `k ≥ 0`.
This is `stdDevPremium_ge_mean` at the mean and standard deviation of `X`. -/
theorem integral_le_stdDevPrinciple {k : ℝ} (hk : 0 ≤ k) : P[X] ≤ stdDevPrinciple k X P :=
  stdDevPremium_ge_mean _ hk (Real.sqrt_nonneg _)

/-- **Translation invariance**: `ρ(X + m) = ρ(X) + m`. -/
theorem stdDevPrinciple_add_const (k : ℝ) (hX : MemLp X 2 P) (m : ℝ) :
    stdDevPrinciple k (fun ω ↦ X ω + m) P = stdDevPrinciple k X P + m := by
  unfold stdDevPrinciple stdDevPremium
  rw [integral_add (hX.integrable one_le_two) (integrable_const m), integral_const,
    sqrt_variance_add_const hX.aestronglyMeasurable]
  simp only [probReal_univ, one_smul]
  ring

omit [IsProbabilityMeasure P] in
/-- **Positive homogeneity**: `ρ(cX) = c ρ(X)` for `c ≥ 0`. -/
theorem stdDevPrinciple_const_mul (k : ℝ) (X : Ω → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    stdDevPrinciple k (fun ω ↦ c * X ω) P = c * stdDevPrinciple k X P := by
  unfold stdDevPrinciple stdDevPremium
  rw [integral_const_mul, variance_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  ring

/-- **Subadditivity**: `ρ(X + Y) ≤ ρ(X) + ρ(Y)` for a nonnegative loading. -/
theorem stdDevPrinciple_add_le {k : ℝ} (hk : 0 ≤ k) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    stdDevPrinciple k (fun ω ↦ X ω + Y ω) P ≤ stdDevPrinciple k X P + stdDevPrinciple k Y P := by
  unfold stdDevPrinciple stdDevPremium
  rw [integral_add (hX.integrable one_le_two) (hY.integrable one_le_two)]
  nlinarith [mul_le_mul_of_nonneg_left (sqrt_variance_add_le hX hY) hk]

/-- **The standard-deviation principle is not monotone** (QRM Exercise 8.11). Let `B ≤ 0` take
the value `−1` with probability `q > 0` and `0` otherwise. If `q (1 + k²) < k²` then
`ρ(B) > 0 = ρ(0)`, although `B ≤ 0` pointwise. -/
theorem stdDevPrinciple_not_monotone {k : ℝ} (hk : 0 ≤ k) {B : Ω → ℝ} (hBm : Measurable B)
    (hB : ∀ ω, B ω = -1 ∨ B ω = 0) {q : ℝ} (hq : P.real {ω | B ω = -1} = q) (hq0 : 0 < q)
    (hqk : q * (1 + k ^ 2) < k ^ 2) :
    (∀ ω, B ω ≤ 0) ∧ stdDevPrinciple k (fun _ ↦ (0 : ℝ)) P < stdDevPrinciple k B P := by
  set A := {ω | B ω = -1}
  have hA : MeasurableSet A := hBm (measurableSet_singleton (-1))
  have hBeq : B = fun ω ↦ -A.indicator 1 ω := by
    ext ω
    rcases hB ω with h | h
    · simp [A, h]
    · simp [A, h]
  have hB2 : MemLp B 2 P :=
    hBeq ▸ (memLp_indicator_const 2 hA.nullMeasurableSet 1 (Or.inr (measure_ne_top _ _))).neg
  have hmean : P[B] = -q := by
    rw [hBeq, integral_neg, integral_indicator_one hA, hq]
  have hsq : P[B ^ 2] = q := by
    have : B ^ 2 = A.indicator 1 := by
      ext ω
      rcases hB ω with h | h
      · simp [A, h]
      · simp [A, h]
    rw [this, integral_indicator_one hA, hq]
  have hvar : Var[B; P] = q * (1 - q) := by
    rw [variance_eq_sub hB2, hsq, hmean]
    ring
  have hq1 : q < 1 := by nlinarith
  refine ⟨fun ω ↦ (hB ω).elim (fun h ↦ h ▸ by norm_num) (fun h ↦ h.le), ?_⟩
  unfold stdDevPrinciple stdDevPremium
  rw [hmean, hvar]
  have h0 : Var[fun _ ↦ (0 : ℝ); P] = 0 := by simpa using variance_const_mul 0 B P
  simp only [integral_const, smul_zero, h0, Real.sqrt_zero, mul_zero, add_zero]
  -- `q < k √(q(1 − q))` because `q² < k² q (1 − q)`
  have hpos : 0 < q * (1 - q) := mul_pos hq0 (by linarith)
  have hlt : q < k * √(q * (1 - q)) := by
    have hx : (k * √(q * (1 - q))) ^ 2 = k ^ 2 * (q * (1 - q)) := by
      rw [mul_pow, Real.sq_sqrt hpos.le]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) (by rw [hx]; nlinarith)
  linarith

/-! ### Gaussian losses -/

omit [IsProbabilityMeasure P] in
/-- **On a Gaussian loss VaR is a standard-deviation principle**: for `X ~ N(m, v)` and
`α ∈ (0, 1)`, `E[X] + Φ⁻¹(α)·sd(X) = m + √v Φ⁻¹(α) = VaR_α(X)`. -/
theorem stdDevPrinciple_eq_valueAtRisk_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal m v) P) {α : ℝ} (hα : α ∈ Ioo 0 1) :
    stdDevPrinciple (PhiInv α) X P = valueAtRisk X P α := by
  rw [valueAtRisk_of_hasLaw_gaussianReal hX hα, gaussianVaR, stdDevPrinciple, stdDevPremium,
    hX.integral_eq, integral_id_gaussianReal, hX.variance_eq, variance_id_gaussianReal, mul_comm]

/-- **On a Gaussian loss ES is a standard-deviation principle**: for `X ~ N(m, v)` with `v ≠ 0`
and `α ∈ (0, 1)`, `E[X] + (ϕ(Φ⁻¹(α))/(1 − α))·sd(X) = ES_α(X)`, where `ϕ` is the standard normal
density. -/
theorem stdDevPrinciple_eq_expectedShortfall_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) (hX : HasLaw X (gaussianReal m v) P) {α : ℝ} (hα : α ∈ Ioo 0 1) :
    stdDevPrinciple (gaussianPDFReal 0 1 (PhiInv α) / (1 - α)) X P = expectedShortfall X P α := by
  rw [expectedShortfall_of_hasLaw_gaussianReal hv hX hα, gaussianCVaR, stdDevPrinciple,
    stdDevPremium, hX.integral_eq, integral_id_gaussianReal, hX.variance_eq,
    variance_id_gaussianReal, mul_comm]

end MathFin
