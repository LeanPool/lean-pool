/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Performance.Ratios
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Multi-period Kelly criterion and Kelly fraction bounds

The single-period Kelly fraction (`kellyFraction`, `kellyGrowth`) and its
first-order optimality live in `Choice/Performance/Ratios.lean`; this file adds the
multi-period / horizon-myopia / fraction-bound extensions.

The `n`-period model is taken seriously rather than asserted: one period's
wealth multiplier is the two-point law `kellyReturnMeasure p b f` (multiplier
`1 + f·b` with probability `p`, `1 - f` with probability `1 - p`), `n` iid
periods are its `n`-fold product measure `Measure.pi`, and the expected
log-wealth of the compounded product — `E[log(R₁⋯R_n)] = E[∑ log Rᵢ]` — is
*computed* coordinate-by-coordinate to equal `n · kellyGrowth p b f`:

  `∫ (∑ i, log Rᵢ) ∂(Π ν) = n · (p·log(1 + f·b) + (1 - p)·log(1 - f))`.

Maximizing this over `f` is the same single-period problem at every horizon,
so the multi-period Kelly fraction equals the single-period one — Kelly is
myopic.

Additionally:

* **`kellyFraction < 1`**: the Kelly fraction is always strictly less than 1 for
  proper probabilities `p < 1` and positive payoffs `b > 0` (no all-in bet
  except in the degenerate `p = 1` case).
* **`kellyFraction = 0 iff break-even`**: `f* = 0` iff `p(b+1) = 1`.
* **`kellyFraction > 0 iff favorable bet`**: `f* > 0` iff `p(b+1) > 1`.

## Main definitions

* `kellyReturnMeasure`: one Kelly period's wealth-multiplier law, `1 + f·b` with probability `p`
  and `1 − f` with probability `1 − p`.

## Main results

* `integral_log_kellyReturnMeasure`: one period's expected log-multiplier is
  exactly `kellyGrowth p b f`.
* `kellyGrowth_n_periods`: over `n` iid periods the expected total log-growth
  is `n · kellyGrowth p b f` — linearity of expectation over the actual
  product model, via the measure-preserving coordinate evaluations of
  `Measure.pi`.
* `kelly_n_periods_deriv_at_kelly`: first-order optimality for `n · kellyGrowth`
  vanishes at the single-period `kellyFraction p b`.
* `kellyFraction_lt_one`, `kellyFraction_eq_zero_iff`, `kellyFraction_pos_iff`:
  bounds and sign analysis of the Kelly fraction.

## References

* [J. L. Kelly, *A new interpretation of information rate*][Kelly1956]
* [MacLean, Thorp and Ziemba (2010)][MacLeanThorpZiemba2010]
* [Thorp (2006)][Thorp2006]

## Tags

Kelly criterion, growth-optimal, log utility, expected log-wealth, myopic investment,
optimal bet size, MSC 91G10, MSC 91B16, JEL G11
-/

@[expose] public section

namespace MathFin

open Real MeasureTheory

/-- One Kelly period's wealth-multiplier law: the bet at fraction `f` pays
odds `b` with probability `p` (multiplier `1 + f·b`) and loses the stake with
probability `1 - p` (multiplier `1 - f`). A two-point Borel measure on `ℝ`. -/
noncomputable def kellyReturnMeasure (p b f : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac (1 + f * b)
    + ENNReal.ofReal (1 - p) • Measure.dirac (1 - f)

lemma kellyReturnMeasure_isProbability {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (b f : ℝ) : IsProbabilityMeasure (kellyReturnMeasure p b f) := by
  constructor
  have hq : (0 : ℝ) ≤ 1 - p := by linarith
  unfold kellyReturnMeasure
  rw [add_apply, smul_apply, smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _),
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, smul_eq_mul,
    mul_one, mul_one, ← ENNReal.ofReal_add hp hq,
    show p + (1 - p) = 1 by ring, ENNReal.ofReal_one]

/-- `log` is integrable against the one-period law (a two-point measure). -/
lemma integrable_log_kellyReturnMeasure (p b f : ℝ) :
    Integrable Real.log (kellyReturnMeasure p b f) :=
  ((integrable_dirac eNorm_lt_top).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac eNorm_lt_top).smul_measure ENNReal.ofReal_ne_top)

/-- **One-period expected log-growth**: the expectation of `log` under the
one-period wealth-multiplier law is exactly `kellyGrowth p b f`. -/
lemma integral_log_kellyReturnMeasure {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (b f : ℝ) :
    ∫ x, Real.log x ∂(kellyReturnMeasure p b f) = kellyGrowth p b f := by
  have hq : (0 : ℝ) ≤ 1 - p := by linarith
  unfold kellyReturnMeasure
  rw [integral_add_measure
      ((integrable_dirac eNorm_lt_top).smul_measure ENNReal.ofReal_ne_top)
      ((integrable_dirac eNorm_lt_top).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq]
  simp [kellyGrowth, smul_eq_mul]

/-- **Multi-period Kelly log-growth linearity**: over `n` iid periods, each
period's wealth multiplier distributed as `kellyReturnMeasure p b f`, the
expected total log-growth `E[log(R₁⋯R_n)] = E[∑ i, log Rᵢ]` equals
`n · kellyGrowth p b f`. This is linearity of expectation over the actual
`n`-period product model: each coordinate evaluation of `Measure.pi` is
measure-preserving onto the one-period law, whose log-expectation is
`kellyGrowth p b f`. -/
theorem kellyGrowth_n_periods (n : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (b f : ℝ) :
    ∫ R : Fin n → ℝ, ∑ i, Real.log (R i)
        ∂(Measure.pi fun _ : Fin n ↦ kellyReturnMeasure p b f)
      = (n : ℝ) * kellyGrowth p b f := by
  have : IsProbabilityMeasure (kellyReturnMeasure p b f) :=
    kellyReturnMeasure_isProbability hp hp1 b f
  -- each coordinate evaluation is measure-preserving onto the one-period law
  have hmp : ∀ i : Fin n, MeasurePreserving (Function.eval i)
      (Measure.pi fun _ : Fin n ↦ kellyReturnMeasure p b f)
      (kellyReturnMeasure p b f) := fun i ↦ measurePreserving_eval _ i
  -- linearity of expectation: integrability of each coordinate's log
  have hint : ∀ i ∈ Finset.univ (α := Fin n),
      Integrable (fun R : Fin n → ℝ ↦ Real.log (R i))
        (Measure.pi fun _ : Fin n ↦ kellyReturnMeasure p b f) := fun i _ ↦
    ((hmp i).integrable_comp Real.measurable_log.aestronglyMeasurable).mpr
      (integrable_log_kellyReturnMeasure p b f)
  rw [integral_finsetSum _ hint]
  -- each marginal integral is the one-period expected log-growth
  have hi : ∀ i : Fin n,
      ∫ R : Fin n → ℝ, Real.log (R i)
          ∂(Measure.pi fun _ : Fin n ↦ kellyReturnMeasure p b f)
        = kellyGrowth p b f := by
    intro i
    have hmap := (hmp i).map_eq
    calc ∫ R : Fin n → ℝ, Real.log (R i)
        ∂(Measure.pi fun _ : Fin n ↦ kellyReturnMeasure p b f)
        = ∫ x, Real.log x ∂(kellyReturnMeasure p b f) := by
          conv_rhs => rw [← hmap]
          rw [integral_map (measurable_pi_apply i).aemeasurable
            Real.measurable_log.aestronglyMeasurable]
      _ = kellyGrowth p b f := integral_log_kellyReturnMeasure hp hp1 b f
  simp_rw [hi]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Multi-period Kelly first-order condition**: the optimal fraction is
independent of the horizon `n` — maximizing `n · kellyGrowth` is the same
single-period problem, so Kelly is myopic. -/
lemma kelly_n_periods_deriv_at_kelly (n : ℕ) {p b : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hb : 0 < b) :
    HasDerivAt (fun f ↦ (n : ℝ) * kellyGrowth p b f) 0 (kellyFraction p b) := by
  have h := kellyGrowth_deriv_at_kelly hp hp1 hb
  have h_mul := h.const_mul (n : ℝ)
  simpa using h_mul

/-- **Kelly fraction < 1** for proper probabilities and positive payoff. -/
lemma kellyFraction_lt_one {p b : ℝ} (hp : p < 1) (hb : 0 < b) :
    kellyFraction p b < 1 := by
  unfold kellyFraction
  rw [div_lt_one hb]
  nlinarith

/-- **Kelly fraction = 0 iff break-even bet** (`p · (b + 1) = 1`). -/
lemma kellyFraction_eq_zero_iff (p : ℝ) {b : ℝ} (hb : b ≠ 0) :
    kellyFraction p b = 0 ↔ p * (b + 1) = 1 := by
  unfold kellyFraction
  rw [div_eq_zero_iff]
  refine ⟨?_, ?_⟩
  · rintro (h | h)
    · linarith
    · exact absurd h hb
  · intro h; left; linarith

/-- **Kelly fraction > 0 iff favorable bet** (`p · (b + 1) > 1`). -/
lemma kellyFraction_pos_iff (p : ℝ) {b : ℝ} (hb : 0 < b) :
    0 < kellyFraction p b ↔ 1 < p * (b + 1) := by
  unfold kellyFraction
  rw [lt_div_iff₀ hb]
  refine ⟨?_, ?_⟩ <;> intro h <;> linarith

end MathFin
