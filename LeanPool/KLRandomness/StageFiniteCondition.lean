/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageFiniteProbability

/-!
# Exact conditional sums for arbitrary finite Boolean conditions

The new syndrome can be tested directly on finite input words before a
certified affine code is reconstructed. This general finite-prefix formula
computes its conditional expectations with exact rational arithmetic.
-/

@[expose] public section

namespace Klr.StageFiniteCondition

open MeasureTheory ProbabilityTheory RationalComputability

/-- The inputs whose prefix of the prescribed length passes a Boolean test. -/
def event (n : ℕ) (p : List Bool → Bool) : Set Cantor :=
  {X | p (ScanRule.inputPrefix X n) = true}

theorem measurableSet_event (n : ℕ) (p : List Bool → Bool) :
    MeasurableSet (event n p) := by
  have hm : Measurable (fun X : Cantor => p (ScanRule.inputPrefix X n)) := by
    simpa only [ScanRule.monotone_transcript] using
      DropEvents.measurable_transcript_eval ScanRule.monotone n p
  exact hm (measurableSet_singleton true)

/-- A finite conditional sum, also defined when the condition is empty. -/
def expectation (n : ℕ) (p : List Bool → Bool) (f : List Bool → ℚ) : ℚ :=
  PoolAdvice.average n (fun s => if p s then f s else 0) /
    PoolAdvice.average n (fun s => if p s then 1 else 0)

theorem computable_expectation {α : Type*} [Primcodable α]
    {n : α → ℕ} {p : α → List Bool → Bool} {f : α → List Bool → ℚ}
    (hn : Computable n) (hp : Computable₂ p) (hf : Computable₂ f) :
    Computable (fun a => expectation (n a) (p a) (f a)) := by
  have hnum := PoolAdvice.computable_average (f := fun a s =>
    _root_.cond (p a s) (f a s) (0 : ℚ)) hn
    (Computable.cond hp hf (Computable.const (0 : ℚ)))
  have hden := PoolAdvice.computable_average (f := fun a s =>
    _root_.cond (p a s) (1 : ℚ) 0) hn
    (Computable.cond hp (Computable.const (1 : ℚ)) (Computable.const 0))
  exact (primrec_rat_div.to_comp.comp hnum hden).of_eq fun _ => by
    simp only [expectation, Bool.cond_eq_ite]

theorem average_eq_setIntegral (n : ℕ) (p : List Bool → Bool) (f : List Bool → ℚ) :
    (PoolAdvice.average n (fun s => if p s then f s else 0) : ℝ) =
      ∫ X in event n p, (f (ScanRule.inputPrefix X n) : ℝ) ∂fairCoin := by
  rw [PoolAdvice.average_eq_integral, ← integral_indicator (measurableSet_event n p)]
  apply integral_congr_ae
  filter_upwards [] with X
  by_cases h : p (ScanRule.inputPrefix X n) = true <;> simp [event, Set.indicator, h]

theorem expectation_eq_integral (n : ℕ) (p : List Bool → Bool) (f : List Bool → ℚ) :
    (expectation n p f : ℝ) =
      ∫ X, (f (ScanRule.inputPrefix X n) : ℝ) ∂cond fairCoin (event n p) := by
  rw [expectation, Rat.cast_div, average_eq_setIntegral, average_eq_setIntegral]
  simp [ProbabilityTheory.cond, integral_smul_measure, measureReal_def,
    ENNReal.toReal_inv, smul_eq_mul, div_eq_mul_inv, mul_comm]

end Klr.StageFiniteCondition
