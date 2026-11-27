/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.LateDropBound
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The dyadic stage error budget

The paper's errors are `e_j = 2^(-j) / 100`.  Their strict tail equals the
current error.  The four contributions to the Section 6 late-drop estimate
therefore total `8e_j`, while the early-wager estimate uses `4e_j`.  Both
series have finite sums, including after any finite set of initial stages.

The final theorem specializes the actual finite-stage estimate in
`LateDropBound`; it does not assert that suitable stages have been chosen.
-/

@[expose] public section

namespace Klr.StageErrorBudget

open MeasureTheory
open scoped ENNReal NNReal

/-- The error assigned to stage `j`. -/
noncomputable def error (j : ℕ) : ℝ≥0∞ := (1 / 2 : ℝ≥0∞) ^ j / 100

theorem error_pos (j : ℕ) : 0 < error j := by
  unfold error
  exact ENNReal.div_pos (pow_ne_zero _ (by norm_num)) (by norm_num)

theorem error_lt_top (j : ℕ) : error j < ∞ := by
  unfold error
  finiteness

/-- The total error budget, with stages indexed starting at zero. -/
theorem tsum_error : (∑' j : ℕ, error j) = (1 / 50 : ℝ≥0∞) := by
  simp_rw [error, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  norm_num
  simpa [ENNReal.coe_inv] using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
    (by norm_num : (2 : ℝ≥0) * 100⁻¹ = 50⁻¹)

theorem tsum_error_lt_top : (∑' j : ℕ, error j) < ∞ := by
  rw [tsum_error]
  norm_num

/-- Any finite multiple of the stage-error series has finite sum. -/
theorem tsum_mul_error_lt_top (c : ℝ≥0∞) (hc : c < ∞) :
    (∑' j : ℕ, c * error j) < ∞ := by
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top hc tsum_error_lt_top

/-- Exact shifted sum; finite exceptional stages can be discarded freely. -/
theorem tsum_error_shift (J : ℕ) :
    (∑' j : ℕ, error (j + J)) = 2 * error J := by
  simp_rw [error, pow_add, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  norm_num
  ac_rfl

theorem tsum_mul_error_shift_lt_top (c : ℝ≥0∞) (hc : c < ∞) (J : ℕ) :
    (∑' j : ℕ, c * error (j + J)) < ∞ := by
  rw [ENNReal.tsum_mul_left, tsum_error_shift]
  exact ENNReal.mul_lt_top hc (ENNReal.mul_lt_top (by norm_num) (error_lt_top J))

/-- The natural-number enumeration of the stages strictly after `j`. -/
def laterEquiv (j : ℕ) : ℕ ≃ {k : ℕ // j < k} where
  toFun n := ⟨n + (j + 1), by omega⟩
  invFun k := k.val - (j + 1)
  left_inv n := by dsimp; omega
  right_inv k := by apply Subtype.ext; dsimp; omega

/-- For this dyadic budget, the strict tail equals the current term. -/
theorem tail_error (j : ℕ) :
    (∑' k : {k : ℕ // j < k}, error k.val) = error j := by
  rw [← (laterEquiv j).tsum_eq (fun k => error k.val)]
  change (∑' n : ℕ, error (n + (j + 1))) = error j
  rw [tsum_error_shift]
  unfold error
  simp only [pow_succ, div_eq_mul_inv, one_mul]
  calc
    _ = ((2 : ℝ≥0∞) * 2⁻¹) * (2⁻¹ ^ j * 100⁻¹) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- The four terms in the late-drop bound collapse to `8e_j`. -/
theorem late_budget (j : ℕ) :
    4 * error j + 2 * error j + error j +
      (∑' k : {k : ℕ // j < k}, error k.val) = 8 * error j := by
  rw [tail_error]
  ring

theorem tsum_four_error : (∑' j : ℕ, 4 * error j) = (2 / 25 : ℝ≥0∞) := by
  rw [ENNReal.tsum_mul_left, tsum_error]
  norm_num
  simpa [ENNReal.coe_inv, ENNReal.coe_div] using
    congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
      (by norm_num : (4 : ℝ≥0) * 50⁻¹ = 2 / 25)

theorem tsum_eight_error : (∑' j : ℕ, 8 * error j) = (4 / 25 : ℝ≥0∞) := by
  rw [ENNReal.tsum_mul_left, tsum_error]
  norm_num
  simpa [ENNReal.coe_inv, ENNReal.coe_div] using
    congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
      (by norm_num : (8 : ℝ≥0) * 50⁻¹ = 4 / 25)

/-- The paper's numerical late-drop estimate under its actual stage hypotheses. -/
theorem law_lateEvent_le_dyadic (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (π : ScanRule) (V : ℕ → ℕ) (j : ℕ) (H : Set Cantor) (hH : MeasurableSet H)
    (havoid : ∀ v, v.length = V j → ∀ k, j < k → (B k).UnreadFullRank π v)
    (hpartial : PrefixStage.law B (j + 1)
      (LateDropBound.partialEvent (B j) π (V j)) ≤ 4 * error j)
    (htail : PrefixStage.law B (j + 1)
      (StoppingTranscript.rankDropTailEvent (B j) π (V j)) ≤ 2 * error j)
    (hhigh : PrefixStage.law B j
      (π.observationMap ⁻¹' H ∩ NoDrop.noDropEvent (B j) π) ≤ error j)
    (hlater : ∀ k, j < k → PrefixStage.law B (j + 1)
      (π.observationMap ⁻¹' Hᶜ ∩ LateDropBound.hasDrop (B k) π) ≤ error k) :
    BlockProduct.law B hdis (DropEvents.lateEvent B π V j) ≤ 8 * error j := by
  simpa only [late_budget] using
    LateDropBound.law_lateEvent_le B hdis π V j H hH
      (4 * error j) (2 * error j) (error j) error havoid hpartial htail hhigh hlater

end Klr.StageErrorBudget
