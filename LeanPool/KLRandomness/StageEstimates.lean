/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.BlockRandomness
public import LeanPool.KLRandomness.HorizonLaw
public import LeanPool.KLRandomness.StageErrorBudget
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The stage-construction contract and the separation reduction

`StageEstimates` records the actual finite-stage estimates (6)--(9), together
with horizon avoidance, for one scan and wager function beyond an arbitrary
finite block index.  It is a proposition about supplied blocks, not an assertion
that blocks with these properties exist.

These estimates imply the actual infinite-law early and late bounds, then
almost-sure summability of all forced wagers.  If they hold for every normalized
strategy and the block solutions have the stated effective description cover,
the final separating-sequence conclusion follows. `StageConstruction` now
supplies this contract using actual pools, candidates and short descriptions.
-/

@[expose] public section

namespace Klr

open MeasureTheory
open scoped ENNReal

/-- The Section 5 output needed for one strategy. Stage `j + 1` includes block `j`;
the finite exceptional prefix before `J` needs no estimates. -/
structure StageEstimates (B : ℕ → AffineBlock) (π : ScanRule) (w : List Bool → ℝ)
    (V : ℕ → ℕ) (H : Set Cantor) (J : ℕ) : Prop where
  measurableH : MeasurableSet H
  horizon_avoidance : ∀ j, J ≤ j → ∀ v, v.length = V j →
    ∀ k, j < k → (B k).UnreadFullRank π v
  early_and_partial : ∀ j, J ≤ j →
    (∫⁻ X, ENNReal.ofReal (EarlyLateWagers.earlyWager B π w V j X)
      ∂PrefixStage.law B (j + 1)) +
      PrefixStage.law B (j + 1) (LateDropBound.partialEvent (B j) π (V j)) ≤
        4 * StageErrorBudget.error j
  first_drop_tail : ∀ j, J ≤ j →
    PrefixStage.law B (j + 1) (StoppingTranscript.rankDropTailEvent (B j) π (V j)) ≤
      2 * StageErrorBudget.error j
  high_no_drop : ∀ j, J ≤ j →
    PrefixStage.law B j (π.observationMap ⁻¹' H ∩ NoDrop.noDropEvent (B j) π) ≤
      StageErrorBudget.error j
  later_low_drop : ∀ j, J ≤ j → ∀ k, j < k →
    PrefixStage.law B (j + 1)
      (π.observationMap ⁻¹' Hᶜ ∩ LateDropBound.hasDrop (B k) π) ≤ StageErrorBudget.error k

namespace StageEstimates

variable {B : ℕ → AffineBlock} {π : ScanRule} {w : List Bool → ℝ}
  {V : ℕ → ℕ} {H : Set Cantor} {J : ℕ}

/-- The stage hypotheses give the paper's `8e_j` late-drop bound under the actual infinite law. -/
theorem late_bound (h : StageEstimates B π w V H J)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j : ℕ) (hj : J ≤ j) :
    BlockProduct.law B hdis (DropEvents.lateEvent B π V j) ≤ 8 * StageErrorBudget.error j := by
  have hp : PrefixStage.law B (j + 1) (LateDropBound.partialEvent (B j) π (V j)) ≤
      4 * StageErrorBudget.error j :=
    (le_add_of_nonneg_left bot_le).trans (h.early_and_partial j hj)
  calc
    _ ≤ 4 * StageErrorBudget.error j + 2 * StageErrorBudget.error j +
        StageErrorBudget.error j +
        ∑' k : {k : ℕ // j < k}, StageErrorBudget.error k.val :=
      LateDropBound.law_lateEvent_le B hdis π V j H h.measurableH
        (4 * StageErrorBudget.error j) (2 * StageErrorBudget.error j)
        (StageErrorBudget.error j) StageErrorBudget.error
        (h.horizon_avoidance j hj) hp (h.first_drop_tail j hj)
        (h.high_no_drop j hj) (h.later_low_drop j hj)
    _ = _ := by rw [StageErrorBudget.tail_error]; ring

/-- Horizon avoidance transfers the early-wager expectation to the actual infinite law. -/
theorem early_bound (h : StageEstimates B π w V H J)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j : ℕ) (hj : J ≤ j) :
    (∫⁻ X, ENNReal.ofReal (EarlyLateWagers.earlyWager B π w V j X)
      ∂BlockProduct.law B hdis) ≤ 4 * StageErrorBudget.error j := by
  rw [HorizonLaw.lintegral_earlyWager_eq_stage B hdis π w V j (h.horizon_avoidance j hj)]
  exact (le_add_of_nonneg_right bot_le).trans (h.early_and_partial j hj)

/-- The actual Section 5 estimates imply equation (11), including all initial exceptional blocks. -/
theorem ae_summable_forcedWager (h : StageEstimates B π w V H J)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) :
    ∀ᵐ X ∂BlockProduct.law B hdis, Summable (EarlyLateWagers.forcedWager B π w X) := by
  exact EarlyLateWagers.ae_summable_forcedWager_of_bounds (BlockProduct.law B hdis) B π w V J
    (fun j => 8 * StageErrorBudget.error j) (fun j => 4 * StageErrorBudget.error j)
    (StageErrorBudget.tsum_mul_error_lt_top 8 (by norm_num))
    (StageErrorBudget.tsum_mul_error_lt_top 4 (by norm_num))
    (h.late_bound hdis) (h.early_bound hdis)

end StageEstimates

/-- Stage estimates for every normalized strategy suffice for almost-sure KL randomness.
The Borel partition and the exceptional block cutoff may depend on the strategy. -/
theorem ae_kolmogorovLovelandRandom_of_stage_estimates (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (V : ℕ → ℕ)
    (hstage : ∀ s : BettingStrategy, ∃ (H : Set Cantor) (J : ℕ),
      StageEstimates B s.normalize.scan s.normalize.capital.wager V H J) :
    ∀ᵐ X ∂BlockProduct.law B hdis, KolmogorovLovelandRandom X := by
  apply BlockRandomness.ae_kolmogorovLovelandRandom_of_forced_summable B hdis
  intro s
  obtain ⟨H, J, h⟩ := hstage s
  exact h.ae_summable_forcedWager hdis

/-- Conditional completion of the paper's argument: actual stage estimates and an effective
description cover yield separation.  Their simultaneous construction is still required. -/
theorem exists_separating_of_stage_estimates_and_descriptions (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (V : ℕ → ℕ)
    (hstage : ∀ s : BettingStrategy, ∃ (H : Set Cantor) (J : ℕ),
      StageEstimates B s.normalize.scan s.normalize.capital.wager V H J)
    {W : ℕ × List Bool × List Bool → Prop} (hW : REPred W)
    (hbound : ∀ (n : ℕ) (p : List Bool),
      fairCoin (cylinderUnion (fun v => W (n, p, v))) ≤
        (1 / 2 : ℝ≥0∞) ^ (2 * p.length + n + 1))
    (hcover : ∀ n : ℕ, ∃ (j : ℕ) (p : List Bool),
      (B j).event ⊆ cylinderUnion (fun v => W (n, p, v))) :
    ∃ X : Cantor, KolmogorovLovelandRandom X ∧ ¬MartinLofRandom X := by
  apply BlockRandomness.exists_separating_of_description_cover B hdis ?_ hW hbound hcover
  intro s
  obtain ⟨H, J, h⟩ := hstage s
  exact h.ae_summable_forcedWager hdis

end Klr
