/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.BlockProductAnswer
public import LeanPool.KLRandomness.FairForced
public import LeanPool.KLRandomness.StrategyCountability
public import LeanPool.KLRandomness.MartinLof
public import LeanPool.KLRandomness.DescriptionBudget
public import LeanPool.KLRandomness.EarlyLateWagers

/-!
# The probabilistic reduction for the separating construction

For an actual disjoint affine-block law, no-drop queries have fair child
probabilities.  Thus almost-sure summability of the absolute wagers on rank-drop
queries makes each normalized strategy fail almost surely.  Countability and
success-preserving normalization then give almost-sure KL randomness.

The final conditional existence theorem leaves the construction's two output
obligations explicit: the forced-wager estimates and coverage of all block
solutions by one genuine Martin-Löf test.  It does not assert that suitable
blocks or descriptions have already been constructed.
-/

@[expose] public section

namespace Klr.BlockRandomness

open MeasureTheory
open scoped ENNReal

/-- Select exactly those histories at which the next query causes no block rank drop. -/
noncomputable def fairSelect (B : ℕ → AffineBlock) (π : ScanRule) : List Bool → Bool := by
  classical
  exact fun v => decide (¬BlockProductAnswer.forced B π v)

/-- The absolute wager series restricted to actual rank-drop queries. -/
noncomputable def forcedWagers (B : ℕ → AffineBlock) (s : BettingStrategy)
    (X : Cantor) (n : ℕ) : ℝ := by
  classical
  exact if BlockProductAnswer.forced B s.scan (s.scan.transcript X n)
    then |s.capital.wager (s.scan.transcript X n)| else 0

theorem forcedAmount_eq (B : ℕ → AffineBlock) (s : BettingStrategy) (X : Cantor) (n : ℕ) :
    FairForced.forcedAmount (fairSelect B s.scan) s.capital.wager (s.scan.transcript X n) =
      forcedWagers B s X n := by
  classical
  by_cases h : BlockProductAnswer.forced B s.scan (s.scan.transcript X n) <;>
    simp [FairForced.forcedAmount, fairSelect, forcedWagers, h]

/-- The actual infinite block law satisfies the fair-step hypothesis of the capital theorem. -/
theorem fairLaw (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (π : ScanRule) :
    FairForced.FairLaw (BlockProduct.law B hdis) π (fairSelect B π) := by
  intro v hv b
  have hnot : ¬BlockProductAnswer.forced B π v := by
    simpa only [fairSelect, decide_eq_true_eq] using hv
  exact BlockProductAnswer.child_mass_of_not_forced B hdis π v hnot b

/-- A bounded-wager strategy fails under the actual block law if its rank-drop wagers sum. -/
theorem ae_not_succeeds (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (s : BettingStrategy) (hw : ∀ v, |s.capital.wager v| ≤ (1 / 2 : ℝ))
    (hforced : ∀ᵐ X ∂BlockProduct.law B hdis, Summable (forcedWagers B s X)) :
    ∀ᵐ X ∂BlockProduct.law B hdis, ¬s.Succeeds X := by
  apply s.ae_not_succeeds_of_fair_forced (BlockProduct.law B hdis) (fairSelect B s.scan)
    hw (fairLaw B hdis s.scan)
  simpa only [forcedAmount_eq] using hforced

/-- The concrete remaining probabilistic obligation for almost-sure KL randomness. -/
theorem ae_kolmogorovLovelandRandom_of_forced_summable (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (hforced : ∀ s : BettingStrategy, ∀ᵐ X ∂BlockProduct.law B hdis,
      Summable (forcedWagers B s.normalize X)) :
    ∀ᵐ X ∂BlockProduct.law B hdis, KolmogorovLovelandRandom X := by
  apply ae_kolmogorovLovelandRandom_of_normalized
  intro s
  exact ae_not_succeeds B hdis s.normalize s.normalize_wager_abs_le_half (hforced s)

/-- Actual late-drop probabilities and early-wager expectations supply forced summability. -/
theorem ae_kolmogorovLovelandRandom_of_early_late (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (V : ℕ → ℕ)
    (hlate : ∀ s : BettingStrategy,
      (∑' j, BlockProduct.law B hdis (DropEvents.lateEvent B s.normalize.scan V j)) < ∞)
    (hearly : ∀ s : BettingStrategy,
      (∑' j, ∫⁻ X, ENNReal.ofReal
        (EarlyLateWagers.earlyWager B s.normalize.scan s.normalize.capital.wager V j X)
          ∂BlockProduct.law B hdis) < ∞) :
    ∀ᵐ X ∂BlockProduct.law B hdis, KolmogorovLovelandRandom X := by
  apply ae_kolmogorovLovelandRandom_of_forced_summable B hdis
  intro s
  exact EarlyLateWagers.ae_summable_forcedWager (BlockProduct.law B hdis) B
    s.normalize.scan s.normalize.capital.wager V (hlate s) (hearly s)

/-- Conditional final reduction: forced-wager control and a genuine test covering every
block solution produce a separating sequence.  Constructing such blocks remains necessary. -/
theorem exists_separating_of_test_cover (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (hforced : ∀ s : BettingStrategy, ∀ᵐ X ∂BlockProduct.law B hdis,
      Summable (forcedWagers B s.normalize X))
    (T : MartinLofTest)
    (hcover : ∀ X : Cantor, (∀ k, X ∈ (B k).event) → T.Fails X) :
    ∃ X : Cantor, KolmogorovLovelandRandom X ∧ ¬MartinLofRandom X := by
  have hboth : ∀ᵐ X ∂BlockProduct.law B hdis,
      KolmogorovLovelandRandom X ∧ ¬MartinLofRandom X := by
    filter_upwards [ae_kolmogorovLovelandRandom_of_forced_summable B hdis hforced,
      BlockProduct.ae_all_blocks B hdis] with X hX hblocks
    exact ⟨hX, fun hML => hML T (hcover X hblocks)⟩
  exact hboth.exists

/-- The same reduction with the explicit uniform description-budget interface.  At each
test level, one imposed block is covered by an event decoded from a sufficiently small
description.  The actual decoder and stage descriptions remain construction obligations. -/
theorem exists_separating_of_description_cover (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (hforced : ∀ s : BettingStrategy, ∀ᵐ X ∂BlockProduct.law B hdis,
      Summable (forcedWagers B s.normalize X))
    {W : ℕ × List Bool × List Bool → Prop} (hW : REPred W)
    (hbound : ∀ (n : ℕ) (p : List Bool),
      fairCoin (cylinderUnion (fun v => W (n, p, v))) ≤
        (1 / 2 : ℝ≥0∞) ^ (2 * p.length + n + 1))
    (hcover : ∀ n : ℕ, ∃ (j : ℕ) (p : List Bool),
      (B j).event ⊆ cylinderUnion (fun v => W (n, p, v))) :
    ∃ X : Cantor, KolmogorovLovelandRandom X ∧ ¬MartinLofRandom X := by
  obtain ⟨T, hT⟩ := exists_martinLofTest_of_description_family hW hbound
  apply exists_separating_of_test_cover B hdis hforced T
  intro X hX n
  rw [hT n]
  obtain ⟨j, p, hp⟩ := hcover n
  exact Set.mem_iUnion.mpr ⟨p, hp (hX j)⟩

end Klr.BlockRandomness
