/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageOneStepDefs

/-!
# All four estimates for the computed one-stage block

The syndrome is the output of the actual finite minimization program. The
early and tail estimates follow from that minimum and the reconstructed
horizon; the high and low estimates survive changing the syndrome because
the unread ranks depend only on the matrix and queried positions.
-/

@[expose] public section

noncomputable section

namespace Klr.StageOneStep

open MeasureTheory ProbabilityTheory SparseListSearch StageCandidate
open scoped BigOperators ENNReal

theorem measure_le_of_real_le (μ : Measure Cantor) [IsFiniteMeasure μ]
    (E : Set Cantor) {c : ℝ} (h : μ.real E ≤ c) : μ E ≤ ENNReal.ofReal c := by
  have he := ENNReal.ofReal_le_ofReal h
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ E)] using he

/-- A concrete computed syndrome satisfies all four stage bounds, once the
selected candidate and the actual finite horizon have the proved score
bounds. No syndrome is supplied as non-effective advice. -/
theorem bounds_of_computed_horizon
    (old : ℕ → AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (n : ℕ) (rules : List BettingStrategy) (H : Fin rules.length → Set Cantor)
    (cs : List AffineCode.Data)
    (hcs : StageFiniteProbability.law cs = PrefixStage.law old n)
    (G : List ℕ) (hG : G.Nodup) {m r : ℕ} (hr : 0 < r)
    (a : Entry) (ha : GoodEntry G.length m r a)
    (hnew : ∀ k < n, Disjoint (old k).support
      (block G.get hG.injective_get a ha 0).support)
    {error : ℚ}
    (hwager : (∑ i : Fin rules.length, StageChoice.wagerCost (PrefixStage.law old n)
      (rules.get i) (block G.get hG.injective_get a ha 0)) < (error : ℝ))
    (hhigh : (∑ i : Fin rules.length, (PrefixStage.law old n).real
      (StagePreHorizon.highMissInput (rules.get i) (H i) G)) < (error : ℝ))
    (hlow : ∀ k ≤ n, (∑ i : Fin rules.length, (PrefixStage.law old k).real
      (StagePreHorizon.lowDropInput (rules.get i) (H i)
        (block G.get hG.injective_get a ha 0))) < (error : ℝ))
    (V : ℕ)
    (hpartial : StageRankLimit.partialMass (PrefixStage.law old n)
      (block G.get hG.injective_get a ha 0)
      (fun i : Fin rules.length => (rules.get i).normalize.scan) V < 3 * (error : ℝ))
    (htail : (∑ i : Fin rules.length, (PrefixStage.law old n).real
      (StoppingTranscript.rankDropTailEvent (block G.get hG.injective_get a ha 0)
        (rules.get i).normalize.scan V)) < 2 * (error : ℝ)) :
    Bounds old n rules H error (chosenBlock rules cs G hG a ha V) V := by
  let C₀ := block G.get hG.injective_get a ha 0
  let y := SparseSearch.wordVector r (StageSyndromeObjective.chosen rules cs G a V)
  let π (i : Fin rules.length) := (rules.get i).normalize.scan
  let h (i : Fin rules.length) := StageFiniteWager.normalizedWager (rules.get i)
  have hmin : ∀ z : Fin C₀.rank → ZMod 2,
      (∫ X, StageHorizonChoice.objective C₀ π h V X
        ∂StageHorizonChoice.law (PrefixStage.prefixFamily old n) C₀ y) ≤
      ∫ X, StageHorizonChoice.objective C₀ π h V X
        ∂StageHorizonChoice.law (PrefixStage.prefixFamily old n) C₀ z := by
    intro z
    change Fin r → ZMod 2 at z
    simpa only [C₀, π, h, y, StageHorizonChoice.law, hcs, PrefixStage.law,
      withSyndrome_block G hG a ha 0] using
      StageSyndromeObjective.chosen_minimizes_integral rules cs G hG a ha V z
  have hw : (∑ i, ∫ X, StageWeights.supportWager (π i)
      (fun v => (h i v : ℝ)) C₀.support X ∂AffineBlock.finiteStageLaw
        (PrefixStage.prefixFamily old n)) < (error : ℝ) := by
    simpa only [C₀, h, π, StageFiniteWager.cast_normalizedWager,
      StageChoice.wagerCost, PrefixStage.law] using hwager
  have hpoint := StageHorizonChoice.minimizing_syndrome_stage_bounds
    (PrefixStage.prefixFamily old n) C₀ (PrefixStage.prefixFamily_pairwise old hold n)
    (fun k => hnew k.val k.isLt) π h V
    (fun i => StageFiniteWager.normalizedWager_abs_le_half (rules.get i))
    (error : ℝ) hw hpartial htail y hmin
  let : IsProbabilityMeasure (PrefixStage.law old n) :=
    PrefixStage.law_isProbabilityMeasure old hold n
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [StageHorizonChoice.earlyWager, StageHorizonChoice.law, C₀, y,
      h, π, StageFiniteWager.cast_normalizedWager, PrefixStage.law, chosenBlock,
      withSyndrome_block G hG a ha 0] using (hpoint i).1
  · intro i
    exact (hpoint i).2
  · intro i
    apply measure_le_of_real_le
    apply le_trans (measureReal_mono (high_noDrop_subset_highMiss (rules.get i) (H i)
      (chosenBlock rules cs G hG a ha V) G (block_support_subset G hG a ha y) hr))
    apply le_trans _ hhigh.le
    exact Finset.single_le_sum (f := fun j : Fin rules.length =>
      (PrefixStage.law old n).real (StagePreHorizon.highMissInput (rules.get j) (H j) G))
      (s := Finset.univ) (fun _ _ => measureReal_nonneg) (Finset.mem_univ i)
  · intro k hk i
    let : IsProbabilityMeasure (PrefixStage.law old k) :=
      PrefixStage.law_isProbabilityMeasure old hold k
    apply measure_le_of_real_le
    apply le_trans _ (hlow k hk).le
    exact Finset.single_le_sum (f := fun j : Fin rules.length =>
      (PrefixStage.law old k).real (StagePreHorizon.lowDropInput (rules.get j) (H j) C₀))
      (s := Finset.univ) (fun _ _ => measureReal_nonneg) (Finset.mem_univ i)

end Klr.StageOneStep
