/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageHorizonChoiceBounds
public import LeanPool.KLRandomness.StagePreHorizon
public import LeanPool.KLRandomness.StagePrefixCode
public import LeanPool.KLRandomness.StageSyndromeObjective
public import LeanPool.KLRandomness.AffineDescription

/-!
# The result of one actual stage extension

The stage result contains an affine block, its reconstructed horizon, a
valid finite code and an actual short program producing that code. Its four
probability estimates refer to the actual previous and new conditional laws.
-/

@[expose] public section

noncomputable section

namespace Klr.StageOneStep

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- The four estimates required of a new block after a fixed old prefix. -/
structure Bounds (old : ℕ → AffineBlock) (n : ℕ) (rules : List BettingStrategy)
    (H : Fin rules.length → Set Cantor) (error : ℚ) (C : AffineBlock) (V : ℕ) : Prop where
  early : ∀ i : Fin rules.length,
    (∫⁻ X, ENNReal.ofReal (EarlyLateWagers.earlyWager (fun _ => C)
      (rules.get i).normalize.scan (rules.get i).normalize.capital.wager (fun _ => V) 0 X)
      ∂cond (PrefixStage.law old n) C.event) +
      cond (PrefixStage.law old n) C.event
        (LateDropBound.partialEvent C (rules.get i).normalize.scan V) ≤
        ENNReal.ofReal (4 * (error : ℝ))
  tail : ∀ i : Fin rules.length,
    cond (PrefixStage.law old n) C.event
      (StoppingTranscript.rankDropTailEvent C (rules.get i).normalize.scan V) ≤
        ENNReal.ofReal (2 * (error : ℝ))
  high : ∀ i : Fin rules.length,
    PrefixStage.law old n ((rules.get i).normalize.scan.observationMap ⁻¹' H i ∩
      NoDrop.noDropEvent C (rules.get i).normalize.scan) ≤ ENNReal.ofReal (error : ℝ)
  low : ∀ a ≤ n, ∀ i : Fin rules.length,
    PrefixStage.law old a (StagePreHorizon.lowDropInput (rules.get i) (H i) C) ≤
      ENNReal.ofReal (error : ℝ)

/-- The fully represented output of one successful stage. -/
structure Result (old : ℕ → AffineBlock) (n : ℕ) (rules : List BettingStrategy)
    (H : Fin rules.length → Set Cantor) (error : ℚ) (r level : ℕ) (G : List ℕ) where
  /-- The selected affine constraint to impose at this stage. -/
  block : AffineBlock
  /-- The query horizon protected by this step. -/
  horizon : ℕ
  /-- The finite description of the selected affine constraint. -/
  code : AffineCode.Data
  /-- The short bit string that runs to the affine code. -/
  program : List Bool
  valid : AffineCode.valid code = true
  runs : code ∈ AffineDescription.run program
  code_rank : AffineCode.rank code = r
  block_rank : block.rank = r
  event_eq : AffineCode.event code = block.event
  budget : 2 * program.length + level + 1 ≤ r
  support_subset : block.support ⊆ G.toFinset
  bounds : Bounds old n rules H error block horizon

/-- The input form of the low-drop event agrees with the rank-event API. -/
theorem lowDropInput_eq (s : BettingStrategy) (H : Set Cantor) (C : AffineBlock) :
    StagePreHorizon.lowDropInput s H C =
      s.normalize.scan.observationMap ⁻¹' Hᶜ ∩ LateDropBound.hasDrop C s.normalize.scan := by
  simp only [StagePreHorizon.lowDropInput, Set.preimage_inter, Set.preimage_compl,
    NoDrop.observationMap_preimage_noDropTranscripts, LateDropBound.hasDrop]

/-- The input form of the high missed-pool event agrees with the horizon API. -/
theorem highMissInput_eq (s : BettingStrategy) (H : Set Cantor) (G : List ℕ) :
    StagePreHorizon.highMissInput s H G =
      s.normalize.scan.observationMap ⁻¹' H ∩
        {X | 0 < PoolQuery.missedCount s.normalize.scan G.toFinset
          (s.normalize.scan.observationMap X)} := by
  ext X
  simp only [StagePreHorizon.highMissInput, Set.mem_preimage, StagePreHorizon.highPoolMiss,
    Set.mem_ofPred_eq, Set.mem_inter_iff, PoolQuery.missedCount_pos_iff, List.mem_toFinset]

/-- Changing the syndrome preserves the low-drop input event. -/
@[simp] theorem lowDropInput_withSyndrome (s : BettingStrategy) (H : Set Cantor)
    (C : AffineBlock) (y : Fin C.rank → ZMod 2) :
    StagePreHorizon.lowDropInput s H (StageSyndrome.withSyndrome C y) =
      StagePreHorizon.lowDropInput s H C := rfl

/-- A positive-rank block with no drop must have an unread coordinate in
any containing pool. Hence its high no-drop event is covered by the same
high-miss event already bounded before horizon selection. -/
theorem high_noDrop_subset_highMiss (s : BettingStrategy) (H : Set Cantor)
    (C : AffineBlock) (G : List ℕ) (hCG : C.support ⊆ G.toFinset) (hr : 0 < C.rank) :
    s.normalize.scan.observationMap ⁻¹' H ∩ NoDrop.noDropEvent C s.normalize.scan ⊆
      StagePreHorizon.highMissInput s H G := by
  rw [highMissInput_eq]
  intro X hX
  refine ⟨hX.1, ?_⟩
  have hz : s.normalize.scan.observationMap X ∈
      NoDrop.noDropTranscripts C s.normalize.scan := by
    change X ∈ s.normalize.scan.observationMap ⁻¹' NoDrop.noDropTranscripts C s.normalize.scan
    rw [NoDrop.observationMap_preimage_noDropTranscripts]
    exact hX.2
  exact StageRank.noDropTranscripts_subset_missed C s.normalize.scan G.toFinset hCG hr hz

/-- The support of every concrete embedded candidate lies in the output pool. -/
theorem block_support_subset (G : List ℕ) (hG : G.Nodup) {m r : ℕ}
    (a : SparseListSearch.Entry) (ha : SparseListSearch.GoodEntry G.length m r a)
    (y : Fin r → ZMod 2) :
    (StageCandidate.block G.get hG.injective_get a ha y).support ⊆ G.toFinset := by
  intro p hp
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
  exact List.mem_toFinset.mpr (List.get_mem _ _)

/-- The block produced by the finite syndrome minimizer. -/
def chosenBlock (rules : List BettingStrategy) (cs : List AffineCode.Data)
    (G : List ℕ) (hG : G.Nodup) {m r : ℕ} (a : SparseListSearch.Entry)
    (ha : SparseListSearch.GoodEntry G.length m r a) (V : ℕ) : AffineBlock :=
  StageCandidate.block G.get hG.injective_get a ha
    (SparseSearch.wordVector r (StageSyndromeObjective.chosen rules cs G a V))

@[simp] theorem withSyndrome_block (G : List ℕ) (hG : G.Nodup) {m r : ℕ}
    (a : SparseListSearch.Entry) (ha : SparseListSearch.GoodEntry G.length m r a)
    (y z : Fin r → ZMod 2) :
    StageSyndrome.withSyndrome (StageCandidate.block G.get hG.injective_get a ha y) z =
      StageCandidate.block G.get hG.injective_get a ha z := rfl

end Klr.StageOneStep
