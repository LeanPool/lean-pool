/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoveragePairRowIndexMasks
public import LeanPool.Erdos97ConvexOctagon.CoverageSearchRowChoiceSoundness
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Soundness of the transposed legal-row pair masks -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence

-- Bound each kernel reduction cache to one centre of the finite table.
private theorem pairRowIndexMasks_bit_centre_0 :
    ∀ (pairIndex : Fin 64) (rowIndex : Fin 35),
      bitSetB ((pairRowIndexMasks.getD 0 #[]).getD pairIndex.val 0) rowIndex.val =
        bitSetB (searchRowChoiceAt 0 rowIndex).pairMask pairIndex.val := by
  decide +kernel

private theorem pairRowIndexMasks_bit_centre_1 :
    ∀ (pairIndex : Fin 64) (rowIndex : Fin 35),
      bitSetB ((pairRowIndexMasks.getD 1 #[]).getD pairIndex.val 0) rowIndex.val =
        bitSetB (searchRowChoiceAt 1 rowIndex).pairMask pairIndex.val := by
  decide +kernel

private theorem pairRowIndexMasks_bit_centre_2 :
    ∀ (pairIndex : Fin 64) (rowIndex : Fin 35),
      bitSetB ((pairRowIndexMasks.getD 2 #[]).getD pairIndex.val 0) rowIndex.val =
        bitSetB (searchRowChoiceAt 2 rowIndex).pairMask pairIndex.val := by
  decide +kernel

private theorem pairRowIndexMasks_bit_centre_3 :
    ∀ (pairIndex : Fin 64) (rowIndex : Fin 35),
      bitSetB ((pairRowIndexMasks.getD 3 #[]).getD pairIndex.val 0) rowIndex.val =
        bitSetB (searchRowChoiceAt 3 rowIndex).pairMask pairIndex.val := by
  decide +kernel

private theorem pairRowIndexMasks_bit_centre_4 :
    ∀ (pairIndex : Fin 64) (rowIndex : Fin 35),
      bitSetB ((pairRowIndexMasks.getD 4 #[]).getD pairIndex.val 0) rowIndex.val =
        bitSetB (searchRowChoiceAt 4 rowIndex).pairMask pairIndex.val := by
  decide +kernel

private theorem pairRowIndexMasks_bit_centre_5 :
    ∀ (pairIndex : Fin 64) (rowIndex : Fin 35),
      bitSetB ((pairRowIndexMasks.getD 5 #[]).getD pairIndex.val 0) rowIndex.val =
        bitSetB (searchRowChoiceAt 5 rowIndex).pairMask pairIndex.val := by
  decide +kernel

private theorem pairRowIndexMasks_bit_centre_6 :
    ∀ (pairIndex : Fin 64) (rowIndex : Fin 35),
      bitSetB ((pairRowIndexMasks.getD 6 #[]).getD pairIndex.val 0) rowIndex.val =
        bitSetB (searchRowChoiceAt 6 rowIndex).pairMask pairIndex.val := by
  decide +kernel

private theorem pairRowIndexMasks_bit_centre_7 :
    ∀ (pairIndex : Fin 64) (rowIndex : Fin 35),
      bitSetB ((pairRowIndexMasks.getD 7 #[]).getD pairIndex.val 0) rowIndex.val =
        bitSetB (searchRowChoiceAt 7 rowIndex).pairMask pairIndex.val := by
  decide +kernel

/-- The transposed pair table records exactly which row choices contain each pair bit. -/
theorem pairRowIndexMasks_bit
    (centre : Vertex) (pairIndex : Fin 64) (rowIndex : Fin 35) :
    bitSetB ((pairRowIndexMasks.getD centre.val #[]).getD pairIndex.val 0)
        rowIndex.val =
      bitSetB (searchRowChoiceAt centre rowIndex).pairMask pairIndex.val := by
  revert centre pairIndex rowIndex
  as_aux_lemma =>
    intro centre
    fin_cases centre
    · exact pairRowIndexMasks_bit_centre_0
    · exact pairRowIndexMasks_bit_centre_1
    · exact pairRowIndexMasks_bit_centre_2
    · exact pairRowIndexMasks_bit_centre_3
    · exact pairRowIndexMasks_bit_centre_4
    · exact pairRowIndexMasks_bit_centre_5
    · exact pairRowIndexMasks_bit_centre_6
    · exact pairRowIndexMasks_bit_centre_7

end Erdos97Octagon.RawIncidence
