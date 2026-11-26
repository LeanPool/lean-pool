/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase06Data
import LeanPool.DistinctDistances.S4CertificateCachedRows
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 6
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 6. -/
noncomputable def case06Summary1 : PackedSummary := s4_summary% 6, case06Rows1

private theorem cachedReplay :
    replaySummaryWithCachedRows (caseY.get 6) (caseY.get 7)
      case06Rows1 = case06Summary1 := by
  s4_check_equality

private theorem certificateReplay :
    SummaryValid 256 params.box case06Build case06Rows1 case06Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 6) (caseY.get 7)
    (by
      as_aux_lemma => exact replaySummary_eq_of_cached cachedReplay)

private theorem certificateCost :
    case06Rows1.sumNat (leafCost 256 params.box.nv case06Build) = case06Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case06Rows1.sumInt (leafRhs case06Build) = case06Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case06Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case06Build Row.pos) =
      case06Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case06Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case06Build Row.neg) =
      case06Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case06Summary1Checked :
    SummaryValid 256 params.box case06Build case06Rows1 case06Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
