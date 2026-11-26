/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase10Data
import LeanPool.DistinctDistances.S4CertificateCachedRows
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 10
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 10. -/
noncomputable def case10Summary1 : PackedSummary := s4_summary% 10, case10Rows1

private theorem cachedReplay :
    replaySummaryWithCachedRows (caseY.get 10) (caseY.get 11)
      case10Rows1 = case10Summary1 := by
  s4_check_equality

private theorem certificateReplay :
    SummaryValid 256 params.box case10Build case10Rows1 case10Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 10) (caseY.get 11)
    (by
      as_aux_lemma => exact replaySummary_eq_of_cached cachedReplay)

private theorem certificateCost :
    case10Rows1.sumNat (leafCost 256 params.box.nv case10Build) = case10Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case10Rows1.sumInt (leafRhs case10Build) = case10Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case10Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case10Build Row.pos) =
      case10Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case10Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case10Build Row.neg) =
      case10Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case10Summary1Checked :
    SummaryValid 256 params.box case10Build case10Rows1 case10Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
