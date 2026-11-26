/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase22Data
import LeanPool.DistinctDistances.S4CertificateCachedRows
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 22
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 22. -/
noncomputable def case22Summary1 : PackedSummary := s4_summary% 22, case22Rows1

private theorem cachedReplay :
    replaySummaryWithCachedRows (caseY.get 22) (caseY.get 23)
      case22Rows1 = case22Summary1 := by
  s4_check_equality

private theorem certificateReplay :
    SummaryValid 256 params.box case22Build case22Rows1 case22Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 22) (caseY.get 23)
    (by
      as_aux_lemma => exact replaySummary_eq_of_cached cachedReplay)

private theorem certificateCost :
    case22Rows1.sumNat (leafCost 256 params.box.nv case22Build) = case22Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case22Rows1.sumInt (leafRhs case22Build) = case22Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case22Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case22Build Row.pos) =
      case22Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case22Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case22Build Row.neg) =
      case22Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case22Summary1Checked :
    SummaryValid 256 params.box case22Build case22Rows1 case22Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
