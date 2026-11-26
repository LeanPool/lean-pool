/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase13Data
import LeanPool.DistinctDistances.S4CertificateCachedRows
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 13
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 13. -/
noncomputable def case13Summary1 : PackedSummary := s4_summary% 13, case13Rows1

private theorem cachedReplay :
    replaySummaryWithCachedRows (caseY.get 13) (caseY.get 14)
      case13Rows1 = case13Summary1 := by
  s4_check_equality

private theorem certificateReplay :
    SummaryValid 256 params.box case13Build case13Rows1 case13Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 13) (caseY.get 14)
    (by
      as_aux_lemma => exact replaySummary_eq_of_cached cachedReplay)

private theorem certificateCost :
    case13Rows1.sumNat (leafCost 256 params.box.nv case13Build) = case13Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case13Rows1.sumInt (leafRhs case13Build) = case13Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case13Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case13Build Row.pos) =
      case13Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case13Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case13Build Row.neg) =
      case13Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case13Summary1Checked :
    SummaryValid 256 params.box case13Build case13Rows1 case13Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
