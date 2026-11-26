/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase09Data
import LeanPool.DistinctDistances.S4CertificateCachedRows
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 3 of certificate case 9
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 3 of case 9. -/
noncomputable def case09Summary3 : PackedSummary := s4_summary% 9, case09Rows3

private theorem cachedReplay :
    replaySummaryWithCachedRows (caseY.get 9) (caseY.get 10)
      case09Rows3 = case09Summary3 := by
  s4_check_equality

private theorem certificateReplay :
    SummaryValid 256 params.box case09Build case09Rows3 case09Summary3 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 9) (caseY.get 10)
    (by
      as_aux_lemma => exact replaySummary_eq_of_cached cachedReplay)

private theorem certificateCost :
    case09Rows3.sumNat (leafCost 256 params.box.nv case09Build) = case09Summary3.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case09Rows3.sumInt (leafRhs case09Build) = case09Summary3.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case09Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case09Build Row.pos) =
      case09Summary3.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case09Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case09Build Row.neg) =
      case09Summary3.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case09Summary3Checked :
    SummaryValid 256 params.box case09Build case09Rows3 case09Summary3 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
