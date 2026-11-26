/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase14Data
import LeanPool.DistinctDistances.S4CertificateCachedRows
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 14
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 14. -/
noncomputable def case14Summary0 : PackedSummary := s4_summary% 14, case14Rows0

private theorem cachedReplay :
    replaySummaryWithCachedRows (caseY.get 14) (caseY.get 15)
      case14Rows0 = case14Summary0 := by
  s4_check_equality

private theorem certificateReplay :
    SummaryValid 256 params.box case14Build case14Rows0 case14Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 14) (caseY.get 15)
    (by
      as_aux_lemma => exact replaySummary_eq_of_cached cachedReplay)

private theorem certificateCost :
    case14Rows0.sumNat (leafCost 256 params.box.nv case14Build) = case14Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case14Rows0.sumInt (leafRhs case14Build) = case14Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case14Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case14Build Row.pos) =
      case14Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case14Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case14Build Row.neg) =
      case14Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case14Summary0Checked :
    SummaryValid 256 params.box case14Build case14Rows0 case14Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
