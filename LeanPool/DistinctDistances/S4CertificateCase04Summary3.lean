/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase04Data
import LeanPool.DistinctDistances.S4CertificateCachedRows
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 3 of certificate case 4
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 3 of case 4. -/
noncomputable def case04Summary3 : PackedSummary := s4_summary% 4, case04Rows3

private theorem cachedReplay :
    replaySummaryWithCachedRows (caseY.get 4) (caseY.get 5)
      case04Rows3 = case04Summary3 := by
  s4_check_equality

private theorem certificateReplay :
    SummaryValid 256 params.box case04Build case04Rows3 case04Summary3 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 4) (caseY.get 5)
    (by
      as_aux_lemma => exact replaySummary_eq_of_cached cachedReplay)

private theorem certificateCost :
    case04Rows3.sumNat (leafCost 256 params.box.nv case04Build) = case04Summary3.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case04Rows3.sumInt (leafRhs case04Build) = case04Summary3.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case04Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case04Build Row.pos) =
      case04Summary3.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case04Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case04Build Row.neg) =
      case04Summary3.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case04Summary3Checked :
    SummaryValid 256 params.box case04Build case04Rows3 case04Summary3 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
