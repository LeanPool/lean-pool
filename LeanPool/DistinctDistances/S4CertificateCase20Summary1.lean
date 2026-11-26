/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase20Data
import LeanPool.DistinctDistances.S4CertificateCachedRows
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 20
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 20. -/
noncomputable def case20Summary1 : PackedSummary := s4_summary% 20, case20Rows1

private theorem cachedReplay :
    replaySummaryWithCachedRows (caseY.get 20) (caseY.get 21)
      case20Rows1 = case20Summary1 := by
  s4_check_equality

private theorem certificateReplay :
    SummaryValid 256 params.box case20Build case20Rows1 case20Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 20) (caseY.get 21)
    (by
      as_aux_lemma => exact replaySummary_eq_of_cached cachedReplay)

private theorem certificateCost :
    case20Rows1.sumNat (leafCost 256 params.box.nv case20Build) = case20Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case20Rows1.sumInt (leafRhs case20Build) = case20Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case20Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case20Build Row.pos) =
      case20Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case20Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case20Build Row.neg) =
      case20Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case20Summary1Checked :
    SummaryValid 256 params.box case20Build case20Rows1 case20Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
