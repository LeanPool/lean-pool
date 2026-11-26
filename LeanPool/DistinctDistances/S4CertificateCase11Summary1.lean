/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase11Data
import LeanPool.DistinctDistances.S4CertificateCachedRows
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 11
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 11. -/
noncomputable def case11Summary1 : PackedSummary := s4_summary% 11, case11Rows1

private theorem cachedReplay :
    replaySummaryWithCachedRows (caseY.get 11) (caseY.get 12)
      case11Rows1 = case11Summary1 := by
  s4_check_equality

private theorem certificateReplay :
    SummaryValid 256 params.box case11Build case11Rows1 case11Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 11) (caseY.get 12)
    (by
      as_aux_lemma => exact replaySummary_eq_of_cached cachedReplay)

private theorem certificateCost :
    case11Rows1.sumNat (leafCost 256 params.box.nv case11Build) = case11Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case11Rows1.sumInt (leafRhs case11Build) = case11Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case11Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case11Build Row.pos) =
      case11Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case11Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case11Build Row.neg) =
      case11Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case11Summary1Checked :
    SummaryValid 256 params.box case11Build case11Rows1 case11Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
