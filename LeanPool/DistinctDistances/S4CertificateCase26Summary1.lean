/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase26Data
import LeanPool.DistinctDistances.S4CertificateCachedRows
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 26
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 26. -/
noncomputable def case26Summary1 : PackedSummary := s4_summary% 26, case26Rows1

private theorem cachedReplay :
    replaySummaryWithCachedRows (caseY.get 26) (caseY.get 27)
      case26Rows1 = case26Summary1 := by
  s4_check_equality

private theorem certificateReplay :
    SummaryValid 256 params.box case26Build case26Rows1 case26Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 26) (caseY.get 27)
    (by
      as_aux_lemma => exact replaySummary_eq_of_cached cachedReplay)

private theorem certificateCost :
    case26Rows1.sumNat (leafCost 256 params.box.nv case26Build) = case26Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case26Rows1.sumInt (leafRhs case26Build) = case26Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case26Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case26Build Row.pos) =
      case26Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case26Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case26Build Row.neg) =
      case26Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case26Summary1Checked :
    SummaryValid 256 params.box case26Build case26Rows1 case26Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
