/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase32Data
import LeanPool.DistinctDistances.S4CertificateCachedRows
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 32
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 32. -/
noncomputable def case32Summary1 : PackedSummary := s4_summary% 32, case32Rows1

private theorem cachedReplay :
    replaySummaryWithCachedRows (caseY.get 32) (caseY.get 33)
      case32Rows1 = case32Summary1 := by
  s4_check_equality

private theorem certificateReplay :
    SummaryValid 256 params.box case32Build case32Rows1 case32Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 32) (caseY.get 33)
    (by
      as_aux_lemma => exact replaySummary_eq_of_cached cachedReplay)

private theorem certificateCost :
    case32Rows1.sumNat (leafCost 256 params.box.nv case32Build) = case32Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case32Rows1.sumInt (leafRhs case32Build) = case32Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case32Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case32Build Row.pos) =
      case32Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case32Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case32Build Row.neg) =
      case32Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case32Summary1Checked :
    SummaryValid 256 params.box case32Build case32Rows1 case32Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
