/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase29Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 29
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 29. -/
noncomputable def case29Summary0 : PackedSummary := s4_summary% 29, case29Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case29Build case29Rows0 case29Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 29) (caseY.get 30)
    (by s4_check_equality)

private theorem certificateCost :
    case29Rows0.sumNat (leafCost 256 params.box.nv case29Build) = case29Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case29Rows0.sumInt (leafRhs case29Build) = case29Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case29Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case29Build Row.pos) =
      case29Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case29Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case29Build Row.neg) =
      case29Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case29Summary0Checked :
    SummaryValid 256 params.box case29Build case29Rows0 case29Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
