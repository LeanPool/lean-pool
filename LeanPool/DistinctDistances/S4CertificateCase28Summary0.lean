/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase28Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 28
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 28. -/
noncomputable def case28Summary0 : PackedSummary := s4_summary% 28, case28Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case28Build case28Rows0 case28Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 28) (caseY.get 29)
    (by s4_check_equality)

private theorem certificateCost :
    case28Rows0.sumNat (leafCost 256 params.box.nv case28Build) = case28Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case28Rows0.sumInt (leafRhs case28Build) = case28Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case28Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case28Build Row.pos) =
      case28Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case28Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case28Build Row.neg) =
      case28Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case28Summary0Checked :
    SummaryValid 256 params.box case28Build case28Rows0 case28Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
