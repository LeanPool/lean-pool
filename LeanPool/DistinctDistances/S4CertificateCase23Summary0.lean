/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase23Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 23
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 23. -/
noncomputable def case23Summary0 : PackedSummary := s4_summary% 23, case23Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case23Build case23Rows0 case23Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 23) (caseY.get 24)
    (by s4_check_equality)

private theorem certificateCost :
    case23Rows0.sumNat (leafCost 256 params.box.nv case23Build) = case23Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case23Rows0.sumInt (leafRhs case23Build) = case23Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case23Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case23Build Row.pos) =
      case23Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case23Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case23Build Row.neg) =
      case23Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case23Summary0Checked :
    SummaryValid 256 params.box case23Build case23Rows0 case23Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
