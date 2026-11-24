/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase23Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 23
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 23. -/
noncomputable def case23Summary1 : PackedSummary := s4_summary% 23, case23Rows1

private theorem certificateReplay :
    SummaryValid 256 params.box case23Build case23Rows1 case23Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 23) (caseY.get 24)
    (by s4_check_equality)

private theorem certificateCost :
    case23Rows1.sumNat (leafCost 256 params.box.nv case23Build) = case23Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case23Rows1.sumInt (leafRhs case23Build) = case23Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case23Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case23Build Row.pos) =
      case23Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case23Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case23Build Row.neg) =
      case23Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case23Summary1Checked :
    SummaryValid 256 params.box case23Build case23Rows1 case23Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
