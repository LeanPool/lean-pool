/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase13Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 13
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 13. -/
noncomputable def case13Summary0 : PackedSummary := s4_summary% 13, case13Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case13Build case13Rows0 case13Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 13) (caseY.get 14)
    (by s4_check_equality)

private theorem certificateCost :
    case13Rows0.sumNat (leafCost 256 params.box.nv case13Build) = case13Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case13Rows0.sumInt (leafRhs case13Build) = case13Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case13Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case13Build Row.pos) =
      case13Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case13Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case13Build Row.neg) =
      case13Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case13Summary0Checked :
    SummaryValid 256 params.box case13Build case13Rows0 case13Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
