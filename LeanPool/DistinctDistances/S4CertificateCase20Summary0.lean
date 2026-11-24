/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase20Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 20
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 20. -/
noncomputable def case20Summary0 : PackedSummary := s4_summary% 20, case20Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case20Build case20Rows0 case20Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 20) (caseY.get 21)
    (by s4_check_equality)

private theorem certificateCost :
    case20Rows0.sumNat (leafCost 256 params.box.nv case20Build) = case20Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case20Rows0.sumInt (leafRhs case20Build) = case20Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case20Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case20Build Row.pos) =
      case20Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case20Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case20Build Row.neg) =
      case20Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case20Summary0Checked :
    SummaryValid 256 params.box case20Build case20Rows0 case20Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
