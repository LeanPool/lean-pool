/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase18Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 18
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 18. -/
noncomputable def case18Summary0 : PackedSummary := s4_summary% 18, case18Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case18Build case18Rows0 case18Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 18) (caseY.get 19)
    (by s4_check_equality)

private theorem certificateCost :
    case18Rows0.sumNat (leafCost 256 params.box.nv case18Build) = case18Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case18Rows0.sumInt (leafRhs case18Build) = case18Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case18Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case18Build Row.pos) =
      case18Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case18Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case18Build Row.neg) =
      case18Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case18Summary0Checked :
    SummaryValid 256 params.box case18Build case18Rows0 case18Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
