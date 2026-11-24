/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase33Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 33
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 33. -/
noncomputable def case33Summary0 : PackedSummary := s4_summary% 33, case33Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case33Build case33Rows0 case33Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 33) (caseY.get 34)
    (by s4_check_equality)

private theorem certificateCost :
    case33Rows0.sumNat (leafCost 256 params.box.nv case33Build) = case33Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case33Rows0.sumInt (leafRhs case33Build) = case33Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case33Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case33Build Row.pos) =
      case33Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case33Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case33Build Row.neg) =
      case33Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case33Summary0Checked :
    SummaryValid 256 params.box case33Build case33Rows0 case33Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
