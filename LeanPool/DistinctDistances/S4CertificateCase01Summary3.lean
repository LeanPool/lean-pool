/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase01Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 3 of certificate case 1
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 3 of case 1. -/
noncomputable def case01Summary3 : PackedSummary := s4_summary% 1, case01Rows3

private theorem certificateReplay :
    SummaryValid 256 params.box case01Build case01Rows3 case01Summary3 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 1) (caseY.get 2)
    (by s4_check_equality)

private theorem certificateCost :
    case01Rows3.sumNat (leafCost 256 params.box.nv case01Build) = case01Summary3.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case01Rows3.sumInt (leafRhs case01Build) = case01Summary3.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case01Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case01Build Row.pos) =
      case01Summary3.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case01Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case01Build Row.neg) =
      case01Summary3.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case01Summary3Checked :
    SummaryValid 256 params.box case01Build case01Rows3 case01Summary3 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
