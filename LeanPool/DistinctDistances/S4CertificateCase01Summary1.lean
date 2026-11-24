/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase01Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 1
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 1. -/
noncomputable def case01Summary1 : PackedSummary := s4_summary% 1, case01Rows1

private theorem certificateReplay :
    SummaryValid 256 params.box case01Build case01Rows1 case01Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 1) (caseY.get 2)
    (by s4_check_equality)

private theorem certificateCost :
    case01Rows1.sumNat (leafCost 256 params.box.nv case01Build) = case01Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case01Rows1.sumInt (leafRhs case01Build) = case01Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case01Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case01Build Row.pos) =
      case01Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case01Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case01Build Row.neg) =
      case01Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case01Summary1Checked :
    SummaryValid 256 params.box case01Build case01Rows1 case01Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
