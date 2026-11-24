/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase27Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 27
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 27. -/
noncomputable def case27Summary1 : PackedSummary := s4_summary% 27, case27Rows1

private theorem certificateReplay :
    SummaryValid 256 params.box case27Build case27Rows1 case27Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 27) (caseY.get 28)
    (by s4_check_equality)

private theorem certificateCost :
    case27Rows1.sumNat (leafCost 256 params.box.nv case27Build) = case27Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case27Rows1.sumInt (leafRhs case27Build) = case27Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case27Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case27Build Row.pos) =
      case27Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case27Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case27Build Row.neg) =
      case27Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case27Summary1Checked :
    SummaryValid 256 params.box case27Build case27Rows1 case27Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
