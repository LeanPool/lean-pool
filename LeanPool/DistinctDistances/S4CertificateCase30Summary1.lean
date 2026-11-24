/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase30Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 30
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 30. -/
noncomputable def case30Summary1 : PackedSummary := s4_summary% 30, case30Rows1

private theorem certificateReplay :
    SummaryValid 256 params.box case30Build case30Rows1 case30Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 30) (caseY.get 31)
    (by s4_check_equality)

private theorem certificateCost :
    case30Rows1.sumNat (leafCost 256 params.box.nv case30Build) = case30Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case30Rows1.sumInt (leafRhs case30Build) = case30Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case30Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case30Build Row.pos) =
      case30Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case30Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case30Build Row.neg) =
      case30Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case30Summary1Checked :
    SummaryValid 256 params.box case30Build case30Rows1 case30Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
