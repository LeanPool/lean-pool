/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase04Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 4
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 4. -/
noncomputable def case04Summary0 : PackedSummary := s4_summary% 4, case04Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case04Build case04Rows0 case04Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 4) (caseY.get 5)
    (by s4_check_equality)

private theorem certificateCost :
    case04Rows0.sumNat (leafCost 256 params.box.nv case04Build) = case04Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case04Rows0.sumInt (leafRhs case04Build) = case04Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case04Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case04Build Row.pos) =
      case04Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case04Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case04Build Row.neg) =
      case04Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case04Summary0Checked :
    SummaryValid 256 params.box case04Build case04Rows0 case04Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
