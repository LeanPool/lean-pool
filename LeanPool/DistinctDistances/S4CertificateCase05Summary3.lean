/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase05Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 3 of certificate case 5
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 3 of case 5. -/
noncomputable def case05Summary3 : PackedSummary := s4_summary% 5, case05Rows3

private theorem certificateReplay :
    SummaryValid 256 params.box case05Build case05Rows3 case05Summary3 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 5) (caseY.get 6)
    (by s4_check_equality)

private theorem certificateCost :
    case05Rows3.sumNat (leafCost 256 params.box.nv case05Build) = case05Summary3.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case05Rows3.sumInt (leafRhs case05Build) = case05Summary3.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case05Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case05Build Row.pos) =
      case05Summary3.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case05Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case05Build Row.neg) =
      case05Summary3.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case05Summary3Checked :
    SummaryValid 256 params.box case05Build case05Rows3 case05Summary3 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
