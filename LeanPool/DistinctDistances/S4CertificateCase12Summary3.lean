/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase12Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 3 of certificate case 12
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 3 of case 12. -/
noncomputable def case12Summary3 : PackedSummary := s4_summary% 12, case12Rows3

private theorem certificateReplay :
    SummaryValid 256 params.box case12Build case12Rows3 case12Summary3 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 12) (caseY.get 13)
    (by s4_check_equality)

private theorem certificateCost :
    case12Rows3.sumNat (leafCost 256 params.box.nv case12Build) = case12Summary3.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case12Rows3.sumInt (leafRhs case12Build) = case12Summary3.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case12Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case12Build Row.pos) =
      case12Summary3.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case12Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case12Build Row.neg) =
      case12Summary3.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case12Summary3Checked :
    SummaryValid 256 params.box case12Build case12Rows3 case12Summary3 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
