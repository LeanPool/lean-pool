/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase11Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 3 of certificate case 11
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 3 of case 11. -/
noncomputable def case11Summary3 : PackedSummary := s4_summary% 11, case11Rows3

private theorem certificateReplay :
    SummaryValid 256 params.box case11Build case11Rows3 case11Summary3 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 11) (caseY.get 12)
    (by s4_check_equality)

private theorem certificateCost :
    case11Rows3.sumNat (leafCost 256 params.box.nv case11Build) = case11Summary3.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case11Rows3.sumInt (leafRhs case11Build) = case11Summary3.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case11Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case11Build Row.pos) =
      case11Summary3.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case11Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case11Build Row.neg) =
      case11Summary3.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case11Summary3Checked :
    SummaryValid 256 params.box case11Build case11Rows3 case11Summary3 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
