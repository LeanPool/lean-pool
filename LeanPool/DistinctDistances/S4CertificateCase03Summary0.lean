/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase03Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 3
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 3. -/
noncomputable def case03Summary0 : PackedSummary := s4_summary% 3, case03Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case03Build case03Rows0 case03Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 3) (caseY.get 4)
    (by s4_check_equality)

private theorem certificateCost :
    case03Rows0.sumNat (leafCost 256 params.box.nv case03Build) = case03Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case03Rows0.sumInt (leafRhs case03Build) = case03Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case03Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case03Build Row.pos) =
      case03Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case03Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case03Build Row.neg) =
      case03Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case03Summary0Checked :
    SummaryValid 256 params.box case03Build case03Rows0 case03Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
