/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase08Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 8
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 8. -/
noncomputable def case08Summary0 : PackedSummary := s4_summary% 8, case08Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case08Build case08Rows0 case08Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 8) (caseY.get 9)
    (by s4_check_equality)

private theorem certificateCost :
    case08Rows0.sumNat (leafCost 256 params.box.nv case08Build) = case08Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case08Rows0.sumInt (leafRhs case08Build) = case08Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case08Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case08Build Row.pos) =
      case08Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case08Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case08Build Row.neg) =
      case08Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case08Summary0Checked :
    SummaryValid 256 params.box case08Build case08Rows0 case08Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
