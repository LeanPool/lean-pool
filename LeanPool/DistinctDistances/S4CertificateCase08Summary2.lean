/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase08Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 2 of certificate case 8
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 2 of case 8. -/
noncomputable def case08Summary2 : PackedSummary := s4_summary% 8, case08Rows2

private theorem certificateReplay :
    SummaryValid 256 params.box case08Build case08Rows2 case08Summary2 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 8) (caseY.get 9)
    (by s4_check_equality)

private theorem certificateCost :
    case08Rows2.sumNat (leafCost 256 params.box.nv case08Build) = case08Summary2.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case08Rows2.sumInt (leafRhs case08Build) = case08Summary2.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case08Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case08Build Row.pos) =
      case08Summary2.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case08Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case08Build Row.neg) =
      case08Summary2.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case08Summary2Checked :
    SummaryValid 256 params.box case08Build case08Rows2 case08Summary2 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
