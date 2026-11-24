/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase16Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 16
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 16. -/
noncomputable def case16Summary0 : PackedSummary := s4_summary% 16, case16Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case16Build case16Rows0 case16Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 16) (caseY.get 17)
    (by s4_check_equality)

private theorem certificateCost :
    case16Rows0.sumNat (leafCost 256 params.box.nv case16Build) = case16Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case16Rows0.sumInt (leafRhs case16Build) = case16Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case16Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case16Build Row.pos) =
      case16Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case16Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case16Build Row.neg) =
      case16Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case16Summary0Checked :
    SummaryValid 256 params.box case16Build case16Rows0 case16Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
