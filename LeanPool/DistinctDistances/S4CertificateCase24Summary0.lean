/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase24Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 24
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 24. -/
noncomputable def case24Summary0 : PackedSummary := s4_summary% 24, case24Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case24Build case24Rows0 case24Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 24) (caseY.get 25)
    (by s4_check_equality)

private theorem certificateCost :
    case24Rows0.sumNat (leafCost 256 params.box.nv case24Build) = case24Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case24Rows0.sumInt (leafRhs case24Build) = case24Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case24Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case24Build Row.pos) =
      case24Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case24Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case24Build Row.neg) =
      case24Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case24Summary0Checked :
    SummaryValid 256 params.box case24Build case24Rows0 case24Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
