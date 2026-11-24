/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase24Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 24
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 24. -/
noncomputable def case24Summary1 : PackedSummary := s4_summary% 24, case24Rows1

private theorem certificateReplay :
    SummaryValid 256 params.box case24Build case24Rows1 case24Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 24) (caseY.get 25)
    (by s4_check_equality)

private theorem certificateCost :
    case24Rows1.sumNat (leafCost 256 params.box.nv case24Build) = case24Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case24Rows1.sumInt (leafRhs case24Build) = case24Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case24Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case24Build Row.pos) =
      case24Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case24Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case24Build Row.neg) =
      case24Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case24Summary1Checked :
    SummaryValid 256 params.box case24Build case24Rows1 case24Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
