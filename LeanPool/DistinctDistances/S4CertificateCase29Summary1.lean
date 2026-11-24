/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase29Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 29
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 29. -/
noncomputable def case29Summary1 : PackedSummary := s4_summary% 29, case29Rows1

private theorem certificateReplay :
    SummaryValid 256 params.box case29Build case29Rows1 case29Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 29) (caseY.get 30)
    (by s4_check_equality)

private theorem certificateCost :
    case29Rows1.sumNat (leafCost 256 params.box.nv case29Build) = case29Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case29Rows1.sumInt (leafRhs case29Build) = case29Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case29Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case29Build Row.pos) =
      case29Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case29Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case29Build Row.neg) =
      case29Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case29Summary1Checked :
    SummaryValid 256 params.box case29Build case29Rows1 case29Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
