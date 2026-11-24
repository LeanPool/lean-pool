/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase05Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 5
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 5. -/
noncomputable def case05Summary1 : PackedSummary := s4_summary% 5, case05Rows1

private theorem certificateReplay :
    SummaryValid 256 params.box case05Build case05Rows1 case05Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 5) (caseY.get 6)
    (by s4_check_equality)

private theorem certificateCost :
    case05Rows1.sumNat (leafCost 256 params.box.nv case05Build) = case05Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case05Rows1.sumInt (leafRhs case05Build) = case05Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case05Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case05Build Row.pos) =
      case05Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case05Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case05Build Row.neg) =
      case05Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case05Summary1Checked :
    SummaryValid 256 params.box case05Build case05Rows1 case05Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
