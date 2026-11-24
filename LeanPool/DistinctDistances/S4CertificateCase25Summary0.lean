/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase25Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 25
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 25. -/
noncomputable def case25Summary0 : PackedSummary := s4_summary% 25, case25Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case25Build case25Rows0 case25Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 25) (caseY.get 26)
    (by s4_check_equality)

private theorem certificateCost :
    case25Rows0.sumNat (leafCost 256 params.box.nv case25Build) = case25Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case25Rows0.sumInt (leafRhs case25Build) = case25Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case25Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case25Build Row.pos) =
      case25Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case25Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case25Build Row.neg) =
      case25Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case25Summary0Checked :
    SummaryValid 256 params.box case25Build case25Rows0 case25Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
