/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase17Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 17
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 17. -/
noncomputable def case17Summary0 : PackedSummary := s4_summary% 17, case17Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case17Build case17Rows0 case17Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 17) (caseY.get 18)
    (by s4_check_equality)

private theorem certificateCost :
    case17Rows0.sumNat (leafCost 256 params.box.nv case17Build) = case17Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case17Rows0.sumInt (leafRhs case17Build) = case17Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case17Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case17Build Row.pos) =
      case17Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case17Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case17Build Row.neg) =
      case17Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case17Summary0Checked :
    SummaryValid 256 params.box case17Build case17Rows0 case17Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
