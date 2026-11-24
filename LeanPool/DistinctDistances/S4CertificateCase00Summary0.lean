/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase00Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 0
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 0. -/
noncomputable def case00Summary0 : PackedSummary := s4_summary% 0, case00Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case00Build case00Rows0 case00Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 0) (caseY.get 1)
    (by s4_check_equality)

private theorem certificateCost :
    case00Rows0.sumNat (leafCost 256 params.box.nv case00Build) = case00Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case00Rows0.sumInt (leafRhs case00Build) = case00Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case00Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case00Build Row.pos) =
      case00Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case00Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case00Build Row.neg) =
      case00Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case00Summary0Checked :
    SummaryValid 256 params.box case00Build case00Rows0 case00Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
