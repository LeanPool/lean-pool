/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase07Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 0 of certificate case 7
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 7. -/
noncomputable def case07Summary0 : PackedSummary := s4_summary% 7, case07Rows0

private theorem certificateReplay :
    SummaryValid 256 params.box case07Build case07Rows0 case07Summary0 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 7) (caseY.get 8)
    (by s4_check_equality)

private theorem certificateCost :
    case07Rows0.sumNat (leafCost 256 params.box.nv case07Build) = case07Summary0.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case07Rows0.sumInt (leafRhs case07Build) = case07Summary0.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case07Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case07Build Row.pos) =
      case07Summary0.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case07Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case07Build Row.neg) =
      case07Summary0.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case07Summary0Checked :
    SummaryValid 256 params.box case07Build case07Rows0 case07Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
