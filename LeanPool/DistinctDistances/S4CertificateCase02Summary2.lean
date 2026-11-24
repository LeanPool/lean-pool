/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase02Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 2 of certificate case 2
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 2 of case 2. -/
noncomputable def case02Summary2 : PackedSummary := s4_summary% 2, case02Rows2

private theorem certificateReplay :
    SummaryValid 256 params.box case02Build case02Rows2 case02Summary2 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 2) (caseY.get 3)
    (by s4_check_equality)

private theorem certificateCost :
    case02Rows2.sumNat (leafCost 256 params.box.nv case02Build) = case02Summary2.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case02Rows2.sumInt (leafRhs case02Build) = case02Summary2.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case02Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case02Build Row.pos) =
      case02Summary2.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case02Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case02Build Row.neg) =
      case02Summary2.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case02Summary2Checked :
    SummaryValid 256 params.box case02Build case02Rows2 case02Summary2 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
