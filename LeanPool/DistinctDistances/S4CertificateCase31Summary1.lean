/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase31Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 31
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 31. -/
noncomputable def case31Summary1 : PackedSummary := s4_summary% 31, case31Rows1

private theorem certificateReplay :
    SummaryValid 256 params.box case31Build case31Rows1 case31Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 31) (caseY.get 32)
    (by s4_check_equality)

private theorem certificateCost :
    case31Rows1.sumNat (leafCost 256 params.box.nv case31Build) = case31Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case31Rows1.sumInt (leafRhs case31Build) = case31Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case31Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case31Build Row.pos) =
      case31Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case31Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case31Build Row.neg) =
      case31Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case31Summary1Checked :
    SummaryValid 256 params.box case31Build case31Rows1 case31Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
