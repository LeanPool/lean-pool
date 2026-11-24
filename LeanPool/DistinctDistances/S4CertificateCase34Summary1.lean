/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase34Data
import LeanPool.DistinctDistances.S4CertificateKernelReplay -- shake: keep

/-!
# Subtree 1 of certificate case 34
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 34. -/
noncomputable def case34Summary1 : PackedSummary := s4_summary% 34, case34Rows1

private theorem certificateReplay :
    SummaryValid 256 params.box case34Build case34Rows1 case34Summary1 :=
  summaryValidOfSharedDenominatorReplay params (caseY.get 34) (caseY.get 35)
    (by s4_check_equality)

private theorem certificateCost :
    case34Rows1.sumNat (leafCost 256 params.box.nv case34Build) = case34Summary1.cost := by
  as_aux_lemma => exact certificateReplay.cost_eq

private theorem certificateRhs :
    case34Rows1.sumInt (leafRhs case34Build) = case34Summary1.rhs := by
  as_aux_lemma => exact certificateReplay.rhs_eq

private theorem certificatePositive :
    case34Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case34Build Row.pos) =
      case34Summary1.positive := by
  as_aux_lemma => exact certificateReplay.positive_eq

private theorem certificateNegative :
    case34Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case34Build Row.neg) =
      case34Summary1.negative := by
  as_aux_lemma => exact certificateReplay.negative_eq

/-- Kernel verification of all four quantities for this subtree. -/
theorem case34Summary1Checked :
    SummaryValid 256 params.box case34Build case34Rows1 case34Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
