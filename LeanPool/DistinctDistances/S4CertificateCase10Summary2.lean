/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase10Data

/-!
# Subtree 2 of certificate case 10
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 2 of case 10. -/
noncomputable def case10Summary2 : PackedSummary := s4_summary% 10, case10Rows2

private theorem certificateCost :
    case10Rows2.sumNat (leafCost 256 params.box.nv case10Build) = case10Summary2.cost := by
  decide +kernel

private theorem certificateRhs :
    case10Rows2.sumInt (leafRhs case10Build) = case10Summary2.rhs := by
  decide +kernel

private theorem certificatePositive :
    case10Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case10Build Row.pos) =
      case10Summary2.positive := by
  decide +kernel

private theorem certificateNegative :
    case10Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case10Build Row.neg) =
      case10Summary2.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case10Summary2Checked :
    SummaryValid 256 params.box case10Build case10Rows2 case10Summary2 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
