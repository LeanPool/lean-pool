/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase01Data

/-!
# Subtree 0 of certificate case 1
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 1. -/
noncomputable def case01Summary0 : PackedSummary := s4_summary% 1, case01Rows0

private theorem certificateCost :
    case01Rows0.sumNat (leafCost 256 params.box.nv case01Build) = case01Summary0.cost := by
  decide +kernel

private theorem certificateRhs :
    case01Rows0.sumInt (leafRhs case01Build) = case01Summary0.rhs := by
  decide +kernel

private theorem certificatePositive :
    case01Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case01Build Row.pos) =
      case01Summary0.positive := by
  decide +kernel

private theorem certificateNegative :
    case01Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case01Build Row.neg) =
      case01Summary0.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case01Summary0Checked :
    SummaryValid 256 params.box case01Build case01Rows0 case01Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
