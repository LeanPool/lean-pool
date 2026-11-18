/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase01Data

/-!
# Subtree 2 of certificate case 1
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 2 of case 1. -/
noncomputable def case01Summary2 : PackedSummary := s4_summary% 1, case01Rows2

private theorem certificateCost :
    case01Rows2.sumNat (leafCost 256 params.box.nv case01Build) = case01Summary2.cost := by
  decide +kernel

private theorem certificateRhs :
    case01Rows2.sumInt (leafRhs case01Build) = case01Summary2.rhs := by
  decide +kernel

private theorem certificatePositive :
    case01Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case01Build Row.pos) =
      case01Summary2.positive := by
  decide +kernel

private theorem certificateNegative :
    case01Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case01Build Row.neg) =
      case01Summary2.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case01Summary2Checked :
    SummaryValid 256 params.box case01Build case01Rows2 case01Summary2 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
