/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase01Data

/-!
# Subtree 3 of certificate case 1
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 3 of case 1. -/
noncomputable def case01Summary3 : PackedSummary := s4_summary% 1, case01Rows3

private theorem certificateCost :
    case01Rows3.sumNat (leafCost 256 params.box.nv case01Build) = case01Summary3.cost := by
  decide +kernel

private theorem certificateRhs :
    case01Rows3.sumInt (leafRhs case01Build) = case01Summary3.rhs := by
  decide +kernel

private theorem certificatePositive :
    case01Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case01Build Row.pos) =
      case01Summary3.positive := by
  decide +kernel

private theorem certificateNegative :
    case01Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case01Build Row.neg) =
      case01Summary3.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case01Summary3Checked :
    SummaryValid 256 params.box case01Build case01Rows3 case01Summary3 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
