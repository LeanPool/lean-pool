/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase04Data

/-!
# Subtree 2 of certificate case 4
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 2 of case 4. -/
noncomputable def case04Summary2 : PackedSummary := s4_summary% 4, case04Rows2

private theorem certificateCost :
    case04Rows2.sumNat (leafCost 256 params.box.nv case04Build) = case04Summary2.cost := by
  decide +kernel

private theorem certificateRhs :
    case04Rows2.sumInt (leafRhs case04Build) = case04Summary2.rhs := by
  decide +kernel

private theorem certificatePositive :
    case04Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case04Build Row.pos) =
      case04Summary2.positive := by
  decide +kernel

private theorem certificateNegative :
    case04Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case04Build Row.neg) =
      case04Summary2.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case04Summary2Checked :
    SummaryValid 256 params.box case04Build case04Rows2 case04Summary2 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
