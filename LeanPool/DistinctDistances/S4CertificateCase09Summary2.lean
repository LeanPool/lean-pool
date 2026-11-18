/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase09Data

/-!
# Subtree 2 of certificate case 9
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 2 of case 9. -/
noncomputable def case09Summary2 : PackedSummary := s4_summary% 9, case09Rows2

private theorem certificateCost :
    case09Rows2.sumNat (leafCost 256 params.box.nv case09Build) = case09Summary2.cost := by
  decide +kernel

private theorem certificateRhs :
    case09Rows2.sumInt (leafRhs case09Build) = case09Summary2.rhs := by
  decide +kernel

private theorem certificatePositive :
    case09Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case09Build Row.pos) =
      case09Summary2.positive := by
  decide +kernel

private theorem certificateNegative :
    case09Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case09Build Row.neg) =
      case09Summary2.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case09Summary2Checked :
    SummaryValid 256 params.box case09Build case09Rows2 case09Summary2 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
