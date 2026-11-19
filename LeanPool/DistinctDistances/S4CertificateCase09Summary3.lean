/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase09Data

/-!
# Subtree 3 of certificate case 9
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 3 of case 9. -/
noncomputable def case09Summary3 : PackedSummary := s4_summary% 9, case09Rows3

private theorem certificateCost :
    case09Rows3.sumNat (leafCost 256 params.box.nv case09Build) = case09Summary3.cost := by
  decide +kernel

private theorem certificateRhs :
    case09Rows3.sumInt (leafRhs case09Build) = case09Summary3.rhs := by
  decide +kernel

private theorem certificatePositive :
    case09Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case09Build Row.pos) =
      case09Summary3.positive := by
  decide +kernel

private theorem certificateNegative :
    case09Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case09Build Row.neg) =
      case09Summary3.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case09Summary3Checked :
    SummaryValid 256 params.box case09Build case09Rows3 case09Summary3 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
