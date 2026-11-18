/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase09Data

/-!
# Subtree 1 of certificate case 9
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 9. -/
noncomputable def case09Summary1 : PackedSummary := s4_summary% 9, case09Rows1

private theorem certificateCost :
    case09Rows1.sumNat (leafCost 256 params.box.nv case09Build) = case09Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case09Rows1.sumInt (leafRhs case09Build) = case09Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case09Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case09Build Row.pos) =
      case09Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case09Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case09Build Row.neg) =
      case09Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case09Summary1Checked :
    SummaryValid 256 params.box case09Build case09Rows1 case09Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
