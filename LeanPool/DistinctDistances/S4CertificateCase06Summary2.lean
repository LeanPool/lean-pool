/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase06Data

/-!
# Subtree 2 of certificate case 6
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 2 of case 6. -/
noncomputable def case06Summary2 : PackedSummary := s4_summary% 6, case06Rows2

private theorem certificateCost :
    case06Rows2.sumNat (leafCost 256 params.box.nv case06Build) = case06Summary2.cost := by
  decide +kernel

private theorem certificateRhs :
    case06Rows2.sumInt (leafRhs case06Build) = case06Summary2.rhs := by
  decide +kernel

private theorem certificatePositive :
    case06Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case06Build Row.pos) =
      case06Summary2.positive := by
  decide +kernel

private theorem certificateNegative :
    case06Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case06Build Row.neg) =
      case06Summary2.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case06Summary2Checked :
    SummaryValid 256 params.box case06Build case06Rows2 case06Summary2 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
