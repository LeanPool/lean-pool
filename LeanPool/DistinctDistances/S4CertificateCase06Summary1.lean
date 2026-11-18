/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase06Data

/-!
# Subtree 1 of certificate case 6
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 6. -/
noncomputable def case06Summary1 : PackedSummary := s4_summary% 6, case06Rows1

private theorem certificateCost :
    case06Rows1.sumNat (leafCost 256 params.box.nv case06Build) = case06Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case06Rows1.sumInt (leafRhs case06Build) = case06Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case06Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case06Build Row.pos) =
      case06Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case06Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case06Build Row.neg) =
      case06Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case06Summary1Checked :
    SummaryValid 256 params.box case06Build case06Rows1 case06Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
