/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase06Data

/-!
# Subtree 3 of certificate case 6
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 3 of case 6. -/
noncomputable def case06Summary3 : PackedSummary := s4_summary% 6, case06Rows3

private theorem certificateCost :
    case06Rows3.sumNat (leafCost 256 params.box.nv case06Build) = case06Summary3.cost := by
  decide +kernel

private theorem certificateRhs :
    case06Rows3.sumInt (leafRhs case06Build) = case06Summary3.rhs := by
  decide +kernel

private theorem certificatePositive :
    case06Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case06Build Row.pos) =
      case06Summary3.positive := by
  decide +kernel

private theorem certificateNegative :
    case06Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case06Build Row.neg) =
      case06Summary3.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case06Summary3Checked :
    SummaryValid 256 params.box case06Build case06Rows3 case06Summary3 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
