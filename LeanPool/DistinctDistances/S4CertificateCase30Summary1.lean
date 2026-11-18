/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase30Data

/-!
# Subtree 1 of certificate case 30
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 30. -/
noncomputable def case30Summary1 : PackedSummary := s4_summary% 30, case30Rows1

private theorem certificateCost :
    case30Rows1.sumNat (leafCost 256 params.box.nv case30Build) = case30Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case30Rows1.sumInt (leafRhs case30Build) = case30Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case30Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case30Build Row.pos) =
      case30Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case30Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case30Build Row.neg) =
      case30Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case30Summary1Checked :
    SummaryValid 256 params.box case30Build case30Rows1 case30Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
