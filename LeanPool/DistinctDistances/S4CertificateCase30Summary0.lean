/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase30Data

/-!
# Subtree 0 of certificate case 30
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 30. -/
noncomputable def case30Summary0 : PackedSummary := s4_summary% 30, case30Rows0

private theorem certificateCost :
    case30Rows0.sumNat (leafCost 256 params.box.nv case30Build) = case30Summary0.cost := by
  decide +kernel

private theorem certificateRhs :
    case30Rows0.sumInt (leafRhs case30Build) = case30Summary0.rhs := by
  decide +kernel

private theorem certificatePositive :
    case30Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case30Build Row.pos) =
      case30Summary0.positive := by
  decide +kernel

private theorem certificateNegative :
    case30Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case30Build Row.neg) =
      case30Summary0.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case30Summary0Checked :
    SummaryValid 256 params.box case30Build case30Rows0 case30Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
