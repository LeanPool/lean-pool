/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase27Data

/-!
# Subtree 0 of certificate case 27
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 27. -/
noncomputable def case27Summary0 : PackedSummary := s4_summary% 27, case27Rows0

private theorem certificateCost :
    case27Rows0.sumNat (leafCost 256 params.box.nv case27Build) = case27Summary0.cost := by
  decide +kernel

private theorem certificateRhs :
    case27Rows0.sumInt (leafRhs case27Build) = case27Summary0.rhs := by
  decide +kernel

private theorem certificatePositive :
    case27Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case27Build Row.pos) =
      case27Summary0.positive := by
  decide +kernel

private theorem certificateNegative :
    case27Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case27Build Row.neg) =
      case27Summary0.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case27Summary0Checked :
    SummaryValid 256 params.box case27Build case27Rows0 case27Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
