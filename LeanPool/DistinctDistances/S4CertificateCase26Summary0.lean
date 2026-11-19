/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase26Data

/-!
# Subtree 0 of certificate case 26
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 26. -/
noncomputable def case26Summary0 : PackedSummary := s4_summary% 26, case26Rows0

private theorem certificateCost :
    case26Rows0.sumNat (leafCost 256 params.box.nv case26Build) = case26Summary0.cost := by
  decide +kernel

private theorem certificateRhs :
    case26Rows0.sumInt (leafRhs case26Build) = case26Summary0.rhs := by
  decide +kernel

private theorem certificatePositive :
    case26Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case26Build Row.pos) =
      case26Summary0.positive := by
  decide +kernel

private theorem certificateNegative :
    case26Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case26Build Row.neg) =
      case26Summary0.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case26Summary0Checked :
    SummaryValid 256 params.box case26Build case26Rows0 case26Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
