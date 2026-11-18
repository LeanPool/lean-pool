/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase31Data

/-!
# Subtree 0 of certificate case 31
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 31. -/
noncomputable def case31Summary0 : PackedSummary := s4_summary% 31, case31Rows0

private theorem certificateCost :
    case31Rows0.sumNat (leafCost 256 params.box.nv case31Build) = case31Summary0.cost := by
  decide +kernel

private theorem certificateRhs :
    case31Rows0.sumInt (leafRhs case31Build) = case31Summary0.rhs := by
  decide +kernel

private theorem certificatePositive :
    case31Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case31Build Row.pos) =
      case31Summary0.positive := by
  decide +kernel

private theorem certificateNegative :
    case31Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case31Build Row.neg) =
      case31Summary0.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case31Summary0Checked :
    SummaryValid 256 params.box case31Build case31Rows0 case31Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
