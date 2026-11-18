/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase15Data

/-!
# Subtree 0 of certificate case 15
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 15. -/
noncomputable def case15Summary0 : PackedSummary := s4_summary% 15, case15Rows0

private theorem certificateCost :
    case15Rows0.sumNat (leafCost 256 params.box.nv case15Build) = case15Summary0.cost := by
  decide +kernel

private theorem certificateRhs :
    case15Rows0.sumInt (leafRhs case15Build) = case15Summary0.rhs := by
  decide +kernel

private theorem certificatePositive :
    case15Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case15Build Row.pos) =
      case15Summary0.positive := by
  decide +kernel

private theorem certificateNegative :
    case15Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case15Build Row.neg) =
      case15Summary0.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case15Summary0Checked :
    SummaryValid 256 params.box case15Build case15Rows0 case15Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
