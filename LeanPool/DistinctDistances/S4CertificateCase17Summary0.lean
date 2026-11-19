/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase17Data

/-!
# Subtree 0 of certificate case 17
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 17. -/
noncomputable def case17Summary0 : PackedSummary := s4_summary% 17, case17Rows0

private theorem certificateCost :
    case17Rows0.sumNat (leafCost 256 params.box.nv case17Build) = case17Summary0.cost := by
  decide +kernel

private theorem certificateRhs :
    case17Rows0.sumInt (leafRhs case17Build) = case17Summary0.rhs := by
  decide +kernel

private theorem certificatePositive :
    case17Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case17Build Row.pos) =
      case17Summary0.positive := by
  decide +kernel

private theorem certificateNegative :
    case17Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case17Build Row.neg) =
      case17Summary0.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case17Summary0Checked :
    SummaryValid 256 params.box case17Build case17Rows0 case17Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
