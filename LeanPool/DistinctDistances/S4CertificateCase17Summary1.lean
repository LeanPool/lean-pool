/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase17Data

/-!
# Subtree 1 of certificate case 17
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 17. -/
noncomputable def case17Summary1 : PackedSummary := s4_summary% 17, case17Rows1

private theorem certificateCost :
    case17Rows1.sumNat (leafCost 256 params.box.nv case17Build) = case17Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case17Rows1.sumInt (leafRhs case17Build) = case17Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case17Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case17Build Row.pos) =
      case17Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case17Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case17Build Row.neg) =
      case17Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case17Summary1Checked :
    SummaryValid 256 params.box case17Build case17Rows1 case17Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
