/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase00Data

/-!
# Subtree 2 of certificate case 0
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 2 of case 0. -/
noncomputable def case00Summary2 : PackedSummary := s4_summary% 0, case00Rows2

private theorem certificateCost :
    case00Rows2.sumNat (leafCost 256 params.box.nv case00Build) = case00Summary2.cost := by
  decide +kernel

private theorem certificateRhs :
    case00Rows2.sumInt (leafRhs case00Build) = case00Summary2.rhs := by
  decide +kernel

private theorem certificatePositive :
    case00Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case00Build Row.pos) =
      case00Summary2.positive := by
  decide +kernel

private theorem certificateNegative :
    case00Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case00Build Row.neg) =
      case00Summary2.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case00Summary2Checked :
    SummaryValid 256 params.box case00Build case00Rows2 case00Summary2 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
