/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase13Data

/-!
# Subtree 1 of certificate case 13
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 13. -/
noncomputable def case13Summary1 : PackedSummary := s4_summary% 13, case13Rows1

private theorem certificateCost :
    case13Rows1.sumNat (leafCost 256 params.box.nv case13Build) = case13Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case13Rows1.sumInt (leafRhs case13Build) = case13Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case13Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case13Build Row.pos) =
      case13Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case13Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case13Build Row.neg) =
      case13Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case13Summary1Checked :
    SummaryValid 256 params.box case13Build case13Rows1 case13Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
