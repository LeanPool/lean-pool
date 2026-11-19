/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase04Data

/-!
# Subtree 1 of certificate case 4
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 4. -/
noncomputable def case04Summary1 : PackedSummary := s4_summary% 4, case04Rows1

private theorem certificateCost :
    case04Rows1.sumNat (leafCost 256 params.box.nv case04Build) = case04Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case04Rows1.sumInt (leafRhs case04Build) = case04Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case04Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case04Build Row.pos) =
      case04Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case04Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case04Build Row.neg) =
      case04Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case04Summary1Checked :
    SummaryValid 256 params.box case04Build case04Rows1 case04Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
