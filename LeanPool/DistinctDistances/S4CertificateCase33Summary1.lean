/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase33Data

/-!
# Subtree 1 of certificate case 33
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 33. -/
noncomputable def case33Summary1 : PackedSummary := s4_summary% 33, case33Rows1

private theorem certificateCost :
    case33Rows1.sumNat (leafCost 256 params.box.nv case33Build) = case33Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case33Rows1.sumInt (leafRhs case33Build) = case33Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case33Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case33Build Row.pos) =
      case33Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case33Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case33Build Row.neg) =
      case33Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case33Summary1Checked :
    SummaryValid 256 params.box case33Build case33Rows1 case33Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
