/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase08Data

/-!
# Subtree 1 of certificate case 8
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 8. -/
noncomputable def case08Summary1 : PackedSummary := s4_summary% 8, case08Rows1

private theorem certificateCost :
    case08Rows1.sumNat (leafCost 256 params.box.nv case08Build) = case08Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case08Rows1.sumInt (leafRhs case08Build) = case08Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case08Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case08Build Row.pos) =
      case08Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case08Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case08Build Row.neg) =
      case08Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case08Summary1Checked :
    SummaryValid 256 params.box case08Build case08Rows1 case08Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
