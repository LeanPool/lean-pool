/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase08Data

/-!
# Subtree 2 of certificate case 8
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 2 of case 8. -/
noncomputable def case08Summary2 : PackedSummary := s4_summary% 8, case08Rows2

private theorem certificateCost :
    case08Rows2.sumNat (leafCost 256 params.box.nv case08Build) = case08Summary2.cost := by
  decide +kernel

private theorem certificateRhs :
    case08Rows2.sumInt (leafRhs case08Build) = case08Summary2.rhs := by
  decide +kernel

private theorem certificatePositive :
    case08Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case08Build Row.pos) =
      case08Summary2.positive := by
  decide +kernel

private theorem certificateNegative :
    case08Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case08Build Row.neg) =
      case08Summary2.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case08Summary2Checked :
    SummaryValid 256 params.box case08Build case08Rows2 case08Summary2 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
