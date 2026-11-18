/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase21Data

/-!
# Subtree 1 of certificate case 21
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 21. -/
noncomputable def case21Summary1 : PackedSummary := s4_summary% 21, case21Rows1

private theorem certificateCost :
    case21Rows1.sumNat (leafCost 256 params.box.nv case21Build) = case21Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case21Rows1.sumInt (leafRhs case21Build) = case21Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case21Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case21Build Row.pos) =
      case21Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case21Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case21Build Row.neg) =
      case21Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case21Summary1Checked :
    SummaryValid 256 params.box case21Build case21Rows1 case21Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
