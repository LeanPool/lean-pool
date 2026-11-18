/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase05Data

/-!
# Subtree 2 of certificate case 5
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 2 of case 5. -/
noncomputable def case05Summary2 : PackedSummary := s4_summary% 5, case05Rows2

private theorem certificateCost :
    case05Rows2.sumNat (leafCost 256 params.box.nv case05Build) = case05Summary2.cost := by
  decide +kernel

private theorem certificateRhs :
    case05Rows2.sumInt (leafRhs case05Build) = case05Summary2.rhs := by
  decide +kernel

private theorem certificatePositive :
    case05Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case05Build Row.pos) =
      case05Summary2.positive := by
  decide +kernel

private theorem certificateNegative :
    case05Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case05Build Row.neg) =
      case05Summary2.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case05Summary2Checked :
    SummaryValid 256 params.box case05Build case05Rows2 case05Summary2 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
