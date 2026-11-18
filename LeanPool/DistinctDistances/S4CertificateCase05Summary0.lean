/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase05Data

/-!
# Subtree 0 of certificate case 5
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 5. -/
noncomputable def case05Summary0 : PackedSummary := s4_summary% 5, case05Rows0

private theorem certificateCost :
    case05Rows0.sumNat (leafCost 256 params.box.nv case05Build) = case05Summary0.cost := by
  decide +kernel

private theorem certificateRhs :
    case05Rows0.sumInt (leafRhs case05Build) = case05Summary0.rhs := by
  decide +kernel

private theorem certificatePositive :
    case05Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case05Build Row.pos) =
      case05Summary0.positive := by
  decide +kernel

private theorem certificateNegative :
    case05Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case05Build Row.neg) =
      case05Summary0.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case05Summary0Checked :
    SummaryValid 256 params.box case05Build case05Rows0 case05Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
