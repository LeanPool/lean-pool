/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase22Data

/-!
# Subtree 0 of certificate case 22
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 22. -/
noncomputable def case22Summary0 : PackedSummary := s4_summary% 22, case22Rows0

private theorem certificateCost :
    case22Rows0.sumNat (leafCost 256 params.box.nv case22Build) = case22Summary0.cost := by
  decide +kernel

private theorem certificateRhs :
    case22Rows0.sumInt (leafRhs case22Build) = case22Summary0.rhs := by
  decide +kernel

private theorem certificatePositive :
    case22Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case22Build Row.pos) =
      case22Summary0.positive := by
  decide +kernel

private theorem certificateNegative :
    case22Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case22Build Row.neg) =
      case22Summary0.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case22Summary0Checked :
    SummaryValid 256 params.box case22Build case22Rows0 case22Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
