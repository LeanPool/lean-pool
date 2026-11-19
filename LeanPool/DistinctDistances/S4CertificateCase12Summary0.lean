/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase12Data

/-!
# Subtree 0 of certificate case 12
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 12. -/
noncomputable def case12Summary0 : PackedSummary := s4_summary% 12, case12Rows0

private theorem certificateCost :
    case12Rows0.sumNat (leafCost 256 params.box.nv case12Build) = case12Summary0.cost := by
  decide +kernel

private theorem certificateRhs :
    case12Rows0.sumInt (leafRhs case12Build) = case12Summary0.rhs := by
  decide +kernel

private theorem certificatePositive :
    case12Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case12Build Row.pos) =
      case12Summary0.positive := by
  decide +kernel

private theorem certificateNegative :
    case12Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case12Build Row.neg) =
      case12Summary0.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case12Summary0Checked :
    SummaryValid 256 params.box case12Build case12Rows0 case12Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
