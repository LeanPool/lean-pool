/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase12Data

/-!
# Subtree 3 of certificate case 12
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 3 of case 12. -/
noncomputable def case12Summary3 : PackedSummary := s4_summary% 12, case12Rows3

private theorem certificateCost :
    case12Rows3.sumNat (leafCost 256 params.box.nv case12Build) = case12Summary3.cost := by
  decide +kernel

private theorem certificateRhs :
    case12Rows3.sumInt (leafRhs case12Build) = case12Summary3.rhs := by
  decide +kernel

private theorem certificatePositive :
    case12Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case12Build Row.pos) =
      case12Summary3.positive := by
  decide +kernel

private theorem certificateNegative :
    case12Rows3.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case12Build Row.neg) =
      case12Summary3.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case12Summary3Checked :
    SummaryValid 256 params.box case12Build case12Rows3 case12Summary3 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
