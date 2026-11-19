/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase28Data

/-!
# Subtree 1 of certificate case 28
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 28. -/
noncomputable def case28Summary1 : PackedSummary := s4_summary% 28, case28Rows1

private theorem certificateCost :
    case28Rows1.sumNat (leafCost 256 params.box.nv case28Build) = case28Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case28Rows1.sumInt (leafRhs case28Build) = case28Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case28Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case28Build Row.pos) =
      case28Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case28Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case28Build Row.neg) =
      case28Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case28Summary1Checked :
    SummaryValid 256 params.box case28Build case28Rows1 case28Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
