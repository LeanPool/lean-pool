/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase20Data

/-!
# Subtree 1 of certificate case 20
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 20. -/
noncomputable def case20Summary1 : PackedSummary := s4_summary% 20, case20Rows1

private theorem certificateCost :
    case20Rows1.sumNat (leafCost 256 params.box.nv case20Build) = case20Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case20Rows1.sumInt (leafRhs case20Build) = case20Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case20Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case20Build Row.pos) =
      case20Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case20Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case20Build Row.neg) =
      case20Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case20Summary1Checked :
    SummaryValid 256 params.box case20Build case20Rows1 case20Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
