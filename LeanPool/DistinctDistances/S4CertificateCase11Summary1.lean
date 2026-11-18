/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase11Data

/-!
# Subtree 1 of certificate case 11
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 11. -/
noncomputable def case11Summary1 : PackedSummary := s4_summary% 11, case11Rows1

private theorem certificateCost :
    case11Rows1.sumNat (leafCost 256 params.box.nv case11Build) = case11Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case11Rows1.sumInt (leafRhs case11Build) = case11Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case11Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case11Build Row.pos) =
      case11Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case11Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case11Build Row.neg) =
      case11Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case11Summary1Checked :
    SummaryValid 256 params.box case11Build case11Rows1 case11Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
