/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase11Data

/-!
# Subtree 0 of certificate case 11
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 11. -/
noncomputable def case11Summary0 : PackedSummary := s4_summary% 11, case11Rows0

private theorem certificateCost :
    case11Rows0.sumNat (leafCost 256 params.box.nv case11Build) = case11Summary0.cost := by
  decide +kernel

private theorem certificateRhs :
    case11Rows0.sumInt (leafRhs case11Build) = case11Summary0.rhs := by
  decide +kernel

private theorem certificatePositive :
    case11Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case11Build Row.pos) =
      case11Summary0.positive := by
  decide +kernel

private theorem certificateNegative :
    case11Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case11Build Row.neg) =
      case11Summary0.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case11Summary0Checked :
    SummaryValid 256 params.box case11Build case11Rows0 case11Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
