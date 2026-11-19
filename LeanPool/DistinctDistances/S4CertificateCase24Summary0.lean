/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase24Data

/-!
# Subtree 0 of certificate case 24
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 24. -/
noncomputable def case24Summary0 : PackedSummary := s4_summary% 24, case24Rows0

private theorem certificateCost :
    case24Rows0.sumNat (leafCost 256 params.box.nv case24Build) = case24Summary0.cost := by
  decide +kernel

private theorem certificateRhs :
    case24Rows0.sumInt (leafRhs case24Build) = case24Summary0.rhs := by
  decide +kernel

private theorem certificatePositive :
    case24Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case24Build Row.pos) =
      case24Summary0.positive := by
  decide +kernel

private theorem certificateNegative :
    case24Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case24Build Row.neg) =
      case24Summary0.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case24Summary0Checked :
    SummaryValid 256 params.box case24Build case24Rows0 case24Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
