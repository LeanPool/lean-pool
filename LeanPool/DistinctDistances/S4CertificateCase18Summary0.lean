/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase18Data

/-!
# Subtree 0 of certificate case 18
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 18. -/
noncomputable def case18Summary0 : PackedSummary := s4_summary% 18, case18Rows0

private theorem certificateCost :
    case18Rows0.sumNat (leafCost 256 params.box.nv case18Build) = case18Summary0.cost := by
  decide +kernel

private theorem certificateRhs :
    case18Rows0.sumInt (leafRhs case18Build) = case18Summary0.rhs := by
  decide +kernel

private theorem certificatePositive :
    case18Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case18Build Row.pos) =
      case18Summary0.positive := by
  decide +kernel

private theorem certificateNegative :
    case18Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case18Build Row.neg) =
      case18Summary0.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case18Summary0Checked :
    SummaryValid 256 params.box case18Build case18Rows0 case18Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
