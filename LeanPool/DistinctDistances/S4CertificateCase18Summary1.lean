/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase18Data

/-!
# Subtree 1 of certificate case 18
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 18. -/
noncomputable def case18Summary1 : PackedSummary := s4_summary% 18, case18Rows1

private theorem certificateCost :
    case18Rows1.sumNat (leafCost 256 params.box.nv case18Build) = case18Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case18Rows1.sumInt (leafRhs case18Build) = case18Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case18Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case18Build Row.pos) =
      case18Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case18Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case18Build Row.neg) =
      case18Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case18Summary1Checked :
    SummaryValid 256 params.box case18Build case18Rows1 case18Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
