/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase29Data

/-!
# Subtree 1 of certificate case 29
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 29. -/
noncomputable def case29Summary1 : PackedSummary := s4_summary% 29, case29Rows1

private theorem certificateCost :
    case29Rows1.sumNat (leafCost 256 params.box.nv case29Build) = case29Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case29Rows1.sumInt (leafRhs case29Build) = case29Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case29Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case29Build Row.pos) =
      case29Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case29Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case29Build Row.neg) =
      case29Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case29Summary1Checked :
    SummaryValid 256 params.box case29Build case29Rows1 case29Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
