/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase14Data

/-!
# Subtree 1 of certificate case 14
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 14. -/
noncomputable def case14Summary1 : PackedSummary := s4_summary% 14, case14Rows1

private theorem certificateCost :
    case14Rows1.sumNat (leafCost 256 params.box.nv case14Build) = case14Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case14Rows1.sumInt (leafRhs case14Build) = case14Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case14Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case14Build Row.pos) =
      case14Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case14Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case14Build Row.neg) =
      case14Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case14Summary1Checked :
    SummaryValid 256 params.box case14Build case14Rows1 case14Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
