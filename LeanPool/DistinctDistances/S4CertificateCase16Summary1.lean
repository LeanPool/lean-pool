/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase16Data

/-!
# Subtree 1 of certificate case 16
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 16. -/
noncomputable def case16Summary1 : PackedSummary := s4_summary% 16, case16Rows1

private theorem certificateCost :
    case16Rows1.sumNat (leafCost 256 params.box.nv case16Build) = case16Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case16Rows1.sumInt (leafRhs case16Build) = case16Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case16Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case16Build Row.pos) =
      case16Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case16Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case16Build Row.neg) =
      case16Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case16Summary1Checked :
    SummaryValid 256 params.box case16Build case16Rows1 case16Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
