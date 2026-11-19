/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase02Data

/-!
# Subtree 1 of certificate case 2
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 2. -/
noncomputable def case02Summary1 : PackedSummary := s4_summary% 2, case02Rows1

private theorem certificateCost :
    case02Rows1.sumNat (leafCost 256 params.box.nv case02Build) = case02Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case02Rows1.sumInt (leafRhs case02Build) = case02Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case02Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case02Build Row.pos) =
      case02Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case02Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case02Build Row.neg) =
      case02Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case02Summary1Checked :
    SummaryValid 256 params.box case02Build case02Rows1 case02Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
