/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase25Data

/-!
# Subtree 1 of certificate case 25
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 25. -/
noncomputable def case25Summary1 : PackedSummary := s4_summary% 25, case25Rows1

private theorem certificateCost :
    case25Rows1.sumNat (leafCost 256 params.box.nv case25Build) = case25Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case25Rows1.sumInt (leafRhs case25Build) = case25Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case25Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case25Build Row.pos) =
      case25Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case25Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case25Build Row.neg) =
      case25Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case25Summary1Checked :
    SummaryValid 256 params.box case25Build case25Rows1 case25Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
