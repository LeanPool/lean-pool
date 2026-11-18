/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase07Data

/-!
# Subtree 1 of certificate case 7
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 7. -/
noncomputable def case07Summary1 : PackedSummary := s4_summary% 7, case07Rows1

private theorem certificateCost :
    case07Rows1.sumNat (leafCost 256 params.box.nv case07Build) = case07Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case07Rows1.sumInt (leafRhs case07Build) = case07Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case07Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case07Build Row.pos) =
      case07Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case07Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case07Build Row.neg) =
      case07Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case07Summary1Checked :
    SummaryValid 256 params.box case07Build case07Rows1 case07Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
