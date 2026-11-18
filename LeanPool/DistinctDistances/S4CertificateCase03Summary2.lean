/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase03Data

/-!
# Subtree 2 of certificate case 3
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 2 of case 3. -/
noncomputable def case03Summary2 : PackedSummary := s4_summary% 3, case03Rows2

private theorem certificateCost :
    case03Rows2.sumNat (leafCost 256 params.box.nv case03Build) = case03Summary2.cost := by
  decide +kernel

private theorem certificateRhs :
    case03Rows2.sumInt (leafRhs case03Build) = case03Summary2.rhs := by
  decide +kernel

private theorem certificatePositive :
    case03Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case03Build Row.pos) =
      case03Summary2.positive := by
  decide +kernel

private theorem certificateNegative :
    case03Rows2.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case03Build Row.neg) =
      case03Summary2.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case03Summary2Checked :
    SummaryValid 256 params.box case03Build case03Rows2 case03Summary2 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
