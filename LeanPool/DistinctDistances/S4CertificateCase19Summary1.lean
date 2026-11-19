/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase19Data

/-!
# Subtree 1 of certificate case 19
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 1 of case 19. -/
noncomputable def case19Summary1 : PackedSummary := s4_summary% 19, case19Rows1

private theorem certificateCost :
    case19Rows1.sumNat (leafCost 256 params.box.nv case19Build) = case19Summary1.cost := by
  decide +kernel

private theorem certificateRhs :
    case19Rows1.sumInt (leafRhs case19Build) = case19Summary1.rhs := by
  decide +kernel

private theorem certificatePositive :
    case19Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case19Build Row.pos) =
      case19Summary1.positive := by
  decide +kernel

private theorem certificateNegative :
    case19Rows1.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case19Build Row.neg) =
      case19Summary1.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case19Summary1Checked :
    SummaryValid 256 params.box case19Build case19Rows1 case19Summary1 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
