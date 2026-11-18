/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase19Data

/-!
# Subtree 0 of certificate case 19
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

/-- Proposed summary for subtree 0 of case 19. -/
noncomputable def case19Summary0 : PackedSummary := s4_summary% 19, case19Rows0

private theorem certificateCost :
    case19Rows0.sumNat (leafCost 256 params.box.nv case19Build) = case19Summary0.cost := by
  decide +kernel

private theorem certificateRhs :
    case19Rows0.sumInt (leafRhs case19Build) = case19Summary0.rhs := by
  decide +kernel

private theorem certificatePositive :
    case19Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case19Build Row.pos) =
      case19Summary0.positive := by
  decide +kernel

private theorem certificateNegative :
    case19Rows0.sumTrie (leafPack 256 (chunkLen params.box.nv 4) 4 case19Build Row.neg) =
      case19Summary0.negative := by
  decide +kernel

/-- Kernel verification of all four quantities for this subtree. -/
theorem case19Summary0Checked :
    SummaryValid 256 params.box case19Build case19Rows0 case19Summary0 :=
  ⟨certificateCost, certificateRhs, certificatePositive, certificateNegative⟩

end Esgk.S4
