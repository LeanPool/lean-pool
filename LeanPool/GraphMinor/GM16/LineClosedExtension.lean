/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.RadialChord

/-!
# Extending line containment to its ends

The closure of a line without its two ends is the whole line.
Thus containment of its open part in a closed set includes the
ends as well. This lets the coordinate checks for the outside
wall sides work first away from their corners.
-/

public section
namespace GraphMinor.GM16
open Set Surface GM11

/-- A closed set containing the open part of a line contains the whole line. -/
theorem line_subset_closed_of_open_part_subset {S : Type*}
    [TopologicalSpace S] [T2Space S] {L C : Set S} {a b : S}
    (hL : IsLineWithEnds L a b) (hC : IsClosed C) (hSub : L \ {a,b} ⊆ C) : L ⊆ C := by
  rw [← closure_sdiff_pair hL]
  exact closure_minimal hSub hC

end GraphMinor.GM16
