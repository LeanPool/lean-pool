/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4ChordCrossing

/-!
# Chord crossings across the end of a full turn

The source drawing for XII (4.5), page 253, uses cyclic vertex
blocks. An end outside the interval of a chord can lie before its
first end or after its last end in the chosen full turn. Adding
one turn in the first case gives the usual alternating order.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A chord from an inside port to an outside port crosses the
chord bounding the interval. This includes a port before the start
of the chosen turn, as needed in XII (4.5), page 253. -/
theorem chords_inter_of_inside_outside_ports {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (ha : 0 ≤ a) (hc : c < 1)
    (hd : d ∈ Ico 0 1) (hout : d < a ∨ c < d) :
    (segment ℝ (ee a : ℂ) (ee c : ℂ) ∩
      segment ℝ (ee b : ℂ) (ee d : ℂ)).Nonempty := by
  rcases hout with hda | hcd
  · have h := ordered_chords_inter hab hbc
      (d := d + 1) (by linarith [hd.1]) (by linarith)
    rw [ee_add_one] at h
    exact h
  · exact ordered_chords_inter hab hbc hcd (by linarith [hd.2])

end GraphMinor.GM12
