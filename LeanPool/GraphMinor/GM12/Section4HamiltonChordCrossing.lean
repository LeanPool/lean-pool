/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4WrappedChordCrossing
public import LeanPool.GraphMinor.GM12.Section4HamiltonPorts

/-!
# A later port crosses the outgoing Hamilton chord

In the source construction for XII (4.5), page 252, non-Hamilton
ports follow the outgoing Hamilton port in each vertex block.
The outgoing Hamilton chord ends in the next block. An edge from
a later port of the first block to any other block therefore
crosses it. Adding one turn handles the last vertex block.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- An edge from a later port to a different, non-successor block
crosses the outgoing Hamilton chord. This supplies the crossing
witness for Hamilton edges in XII (4.5)(vi), page 252. -/
theorem hamilton_chord_crosses_later_port {p : ℕ}
    (F : Fin p → Fin p → ℝ) (hF : ∀ v w, F v w ∈ Ioo 0 1)
    (hblocks : ∀ v w i j, v < i → F v w < F i j)
    {v w : Fin p} (hwv : w ≠ v) (hwnext : w ≠ finRotate p v)
    (hlater : F v (finRotate p v) < F v w) :
    (segment ℝ (ee (F v (finRotate p v)) : ℂ) (ee (F (finRotate p v) v) : ℂ) ∩
      segment ℝ (ee (F v w) : ℂ) (ee (F w v) : ℂ)).Nonempty := by
  cases p with
  | zero => exact v.elim0
  | succ q =>
    by_cases hvlast : v = Fin.last q
    · have hnext : finRotate (q + 1) v = 0 := by rw [hvlast, finRotate_last]
      have hwpos : (0 : Fin (q + 1)) < w := by
        have hwzero : w ≠ 0 := by simpa only [hnext] using hwnext
        change 0 < w.val
        have hwval : w.val ≠ 0 := fun h => hwzero (Fin.ext h)
        omega
      have hwlt : w < v := by
        rw [hvlast]
        exact Fin.lt_last_iff_ne_last.mpr (by simpa only [← hvlast] using hwv)
      have h := ordered_chords_inter hlater
        (c := F (finRotate (q + 1) v) v + 1) (d := F w v + 1)
        (by linarith [(hF v w).2, (hF (finRotate (q + 1) v) v).1])
        (by have hh := hblocks 0 v w v hwpos; rw [hnext]; linarith)
        (by have hh := hblocks w v v (finRotate (q + 1) v) hwlt; linarith)
      rw [ee_add_one, ee_add_one] at h
      exact h
    · have hvnext : v < finRotate (q + 1) v := (lt_finRotate_iff_ne_last v).mpr hvlast
      apply chords_inter_of_inside_outside_ports hlater
        (hblocks v w (finRotate (q + 1) v) v hvnext)
        (hF v (finRotate (q + 1) v)).1.le (hF (finRotate (q + 1) v) v).2
        ⟨(hF w v).1.le, (hF w v).2⟩
      rcases lt_or_gt_of_ne hwv with hwlt | hvw
      · exact Or.inl (hblocks w v v (finRotate (q + 1) v) hwlt)
      · have hnextval := coe_finRotate_of_ne_last hvlast
        have hneval : w.val ≠ (finRotate (q + 1) v).val := fun h => hwnext (Fin.ext h)
        have hnextlt : finRotate (q + 1) v < w := by
          change (finRotate (q + 1) v).val < w.val
          have hvwval : v.val < w.val := hvw
          omega
        exact Or.inr (hblocks (finRotate (q + 1) v) v w v hnextlt)

end GraphMinor.GM12
