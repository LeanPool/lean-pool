/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4OuterPorts
import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.Surface.Lunes

/-!
# Joining the outer pieces to an inner chord

An edge of the crossing drawing in XII (4.5), page 253, consists
of two outer vertex pieces and one inner chord. Each outer piece
meets the chord at its own port. When the outer pieces lie in
disjoint vertex neighborhoods, their union with the chord is a
simple arc. Its intersection with the unit disc is exactly the
inner chord.
-/

public section

namespace GraphMinor.GM12

open Set Metric Surface

private theorem outer_piece_inter_own_chord {a b v : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hv : 1 < ((starRingEnd ℂ) a * v).re) :
    segment ℝ a v ∩ segment ℝ a b = {a} := by
  ext x
  constructor
  · rintro ⟨hx, hx'⟩
    have hxD : x ∈ closedBall (0 : ℂ) 1 :=
      (convex_closedBall (0 : ℂ) 1).segment_subset (by simp [ha]) (by simp [hb]) hx'
    exact show x ∈ ({a} : Set ℂ) from
      outer_port_segment_inter_disc ha hv ▸ And.intro hx hxD
  · rintro rfl
    exact ⟨left_mem_segment _ _ _, left_mem_segment _ _ _⟩

/-- Three pieces form a simple edge arc, and the part of this arc
inside the unit disc is exactly its chord. This proves the absence
of self-crossings in the port construction for XII (4.5), page 253. -/
theorem port_edge_isLine {a b v w : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b)
    (hv : 1 < ((starRingEnd ℂ) a * v).re)
    (hw : 1 < ((starRingEnd ℂ) b * w).re)
    (houter : Disjoint (segment ℝ a v) (segment ℝ b w)) :
    IsLineWithEnds ((segment ℝ a v ∪ segment ℝ a b) ∪ segment ℝ b w) v w ∧
      ((segment ℝ a v ∪ segment ℝ a b) ∪ segment ℝ b w) ∩ closedBall 0 1 =
        segment ℝ a b := by
  have hfirst : IsLineWithEnds (segment ℝ a v ∪ segment ℝ a b) v b :=
    (outer_port_segment_isLine ha hv).symm.union (isLineWithEnds_segment hab)
      (outer_piece_inter_own_chord ha hb hv)
  have hlast : segment ℝ a b ∩ segment ℝ b w = {b} := by
    rw [inter_comm, segment_symm ℝ a b]
    exact outer_piece_inter_own_chord hb ha hw
  have hmeet : (segment ℝ a v ∪ segment ℝ a b) ∩ segment ℝ b w = {b} := by
    rw [union_inter_distrib_right, houter.inter_eq, empty_union, hlast]
  refine ⟨hfirst.union (outer_port_segment_isLine hb hw) hmeet, ?_⟩
  ext x
  constructor
  · rintro ⟨(hx | hx) | hx, hxD⟩
    · have hxa : x = a := show x ∈ ({a} : Set ℂ) from
        outer_port_segment_inter_disc ha hv ▸ And.intro hx hxD
      exact hxa ▸ left_mem_segment ℝ a b
    · exact hx
    · have hxb : x = b := show x ∈ ({b} : Set ℂ) from
        outer_port_segment_inter_disc hb hw ▸ And.intro hx hxD
      exact hxb ▸ right_mem_segment ℝ a b
  · intro hx
    exact ⟨Or.inl (Or.inr hx), (convex_closedBall (0 : ℂ) 1).segment_subset
      (by simp [ha]) (by simp [hb]) hx⟩

end GraphMinor.GM12
