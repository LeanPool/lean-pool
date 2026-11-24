/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4PieceNeighborhood
public import LeanPool.GraphMinor.GM12.Section4LocalCrossDiscs

/-!
# Straightness of a subdivided edge near its meeting

For XII (4.5), page 253, the original edge agrees with its
supporting line inside the open unit disc. Near a meeting, the
subdivision piece containing that meeting agrees with the old
edge. Intersect these two neighborhoods to obtain the local
straight-line model for the subdivision piece itself.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric

/-- A subdivision piece is locally its chord's complete
supporting line at its unique meeting in the open unit disc.
This supplies the straightness needed to choose crossing discs
for the subdivided drawing in XII (4.5), page 253. -/
theorem exists_open_subdivision_line_agreement {k : ℕ}
    (E M : Set ℂ) (w : Fin (k + 1) → ℂ) (P : Fin k → Set ℂ)
    (hline : ∀ i, IsLineWithEnds (P i) (w i.castSucc) (w i.succ))
    (hcover : (⋃ i, P i) = E) (havoid : ∀ r, w r ∉ E ∩ M)
    (hinter : ∀ i j, i ≠ j → P i ∩ P j ⊆ range w)
    {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b)
    (hchord : E ∩ closedBall 0 1 = segment ℝ a b)
    {i : Fin k} {x : ℂ} (hx : x ∈ P i ∩ (E ∩ M)) (hxB : x ∈ ball (0 : ℂ) 1) :
    ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧
      P i ∩ U = (line[ℝ, a, b] : Set ℂ) ∩ U := by
  obtain ⟨U, hU, hxU, hmatch⟩ := exists_open_subdivision_piece_agreement E M w P
    hline hcover havoid hinter hx
  have hstraight := edge_inter_openBall_eq_line_inter_openBall ha hb hab hchord
  refine ⟨U ∩ ball 0 1, hU.inter isOpen_ball, ⟨hxU, hxB⟩, ?_⟩
  ext z
  constructor
  · rintro ⟨hzP, hzU, hzB⟩
    have hzE : z ∈ E := (show z ∈ E ∩ U from hmatch.symm ▸ ⟨hzP, hzU⟩).1
    have hzL : z ∈ line[ℝ, a, b] :=
      (show z ∈ (line[ℝ, a, b] : Set ℂ) ∩ ball 0 1 from hstraight ▸ ⟨hzE, hzB⟩).1
    exact ⟨hzL, hzU, hzB⟩
  · rintro ⟨hzL, hzU, hzB⟩
    have hzE : z ∈ E :=
      (show z ∈ E ∩ ball 0 1 from hstraight.symm ▸ ⟨hzL, hzB⟩).1
    have hzP : z ∈ P i := (show z ∈ P i ∩ U from hmatch ▸ ⟨hzE, hzU⟩).1
    exact ⟨hzP, hzU, hzB⟩

end GraphMinor.GM12
