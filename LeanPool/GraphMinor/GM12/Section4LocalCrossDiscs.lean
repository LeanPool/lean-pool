/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CrossDiscMarks
public import LeanPool.GraphMinor.GM12.Section4ChordGeometry

/-!
# Boundary contacts for locally straight crossing arcs

The source edges of XII (4.5), page 253, agree with straight
chords near each crossing. The part of a chord inside the open
unit disc agrees with its whole line. A sufficiently small
coordinate disc therefore meets each of the actual edge arcs
at the same two opposite boundary marks as its supporting line.
-/

public section

namespace GraphMinor.GM12

open Set Metric Surface

/-- An edge whose part in the unit disc is a chord agrees with
its supporting line throughout the open unit disc. -/
theorem edge_inter_openBall_eq_line_inter_openBall {E : Set ℂ} {a b : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b)
    (hchord : E ∩ closedBall 0 1 = segment ℝ a b) :
    E ∩ ball 0 1 = (line[ℝ, a, b] : Set ℂ) ∩ ball 0 1 := by
  have hl := unit_chord_eq_line_inter_closedBall ha hb hab
  ext z
  constructor
  · rintro ⟨hzE, hzB⟩
    have hz : z ∈ segment ℝ a b := hchord ▸ ⟨hzE, ball_subset_closedBall hzB⟩
    exact ⟨(show z ∈ (line[ℝ, a, b] : Set ℂ) ∩ closedBall 0 1 from hl.symm ▸ hz).1, hzB⟩
  · rintro ⟨hzL, hzB⟩
    have hz : z ∈ segment ℝ a b := hl ▸ ⟨hzL, ball_subset_closedBall hzB⟩
    exact ⟨(show z ∈ E ∩ closedBall 0 1 from hchord.symm ▸ hz).1, hzB⟩

private theorem restrict_inter_eq {E L U B : Set ℂ}
    (h : E ∩ U = L ∩ U) (hB : B ⊆ U) : E ∩ B = L ∩ B := by
  ext z
  constructor
  · rintro ⟨hz, hzB⟩
    exact ⟨(show z ∈ L ∩ U from h ▸ ⟨hz, hB hzB⟩).1, hzB⟩
  · rintro ⟨hz, hzB⟩
    exact ⟨(show z ∈ E ∩ U from h.symm ▸ ⟨hz, hB hzB⟩).1, hzB⟩

/-- Two arcs which are the coordinate lines near their crossing
have a small closed disc whose boundary contacts are exactly
the two opposite pairs. This supplies the local discs used in
XII (4.5), claim (1), page 253. -/
theorem exists_local_cross_disc (A : ℂ ≃L[ℝ] ℂ) (x : ℂ)
    {E F U : Set ℂ} (hU : IsOpen U) (hx : x ∈ U)
    (hE : E ∩ U = (line[ℝ, x, x + A 1] : Set ℂ) ∩ U)
    (hF : F ∩ U = (line[ℝ, x, x + A Complex.I] : Set ℂ) ∩ U) :
    ∃ r : ℝ, 0 < r ∧ ∃ D : Set ℂ,
      IsClosedDisc D ∧ D ⊆ U ∧
      E ∩ discBd D = {x + A (r • (1 : ℂ)), x + A ((-r) • (1 : ℂ))} ∧
      F ∩ discBd D = {x + A (r • Complex.I), x + A ((-r) • Complex.I)} ∧
      D = (fun z => x + A z) '' closedBall 0 r := by
  obtain ⟨r, hr, hd, -, hsub⟩ := exists_small_cross_disc A x hU hx
  let D := (fun z => x + A z) '' closedBall 0 r
  have hbd : discBd D ⊆ U := (discBd_subset D).trans hsub
  refine ⟨r, hr, D, hd, hsub, ?_, ?_, rfl⟩
  · exact (restrict_inter_eq hE hbd).trans
      (cross_disc_line_boundary A x (by simp) hr)
  · exact (restrict_inter_eq hF hbd).trans
      (cross_disc_line_boundary A x Complex.norm_I hr)

end GraphMinor.GM12
