/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SmallCrossDiscs
import LeanPool.GraphMinor.GM12.Section4ChordGeometry

/-!
# Opposite boundary marks on a crossing disc

For the small crossing discs in XII (4.5), page 253, each of the
two straight lines meets the boundary exactly twice. A line
through the centre of a round disc meets its circle at opposite
points. The coordinate change preserves these intersection
equations.
-/

public section

namespace GraphMinor.GM12

open Set Metric

private theorem line_inter_circle_of_two_points {r : ℝ} {a b : ℂ}
    (ha : ‖a‖ = r) (hb : ‖b‖ = r) (hab : a ≠ b) :
    (line[ℝ, a, b] : Set ℂ) ∩ sphere 0 r = {a, b} := by
  let s : EuclideanGeometry.Sphere ℂ := ⟨0, r⟩
  have ha' : a ∈ s := by simpa [s, EuclideanGeometry.mem_sphere] using ha
  have hb' : b ∈ s := by simpa [s, EuclideanGeometry.mem_sphere] using hb
  have hsec := (s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair ha'
    (right_mem_affineSpan_pair ℝ a b)).mpr hb'
  have heq : b = s.secondInter a (b -ᵥ a) := hsec.resolve_left (Ne.symm hab)
  ext z
  constructor
  · rintro ⟨hl, hz⟩
    have hz' : z ∈ s := by
      simpa [s, EuclideanGeometry.mem_sphere] using mem_sphere_zero_iff_norm.mp hz
    have h := (s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair ha' hl).mpr hz'
    rwa [← heq] at h
  · rintro (rfl | rfl)
    · exact ⟨left_mem_affineSpan_pair _ _ _, mem_sphere_zero_iff_norm.mpr ha⟩
    · exact ⟨right_mem_affineSpan_pair _ _ _, mem_sphere_zero_iff_norm.mpr hb⟩

/-- A line in a unit direction meets a positive-radius circle at
exactly the two opposite radial points. -/
theorem unit_direction_line_inter_sphere {u : ℂ} (hu : ‖u‖ = 1)
    {r : ℝ} (hr : 0 < r) :
    (line[ℝ, 0, u] : Set ℂ) ∩ sphere 0 r = {r • u, (-r) • u} := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
  have hab : r • u ≠ (-r) • u := by
    intro heq
    have h := smul_left_injective ℝ hu0 heq
    linarith
  have hmem : ∀ t : ℝ, t • u ∈ line[ℝ, (0 : ℂ), u] := by
    intro t
    apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
    exact ⟨t, by simp [AffineMap.lineMap_apply]⟩
  have heq := affineSpan_pair_eq_of_mem_of_mem_of_ne (hmem r) (hmem (-r)) hab
  rw [← heq]
  apply line_inter_circle_of_two_points
  · rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  · rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos hr]
  · exact hab

/-- In crossing coordinates, the line in any unit direction
meets the coordinate disc boundary at exactly two opposite
marks. This is the boundary-contact equation in XII (4.5),
page 253. -/
theorem cross_disc_line_boundary (A : ℂ ≃L[ℝ] ℂ) (x : ℂ)
    {u : ℂ} (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 < r) :
    (line[ℝ, x, x + A u] : Set ℂ) ∩
        Surface.discBd ((fun z => x + A z) '' closedBall 0 r) =
      {x + A (r • u), x + A ((-r) • u)} := by
  let h : ℂ ≃ₜ ℂ := A.toHomeomorph.trans (Homeomorph.addLeft x)
  have hD : Surface.IsClosedDisc (closedBall (0 : ℂ) r) ∧
      Surface.discBd (closedBall (0 : ℂ) r) = sphere 0 r := by
    have hi : interior (closedBall (0 : ℂ) r) = ball 0 r := interior_closedBall _ (ne_of_gt hr)
    obtain ⟨hd, hb⟩ := Surface.isClosedDisc_of_convex (convex_closedBall (0 : ℂ) r)
      (by rw [hi]; exact ⟨0, mem_ball_self hr⟩) isBounded_closedBall isClosed_closedBall
    exact ⟨hd, hb.trans (frontier_closedBall _ (ne_of_gt hr))⟩
  have hb := (hD.1.image h.continuous.continuousOn h.symm.continuous.continuousOn
    (fun z _ => h.symm_apply_apply z)).2
  rw [hD.2] at hb
  change (line[ℝ, x, x + A u] : Set ℂ) ∩ Surface.discBd (h '' closedBall 0 r) = _
  rw [hb]
  have hl : h '' (line[ℝ, 0, u] : Set ℂ) = (line[ℝ, x, x + A u] : Set ℂ) := by
    change (fun z => x + A z) '' (line[ℝ, 0, u] : Set ℂ) = _
    simpa only [map_zero, add_zero] using image_line_cross_coordinates A x 0 u
  rw [← hl, ← image_inter h.injective, unit_direction_line_inter_sphere hu hr, image_pair]
  rfl

end GraphMinor.GM12
