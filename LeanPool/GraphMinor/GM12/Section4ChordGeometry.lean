/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4ChordFamily
public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Analysis.Convex.Segment
import LeanPool.GraphMinor.Surface.Lunes
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Convex.Between

/-!
# Chord arcs and their intersections

In the crossing construction of XII (4.5), page 253, a straight
chord is a simple arc. Strict convexity puts its interior inside
the open unit disc. Distinct supporting lines give finite pairwise
intersections, and the choice of supporting lines rules out triple
intersections of the arcs as well.
-/

public section

namespace GraphMinor.GM12

open Set Metric Surface

/-- A chord with distinct unit circle ends is a line whose only
unit circle points are its ends. This separates the chord from the
outer vertex pieces in XII (4.5), page 253. -/
theorem unit_chord_geometry {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) :
    IsLineWithEnds (segment ℝ a b) a b ∧
      segment ℝ a b ⊆ closedBall 0 1 ∧
      segment ℝ a b ∩ sphere 0 1 = {a, b} := by
  have haD : a ∈ closedBall (0 : ℂ) 1 := by simp [ha]
  have hbD : b ∈ closedBall (0 : ℂ) 1 := by simp [hb]
  refine ⟨isLineWithEnds_segment hab, (convex_closedBall (0 : ℂ) 1).segment_subset haD hbD, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hxs⟩
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr hxb
    have hxi := mem_openSegment_of_ne_left_right (fun h => hxa h.symm) (fun h => hxb h.symm) hx
    have hxB := openSegment_subset_ball_of_ne haD hbD hab hxi
    have hn := mem_sphere_zero_iff_norm.mp hxs
    exact False.elim ((not_lt_of_ge (le_of_eq hn.symm)) (mem_ball_zero_iff.mp hxB))
  · rintro (rfl | rfl)
    · exact ⟨left_mem_segment _ _ _, by simp [ha]⟩
    · exact ⟨right_mem_segment _ _ _, by simp [hb]⟩

/-- Distinct chord supporting lines give finite intersections of
the chord arcs, as required by XII (4.5)(ii), page 253. -/
theorem finite_chord_inter_of_ne_lines {a b c d : ℂ}
    (hne : line[ℝ, a, b] ≠ line[ℝ, c, d]) :
    (segment ℝ a b ∩ segment ℝ c d).Finite := by
  apply (subsingleton_inter_of_ne_lines hne).finite.subset
  intro x hx
  exact ⟨(line[ℝ, a, b]).convex.segment_subset
      (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _) hx.1,
    (line[ℝ, c, d]).convex.segment_subset
      (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _) hx.2⟩

/-- A supporting line through two distinct unit circle points has
no third unit circle point. -/
theorem unit_circle_mem_line_iff {a b x : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) (hx : ‖x‖ = 1) :
    x ∈ line[ℝ, a, b] ↔ x = a ∨ x = b := by
  let s : EuclideanGeometry.Sphere ℂ := ⟨0, 1⟩
  have ha' : a ∈ s := by simpa [s, EuclideanGeometry.mem_sphere] using ha
  have hb' : b ∈ s := by simpa [s, EuclideanGeometry.mem_sphere] using hb
  have hx' : x ∈ s := by simpa [s, EuclideanGeometry.mem_sphere] using hx
  have hbsec := (s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair ha'
    (right_mem_affineSpan_pair ℝ a b)).mpr hb'
  have hsec : b = s.secondInter a (b - a) := hbsec.resolve_left (fun h => hab h.symm)
  change b = s.secondInter a (b -ᵥ a) at hsec
  constructor
  · intro hline
    have h := (s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair ha' hline).mpr hx'
    rwa [← hsec] at h
  · rintro (rfl | rfl)
    · exact left_mem_affineSpan_pair _ _ _
    · exact right_mem_affineSpan_pair _ _ _

/-- Chords with four distinct unit circle ends meet only in the
open disc. Thus every meeting is away from the ports in the
crossing construction of XII (4.5), page 253. -/
theorem unit_chord_inter_subset_openBall {a b c d : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    segment ℝ a b ∩ segment ℝ c d ⊆ ball 0 1 := by
  intro x hx
  have hgeom := unit_chord_geometry ha hb hab
  have hn : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp (hgeom.2.1 hx.1)
  refine mem_ball_zero_iff.mpr (lt_of_le_of_ne hn ?_)
  intro heq
  have hxs : x ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr heq
  have habx : x = a ∨ x = b := show x ∈ ({a, b} : Set ℂ) from hgeom.2.2 ▸ And.intro hx.1 hxs
  have hcdx : x = c ∨ x = d :=
    show x ∈ ({c, d} : Set ℂ) from
      (unit_chord_geometry hc hd hcd).2.2 ▸ And.intro hx.2 hxs
  rcases habx with rfl | rfl
  · exact hcdx.elim hac had
  · exact hcdx.elim hbc hbd

/-- A unit chord is exactly the part of its supporting line in
the unit disc. Thus near an interior meeting the source edges
are straight lines, as used for the crossing discs of XII (4.5),
page 253. -/
theorem unit_chord_eq_line_inter_closedBall {a b : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) :
    (line[ℝ, a, b] : Set ℂ) ∩ closedBall 0 1 = segment ℝ a b := by
  apply Subset.antisymm
  · rintro z ⟨hzline, hzD⟩
    let s : EuclideanGeometry.Sphere ℂ := ⟨0, 1⟩
    have ha' : a ∈ s := by simpa [s, EuclideanGeometry.mem_sphere] using ha
    have hb' : b ∈ s := by simpa [s, EuclideanGeometry.mem_sphere] using hb
    have hcol : Collinear ℝ ({a, z, b} : Set ℂ) := by
      rw [Set.insert_comm]
      exact collinear_insert_of_mem_affineSpan_pair hzline
    have hz' : dist z s.center ≤ s.radius := mem_closedBall.mp hzD
    exact (EuclideanGeometry.wbtw_of_collinear_of_dist_center_le_radius hcol ha' hz' hb'
      hab).mem_segment
  · intro z hz
    exact ⟨(line[ℝ, a, b]).convex.segment_subset
        (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _) hz,
      (unit_chord_geometry ha hb hab).2.1 hz⟩

end GraphMinor.GM12
