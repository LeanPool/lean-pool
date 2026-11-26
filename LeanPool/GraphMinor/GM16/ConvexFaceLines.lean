/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM16.LineImageEmbedding
import LeanPool.GraphMinor.GM11.ArcDrawings
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Affine

/-!
# Lines in intersections of rectangular faces

The intersection of two coordinate rectangles is convex. Any two
distinct points in it are joined by their straight line segment.
An embedding carries this segment to the line required by the
face criterion for rigidity in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface GM11

/-- Distinct points of a convex subset of the coordinate plane are
joined by a line contained in that subset. -/
theorem exists_line_in_convex {C : Set (ℝ × ℝ)} (hC : Convex ℝ C)
    {a b : ℝ × ℝ} (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) :
    ∃ L, IsLineWithEnds L a b ∧ L ⊆ C := by
  refine ⟨segment ℝ a b,?_,hC.segment_subset ha hb⟩
  have h := isLine_of_injOn (AffineMap.lineMap_continuous (p := a) (q := b))
    (show (0 : ℝ) < 1 by norm_num) (AffineMap.lineMap_injective ℝ hab).injOn
  simpa only [← segment_eq_image_lineMap,AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] using h

/-- Common points of two embedded closed rectangles can be joined
inside their intersection by a line. -/
theorem exists_line_in_embedded_rectangles_intersection {S : Type*}
    [TopologicalSpace S] [T2Space S] {f : (ℝ × ℝ) → S} (hf : IsEmbedding f)
    (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) {x y : S} (hxy : x ≠ y)
    (hx : x ∈ (f '' (Icc a₁ b₁ ×ˢ Icc c₁ d₁)) ∩ (f '' (Icc a₂ b₂ ×ˢ Icc c₂ d₂)))
    (hy : y ∈ (f '' (Icc a₁ b₁ ×ˢ Icc c₁ d₁)) ∩ (f '' (Icc a₂ b₂ ×ˢ Icc c₂ d₂))) :
    ∃ K, IsLineWithEnds K x y ∧
      K ⊆ (f '' (Icc a₁ b₁ ×ˢ Icc c₁ d₁)) ∩ (f '' (Icc a₂ b₂ ×ˢ Icc c₂ d₂)) := by
  rw [← image_inter hf.injective] at hx hy ⊢
  obtain ⟨p,hp,rfl⟩ := hx
  obtain ⟨q,hq,rfl⟩ := hy
  have hpq : p ≠ q := fun he => hxy (congrArg f he)
  have hConvex : Convex ℝ ((Icc a₁ b₁ ×ˢ Icc c₁ d₁) ∩ (Icc a₂ b₂ ×ˢ Icc c₂ d₂)) :=
    ((convex_Icc a₁ b₁).prod (convex_Icc c₁ d₁)).inter
      ((convex_Icc a₂ b₂).prod (convex_Icc c₂ d₂))
  obtain ⟨L,hL,hLC⟩ := exists_line_in_convex hConvex hp hq hpq
  exact ⟨f '' L,isLineWithEnds_image_embedding hf hL,image_mono hLC⟩

end GraphMinor.GM16
