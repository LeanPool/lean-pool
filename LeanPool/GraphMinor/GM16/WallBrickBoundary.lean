/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4WallDrawing
import LeanPool.GraphMinor.GM16.WallEdgeInDrawing
import LeanPool.GraphMinor.GM16.RectangularDisc
import LeanPool.GraphMinor.Surface.Wedge
import Mathlib.Tactic.Linarith

/-!
# The boundary of each wall brick lies in the drawing

The top and bottom sides each consist of two retained horizontal
unit lines. The other two sides are vertical lines with the even
parity required by the wall. Thus the boundary of the embedded
closed rectangle belongs to the wall drawing. Together with its
empty interior this identifies a bounded face in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface

/-- Every side of a closed wall brick belongs to the drawing. -/
theorem sphereWall_brick_frontier_image_subset_U {S : Type*}
    [TopologicalSpace S] {θ : ℕ}
    (f : (ℝ × ℝ) → S) (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val
      = f '' rectangularGridLine e.val)
    {i j : ℕ} (hi : i+2 < 2*θ+1) (hj : j+1 < θ) (hEven : Even (i+j)) :
    f '' frontier (Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1)) ⊆ Γ.drawing.U := by
  have hHorizontal {q : ℕ} (hq : q < θ) {p : ℝ × ℝ}
      (hx : p.1 ∈ Icc (i : ℝ) ((i : ℝ)+2)) (hy : p.2 = (q : ℝ)) : f p ∈ Γ.drawing.U := by
    by_cases hCut : p.1 ≤ (i : ℝ)+1
    · apply sphereWall_horizontal_line_subset_U f Γ hE (by omega : i+1<2*θ+1) hq
      exact ⟨p,⟨⟨hx.1,hCut⟩,hy⟩,rfl⟩
    · apply sphereWall_horizontal_line_subset_U f Γ hE (by omega : (i+1)+1<2*θ+1) hq
      refine ⟨p,⟨⟨?_,?_⟩,hy⟩,rfl⟩
      · simpa only [Nat.cast_add,Nat.cast_one] using (le_of_not_ge hCut)
      · simp only [Nat.cast_add,Nat.cast_one]
        linarith [hx.2]
  have hVertical {q : ℕ} (hq : q < 2*θ+1) (he : Even (q+j)) {p : ℝ × ℝ}
      (hx : p.1 = (q : ℝ)) (hy : p.2 ∈ Icc (j : ℝ) ((j : ℝ)+1)) : f p ∈ Γ.drawing.U := by
    exact sphereWall_vertical_line_subset_U f Γ hE hq hj he ⟨p,⟨hx,hy⟩,rfl⟩
  have hEvenRight : Even ((i+2)+j) := by
    obtain ⟨k,hk⟩ := hEven
    exact ⟨k+1,by omega⟩
  rintro x ⟨p,hp,rfl⟩
  rw [frontier_prod_eq,isClosed_Icc.closure_eq,isClosed_Icc.closure_eq,
    frontier_Icc (by linarith : (i : ℝ) ≤ (i : ℝ)+2),
    frontier_Icc (by linarith : (j : ℝ) ≤ (j : ℝ)+1)] at hp
  rcases hp with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · rcases hy with hy | hy
    · exact hHorizontal (by omega : j<θ) hx hy
    · rw [mem_singleton_iff] at hy
      apply hHorizontal (q := j+1) hj hx
      simpa only [Nat.cast_add,Nat.cast_one] using hy
  · rcases hx with hx | hx
    · exact hVertical (by omega : i<2*θ+1) hEven hx hy
    · rw [mem_singleton_iff] at hx
      apply hVertical hi hEvenRight (p := p) _ hy
      simpa only [Nat.cast_add,Nat.cast_ofNat] using hx

/-- The intrinsic boundary of an embedded wall brick lies in the drawing. -/
theorem sphereWall_brick_disc_boundary_subset_U {S : Type*}
    [TopologicalSpace S] [T2Space S] {θ : ℕ}
    (f : (ℝ × ℝ) → S) (hf : IsEmbedding f) (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val
      = f '' rectangularGridLine e.val)
    {i j : ℕ} (hi : i+2 < 2*θ+1) (hj : j+1 < θ) (hEven : Even (i+j)) :
    discBd (f '' (Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1))) ⊆ Γ.drawing.U := by
  obtain ⟨hRect,hB⟩ := isClosedDisc_real_rectangle_with_boundary
    (by linarith : (i : ℝ) < (i : ℝ)+2) (by linarith : (j : ℝ) < (j : ℝ)+1)
  obtain ⟨_,hImage⟩ := isClosedDisc_image_injOn hRect hRect.isCompact
    hf.continuous.continuousOn hf.injective.injOn
  rw [hImage,hB]
  exact sphereWall_brick_frontier_image_subset_U f Γ hE hi hj hEven

end GraphMinor.GM16
