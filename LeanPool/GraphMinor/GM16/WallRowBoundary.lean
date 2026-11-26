/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
import LeanPool.GraphMinor.GM16.WallEnclosedCoordinates
import LeanPool.GraphMinor.GM16.LocalCoordinateBoundary
import LeanPool.GraphMinor.GM16.LineClosedExtension
import LeanPool.GraphMinor.GM16.RectangularLines
import Mathlib.Tactic.Linarith

/-!
# The vertical sides of the outside wall boundary

Inside an open unit-height strip, the enclosed disc has exactly
that row's horizontal interval. Its extreme horizontal coordinates
are boundary points. Closedness of the frontier adds the two row
corners. Thus both vertical sides of every row are on the outer
boundary, including the indented sides of odd rows.
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

private theorem vertical_side_subset_closed {C : Set (ℝ × ℝ)} (hC : IsClosed C)
    (x y : ℝ) (hSub : ∀ p : ℝ × ℝ, p.1 = x → p.2 ∈ Ioo y (y+1) → p ∈ C) :
    {x} ×ˢ Icc y (y+1) ⊆ C := by
  apply line_subset_closed_of_open_part_subset
    (vertical_interval_isLine x (by linarith : y<y+1)) hC
  rintro p ⟨hp,hn⟩
  have hyLo : y < p.2 := by
    apply lt_of_le_of_ne hp.2.1
    intro he
    exact hn (Or.inl (Prod.ext hp.1 he.symm))
  have hyHi : p.2 < y+1 := by
    apply lt_of_le_of_ne hp.2.2
    intro he
    exact hn (Or.inr (mem_singleton_iff.mpr (Prod.ext hp.1 he)))
  exact hSub p hp.1 ⟨hyLo,hyHi⟩

/-- Both vertical sides of a row belong to the frontier of the enclosed disc. -/
theorem wall_row_vertical_sides_subset_frontier {θ j : ℕ} (hθ : 2 ≤ θ) (hj : j + 1 < θ) :
    ({wallRowLeft j} ×ˢ Icc (j : ℝ) ((j : ℝ)+1) ⊆ frontier (wallEnclosedSet θ)) ∧
    ({wallRowRight θ j} ×ˢ Icc (j : ℝ) ((j : ℝ)+1) ⊆ frontier (wallEnclosedSet θ)) := by
  have hθReal : (4 : ℝ) ≤ ((2*θ : ℕ) : ℝ) := by exact_mod_cast (show 4≤2*θ by omega)
  have hWidth : wallRowLeft j ≤ wallRowRight θ j := by
    dsimp only [wallRowRight]
    linarith [(wallRowLeft_bounds j).2]
  have hOpen : IsOpen {p : ℝ × ℝ | p.2 ∈ Ioo (j : ℝ) ((j : ℝ)+1)} :=
    isOpen_Ioo.preimage continuous_snd
  constructor
  · apply vertical_side_subset_closed isClosed_frontier
    intro p hpx hpy
    have hpC : p ∈ wallEnclosedSet θ := mem_iUnion₂.mpr
      ⟨j,by omega,⟨⟨hpx.ge,hpx.symm ▸ hWidth⟩,Ioo_subset_Icc_self hpy⟩⟩
    refine ⟨subset_closure hpC,?_⟩
    apply not_mem_interior_of_local_coordinate_min hOpen isOpenMap_fst hpy hpx
    intro q hq
    exact (wallEnclosedSet_mem_open_strip hq.1 hq.2).2.1
  · apply vertical_side_subset_closed isClosed_frontier
    intro p hpx hpy
    have hpC : p ∈ wallEnclosedSet θ := mem_iUnion₂.mpr
      ⟨j,by omega,⟨⟨hpx.symm ▸ hWidth,hpx.le⟩,Ioo_subset_Icc_self hpy⟩⟩
    refine ⟨subset_closure hpC,?_⟩
    apply not_mem_interior_of_local_coordinate_max hOpen isOpenMap_fst hpy hpx
    intro q hq
    exact (wallEnclosedSet_mem_open_strip hq.1 hq.2).2.2

end GraphMinor.GM16
