/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ThetaHomotopy
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.GM12.Section3PlanarityMaps

/-!
# A planar chord is homotopic into its circle

In the extraction used by XII (3.1), page 245, a cap making the first
circle and a chord planar also makes the chord homotopic to one arc
of that circle. Choose an arc between the chord endpoints and apply
the fixed-end homotopy inside the containing disc.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A planar image of a circle and injective chord makes that chord
homotopic to a path in the image of the circle. -/
theorem exists_homotopic_path_in_oArc_of_planar_chord
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    {F : Set S} (hF : IsOArc F) {a b : S} (c : Path a b)
    (hci : Function.Injective c) (ha : a ∈ F) (hb : b ∈ F) (j : C(S, T))
    (hplan : IsPlanar (j '' (F ∪ range c))) :
    ∃ r : Path (j a) (j b), (c.map j.continuous).Homotopic r ∧ range r ⊆ j '' F := by
  have hab : a ≠ b := by
    intro heq
    have he : c 0 = c 1 := c.source.trans (heq.trans c.target.symm)
    exact zero_ne_one (hci he)
  obtain ⟨f, g, hfg, hf0, hf1, hfgF⟩ := hF.exists_arcs ha hb hab
  let r₀ : Path a b := {
    toFun := f
    continuous_toFun := hfg.arc_left.1
    source' := hf0
    target' := hf1 }
  let r := r₀.map j.continuous
  have hr₀ : range r₀ ⊆ F := hfgF ▸ subset_union_left
  have hr : range r ⊆ j '' F := by
    change range (j ∘ r₀) ⊆ j '' F
    rw [range_comp]
    exact image_mono hr₀
  refine ⟨r, paths_homotopic_of_planar_union (c.map j.continuous) r
    (isPlanar_mono ?_ hplan), hr⟩
  apply union_subset
  · change range (j ∘ c) ⊆ j '' (F ∪ range c)
    rw [range_comp]
    exact image_mono subset_union_right
  · exact hr.trans (image_mono subset_union_left)

end GraphMinor.GM12
