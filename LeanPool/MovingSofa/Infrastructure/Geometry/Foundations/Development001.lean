/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Moving sofa: related mathematical developments

* `Classical.Foundations.Development001`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Classical.Area`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Planar area

The real-valued Lebesgue area of a planar set, and its invariance under translation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace MovingSofa.ClassicalResults

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The real-valued Lebesgue area of a planar set. -/
def area (s : Set Plane) : ℝ := (volume s).toReal

/-- Planar area is invariant under translation. -/
theorem area_image_add (S : Set Plane) (v : Plane) :
    area ((fun p ↦ p + v) '' S) = area S := by
  change (MeasureTheory.volume ((fun p ↦ p + v) '' S)).toReal =
    (MeasureTheory.volume S).toReal
  rw [Set.image_add_right]
  have hf : (fun x : Plane ↦ x + -v) = fun x ↦ -v + x := by
    funext x
    exact add_comm x (-v)
  rw [hf, MeasureTheory.measure_preimage_add]

end MovingSofa.ClassicalResults

end

end

end

end

end

end
