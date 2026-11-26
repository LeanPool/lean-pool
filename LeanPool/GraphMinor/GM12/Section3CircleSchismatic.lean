/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.GM12.Section3CircleInclusion

/-!
# The circle case of the schismatic definition

For VII Section 8, used in XII (3.1), page 245, a circle which is not
near-planar is schismatic. It contains no proper subset which is a
circle, so the minimal-circle clause follows from the circle inclusion
theorem.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A circle which is not near-planar is schismatic, since every
circle contained in it is equal to it. -/
theorem isSchismatic_oArc
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (hF : IsOArc F) (hnot : ¬ GM07.IsNearPlanar F) : GM07.IsSchismatic F := by
  refine ⟨Or.inl hF, hnot, ?_⟩
  intro Z hZ hZF
  have heq : Z = F := oArc_eq_of_subset hZ hF hZF.1
  exact False.elim (hZF.2 heq.symm.le)

end GraphMinor.GM12
