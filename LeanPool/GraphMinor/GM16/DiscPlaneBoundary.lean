/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# Boundaries of plane discs

The closed domain of a Jordan curve is the complement of its outer
side. Its frontier is therefore that curve. This identifies the
intrinsic disc boundary with the frontier in the plane presentations
used in XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface

/-- In the complex plane a closed disc has frontier equal to its
intrinsic boundary. -/
theorem complex_disc_frontier {D : Set ℂ} (hD : IsClosedDisc D) :
    frontier D = discBd D := by
  obtain ⟨φ⟩ := hD.isOArc_discBd
  have J := isJordanParts φ
  have heq : closedInner (discBd D) = (outer (discBd D))ᶜ := by
    ext z
    change (z ∈ inner (discBd D) ∨ z ∈ discBd D) ↔ z ∉ outer (discBd D)
    constructor
    · rintro (hz | hz)
      · exact J.disjoint.notMem_of_mem_left hz
      · exact fun h => h.1 hz
    · intro hz
      by_cases hb : z ∈ discBd D
      · exact Or.inr hb
      · have hmem : z ∈ inner (discBd D) ∪ outer (discBd D) :=
          J.union_eq.symm ▸ hb
        exact Or.inl (hmem.resolve_right hz)
  conv_lhs => rw [eq_closedInner_of_discBd ⟨φ⟩ hD rfl, heq, frontier_compl, J.frontier_outer]

/-- In the Euclidean plane the frontier and intrinsic disc boundary
also agree. -/
theorem plane_disc_frontier {D : Set EuclideanPlane} (hD : IsClosedDisc D) :
    frontier D = discBd D := by
  let e : EuclideanPlane ≃ₜ ℂ := complexPlane.symm.toHomeomorph
  obtain ⟨hDc, hb⟩ := hD.image (f := e) (f' := e.symm)
    e.continuous.continuousOn e.symm.continuous.continuousOn
    (fun _ _ => e.symm_apply_apply _)
  apply e.injective.image_injective
  rw [e.image_frontier, complex_disc_frontier hDc, hb]

end GraphMinor.GM16
