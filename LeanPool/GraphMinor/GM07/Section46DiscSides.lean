/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# The disc-side argument for the unique seam region

In VII (4.6), page 226, the complement of the seam is connected and
dense in the original surface. If a disc boundary misses that complement,
the complement lies on one side of the disc. Either the disc contains
the whole original surface, or it meets that surface only in its boundary.
This also applies when the disc lies in a capped surface.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

/-- The disc-side argument used for `R` in VII (4.6), page 226. The set
`C` is the complement of the seam, and `A` is the original surface
inside the ambient (possibly capped) surface. -/
theorem disc_side_of_dense_connected_set {S : Type*} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {A C D : Set S}
    (hD : IsClosedDisc D) (hC : IsPreconnected C) (hAC : A ⊆ closure C)
    (hbd : Disjoint C (discBd D)) :
    A ⊆ D ∨ D ∩ A ⊆ discBd D := by
  rcases hD.side hman hC hbd with hinside | houtside
  · exact .inl (hAC.trans (closure_minimal (hinside.trans (discInt_subset D)) hD.isClosed))
  · apply Or.inr
    intro x hx
    by_contra hxbd
    have hxInt : x ∈ discInt D := ⟨hx.1, hxbd⟩
    obtain ⟨y, hyInt, hyC⟩ := mem_closure_iff.mp (hAC hx.2)
      (discInt D) (hD.isOpen_discInt hman) hxInt
    exact disjoint_left.mp houtside hyC hyInt.1

end GraphMinor.GM07
