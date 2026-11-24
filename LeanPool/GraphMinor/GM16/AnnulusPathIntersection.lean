/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.PathCrossesZone
import LeanPool.GraphMinor.GM16.DrawingGraphPaths
import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM11.Section810

/-!
# The clean path meets the annular subdrawing

A path from inside the outer zone to outside it contains a vertex
on that zone boundary. Since the inner closed zone lies strictly
inside the outer zone, this vertex belongs to the annular subdrawing.
This is the intersection assertion in XVI (8.1), Claim (14).
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- Crossing the outer boundary of an annulus gives a common vertex
with its annular subdrawing. -/
theorem drawingPath_meets_annular_subdrawing {H P : Drawing S}
    {d : Set S → Set S → ℕ} {γ δ : ℕ} {z w I O : Set S} {a b : S}
    (hI : IsLambdaZoneAround H d γ z I) (hO : IsLambdaZoneAround H d δ w O)
    (hNest : closure I ⊆ O) (hP : P.IsSubdrawing H) (hPath : P.IsPathBetween a b)
    (ha : a ∈ O) (hb : b ∉ O) :
    (P.V ∩ (H.interSet (closure O \ I)).V).Nonempty := by
  obtain ⟨v, hvP, hvH, hvBd⟩ := drawingPath_meets_zone_boundary hO hP hPath ha hb
  have hvNot : v ∉ I := fun hvi =>
    ((isOpen_disjoint_subBd_and_closure_eq hO.isOpenDisc.1).1).notMem_of_mem_left
      (hNest (subset_closure hvi)) hvBd
  refine ⟨v, hvP, (mem_interSet_V_iff (isClosed_closure.sdiff hI.isOpenDisc.1)).mpr ?_⟩
  exact ⟨hvH, hvBd.1, hvNot⟩

end GraphMinor.GM16
