/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM16.DrawingGraphPaths
import LeanPool.GraphMinor.GM16.Section9Attachments
import LeanPool.GraphMinor.GM11.Section6

/-!
# A path meets a drawn boundary only at its boundary vertices

If a path has only one vertex on a boundary subdrawing, it has no
edge there. Their point-set intersection is consequently their
vertex intersection. This is used when trimming Claim (10)'s paths
into the battlefield disc for XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11
universe u
variable {S : Type u} [TopologicalSpace S]

/-- A path with at most one vertex on a subdrawing meets its whole
point set only at that vertex. -/
theorem path_inter_subdrawing_subset_singleton {H P B : Drawing S}
    {a b v : S} (hP : P.IsSubdrawing H) (hB : B.IsSubdrawing H)
    (hPath : P.IsPathBetween a b) (hInter : P.V ∩ B.U ⊆ {v}) :
    P.U ∩ B.U ⊆ {v} := by
  have hE : Disjoint P.E B.E := path_edges_disjoint_of_singleton_inter
    (toGraph_le_of_isSubdrawing hB) (graphPath_of_drawingPath hP hPath)
    (fun _ hx => hInter ⟨hx.1, B.V_subset_U hx.2⟩)
  rw [U_inter_of_disjoint hP hB hE]
  exact fun _ hx => hInter ⟨hx.1, B.V_subset_U hx.2⟩

end GraphMinor.GM16
