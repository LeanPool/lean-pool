/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM01.Defs
import LeanPool.GraphMinor.GM09.Basic

/-!
# Branch centres occur on replacing paths

If the original graph has no isolated vertices, choose an edge
incident with each vertex. Its replacing path contains that
vertex's centre as one of its ends. Thus the replacing paths
already contain all centres, and no separate isolated-vertex
piece is needed when gluing the wall subdivision drawing.
-/

public section
namespace GraphMinor.GM16
open Set Graph Surface GM09
universe u v w

/-- With no isolated original vertices, the replacing paths cover
all branch centres. -/
theorem subdivision_centres_subset_path_union
    {α : Type u} {β : Type v} {ν : Type w} {N : Graph α β} {H : SimpleGraph ν}
    (c : ν → α) (P : H.edgeSet → Graph α β)
    (hPaths : ∀ e : H.edgeSet, ∃ a b, e.val=s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b))
    (hNoIsolated : ∀ v, ∃ w, H.Adj v w) : range c ⊆ ⋃ e, V(P e) := by
  rintro x ⟨v,rfl⟩
  obtain ⟨w,hw⟩ := hNoIsolated v
  let e : H.edgeSet := ⟨s(v,w),hw⟩
  obtain ⟨a,b,he,hPath⟩ := hPaths e
  have hv : v ∈ s(a,b) := he ▸ Sym2.mem_mk_left v w
  rw [Sym2.mem_iff] at hv
  refine mem_iUnion_of_mem e ?_
  rcases hv with hv | hv
  · exact hv.symm ▸ hPath.left_mem
  · exact hv.symm ▸ hPath.right_mem

end GraphMinor.GM16
