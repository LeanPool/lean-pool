/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46LongEdges
import LeanPool.GraphMinor.GM07.Section46RefinedEdges

/-!
# Short edges remain edges of `J⁺`

The new vertices `W(e)` lie inside long edges. Distinct old edges are
disjoint, so no short edge contains a new vertex. It therefore remains
an edge of the refined seam graph, as stated on page 225 of VII (4.6).
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

/-- Every short edge of `J` is an edge of `J⁺`, in VII (4.6), page 225. -/
theorem short_edge_mem_J_plus {S : Type*} [TopologicalSpace S]
    {G J J' : Drawing S} {μ w : ℕ}
    (W : longSeamEdges G J μ w → Set S) (hW : ∀ f, W f ⊆ f.1)
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ ⋃ f, W f)
    {e : Set S} (he : e ∈ shortSeamEdges G J μ w) : e ∈ J'.E := by
  apply edge_mem_refinement_of_disjoint hU hV he.1
  apply disjoint_left.mpr
  intro x hxe hxW
  obtain ⟨f, hxf⟩ := mem_iUnion.mp hxW
  have hef := J.edge_eq_of_mem he.1 f.2.1 hxe (hW f hxf)
  exact he.2 (hef.symm ▸ f.2)

end GraphMinor.GM07
