/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46LongEdges
import LeanPool.GraphMinor.GM11.Walks

/-!
# The new vertices on each closed seam edge

In VII (4.6), page 225, `W(e)` lies inside the old edge `e`.
Different old edges are disjoint. No point of `W` is an old vertex,
so intersecting `W` with a closed long edge gives exactly its own
pair of cut points. This identifies the marked local drawing in `J⁺`.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

/-- Only the two cut points belonging to a long edge lie on its closure,
in the construction of `J⁺` in VII (4.6), page 225. -/
theorem W_inter_closed_long_edge {S : Type*} [TopologicalSpace S]
    {G J : Drawing S} {μ w : ℕ} (W : longSeamEdges G J μ w → Set S)
    (hW : ∀ f, W f ⊆ f.1) (e : longSeamEdges G J μ w) :
    (⋃ f, W f) ∩ closure e.1 = W e := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨f, hxf⟩ := mem_iUnion.mp hx.1
    have hxfE := hW f hxf
    have hxV : x ∉ J.V := (f.2.1.2.1 hxfE).2
    have hxe : x ∈ e.1 := J.closure_diff_V e.2.1 ▸ (⟨hx.2, hxV⟩ : x ∈ closure e.1 \ J.V)
    have hef : e = f := Subtype.ext (J.edge_eq_of_mem e.2.1 f.2.1 hxe hxfE)
    exact hef ▸ hxf
  · intro x hx
    exact ⟨mem_iUnion.mpr ⟨e, hx⟩, subset_closure (hW e hx)⟩

/-- The marked vertices of the local drawing on a closed long edge are
its old ends together with `W(e)`, in VII (4.6), page 225. -/
theorem marked_vertices_closed_long_edge {S : Type*} [TopologicalSpace S]
    {G J : Drawing S} {μ w : ℕ} (W : longSeamEdges G J μ w → Set S)
    (hW : ∀ f, W f ⊆ f.1) (e : longSeamEdges G J μ w) :
    (J.V ∪ ⋃ f, W f) ∩ closure e.1 = (closure e.1 ∩ J.V) ∪ W e := by
  rw [union_inter_distrib_right, W_inter_closed_long_edge W hW e, inter_comm J.V]

end GraphMinor.GM07
