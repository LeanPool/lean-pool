/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM12.Section4PendantLine
import LeanPool.GraphMinor.GM11.PaintingCells
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM11.Walks

/-!
# Adding a pendant edge at an isolated vertex

The target replacement in XII (4.3), page 249, also has to
handle isolated vertices. A short line in an isolated vertex's
chart adds a new neighbour and meets the drawing only at the
original vertex. Glue its one-edge drawing to the target. Both
ends then have an incident edge.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The isolated-vertex step of the target replacement in XII
(4.3), page 249. The old drawing is retained as a subdrawing. -/
theorem exists_pendant_augmentation
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (Γ : Drawing S) {v : S} (hv : v ∈ Γ.V)
    (hiso : ∀ e, ¬ Γ.toGraph.Inc e v) :
    ∃ (H : Drawing S) (w : S) (e : Set S), Γ.IsSubdrawing H ∧
      H.V = insert w Γ.V ∧ w ∉ Γ.U ∧ H.toGraph.IsLink e v w := by
  have hoff : ∀ e ∈ Γ.E, v ∉ closure e := by
    intro e he hve
    obtain ⟨x, y, hl⟩ := Γ.toGraph.exists_isLink_of_mem_edgeSet he
    have hvpair : v ∈ ({x, y} : Set S) := hl.2.2.2 ▸ ⟨hve, hv⟩
    rcases hvpair with hvx | hvy
    · exact hiso e (hvx ▸ hl.inc_left)
    · exact hiso e ((Set.mem_singleton_iff.mp hvy) ▸ hl.inc_right)
  obtain ⟨w, L, hL, hw, hLU⟩ := exists_line_at_isolated_point hS (Γ.V_subset_U hv)
    (isClosed_U_sdiff_of_isolated_vertex hoff)
  have hvw : v ≠ w := fun heq => hw (heq ▸ Γ.V_subset_U hv)
  let K := lineDrawing hL hvw
  have hKU : K.U = L := rfl
  have hKV : K.V = {v, w} := rfl
  have hKE : K.E = {L \ {v, w}} := lineDrawing_E _ _
  have hglue : Γ.U ∩ K.U ⊆ Γ.V ∩ K.V := by
    rintro x ⟨hxΓ, hxK⟩
    have hxv : x = v := Set.mem_singleton_iff.mp (hLU.subset ⟨hxK, hxΓ⟩)
    exact hxv ▸ ⟨hv, Or.inl rfl⟩
  let H := Γ.glue K hglue
  have hHE : H.E = Γ.E ∪ K.E := Drawing.glue_E hglue
  have hΓH : Γ.IsSubdrawing H := ⟨subset_union_left, by rw [hHE]; exact subset_union_left⟩
  have hKH : K.IsSubdrawing H := ⟨subset_union_right, by rw [hHE]; exact subset_union_right⟩
  have hHV : H.V = insert w Γ.V := by
    change Γ.V ∪ {v, w} = insert w Γ.V
    ext x
    simp only [mem_union, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (hx | hx | hx)
      · exact Or.inr hx
      · exact Or.inr (hx ▸ hv)
      · exact Or.inl hx
    · rintro (hx | hx)
      · exact Or.inr (Or.inr hx)
      · exact Or.inl hx
  have hlink : K.toGraph.IsLink (L \ {v, w}) v w := by
    refine ⟨?_, Or.inl rfl, Or.inr rfl, ?_⟩
    · rw [hKE]
      exact mem_singleton _
    · rw [closure_sdiff_pair hL]
      apply inter_eq_right.mpr
      exact K.V_subset_U
  exact ⟨H, w, L \ {v, w}, hΓH, hHV, hw, (hKH.isLink_iff hlink.edge_mem).mp hlink⟩

end GraphMinor.GM12
