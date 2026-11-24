/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46SeamPartsDefs
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46SplitEdges

/-!
# Counting the edges retained in `L`

For VII (4.6), page 226, each short old edge contributes at most one
edge to `L`, and each long old edge at most its two linking edges.
Thus `|E(L)| ≤ 2|E(J)|`. The central set has at most one edge for each
long old edge, as used for the matching bound on page 227.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

private theorem ncard_range_le_card {α β : Type*} [Finite α] (f : α → β) :
    (range f).ncard ≤ Nat.card α := by
  rw [← image_univ]
  exact (ncard_image_le finite_univ).trans_eq (ncard_univ α)

/-- There is at most one central edge for each long edge, in
VII (4.6), pages 226–227. -/
theorem ncard_centralEdges_le {S : Type*} [TopologicalSpace S]
    (G J : Drawing S) (μ w : ℕ) (γ : Set S → unitInterval → S)
    (s t : longSeamEdges G J μ w → unitInterval) :
    (centralEdges G J μ w γ s t).ncard ≤ (longSeamEdges G J μ w).ncard := by
  have hlong : longSeamEdges G J μ w ⊆ J.E := fun _ he => he.1
  have : Finite (longSeamEdges G J μ w) := (J.finite_edges.subset hlong).to_subtype
  exact ncard_range_le_card _

/-- At most two linking edges arise from each long edge in VII (4.6),
page 225. -/
theorem ncard_linkingEdges_le {S : Type*} [TopologicalSpace S]
    (G J : Drawing S) (μ w : ℕ) (γ : Set S → unitInterval → S)
    (s t : longSeamEdges G J μ w → unitInterval) :
    (linkingEdges G J μ w γ s t).ncard ≤ 2 * (longSeamEdges G J μ w).ncard := by
  have hlong : longSeamEdges G J μ w ⊆ J.E := fun _ he => he.1
  have : Finite (longSeamEdges G J μ w) := (J.finite_edges.subset hlong).to_subtype
  have hleft := ncard_range_le_card (fun e : longSeamEdges G J μ w => γ e.1 '' Ioo 0 (s e))
  have hright := ncard_range_le_card (fun e : longSeamEdges G J μ w => γ e.1 '' Ioo (t e) 1)
  have hu := ncard_union_le (range fun e : longSeamEdges G J μ w => γ e.1 '' Ioo 0 (s e))
    (range fun e : longSeamEdges G J μ w => γ e.1 '' Ioo (t e) 1)
  change (linkingEdges G J μ w γ s t).ncard ≤ _ at hu
  rw [Nat.card_coe_set_eq] at hleft hright
  omega

/-- Every retained edge is short or linking, in VII (4.6), page 226. -/
theorem L_edges_subset_short_union_linking {S : Type*} [TopologicalSpace S] [T2Space S]
    {G J J' L : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (s t : longSeamEdges G J μ w → unitInterval)
    (W : longSeamEdges G J μ w → Set S)
    (hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
      W e = {γ e.1 (s e), γ e.1 (t e)})
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ ⋃ e, W e)
    (hLE : L.E = forestSeamEdges J' (centralEdges G J μ w γ s t)) :
    L.E ⊆ shortSeamEdges G J μ w ∪ linkingEdges G J μ w γ s t := by
  have hE := J_plus_edges hγ s t W hcuts hU hV
  intro f hf
  rw [hLE] at hf
  have hfE := hf.1
  rw [hE] at hfE
  rcases hfE with hshort | hpieces
  · exact .inl hshort
  · obtain ⟨e, he⟩ := mem_iUnion.mp hpieces
    rcases he with rfl | rfl | rfl
    · exact .inr (.inl ⟨e, rfl⟩)
    · exact (hf.2.1 ⟨e, rfl⟩).elim
    · exact .inr (.inr ⟨e, rfl⟩)

/-- The retained graph `L` has at most twice as many edges as `J`,
the edge count used on page 226 of VII (4.6). -/
theorem L_edge_ncard_le_two_mul_old_edges {S : Type*} [TopologicalSpace S] [T2Space S]
    {G J J' L : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (s t : longSeamEdges G J μ w → unitInterval)
    (W : longSeamEdges G J μ w → Set S)
    (hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
      W e = {γ e.1 (s e), γ e.1 (t e)})
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ ⋃ e, W e)
    (hLE : L.E = forestSeamEdges J' (centralEdges G J μ w γ s t)) :
    L.E.ncard ≤ 2 * J.E.ncard := by
  have hsub := L_edges_subset_short_union_linking hγ s t W hcuts hU hV hLE
  have hshortfin : (shortSeamEdges G J μ w).Finite := J.finite_edges.subset sdiff_subset
  have hlongfin : (longSeamEdges G J μ w).Finite := J.finite_edges.subset fun e he => he.1
  have : Finite (longSeamEdges G J μ w) := hlongfin.to_subtype
  have hlinkfin : (linkingEdges G J μ w γ s t).Finite := (finite_range _).union (finite_range _)
  have hcard := ncard_le_ncard hsub (hshortfin.union hlinkfin)
  have hu := ncard_union_le (shortSeamEdges G J μ w) (linkingEdges G J μ w γ s t)
  have hl := ncard_linkingEdges_le G J μ w γ s t
  have hlongsub : longSeamEdges G J μ w ⊆ J.E := fun e he => he.1
  have hpartition := ncard_sdiff_add_ncard_of_subset hlongsub J.finite_edges
  change (shortSeamEdges G J μ w).ncard + (longSeamEdges G J μ w).ncard = J.E.ncard at hpartition
  omega

end GraphMinor.GM07
