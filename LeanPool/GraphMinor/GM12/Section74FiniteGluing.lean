/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Corners
public import LeanPool.GraphMinor.GM12.Section76
import LeanPool.GraphMinor.GM12.Section74RegionMerge
import LeanPool.GraphMinor.GM12.Section74LeafTwoCell
import LeanPool.GraphMinor.GM12.Section77
import Mathlib.Data.Finset.Card

/-!
# Finite gluing of the corner regions at a vertex

In the base case of XII (7.4), pages 262--263, the corner regions
at the vertex are distinct. Keep one incident edge. Starting in
one corner, glue successive corner regions across all the other
incident edges. At each step the fresh corner region is distinct
from the merged region, so deleting their common edge preserves
two-cellularity. A finite cyclic order has an exit from every
proper nonempty subset. Thus the process reaches every corner.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private def removedCornerEdges {α β : Type*} (f : α → β) (keep : α) (A : Finset α) : Set β :=
  {e | ∃ k ∈ A, k ≠ keep ∧ f k = e}

private theorem removedCornerEdges_insert {α β : Type*} [DecidableEq α] (f : α → β) (keep b : α)
    (A : Finset α) (hb : b ≠ keep) :
    removedCornerEdges f keep (insert b A) = insert (f b) (removedCornerEdges f keep A) := by
  ext e
  simp only [removedCornerEdges, mem_ofPred_eq, Finset.mem_insert, mem_insert_iff]
  constructor
  · rintro ⟨k, hk | hk, hkeep, he⟩
    · exact Or.inl (he.symm.trans (congrArg f hk))
    · exact Or.inr ⟨k, hk, hkeep, he⟩
  · rintro (he | ⟨k, hk, hkeep, hke⟩)
    · exact ⟨b, Or.inl rfl, hb, he.symm⟩
    · exact ⟨k, Or.inr hk, hkeep, hke⟩

private theorem exists_exit_of_reach {α : Type*} (next : α → α)
    (hreach : ∀ a b, Relation.ReflTransGen (fun x y => y = next x) a b)
    (A : Finset α) {keep : α} (hkeep : keep ∈ A) (hne : ∃ b, b ∉ A) :
    ∃ a ∈ A, next a ∉ A := by
  by_contra h
  push Not at h
  obtain ⟨b, hb⟩ := hne
  have hall : ∀ c, c ∈ A := by
    intro c
    have hr := hreach keep c
    induction hr with
    | refl => exact hkeep
    | tail hr hs ih => exact hs ▸ h _ ih
  exact hb (hall b)

/-- Finite gluing around a vertex with distinct corner regions
and with each incident edge represented once. All incident edges
except the chosen one can be deleted while keeping two-cellularity. -/
theorem exists_twoCell_after_gluing_corners
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S}
    (hΓ : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    {γ : Set S → unitInterval → S} {v : S}
    {next : halfEdges Γ γ v → halfEdges Γ γ v}
    {ρ : halfEdges Γ γ v → Set S} (hcor : IsCorners Γ γ v next ρ)
    (hρ : Function.Injective ρ)
    (hEdges : Function.Injective (fun k : halfEdges Γ γ v => k.1.1))
    (keep : halfEdges Γ γ v) :
    ∃ D : Drawing S, D.IsSubdrawing Γ ∧ D.V = Γ.V ∧
      D.E = Γ.E \ {e | ∃ k : halfEdges Γ γ v, k ≠ keep ∧ k.1.1 = e} ∧
      (PaintingOrDrawing.drawing D).IsTwoCell := by
  let α := halfEdges Γ γ v
  let : Fintype α := (finite_halfEdges Γ γ v).fintype
  let f : α → Set S := fun k => k.1.1
  let R := removedCornerEdges f keep
  let good : ℕ → Prop := fun n => ∃ (A : Finset α) (D : Drawing S) (T : Set S),
    keep ∈ A ∧ (Finset.univ \ A).card = n ∧ D.IsSubdrawing Γ ∧ D.V = Γ.V ∧
    D.E = Γ.E \ R A ∧ (PaintingOrDrawing.drawing D).IsTwoCell ∧ T ∈ D.R ∧
    (∀ k ∈ A, ρ k ⊆ T) ∧ (∀ k ∉ A, ρ k ∈ D.R)
  have hRone : R {keep} = ∅ := by
    ext e
    simp [R, removedCornerEdges]
  have hex : ∃ n, good n := by
    refine ⟨_, {keep}, Γ, ρ keep, by simp, rfl, Drawing.IsSubdrawing.refl Γ, rfl, ?_, hΓ,
      hcor.region keep, ?_, ?_⟩
    · rw [hRone, sdiff_empty]
    · intro k hk
      have hkEq : k = keep := Finset.mem_singleton.mp hk
      exact hkEq ▸ Subset.rfl
    · intro k _
      exact hcor.region k
  classical
  obtain ⟨A, D, T, hkeep, hcard, hDΓ, hDV, hDE, hD, hTR, hcontain, houtside⟩ := Nat.find_spec hex
  by_cases hAll : A = Finset.univ
  · refine ⟨D, hDΓ, hDV, ?_, hD⟩
    rw [hDE, hAll]
    congr 1
    ext e
    simp only [R, removedCornerEdges, mem_ofPred_eq, Finset.mem_univ, true_and]
    rfl
  have hne : ∃ b : α, b ∉ A := by
    by_contra h
    push Not at h
    exact hAll (Finset.eq_univ_of_forall h)
  obtain ⟨a, ha, hb⟩ := exists_exit_of_reach next hcor.reach A hkeep hne
  let b := next a
  have hbA : b ∉ A := hb
  have hbkeep : b ≠ keep := fun h => hbA ((congrArg (fun x => x ∈ A) h.symm).mp hkeep)
  have hbD : f b ∈ D.E := by
    rw [hDE]
    refine ⟨b.2.1, ?_⟩
    rintro ⟨k, hk, _, hke⟩
    exact hbA ((congrArg (fun x => x ∈ A) (hEdges hke)).mp hk)
  have hneT : ∀ k ∉ A, ρ k ≠ T := by
    intro k hk hEq
    obtain ⟨x, hx⟩ := region_nonempty (hcor.region keep)
    have hxT := hcontain keep hkeep hx
    have heq : ρ keep = ρ k := region_eq_of_mem (hcor.region keep) (hcor.region k) hx
      (hEq.symm ▸ hxT)
    exact hk ((hρ heq) ▸ hkeep)
  have hbR : ρ b ∈ D.R := houtside b hb
  have hTb : T ≠ ρ b := (hneT b hb).symm
  have heT : f b ⊆ closure T := (hcor.left a).trans (closure_mono (hcontain a ha))
  have heb : f b ⊆ closure (ρ b) := hcor.right a
  have hDnew := isTwoCell_deleteEdge_of_distinct_regions hS hD hbD hTR hbR hTb heT heb
  obtain ⟨hTnew, _⟩ := merged_region_deleteEdge hS hbD hTR hbR hTb (hD.2 T hTR) (hD.2
    (ρ b) hbR) heT heb
  have hRinsert : R (insert b A) = insert (f b) (R A) := by
    simpa only [R] using removedCornerEdges_insert f keep b A hbkeep
  have hDEnew : (D.deleteEdge (f b)).E = Γ.E \ R (insert b A) := by
    rw [deleteEdge_E, hDE, hRinsert]
    ext e
    simp only [mem_sdiff, mem_singleton_iff, mem_insert_iff]
    tauto
  have hnew : good (Finset.univ \ insert b A).card := by
    refine ⟨insert b A, D.deleteEdge (f b), T ∪ ρ b ∪ f b, Finset.mem_insert_of_mem hkeep, rfl,
      (deleteEdge_isSubdrawing D (f b)).trans hDΓ, (deleteEdge_V D (f b)).trans hDV,
      hDEnew, hDnew, hTnew, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_insert.mp hk with hk | hk
      · exact hk ▸ (subset_union_right.trans subset_union_left)
      · exact (hcontain k hk).trans (subset_union_left.trans subset_union_left)
    · intro k hk
      have hkA : k ∉ A := fun h => hk (Finset.mem_insert_of_mem h)
      have hkb : k ≠ b := fun h => hk (Finset.mem_insert.mpr (Or.inl h))
      exact region_deleteEdge_of_ne_merged_pair hS hbD hTR hbR hTb
        (hD.2 T hTR) (hD.2 (ρ b) hbR) heT heb (houtside k hkA) (hneT k hkA)
        (fun h => hkb (hρ h))
  have hle := Nat.find_min' hex hnew
  have hbDiff : b ∈ Finset.univ \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hb⟩
  have hpos : 0 < (Finset.univ \ A).card := Finset.card_pos.mpr ⟨b, hbDiff⟩
  rw [Finset.sdiff_insert, Finset.card_erase_of_mem hbDiff] at hle
  omega

/-- Distinct corner regions give cellularity after vertex deletion
when each incident edge has one half-edge there and the retained
edge is a line. The finite gluing leaves precisely this leaf edge. -/
theorem isTwoCell_delete_vertex_of_corner_data
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S}
    (hΓ : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    {γ : Set S → unitInterval → S} (hγ : EdgePar Γ γ) {v : S} (hv : v ∈ Γ.V)
    {next : halfEdges Γ γ v → halfEdges Γ γ v}
    {ρ : halfEdges Γ γ v → Set S} (hcor : IsCorners Γ γ v next ρ)
    (hρ : Function.Injective ρ)
    (hEdges : Function.Injective (fun k : halfEdges Γ γ v => k.1.1))
    (keep : halfEdges Γ γ v) {u : S} (huv : u ≠ v)
    (hcap : closure keep.1.1 ∩ Γ.V = {u, v})
    (hLine : IsLineWithEnds (closure keep.1.1) u v) :
    (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell := by
  obtain ⟨D, hDΓ, hDV, hDE, hD⟩ := exists_twoCell_after_gluing_corners hS hΓ hcor hρ hEdges keep
  have hhalf : ∀ k : halfEdges Γ γ v, v ∈ closure k.1.1 := by
    intro k
    exact (congrArg (fun x => x ∈ closure k.1.1) k.2.2).mp
      (end_mem_closure hγ k.2.1 k.1.2)
  have hkept : keep.1.1 ∈ D.E := by
    rw [hDE]
    refine ⟨keep.2.1, ?_⟩
    rintro ⟨k, hk, hke⟩
    exact hk (hEdges hke)
  have hleaf : ∀ f ∈ D.E, f ≠ keep.1.1 → v ∉ closure f := by
    intro f hf hne hvf
    have hfΓ : f ∈ Γ.E := hDΓ.2 hf
    obtain ⟨b, hb⟩ := exists_end_eq hγ hfΓ hv hvf
    let k : halfEdges Γ γ v := ⟨(f, b), hfΓ, hb⟩
    have hk : k ≠ keep := fun hk => hne (congrArg (fun j : halfEdges Γ γ v => j.1.1) hk)
    exact (hDE.subset hf).2 ⟨k, hk, rfl⟩
  have hcapD : closure keep.1.1 ∩ D.V = {u, v} := hDV.symm ▸ hcap
  have hcell := isTwoCell_delete_leaf hS hD hkept huv hcapD hLine hleaf
  have heq : deleteVertices D {v} = deleteVertices Γ {v} := by
    apply Drawing.ext_of_V_E
    · rw [deleteVertices_V, deleteVertices_V, hDV]
    · rw [deleteVertices_E, deleteVertices_E]
      ext f
      constructor
      · intro hf
        exact ⟨hDΓ.2 hf.1, hDV ▸ hf.2⟩
      · intro hf
        refine ⟨?_, hDV.symm ▸ hf.2⟩
        rw [hDE]
        refine ⟨hf.1, ?_⟩
        rintro ⟨k, _, hkf⟩
        have hvf : v ∈ closure f := hkf ▸ hhalf k
        exact disjoint_left.mp hf.2 ⟨hvf, hv⟩ rfl
  exact heq ▸ hcell

end GraphMinor.GM12
