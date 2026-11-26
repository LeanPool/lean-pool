/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72PushAway
public import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.Surface.ArcTools

/-!
# A drawing of the two branches of a normal circle at a vertex

In the diversion at the boundary vertex in XII (7.2), page 260, only
the two local branches of the circle matter. Choose a short line of
the circle containing it near the vertex and missing all other vertices.
Split this line at the vertex and add the two one-edge drawings. They
meet the old drawing only at that vertex.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- The local drawing of a normal circle through a vertex, used in the
vertex case of the diversion in XII (7.2), page 260. There are just two
new edges at that vertex, and neither meets any other old vertex. -/
theorem exists_normal_circle_patch {Γ : Drawing S} {C : Set S} {v : S}
    (hC : IsOArc C) (hn : (PaintingOrDrawing.drawing Γ).IsNormal C)
    (hvC : v ∈ C) (hv : v ∈ Γ.V) :
    ∃ (H : Drawing S) (L₁ L₂ O : Set S) (a b : S),
      IsOpen O ∧ v ∈ O ∧ C ∩ O ⊆ L₁ ∪ L₂ ∧ L₁ ∪ L₂ ⊆ C ∧
      Γ.U ∩ (L₁ ∪ L₂) ⊆ {v} ∧
      IsLineWithEnds L₁ v a ∧ IsLineWithEnds L₂ v b ∧ a ≠ v ∧ b ≠ v ∧
      L₁ ∩ L₂ = {v} ∧ H.U = Γ.U ∪ (L₁ ∪ L₂) ∧
      H.V = Γ.V ∪ {a, b} ∧ H.E = Γ.E ∪ {L₁ \ {v, a}, L₂ \ {v, b}} := by
  have hVclosed : IsClosed (Γ.V \ {v}) := (Γ.finite_V.subset sdiff_subset).isClosed
  obtain ⟨L, a, b, hL, hLC, hvL, hdis, hav, hbV, O, hOo, hvO, hCO⟩ :=
    exists_small_boundary_line hC hvC hVclosed (fun h => h.2 rfl)
  have hmeet : Γ.U ∩ L ⊆ {v} := by
    rintro x ⟨hxΓ, hxL⟩
    have hxV := hn ⟨hLC hxL, hxΓ⟩
    by_contra hxv
    exact disjoint_left.mp hdis hxL ⟨hxV, hxv⟩
  obtain ⟨L₁, L₂, h₁, h₂, hLunion, hLcap⟩ := hL.split hvL hav.symm hbV.symm
  have h₁' := Surface.IsLineWithEnds.symm h₁
  let D₁ := lineDrawing h₁' hav.symm
  let D₂ := lineDrawing h₂ hbV.symm
  have hmeet₁ : Γ.U ∩ D₁.U ⊆ Γ.V ∩ D₁.V := by
    rintro x ⟨hxΓ, hxL⟩
    have hxv : x = v := mem_singleton_iff.mp (hmeet ⟨hxΓ, hLunion ▸ Or.inl hxL⟩)
    subst x
    exact ⟨hv, Or.inl rfl⟩
  let G := Γ.glue D₁ hmeet₁
  have hmeet₂ : G.U ∩ D₂.U ⊆ G.V ∩ D₂.V := by
    rintro x ⟨hxG, hxL₂⟩
    have hxv : x = v := by
      rcases hxG with hxΓ | hxL₁
      · exact mem_singleton_iff.mp (hmeet ⟨hxΓ, hLunion ▸ Or.inr hxL₂⟩)
      · exact mem_singleton_iff.mp (hLcap ▸ ⟨hxL₁, hxL₂⟩)
    subst x
    exact ⟨Or.inl hv, Or.inl rfl⟩
  let H := G.glue D₂ hmeet₂
  refine ⟨H, L₁, L₂, O, a, b, hOo, hvO, ?_, ?_, ?_, h₁', h₂, hav, hbV, hLcap, ?_, ?_, ?_⟩
  · exact hLunion.symm ▸ hCO
  · exact hLunion.symm ▸ hLC
  · exact hLunion.symm ▸ hmeet
  · change (Γ.U ∪ L₁) ∪ L₂ = Γ.U ∪ (L₁ ∪ L₂)
    exact union_assoc _ _ _
  · change (Γ.V ∪ {v, a}) ∪ {v, b} = Γ.V ∪ {a, b}
    ext x
    by_cases hx : x ∈ Γ.V
    · simp [hx]
    · have hxv : x ≠ v := fun h => hx (h.symm ▸ hv)
      simp [hx, hxv, or_comm]
  · change (G.glue D₂ hmeet₂).E = _
    rw [Drawing.glue_E]
    change (Γ.glue D₁ hmeet₁).E ∪ D₂.E = _
    rw [Drawing.glue_E, lineDrawing_E, lineDrawing_E]
    ext e
    simp only [mem_union, mem_insert_iff, mem_singleton_iff]
    tauto

end GraphMinor.GM12
