/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.Rotation

/-!
# Compatibility of path drawing maps

Shared source vertices are centres, whose maps agree by the fixed
centre coordinates. Shared target vertices are also centre points.
The inverse map sends each such point to its source centre, so
the inverse maps agree as well. Drawing edges in different pieces
are disjoint because their supports meet only at common vertices.
These facts verify the gluing conditions for XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface GM11
universe u v w t z

/-- Centre compatibility gives compatibility of both the forward
and inverse vertex maps of a family of path drawings. -/
theorem drawing_family_vertex_maps_compatible
    {α : Type u} {β : Type v} {ν : Type w} {S : Type t} {ι : Type z}
    [TopologicalSpace S] (P : ι → Graph α β) (D : ∀ i, GraphDrawing (P i) S)
    (c : ν → α) (p : ν → S)
    (hSource : ∀ i j, i ≠ j → V(P i) ∩ V(P j) ⊆ range c)
    (hTarget : ∀ i j, i ≠ j → (D i).drawing.U ∩ (D j).drawing.U ⊆ range p)
    (hPointSource : ∀ i v, p v ∈ (D i).drawing.U → c v ∈ V(P i))
    (hCentre : ∀ i v (x : V(P i)), x.val = c v → ((D i).iso.vertexEquiv x).val = p v) :
    (∀ i j x (hi : x ∈ V(P i)) (hj : x ∈ V(P j)),
      ((D i).iso.vertexEquiv ⟨x,hi⟩).val = ((D j).iso.vertexEquiv ⟨x,hj⟩).val) ∧
    (∀ i j y (hi : y ∈ (D i).drawing.V) (hj : y ∈ (D j).drawing.V),
      ((D i).iso.vertexEquiv.symm ⟨y,hi⟩).val = ((D j).iso.vertexEquiv.symm ⟨y,hj⟩).val) := by
  have hInv (i : ι) (v : ν) (hy : p v ∈ (D i).drawing.V) :
      ((D i).iso.vertexEquiv.symm ⟨p v,hy⟩).val = c v := by
    have hv := hPointSource i v ((D i).drawing.V_subset_U hy)
    have he : (D i).iso.vertexEquiv ⟨c v,hv⟩ = ⟨p v,hy⟩ :=
      Subtype.ext (hCentre i v ⟨c v,hv⟩ rfl)
    have h := congrArg (D i).iso.vertexEquiv.symm he
    rw [Equiv.symm_apply_apply] at h
    exact (congrArg Subtype.val h).symm
  constructor
  · intro i j x hi hj
    by_cases hij : i=j
    · subst j
      rfl
    obtain ⟨v,hv⟩ := hSource i j hij ⟨hi,hj⟩
    exact (hCentre i v ⟨x,hi⟩ hv.symm).trans (hCentre j v ⟨x,hj⟩ hv.symm).symm
  · intro i j y hi hj
    by_cases hij : i=j
    · subst j
      rfl
    obtain ⟨v,rfl⟩ := hTarget i j hij ⟨(D i).drawing.V_subset_U hi,(D j).drawing.V_subset_U hj⟩
    exact (hInv i v hi).trans (hInv j v hj).symm

/-- Distinct drawings in a family meeting only at prescribed common
vertices have disjoint edge sets. -/
theorem drawing_family_edges_disjoint {S : Type u} [TopologicalSpace S]
    {ι : Type v} (D : ι → Drawing S) (Z : Set S)
    (hZ : ∀ i, (D i).U ∩ Z ⊆ (D i).V)
    (hMeet : ∀ i j, i ≠ j → (D i).U ∩ (D j).U ⊆ Z)
    {i j : ι} (hij : i ≠ j) : Disjoint (D i).E (D j).E := by
  apply disjoint_left.mpr
  intro e he hf
  obtain ⟨x,hx⟩ := he.1
  have hxi := he.2.1 hx
  have hxj := hf.2.1 hx
  exact hxi.2 (hZ i ⟨hxi.1,hMeet i j hij ⟨hxi.1,hxj.1⟩⟩)

end GraphMinor.GM16
