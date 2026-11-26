/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import LeanPool.GraphMinor.GM01.Defs

/-!
# The vertex map of a drawing of a simple graph

The abstract vertex set is the whole vertex type. Evaluating the
vertex equivalence gives an injective map to the points of the
drawing, whose range is exactly its vertex set. This keeps the
centre coordinates explicit when drawing a subdivision in
XVI (4.2).
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph Surface
universe u v

/-- The point assigned to an abstract simple-graph vertex by its drawing. -/
def simpleDrawingVertex {ν : Type u} {S : Type v} [TopologicalSpace S]
    {H : SimpleGraph ν} (Γ : GraphDrawing (Graph.ofSimpleGraph H) S) (v : ν) : S :=
  (Γ.iso.vertexEquiv ⟨v,mem_univ v⟩).val

/-- Distinct abstract vertices are drawn at distinct points. -/
theorem simpleDrawingVertex_injective {ν : Type u} {S : Type v} [TopologicalSpace S]
    {H : SimpleGraph ν} (Γ : GraphDrawing (Graph.ofSimpleGraph H) S) :
    Function.Injective (simpleDrawingVertex Γ) := by
  intro a b he
  exact congrArg Subtype.val (Γ.iso.vertexEquiv.injective (Subtype.ext he))

/-- The range of the vertex map is the vertex set of the drawing. -/
theorem range_simpleDrawingVertex {ν : Type u} {S : Type v} [TopologicalSpace S]
    {H : SimpleGraph ν} (Γ : GraphDrawing (Graph.ofSimpleGraph H) S) :
    range (simpleDrawingVertex Γ) = Γ.drawing.V := by
  ext x
  constructor
  · rintro ⟨v,rfl⟩
    exact (Γ.iso.vertexEquiv ⟨v,mem_univ v⟩).property
  · intro hx
    let v := Γ.iso.vertexEquiv.symm ⟨x,hx⟩
    refine ⟨v.val,?_⟩
    exact congrArg Subtype.val (Γ.iso.vertexEquiv.apply_symm_apply ⟨x,hx⟩)

end GraphMinor.GM16
