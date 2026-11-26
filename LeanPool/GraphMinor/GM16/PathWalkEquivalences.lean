/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.PathWalkCoordinates
import LeanPool.GraphMinor.GM11.Forest
import LeanPool.GraphMinor.GM11.Walks

/-!
# Enumerating a path's vertices and edges by finite intervals

A simple walk lists each vertex and edge of its path exactly once.
The position maps therefore give equivalences with finite integer
intervals. The specifications retain the order along the path,
which fixes the two ends when matching it to a line drawing in
XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Surface GM11
universe u v
variable {α : Type u} {β : Type v} {P : Graph α β}

/-- The vertex positions of a spanning simple walk enumerate the path vertices. -/
theorem exists_pathWalk_vertexEquiv {a b : α} (W : GraphWalk P a b) (hW : W.IsSimple)
    (hV : V(P) = {x | x ∈ W.support}) :
    ∃ φ : Fin (W.length+1) ≃ V(P), ∀ i,
      (φ i).val = pathWalkVertex W i.val (by omega) := by
  let f : Fin (W.length+1) → V(P) := fun i =>
    ⟨pathWalkVertex W i.val (by omega),(congrArg (fun A : Set α => pathWalkVertex W i.val
      (by omega) ∈ A) hV).mpr
      (pathWalkVertex_mem_support W i.val (by omega))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j he
      apply Fin.ext
      exact pathWalkVertex_injective hW (by omega) (by omega) (congrArg Subtype.val he)
    · intro x
      have hx : x.val ∈ W.support := (congrArg (fun A : Set α => x.val ∈ A) hV).mp x.property
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
      have hi' : i < W.length+1 := length_support W ▸ hi
      exact ⟨⟨i,hi'⟩,Subtype.ext he⟩
  exact ⟨Equiv.ofBijective f hf,fun _ => rfl⟩

/-- The edge positions of a spanning simple walk enumerate the path edges. -/
theorem exists_pathWalk_edgeEquiv {a b : α} (W : GraphWalk P a b) (hW : W.IsSimple)
    (hE : E(P) = {e | e ∈ W.edges}) :
    ∃ φ : Fin W.length ≃ E(P), ∀ i,
      (φ i).val = pathWalkEdge W i.val i.isLt := by
  let f : Fin W.length → E(P) := fun i =>
    ⟨pathWalkEdge W i.val i.isLt,(congrArg (fun A : Set β => pathWalkEdge W i.val i.isLt ∈ A)
      hE).mpr
      (pathWalkEdge_mem_edges W i.val i.isLt)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j he
      apply Fin.ext
      exact pathWalkEdge_injective hW i.isLt j.isLt (congrArg Subtype.val he)
    · intro x
      have hx : x.val ∈ W.edges := (congrArg (fun A : Set β => x.val ∈ A) hE).mp x.property
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
      exact ⟨⟨i,hi⟩,Subtype.ext he⟩
  exact ⟨Equiv.ofBijective f hf,fun _ => rfl⟩

end GraphMinor.GM16
