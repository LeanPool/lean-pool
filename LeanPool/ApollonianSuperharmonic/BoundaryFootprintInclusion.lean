/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import Mathlib.Init


/-!
# BoundaryFootprintInclusion

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BoundaryFootprintInclusion

/-- Shared boundaryEdge identity for BoundaryFootprintInclusion. -/
theorem boundaryEdge :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges U) → (e ∈
            FootprintEdges U) ) := by
  classical
  intro U e he
  let I : GaussianInt := ⟨0, 1⟩
  rcases he with ⟨z, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
  · rcases h with ⟨hz, -⟩ | ⟨-, hz⟩
    · exact ⟨z, hz, Or.inl rfl⟩
    · refine ⟨z - I, hz, Or.inr (Or.inr (Or.inr ?_))⟩
      congr 1 <;> simp [I, Zsqrtd.ext_iff]
  · rcases h with ⟨hz, -⟩ | ⟨-, hz⟩
    · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
    · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
      congr 1 <;> simp []

/-- Shared edgeVertex identity for BoundaryFootprintInclusion. -/
theorem edgeVertex :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges X) → (∀ (z :
            GaussianInt), (z ∈ e) → (z ∈ FootprintVertices X)) ) := by
  classical
  intro X e he z hz
  rcases he with ⟨c, hc, he⟩
  unfold FootprintVertices
  rw [ite_eq_left ⟨c, hc⟩]
  rcases he with h | h | h | h <;> subst e
  all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  · rcases hz with rfl | rfl
    · exact ⟨_, hc, Or.inl rfl⟩
    · exact ⟨_, hc, Or.inr (Or.inl rfl)⟩
  · rcases hz with rfl | rfl
    · exact ⟨_, hc, Or.inl rfl⟩
    · exact ⟨_, hc, Or.inr (Or.inr (Or.inl rfl))⟩
  · rcases hz with rfl | rfl
    · exact ⟨_, hc, Or.inr (Or.inl rfl)⟩
    · exact ⟨_, hc, Or.inr (Or.inr (Or.inr rfl))⟩
  · rcases hz with rfl | rfl
    · exact ⟨_, hc, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨_, hc, Or.inr (Or.inr (Or.inr rfl))⟩

/-- Shared boundaryVertex identity for BoundaryFootprintInclusion. -/
theorem boundaryVertex :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges X) → (e ∈
            FootprintEdges X)) → ((∀ (X : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈
            FootprintEdges X) → (∀ (z : GaussianInt), (z ∈ e) → (z ∈ FootprintVertices X))) → (∀
            (X : ProtoTile), ∀ (x : GaussianInt), (x ∈ BoundaryFootprintVertices X) → (x ∈
            FootprintVertices X))) ) := by
  classical
  intro boundary_edge_footprint edge_vertex_footprint X x hx
  by_cases hne : X.cells.Nonempty
  · unfold BoundaryFootprintVertices at hx
    rw [ite_eq_left hne] at hx
    rcases hx with ⟨e, he, hxe⟩
    exact edge_vertex_footprint X e (boundary_edge_footprint X e he) x hxe
  · unfold BoundaryFootprintVertices at hx
    rw [ite_eq_right hne] at hx
    subst x
    simp [FootprintVertices, hne]

/-- Every boundary footprint vertex is a footprint vertex, including empty tiles. -/
theorem boundaryVertex_mem (T : ProtoTile) (x : GaussianInt)
    (hx : x ∈ BoundaryFootprintVertices T) : x ∈ FootprintVertices T :=
  boundaryVertex boundaryEdge edgeVertex T x hx

end BoundaryFootprintInclusion
end ApollonianSuperharmonic

end
