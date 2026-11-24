/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Statement
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Basic

/-!
# Finite labels for the target graph

In XII (4.3), pages 249--250, enumerate the target vertices and
edges before choosing one selected free edge for each target edge.
An arbitrary finite graph is isomorphic to a graph whose vertices
and edges are all the elements of two finite initial intervals.
The isomorphism sends each index to the corresponding original
vertex or edge.
-/

public section

namespace GraphMinor.GM12

open Set

/-- Enumerating the finite vertex and edge sets gives finite labels
for the target of XII (4.3), pages 249--250. -/
theorem exists_finite_labels {α β : Type*} (G : Graph α β)
    (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) :
    ∃ (p t : ℕ) (L : Graph (Fin p) (Fin t)),
      L.vertexSet = univ ∧ L.edgeSet = univ ∧ Nonempty (Iso L G) := by
  classical
  let : Fintype G.vertexSet := hV.fintype
  let : Fintype G.edgeSet := hE.fintype
  let p := Fintype.card G.vertexSet
  let t := Fintype.card G.edgeSet
  let ν : Fin p ≃ G.vertexSet := (Fintype.equivFin G.vertexSet).symm
  let ε : Fin t ≃ G.edgeSet := (Fintype.equivFin G.edgeSet).symm
  let L : Graph (Fin p) (Fin t) := {
    vertexSet := univ
    edgeSet := univ
    IsLink := fun e x y => G.IsLink (ε e).val (ν x).val (ν y).val
    isLink_symm := by intro e he; exact ⟨fun _ _ h => h.symm⟩
    eq_or_eq_of_isLink_of_isLink := by
      intro e x y v w hxy hvw
      rcases G.eq_or_eq_of_isLink_of_isLink hxy hvw with h | h
      · exact Or.inl (ν.injective (Subtype.ext h))
      · exact Or.inr (ν.injective (Subtype.ext h))
    edge_mem_iff_exists_isLink := by
      intro e
      constructor
      · intro _
        obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet (ε e).property
        refine ⟨ν.symm ⟨x, hxy.left_mem⟩, ν.symm ⟨y, hxy.right_mem⟩, ?_⟩
        simpa only [ν.apply_symm_apply] using hxy
      · exact fun _ => mem_univ _
    left_mem_of_isLink := by intro e x y h; exact mem_univ x }
  let φ : Iso L G := {
    vertexEquiv := (Equiv.Set.univ (Fin p)).trans ν
    edgeEquiv := (Equiv.Set.univ (Fin t)).trans ε
    isLink_iff := fun _ _ _ => Iff.rfl }
  exact ⟨p, t, L, rfl, rfl, ⟨φ⟩⟩

end GraphMinor.GM12
