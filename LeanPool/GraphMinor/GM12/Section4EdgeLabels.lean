/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Statement
import LeanPool.GraphMinor.Minor.Basic

/-!
# An unused edge label

The paper's minor models are maps on the actual edge sets. The library
represents them as total maps on ambient edge types. For XII (4.2) we
may give the intermediate target an extra unused edge label, so its
ambient edge type is inhabited even when the graph has no edges.
This changes neither the graph nor its number of vertices up to isomorphism.
-/

public section

namespace GraphMinor.GM12

open Set Graph

/-- Relabel the actual edges by `some`, leaving `none` unused. The
resulting graph is isomorphic to the original and has the same vertices. -/
theorem exists_option_edge_copy {α β : Type*} (G : Graph α β)
    (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) :
    ∃ K : Graph α (Option β), Nonempty (Iso G K) ∧
      K.vertexSet = G.vertexSet ∧ K.vertexSet.Finite ∧ K.edgeSet.Finite := by
  let K : Graph α (Option β) := {
    vertexSet := G.vertexSet
    edgeSet := Option.some '' G.edgeSet
    IsLink := fun e x y => match e with | none => False | some f => G.IsLink f x y
    isLink_symm := by
      intro e _
      refine ⟨?_⟩
      intro x y h
      cases e with
      | none => exact h.elim
      | some e => exact h.symm
    eq_or_eq_of_isLink_of_isLink := by
      intro e x y z w h₁ h₂
      cases e with
      | none => exact h₁.elim
      | some e => exact G.eq_or_eq_of_isLink_of_isLink h₁ h₂
    edge_mem_iff_exists_isLink := by
      intro e
      cases e with
      | none => simp
      | some e => simpa using
          G.edge_mem_iff_exists_isLink e
    left_mem_of_isLink := by
      intro e x y h
      cases e with
      | none => exact h.elim
      | some e => exact h.left_mem }
  have φ : Iso G K := {
    vertexEquiv := Equiv.refl _
    edgeEquiv := Equiv.Set.image Option.some G.edgeSet (Option.some_injective β)
    isLink_iff := fun _ _ _ => Iff.rfl }
  exact ⟨K, ⟨φ⟩, rfl, hV, hE.image Option.some⟩

end GraphMinor.GM12
