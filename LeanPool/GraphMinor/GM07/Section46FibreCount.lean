/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Counting points joined by finitely many identifications

For the fibre count on page 225 of VII (4.6), each pasted endpoint joins two
points of the net disc. A connected set joined by `m` such pairs has at most
`m + 1` points. We prove this count using the connected graph of the pairs.
-/

public section

namespace GraphMinor.GM07

open Set

/-- A connected family of endpoint identifications joins at most one more
point than its number of pairs. This is the finite graph count used for
fibres of the net surjection in VII (4.6), page 225. -/
theorem card_le_pairs_add_one {α ι : Type*} [Nonempty α] [Finite ι]
    (f g : ι → α)
    (hconn : ∀ x y : α, Relation.EqvGen
      (fun x y => ∃ i, x = f i ∧ y = g i) x y) :
    Nat.card α ≤ Nat.card ι + 1 := by
  classical
  let E : Set (Sym2 α) := range (fun i => s(f i, g i))
  let G := SimpleGraph.fromEdgeSet E
  have hreach : ∀ x y, Relation.EqvGen
      (fun x y => ∃ i, x = f i ∧ y = g i) x y → G.Reachable x y := by
    intro x y h
    induction h with
    | rel x y h =>
      obtain ⟨i, rfl, rfl⟩ := h
      by_cases he : f i = g i
      · rw [he]
      · exact SimpleGraph.Adj.reachable (show G.Adj (f i) (g i) from ⟨⟨i, rfl⟩, he⟩)
    | refl x => exact SimpleGraph.Reachable.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hG : G.Connected := { preconnected := fun x y => hreach x y (hconn x y) }
  have hE : E.Finite := finite_range _
  have hsub : G.edgeSet ⊆ E := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact sdiff_subset
  have hcard : Nat.card G.edgeSet ≤ Nat.card ι := by
    rw [Nat.card_coe_set_eq]
    exact (ncard_le_ncard hsub hE).trans (by
      rw [show E = (fun i => s(f i, g i)) '' univ from (image_univ).symm]
      exact (ncard_image_le (finite_univ)).trans_eq (ncard_univ ι))
  exact hG.card_vert_le_card_edgeSet_add_one.trans (Nat.add_le_add_right hcard 1)

end GraphMinor.GM07
