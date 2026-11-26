/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CrossingPoints
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Counting the subdivided source edges

XII (4.5), page 252, has twice as many subdivided edges as
crossings. Count incidences between an original edge and one of
its meeting points. Counting first by edges gives the sum of the
meeting counts on the edges. Counting first by meeting points
gives two incidences for each point, since no third edge passes
through it away from the vertices.
-/

public section

namespace GraphMinor.GM12

open Set
open scoped BigOperators

/-- The sum of the meeting counts on the original edges is twice
the total number of meetings. Combined with one piece per meeting,
this proves the edge count in XII (4.5), page 252. -/
theorem sum_edge_meeting_counts {m n : ℕ} (V : Fin m → ℂ) (E : Fin n → Set ℂ)
    (hfinite : ∀ i j, i ≠ j → (E i ∩ E j).Finite)
    (htriple : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → E i ∩ E j ∩ E k ⊆ range V) :
    (∑ i, (E i ∩ edgeMeetingPoints V E).ncard) = 2 * (edgeMeetingPoints V E).ncard := by
  classical
  let X := edgeMeetingPoints V E
  let : Fintype X := (finite_edgeMeetingPoints V E hfinite).fintype
  let A := Σ i : Fin n, {x : X // x.val ∈ E i}
  let B := Σ x : X, {i : Fin n // x.val ∈ E i}
  let swap : A ≃ B := {
    toFun := fun a => ⟨a.2.val, ⟨a.1, a.2.property⟩⟩
    invFun := fun b => ⟨b.2.val, ⟨b.1, b.2.property⟩⟩
    left_inv := by rintro ⟨i, ⟨x, hx⟩⟩; rfl
    right_inv := by rintro ⟨x, ⟨i, hi⟩⟩; rfl }
  have hcardEdge : ∀ i, Fintype.card {x : X // x.val ∈ E i} = (E i ∩ X).ncard := by
    intro i
    let e : {x : X // x.val ∈ E i} ≃ ↥(E i ∩ X) := {
      toFun := fun x => ⟨x.val.val, ⟨x.property, x.val.property⟩⟩
      invFun := fun x => ⟨⟨x.val, x.property.2⟩, x.property.1⟩
      left_inv := by rintro ⟨⟨x, hx⟩, hi⟩; rfl
      right_inv := by rintro ⟨x, hx⟩; rfl }
    calc
      Fintype.card {x : X // x.val ∈ E i} = Nat.card {x : X // x.val ∈ E i} :=
        Nat.card_eq_fintype_card.symm
      _ = Nat.card ↥(E i ∩ X) := Nat.card_congr e
      _ = (E i ∩ X).ncard := Nat.card_coe_set_eq _
  have hcardPoint : ∀ x : X, Fintype.card {i : Fin n // x.val ∈ E i} = 2 := by
    intro x
    obtain ⟨i, j, hij, hx, hxV⟩ := x.property
    have hset : {k : Fin n | x.val ∈ E k} = {i, j} := by
      ext k
      constructor
      · intro hk
        exact edge_eq_of_mem_pair_meeting V E htriple hij ⟨hx, hxV⟩ hk
      · rintro (rfl | rfl)
        · exact hx.1
        · exact hx.2
    calc
      Fintype.card {i : Fin n // x.val ∈ E i} = ({i : Fin n | x.val ∈ E i} : Set (Fin n)).ncard :=
        fintypeCard_eq_ncard (s := {i : Fin n | x.val ∈ E i})
      _ = 2 := by rw [hset, ncard_pair hij]
  calc
    (∑ i, (E i ∩ X).ncard) = ∑ i, Fintype.card {x : X // x.val ∈ E i} :=
      Finset.sum_congr rfl fun i _ => (hcardEdge i).symm
    _ = Fintype.card A := Fintype.card_sigma.symm
    _ = Fintype.card B := Fintype.card_congr swap
    _ = ∑ x : X, Fintype.card {i : Fin n // x.val ∈ E i} := Fintype.card_sigma
    _ = ∑ _x : X, (2 : ℕ) := Finset.sum_congr rfl fun x _ => hcardPoint x
    _ = 2 * X.ncard := by simp [fintypeCard_eq_ncard, Nat.mul_comm]

end GraphMinor.GM12
