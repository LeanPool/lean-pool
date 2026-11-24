/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.ConnectedTripod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases

/-!
# Branch arms for at most three attachments

The subdivision step in XVI (4.2), page 54, uses a connected branch
set with at most three attachment vertices. Pad the list of attachments
to three entries, apply the three-arm construction, and keep just the
arms for the actual attachments. Empty attachment sets are allowed.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09
universe u v

private theorem tripod_family {α : Type u} {β : Type v} {G : Graph α β}
    (hG : GraphConnected G) (a : Fin 3 → α) (ha : ∀ i, a i ∈ V(G)) :
    ∃ (m : α) (P : Fin 3 → Graph α β), m ∈ V(G) ∧
      (∀ i, IsGraphPathWithEnds G (P i) m (a i)) ∧
      ∀ i j, i ≠ j → V(P i) ∩ V(P j) = {m} := by
  obtain ⟨m, P₁, P₂, P₃, hm, hP₁, hP₂, hP₃, h12, h13, h23⟩ :=
    exists_connected_tripod hG (ha 0) (ha 1) (ha 2)
  let P : Fin 3 → Graph α β := ![P₁, P₂, P₃]
  refine ⟨m, P, hm, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hP₁
    · exact hP₂
    · exact hP₃
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try exact (hij rfl).elim
    · exact h12
    · exact h13
    · exact (Set.inter_comm _ _).trans h12
    · exact h23
    · exact (Set.inter_comm _ _).trans h13
    · exact (Set.inter_comm _ _).trans h23

/-- A family of at most three attachment occurrences has disjoint arms
from a common centre. Repeated attachment vertices are allowed. -/
theorem exists_connected_indexed_arms {α : Type u} {β : Type v} {G : Graph α β}
    (hG : GraphConnected G) {ι : Type*} [Finite ι] (hCard : Nat.card ι ≤ 3)
    (attach : ι → α) (hAttach : ∀ i, attach i ∈ V(G)) :
    ∃ (m : α) (P : ι → Graph α β), m ∈ V(G) ∧
      (∀ i, IsGraphPathWithEnds G (P i) m (attach i)) ∧
      ∀ i j, i ≠ j → V(P i) ∩ V(P j) = {m} := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨emb⟩ : Nonempty (ι ↪ Fin 3) := Function.Embedding.nonempty_of_card_le
    (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hCard)
  obtain ⟨v, hv⟩ := hG.1
  let a : Fin 3 → α := fun i => if h : ∃ x : ι, emb x = i then attach h.choose else v
  have ha : ∀ i, a i ∈ V(G) := by
    intro i
    dsimp only [a]
    split_ifs with h
    · exact hAttach h.choose
    · exact hv
  have hax (x : ι) : a (emb x) = attach x := by
    dsimp only [a]
    rw [dite_eq_left (show ∃ y : ι, emb y = emb x from ⟨x, rfl⟩)]
    exact congrArg attach (emb.injective
      (Exists.choose_spec (show ∃ y : ι, emb y = emb x from ⟨x, rfl⟩)))
  obtain ⟨m, P, hm, hPath, hInter⟩ := tripod_family hG a ha
  refine ⟨m, fun x => P (emb x), hm, ?_, ?_⟩
  · intro x
    exact hax x ▸ hPath (emb x)
  · intro x y hne
    exact hInter (emb x) (emb y) (fun h => hne (emb.injective h))

/-- A connected branch set with at most three attachment vertices has
arms from one centre to those vertices, meeting pairwise only at the
centre. This is the local construction in XVI (4.2), page 54. -/
theorem exists_connected_branch_arms {α : Type u} {β : Type v} {G : Graph α β}
    (hG : GraphConnected G) {X : Set α} (hFin : X.Finite)
    (hSub : X ⊆ V(G)) (hCard : X.ncard ≤ 3) :
    ∃ (m : α) (P : X → Graph α β), m ∈ V(G) ∧
      (∀ x : X, IsGraphPathWithEnds G (P x) m x.val) ∧
      ∀ x y : X, x ≠ y → V(P x) ∩ V(P y) = {m} := by
  let : Finite X := hFin.to_subtype
  exact exists_connected_indexed_arms hG hCard Subtype.val (fun x => hSub x.property)

end GraphMinor.GM16
