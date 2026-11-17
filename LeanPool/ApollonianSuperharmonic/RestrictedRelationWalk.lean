/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.List.Chain

/-!
# Finite walks from restricted relations

Adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- A restricted reflexive-transitive path yields a finite walk within its predicate. -/
theorem restrictedRelationWalk {α : Type*} (relation adjacent : α → α → Prop)
    (map_adjacent : ∀ x y, relation x y → adjacent x y)
    (vertices : α → Prop) (a b : α) (ha : vertices a)
    (h : Relation.ReflTransGen (fun x y => relation x y ∧ vertices x ∧ vertices y) a b) :
    ∃ path : List α, path.head? = some a ∧ path.getLast? = some b ∧
      (∀ x ∈ path, vertices x) ∧ ∀ x y l₁ l₂,
        path = l₁ ++ x :: y :: l₂ → adjacent x y := by
  obtain ⟨l, hc, hl⟩ := List.exists_isChain_cons_of_relationReflTransGen h
  refine ⟨a :: l, rfl, ?_, ?_, ?_⟩
  · simpa only [List.getLast?_eq_some_getLast (List.cons_ne_nil a l)] using congrArg some hl
  · have go : ∀ (u : α) (path : List α), vertices u →
        (u :: path).IsChain (fun x y => relation x y ∧ vertices x ∧ vertices y) →
        ∀ x ∈ u :: path, vertices x := by
      intro u path
      induction path generalizing u with
      | nil => simp_all
      | cons v path ih =>
        intro hu hc x hx
        simp only [List.mem_cons] at hx
        rcases hx with hx | hx
        · exact hx.symm ▸ hu
        · exact ih v hc.rel.2.2 hc.tail x (by simpa only [List.mem_cons] using hx)
    exact go a l ha hc
  · intro x y l₁ l₂ he
    exact map_adjacent x y (List.isChain_iff_forall_rel_of_append_cons_cons.mp hc he).1

end ApollonianSuperharmonic

end
