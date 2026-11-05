/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Balanced.Basic

/-!
# Simultaneous Kempe changes

For a vertex set `X` closed under `(a, b)`-coloured edges (`KClosed`), `swapOn c a b X hX`
interchanges `a` and `b` on every edge inside `X`. This is the simultaneous Kempe change on all
the `(a, b)`-chains contained in `X`: `S(v)` becomes `i_ab S(v)` for `v ∈ X` and is unchanged
otherwise.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Balanced

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ}

/-- `X` is closed under edges coloured `a` or `b`. -/
def KClosed (c : PEC G (Fin k)) (a b : Fin k) (X : Finset V) : Prop :=
  ∀ u v, u ∈ X → (c.col u v = some a ∨ c.col u v = some b) → v ∈ X

/-- The colour function of `swapOn`. -/
def swapOnFun (c : PEC G (Fin k)) (a b : Fin k) (X : Finset V) (u v : V) : Option (Fin k) :=
  if u ∈ X ∧ v ∈ X then (c.col u v).map (Equiv.swap a b) else c.col u v

omit [DecidableRel G.Adj] [Fintype V] in
theorem swapOnFun_of_mem {c : PEC G (Fin k)} {a b : Fin k} {X : Finset V} (hX : KClosed c a b X)
    {u v : V} (hu : u ∈ X) {γ : Fin k} (h : swapOnFun c a b X u v = some γ) :
    c.col u v = some (Equiv.swap a b γ) := by
  classical
  unfold swapOnFun at h
  by_cases hv : v ∈ X
  · rw [ite_eq_left ⟨hu, hv⟩] at h
    obtain ⟨δ, hδ, e⟩ := Option.map_eq_some_iff.1 h
    rw [hδ, ← e, Equiv.swap_apply_self]
  · rw [ite_eq_right (fun h' => hv h'.2)] at h
    rw [h]
    have h1 : γ ≠ a := fun e => hv (hX u v hu (Or.inl (e ▸ h)))
    have h2 : γ ≠ b := fun e => hv (hX u v hu (Or.inr (e ▸ h)))
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

omit [DecidableRel G.Adj] [Fintype V] in
theorem swapOnFun_of_not_mem {c : PEC G (Fin k)} {a b : Fin k} {X : Finset V} {u : V}
    (hu : u ∉ X) (v : V) : swapOnFun c a b X u v = c.col u v := by
  classical
  unfold swapOnFun
  rw [ite_eq_right (fun h => hu h.1)]

/-- The simultaneous Kempe change on `X`. -/
noncomputable def swapOn (c : PEC G (Fin k)) (a b : Fin k) (X : Finset V) (hX : KClosed c a b X) :
    PEC G (Fin k) where
  col := swapOnFun c a b X
  col_symm := by
    intro u v
    unfold swapOnFun
    rw [c.col_symm u v]
    by_cases h : u ∈ X ∧ v ∈ X
    · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1⟩]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.2, h'.1⟩)]
  col_adj := by
    intro u v γ h
    by_cases hu : u ∈ X
    · exact c.col_adj (swapOnFun_of_mem hX hu h)
    · rw [swapOnFun_of_not_mem hu] at h
      exact c.col_adj h
  col_proper := by
    intro u v w γ h1 h2
    by_cases hu : u ∈ X
    · exact c.col_proper (swapOnFun_of_mem hX hu h1) (swapOnFun_of_mem hX hu h2)
    · rw [swapOnFun_of_not_mem hu] at h1 h2
      exact c.col_proper h1 h2

variable {c : PEC G (Fin k)} {a b : Fin k} {X : Finset V} (hX : KClosed c a b X)
include hX

omit [DecidableRel G.Adj] [Fintype V] in
theorem swapOn_col (u v : V) : (swapOn c a b X hX).col u v = swapOnFun c a b X u v := by
  classical
  exact rfl

omit [DecidableRel G.Adj] [Fintype V] in
theorem isFree_swapOn_of_mem [Finite V] {v : V} (hv : v ∈ X) (θ : Fin k) :
    (swapOn c a b X hX).IsFree v θ ↔ c.IsFree v (Equiv.swap a b θ) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  constructor
  · intro h u hu
    refine h u ?_
    rw [swapOn_col]
    unfold swapOnFun
    by_cases hu' : u ∈ X
    · rw [ite_eq_left ⟨hv, hu'⟩, hu]; simp
    · have h1 : Equiv.swap a b θ ≠ a := fun e => hu' (hX v u hv (Or.inl (e ▸ hu)))
      have h2 : Equiv.swap a b θ ≠ b := fun e => hu' (hX v u hv (Or.inr (e ▸ hu)))
      rw [ite_eq_right (fun h' => hu' h'.2), hu]
      have : θ = Equiv.swap a b θ := by
        have := Equiv.swap_apply_of_ne_of_ne h1 h2
        rw [Equiv.swap_apply_self] at this
        exact this
      rw [← this]
  · intro h u hu
    exact h u (by rw [swapOnFun_of_mem hX hv hu])

omit [DecidableRel G.Adj] [Fintype V] in
theorem isFree_swapOn_of_not_mem [Finite V] {v : V} (hv : v ∉ X) (θ : Fin k) :
    (swapOn c a b X hX).IsFree v θ ↔ c.IsFree v θ := by
  classical
  let : Fintype V := Fintype.ofFinite V
  constructor <;> intro h u hu
  · exact h u (by rw [swapOn_col, swapOnFun_of_not_mem hv]; exact hu)
  · exact h u (by rw [swapOn_col, swapOnFun_of_not_mem hv] at hu; exact hu)

omit [DecidableRel G.Adj] [Fintype V] in
theorem colSet_swapOn_of_mem [Finite V] {v : V} (hv : v ∈ X) :
    colSet (swapOn c a b X hX) v = swapSet a b (colSet c v) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  ext θ
  rw [mem_colSet, mem_swapSet, mem_colSet, isFree_swapOn_of_mem hX hv]

omit [DecidableRel G.Adj] [Fintype V] in
theorem colSet_swapOn_of_not_mem [Finite V] {v : V} (hv : v ∉ X) :
    colSet (swapOn c a b X hX) v = colSet c v := by
  classical
  let : Fintype V := Fintype.ofFinite V
  ext θ
  rw [mem_colSet, mem_colSet, isFree_swapOn_of_not_mem hX hv]

omit [DecidableRel G.Adj] [Fintype V] in
theorem Total.swapOn [Finite V] (h : Total c) : Total (swapOn c a b X hX) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  intro u v huv
  rw [swapOn_col]
  unfold swapOnFun
  split_ifs
  · simpa using h u v huv
  · exact h u v huv
end Balanced

end LeanPool.BalancedEdgeColourings
