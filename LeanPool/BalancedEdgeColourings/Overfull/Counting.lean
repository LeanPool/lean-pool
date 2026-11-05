/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Vizing.Kempe
public import Mathlib.Data.ZMod.Basic

/-!
# Parity of vertices incident with a fixed edge colour

The edges of a proper colouring pair the vertices incident with each colour.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC Finset


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

open Classical in
omit [DecidableEq V] in
/-- For each colour, the vertices on an edge of that colour come in pairs. -/
theorem even_card_not_free {k : ℕ} (c : PEC G (Fin k)) (θ : Fin k) :
    Even #(univ.filter fun v => ¬ c.IsFree v θ) := by
  classical
  set S := univ.filter fun v => ¬ c.IsFree v θ with hS
  have hex : ∀ v ∈ S, ∃ w, c.col v w = some θ := by
    intro v hv
    simp only [hS, mem_filter, mem_univ, true_and, IsFree, not_forall, not_not] at hv
    exact hv
  choose g hg using hex
  have hmem : ∀ v hv, g v hv ∈ S := by
    intro v hv
    simp only [hS, mem_filter, mem_univ, true_and, IsFree, not_forall, not_not]
    exact ⟨v, by rw [c.col_symm]; exact hg v hv⟩
  have key : ∑ v ∈ S, (1 : ZMod 2) = 0 := by
    refine sum_involution g (fun _ _ => rfl) (fun v hv _ he => ?_) hmem (fun v hv => ?_)
    · have := hg v hv
      rw [he, c.col_self] at this
      cases this
    · have h1 := hg (g v hv) (hmem v hv)
      have h2 : c.col (g v hv) v = some θ := by rw [c.col_symm]; exact hg v hv
      exact c.col_proper h1 h2
  rw [sum_const, nsmul_eq_mul, mul_one] at key
  exact (ZMod.natCast_eq_zero_iff_even).1 key

end Overfull

end LeanPool.BalancedEdgeColourings
