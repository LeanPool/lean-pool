/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/


module

public import Mathlib.Combinatorics.Graph.Basic

/-!
# Complete graphs with unordered pairs as edges
-/

@[expose] public section

namespace GraphMinor

/-- The complete graph on `Fin n`, with distinct unordered pairs as edges. -/
def completeGraph (n : ℕ) : Graph (Fin n) (Sym2 (Fin n)) where
  vertexSet := Set.univ
  edgeSet := {e : Sym2 (Fin n) | ∃ x y : Fin n, x ≠ y ∧ e = s(x, y)}
  IsLink e x y := x ≠ y ∧ e = s(x, y)
  isLink_symm _ _ := ⟨fun _ _ ⟨hne, he⟩ => ⟨hne.symm, he.trans Sym2.eq_swap⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h1 h2 := by
    have heq : s(_, _) = s(_, _) := h1.2.symm.trans h2.2
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink _ := Iff.rfl
  left_mem_of_isLink _ _ _ _ := Set.mem_univ _

end GraphMinor
