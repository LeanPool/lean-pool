/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.CotreeCompleteness

/-!
# Regression examples for structural graph classes

The four-vertex path is split but not threshold. This prevents the nested-
neighborhood property from accidentally becoming an assumption of split membership.
-/

@[expose] public section

namespace SimpleGraph.StructuralGraphClasses

/-- The path with vertices `0, 1, 2, 3` in their natural order. -/
def pathFour : SimpleGraph (Fin 4) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm.symm _ _ h := h.symm
  loopless.irrefl i := by omega

/-- The middle vertices are a clique and the endpoints form an independent set. -/
def pathFourSplitPartition : pathFour.SplitPartition where
  clique := {v | v.val = 1 ∨ v.val = 2}
  independent := {v | v.val = 0 ∨ v.val = 3}
  isClique := by
    intro u hu v hv hne
    have hne' : u.val ≠ v.val := fun he => hne (Fin.ext he)
    simp only [Set.mem_ofPred_eq] at hu hv
    change u.val + 1 = v.val ∨ v.val + 1 = u.val
    omega
  isIndepSet := by
    intro u hu v hv hne
    simp only [Set.mem_ofPred_eq] at hu hv
    change ¬(u.val + 1 = v.val ∨ v.val + 1 = u.val)
    omega
  disjoint := by
    apply Set.disjoint_left.mpr
    intro v hv hi
    simp only [Set.mem_ofPred_eq] at hv hi
    omega
  cover := by
    ext v
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have := v.isLt
    omega

/-- `P₄` belongs to the split class. -/
theorem pathFour_isSplit : pathFour.IsSplit := ⟨pathFourSplitPartition⟩

/-- The four vertices themselves witness failure of `P₄` exclusion. -/
theorem pathFour_not_isP4Free : ¬pathFour.IsP4Free := by
  intro h
  exact h 0 1 2 3 (by simp [pathFour]) (by simp [pathFour]) (by simp [pathFour])
    (by simp [pathFour]) (by simp [pathFour]) (by simp [pathFour])

/-- A split graph need not be threshold. -/
theorem pathFour_not_isThreshold : ¬pathFour.IsThreshold := by
  intro h
  exact pathFour_not_isP4Free (isThreshold_iff_isSplit_and_isP4Free.mp h).2

/-- The split partition of `P₄` does not have nested independent neighborhoods. -/
theorem pathFour_not_hasNestedNeighborhoods :
    ¬pathFourSplitPartition.HasNestedNeighborhoods := by
  intro h
  exact pathFour_not_isP4Free (pathFourSplitPartition.isP4Free_of_hasNestedNeighborhoods h)

/-- The four-vertex path cannot have a cotree representation. -/
theorem pathFour_not_nonempty_cotreeRepresentation :
    ¬Nonempty (CotreeRepresentation pathFour) := by
  rintro ⟨R⟩
  exact pathFour_not_isP4Free R.isCograph

/-- The empty graph on an empty vertex type is covered by completeness. -/
theorem empty_has_cotreeRepresentation :
    Nonempty (CotreeRepresentation (⊥ : SimpleGraph (Fin 0))) :=
  isCograph_bot.nonempty_cotreeRepresentation

/-- Complete finite graphs, including the empty one, have cotrees. -/
theorem complete_has_cotreeRepresentation (n : ℕ) :
    Nonempty (CotreeRepresentation (⊤ : SimpleGraph (Fin n))) :=
  isCograph_top.nonempty_cotreeRepresentation

end SimpleGraph.StructuralGraphClasses
