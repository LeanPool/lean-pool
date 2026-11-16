/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Full.Closure.Basic
public import LeanPool.DeciSigma1.Semantics.Classes
import Mathlib.Basic.Finite.Prod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Regular trees from regular leaf cones

The cones of a subtree are the residual cones of the original tree, with their signs exchanged
at paths of negative polarity. Two cones determine a tree, so finitely many cone residuals give
finitely many subtrees.

## Main declarations

- `Closure.leaf_subtree`: subtree cones are residuals, with the path polarity applied.
- `Closure.regular_of_leaf`: regular leaf cones give finitely many subtrees.
-/

@[expose] public section


namespace DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Semantics.Tree

variable {n : ℕ}

/-- The two leaf cones determine a tree. -/
theorem leaf_injective (c : Fin n → Bool) :
    Function.Injective (fun t : Tree n => (leaf c t false, leaf c t true)) := by
  intro t u h
  have hp := congrArg Prod.fst h
  have hm := congrArg Prod.snd h
  apply treeLe_antisymm
  · exact (treeLe_iff_leaf c t u).mpr ⟨hp.subset, hm.symm.subset⟩
  · exact (treeLe_iff_leaf c u t).mpr ⟨hp.symm.subset, hm.subset⟩

/-- Subtree cones are residuals with signs shifted by the path polarity. -/
theorem leaf_subtree (c : Fin n → Bool) {t u : Tree n} {w : List (Fin n)}
    (h : t.subtree w = some u) (s : Bool) :
    residual (leaf c t s) w = leaf c u (Bool.xor s (polarity c w)) := by
  ext v
  induction w generalizing t s with
  | nil =>
    have hu : t = u := by
      simpa only [Characterization.subtree_nil, Option.some.injEq] using h
    subst u
    simp only [pol_nil, Bool.xor_false]
    rfl
  | cons i w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp [Tree.subtree] at h
    · simp [Tree.subtree] at h
    · have h' : (a i).subtree w = some u := h
      simpa only [residual, Set.mem_ofPred_eq, List.cons_append, leaf_node_cons,
        pol_cons, Bool.xor_assoc] using ih h' (Bool.xor s (c i))

/-- A tree with regular leaf cones has finitely many distinct subtrees. -/
theorem regular_of_leaf (c : Fin n → Bool) {t : Tree n}
    (h : ∀ s, IsRegular (leaf c t s)) : (Characterization.subtrees t).Finite := by
  let R := Set.range (residual (leaf c t false)) ∪ Set.range (residual (leaf c t true))
  have hR : R.Finite := (h false).union (h true)
  apply Set.Finite.of_finite_image (f := fun u => (leaf c u false, leaf c u true))
  · apply (hR.prod hR).subset
    rintro _ ⟨u, ⟨w, hw⟩, rfl⟩
    have hs (s : Bool) : leaf c u s ∈ R := by
      have he := leaf_subtree c hw (Bool.xor s (polarity c w))
      simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false] at he
      rw [← he]
      cases Bool.xor s (polarity c w) with
      | false => exact Or.inl ⟨w, rfl⟩
      | true => exact Or.inr ⟨w, rfl⟩
    exact ⟨hs false, hs true⟩
  · exact (leaf_injective c).injOn

end DeciSigma1.Full.Closure
