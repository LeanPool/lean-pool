/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StagePrepared

/-!
# Indices of the finite protected strategy list

The executable header lists exactly strategies `0, ..., n`. These lemmas
identify its list indices and finite sums with the corresponding stage indices.
-/

@[expose] public section

namespace Klr.StagePrepared

open scoped BigOperators

theorem get_protectedRules (s : ℕ → BettingStrategy) (n : ℕ)
    (i : Fin (protectedRules s n).length) :
    (protectedRules s n).get i = s i.val := by
  exact List.get_ofFn (fun j : Fin (n + 1) => s j.val) i

@[simp] theorem sum_protectedRules {α : Type*} [AddCommMonoid α]
    (s : ℕ → BettingStrategy) (n : ℕ) (f : ℕ → α) :
    (∑ i : Fin (protectedRules s n).length, f i.val) =
      ∑ i : Fin (n + 1), f i.val := by
  rw [length_protectedRules]

end Klr.StagePrepared
