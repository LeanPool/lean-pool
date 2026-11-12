/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Aesop
public import Mathlib.Algebra.Group.Fin.Basic


-- [TABLET NODE: P4431T1OwnerTransitionSelector]

/-!
# P4431T1OwnerTransitionSelector

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4431T1OwnerTransitionSelector {α : Type*}
    (o : Fin 4 → α) (s : Fin 4 → Bool)
    (hleft : ∀ i k, s i ≠ s (i + 1) → o k = o i → s k = s i)
    (hright : ∀ i k, s i ≠ s (i + 1) →
      o k = o (i + 1) → s k = s (i + 1))
    (hrepeat : o 0 = o 1 ∨ o 0 = o 2 ∨ o 0 = o 3 ∨
      o 1 = o 2 ∨ o 1 = o 3 ∨ o 2 = o 3)
    (hchecker : ¬ ((o 0 = o 2 ∧ o 1 ≠ o 0 ∧ o 3 ≠ o 0) ∨
      (o 1 = o 3 ∧ o 0 ≠ o 1 ∧ o 2 ≠ o 1)))
    (hopposite : s 0 ≠ s 2 ∨ s 1 ≠ s 3) :
    ∃ i, s i ≠ s (i + 1) ∧
      (o i = o (i + 3) ∨ o (i + 1) = o (i + 2)) := by
-- BODY
  classical
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [Fin.forall_fin_succ, h0, h1, h2, h3] at hleft hright hopposite
  all_goals simp [Fin.exists_fin_succ, h0, h1, h2, h3]
  all_goals aesop

end ApollonianSuperharmonic

end
