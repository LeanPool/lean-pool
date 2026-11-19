/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.List.Chain

/-!
# A chain of intervals that is pairwise apart

A candidate for `Mathlib.Data.List.Chain`: a chain of intervals `[l, u]` with `l ≤ u`, each ending
below the start of the next, is pairwise so.

## Main statements

* `List.pairwise_of_isChain_of_le`: a chain of intervals, each ending below the start of the next,
  is pairwise so.
-/

@[expose] public section

namespace List

/-- A chain of intervals `[l, u]` with `l ≤ u`, each ending below the start of the next, is pairwise
so: the relation is transitive on such intervals. -/
theorem pairwise_of_isChain_of_le {α : Type*} [Preorder α] {l : List (α × α)}
    (h1 : ∀ i ∈ l, i.1 ≤ i.2) (h2 : l.IsChain fun i j ↦ i.2 < j.1) :
    l.Pairwise fun i j ↦ i.2 < j.1 := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    rcases l with _ | ⟨b, l⟩
    · exact pairwise_singleton _ _
    · rw [isChain_cons_cons] at h2
      have ih' := ih (fun i hi ↦ h1 i (mem_cons_of_mem _ hi)) h2.2
      refine .cons (fun x hx ↦ ?_) ih'
      rcases mem_cons.mp hx with rfl | hx
      · exact h2.1
      · exact h2.1.trans_le ((h1 b (by simp)).trans (rel_of_pairwise_cons ih' hx).le)

end List

end
