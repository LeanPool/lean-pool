/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Finite sums of compact operators

`IsCompactOperator` is closed under addition (`IsCompactOperator.add`) and contains `0`, so a
finite sum of compact continuous linear maps is compact.  Mathlib states the two-term case; the
`Finset` case is the shape the compactness argument for the paper's velocity part `K_w` of the
form operator in §2.3 consumes: `K_w` is shown compact term by term, the terms being indexed by
the two horizontal coordinates.
-/

@[expose] public section

namespace FastDynamo

/-- A finite sum of compact continuous linear maps is compact. -/
theorem isCompactOperator_finsetSum {iota : Type*} {M N : Type*}
    [AddCommGroup M] [TopologicalSpace M] [Module ℂ M]
    [AddCommGroup N] [TopologicalSpace N] [Module ℂ N] [ContinuousAdd N]
    (t : Finset iota) (F : iota → M →L[ℂ] N)
    (h : ∀ i, IsCompactOperator (F i)) :
    IsCompactOperator (⇑(∑ i ∈ t, F i)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : M → N))
  | insert i u hi ih =>
      rw [Finset.sum_insert hi]
      simpa using (h i).add ih

end FastDynamo
