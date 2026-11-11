/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.RandomInitialStakePairTailBounds
public import Mathlib.Basic.Real.Basic

/-!
Summed dyadic reciprocal-pair comparisons over arbitrary finite shifted
tails. These finite bounds precede the separate identification of the
infinite harmonic-tail limit with `log 2`.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- The finite tail of dyadic reciprocal pairs lies between the two
shifted telescoping rational sums. -/
theorem proposed_randomInitialStake_finitePairTail_sandwich
    (m n : Nat) (hm : 1 ≤ m) :
    (Finset.range n).sum (fun j =>
      1 / (4 * (((m + j : Nat) : Real) + 1) *
        (((m + j : Nat) : Real) + 2))) ≤
      (Finset.range n).sum (fun j =>
        1 / ((2 * ((m + j : Nat) : Real) + 1) *
          (2 * ((m + j : Nat) : Real) + 2))) ∧
    (Finset.range n).sum (fun j =>
        1 / ((2 * ((m + j : Nat) : Real) + 1) *
          (2 * ((m + j : Nat) : Real) + 2))) ≤
      (Finset.range n).sum (fun j =>
        1 / (4 * ((m + j : Nat) : Real) *
          (((m + j : Nat) : Real) + 1))) := by
  constructor
  · apply Finset.sum_le_sum
    intro j hj
    have hidx : 1 ≤ m + j := by omega
    exact (proposed_randomInitialStake_pairReciprocalBounds (m + j) hidx).1
  · apply Finset.sum_le_sum
    intro j hj
    have hidx : 1 ≤ m + j := by omega
    exact (proposed_randomInitialStake_pairReciprocalBounds (m + j) hidx).2

end ECRuntime
