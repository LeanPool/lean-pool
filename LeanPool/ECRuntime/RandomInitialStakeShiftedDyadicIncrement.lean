/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.FitnessLevel
public import LeanPool.ECRuntime.RandomInitialStakePairTailBounds

/-!
Finite harmonic differences expressed as shifted dyadic reciprocal-pair
sums. This is an exact telescoping identity, independent of any limit.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- One step of the dyadic harmonic difference is a positive pair. -/
private theorem stage197_dyadic_step (r : Nat) :
    (harmonicReal (2 * (r + 1)) - harmonicReal (r + 1)) -
       (harmonicReal (2 * r) - harmonicReal r) =
      1 / ((2 * (r : Real) + 1) * (2 * (r : Real) + 2)) := by
  have hsuccM : harmonicReal (r + 1) =
      harmonicReal r + ((r + 1 : Nat) : Real)⁻¹ := by
    simp [harmonicReal, harmonic_succ]
  have hsucc2M : harmonicReal (2 * r + 1) =
      harmonicReal (2 * r) + ((2 * r + 1 : Nat) : Real)⁻¹ := by
    simp [harmonicReal, harmonic_succ]
  have hsucc2M' : harmonicReal (2 * r + 2) =
      harmonicReal (2 * r + 1) + ((2 * r + 2 : Nat) : Real)⁻¹ := by
    have hidx : 2 * r + 2 = (2 * r + 1) + 1 := by omega
    rw [hidx]
    simp [harmonicReal, harmonic_succ]
  have htwo : ((2 * r + 2 : Nat) : Real) =
      2 * ((r + 1 : Nat) : Real) := by
    push_cast
    ring
  have hinv : ((r + 1 : Nat) : Real)⁻¹ =
      2 * (((2 * r + 2 : Nat) : Real)⁻¹) := by
    have hr : ((r + 1 : Nat) : Real) ≠ 0 := by positivity
    rw [htwo]
    field_simp
  have hidx : 2 * (r + 1) = (2 * r + 2 : Nat) := by omega
  have hdifference :
      (harmonicReal (2 * (r + 1)) - harmonicReal (r + 1)) -
        (harmonicReal (2 * r) - harmonicReal r) =
        (((2 * r + 1 : Nat) : Real)⁻¹ -
          ((2 * r + 2 : Nat) : Real)⁻¹) := by
    rw [hidx, hsuccM, hsucc2M', hsucc2M, hinv]
    ring
  rw [hdifference]
  exact stage191_dyadicPair_eq_reciprocal r

/-- Increasing the dyadic index from `m` to `m+n` adds exactly `n`
shifted dyadic reciprocal pairs. -/
theorem proposed_randomInitialStake_shiftedDyadicIncrement
    (m n : Nat) :
    (harmonicReal (2 * (m + n)) - harmonicReal (m + n)) -
        (harmonicReal (2 * m) - harmonicReal m) =
      (Finset.range n).sum (fun j =>
        1 / ((2 * ((m + j : Nat) : Real) + 1) *
          (2 * ((m + j : Nat) : Real) + 2))) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hstep := stage197_dyadic_step (m + n)
      have hidx : m + (n + 1) = (m + n) + 1 := by omega
      rw [hidx]
      rw [← ih]
      linarith

end ECRuntime
