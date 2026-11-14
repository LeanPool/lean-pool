/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.RandomInitialStakeFinitePairSandwich
public import LeanPool.ECRuntime.RandomInitialStakeReciprocalTelescoping
public import LeanPool.ECRuntime.RandomInitialStakeShiftedDyadicIncrement

/-!
Finite bounds on `A(m+n) - A(m)`, where `A(m) = H_(2m) - H_m`.
Reciprocal-quadratic comparison sums telescope to the two endpoints.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

namespace ECRuntime

/-- Finite increments of the dyadic harmonic tail are enclosed between
adjacent rational telescoping endpoints. -/
theorem proposed_randomInitialStake_finiteHarmonicTailEnclosure
    (m n : Nat) (hm : 1 <= m) :
    1 / (4 * (((m+1 : Nat) : Real))) -
        1 / (4 * (((m+1+n : Nat) : Real))) <=
      (harmonicReal (2*(m+n)) - harmonicReal (m+n)) -
        (harmonicReal (2*m) - harmonicReal m) ∧
    (harmonicReal (2*(m+n)) - harmonicReal (m+n)) -
        (harmonicReal (2*m) - harmonicReal m) <=
      1 / (4 * (m : Real)) - 1 / (4 * (((m+n : Nat) : Real))) := by
  have hsum := proposed_randomInitialStake_finitePairTail_sandwich m n hm
  have hinc := proposed_randomInitialStake_shiftedDyadicIncrement m n
  have hl := proposed_randomInitialStake_reciprocalTail_telescope
    (m+1) n (by omega : 0 < m+1)
  have hu := proposed_randomInitialStake_reciprocalTail_telescope m n (by omega)
  have hleftSum :
      (Finset.range n).sum (fun j =>
        1 / (4 * (((m+j : Nat) : Real)+1) * (((m+j : Nat) : Real)+2))) =
      (Finset.range n).sum (fun j =>
        1 / (4 * (((m+1+j : Nat) : Real)) * (((m+1+j+1 : Nat) : Real)))) := by
    apply Finset.sum_congr rfl
    intro j _
    have h1 : m+j+1 = m+1+j := by omega
    have h2 : m+j+2 = m+1+j+1 := by omega
    rw [show ((m+j : Nat) : Real)+1 = ((m+j+1 : Nat) : Real) by push_cast; ring,
      show ((m+j : Nat) : Real)+2 = ((m+j+2 : Nat) : Real) by push_cast; ring,
      h1, h2]
  have hrightSum :
      (Finset.range n).sum (fun j =>
        1 / (4 * (((m+j : Nat) : Real)) * (((m+j : Nat) : Real)+1))) =
      (Finset.range n).sum (fun j =>
        1 / (4 * (((m+j : Nat) : Real)) * (((m+j+1 : Nat) : Real)))) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [show ((m+j : Nat) : Real)+1 = ((m+j+1 : Nat) : Real) by push_cast; ring]
  constructor
  · calc
      1 / (4 * (((m+1 : Nat) : Real))) -
          1 / (4 * (((m+1+n : Nat) : Real))) =
        (Finset.range n).sum (fun j =>
          1 / (4 * (((m+j : Nat) : Real)+1) * (((m+j : Nat) : Real)+2))) := by
            rw [hleftSum, hl]
      _ <= (Finset.range n).sum (fun j =>
          1 / ((2 * ((m+j : Nat) : Real)+1) * (2 * ((m+j : Nat) : Real)+2))) := hsum.1
      _ = _ := hinc.symm
  · calc
      _ = (Finset.range n).sum (fun j =>
          1 / ((2 * ((m+j : Nat) : Real)+1) * (2 * ((m+j : Nat) : Real)+2))) := hinc
      _ <= (Finset.range n).sum (fun j =>
          1 / (4 * (((m+j : Nat) : Real)) * (((m+j : Nat) : Real)+1))) := hsum.2
      _ = 1 / (4 * (m : Real)) -
          1 / (4 * (((m+n : Nat) : Real))) := by rw [hrightSum, hu]

end ECRuntime
