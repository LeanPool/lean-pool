/-
Copyright (c) 2026 Chris Henson and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson, Lean Pool contributors
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Orbit

/-! # Reusing the checked columns of a group action

Many segments use the same permutation group. Certifying its bit matrix once lets every
segment reuse the columns.
-/

@[expose] public section

namespace RACert

/-- Read a natural number from little-endian words of 256 bits each. -/
def ofWords (words : List ℕ) : ℕ :=
  words.foldr (fun word rest => Nat.lor word (Nat.shiftLeft rest 256)) 0

/-- Check an orbit segment using its precomputed group-action columns. -/
noncomputable def checkSegUsingColumns (t size lo hi : ℕ) (columns : List ℕ)
    (segment : List (ℕ × ℕ)) : Bool :=
  and3 (Nat.ble hi (Nat.pow 2 t)) (Nat.ble lo hi)
    (segLoop t size (Nat.succ (Nat.log2 size))
      (Nat.sub (Nat.pow 2 size) 1) (Nat.pow 2 size) hi columns segment lo)

/-- A segment checked with the certified columns also passes the original check. -/
theorem checkSeg_of_columns {t size lo hi : ℕ} {perms : List (List ℕ × List ℕ)}
    {columns : List ℕ} {segment : List (ℕ × ℕ)} (hsize : perms.length = size)
    (hcolumns : cols t size perms = columns)
    (hsegment : checkSegUsingColumns t size lo hi columns segment = true) :
    checkSeg t perms lo hi segment = true := by
  unfold checkSeg checkSegUsingColumns at *
  rw [hsize, hcolumns]
  exact hsegment

end RACert
