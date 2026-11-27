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

/-- A segment checked with the certified columns also passes the original check. -/
theorem checkSeg_of_columns {t size lo hi : ℕ} {perms : List (List ℕ × List ℕ)}
    {columns : List ℕ} {segment : List (ℕ × ℕ)} (hsize : perms.length = size)
    (hcolumns : cols t size perms = columns)
    (hsegment : checkSegUsingColumns t size lo hi columns segment = true) :
    checkSeg t perms lo hi segment = true := by
  unfold checkSeg
  rw [hsize, hcolumns]
  exact hsegment

end RACert
