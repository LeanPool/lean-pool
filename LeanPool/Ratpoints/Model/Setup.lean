/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# Polynomial reversal for bounded-height search
-/

@[expose] public section

namespace Ratpoints

/-- Polynomial reversal can fail when the binary form has a repeated factor. -/
inductive Refusal where
  /-- The leading coefficients of the reversed form vanish. -/
  | notSquarefree
  deriving DecidableEq, Repr

namespace Setup

/-- Whether `a` is a square, as `mpz_perfect_square_p` of GMP decides it: `0` and the squares of
the positive integers, so that no negative integer is a square. -/
def isSquare (a : Int) : Bool := 0 ≤ a && a.toNat.sqrt * a.toNat.sqrt == a.toNat

/-- The reversal check on the coefficients `c` of degree `d`, the leading zeros dropped, with the
switch `allow` of the reversal: the list that the search goes on with, its degree, and whether it is
reversed. If the switch is off, `c` itself. Otherwise, for even `d` with `c₀ = 0`, the refusal
`Ratpoints.Refusal.notSquarefree` if also `c₁ = 0`, since `X ^ 2` then divides the binary form, and
else the list `c_d, …, c₁, c₀` with the degree `d - 1` (case 1); for even `d` with `c_d` a square
and `c₀` not (`Ratpoints.Setup.isSquare`), the list `c_d, …, c₀` (case 2); for odd `d` with
`|c_d| ≠ 1`, `c₀ = 0` and `|c₁| = 1`, the list `c₀, c_d, …, c₁` (case 3); and otherwise `c` itself.
In each case the reversed list is the reflection of `c` in the even degree `d + d % 2` of the binary
form, so that its binary form is that of `c` with `x` and `z` exchanged
(`Ratpoints.Setup.binaryForm_eq_of_reversal_eq_ok`).

C: `find_points.c:4732-4739`, `find_points.c:4744-4756`, `find_points.c:4759-4770`,
`find_points.c:4775-4790`, `find_points.c:4802-4803`

Deviation: a new list for the reversal in place, and nothing written back to the caller: the
reversed coefficients, the degree and the flag `RATPOINTS_REVERSED` are returned instead; the
switch for the test of the flags `RATPOINTS_NO_REVERSE` and `RATPOINTS_NO_REVERSE_AUTO`, which is
on when neither is set, as the normalized options give it (`Ratpoints.Options.normalize`: off for a
search region or a range of the denominators); the square test of `c_d` made here, where the C code
reads the flag `lcfsq` that the set-up computes before (line 4634), and no flag `lcfsq` for the
reversed list, which case 2 clears, since `Ratpoints.Sieve.pointsAtInfinity` tests the leading
coefficient of the list it is given; integers and their absolute values for the GMP integers, with
no scratch integers `work[0]` and `work[1]`; the report under `RATPOINTS_VERBOSE` printed by the
caller from the result (`Ratpoints.Report.reversal`). -/
def reversal (allow : Bool) (c : List Int) (d : Nat) : Except Refusal (List Int × Nat × Bool) :=
  if !allow then .ok (c, d, false)
  else if d % 2 = 0 then
    if c.getD 0 0 = 0 then
      if c.getD 1 0 = 0 then .error .notSquarefree
      else .ok ((c.take (d + 1)).reverse, d - 1, true)
    else if isSquare (c.getD d 0) && !isSquare (c.getD 0 0) then
      .ok ((c.take (d + 1)).reverse, d, true)
    else .ok (c, d, false)
  else if (c.getD d 0).natAbs ≠ 1 ∧ c.getD 0 0 = 0 ∧ (c.getD 1 0).natAbs = 1 then
    .ok (c.getD 0 0 :: ((c.take (d + 1)).drop 1).reverse, d, true)
  else .ok (c, d, false)

end Setup

end Ratpoints

end
