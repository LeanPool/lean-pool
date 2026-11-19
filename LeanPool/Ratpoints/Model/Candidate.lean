/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# Transporting a point between reciprocal models
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The points of a reversed search -/

/-- The point of the caller's curve for the point `(a, y, b)` of the reversed curve: `(b, y, a)` for
`a ≥ 0` and `(-b, y, -a)` for `a < 0`. After the reversal check has reversed the polynomial
(`Ratpoints.Setup.reversal`), the C code delivers the mapped points: the exact check maps each point
that it finds by this map, and the points at infinity take the candidate `(0, 1)` in place of
`(1, 0)`, which gives the image of `(1, y, 0)`; the two components deliver the mapped points when
their flag of the reversal is set (`Ratpoints.Sieve.checkPoint`,
`Ratpoints.Sieve.pointsAtInfinity`), and so does the check of the reference
(`Ratpoints.Sieve.checkNum`). It maps the normalized points of height at most `H` of the reversed
curve one to one onto those of the caller's curve (`Ratpoints.Sieve.perm_map_swapPoint_bruteForce`).
Its negations `-b` and `-a` stay in the range of a `long`, since `|a| ≤ H`, `1 ≤ b ≤ H` and
`H < 2 ^ 63` (`Ratpoints.fitsLong_neg`). -/
def swapPoint (q : Int × Int × Int) : Int × Int × Int :=
  if 0 ≤ q.1 then (q.2.2, q.2.1, q.1) else (-q.2.2, q.2.1, -q.1)

end Sieve

end Ratpoints

end
