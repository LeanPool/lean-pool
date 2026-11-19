/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# The brute-force reference

`Ratpoints.bruteForce c H` lists the normalized points of height at most `H` on
`y ^ 2 = F(x, z)` by testing every candidate: first `(x, z) = (1, 0)`, the point at infinity,
then every coprime pair with `1 ≤ z ≤ H` and `-H ≤ x ≤ H`, by ascending `z` and, for each `z`, by
ascending `x`. It is the core of `verify-test4.py` of the C repository, written in the model
(Lean core, no Mathlib); `Ratpoints.mem_bruteForce_iff` and `Ratpoints.nodup_bruteForce` prove
that it lists exactly the points of the specification, each once. It models no C code, but it
evaluates the binary form as the exact check of the C code does: by Horner's rule in `x` on the
products `cₖ z^(d - k)`, computed once per `z`, with one more factor `z` when the degree `d` is
odd. For the candidate `(1, 0)` this gives `c_d` for even `d` and `0` for odd `d`, the value of
the form at the point at infinity, so that it needs no case of its own.

## Main definitions

* `Ratpoints.bruteForce`: the points by brute force, in the order described above.
-/

@[expose] public section

namespace Ratpoints

namespace BruteForce

/-- The degree of the polynomial `∑ cᵢ Xⁱ`: the largest index of a nonzero entry of `c`, or `0`
if there is none. The expression of the specification's `Ratpoints.degree`, which the model
cannot import. -/
def degree (c : List Int) : Nat := (c.reverse.dropWhile (· == 0)).length - 1

/-- The products `cₖ z^(d - k)` for `k = 0, …, d`: the coefficients of the polynomial in `x`
that the exact check of the C code evaluates for the denominator `z`. -/
def scaledCoeffs (c : List Int) (d : Nat) (z : Int) : List Int :=
  (List.range (d + 1)).map fun k ↦ c.getD k 0 * z ^ (d - k)

/-- Horner's rule: the value `w₀ + x (w₁ + x (w₂ + ⋯))` of the polynomial with coefficient
list `w`. -/
def horner (w : List Int) (x : Int) : Int := w.foldr (fun a v ↦ a + x * v) 0

/-- The triples `(x, y, z)` with `y ^ 2 = v`: `(x, y, z)` and then `(x, -y, z)` for
`y = ⌊√v⌋ > 0`, the one triple `(x, 0, z)` for `v = 0`, and none when `v` is negative or not a
square. -/
def pointsAbove (x z v : Int) : List (Int × Int × Int) :=
  let y := v.toNat.sqrt
  if 0 ≤ v ∧ y * y = v.toNat then
    if y = 0 then [(x, 0, z)] else [(x, y, z), (x, -y, z)]
  else []

/-- The points `(x, y, z)` with the denominator `z` and a numerator `x` from `xs` coprime to `z`,
for the binary form of degree `d` of `c`: the values `F(x, z)` come by Horner's rule from the
products `Ratpoints.BruteForce.scaledCoeffs c d z`, computed once, and one more factor `z` when
`d` is odd. -/
def pointsOfDen (c : List Int) (d : Nat) (z : Int) (xs : List Int) : List (Int × Int × Int) :=
  let w := scaledCoeffs c d z
  let f := if d % 2 = 1 then z else 1
  xs.flatMap fun x ↦ if Int.gcd x z = 1 then pointsAbove x z (horner w x * f) else []

/-- The numerators `-H, …, H`, in ascending order. -/
def numerators (H : Nat) : List Int := (List.range (2 * H + 1)).map fun (i : Nat) ↦ (i : Int) - H

end BruteForce

open BruteForce in
/-- The normalized points of height at most `H` on `y ^ 2 = F(x, z)`, by brute force: the
candidate `(1, 0)` if `1 ≤ H`, then the pairs `(x, z)` with `1 ≤ z ≤ H`, `-H ≤ x ≤ H` and
`gcd(x, z) = 1`, by ascending `z` and then ascending `x`; for each, `(x, y, z)` and `(x, -y, z)`
when `F(x, z) = y ^ 2` with `y > 0`, and `(x, 0, z)` when `F(x, z) = 0`. -/
def bruteForce (c : List Int) (H : Nat) : List (Int × Int × Int) :=
  let d := degree c
  let xs := numerators H
  (if 1 ≤ H then pointsOfDen c d 0 [1] else []) ++
    (List.range H).flatMap fun (j : Nat) ↦ pointsOfDen c d (j + 1 : Nat) xs

/-! ### Examples from the C program at the pin (`ratpoints c H -q`) -/

#guard bruteForce [-2, 0, 0, 1] 10 == [(1, 0, 0), (3, 5, 1), (3, -5, 1)]

#guard bruteForce [-2, 0, 0, 1] 130 ==
  [(1, 0, 0), (3, 5, 1), (3, -5, 1), (129, 3830, 100), (129, -3830, 100)]

#guard bruteForce [1, 0, 0, 0, 1] 5 == [(1, 1, 0), (1, -1, 0), (0, 1, 1), (0, -1, 1)]

#guard bruteForce [1, 2, 3, 4, 5, 6, 7] 20 ==
  [(-1, 2, 1), (-1, -2, 1), (0, 1, 1), (0, -1, 1), (8, 2401, 7), (8, -2401, 7)]

#guard bruteForce [1, 1, 1, 1, 0] 3 ==
  [(1, 0, 0), (-1, 0, 1), (0, 1, 1), (0, -1, 1), (1, 2, 1), (1, -2, 1)]

#guard bruteForce [1, 0, 126, 0, 441] 30 ==
  [(1, 21, 0), (1, -21, 0), (0, 1, 1), (0, -1, 1), (-1, 31, 2), (-1, -31, 2), (1, 31, 2),
    (1, -31, 2), (-2, 651, 21), (-2, -651, 21), (2, 651, 21), (2, -651, 21)]

-- The program reverses this polynomial and prints the points in another order.
#guard (bruteForce [-1, 0, 9] 4).isPerm [(-1, 0, 3), (1, 3, 0), (1, -3, 0), (1, 0, 3)]

#guard bruteForce [1, 0, 1] 0 == []

end Ratpoints

end
