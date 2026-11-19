/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import LeanPool.Ratpoints.Spec.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

import LeanPool.Ratpoints.Proof.Tables

/-!
# The Jacobi test on denominators of points on even-degree curves
-/

@[expose] public section

open scoped NumberTheorySymbols

namespace Ratpoints.Sieve

/-- **Soundness of every form of the Jacobi test.** For a point `(a, y, b)` of a curve of even
degree, every divisor `b'` of `b` prime to the leading coefficient `c_d` has `J(c_d | b') = 1`: a
prime `q ∣ b'` divides `b`, so `c_d` is a square modulo `q`
(`Ratpoints.Sieve.isSquare_getD_degree_of_sq_eq_binaryForm`), and a Jacobi symbol `-1` would have a
prime factor `q` with `J(c_d | q) = -1` (`jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one`). -/
theorem jacobiSym_eq_one_of_sq_eq_binaryForm {c : List ℤ} {a y : ℤ} {b b' : ℕ}
    (hab : Int.gcd a b = 1) (hd : degree c % 2 = 0) (hy : y ^ 2 = binaryForm c a b)
    (hb' : b' ∣ b) (hc : Int.gcd (c.getD (degree c) 0) b' = 1) :
    J(c.getD (degree c) 0 | b') = 1 := by
  refine (jacobiSym.eq_one_or_neg_one hc).resolve_right fun h ↦ ?_
  obtain ⟨q, hq, hqb', hJ⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one h
  have : Fact q.Prime := ⟨hq⟩
  exact ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp hJ <|
    isSquare_getD_degree_of_sq_eq_binaryForm hab (Nat.mod_eq_zero_of_dvd (hqb'.trans hb')) hd hy

end Ratpoints.Sieve

end
