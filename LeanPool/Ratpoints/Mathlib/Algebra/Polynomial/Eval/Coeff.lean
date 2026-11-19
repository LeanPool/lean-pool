/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# The value of the image of a polynomial at a rational point

A candidate for `Mathlib.Algebra.Polynomial.Eval.Coeff`, next to `Polynomial.eval_natCast_map` and
`Polynomial.eval_intCast_map`: under a map of division rings, the image of a polynomial takes at a
rational number the image of the value of the polynomial there (`Polynomial.eval_ratCast_map`).

## Main statements

* `Polynomial.eval_ratCast_map`: the value of the image of a polynomial at a rational number.
-/

@[expose] public section

namespace Polynomial

@[simp]
theorem eval_ratCast_map {R S : Type*} [DivisionRing R] [DivisionRing S] (f : R →+* S) (p : R[X])
    (q : ℚ) : (p.map f).eval (q : S) = f (p.eval q) := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' => simp only [hp, hp', Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [map_ratCast, eval_monomial, map_monomial, map_pow, map_mul]

end Polynomial

end
