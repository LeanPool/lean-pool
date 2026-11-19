/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Remainders by constant multiples, and the quotient by `X - x` at `x`

Candidates for `Mathlib.Algebra.Polynomial.FieldDivision`: over a commutative ring, the quotient of
`p` by `X - x` takes the value `p'(x)` at `x` (`Polynomial.eval_divByMonic_X_sub_C`); over a field,
a constant factor of the dividend comes out of the remainder (`Polynomial.C_mul_mod`, from
`Polynomial.smul_modByMonic`), and a nonzero constant factor of the divisor does not change it
(`Polynomial.mod_C_mul`, from `Polynomial.div_C_mul`).
-/

@[expose] public section

namespace Polynomial

/-- The quotient of `p` by `X - x` takes the value `p'(x)` at `x`, so that at a root `x` of `p`,
`p = (X - x) q` with `q(x) = p'(x)`. -/
theorem eval_divByMonic_X_sub_C {R : Type*} [CommRing R] (p : R[X]) (x : R) :
    (p /ₘ (X - C x)).eval x = p.derivative.eval x := by
  simpa using congr(eval x $(divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative p x))

variable {K : Type*} [Field K]

/-- A constant factor of the dividend comes out of the remainder. -/
theorem C_mul_mod (c : K) (p q : K[X]) : C c * p % q = C c * (p % q) := by
  simp only [mod_def, ← smul_eq_C_mul, smul_modByMonic]

/-- A nonzero constant factor of the divisor does not change the remainder. -/
theorem mod_C_mul {c : K} (hc : c ≠ 0) (p q : K[X]) : p % (C c * q) = p % q := by
  rw [EuclideanDomain.mod_eq_sub_mul_div, EuclideanDomain.mod_eq_sub_mul_div p q, div_C_mul,
    mul_mul_mul_comm, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]

end Polynomial

end
