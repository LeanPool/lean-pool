/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Central scalar identities

Scalars act by right multiplication in any algebra over a commutative semiring.
Specializing to real scalars gives the factorial weights in the Taylor expansion.

## Main results

* `TrotterError.smul_eq_mul_right`.
* `TrotterError.pow_smul_eq_smul_mul`.
* `TrotterError.smul_mul_cast`.
-/

@[expose] public section

namespace TrotterError

open scoped algebraMap

/-- Scalar multiplication is right multiplication by the image of the scalar. -/
lemma smul_eq_mul_right {𝔸 R : Type*} [CommSemiring R] [Semiring 𝔸] [Algebra R 𝔸] (r : R) (a : 𝔸) :
    r • a = a * algebraMap R 𝔸 r := by
  rw [Algebra.smul_def, Algebra.commutes]

/-- The Taylor coefficient `(j! : ℝ)⁻¹ * τ^j` acting by `•` equals the paper's form
`(j! : ℝ)⁻¹ • x * (τ : 𝔸)^j`. -/
lemma pow_smul_eq_smul_mul {𝔸 : Type*} [Semiring 𝔸] [Algebra ℝ 𝔸] (j : ℕ) (x : 𝔸) (τ : ℝ) :
    ((Nat.factorial j : ℝ)⁻¹ * τ ^ j) • x = (Nat.factorial j : ℝ)⁻¹ • x * (τ : 𝔸) ^ j := by
  rw [mul_smul, smul_eq_mul_right (τ ^ j) x]
  simp

/-- Right multiplication by a scalar combines the two scalar factors. -/
lemma smul_mul_cast {𝔸 R : Type*} [CommSemiring R] [Semiring 𝔸] [Algebra R 𝔸]
    (r c : R) (a : 𝔸) : (r • a) * algebraMap R 𝔸 c = (r * c) • a := by
  rw [smul_eq_mul_right r a, smul_eq_mul_right (r * c) a, map_mul, mul_assoc]

end TrotterError
