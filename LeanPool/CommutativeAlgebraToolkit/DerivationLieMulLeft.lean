/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.RingTheory.Derivation.Lie

/-!
# Derivations and multiplication operators

For a derivation `D` of a commutative `R`-algebra `A`, the commutator of `D` with multiplication
by `a` is multiplication by `D a`, and conjugating `D` by multiplication by a unit `u` subtracts
multiplication by the logarithmic derivative `u⁻¹ * D u`.

## Main statements

* `Derivation.lie_mulLeft`: `⁅D, mulLeft a⁆ = mulLeft (D a)`.
* `Derivation.mulLeft_mul_mul_mulLeft_inv`: `u ∘ D ∘ u⁻¹ = D - (u⁻¹ * D u)`.
-/

public section

namespace Derivation

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] (a : A)

/-- The commutator of a derivation with multiplication by `a` is multiplication by `D a`. -/
theorem lie_mulLeft (D : Derivation R A A) :
    ⁅(D : Module.End R A), LinearMap.mulLeft R a⁆ = LinearMap.mulLeft R (D a) := by
  ext; simp [Ring.lie_def, leibniz, mul_comm]

/-- Conjugating a derivation by multiplication by a unit `u` subtracts multiplication by the
logarithmic derivative `u⁻¹ * D u`. -/
theorem mulLeft_mul_mul_mulLeft_inv (D : Derivation R A A) (u : Aˣ) :
    LinearMap.mulLeft R (u : A) * (D : Module.End R A) * LinearMap.mulLeft R ((u⁻¹ : Aˣ) : A) =
      (D : Module.End R A) - LinearMap.mulLeft R ((u⁻¹ : Aˣ) * D u) := by
  ext b
  simp [leibniz, D.leibniz_of_mul_eq_one u.inv_mul, mul_add, sq, ← mul_assoc, mul_comm _ b,
    sub_eq_neg_add]

end Derivation
