/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# The coefficientwise derivative on a polynomial ring

`Derivation.dotDer d` applies a derivation `d` of `A` to each coefficient of a polynomial,
killing `X`.  It is Mathlib's `Derivation.mapCoeffs` composed with the identification
`PolynomialModule A A ≃ A[X]`, so that the value is again a polynomial; being a bundled
`Derivation`, it comes with the Leibniz rule.

Mathlib contains this construction in the special case of the `Differential` typeclass
(`Differential.mapCoeffs`, with base ring `ℤ`); this is the same thing over an arbitrary base.
-/

@[expose] public section

open Polynomial

/-- The Leibniz rule for a derivation of a commutative ring into itself, in `mul` form. -/
theorem Derivation.leibniz_mul {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (d : Derivation R A A) (p q : A) : d (p * q) = d p * q + p * d q := by
  rw [d.leibniz, smul_eq_mul, smul_eq_mul]; ring

/-- The coefficientwise derivative on `A[X]` attached to a derivation `d` of `A`. -/
noncomputable def Derivation.dotDer {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (d : Derivation R A A) : Derivation R A[X] A[X] :=
  PolynomialModule.equivPolynomialSelf.compDer d.mapCoeffs

namespace Derivation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (d : Derivation R A A)

@[simp]
theorem coeff_dotDer (p : A[X]) (i : ℕ) : (d.dotDer p).coeff i = d (p.coeff i) := rfl

@[simp]
theorem dotDer_monomial (n : ℕ) (a : A) : d.dotDer (monomial n a) = monomial n (d a) := by
  ext i
  simp [coeff_monomial, apply_ite d]

@[simp]
theorem dotDer_C (a : A) : d.dotDer (C a) = C (d a) := by simp [← monomial_zero_left]

@[simp]
theorem dotDer_X : d.dotDer (X : A[X]) = 0 := by simp [← monomial_one_one_eq_X]

theorem dotDer_C_mul_X_pow (a : A) (j : ℕ) : d.dotDer (C a * X ^ j) = C (d a) * X ^ j := by
  rw [C_mul_X_pow_eq_monomial, dotDer_monomial, C_mul_X_pow_eq_monomial]

/-- The Leibniz rule for `dotDer`, in multiplicative form: `Derivation.leibniz` states it
with a scalar action, which no polynomial identity downstream is phrased in. -/
theorem dotDer_mul (p q : A[X]) : d.dotDer (p * q) = d.dotDer p * q + p * d.dotDer q := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-- The coefficientwise derivative of a square, by the Leibniz rule. -/
theorem dotDer_sq (p : A[X]) : d.dotDer (p ^ 2) = 2 * p * d.dotDer p := by
  rw [sq, dotDer_mul]
  ring

/-- A polynomial whose coefficients are `d`-constant is killed by `dotDer`. -/
theorem dotDer_eq_zero_of_coeff {p : A[X]} (hp : ∀ i, d (p.coeff i) = 0) : d.dotDer p = 0 :=
  Polynomial.ext fun i ↦ by rw [coeff_dotDer, hp i, coeff_zero]

/-- A polynomial congruent, modulo a `d`-constant `B`, to a `d`-constant polynomial has a
`B`-divisible coefficientwise derivative. -/
theorem dvd_dotDer_of_dvd_sub {B v w : A[X]} (hB : ∀ i, d (B.coeff i) = 0)
    (hw : ∀ i, d (w.coeff i) = 0) (h : B ∣ v - w) : B ∣ d.dotDer v := by
  obtain ⟨t, ht⟩ := h
  rw [show v = w + B * t by linear_combination ht, map_add, d.dotDer_eq_zero_of_coeff hw,
    zero_add, leibniz, d.dotDer_eq_zero_of_coeff hB]
  exact ⟨d.dotDer t, by simp⟩

/-- Differentiating the coefficients cannot raise the degree: `dotDer` acts coefficientwise. -/
theorem natDegree_dotDer_le (p : A[X]) : (d.dotDer p).natDegree ≤ p.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun m hm ↦ by
    rw [coeff_dotDer, coeff_eq_zero_of_natDegree_lt hm, map_zero]

end Derivation

end
