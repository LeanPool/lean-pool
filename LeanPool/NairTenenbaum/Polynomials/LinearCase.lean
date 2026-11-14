/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialSystem

/-! # The linear specialization

An explicit instance of the polynomial hypotheses and the simplification of the
weight and main term when `Q(X)=X`. This checks that the statement surface admits
the paper's basic example and that the dagger restriction simplifies correctly.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- The single linear-polynomial system used to specialize the general estimates. -/
noncomputable def linearSystem : PolynomialSystem 1 1 where
  Q := fun _ => X
  R := fun _ => X
  exponent := identityExponents 1
  sign := fun _ => 1
  sign_abs := by simp
  factorization := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp [identityExponents]
  irreducible := by intro h; simpa using (Polynomial.irreducible_X (R := ℚ))
  nonassociated := by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim
  exponent_pos := by intro h; simp
  noFixedPrime := by simpa using noFixedPrimeDivisor_X

@[simp] theorem linearSystem_radical : linearSystem.radical = (X : ℤ[X]) := by
  simp [PolynomialSystem.radical, linearSystem]

@[simp] theorem linearSystem_discriminant : linearSystem.discriminant = 1 := by
  rw [PolynomialSystem.discriminant, linearSystem_radical,
    Polynomial.discr_of_degree_eq_one (by simp)]
  rfl

end NairTenenbaum
