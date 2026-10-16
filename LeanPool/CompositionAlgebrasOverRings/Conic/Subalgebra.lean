/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.Multiplicative
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Subalgebra

/-!
# Restricting a conic structure to a subalgebra

A unital subalgebra `B` of a conic algebra `(A, n)` is again a conic algebra, with the restricted
norm `n|_B`. Nothing has to be checked beyond the two axioms of `GPR 16.1`, both of which are
inherited: `n(1) = 1` because `B` contains the ambient unit, and the degree-two identity because it
is an identity in `A` between elements of `B`.

Trace, conjugation and multiplicativity are likewise the ambient ones restricted, which is what
makes the subalgebra usable as an input to the Cayley–Dickson construction.

## Main definitions

* `ConicAlgebra.restrict` : the conic algebra `B` carved out of `C : ConicAlgebra k A`.

## Main results

* `ConicAlgebra.restrict_norm_apply`, `ConicAlgebra.restrict_trace_apply`,
  `ConicAlgebra.coe_restrict_conj` : norm, trace and conjugation restrict.
* `ConicAlgebra.IsMultiplicative.restrict` : so does multiplicativity of the norm.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 16.1.
-/

@[expose] public section

universe u v

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] (C : ConicAlgebra k A)
  (B : NonAssocSubalgebra k A)

/-- The norm of `C` restricted to a unital subalgebra. -/
def normRestrict : QuadraticForm k B :=
  C.norm.comp B.toNonUnitalSubalgebra.toSubmodule.subtype

variable {C B}

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem normRestrict_apply (b : B) : C.normRestrict B b = C.norm (b : A) := rfl

variable (C B)

/-- **A unital subalgebra of a conic algebra is a conic algebra**, with the restricted norm.

Both axioms are inherited verbatim; in particular no regularity, projectivity or rank hypothesis is
involved, and the subalgebra need not be associative. -/
def restrict : ConicAlgebra k B where
  norm := C.normRestrict B
  norm_one := C.norm_one
  mul_self b := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, OneMemClass.coe_one,
      MulMemClass.coe_mul]
    exact C.mul_self (b : A)

variable {C B}

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem restrict_norm_apply (b : B) : (C.restrict B).norm b = C.norm (b : A) := rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem restrict_trace_apply (b : B) : (C.restrict B).trace b = C.trace (b : A) := rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem coe_restrict_conj (b : B) : ((C.restrict B).conj b : A) = C.conj (b : A) := by
  rw [conj_apply, conj_apply]
  simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, OneMemClass.coe_one,
    restrict_trace_apply]

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- Multiplicativity of the norm is inherited by every unital subalgebra. -/
theorem IsMultiplicative.restrict (h : C.IsMultiplicative) : (C.restrict B).IsMultiplicative :=
  fun x y ↦ h (x : A) (y : A)

end ConicAlgebra
