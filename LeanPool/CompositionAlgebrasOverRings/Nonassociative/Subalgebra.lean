/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra

/-!
# Unital subalgebras of non-associative algebras

Mathlib's `Subalgebra` requires an associative `Semiring`, while its
`NonUnitalSubalgebra` works for a `NonUnitalNonAssocSemiring`. Composition algebras are unital but
need not be associative, so neither object alone represents their unital subalgebras. This file
adds the missing one-field wrapper.

## Main definitions

* `NonAssocSubalgebra R A` : a mathlib `NonUnitalSubalgebra R A` containing `1`.

## Implementation notes

⚠ This is deliberately not named `Subalgebra`: mathlib owns that name for associative algebras.
The underlying multiplication and scalar-action API is inherited from
`NonUnitalSubalgebra`; only the unit is new. With it a `NonAssocSubalgebra` is a `SubringClass`,
from which mathlib supplies the unit, the casts and the `NonAssocRing` structure on each
subalgebra (`SubringClass.toNonAssocRing`).
-/

@[expose] public section

universe u v

/-- A unital subalgebra of a possibly non-associative algebra. -/
structure NonAssocSubalgebra (R : Type u) (A : Type v) [CommRing R]
    [NonAssocRing A] [Module R A] extends NonUnitalSubalgebra R A where
  /-- The ambient unit belongs to the subalgebra. -/
  one_mem : (1 : A) ∈ carrier

namespace NonAssocSubalgebra

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]

instance : SetLike (NonAssocSubalgebra R A) A where
  coe S := S.carrier
  coe_injective S T h := by
    cases S with
    | mk S hS =>
      cases T with
      | mk T hT =>
        have : S = T := NonUnitalSubalgebra.ext fun x ↦ Set.ext_iff.mp h x
        subst T
        rfl

instance : SubringClass (NonAssocSubalgebra R A) A where
  zero_mem {s} := s.toNonUnitalSubalgebra.zero_mem
  add_mem {s} := s.toNonUnitalSubalgebra.add_mem
  mul_mem {s} := s.toNonUnitalSubalgebra.mul_mem
  one_mem {s} := s.one_mem
  neg_mem {s} {_} hx := s.toNonUnitalSubalgebra.neg_mem hx

instance : SMulMemClass (NonAssocSubalgebra R A) R A where
  smul_mem {s} r {_} hx := s.toNonUnitalSubalgebra.smul_mem r hx

end NonAssocSubalgebra
