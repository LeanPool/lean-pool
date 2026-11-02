/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Conic algebras

A **conic algebra** over a commutative ring `k` (`GPR 16.1`) is a unital, not necessarily
associative `k`-algebra `A` together with a quadratic form `n : A → k`, the *norm*, such that

* `n 1 = 1`, and
* `x * x - n(1, x) • x + n x • 1 = 0` for every `x`, where `n(1, x) = polar n 1 x`.

The second axiom says that every element satisfies a monic quadratic equation whose coefficients
are the trace and the norm; conic algebras are exactly the "algebras of degree two" in the older
literature.

## Main definitions

* `ConicAlgebra k A` : the conic structure on a unital non-associative `k`-algebra `A`.
* `ConicAlgebra.baseRing` : the conic structure on `k` itself, with norm `x ↦ x ^ 2`.

The trace, the conjugation and their calculus live in `CompositionAlgebras/Conic/Basic.lean`.

## Implementation notes

**The norm is data, not a property.** Over a general commutative ring a unital algebra can carry
more than one conic norm, so `ConicAlgebra k A` is a *structure* whose first field is the norm —
not a `Prop`-valued mixin asserting that some norm exists. Consequently it is passed explicitly
(`C : ConicAlgebra k A`) rather than found by instance search, and every derived notion (trace,
conjugation) is a function of `C`.

**No regularity, no projectivity, no `2 ∈ kˣ`.** The definition carries none of them, by design
(overview §2): the sedenions (`GPR 19.23`) must be conic without a non-singular norm, and the
characteristic-2 purely inseparable example (`GPR 19.4`) must be conic with an identically zero
polar form. Anything stronger belongs on theorems, not here.

⚠ **Un-halved polar.** The degree-two identity uses `QuadraticMap.polar` — `n(x + y) - n x - n y`
— and never `QuadraticMap.associated`, which is half of it and requires `Invertible 2`. In
particular `n(1, 1) = 2`, not `1`. See overview §6(a).

**Typeclass shape.** A unital non-associative `k`-algebra is spelled
`[NonAssocRing A] [Module k A] [SMulCommClass k A A] [IsScalarTower k A A]`, mathlib's idiom for a
bilinear multiplication (mathlib's `Algebra` class is only available for *associative* `A`, and
implies exactly these four for such `A`, so associative examples need no extra work).

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 16.1.
-/

@[expose] public section

universe u v

variable (k : Type u) (A : Type v) [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A]

/-- A **conic algebra** over `k` (`GPR 16.1`): a unital, not necessarily associative `k`-algebra
`A` together with a quadratic norm `n` satisfying `n 1 = 1` and the degree-two identity

`x * x - n(1, x) • x + n x • 1 = 0`.

The norm is *data*: over a general commutative ring it need not be determined by the algebra
structure. -/
structure ConicAlgebra where
  /-- The norm of the conic algebra, `n_C` in `GPR 16.1`. It is data, not a property: a unital
  algebra may admit several conic norms. -/
  norm : QuadraticForm k A
  /-- The norm is normalized at the unit: `n 1 = 1`. -/
  norm_one : norm 1 = 1
  /-- The **degree-two identity** `x * x = n(1, x) • x - n x • 1`, i.e.
  `x * x - n(1, x) • x + n x • 1 = 0`. The scalar `n(1, x)` is the *un-halved* polar form of `n`
  at the unit, which `Conic/Basic.lean` names `ConicAlgebra.trace`. -/
  mul_self : ∀ x : A, x * x = QuadraticMap.polar norm 1 x • x - norm x • (1 : A)

namespace ConicAlgebra

variable {k A}

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The degree-two identity in the shape it takes in `GPR 16.1`. -/
theorem mul_self_sub_polar_smul_add_norm_smul_eq_zero (C : ConicAlgebra k A) (x : A) :
    x * x - QuadraticMap.polar C.norm 1 x • x + C.norm x • (1 : A) = 0 := by
  rw [C.mul_self]; abel

variable (k) in
/-- The base ring `k` is a conic algebra over itself, with norm the squaring map. This is the
rank-one composition algebra; it is recorded here as the smallest sanity check on the axioms. -/
def baseRing : ConicAlgebra k k where
  norm := QuadraticMap.sq
  norm_one := one_mul 1
  mul_self x := by
    have : QuadraticMap.polar (QuadraticMap.sq (R := k)) 1 x = 2 * x := by
      simp [QuadraticMap.polar, QuadraticMap.sq_apply]; ring
    rw [this]
    simp [QuadraticMap.sq_apply, smul_eq_mul]
    ring

@[simp] theorem baseRing_norm_apply (x : k) : (baseRing k).norm x = x * x := rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **A conic algebra is determined by its norm.** The remaining two fields are propositions, so
two conic structures on the same algebra with the same norm are equal.

⚠ This says nothing about *uniqueness* of the norm, which is false in general and holds for
finitely generated projective algebras only — see `ConicAlgebra.norm_eq_of_projective`. -/
@[ext] theorem ext {C D : ConicAlgebra k A} (h : C.norm = D.norm) : C = D := by
  rcases C with ⟨n, hn₁, hn₂⟩
  rcases D with ⟨m, hm₁, hm₂⟩
  simp only at h
  subst h
  rfl

end ConicAlgebra
