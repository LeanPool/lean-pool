/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.Multiplicative
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Regularity

/-!
# Composition algebras (`GPR 19.5`)

A **composition algebra** over a commutative ring `k` is a conic algebra `C` (`GPR 16.1`) which is
finitely generated projective as a `k`-module and whose norm is

* **non-singular** in `GPR`'s sense (`QuadraticForm.IsGPRNonsingular`, `GN C.8(e)`: the radical
  vanishes after base change to every field), and
* **multiplicative** (`ConicAlgebra.IsMultiplicative`, `GPR 19.1`: `n(xy) = n(x) n(y)`).

Over a field these are exactly `k`, the quadratic étale algebras, the quaternion algebras and the
octonion algebras, of dimensions 1, 2, 4, 8.

## Main definitions

* `ConicAlgebra.IsComposition` : **`GPR 19.5`**.

## Main results

* `ConicAlgebra.isComposition_baseRing` : `k` itself, with norm the squaring map, is the rank-one
  composition algebra.
* `ConicAlgebra.IsComposition.isGPRRegular` : when `2 ∈ kˣ` the norm of a composition algebra is
  regular, by `GN (C.8.2)`. This is *false* without a hypothesis on `2` — see
  `QuadraticForm.rankOne`, which is `k` itself in characteristic 2.

## Implementation notes

**Why a predicate and not a structure extending `ConicAlgebra`.** The norm of a conic algebra is
data; being a composition algebra is a *property* of that data, so `IsComposition` is `Prop`-valued
and takes `C : ConicAlgebra k A` as an argument. This keeps the three axes of overview §2
separate: the algebra structure is in `A`'s instances, the module regularity is in the
`[Module.Finite k A] [Module.Projective k A]` instance arguments, and only the two genuinely
norm-theoretic clauses are fields of `IsComposition`.

⚠ **Finite generation is assumed here, where `GPR` derives it.** This is a genuine, if slight,
divergence from `GPR 19.5`, and it goes in the direction of *less* generality. `GPR` assumes only
that the underlying module is projective of locally constant rank — allowing that rank to be
infinite a priori — and then *proves* the rank is finite, indeed one of `1, 2, 4, 8` (`GPR 19.18`).
We assume `[Module.Finite k A]` outright. The two definitions therefore pick out the same objects,
but only a posteriori: ours builds in a conclusion of the theory rather than deriving it. So a
`GPR` composition algebra is an `IsComposition` only by way of `GPR 19.18`, and until that theorem
is formalized here, a statement about "every composition algebra" is strictly a statement about the
finitely generated ones.

**No separate "locally constant rank" clause**, although `GPR 19.5` states one: over a commutative
ring the rank of a finitely generated projective module is automatically locally constant on
`Spec k` (this project proves as much in `Module/RankDecomposition.lean`,
`Module.finite_range_rankAtStalk` and `Module.rankIdempotent`), so the clause would be redundant.
The *constancy* of the rank — which is what makes the rank dichotomy `1, 2, 4, 8` a statement about
a single number — is a hypothesis on theorems, not part of the definition.

**No `PreCompositionAlgebra`.** `GPR` defines one; we deliberately do not (overview, *Design
decisions* 1): the bundle "projective + non-degenerate + multiplicative" is not stable under base
change (`GPR 19.7(a)`, with `GPR 19.4` as the counterexample), and the one theorem that motivates
the notion (`GPR 19.3`) is stated with those three as separate hypotheses instead.

**Universes.** `QuadraticForm.IsGPRNonsingular` quantifies over all fields in a universe, so it
carries a third universe parameter beyond those of `k` and `A`; `IsComposition` inherits it, and
names it the same way `QuadraticForm.IsEKMNondegenerate` does.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.1, 19.5.
* [GN] Gille, Neher, *Group schemes over LG-rings…*, European J. Math. **11** (2025), art. 42,
  C.8 (non-singularity).
-/

@[expose] public section

universe u v w

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]

/-- **`GPR 19.5`: `C` is a composition algebra.** A conic algebra whose underlying module is
finitely generated projective (an instance argument, not a field) and whose norm is non-singular
in `GPR`'s sense and multiplicative.

⚠ **Finite generation is a hypothesis here and a theorem in `GPR`**, which assumes only projective
of locally constant rank and derives finiteness of the rank from `GPR 19.18`. This definition is
correspondingly, and very slightly, less general; see the module docstring.

⚠ **Non-singular, not regular and not non-degenerate.** `QuadraticForm.IsGPRNonsingular` is the
base-change-stable vanishing of the radical (`GN C.8(e)`), which is what makes composition algebras
stable under base change. It is strictly weaker than `QuadraticForm.IsGPRRegular` unless `2 ∈ kˣ`
(`QuadraticForm.isGPRRegular_iff_isGPRNonsingular`), and it is not mathlib's
`LinearMap.BilinForm.Nondegenerate`; see overview §6(b). -/
structure IsComposition.{w'} (C : ConicAlgebra k A) : Prop where
  /-- The norm is non-singular in `GPR`'s sense (`GN C.8(e)`): its radical vanishes after base
  change to every field. -/
  isGPRNonsingular : QuadraticForm.IsGPRNonsingular.{u, v, w'} C.norm
  /-- The norm permits composition: `n(xy) = n(x) n(y)` (`GPR 19.1`). -/
  isMultiplicative : C.IsMultiplicative

namespace IsComposition

variable {C : ConicAlgebra k A}

omit [SMulCommClass k A A] [IsScalarTower k A A] in
theorem norm_mul (h : C.IsComposition.{u, v, w}) (x y : A) :
    C.norm (x * y) = C.norm x * C.norm y :=
  h.isMultiplicative.norm_mul x y

omit [SMulCommClass k A A] in
/-- **Norm-associativity** of a composition algebra (`GPR 16.5`): `n(xy, z) = n(y, (conj x)z)`. -/
theorem polar_mul_left (h : C.IsComposition.{u, v, w}) (x y z : A) :
    QuadraticMap.polar C.norm (x * y) z = QuadraticMap.polar C.norm y (C.conj x * z) :=
  h.isMultiplicative.polar_mul_left x y z

omit [IsScalarTower k A A] in
/-- **Norm-associativity** of a composition algebra (`GPR 16.5`): `n(xy, z) = n(x, z(conj y))`. -/
theorem polar_mul_right (h : C.IsComposition.{u, v, w}) (x y z : A) :
    QuadraticMap.polar C.norm (x * y) z = QuadraticMap.polar C.norm x (z * C.conj y) :=
  h.isMultiplicative.polar_mul_right x y z

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- When `2 ∈ kˣ`, the norm of a composition algebra is **regular** (`GN (C.8.2)`), i.e. its polar
form is an isomorphism onto the dual and not merely injective.

⚠ The hypothesis on `2` is not removable: `ConicAlgebra.baseRing k` is a composition algebra whose
norm is `QuadraticForm.rankOne 1`, and over `ℤ` that form is non-singular but not regular
(`QuadraticForm.not_isGPRRegular_rankOne_one_int`). -/
theorem isGPRRegular [Invertible (2 : k)] (h : C.IsComposition.{u, v, u}) :
    C.norm.IsGPRRegular :=
  h.isGPRNonsingular.isGPRRegular

end IsComposition

variable (k) in
/-- **The rank-one composition algebra.** `k` itself, with norm the squaring map
(`ConicAlgebra.baseRing`), is a composition algebra: the norm is `QuadraticForm.rankOne 1`, which is
non-singular over any commutative ring (`QuadraticForm.isGPRNonsingular_rankOne`), and `(xy)² =
x²y²`.

Note that this holds with no hypothesis on `2`, even though `⟨1⟩` is *regular* only when `2` is a
unit. -/
theorem isComposition_baseRing : (baseRing k).IsComposition.{u, u, u} where
  isGPRNonsingular := by
    have hsq : (baseRing k).norm = QuadraticForm.rankOne (1 : k) := by
      rw [QuadraticForm.rankOne, one_smul]
      rfl
    rw [hsq]
    exact QuadraticForm.isGPRNonsingular_rankOne isUnit_one
  isMultiplicative := isMultiplicative_baseRing k

end ConicAlgebra
