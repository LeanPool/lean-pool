/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Regularity
public import Mathlib.LinearAlgebra.QuadraticForm.Dual

/-!
# Hyperbolic quadratic forms

The **hyperbolic form** of an `R`-module `M` is mathlib's `QuadraticForm.dualProd R M`, the
quadratic form `(f, m) ↦ f m` on `M* ⊕ M`. (GPR writes it on `M ⊕ M*`; we follow mathlib's order
of the factors.) It is the basic example of a regular quadratic form that exists over *every*
commutative ring with no hypothesis on `2`, and it is what Witt cancellation is ultimately about:
the reduction of `GN 6.5` to the hyperbolic case (via `q ⊥ (-q)` hyperbolic) is what makes the
elementary route to cancellation possible in characteristic `2`, where a regular form need not
split off any rank-one piece at all.

mathlib supplies the form and its functoriality (`QuadraticForm.dualProdIsometry`,
`QuadraticForm.dualProdProdIsometry`). This file adds its regularity, and the
characteristic-free isometry `q ⊥ (-q) ≅ dualProd R M` for `q` regular.

## Main definitions

* `QuadraticForm.dualProdPolarEquiv R M` : the polar map of `dualProd R M`, as a linear
  equivalence `M* ⊕ M ≃ (M* ⊕ M)*`.
* `QuadraticForm.toDualProdMap q`, `QuadraticForm.isometryEquivDualProd q hq` : the comparison
  map `M ⊕ M → M* ⊕ M`, and the isometry `q ⊥ (-q) ≅ dualProd R M` it gives for `q` regular.

## Main results

* `QuadraticForm.polar_dualProd` : the polar form is the canonical pairing,
  `((f, m), (f', m')) ↦ f m' + f' m`. It is *symmetric and nondegenerate over any ring*, with no
  hypothesis on `2` — which is exactly why hyperbolic forms survive characteristic `2`.
* `QuadraticForm.isGPRRegular_dualProd` : the hyperbolic form of a finitely generated projective
  module is regular.
* `QuadraticForm.isGPRNonsingular_dualProd` : hence non-singular.
* `QuadraticForm.dualProd_apply_inl`, `QuadraticForm.dualProd_apply_inr` : `M* ⊕ 0` and
  `0 ⊕ M` are totally isotropic — the two standard Lagrangians.
* `QuadraticForm.isGPRNonsingular_of_basis_pairing` : a form on `M ⊕ M` pairing the two summands
  against each other in the coordinates of a finite basis, `Q (x, y) = ∑ᵢ xᵢ yᵢ`, is hyperbolic
  and therefore non-singular. This is how a hyperbolic form is recognized in practice.
* `QuadraticForm.isGPRNonsingular_of_linearEquiv_basis_pairing` : the same, for a form on a module
  presented as `M ⊕ M` by an explicit equivalence.
* `QuadraticForm.isGPRRegular_of_basis_pairing` : such a form is in fact *regular*, which is the
  stronger conclusion the orthogonal splitting of a submodule needs.

## Implementation notes

Regularity is proved by factoring the polar map as a composition of two linear equivalences:

  `M* ⊕ M  ≃  M** ⊕ M*  ≃  (M* ⊕ M)*`

The first is `Prod.comm` followed by `Module.evalEquiv` on the first factor — this is where
finiteness and projectivity of `M` enter, through mathlib's `Module.IsReflexive` instance for
finitely generated projective modules. The second is mathlib's
`Module.dualProdDualEquivDual`. No determinant, no localization, and no assumption on `2`.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Exc. 11.30.
* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, 6.5.
* R. Baeza, *Quadratic Forms over Semilocal Rings*, Lecture Notes in Math. **655**, Springer 1978,
  I, (4.7).
-/

@[expose] public section

universe u v w t₁

namespace QuadraticForm

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- `M* ⊕ 0` is totally isotropic: it is one of the two standard Lagrangians of the hyperbolic
form. (Not a `simp` lemma: `dualProd_apply` already reduces both sides.) -/
theorem dualProd_apply_inl (f : Module.Dual R M) : dualProd R M (f, 0) = 0 :=
  map_zero f

/-- `0 ⊕ M` is totally isotropic: it is the other standard Lagrangian. -/
theorem dualProd_apply_inr (m : M) : dualProd R M (0, m) = 0 :=
  rfl

/-- The polar form of the hyperbolic form is the canonical pairing between `M* ⊕ M` and itself,
`((f, m), (f', m')) ↦ f m' + f' m`. Note there is no factor of `2` anywhere: this is a
nondegenerate *symmetric* bilinear form over an arbitrary commutative ring. -/
theorem polar_dualProd (x y : Module.Dual R M × M) :
    QuadraticMap.polar (dualProd R M) x y = x.1 y.2 + y.1 x.2 := by
  simp only [QuadraticMap.polar, dualProd_apply, Prod.fst_add, Prod.snd_add,
    LinearMap.add_apply, map_add]
  ring

variable (R M)

/-- The linear equivalence `M* ⊕ M ≃ (M* ⊕ M)*` underlying regularity of the hyperbolic form.
Reflexivity of `M` — automatic for `M` finitely generated projective — is the only input. -/
noncomputable def dualProdPolarEquiv [Module.Finite R M] [Module.Projective R M] :
    (Module.Dual R M × M) ≃ₗ[R] Module.Dual R (Module.Dual R M × M) :=
  ((LinearEquiv.prodComm R (Module.Dual R M) M).trans
      ((Module.evalEquiv R M).prodCongr (LinearEquiv.refl R (Module.Dual R M)))).trans
    (Module.dualProdDualEquivDual R (Module.Dual R M) M)

theorem dualProdPolarEquiv_apply [Module.Finite R M] [Module.Projective R M]
    (x y : Module.Dual R M × M) : dualProdPolarEquiv R M x y = x.1 y.2 + y.1 x.2 := by
  simp [dualProdPolarEquiv, Module.dualProdDualEquivDual_apply, add_comm]

/-- **The hyperbolic form of a finitely generated projective module is regular.**

The polar map is the canonical isomorphism `M* ⊕ M ≃ (M* ⊕ M)*`, which exists because `M` is
reflexive. Unlike the criteria in `QuadraticForm/Regularity.lean`, this needs no assumption on
`2`, no determinant computation and no localization. -/
theorem isGPRRegular_dualProd [Module.Finite R M] [Module.Projective R M] :
    QuadraticForm.IsGPRRegular (dualProd R M) := by
  have h : (QuadraticMap.polarBilin (dualProd R M) :
      (Module.Dual R M × M) →ₗ[R] Module.Dual R (Module.Dual R M × M)) =
      (dualProdPolarEquiv R M).toLinearMap := by
    refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
    rw [QuadraticMap.polarBilin_apply_apply, polar_dualProd, LinearEquiv.coe_coe,
      dualProdPolarEquiv_apply]
  rw [QuadraticForm.IsGPRRegular, h]
  exact (dualProdPolarEquiv R M).bijective

/-- The hyperbolic form of a finitely generated projective module is non-singular
(`GN (C.8.1)` applied to `QuadraticForm.isGPRRegular_dualProd`). -/
theorem isGPRNonsingular_dualProd [Module.Finite R M] [Module.Projective R M] :
    QuadraticForm.IsGPRNonsingular (dualProd R M) :=
  (isGPRRegular_dualProd R M).isGPRNonsingular

end QuadraticForm

/-! ### `q ⊥ (-q)` is hyperbolic

This is the reduction that makes the elementary route to Witt cancellation work: from
`q₁ ⊥ q₃ ≅ q₂ ⊥ q₃` one gets `q₁ ⊥ h ≅ q₂ ⊥ h` with `h` hyperbolic by adding `-q₃` to both sides,
so cancelling an arbitrary regular form reduces to cancelling a hyperbolic one. -/

namespace QuadraticForm

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M] (q : QuadraticForm R M)

/-- The comparison map `M ⊕ M → M* ⊕ M` witnessing that `q ⊥ (-q)` is hyperbolic:
`(x, y) ↦ (B(x - y, ·) + polar q y, x - y)`, where `B` is the bilinear representative of `q`.

This is a characteristic-free version of mathlib's `QuadraticForm.toDualProd`, which is built from
`QuadraticMap.associated` and so needs `2` to be invertible. The `B(x - y, ·)` summand is what
makes this work in characteristic `2`: the naive map `(x, y) ↦ (polar q y, x - y)` computes
`q x - q y - q (x - y)`, and it is precisely a *bilinear representative* — which
`QuadraticForm/BaseChangeProjective.lean` provides for any finitely generated projective module,
with no hypothesis on `2` — that supplies the missing `q (x - y)` linearly. -/
noncomputable def toDualProdMap : (M × M) →ₗ[R] (Module.Dual R M × M) :=
  LinearMap.prod
    (QuadraticMap.bilinRepr q ∘ₗ (LinearMap.fst R M M - LinearMap.snd R M M) +
      QuadraticMap.polarBilin q ∘ₗ LinearMap.snd R M M)
    (LinearMap.fst R M M - LinearMap.snd R M M)

@[simp]
theorem toDualProdMap_apply (x : M × M) :
    toDualProdMap q x =
      (QuadraticMap.bilinRepr q (x.1 - x.2) + QuadraticMap.polarBilin q x.2, x.1 - x.2) :=
  rfl

/-- The comparison map is an isometry onto the hyperbolic form: `q x - q y` is computed by the
hyperbolic pairing. -/
theorem dualProd_toDualProdMap (x : M × M) :
    dualProd R M (toDualProdMap q x) = (q.prod (-q)) x := by
  simp only [toDualProdMap_apply, dualProd_apply, LinearMap.add_apply,
    QuadraticMap.bilinRepr_apply_self, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.prod_apply, neg_apply, QuadraticMap.polar]
  abel_nf

/-- When `q` is regular the comparison map is bijective: solving `B(u, ·) + polar q y = φ` for `y`
is exactly inverting the polar map, which is what regularity provides. -/
theorem bijective_toDualProdMap (hq : QuadraticForm.IsGPRRegular q) :
    Function.Bijective (toDualProdMap q) := by
  set E := LinearEquiv.ofBijective (QuadraticMap.polarBilin q :
    M →ₗ[R] Module.Dual R M) hq with hE
  have hEq : ∀ y : M, QuadraticMap.polarBilin q y = E y := fun _ ↦ rfl
  set s : (Module.Dual R M × M) →ₗ[R] M :=
    E.symm.toLinearMap ∘ₗ (LinearMap.fst R (Module.Dual R M) M -
      QuadraticMap.bilinRepr q ∘ₗ LinearMap.snd R (Module.Dual R M) M) with hs
  have hsapp : ∀ z : Module.Dual R M × M,
      QuadraticMap.polarBilin q (s z) = z.1 - QuadraticMap.bilinRepr q z.2 := by
    intro z
    rw [hEq, hs]
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.snd_apply,
      LinearMap.fst_apply, LinearEquiv.coe_coe]
    exact E.apply_symm_apply _
  constructor
  · intro x y hxy
    simp only [toDualProdMap_apply, Prod.mk.injEq] at hxy
    obtain ⟨h2, h1⟩ := hxy
    rw [h1, add_right_inj] at h2
    have hsnd : x.2 = y.2 := hq.1 h2
    rw [hsnd, sub_left_inj] at h1
    exact Prod.ext h1 hsnd
  · intro z
    have hfst : (z.2 + s z) - s z = z.2 := by abel
    refine ⟨(z.2 + s z, s z), ?_⟩
    rw [toDualProdMap_apply]
    refine Prod.ext ?_ hfst
    simp only [hfst, hsapp z]
    abel

/-- **`q ⊥ (-q)` is hyperbolic**, for `q` regular on a finitely generated projective module
(`Baeza I, (4.7)`; used in the proof of `GN 6.5`).

Regularity is exactly what is needed, and not merely a convenience: the comparison map is
bijective if and only if the polar map is. This answers, without any hypothesis on `2`, the TODO
in mathlib's `Mathlib/LinearAlgebra/QuadraticForm/Dual.lean` asking for `QuadraticForm.toDualProd`
to be upgraded to an isometry equivalence. -/
noncomputable def isometryEquivDualProd (hq : QuadraticForm.IsGPRRegular q) :
    QuadraticMap.IsometryEquiv (q.prod (-q)) (dualProd R M) where
  __ := LinearEquiv.ofBijective (toDualProdMap q) (bijective_toDualProdMap q hq)
  map_app' := dualProd_toDualProdMap q

end QuadraticForm

/-! ### Recognizing a hyperbolic form in coordinates

A quadratic form on `M ⊕ M` given by the *pairing of the two summands against each other* is
hyperbolic: the second summand is being used as a copy of `M*`, along the self-duality supplied by
a finite basis. This is the shape in which hyperbolic forms actually turn up — the norm of a split
octonion algebra is one — and it is the one place a basis is used, so that the
coordinate form `∑ᵢ xᵢ yᵢ` can be recognized without unfolding any duality by hand. -/

namespace Module.Basis

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The self-duality attached to a finite basis is the **coordinate pairing**
`⟪m, n⟫ = ∑ᵢ mᵢ nᵢ`: mathlib's `Module.Basis.toDual` sends `bᵢ ↦ bᵢ*`, and evaluating it at a
second vector expands both arguments in the basis. Symmetric, and with no hypothesis on `2`. -/
theorem toDual_apply_eq_sum (b : Basis ι R M) (m n : M) :
    b.toDual m n = ∑ i, b.repr n i * b.repr m i := by
  conv_lhs => rw [← b.sum_repr n]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [map_smul, smul_eq_mul, b.toDual_apply_left]

end Module.Basis

namespace QuadraticForm

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]

/-- **A form pairing two copies of `M` against each other is hyperbolic**, hence non-singular.

The hypothesis is the coordinate identity `Q (x, y) = ∑ᵢ xᵢ yᵢ` for the coordinates of some finite
basis of `M`; the conclusion needs no hypothesis on `2`, since
`QuadraticForm.isGPRNonsingular_dualProd` needs none. -/
theorem isGPRNonsingular_of_basis_pairing {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R M) {Q : QuadraticForm R (M × M)}
    (hQ : ∀ x : M × M, Q x = ∑ i, b.repr x.1 i * b.repr x.2 i) :
    QuadraticForm.IsGPRNonsingular.{u, v, w} Q := by
  classical
  have hcomp : Q = (dualProd R M).comp
      (LinearEquiv.prodCongr b.toDualEquiv (LinearEquiv.refl R M)).toLinearMap := by
    refine QuadraticMap.ext fun x ↦ ?_
    rw [hQ x, QuadraticMap.comp_apply]
    simp [b.toDual_apply_eq_sum, mul_comm]
  rw [hcomp]
  exact (isGPRNonsingular_dualProd R M).comp_linearEquiv _

/-- **A form pairing two copies of `M` against each other is regular**, being the hyperbolic form
of `M` in the coordinates of the given basis.

Regularity, unlike non-singularity, is what the orthogonal splitting of
`QuadraticForm/OrthogonalComplement.lean` consumes; it needs no hypothesis on `2` either. -/
theorem isGPRRegular_of_basis_pairing {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R M) {Q : QuadraticForm R (M × M)}
    (hQ : ∀ x : M × M, Q x = ∑ i, b.repr x.1 i * b.repr x.2 i) :
    QuadraticForm.IsGPRRegular Q := by
  classical
  have hcomp : Q = (dualProd R M).comp
      (LinearEquiv.prodCongr b.toDualEquiv (LinearEquiv.refl R M)).toLinearMap := by
    refine QuadraticMap.ext fun x ↦ ?_
    rw [hQ x, QuadraticMap.comp_apply]
    simp [b.toDual_apply_eq_sum, mul_comm]
  rw [hcomp]
  exact QuadraticForm.IsGPRRegular.comp_linearEquiv (isGPRRegular_dualProd R M) _

/-- **A form that becomes a pairing of two copies of `M` in suitable coordinates is hyperbolic**,
hence non-singular.

The same statement as `QuadraticForm.isGPRNonsingular_of_basis_pairing`, but for a form on any
module `N` presented as `M ⊕ M` by an explicit equivalence — which is how the split quaternion
algebra meets it: `Mat₂(k)` becomes `k² ⊕ k²` by reading off `(a₀₀, a₀₁)` and `(a₁₁, -a₁₀)`, and
the determinant becomes the standard pairing of the two. -/
theorem isGPRNonsingular_of_linearEquiv_basis_pairing {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R M) {N : Type t₁} [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Projective R N] (e : N ≃ₗ[R] M × M) {Q : QuadraticForm R N}
    (hQ : ∀ x : N, Q x = ∑ i, b.repr (e x).1 i * b.repr (e x).2 i) :
    QuadraticForm.IsGPRNonsingular.{u, t₁, w} Q := by
  have hcomp : Q = (Q.comp e.symm.toLinearMap).comp e.toLinearMap := by
    refine QuadraticMap.ext fun x ↦ ?_
    simp [QuadraticMap.comp_apply]
  rw [hcomp]
  refine QuadraticForm.IsGPRNonsingular.comp_linearEquiv ?_ e
  refine isGPRNonsingular_of_basis_pairing b fun x ↦ ?_
  rw [QuadraticMap.comp_apply, hQ]
  simp

end QuadraticForm
