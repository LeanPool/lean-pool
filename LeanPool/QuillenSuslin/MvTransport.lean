/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.Fibre
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Transport of modules along `A[X₁, …, Xₙ₊₁] ≅ A[X₁, …, Xₙ][X]`

Quillen's Theorem 1′ (Quillen 1976, p. 169) is proved by induction on the number of variables,
viewing `A[X₁, …, Xₙ₊₁]` as the polynomial ring `B[X]` over `B = A[X₁, …, Xₙ]` through
`MvPolynomial.finSuccEquiv`. This file collects the base changes needed to move modules and
extension isomorphisms along that identification.

* Base change along a bijective algebra map `R → P` is an equivalence of module categories, so an
  isomorphism `P ⊗[R] M ≅ P ⊗[A] N` gives `M ≅ R ⊗[A] N` (`linearEquivOfBijective`); in
  particular every module over `R` is extended from `A` when `A → R` is bijective
  (`isExtendedFrom_of_bijective`).
* An extension isomorphism over `R' = A'[X₁, …, Xₙ₊₁]` becomes one over `L[X]`, with
  `L = A'[X₁, …, Xₙ]` (`extensionEquivTransport`, `finSuccEquiv_map`).
* Such an isomorphism `L[X] ⊗[B[X]] M ≅ L[X] ⊗[A'] Q` shows that `M` is extended after base
  change to `L`, and its reduction at `X = 0` is an isomorphism `L ⊗[B] M(0) ≅ L ⊗[A'] Q`
  (`IsExtendedAfter.of_equiv_tensor`, `fibreEquivOfEquiv`).

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
-/

@[expose] public noncomputable section

universe u v

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

section Bijective

variable {A R P : Type*} [CommRing A] [CommRing R] [CommRing P] [Algebra A R] [Algebra A P]
  [Algebra R P] [IsScalarTower A R P]

/-- Base change along a bijective algebra map `R → P` is isomorphic to the identity. -/
def equivBaseChangeOfBijective (hbij : Function.Bijective (algebraMap R P)) (M : Type*)
    [AddCommGroup M] [Module R M] : M ≃ₗ[R] P ⊗[R] M :=
  (TensorProduct.lid R M).symm ≪≫ₗ
    TensorProduct.congr (LinearEquiv.ofBijective (Algebra.linearMap R P) hbij)
      (LinearEquiv.refl R M)

theorem surjective_tmul_of_bijective (hbij : Function.Bijective (algebraMap R P)) (M : Type*)
    [AddCommGroup M] [Module R M] : Function.Surjective fun m : M => (1 : P) ⊗ₜ[R] m :=
  TensorProduct.mk_surjective R M P hbij.2

/-- For a bijective algebra map `R → P` over `A`, an isomorphism `P ⊗[R] M ≅ P ⊗[A] N` gives an
isomorphism `M ≅ R ⊗[A] N`. -/
def linearEquivOfBijective (hbij : Function.Bijective (algebraMap R P)) {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module A N]
    (e : P ⊗[R] M ≃ₗ[P] P ⊗[A] N) : M ≃ₗ[R] R ⊗[A] N :=
  equivBaseChangeOfBijective hbij M ≪≫ₗ e.restrictScalars R ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.ofBijective (Algebra.linearMap R P) hbij).symm
      (LinearEquiv.refl A N)

end Bijective

/-- If `A → R` is bijective, every `R`-module is extended from `A`. -/
theorem isExtendedFrom_of_bijective {A : Type u} {R : Type*} [CommRing A] [CommRing R]
    [Algebra A R] (hbij : Function.Bijective (algebraMap A R)) (M : Type v) [AddCommGroup M]
    [Module R M] : IsExtendedFrom A R M := by
  let σ := RingEquiv.ofBijective (algebraMap A R) hbij
  let _ : Algebra R A := σ.symm.toRingHom.toAlgebra
  have : IsScalarTower A R A := .of_algebraMap_eq fun a => (σ.symm_apply_apply a).symm
  have hbij' : Function.Bijective (algebraMap R A) := σ.symm.bijective
  have : Small.{v} (A ⊗[R] M) := small_of_surjective (surjective_tmul_of_bijective hbij' M)
  exact .of_linearEquiv_tensor
    (linearEquivOfBijective hbij' (TensorProduct.lid A (A ⊗[R] M)).symm)

section Transport

variable {A' R R' P P' : Type*} [CommRing A'] [CommRing R] [CommRing R'] [CommRing P]
  [CommRing P'] [Algebra R P] [Algebra P P'] [Algebra R R'] [Algebra A' R'] [Algebra A' P']

/-- Transport of an extension isomorphism over `R'` along an `A'`-algebra isomorphism
`ψ : R' ≅ P'` compatible with `R → R'` and `R → P → P'`: an isomorphism
`R' ⊗[R] M ≅ R' ⊗[A'] Q` gives `P' ⊗[P] (P ⊗[R] M) ≅ P' ⊗[A'] Q`. -/
def extensionEquivTransport (ψ : R' ≃ₐ[A'] P')
    (hψ : ∀ r : R, ψ (algebraMap R R' r) = algebraMap P P' (algebraMap R P r)) {M Q : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module A' Q]
    (e : R' ⊗[R] M ≃ₗ[R'] R' ⊗[A'] Q) : P' ⊗[P] (P ⊗[R] M) ≃ₗ[P'] P' ⊗[A'] Q :=
  letI : Algebra R' P' := ψ.toRingHom.toAlgebra
  letI : Algebra R P' := ((algebraMap P P').comp (algebraMap R P)).toAlgebra
  haveI : IsScalarTower R P P' := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R R' P' := .of_algebraMap_eq fun r => (hψ r).symm
  haveI : IsScalarTower A' R' P' := .of_algebraMap_eq fun a => (ψ.commutes a).symm
  AlgebraTensorModule.cancelBaseChange R P P' P' M ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R R' P' P' M).symm ≪≫ₗ e.baseChange R' P' _ _ ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange A' R' P' P' Q

end Transport

section FinSucc

attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra

/-- `MvPolynomial.finSuccEquiv` commutes with change of coefficients. -/
theorem finSuccEquiv_map {A A' : Type*} [CommRing A] [CommRing A'] (f : A →+* A') (n : ℕ)
    (r : MvPolynomial (Fin (n + 1)) A) :
    MvPolynomial.finSuccEquiv A' n (MvPolynomial.map f r) =
      (MvPolynomial.finSuccEquiv A n r).map (MvPolynomial.map f) := by
  have key : (MvPolynomial.finSuccEquiv A' n).toRingHom.comp (MvPolynomial.map f) =
      (Polynomial.mapRingHom (MvPolynomial.map f)).comp
        (MvPolynomial.finSuccEquiv A n).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [MvPolynomial.finSuccEquiv_apply]
  exact RingHom.congr_fun key r

end FinSucc

section Fibre

variable {B : Type u} [CommRing B] {L A' : Type*} [CommRing L] [CommRing A'] [Algebra B L]
  [Algebra A' L]

/-- An isomorphism `L[X] ⊗[B[X]] M ≅ L[X] ⊗[A'] Q` shows that `M` is extended after base change
to `L`. -/
theorem IsExtendedAfter.of_equiv_tensor {M : Type v} [AddCommGroup M] [Module B[X] M]
    {Q : Type*} [AddCommGroup Q] [Module A' Q]
    (e : (letI := Polynomial.algebra B L; L[X] ⊗[B[X]] M) ≃ₗ[L[X]] L[X] ⊗[A'] Q) :
    IsExtendedAfter B L M := by
  let _ := Polynomial.algebra B L
  exact .of_polynomial_linearEquiv (e ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange A' L L[X] L[X] Q).symm)

/-- The reduction at `X = 0` of an isomorphism `L[X] ⊗[B[X]] M ≅ L[X] ⊗[A'] Q` is an isomorphism
`L ⊗[B] M(0) ≅ L ⊗[A'] Q`. -/
def fibreEquivOfEquiv {M : Type v} [AddCommGroup M] [Module B[X] M] {Q : Type*}
    [AddCommGroup Q] [Module A' Q]
    (e : (letI := Polynomial.algebra B L; L[X] ⊗[B[X]] M) ≃ₗ[L[X]] L[X] ⊗[A'] Q) :
    L ⊗[B] fibre B M ≃ₗ[L] L ⊗[A'] Q :=
  letI := Polynomial.algebra B L
  letI := evalZeroAlgebra L
  haveI : IsScalarTower A' L[X] L := .of_algebraMap_eq fun a => by
    change _ = (C (algebraMap A' L a)).eval 0
    rw [eval_C]
  (fibreEquiv B M L).symm ≪≫ₗ e.baseChange L[X] L _ _ ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange A' L[X] L L Q

end Fibre

end LeanPool.QuillenSuslin
