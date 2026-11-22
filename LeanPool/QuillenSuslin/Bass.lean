/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.Glue
public import LeanPool.QuillenSuslin.Horrocks

import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Bass's theorem and Horrocks' theorem in Quillen's form

Finitely generated projective `A`-modules `P` and `Q` that become isomorphic over `A⟨X⟩` are
isomorphic (Bass; Lombardi–Quitté, Theorem XVI.4.8). The isomorphism descends to `A[X]_r` for a
monic `r` of degree `d`, because the modules are finitely presented. With `r* = Xᵈ r(1/X)` the
reverse of `r`, which has constant coefficient `1`, the substitution `X ↦ X⁻¹` maps `A[X]_r` to
`A[X]_{X r*}`, and `X`, `r*` are comaximal. Zariski gluing (3.6) of `A[X]_X ⊗[A] P` and
`A[X]_{r*} ⊗[A] Q` gives a finitely generated projective `A[X]`-module `M` which is extended from
`A` over `A⟨X⟩` (a localisation of `A[X]_X`), hence extended from `A` by the affine Horrocks
theorem; evaluating at `X = 1` (through `A[X]_X`) and at `X = 0` (through `A[X]_{r*}`) gives
`P ≅ M(1) ≅ M(0) ≅ Q`.

Horrocks' theorem in Quillen's form follows: a finitely generated projective `A[X]`-module `P`
that becomes free over `A⟨X⟩` is extended from `A` by the affine Horrocks theorem, `P ≅ A[X] ⊗ N`,
and `N` is free by Bass's theorem (Quillen 1976, Theorem 3).

## Main results

* `exists_monic_away_equiv`: an isomorphism over `A⟨X⟩` descends to `A[X]_r`, `r` monic.
* `nonempty_linearEquiv_of_eval`: evaluation of an extended module through a localisation.
* `nonempty_linearEquiv_of_monicLocalization`: Bass's theorem.
* `free_of_free_monicLocalization`: Horrocks' theorem in Quillen's form.

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
* H. Lombardi, C. Quitté, *Commutative Algebra: Constructive Methods*, Springer, 2015.
-/

@[expose] public noncomputable section

universe u v

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

variable {A : Type u} [CommRing A]

/-- The base change map `A[X] ⊗[A] P → B ⊗[A] P`. -/
def polyBaseChangeMap (B : Type*) [CommRing B] [Algebra A[X] B] [Algebra A B]
    [IsScalarTower A A[X] B] (P : Type*) [AddCommGroup P] [Module A P] :
    A[X] ⊗[A] P →ₗ[A[X]] B ⊗[A] P :=
  ((AlgebraTensorModule.cancelBaseChange A A[X] B B P).restrictScalars A[X]).toLinearMap ∘ₗ
    TensorProduct.mk A[X] B (A[X] ⊗[A] P) 1

/-- The base change map to a localisation of `A[X]` is a localisation map. -/
instance isLocalizedModule_polyBaseChangeMap (S : Submonoid A[X]) (B : Type*) [CommRing B]
    [Algebra A[X] B] [IsLocalization S B] [Algebra A B] [IsScalarTower A A[X] B]
    (P : Type*) [AddCommGroup P] [Module A P] :
    IsLocalizedModule S (polyBaseChangeMap B P) := by
  unfold polyBaseChangeMap
  infer_instance

/-- An isomorphism `A⟨X⟩ ⊗[A] P ≅ A⟨X⟩ ⊗[A] Q` of finitely generated projective modules
descends to `A[X]_r` for a monic `r`. -/
theorem exists_monic_away_equiv (P Q : Type v) [AddCommGroup P] [Module A P] [Module.Finite A P]
    [Module.Projective A P] [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
    [Module.Projective A Q]
    (α : Localization (monicSubmonoid A) ⊗[A] P ≃ₗ[Localization (monicSubmonoid A)]
      Localization (monicSubmonoid A) ⊗[A] Q) :
    ∃ r : A[X], r.Monic ∧ Nonempty (Localization.Away r ⊗[A] P ≃ₗ[Localization.Away r]
      Localization.Away r ⊗[A] Q) := by
  set S := monicSubmonoid A
  set L := Localization S
  have : Module.FinitePresentation A[X] (A[X] ⊗[A] P) := Module.finitePresentation_of_projective _ _
  have : Module.FinitePresentation A[X] (A[X] ⊗[A] Q) := Module.finitePresentation_of_projective _ _
  obtain ⟨r, hr, l', -⟩ := Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule
    (R := A[X]) (M' := L ⊗[A] P) (N' := L ⊗[A] Q) S
    (polyBaseChangeMap L P) (polyBaseChangeMap L Q)
    { toFun := α
      invFun := α.symm
      map_add' := map_add α
      map_smul' := fun c x => by
        rw [← algebraMap_smul L c x, map_smul, algebraMap_smul]
        rfl
      left_inv := α.left_inv
      right_inv := α.right_inv }
  refine ⟨r, hr, ⟨?_⟩⟩
  exact ((IsLocalizedModule.iso (Submonoid.powers r)
    (polyBaseChangeMap _ P)).extendScalarsOfIsLocalization (Submonoid.powers r)
      (Localization.Away r)).symm ≪≫ₗ l' ≪≫ₗ
    (IsLocalizedModule.iso (Submonoid.powers r)
      (polyBaseChangeMap _ Q)).extendScalarsOfIsLocalization (Submonoid.powers r)
        (Localization.Away r)

/-- `X` is a unit of `A[X]_{X r*}`. -/
theorem isUnit_X_away (r : A[X]) :
    IsUnit (algebraMap A[X] (Localization.Away (X * r.reverse)) X) :=
  isUnit_of_mul_isUnit_left (by
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (X * r.reverse))

/-- The reverse `r*` is a unit of `A[X]_{X r*}`. -/
theorem isUnit_reverse_away (r : A[X]) :
    IsUnit (algebraMap A[X] (Localization.Away (X * r.reverse)) r.reverse) :=
  isUnit_of_mul_isUnit_right (by
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (X * r.reverse))

/-- The substitution `X ↦ X⁻¹` from `A[X]` to `A[X]_{X r*}`, with `r*` the reverse of `r`. -/
def invSubst (r : A[X]) : A[X] →+* Localization.Away (X * r.reverse) :=
  eval₂RingHom (algebraMap A _) ↑(isUnit_X_away r).unit⁻¹

/-- Evaluating at the image of `X` is the algebra map. -/
theorem eval₂_algebraMap_X' {S : Type*} [CommRing S] [Algebra A[X] S] [Algebra A S]
    [IsScalarTower A A[X] S] (p : A[X]) :
    eval₂ (algebraMap A S) (algebraMap A[X] S X) p = algebraMap A[X] S p := by
  have := eval₂_algebraMap_X p (IsScalarTower.toAlgHom A A[X] S)
  simpa using this

/-- The substitution `X ↦ X⁻¹` sends `r` to `r* X⁻ᵈ`, a unit of `A[X]_{X r*}`. -/
theorem isUnit_invSubst (r : A[X]) : IsUnit (invSubst r r) := by
  set u := (isUnit_X_away r).unit
  let _ : Invertible ((↑u⁻¹ : Localization.Away (X * r.reverse))) := Units.invertible _
  have h := eval₂_reverse_mul_pow (algebraMap A (Localization.Away (X * r.reverse))) (↑u⁻¹) r
  rw [invOf_units, inv_inv, IsUnit.unit_spec, eval₂_algebraMap_X'] at h
  change IsUnit (eval₂ _ _ r)
  rw [← h]
  exact (isUnit_reverse_away r).mul ((Units.isUnit _).pow _)

/-- For a monic `r`, `X` and the reverse `r*` are comaximal, `r*` having constant term `1`. -/
theorem isCoprime_X_reverse {r : A[X]} (hr : r.Monic) : IsCoprime (X : A[X]) r.reverse := by
  obtain ⟨k, hk⟩ := X_dvd_sub_C (p := r.reverse)
  rw [coeff_zero_reverse, hr.leadingCoeff, C_1] at hk
  exact ⟨-k, 1, by rw [eq_add_of_sub_eq hk]; ring⟩

/-- Evaluation of an extended module. If `ε : A[X] → A` is a retraction of `C` that factors
through an `A[X]`-algebra `R'` over which `M` becomes `R' ⊗[A] P'`, and `M ≅ A[X] ⊗[A] N`, then
`P' ≅ N`: both are `A ⊗[A[X]] M` along `ε`. -/
theorem nonempty_linearEquiv_of_eval {ε : A[X] →+* A} (hε : ∀ a, ε (C a) = a)
    (R' : Type*) [CommRing R'] [Algebra A[X] R'] [Algebra A R'] [IsScalarTower A A[X] R']
    {ε' : R' →+* A} (hε' : ∀ x, ε' (algebraMap A[X] R' x) = ε x)
    {M : Type*} [AddCommGroup M] [Module A[X] M] {P' : Type*} [AddCommGroup P'] [Module A P']
    (e : R' ⊗[A[X]] M ≃ₗ[R'] R' ⊗[A] P') {N : Type*} [AddCommGroup N] [Module A N]
    (eN : M ≃ₗ[A[X]] A[X] ⊗[A] N) : Nonempty (P' ≃ₗ[A] N) := by
  let _ : Algebra A[X] A := ε.toAlgebra
  let _ : Algebra R' A := ε'.toAlgebra
  have : IsScalarTower A[X] R' A := ⟨fun x y z => by
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    congr 1
    exact hε' x⟩
  have : IsScalarTower A A[X] A := ⟨fun x y z => by
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    congr 1
    exact hε x⟩
  have : IsScalarTower A R' A := ⟨fun x y z => by
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    congr 1
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    change ε' (algebraMap A R' x) = x
    rw [IsScalarTower.algebraMap_apply A A[X] R', hε', Polynomial.algebraMap_eq, hε]⟩
  exact ⟨(AlgebraTensorModule.cancelBaseChange A R' A A P' ≪≫ₗ TensorProduct.lid A P').symm ≪≫ₗ
    (AlgebraTensorModule.congr (LinearEquiv.refl A A) e).symm ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange A[X] R' A A M ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl A A) eN ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange A A[X] A A N ≪≫ₗ TensorProduct.lid A N⟩

/-- **4.4.** Bass: finitely generated projective `A`-modules that become isomorphic over `A⟨X⟩`
are isomorphic (Lombardi–Quitté, Theorem XVI.4.8). -/
theorem nonempty_linearEquiv_of_monicLocalization (P Q : Type v) [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P] [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
    [Module.Projective A Q]
    (h : Nonempty (Localization (monicSubmonoid A) ⊗[A] P ≃ₗ[Localization (monicSubmonoid A)]
      Localization (monicSubmonoid A) ⊗[A] Q)) :
    Nonempty (P ≃ₗ[A] Q) := by
  obtain ⟨α⟩ := h
  obtain ⟨r, hr, ⟨αr⟩⟩ := exists_monic_away_equiv P Q α
  set L := Localization (monicSubmonoid A)
  set g := r.reverse
  set Rf := Localization.Away (X : A[X])
  set Rg := Localization.Away g
  set Rfg := Localization.Away (X * g)
  set Rr := Localization.Away r
  let _ : Algebra Rf Rfg := (IsLocalization.Away.lift X (isUnit_X_away r)).toAlgebra
  let _ : Algebra Rg Rfg := (IsLocalization.Away.lift g (isUnit_reverse_away r)).toAlgebra
  let _ : Algebra Rr Rfg := (IsLocalization.Away.lift r (isUnit_invSubst r)).toAlgebra
  have : IsScalarTower A[X] Rf Rfg := ⟨fun x y z => by
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    congr 1
    exact IsLocalization.Away.lift_eq X (isUnit_X_away r) x⟩
  have : IsScalarTower A[X] Rg Rfg := ⟨fun x y z => by
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    congr 1
    exact IsLocalization.Away.lift_eq g (isUnit_reverse_away r) x⟩
  have : IsScalarTower A Rf Rfg := ⟨fun x y z => by
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    congr 1
    rw [IsScalarTower.algebraMap_apply A A[X] Rf, IsScalarTower.algebraMap_apply A A[X] Rfg]
    exact IsLocalization.Away.lift_eq X (isUnit_X_away r) _⟩
  have : IsScalarTower A Rg Rfg := ⟨fun x y z => by
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    congr 1
    rw [IsScalarTower.algebraMap_apply A A[X] Rg, IsScalarTower.algebraMap_apply A A[X] Rfg]
    exact IsLocalization.Away.lift_eq g (isUnit_reverse_away r) _⟩
  have : IsScalarTower A Rr Rfg := ⟨fun x y z => by
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    congr 1
    rw [IsScalarTower.algebraMap_apply A A[X] Rr]
    refine (IsLocalization.Away.lift_eq r (isUnit_invSubst r) _).trans ?_
    simp only [invSubst, coe_eval₂RingHom, Polynomial.algebraMap_eq, eval₂_C]
    rfl⟩
  let β : Rfg ⊗[Rf] (Rf ⊗[A] P) ≃ₗ[Rfg] Rfg ⊗[Rg] (Rg ⊗[A] Q) :=
    AlgebraTensorModule.cancelBaseChange A Rf Rfg Rfg P ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange A Rr Rfg Rfg P).symm ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl Rfg Rfg) αr ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange A Rr Rfg Rfg Q ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange A Rg Rfg Rfg Q).symm
  obtain ⟨M, _, _, _, _, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    exists_finite_projective_glue (Rf := Rf) (Rg := Rg) (Rfg := Rfg) (isCoprime_X_reverse hr)
      (Rf ⊗[A] P) (Rg ⊗[A] Q) β
  have hXL : IsUnit (algebraMap A[X] L X) :=
    IsLocalization.map_units L (⟨X, monic_X⟩ : monicSubmonoid A)
  let _ : Algebra Rf L := (IsLocalization.Away.lift X hXL).toAlgebra
  have : IsScalarTower A[X] Rf L := ⟨fun x y z => by
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    congr 1
    exact IsLocalization.Away.lift_eq X hXL x⟩
  have : IsScalarTower A Rf L := ⟨fun x y z => by
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    congr 1
    rw [IsScalarTower.algebraMap_apply A A[X] Rf, IsScalarTower.algebraMap_apply A A[X] L]
    exact IsLocalization.Away.lift_eq X hXL _⟩
  have : Small.{max u v} P := ⟨⟨ULift.{u} P, ⟨Equiv.ulift.symm⟩⟩⟩
  have hext : IsExtendedFrom A L (L ⊗[A[X]] M) := .of_linearEquiv_tensor
    ((AlgebraTensorModule.cancelBaseChange A[X] Rf L L M).symm ≪≫ₗ
      AlgebraTensorModule.congr (LinearEquiv.refl L L) e₁ ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange A Rf L L P)
  obtain ⟨N, _, _, ⟨eN⟩⟩ := isExtendedFrom_of_isExtendedFrom_monicLocalization M hext
  have h1 : IsUnit ((evalRingHom (1 : A)) X) := by simp
  have h0 : IsUnit ((evalRingHom (0 : A)) g) := by
    rw [coe_evalRingHom, ← coeff_zero_eq_eval_zero, coeff_zero_reverse, hr.leadingCoeff]
    exact isUnit_one
  obtain ⟨eP⟩ := nonempty_linearEquiv_of_eval (ε := evalRingHom 1) (fun a => eval_C) Rf
    (ε' := IsLocalization.Away.lift X h1) (IsLocalization.Away.lift_eq X h1) e₁ eN
  obtain ⟨eQ⟩ := nonempty_linearEquiv_of_eval (ε := evalRingHom 0) (fun a => eval_C) Rg
    (ε' := IsLocalization.Away.lift g h0) (IsLocalization.Away.lift_eq g h0) e₂ eN
  exact ⟨eP ≪≫ₗ eQ.symm⟩

/-- **4.5.** Quillen's form of Horrocks' theorem: over any commutative ring `A`, a finitely
generated projective `A[X]`-module that becomes free over `A⟨X⟩` is free (Quillen 1976,
Theorem 3, p. 169). -/
theorem free_of_free_monicLocalization (P : Type v) [AddCommGroup P] [Module A[X] P]
    [Module.Finite A[X] P] [Module.Projective A[X] P]
    (h : Module.Free (Localization (monicSubmonoid A))
      (Localization (monicSubmonoid A) ⊗[A[X]] P)) :
    Module.Free A[X] P := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : Subsingleton P := Module.subsingleton A[X] P
    infer_instance
  set L := Localization (monicSubmonoid A)
  have : Nontrivial L :=
    (IsLocalization.injective L (monicSubmonoid_le_nonZeroDivisors (A := A))).nontrivial
  set ι := Module.Free.ChooseBasisIndex L (L ⊗[A[X]] P)
  let b := Module.Free.chooseBasis L (L ⊗[A[X]] P)
  have : Finite ι := Module.Finite.finite_basis b
  obtain ⟨N, _, _, ⟨e⟩⟩ := isExtendedFrom_of_isExtendedFrom_monicLocalization P
    ⟨ι →₀ A, _, _, ⟨b.repr ≪≫ₗ (finsuppScalarRight A L L ι).symm⟩⟩
  let _ : Algebra A[X] A := (evalRingHom 0).toAlgebra
  have := isScalarTower_evalZero (A := A) rfl
  let eN : A ⊗[A[X]] P ≃ₗ[A] N := AlgebraTensorModule.congr (LinearEquiv.refl A A) e ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange A A[X] A A N ≪≫ₗ TensorProduct.lid A N
  let eU : ULift.{u} N ≃ₗ[A] A ⊗[A[X]] P := ULift.moduleEquiv ≪≫ₗ eN.symm
  have : Module.Finite A (ULift.{u} N) := Module.Finite.equiv eU.symm
  have : Module.Projective A (ULift.{u} N) := Module.Projective.of_equiv eU.symm
  obtain ⟨f⟩ := nonempty_linearEquiv_of_monicLocalization (ULift.{u} N) (ι →₀ A)
    ⟨AlgebraTensorModule.congr (LinearEquiv.refl L L) ULift.moduleEquiv ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange A A[X] L L N).symm ≪≫ₗ
      AlgebraTensorModule.congr (LinearEquiv.refl L L) e.symm ≪≫ₗ
      b.repr ≪≫ₗ (finsuppScalarRight A L L ι).symm⟩
  have : Module.Free A N := Module.Free.of_equiv (f.symm ≪≫ₗ ULift.moduleEquiv)
  exact Module.Free.of_equiv e.symm

end LeanPool.QuillenSuslin
