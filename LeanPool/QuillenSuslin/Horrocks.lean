/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.HorrocksLocal
public import LeanPool.QuillenSuslin.QuillenPatching

import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.LocalRing.Module

/-!
# The affine Horrocks theorem

A finitely generated projective `A[X]`-module `P` such that `A⟨X⟩ ⊗[A[X]] P` is extended from
`A` is extended from `A` (Lombardi–Quitté, Theorem XVI.4.7). Writing `A⟨X⟩ ⊗[A[X]] P ≅
A⟨X⟩ ⊗[A] N`, the module `N` is finitely generated and flat by faithfully flat descent along
`A → A⟨X⟩`, hence free after localising at a maximal ideal `m`; so the base change of `P` to
`A_m[X]` becomes free over `A_m⟨X⟩`, is free by the local Horrocks theorem, and Quillen patching
concludes.

## Main results

* `monicLocalizationAlgebra`: the map `A⟨X⟩ → B⟨X⟩` for an `A`-algebra `B`.
* `isExtendedFrom_of_free`: a free `B[X]`-module is extended from `B`.
* `isExtendedFrom_of_isExtendedFrom_monicLocalization`: the affine Horrocks theorem.

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
* H. Lombardi, C. Quitté, *Commutative Algebra: Constructive Methods*, Springer, 2015.
-/

@[expose] public noncomputable section

universe u v

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

variable {A : Type u} [CommRing A]

/-- The map `A⟨X⟩ → B⟨X⟩` induced by an `A`-algebra `B`. -/
@[instance_reducible]
def monicLocalizationAlgebra (B : Type*) [CommRing B] [Algebra A B] :
    Algebra (Localization (monicSubmonoid A)) (Localization (monicSubmonoid B)) :=
  letI := Polynomial.algebra A B
  (IsLocalization.lift (M := monicSubmonoid A)
    (g := algebraMap A[X] (Localization (monicSubmonoid B))) fun s => by
      rw [IsScalarTower.algebraMap_apply A[X] B[X]]
      exact IsLocalization.map_units _ (⟨_, s.2.map (algebraMap A B)⟩ : monicSubmonoid B)).toAlgebra

attribute [local instance] Polynomial.algebra monicLocalizationAlgebra

/-- The tower `A[X] → A⟨X⟩ → B⟨X⟩`. -/
theorem isScalarTower_monicLocalization (B : Type*) [CommRing B] [Algebra A B] :
    IsScalarTower A[X] (Localization (monicSubmonoid A)) (Localization (monicSubmonoid B)) :=
  ⟨fun x y z => by
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    congr 1
    exact IsLocalization.lift_eq _ x⟩

attribute [local instance] isScalarTower_monicLocalization

/-- The tower `A → A⟨X⟩ → B⟨X⟩`. -/
theorem isScalarTower_monicLocalization' (B : Type*) [CommRing B] [Algebra A B] :
    IsScalarTower A (Localization (monicSubmonoid A)) (Localization (monicSubmonoid B)) :=
  ⟨fun a y z => by
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    congr 1
    rw [IsScalarTower.algebraMap_apply A A[X] (Localization (monicSubmonoid A)),
      ← IsScalarTower.algebraMap_apply A[X] (Localization (monicSubmonoid A)),
      ← IsScalarTower.algebraMap_apply A A[X] (Localization (monicSubmonoid B))]⟩

attribute [local instance] isScalarTower_monicLocalization'

/-- A free `B[X]`-module is extended from `B`. -/
theorem isExtendedFrom_of_free {B : Type u} [CommRing B] {M : Type v} [AddCommGroup M]
    [Module B[X] M] [Module.Free B[X] M] : IsExtendedFrom B B[X] M :=
  .of_polynomial_linearEquiv ((Module.Free.chooseBasis B[X] M).repr ≪≫ₗ
    (finsuppScalarRight B B[X] B[X] _).symm)

/-- If `A⟨X⟩ ⊗[A[X]] P ≅ A⟨X⟩ ⊗[A] N` and `B ⊗[A] N` is free over the `A`-algebra `B`, then the
base change of `P` to `B[X]` becomes free over `B⟨X⟩`. -/
theorem free_monicLocalization_baseChange (B : Type u) [CommRing B] [Algebra A B] (P : Type v)
    [AddCommGroup P] [Module A[X] P] (N : Type*) [AddCommGroup N] [Module A N]
    (e : Localization (monicSubmonoid A) ⊗[A[X]] P ≃ₗ[Localization (monicSubmonoid A)]
      Localization (monicSubmonoid A) ⊗[A] N) [Module.Free B (B ⊗[A] N)] :
    Module.Free (Localization (monicSubmonoid B))
      (Localization (monicSubmonoid B) ⊗[B[X]] (B[X] ⊗[A[X]] P)) :=
  Module.Free.of_equiv
    (AlgebraTensorModule.cancelBaseChange A B (Localization (monicSubmonoid B))
      (Localization (monicSubmonoid B)) N ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange A (Localization (monicSubmonoid A))
      (Localization (monicSubmonoid B)) (Localization (monicSubmonoid B)) N).symm ≪≫ₗ
    (AlgebraTensorModule.congr (LinearEquiv.refl _ _) e).symm ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange A[X] (Localization (monicSubmonoid A))
      (Localization (monicSubmonoid B)) (Localization (monicSubmonoid B)) P ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange A[X] B[X] (Localization (monicSubmonoid B))
      (Localization (monicSubmonoid B)) P).symm)

/-- **4.3.** Affine Horrocks' theorem: a finitely generated projective `A[X]`-module that becomes
extended from `A` over `A⟨X⟩` is extended from `A` (Lombardi–Quitté, Theorem XVI.4.7). -/
theorem isExtendedFrom_of_isExtendedFrom_monicLocalization (P : Type v) [AddCommGroup P]
    [Module A[X] P] [Module.Finite A[X] P] [Module.Projective A[X] P]
    (h : IsExtendedFrom A (Localization (monicSubmonoid A))
      (Localization (monicSubmonoid A) ⊗[A[X]] P)) :
    IsExtendedFrom A A[X] P := by
  obtain ⟨N, _, _, ⟨e⟩⟩ := h
  set L := Localization (monicSubmonoid A)
  have : Module.Finite L (L ⊗[A] N) := Module.Finite.equiv e
  have : Module.Finite A N := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat L
  have : Module.Flat L (L ⊗[A] N) := Module.Flat.of_linearEquiv e.symm
  have : Module.Flat A N := Module.Flat.of_flat_tensorProduct A N L
  have : Module.FinitePresentation A[X] P := Module.finitePresentation_of_projective _ _
  refine isExtendedFrom_of_forall_isMaximal P fun m _ => ?_
  have : Module.Free (Localization.AtPrime m) (Localization.AtPrime m ⊗[A] N) :=
    Module.free_of_flat_of_isLocalRing
  have := free_monicLocalization_baseChange (Localization.AtPrime m) P N e
  have : Module.Free (Localization.AtPrime m)[X] ((Localization.AtPrime m)[X] ⊗[A[X]] P) :=
    free_of_free_monicLocalization_of_isLocalRing _ this
  exact isExtendedFrom_of_free

end LeanPool.QuillenSuslin
