/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.PatchingTwo


/-!
# The Quillen ideal

For a finitely presented `A[X]`-module `M`, the elements `a ∈ A` such that `M` becomes extended
after inverting `a` form an ideal of `A` (Quillen 1976, proof of Theorem 1, p. 168). Closure
under multiples is base change; closure under sums is the patching step over two comaximal
localisations, applied over `A_{a+b}`.

## Main results

* `IsExtendedAfter.of_algebra`: extension is preserved by further base change.
* `isExtendedAfter_add`: closure under sums.
* `exists_ideal_isExtendedAfter_away`: the Quillen ideal.

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
-/

@[expose] public noncomputable section

universe u v

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A[X] M]

/-- A base change `B[X] ⊗[A[X]] M` isomorphic to `B[X] ⊗[A] N` is extended from `B`. -/
theorem isExtendedAfter_of_equiv {B : Type*} [CommRing B] [Algebra A B] {N : Type*}
    [AddCommGroup N] [Module A N]
    (u : (B[X] ⊗[A] N) ≃ₗ[B[X]] (letI := Polynomial.algebra A B; B[X] ⊗[A[X]] M)) :
    IsExtendedAfter A B M := by
  let _ := Polynomial.algebra A B
  exact .of_polynomial_linearEquiv (A := B)
    (u.symm ≪≫ₗ (AlgebraTensorModule.cancelBaseChange A B B[X] B[X] N).symm)

/-- Extension after base change to `B` is preserved by any further base change `B → B'`. -/
theorem IsExtendedAfter.of_algebra {B B' : Type*} [CommRing B] [CommRing B'] [Algebra A B]
    [Algebra A B'] [Algebra B B'] [IsScalarTower A B B'] (h : IsExtendedAfter A B M) :
    IsExtendedAfter A B' M := by
  obtain ⟨u, -⟩ := exists_normalized_equiv A M B h
  exact isExtendedAfter_of_equiv (baseChangeEquiv (B' := B') u)

/-- For `A → C → D`, extension of `M` after base change to `D` is extension of `C[X] ⊗[A[X]] M`
after base change from `C` to `D`. -/
theorem IsExtendedAfter.restrict {C D : Type*} [CommRing C] [CommRing D] [Algebra A C]
    [Algebra A D] [Algebra C D] [IsScalarTower A C D] (h : IsExtendedAfter A D M) :
    letI := Polynomial.algebra A C
    IsExtendedAfter C D (C[X] ⊗[A[X]] M) := by
  let _ := Polynomial.algebra A C
  let _ := Polynomial.algebra A D
  let _ := Polynomial.algebra C D
  exact IsExtendedFrom.of_polynomial_equiv (A := D) h
    (AlgebraTensorModule.cancelBaseChange A[X] C[X] D[X] D[X] M)

/-- Over the zero ring every module is extended. -/
theorem isExtendedAfter_of_subsingleton {B : Type*} [CommRing B] [Algebra A B] [Subsingleton B] :
    IsExtendedAfter A B M := by
  let _ := Polynomial.algebra A B
  have : Subsingleton (B[X] ⊗[A] PUnit.{1}) := Module.subsingleton B[X] _
  have : Subsingleton (B[X] ⊗[A[X]] M) := Module.subsingleton B[X] _
  exact isExtendedAfter_of_equiv (N := PUnit.{1}) (LinearEquiv.ofSubsingleton _ _)

/-- If `a ∈ A` becomes a unit in an `A`-algebra `D` and `M` is extended after inverting `a`,
then `M` is extended after base change to `D`. -/
theorem IsExtendedAfter.of_isUnit {a : A} {D : Type*} [CommRing D] [Algebra A D]
    (h : IsExtendedAfter A (Localization.Away a) M) (hu : IsUnit (algebraMap A D a)) :
    IsExtendedAfter A D M := by
  let _ : Algebra (Localization.Away a) D := (IsLocalization.Away.lift a hu).toAlgebra
  have : IsScalarTower A (Localization.Away a) D :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq a hu x).symm
  exact h.of_algebra

/-- The algebra structure `Away x → Away y` for `x ∣ y`, with its scalar tower over `A`. -/
theorem exists_algebra_away {x y : A} (h : x ∣ y) :
    ∃ _ : Algebra (Localization.Away x) (Localization.Away y),
      IsScalarTower A (Localization.Away x) (Localization.Away y) := by
  have hu : IsUnit (algebraMap A (Localization.Away y) x) := IsLocalization.Away.isUnit_of_dvd y h
  let _ : Algebra (Localization.Away x) (Localization.Away y) :=
    (IsLocalization.Away.lift x hu).toAlgebra
  exact ⟨inferInstance, IsScalarTower.of_algebraMap_eq fun z =>
    (IsLocalization.Away.lift_eq x hu z).symm⟩

/-- Two algebra maps out of `A_x` that agree on `A` agree. -/
theorem isScalarTower_of_away {x : A} {S T : Type*} [CommRing S] [CommRing T] [Algebra A S]
    [Algebra A T] [Algebra (Localization.Away x) S] [Algebra (Localization.Away x) T]
    [Algebra S T] [IsScalarTower A (Localization.Away x) S]
    [IsScalarTower A (Localization.Away x) T] [IsScalarTower A S T] :
    IsScalarTower (Localization.Away x) S T := by
  refine IsScalarTower.of_algebraMap_eq fun z => ?_
  have h : algebraMap (Localization.Away x) T =
      (algebraMap S T).comp (algebraMap (Localization.Away x) S) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers x) ?_
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, ← IsScalarTower.algebraMap_apply]
  exact RingHom.congr_fun h z

/-- **Closure of the Quillen ideal under sums.** -/
theorem isExtendedAfter_add [Module.FinitePresentation A[X] M] {a b : A}
    (ha : IsExtendedAfter A (Localization.Away a) M)
    (hb : IsExtendedAfter A (Localization.Away b) M) :
    IsExtendedAfter A (Localization.Away (a + b)) M := by
  let C := Localization.Away (a + b)
  let Da := Localization.Away (a * (a + b))
  let Db := Localization.Away (b * (a + b))
  let Dab := Localization.Away (a * b * (a + b))
  obtain ⟨_, _⟩ := exists_algebra_away (A := A) (dvd_mul_left (a + b) a)
  obtain ⟨_, _⟩ := exists_algebra_away (A := A) (dvd_mul_left (a + b) b)
  obtain ⟨_, _⟩ := exists_algebra_away (A := A) (dvd_mul_left (a + b) (a * b))
  obtain ⟨_, _⟩ := exists_algebra_away (A := A)
    (show a * (a + b) ∣ a * b * (a + b) from ⟨b, by ring⟩)
  obtain ⟨_, _⟩ := exists_algebra_away (A := A)
    (show b * (a + b) ∣ a * b * (a + b) from ⟨a, by ring⟩)
  have : IsScalarTower C Da Dab := isScalarTower_of_away
  have : IsScalarTower C Db Dab := isScalarTower_of_away
  have : IsLocalization.Away (algebraMap A C a) Da :=
    isLocalization_away_algebraMap_of_mul a (a + b)
  have : IsLocalization.Away (algebraMap A C b) Db :=
    isLocalization_away_algebraMap_of_mul b (a + b)
  have : IsLocalization.Away (algebraMap A C a * algebraMap A C b) Dab := by
    rw [← map_mul]
    exact isLocalization_away_algebraMap_of_mul (a * b) (a + b)
  have hcop : IsCoprime (algebraMap A C a) (algebraMap A C b) := by
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := C) (a + b)
    refine ⟨↑u⁻¹, ↑u⁻¹, ?_⟩
    rw [← mul_add, ← map_add, ← hu, Units.inv_mul]
  let _ := Polynomial.algebra A C
  obtain ⟨e⟩ := nonempty_linearEquiv_fibre_of_isCoprime (A := C) (Bab := Dab)
    (C[X] ⊗[A[X]] M) hcop
    (IsExtendedAfter.restrict (C := C)
      (ha.of_isUnit (D := Da)
        (IsLocalization.Away.isUnit_of_dvd _ (dvd_mul_right a (a + b)))))
    (IsExtendedAfter.restrict (C := C)
      (hb.of_isUnit (D := Db)
        (IsLocalization.Away.isUnit_of_dvd _ (dvd_mul_right b (a + b)))))
  exact IsExtendedFrom.of_polynomial_linearEquiv (A := C) e.symm

variable (M) in
/-- **3.3.** The Quillen ideal: for a finitely presented `A[X]`-module `M`, the `a ∈ A` such that
`M_a` is extended from `A_a` form an ideal (Quillen 1976, proof of Theorem 1, p. 168). -/
theorem exists_ideal_isExtendedAfter_away [Module.FinitePresentation A[X] M] :
    ∃ I : Ideal A, ∀ a : A, a ∈ I ↔ IsExtendedAfter A (Localization.Away a) M :=
  ⟨{ carrier := {a | IsExtendedAfter A (Localization.Away a) M}
     add_mem' := isExtendedAfter_add
     zero_mem' := by
       have : Subsingleton (Localization.Away (0 : A)) :=
         IsLocalization.subsingleton (M := Submonoid.powers (0 : A)) (Submonoid.mem_powers 0)
       exact isExtendedAfter_of_subsingleton
     smul_mem' := fun c a ha =>
       IsExtendedAfter.of_isUnit ha (IsLocalization.Away.isUnit_of_dvd _ (dvd_mul_left a c)) },
    fun _ => Iff.rfl⟩

end LeanPool.QuillenSuslin

