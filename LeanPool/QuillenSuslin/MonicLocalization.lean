/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

import Mathlib.RingTheory.TotallySplit

/-!
# The monic localisation `A⟨X⟩`

For a commutative ring `A`, the monic polynomials form a submonoid `monicSubmonoid A` of `A[X]`,
and `A⟨X⟩` is the localisation `Localization (monicSubmonoid A)` (Quillen 1976, p. 169;
Lombardi–Quitté, Notation XVI.4.2).

## Main results

* `monicSubmonoid`: the submonoid of monic polynomials.
* `faithfullyFlat_monicLocalization`: `A⟨X⟩` is a faithfully flat `A`-algebra.
* `isField_monicLocalization`: for a field `k`, `k⟨X⟩` is a field (Quillen 1976, Lemma 2).

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
* H. Lombardi, C. Quitté, *Commutative Algebra: Constructive Methods*, Springer, 2015.
-/

@[expose] public section

universe u

open Polynomial

namespace LeanPool.QuillenSuslin

/-- The monic polynomials of `A[X]`, a submonoid. -/
def monicSubmonoid (A : Type u) [CommRing A] : Submonoid A[X] where
  carrier := {p | p.Monic}
  mul_mem' hp hq := Monic.mul hp hq
  one_mem' := monic_one

variable {A : Type u} [CommRing A]

@[simp]
theorem mem_monicSubmonoid {p : A[X]} : p ∈ monicSubmonoid A ↔ p.Monic := Iff.rfl

theorem monicSubmonoid_le_nonZeroDivisors : monicSubmonoid A ≤ nonZeroDivisors A[X] :=
  fun _ hp => Monic.mem_nonZeroDivisors hp

/-- A prime ideal `p` of `A` extends to a prime `p[X]` of `A[X]` containing no monic
polynomial. -/
theorem disjoint_monicSubmonoid_map_C {I : Ideal A} (hI : I ≠ ⊤) :
    Disjoint (monicSubmonoid A : Set A[X]) (I.map C : Ideal A[X]) := by
  rw [Set.disjoint_left]
  intro p hp hpI
  have h := (Ideal.mem_map_C_iff.mp hpI) p.natDegree
  rw [show p.coeff p.natDegree = 1 from hp] at h
  exact hI ((Ideal.eq_top_iff_one I).mpr h)

instance isDomain_monicLocalization [IsDomain A] :
    IsDomain (Localization (monicSubmonoid A)) :=
  IsLocalization.isDomain_localization monicSubmonoid_le_nonZeroDivisors

/-- `A⟨X⟩` is a faithfully flat `A`-algebra: it is flat, being a localisation of the free
`A`-module `A[X]`, and every prime of `A` lies under the extension of `p[X]` (Lombardi–Quitté,
Theorem VIII.6.1). -/
instance faithfullyFlat_monicLocalization :
    Module.FaithfullyFlat A (Localization (monicSubmonoid A)) := by
  refine Module.FaithfullyFlat.of_comap_surjective ?_
  intro p
  set L := Localization (monicSubmonoid A)
  have hd := disjoint_monicSubmonoid_map_C (A := A) p.isPrime.ne_top
  have hP : (p.asIdeal.map (C : A →+* A[X])).IsPrime :=
    @Ideal.isPrime_map_C_of_isPrime _ _ _ p.isPrime
  refine ⟨⟨(p.asIdeal.map (C : A →+* A[X])).map (algebraMap A[X] L),
    IsLocalization.isPrime_of_isPrime_disjoint (monicSubmonoid A) L _ hP hd⟩, ?_⟩
  ext a
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  rw [IsScalarTower.algebraMap_apply A A[X] L, ← Ideal.mem_comap,
    ← Ideal.under_def, IsLocalization.under_map_of_isPrime_disjoint (monicSubmonoid A) L hP hd,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Ideal.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h n
    rw [coeff_C]
    split_ifs
    · exact h
    · exact p.asIdeal.zero_mem

/-- For a field `k`, the localisation `k⟨X⟩` of `k[X]` at the monic polynomials is a field
(Quillen 1976, Lemma 2, p. 169). -/
theorem isField_monicLocalization (k : Type u) [Field k] :
    IsField (Localization (monicSubmonoid k)) := by
  refine ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩
  obtain ⟨⟨p, s⟩, rfl⟩ := IsLocalization.mk'_surjective (monicSubmonoid k) x
  have hp : p ≠ 0 := by
    rintro rfl
    exact hx (by simp)
  have hm : (C (p.leadingCoeff)⁻¹ * p).Monic := monic_C_mul_of_mul_leadingCoeff_eq_one
    (inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hp))
  refine ⟨IsLocalization.mk' _ ((s : k[X]) * C (p.leadingCoeff)⁻¹)
    (⟨_, hm⟩ : monicSubmonoid k), ?_⟩
  rw [← IsLocalization.mk'_mul]
  convert IsLocalization.mk'_self'' (M := monicSubmonoid k) (S := Localization (monicSubmonoid k))
    (x := s * ⟨_, hm⟩) using 2
  simp only [Submonoid.coe_mul]
  ring
end LeanPool.QuillenSuslin

