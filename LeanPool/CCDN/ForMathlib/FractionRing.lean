/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Fraction fields of localizations, polynomial rings and finite extensions

## Main results

* `IsFractionRing.liftOfLocalization`: a nonzero localization of a domain embeds compatibly in any
  fraction field of the domain, which is then a fraction field of the localization
  (`IsFractionRing.isFractionRing_liftOfLocalization`).
* `MvPolynomial.coeffFractionRingEmbedding`: a fraction field of a coefficient domain `A` embeds
  canonically in a fraction field of `MvPolynomial σ A`, compatibly with `A` and its ground field.
* `MvPolynomial.fractionRingCoeffMap`, `MvPolynomial.isFractionRing_fractionRingCoeffMap`:
  enlarging the coefficients to their fraction field does not change the fraction field of a
  polynomial ring.
* `IsFractionRing.exists_ne_zero_mul_mem_range_of_finite`: a finite extension of domains with a
  common fraction field has a nonzero conductor element.
-/

@[expose] public section

noncomputable section

namespace IsLocalization

/-- The elements of the submonoid of a nontrivial localization are nonzero. -/
theorem submonoid_coe_ne_zero {R S : Type*}
    [CommRing R] [CommRing S] [Nontrivial S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (y : M) : (y : R) ≠ 0 := by
  intro hy
  have h := (IsLocalization.map_units S y).ne_zero
  exact h (by rw [hy,map_zero])

end IsLocalization

namespace IsFractionRing

/-- A localization of a domain embeds compatibly in any fraction field of the domain. -/
def liftOfLocalization {R S F : Type*}
    [CommRing R] [CommRing S] [Nontrivial S]
    [Field F] [Algebra R S] [Algebra R F]
    (M : Submonoid R) [IsLocalization M S] [IsFractionRing R F] : S →+* F :=
  IsLocalization.lift (fun y : M => isUnit_iff_ne_zero.mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr
      (IsLocalization.submonoid_coe_ne_zero (S := S) M y)))

/-- The embedding `liftOfLocalization M` of the localization `S` into a fraction field `F` of `R`
restricts to the algebra map `R → F` along `R → S`. -/
theorem liftOfLocalization_comp {R S F : Type*}
    [CommRing R] [CommRing S] [Nontrivial S]
    [Field F] [Algebra R S] [Algebra R F]
    (M : Submonoid R) [IsLocalization M S] [IsFractionRing R F] :
    (liftOfLocalization (S := S) (F := F) M).comp (algebraMap R S) =
      algebraMap R F := IsLocalization.lift_comp _

/-- A fraction field of a domain is a fraction field of each of its nonzero localizations. -/
theorem isFractionRing_liftOfLocalization {R S F : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [Nontrivial S]
    [Field F] [Algebra R S] [Algebra R F]
    (M : Submonoid R) [IsLocalization M S] [IsFractionRing R F] :
    let : Algebra S F := (liftOfLocalization (S := S) (F := F) M).toAlgebra
    IsFractionRing S F := by
  let : Algebra S F := (liftOfLocalization (S := S) (F := F) M).toAlgebra
  let : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq'
    (liftOfLocalization_comp M).symm
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S F

end IsFractionRing

namespace MvPolynomial

/-- The coefficients embed in a fraction field of a polynomial ring over a domain. -/
theorem algebraMap_injective_of_isFractionRing
    {A E σ : Type*} [CommRing A] [Field E]
    [Algebra A E] [Algebra (MvPolynomial σ A) E]
    [IsScalarTower A (MvPolynomial σ A) E]
    [IsFractionRing (MvPolynomial σ A) E] :
    Function.Injective (algebraMap A E) := by
  rw [IsScalarTower.algebraMap_eq A (MvPolynomial σ A) E]
  exact (IsFractionRing.injective (MvPolynomial σ A) E).comp (C_injective σ A)

variable {K A F E σ : Type*} [Field K] [CommRing A]
  [Field F] [Field E] [Algebra K A] [Algebra K F] [Algebra K E]
  [Algebra A F] [IsFractionRing A F] [IsScalarTower K A F]
  [Algebra A E] [IsScalarTower K A E]
  [Algebra (MvPolynomial σ A) E] [IsScalarTower A (MvPolynomial σ A) E]
  [IsFractionRing (MvPolynomial σ A) E]

/-- The embedding of a fraction field of the coefficients into a fraction field of the polynomial
ring. -/
def coeffFractionRingEmbedding : F →ₐ[K] E :=
  IsFractionRing.liftAlgHom (g := IsScalarTower.toAlgHom K A E)
    (algebraMap_injective_of_isFractionRing (σ := σ))

/-- The embedding `coeffFractionRingEmbedding` of a fraction field `F` of `A` into `E` sends the
image of `x : A` in `F` to the image of `x` in `E`. -/
lemma coeffFractionRingEmbedding_algebraMap (x : A) :
    coeffFractionRingEmbedding (K := K) (A := A) (E := E) (σ := σ)
      (algebraMap A F x) =
      algebraMap A E x :=
  IsFractionRing.lift_algebraMap
    (algebraMap_injective_of_isFractionRing (A := A) (E := E) (σ := σ)) x

/-- With the `F`-algebra structure on `E` given by `coeffFractionRingEmbedding`, the rings `A`, `F`
and `E` form a scalar tower. -/
theorem isScalarTower_coeffFractionRingEmbedding :
    let : Algebra F E :=
      (coeffFractionRingEmbedding (K := K) (A := A) (F := F) (E := E)
        (σ := σ)).toRingHom.toAlgebra
    IsScalarTower A F E := by
  let : Algebra F E :=
    (coeffFractionRingEmbedding (K := K) (A := A) (F := F) (E := E)
      (σ := σ)).toRingHom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  exact (coeffFractionRingEmbedding_algebraMap
    (K := K) (F := F) (E := E) (σ := σ) x).symm

end MvPolynomial

namespace MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Extend polynomial coefficients inside the ambient fraction field. -/
def fractionRingCoeffMap
    {A K F σ : Type*} [CommRing A] [Field K] [Field F]
    [Algebra K F]
    [Algebra (MvPolynomial σ A) F] : MvPolynomial σ K →+* F :=
  eval₂Hom (algebraMap K F) (fun i => algebraMap (MvPolynomial σ A) F (X i))

/-- Composing `fractionRingCoeffMap` with the coefficient map `MvPolynomial σ A → MvPolynomial σ K`
gives the algebra map `MvPolynomial σ A → F`. -/
lemma fractionRingCoeffMap_comp
    {A K F σ : Type*} [CommRing A] [Field K] [Field F]
    [Algebra A K] [Algebra A F] [Algebra K F]
    [IsScalarTower A K F]
    [Algebra (MvPolynomial σ A) F] [IsScalarTower A (MvPolynomial σ A) F] :
    (fractionRingCoeffMap (A := A) (K := K) (F := F) (σ := σ)).comp
      (map (algebraMap A K)) = algebraMap (MvPolynomial σ A) F := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,map_C,fractionRingCoeffMap,eval₂Hom_C,
      ← IsScalarTower.algebraMap_apply]
    exact IsScalarTower.algebraMap_apply A (MvPolynomial σ A) F a
  · intro i
    simp [fractionRingCoeffMap]

/-- The constructed coefficient extension realizes the same
ambient field as a fraction field after coefficient localization. -/
theorem isFractionRing_fractionRingCoeffMap
    {A K F σ : Type*} [CommRing A] [IsDomain A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra A F] [Algebra K F] [IsScalarTower A K F]
    [Algebra (MvPolynomial σ A) F] [IsScalarTower A (MvPolynomial σ A) F]
    [IsFractionRing (MvPolynomial σ A) F] :
    let : Algebra (MvPolynomial σ K) F :=
      (fractionRingCoeffMap (A := A) (K := K) (F := F) (σ := σ)).toAlgebra
    IsFractionRing (MvPolynomial σ K) F := by
  let : Algebra (MvPolynomial σ K) F :=
    (fractionRingCoeffMap (A := A) (K := K) (F := F) (σ := σ)).toAlgebra
  let : IsScalarTower (MvPolynomial σ A) (MvPolynomial σ K) F :=
    IsScalarTower.of_algebraMap_eq' (fractionRingCoeffMap_comp).symm
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    ((nonZeroDivisors A).map (C (σ := σ))) (MvPolynomial σ K) F

end MvPolynomial

namespace IsFractionRing

/-- A common nonzero denominator for a finite birational extension. -/
theorem exists_ne_zero_mul_mem_range_of_finite
    (R A F : Type*) [CommRing R] [IsDomain R] [CommRing A] [Field F]
    [Algebra R A] [Algebra R F] [Algebra A F] [IsScalarTower R A F]
    [IsFractionRing R F] [IsFractionRing A F] [Module.Finite R A] :
    ∃ c : R, c ≠ 0 ∧ ∀ a : A, ∃ r : R,
      algebraMap R A r = algebraMap R A c * a := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R A).FG)
  let φ : A →ₐ[R] F := IsScalarTower.toAlgHom R A F
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors R) s (fun a => φ a)
  let N : Submodule R A :=
    Submodule.comap ((c : R) • φ.toLinearMap) (LinearMap.range (Algebra.linearMap R F))
  have hspan : Submodule.span R (s : Set A) ≤ N := by
    apply Submodule.span_le.mpr
    intro a ha
    exact hc a ha
  have hall (a : A) : a ∈ N := by
    apply hspan
    rw [hs]
    trivial
  refine ⟨c, mem_nonZeroDivisors_iff_ne_zero.mp c.2, ?_⟩
  intro a
  obtain ⟨r, hr⟩ := hall a
  refine ⟨r, ?_⟩
  apply IsFractionRing.injective A F
  change algebraMap A F (algebraMap R A r) =
    algebraMap A F (algebraMap R A (c : R) * a)
  rw [map_mul, ← IsScalarTower.algebraMap_apply R A F,
    ← IsScalarTower.algebraMap_apply R A F]
  simpa only [LinearMap.smul_apply, Algebra.smul_def, Algebra.linearMap_apply,
    AlgHom.toLinearMap_apply, φ, IsScalarTower.toAlgHom_apply] using hr

end IsFractionRing

end
