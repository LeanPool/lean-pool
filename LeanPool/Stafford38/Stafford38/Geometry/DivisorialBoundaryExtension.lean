/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.AsymptoticDivisorExistence
public import LeanPool.Stafford38.Stafford38.Geometry.RetainedDVRCore
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.AsSubring


/-!
# Discrete boundary places in finite extensions

This file closes the valuation-theoretic extension step whenever the ambient
function field is finite separable over the fraction field of the chosen DVR.
The construction is the classical one: take the integral closure, choose a
prime above the maximal ideal, and localize.  Mathlib proves that the integral
closure is Dedekind and that its localization at a nonzero prime is a DVR.

The resulting localization is realized as an actual subring of the ambient
field, so the theorem produces a `ValuationSubring`, not merely an abstract
local ring.  The distinguished nonzero nonunit remains a nonunit at the
chosen place.

For a general finitely generated extension, the remaining reduction is to
present the ambient field as a finite separable extension of the fraction
field of a DVR whose parameter maps to the selected coordinate.  In
characteristic zero this is the usual finite transcendence-basis step; no
such presentation is assumed or named in the theorem proved here.
-/

public section

namespace Stafford38.Geometry.DivisorialBoundaryExtension

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence

noncomputable section

universe u v w z


/-- A finite separable extension of the fraction field of a DVR has a
discrete valuation subring above the maximal ideal.

The output is embedded in `L`.  The element `a` is carried to a nonzero
nonunit of this valuation subring, and its underlying element of `L` is the
original image of `a`. -/
theorem exists_discreteValuationSubring_over_maximalIdeal
    {A : Type u} {F : Type v} {L : Type w}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field L] [Algebra A L] [Algebra F L] [IsScalarTower A F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (a : A) (ha_ne : a ≠ 0) (ha_nonunit : ¬IsUnit a) :
    ∃ V : ValuationSubring L,
      IsDiscreteValuationRing V.toSubring ∧
      ∃ aV : V.toSubring,
        (aV : L) = algebraMap A L a ∧
        aV ≠ 0 ∧ ¬IsUnit aV := by
  obtain ⟨place⟩ :=
    Stafford38.Geometry.RetainedDVR.exists_retainedDVRPlace
      (A := A) (F := F) (L := L) a ha_ne ha_nonunit
  exact ⟨place.valuation, place.isDiscrete, place.parameter,
    place.parameter_eq, place.parameter_ne, place.parameter_nonunit⟩

/-- Characteristic-zero form.  Finite extensions are automatically
separable, so no separability hypothesis is exposed to the caller. -/
theorem exists_discreteValuationSubring_over_maximalIdeal_of_charZero
    {A : Type u} {F : Type v} {L : Type w}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [CharZero F] [Algebra A F] [IsFractionRing A F]
    [Field L] [Algebra A L] [Algebra F L] [IsScalarTower A F L]
    [FiniteDimensional F L]
    (a : A) (ha_ne : a ≠ 0) (ha_nonunit : ¬IsUnit a) :
    ∃ V : ValuationSubring L,
      IsDiscreteValuationRing V.toSubring ∧
      ∃ aV : V.toSubring,
        (aV : L) = algebraMap A L a ∧
        aV ≠ 0 ∧ ¬IsUnit aV := by
  let : Algebra.IsSeparable F L := inferInstance
  exact exists_discreteValuationSubring_over_maximalIdeal
    (A := A) (F := F) (L := L) a ha_ne ha_nonunit

/-- Specialization to the coordinate-zero DVR.  If the ambient field is a
finite separable extension of the fraction field of `k[X]_(X)`, compatibly
with `X ↦ x`, then the previously conditional `DiscreteBoundaryRefinement`
exists unconditionally. -/
theorem exists_discreteBoundaryRefinement_of_finiteExtension
    (k : Type u) [Field k]
    {K : Type w} [Field K] [Algebra k K]
    (x : K)
    [Algebra (CoordinateZeroLocalRing k) K]
    [Algebra (FractionRing (CoordinateZeroLocalRing k)) K]
    [IsScalarTower (CoordinateZeroLocalRing k)
      (FractionRing (CoordinateZeroLocalRing k)) K]
    [FiniteDimensional (FractionRing (CoordinateZeroLocalRing k)) K]
    [Algebra.IsSeparable (FractionRing (CoordinateZeroLocalRing k)) K]
    (hcoordinate :
      algebraMap (CoordinateZeroLocalRing k) K
        (algebraMap (Polynomial k) (CoordinateZeroLocalRing k)
          (Polynomial.X : Polynomial k)) = x) :
    Nonempty (DiscreteBoundaryRefinement k x) := by
  let R := CoordinateZeroLocalRing k
  let q : R := algebraMap (Polynomial k) R Polynomial.X
  have hq_ne : q ≠ 0 := by
    intro hq
    apply Polynomial.X_ne_zero (R := k)
    apply IsLocalization.injective R
      (coordinateZeroPrime k).primeCompl_le_nonZeroDivisors
    simpa only [q, map_zero] using hq
  have hq_nonunit : ¬IsUnit q := by
    rw [← mem_nonunits_iff, ← mem_maximalIdeal]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      R (coordinateZeroPrime k) Polynomial.X).2
        (Ideal.mem_span_singleton_self Polynomial.X)
  obtain ⟨V, hVdvr, qV, hqV, hqV_ne, hqV_nonunit⟩ :=
    exists_discreteValuationSubring_over_maximalIdeal
      (A := R) (F := FractionRing R) (L := K) q hq_ne hq_nonunit
  exact ⟨{
    valuation := V
    isDiscrete := hVdvr
    coordinate := qV
    coordinate_eq := hqV.trans hcoordinate
    coordinate_ne := hqV_ne
    coordinate_nonunit := hqV_nonunit
  }⟩

/-- Relative-function-field form.  The coefficient field `E` used to build
the `X`-adic DVR may differ from the original ground field `k`.  This is the
form needed after adjoining the other members of a transcendence basis:
once `K` is finite separable over `E(x)`, the output is still a boundary
refinement indexed by the original ground field. -/
theorem exists_discreteBoundaryRefinement_of_relativeFiniteExtension
    (k : Type z) (E : Type u) [Field k] [Field E]
    {K : Type w} [Field K] [Algebra k K] [Algebra E K]
    (x : K)
    [Algebra (CoordinateZeroLocalRing E) K]
    [Algebra (FractionRing (CoordinateZeroLocalRing E)) K]
    [IsScalarTower (CoordinateZeroLocalRing E)
      (FractionRing (CoordinateZeroLocalRing E)) K]
    [FiniteDimensional (FractionRing (CoordinateZeroLocalRing E)) K]
    [Algebra.IsSeparable (FractionRing (CoordinateZeroLocalRing E)) K]
    (hcoordinate :
      algebraMap (CoordinateZeroLocalRing E) K
        (algebraMap (Polynomial E) (CoordinateZeroLocalRing E)
          (Polynomial.X : Polynomial E)) = x) :
    Nonempty (DiscreteBoundaryRefinement k x) := by
  obtain ⟨D⟩ :=
    exists_discreteBoundaryRefinement_of_finiteExtension E x hcoordinate
  exact ⟨{
    valuation := D.valuation
    isDiscrete := D.isDiscrete
    coordinate := D.coordinate
    coordinate_eq := D.coordinate_eq
    coordinate_ne := D.coordinate_ne
    coordinate_nonunit := D.coordinate_nonunit
  }⟩

/-- Characteristic-zero specialization of the coordinate theorem. -/
theorem exists_discreteBoundaryRefinement_of_finiteExtension_of_charZero
    (k : Type u) [Field k] [CharZero k]
    {K : Type w} [Field K] [Algebra k K]
    (x : K)
    [Algebra (CoordinateZeroLocalRing k) K]
    [Algebra (FractionRing (CoordinateZeroLocalRing k)) K]
    [IsScalarTower (CoordinateZeroLocalRing k)
      (FractionRing (CoordinateZeroLocalRing k)) K]
    [FiniteDimensional (FractionRing (CoordinateZeroLocalRing k)) K]
    (hcoordinate :
      algebraMap (CoordinateZeroLocalRing k) K
        (algebraMap (Polynomial k) (CoordinateZeroLocalRing k)
          (Polynomial.X : Polynomial k)) = x) :
    Nonempty (DiscreteBoundaryRefinement k x) := by
  let : CharZero (CoordinateZeroLocalRing k) :=
    charZero_of_injective_algebraMap
      (algebraMap k (CoordinateZeroLocalRing k)).injective
  let : CharZero (FractionRing (CoordinateZeroLocalRing k)) :=
    IsFractionRing.charZero_of_isFractionRing (CoordinateZeroLocalRing k)
  let : Algebra.IsIntegral
      (FractionRing (CoordinateZeroLocalRing k)) K :=
    ⟨fun y ↦ (IsAlgebraic.of_finite
      (FractionRing (CoordinateZeroLocalRing k)) y).isIntegral⟩
  let : Algebra.IsSeparable
      (FractionRing (CoordinateZeroLocalRing k)) K := inferInstance
  exact exists_discreteBoundaryRefinement_of_finiteExtension
    k x hcoordinate

/-- Characteristic-zero relative-function-field form. -/
theorem exists_discreteBoundaryRefinement_of_relativeFiniteExtension_of_charZero
    (k : Type z) (E : Type u) [Field k] [Field E] [CharZero E]
    {K : Type w} [Field K] [Algebra k K] [Algebra E K]
    (x : K)
    [Algebra (CoordinateZeroLocalRing E) K]
    [Algebra (FractionRing (CoordinateZeroLocalRing E)) K]
    [IsScalarTower (CoordinateZeroLocalRing E)
      (FractionRing (CoordinateZeroLocalRing E)) K]
    [FiniteDimensional (FractionRing (CoordinateZeroLocalRing E)) K]
    (hcoordinate :
      algebraMap (CoordinateZeroLocalRing E) K
        (algebraMap (Polynomial E) (CoordinateZeroLocalRing E)
          (Polynomial.X : Polynomial E)) = x) :
    Nonempty (DiscreteBoundaryRefinement k x) := by
  obtain ⟨D⟩ :=
    exists_discreteBoundaryRefinement_of_finiteExtension_of_charZero
      E x hcoordinate
  exact ⟨{
    valuation := D.valuation
    isDiscrete := D.isDiscrete
    coordinate := D.coordinate
    coordinate_eq := D.coordinate_eq
    coordinate_ne := D.coordinate_ne
    coordinate_nonunit := D.coordinate_nonunit
  }⟩



end

end Stafford38.Geometry.DivisorialBoundaryExtension
