/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

/-
Extracted from Prove2Me proofs by Claude (2026-09-05):
* WeierstrassCurve.Affine.IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong
  (7adb32a2-3d95-5f94-8f9b-631ec0a69a45), submission
  67b5cb36-254f-5a1b-99ed-935bbd484158.
* WeierstrassCurve.Affine.IsogenyEndDatum.exists_restrictAlong_placeOfPoint_eq_add
  (f8a39c1e-1459-50cb-893b-11563e5e5727), submission
  52dbf7a5-8da4-5f91-a7ee-93f5d4b10c7e.
* WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom
  (f4d949d7-d2e9-583c-970a-d2c81be54545), submission
  dc1eabf7-1867-53e3-b324-7414996a1c99.
* WeierstrassCurve.Affine.exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward
  (e43a54a4-70bb-5551-8efe-0ba1b5eb4b2c), submission
  3e4feffd-4b48-5cc6-aa05-ac80b8acf609.
* WeierstrassCurve.Affine.exists_algHom_functionField_baseChange_finrankAlong_eq
  (f9fb6037-8f9d-5c67-be82-66f7e78fec74), submission
  b3015788-82b4-558c-8e89-28fc2203960b.
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_PlaceEvaluation
public import LeanPool.FLTEichlerShimura.Definitions.Def_Isogeny_ConditionalCurrency
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
public import Mathlib.Algebra.Polynomial.Basis
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
public import LeanPool.FLTEichlerShimura.Definitions.Def_EllipticCurve_FunctionFieldPullback -- shake: keep
public import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot -- shake: keep

import LeanPool.FLTEichlerShimura.Theorems.Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place
import Mathlib.Data.Nat.Choose.Multinomial
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add_v2
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum
import Mathlib.Tactic.NormNum.Prime
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_normFormulaAlong
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Logic.Equiv.PartialEquiv

/-!
# Shared library for isogeny endomorphism data

Common declarations from the dual-endomorphism and pointwise-addition proofs, together with
the supporting helpers needed to make those declarations independent of either proof file.
Also contains general coordinate-ring pullbacks, scalar-extension constructions for function
fields, and compatibility of point maps with geometric morphisms.
-/


section privateSection




open Polynomial IsDedekindDomain IsLocalRing WithZero
  WeierstrassCurve Affine CoordinateRing AlgebraicCurve

open scoped Bivariate

noncomputable section

namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F] {W : Affine F}


namespace CoordinateRing

public section publicSection

theorem algebraMap_eq_mk_C_C (a : F) :
    algebraMap F W.CoordinateRing a = CoordinateRing.mk W (C (C a)) := by
  rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_apply,
    Algebra.algebraMap_self_apply]
  rfl

theorem eq_of_XYIdeal_eq {x₁ y₁ x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (h : XYIdeal W x₁ (C y₁) = XYIdeal W x₂ (C y₂)) : x₁ = x₂ ∧ y₁ = y₂ := by
  have hne : XYIdeal W x₂ (C y₂) ≠ ⊤ := (XYIdeal_isMaximal h₂).ne_top
  have hX₁ : XClass W x₁ ∈ XYIdeal W x₂ (C y₂) :=
    h ▸ Ideal.subset_span (Set.mem_insert _ _)
  have hX₂ : XClass W x₂ ∈ XYIdeal W x₂ (C y₂) := Ideal.subset_span (Set.mem_insert _ _)
  have hY₁ : YClass W (C y₁) ∈ XYIdeal W x₂ (C y₂) :=
    h ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hY₂ : YClass W (C y₂) ∈ XYIdeal W x₂ (C y₂) :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  constructor
  · by_contra hx
    apply hne
    have hsub : XClass W x₁ - XClass W x₂ = algebraMap F W.CoordinateRing (x₂ - x₁) := by
      rw [XClass, XClass, ← map_sub, algebraMap_eq_mk_C_C]
      congr 1
      rw [← map_sub]
      congr 1
      rw [map_sub]
      ring
    have hmem := (XYIdeal W x₂ (C y₂)).sub_mem hX₁ hX₂
    rw [hsub] at hmem
    exact Ideal.eq_top_of_isUnit_mem _ hmem
      ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr fun hxy => hx hxy.symm)).map
        (algebraMap F W.CoordinateRing))
  · by_contra hy
    apply hne
    have hsub : YClass W (C y₁) - YClass W (C y₂) = algebraMap F W.CoordinateRing (y₂ - y₁) := by
      rw [YClass, YClass, ← map_sub, algebraMap_eq_mk_C_C]
      congr 1
      simp only [map_sub]
      ring
    have hmem := (XYIdeal W x₂ (C y₂)).sub_mem hY₁ hY₂
    rw [hsub] at hmem
    exact Ideal.eq_top_of_isUnit_mem _ hmem
      ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr fun hxy => hy hxy.symm)).map
        (algebraMap F W.CoordinateRing))

end publicSection

@[expose] public def heightOneSpectrumOfEquation {x y : F} (h : W.Equation x y) :
    HeightOneSpectrum W.CoordinateRing where
  asIdeal := XYIdeal W x (C y)
  isPrime := (XYIdeal_isMaximal h).isPrime
  ne_bot := XYIdeal_ne_bot x (C y)

public section publicSection

@[scoped simp]
theorem heightOneSpectrumOfEquation_asIdeal {x y : F} (h : W.Equation x y) :
    (heightOneSpectrumOfEquation h).asIdeal = XYIdeal W x (C y) := rfl

end publicSection


end CoordinateRing

@[expose] public def IsFinitePlace (v : AlgebraicCurve.Place F W.FunctionField) : Prop :=
  ∀ r : W.CoordinateRing, algebraMap W.CoordinateRing W.FunctionField r ∈ v.toValuationSubring

@[expose] public def IsFinitePlace.ringHom {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) :
    W.CoordinateRing →+* v.toValuationSubring where
  toFun r := ⟨algebraMap W.CoordinateRing W.FunctionField r, hv r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

public section publicSection

@[scoped simp]
theorem IsFinitePlace.coe_ringHom_apply {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) (r : W.CoordinateRing) :
    (hv.ringHom r : W.FunctionField) = algebraMap W.CoordinateRing W.FunctionField r := rfl

end publicSection

@[expose] public def IsFinitePlace.centre {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) :
    Ideal W.CoordinateRing :=
  (IsLocalRing.maximalIdeal v.toValuationSubring).comap hv.ringHom

public section publicSection

theorem IsFinitePlace.centre_isPrime {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) : hv.centre.IsPrime :=
  Ideal.IsPrime.comap _

theorem IsFinitePlace.inv_mem {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) {r : W.CoordinateRing} (hr : r ∉ hv.centre) :
    (algebraMap W.CoordinateRing W.FunctionField r)⁻¹ ∈ v.toValuationSubring := by
  have hunit : IsUnit (hv.ringHom r) := by
    rw [IsFinitePlace.centre, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, not_not] at hr
    exact hr
  obtain ⟨t, ht⟩ := hunit.exists_right_inv
  have ht' : algebraMap W.CoordinateRing W.FunctionField r * (t : W.FunctionField) = 1 := by
    simpa using congrArg (fun a : v.toValuationSubring => (a : W.FunctionField)) ht
  rw [inv_eq_of_mul_eq_one_right ht']
  exact t.2

theorem IsFinitePlace.centre_ne_bot {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) : hv.centre ≠ ⊥ := by
  intro hbot
  apply v.ne_top'
  rw [eq_top_iff]
  rintro z -
  obtain ⟨r, s, hs, hz⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  have hs0 : s ∉ hv.centre := by
    rw [hbot, Ideal.mem_bot]
    exact fun h => nonZeroDivisors.ne_zero hs h
  rw [← hz, div_eq_mul_inv]
  exact mul_mem (hv r) (hv.inv_mem hs0)

end publicSection

variable [IsDedekindDomain W.CoordinateRing]

@[expose] public def placeOfEquation {x y : F} (h : W.Equation x y) :
    AlgebraicCurve.Place F W.FunctionField :=
  AlgebraicCurve.Place.ofHeightOneSpectrum (heightOneSpectrumOfEquation h)


public section publicSection

theorem isFinitePlace_placeOfEquation {x y : F} (h : W.Equation x y) :
    IsFinitePlace (placeOfEquation h) := fun r =>
  (heightOneSpectrumOfEquation h).valuation_le_one r

theorem isFinitePlace_iff_exists_placeOfEquation [IsAlgClosed F]
    (v : AlgebraicCurve.Place F W.FunctionField) :
    IsFinitePlace v ↔ ∃ (x y : F) (h : W.Equation x y), v = placeOfEquation h := by
  constructor
  · intro hv
    have := hv.centre_isPrime
    have hmax : hv.centre.IsMaximal := Ideal.IsPrime.isMaximal hv.centre_isPrime hv.centre_ne_bot
    obtain ⟨x, y, hxy, hXY⟩ :=
      CoordinateRing.exists_eq_XYIdeal (W := W) (P := hv.centre) hv.centre_ne_bot
    refine ⟨x, y, hxy, ?_⟩
    set w : HeightOneSpectrum W.CoordinateRing := heightOneSpectrumOfEquation hxy with hw
    set A : ValuationSubring W.FunctionField :=
      HeightOneSpectrum.valuationSubringAtPrime W.FunctionField w with hA
    have hAded : IsDedekindDomain A := by rw [hA]; infer_instance
    have hle : A ≤ v.toValuationSubring := by
      intro z hz
      rw [hA] at hz
      obtain ⟨r, s, hs, rfl⟩ := hz
      have hs' : s ∉ hv.centre := by
        intro hmem
        rw [hXY] at hmem
        exact hs hmem
      exact mul_mem (hv r) (hv.inv_mem hs')
    have hSP : A.ofPrime (A.idealOfLE v.toValuationSubring hle) = v.toValuationSubring :=
      ValuationSubring.ofPrime_idealOfLE A v.toValuationSubring hle
    rcases eq_or_ne (A.idealOfLE v.toValuationSubring hle) ⊥ with hP | hP
    · exfalso
      apply v.ne_top'
      have h2 : A.ofPrime ⊥ ≤ A.ofPrime (A.idealOfLE v.toValuationSubring hle) :=
        ValuationSubring.ofPrime_le_of_le (h := hP.le)
      rw [ValuationSubring.ofPrime_bot] at h2
      exact top_le_iff.mp (le_trans h2 hSP.le)
    · have hPmax : (A.idealOfLE v.toValuationSubring hle).IsMaximal :=
        Ideal.IsPrime.isMaximal inferInstance hP
      have hPeq : A.idealOfLE v.toValuationSubring hle = IsLocalRing.maximalIdeal A :=
        IsLocalRing.eq_maximalIdeal hPmax
      have h3 : A.ofPrime (A.idealOfLE v.toValuationSubring hle)
          = A.ofPrime (IsLocalRing.maximalIdeal A) :=
        le_antisymm (ValuationSubring.ofPrime_le_of_le (h := hPeq.ge))
          (ValuationSubring.ofPrime_le_of_le (h := hPeq.le))
      rw [ValuationSubring.ofPrime_top] at h3
      have hAv : A = v.toValuationSubring := h3.symm.trans hSP
      refine (AlgebraicCurve.Place.ext ?_).symm
      change (AlgebraicCurve.Place.ofHeightOneSpectrum w).toValuationSubring = v.toValuationSubring
      rw [AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring,
        ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hAv
  · rintro ⟨x, y, h, rfl⟩
    exact isFinitePlace_placeOfEquation h

end publicSection

public scoped instance S13_instIsDedekindDomainCoordinateRing [IsAlgClosed F] [W.IsElliptic] :
    IsDedekindDomain W.CoordinateRing :=
  CoordinateRing.isDedekindDomain (W := W)

section CentredGate

variable [DecidableEq F] [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]

public section publicSection

omit [DecidableEq F] in
@[scoped simp]
theorem placeOfPoint_some {x y : F} (h : W.Nonsingular x y) :
    placeOfPoint (.some x y h) = placeOfEquation h.left := by
  classical
  exact
    placeOfPoint_some_eq_ofHeightOneSpectrum h (heightOneSpectrumOfEquation h.left) rfl

end publicSection

namespace InfinitePlace

@[expose] public def place : AlgebraicCurve.Place F W.FunctionField := placeOfPoint (0 : W.Point)


public section publicSection

omit [DecidableEq F] in
omit [IsDedekindDomain W.CoordinateRing] in
theorem not_isFinitePlace [IsAlgClosed F] [W.IsElliptic] :
    ¬ IsFinitePlace (place : AlgebraicCurve.Place F W.FunctionField) := by
  classical
  exact
    fun h =>
     algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero (W := W) (h _)

omit [DecidableEq F] in
theorem eq_of_not_isFinitePlace
    (v : AlgebraicCurve.Place F W.FunctionField) (hv : ¬ IsFinitePlace v) :
    v = place := by
  classical
  obtain ⟨P, rfl⟩ : ∃ P : W.Point, placeOfPoint P = v :=
    ⟨(pointEquivPlace (W := W)).symm v, (pointEquivPlace (W := W)).apply_symm_apply v⟩
  cases P with
  | zero => rfl
  | some x y h =>
      exact absurd (placeOfPoint_some (W := W) h ▸ isFinitePlace_placeOfEquation h.left) hv

end publicSection

end InfinitePlace

public section publicSection

omit [DecidableEq F] in
omit [IsDedekindDomain W.CoordinateRing] [GenusOnePlaceGate.IsCentred W] in
@[scoped simp]
theorem placeOfPoint_zero : placeOfPoint (.zero : W.Point) = InfinitePlace.place := by
  classical
  exact
    rfl

omit [DecidableEq F] in
omit [IsDedekindDomain W.CoordinateRing] [GenusOnePlaceGate.IsCentred W] in
theorem placeOfPoint_injective : Function.Injective (placeOfPoint (W := W)) := by
  classical
  exact
    (pointEquivPlace (W := W)).injective

omit [DecidableEq F] in
omit [IsDedekindDomain W.CoordinateRing] [GenusOnePlaceGate.IsCentred W] in
theorem placeOfPoint_surjective (_hΔ : W.Δ ≠ 0) :
    Function.Surjective (placeOfPoint (W := W)) := by
  classical
  exact
    (pointEquivPlace (W := W)).surjective

end publicSection


end CentredGate
end Affine
end WeierstrassCurve

namespace WeierstrassCurve
namespace Affine

section AutoNorm

variable {F : Type*} [Field F] [CharZero F] {V W : Affine F}

public section publicSection

theorem normFormulaAlong_of_elliptic (ι : V.FunctionField →ₐ[F] W.FunctionField)
    (hfin : FiniteAlong F ι) : NormFormulaAlong F ι hfin := by
  classical
  have : HasPrincipalDivisors F W.FunctionField := hasPrincipalDivisors_functionField W
  have : CharZero V.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F V.FunctionField).injective
  have hsep : SeparableAlong F ι := by
    let := algebraAlong ι
    have := isScalarTower_along ι
    have : Module.Finite V.FunctionField W.FunctionField := hfin
    change Algebra.IsSeparable V.FunctionField W.FunctionField
    infer_instance
  exact AlgebraicCurve.normFormulaAlong ι hfin hsep

end publicSection

end AutoNorm

namespace IsogenyEndDatum
open WeierstrassCurve.Affine.IsogenyEndDatum

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]

public section publicSection

omit [DecidableEq F] [W.GenusOnePlaceGate] [W.AbelTheorem] in
omit [IsAlgClosed F] [WeierstrassCurve.IsElliptic W] in
theorem normFormulaAlong_auto (D :
  IsogenyEndDatum W) :
    NormFormulaAlong F D.ι D.hfin :=
  normFormulaAlong_of_elliptic D.ι D.hfin

end publicSection

@[expose] public def pointEnd' (D : IsogenyEndDatum
  W) :
    AddMonoid.End W.Point := D.pointEnd D.normFormulaAlong_auto


public section publicSection

omit [IsAlgClosed F] [WeierstrassCurve.IsElliptic W] in
theorem pointEnd'_apply (D : IsogenyEndDatum W) (P : W.Point) :
    D.pointEnd' P = genusOnePic0Equiv W
      (Pic0.pushforwardAlongHom D.ι D.hι D.hfin D.normFormulaAlong_auto (pointClass P)) :=
  pointEnd_apply D _ P

omit [IsAlgClosed F] [WeierstrassCurve.IsElliptic W] in
theorem pointEnd'_eq_of_seam (D : IsogenyEndDatum W) (g : W.Point → W.Point) (hg0 : g 0 = 0)
    (hg : ∀ P, (placeOfPoint P).restrictAlong D.ι D.hι = placeOfPoint (g P)) (P : W.Point) :
    D.pointEnd' P = g P :=
  pointEnd_eq_of_seam D _ g hg0 hg P

end publicSection

end IsogenyEndDatum
end Affine
end WeierstrassCurve

section

section

universe u

namespace WeierstrassCurve
namespace Affine

variable {F : Type u} [Field F]

theorem exists_algebraMap_eq_of_isAlgebraic [IsAlgClosed F] {L : Type u} [Field L] [Algebra F L]
    {z : L} (hz : IsAlgebraic F z) : ∃ c : F, algebraMap F L c = z := by
  have hint : _root_.IsIntegral F z := hz.isIntegral
  have hdeg : (minpoly F z).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hint)
  exact minpoly.degree_eq_one_iff.mp hdeg

end Affine
end WeierstrassCurve
end
end

section

section

namespace AlgebraicCurve
namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

public section publicSection

theorem evalAt_add (hv : v.IsRational) {f g : F} (hf : f ∈
  v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

end publicSection

theorem evalAt_neg (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    v.evalAt (-f) = -v.evalAt f := by
  apply v.algebraMap_residueField_injective
  rw [_root_.map_neg, v.algebraMap_evalAt hv (neg_mem hf), v.algebraMap_evalAt hv hf, ←
    _root_.map_neg]
  rfl

public section publicSection

theorem evalAt_sub (hv : v.IsRational) {f g : F} (hf : f ∈
  v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  rw [sub_eq_add_neg, v.evalAt_add hv hf (neg_mem hg), v.evalAt_neg hv hg, sub_eq_add_neg]

end publicSection

end Place
end AlgebraicCurve

end
end

section

namespace ModularCurve

universe u

section Foundation

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

public abbrev KwIsogenyEndAddDatumSupply : Prop :=
  ∀ D₁ D₂ : IsogenyEndDatum W, D₁.pointEnd' + D₂.pointEnd' ≠ 0 →
    ∃ D₃ : IsogenyEndDatum W, D₃.pointEnd' = D₁.pointEnd' + D₂.pointEnd'

end Foundation
end ModularCurve
end

section

section

namespace WeierstrassCurve
namespace Affine

universe u

variable {F : Type u} [Field F] {W : Affine F} [W.IsElliptic]

theorem isElliptic_Δ_ne_zero : W.Δ ≠ 0 := W.coe_Δ' ▸ W.Δ'.ne_zero

end Affine
end WeierstrassCurve
end

section

namespace WeierstrassCurve
namespace Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

public section publicSection

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [W.GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem Δ_ne_zero_of_isElliptic : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero

end publicSection

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [W.IsElliptic]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
@[expose] public def placeOfPointEquiv : W.Point ≃ AlgebraicCurve.Place F W.FunctionField :=
  pointEquivPlace (W := W)

public section publicSection

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [W.IsElliptic]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem placeOfPoint_placeOfPointEquiv_symm (w : AlgebraicCurve.Place F W.FunctionField) :
    placeOfPoint ((placeOfPointEquiv W).symm w) = w :=
  (placeOfPointEquiv W).apply_symm_apply w

end publicSection

namespace IsogenyEndDatum
open WeierstrassCurve.Affine.IsogenyEndDatum

variable {W}

@[expose] public def geomMorph (D : IsogenyEndDatum
  W) :
    W.Point → W.Point :=
  fun P => (placeOfPointEquiv W).symm ((placeOfPoint P).restrictAlong D.ι D.hι)

public section publicSection

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [W.IsElliptic]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem placeOfPoint_geomMorph (D :
  IsogenyEndDatum W) (P : W.Point) :
    (placeOfPoint P).restrictAlong D.ι D.hι = placeOfPoint (D.geomMorph P) :=
  (placeOfPoint_placeOfPointEquiv_symm W _).symm

end publicSection

end IsogenyEndDatum
end Affine
end WeierstrassCurve
end

section

namespace AlgebraicCurve
namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

public section publicSection

theorem restrictAlong_comp (φ ψ : F →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral)
    (hψ : ψ.toRingHom.IsIntegral) (hcomp : (ψ.comp φ).toRingHom.IsIntegral)
    (w : Place K F) :
    w.restrictAlong (ψ.comp φ) hcomp = (w.restrictAlong ψ hψ).restrictAlong φ hφ := by
  refine Place.ext (SetLike.ext fun x => ?_)
  exact Iff.rfl

end publicSection

end Place
end AlgebraicCurve

end

section

section

namespace ModularCurve
namespace Mmr48

universe u

section PointCongr

variable {R : Type u} [CommRing R] {V : WeierstrassCurve.Affine R}

theorem mmr48_sp_point_some_congr {x₁ y₁ x₂ y₂ : R} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    (Point.some x₁ y₁ h₁ : V.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

end PointCongr
end Mmr48
end ModularCurve
end
end

section

section

namespace ModularCurve
namespace Mmr72

universe u

section CofiniteEngine

theorem mmr72_pp_end_eq_zero_of_cofinite_const {M : Type*} [AddCommGroup M]
    [Infinite M] (S : AddMonoid.End M) (v : M)
    (hfin : {P : M | S P ≠ v}.Finite) :
    S = 0 := by
  have _pin := Classical.em True
  refine DFunLike.ext _ _ fun P => ?_
  have hinj : Function.Injective fun R : M => P + R := fun a b h =>
    add_left_cancel h
  have hpre : ((fun R : M => P + R) ⁻¹' {Q : M | S Q ≠ v}).Finite :=
    Set.Finite.preimage hinj.injOn hfin
  obtain ⟨Q', hQ'⟩ :=
    (Set.Finite.infinite_compl (hfin.union hpre)).nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq,
    Set.mem_preimage, not_or, not_not] at hQ'
  have hadd : S (P + Q') = S P + S Q' := map_add S P Q'
  rw [hQ'.2, hQ'.1] at hadd
  change S P = 0
  grind

end CofiniteEngine
end Mmr72
end ModularCurve
end
end

section




namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

public section publicSection

theorem isRational_of_deg_eq_one (h : v.deg = 1) :
    v.IsRational := by
  intro x
  have hbot : (⊥ : Subalgebra K v.ResidueField) = ⊤ :=
    Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr h
  have hx : x ∈ (⊥ : Subalgebra K v.ResidueField) := by
    rw [hbot]
    exact Algebra.mem_top
  exact Algebra.mem_bot.mp hx

end publicSection

end Place

end AlgebraicCurve
end

section

namespace WeierstrassCurve
namespace Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

namespace IsogenyEndDatum
open WeierstrassCurve.Affine.IsogenyEndDatum

variable {W}

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [W.IsElliptic]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem pushforwardAlongDegZero_pointDivisor_geomMorph (D : IsogenyEndDatum W)
    (P : W.Point) :
    Pic0.pushforwardAlongDegZero D.ι D.hι (pointDivisor P)
      = pointDivisor (D.geomMorph P) - pointDivisor (D.geomMorph 0) := by
  refine Subtype.ext ?_
  rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, map_sub,
    pushforwardAlong_single_eq D.ι D.hι, pushforwardAlong_single_eq D.ι D.hι,
    D.placeOfPoint_geomMorph P, D.placeOfPoint_geomMorph 0]
  push_cast
  rw [coe_pointDivisor, coe_pointDivisor, sub_sub_sub_cancel_right]

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem pushforwardAlongHom_pointClass_eq_sub (D : IsogenyEndDatum W) (P : W.Point) :
    Pic0.pushforwardAlongHom D.ι D.hι D.hfin (normFormulaAlong_of_elliptic D.ι D.hfin)
        (pointClass P)
      = pointClass (D.geomMorph P) - pointClass (D.geomMorph 0) := by
  change Pic0.pushforwardAlongHom D.ι D.hι D.hfin _ (Pic0.mk (pointDivisor P))
      = Pic0.mk (pointDivisor (D.geomMorph P)) - Pic0.mk (pointDivisor (D.geomMorph 0))
  rw [Pic0.pushforwardAlongHom_mk, pushforwardAlongDegZero_pointDivisor_geomMorph D P]
  rfl

public section publicSection

omit [IsAlgClosed F] [W.IsElliptic] [GenusOnePlaceGate.IsCentred W] in
theorem
  pointEnd_eq_geomMorph_sub_geomMorph_zero (D :
  IsogenyEndDatum W) (P : W.Point) :
    D.pointEnd' P = D.geomMorph P - D.geomMorph 0 := by
  rw [IsogenyEndDatum.pointEnd'_apply, pushforwardAlongHom_pointClass_eq_sub D P, map_sub,
    genusOnePic0Equiv_apply, genusOnePic0Equiv_apply, pic0ToPoint_pointClass,
    pic0ToPoint_pointClass]

end publicSection


end IsogenyEndDatum
end Affine
end WeierstrassCurve
end

section

namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

variable (v : AlgebraicCurve.Place F W.FunctionField)

public section publicSection

theorem isFinitePlace_of_mem
    (hx : polyToFunctionField W X ∈ v.toValuationSubring) : IsFinitePlace v := by
  have hpoly : ∀ p : F[X], polyToFunctionField W p ∈ v.toValuationSubring := by
    intro p
    induction p using Polynomial.induction_on' with
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | monomial n c =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
        refine mul_mem ?_ (pow_mem hx n)
        rw [polyToFunctionField_C]
        exact v.algebraMap_mem' c
  set η := algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) with hηdef
  set c₁ : F[X] := C W.a₁ * X + C W.a₃ with hc₁def
  set cb : F[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ with hcbdef
  have hrel : η * η = polyToFunctionField W cb - polyToFunctionField W c₁ * η := by
    have h1 := smul_basis_mul_Y (W' := W) 0 1
    rw [zero_smul, zero_add, one_smul, one_mul, one_mul, zero_sub] at h1
    have h2 := congrArg (algebraMap W.CoordinateRing W.FunctionField) h1
    rw [map_mul, algebraMap_smul_basis, _root_.map_neg, neg_mul, ← sub_eq_add_neg] at h2
    exact h2
  have hy : η ∈ v.toValuationSubring := by
    refine v.mem_of_eval_monic_eq_zero (P := Polynomial.X ^ 2
      + (Polynomial.C (polyToFunctionField W c₁) * Polynomial.X
        - Polynomial.C (polyToFunctionField W cb))) ?_ ?_ (x := η) ?_
    · refine Polynomial.monic_X_pow_add (n := 2) ?_
      rw [sub_eq_add_neg, ← Polynomial.C_neg]
      refine lt_of_le_of_lt Polynomial.degree_linear_le ?_
      exact_mod_cast Nat.one_lt_two
    · intro i
      rw [show (Polynomial.C (polyToFunctionField W c₁) * Polynomial.X : Polynomial _)
          = Polynomial.C (polyToFunctionField W c₁) * Polynomial.X ^ 1 by ring]
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        Polynomial.coeff_C_mul, Polynomial.coeff_C]
      refine add_mem ?_ (sub_mem ?_ ?_)
      · split <;> simp [v.toValuationSubring.one_mem, v.toValuationSubring.zero_mem]
      · split
        · rw [mul_one]; exact hpoly _
        · rw [mul_zero]; exact v.toValuationSubring.zero_mem
      · split
        · exact hpoly _
        · exact v.toValuationSubring.zero_mem
    · simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [sq]
      linear_combination hrel
  intro r
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq r
  rw [algebraMap_smul_basis]
  exact add_mem (hpoly p) (mul_mem (hpoly q) hy)

theorem ord_X_neg_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) :
    v.ord (polyToFunctionField W X) < 0 := by
  by_contra hcon
  push Not at hcon
  exact hv (isFinitePlace_of_mem v
    (AlgebraicCurve.Place.mem_of_ord_nonneg v (polyToFunctionField_ne_zero Polynomial.X_ne_zero)
      hcon))

end publicSection

theorem exists_equation [IsAlgClosed F] (W : Affine F) (x₀ : F) :
    ∃ y₀ : F, W.Equation x₀ y₀ := by
  set P : F[X] := Polynomial.X ^ 2 + Polynomial.C (W.a₁ * x₀ + W.a₃) * Polynomial.X
    - Polynomial.C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hPdef
  have hPdeg : P.degree ≠ 0 := by
    have hcoeff : P.coeff 2 = 1 := by
      rw [hPdef]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
      norm_num
    intro hcon
    have h2 : P.coeff 2 = 0 := by
      refine Polynomial.coeff_eq_zero_of_degree_lt ?_
      rw [hcon]
      norm_num
    rw [hcoeff] at h2
    exact one_ne_zero h2
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root P hPdeg
  refine ⟨y₀, ?_⟩
  rw [equation_iff]
  have h3 : P.eval y₀ = 0 := hy₀
  rw [hPdef] at h3
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at h3
  linear_combination h3

end Affine
end WeierstrassCurve
end

section

namespace ModularCurve

universe u

section GeomMorphWire

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

public abbrev KwIsogenyEndAddGeomMorphSupply : Prop :=
  ∀ D₁ D₂ : IsogenyEndDatum W, D₁.pointEnd' + D₂.pointEnd' ≠ 0 →
    ∃ D₃ : IsogenyEndDatum W, ∀ P : W.Point,
      D₃.geomMorph P = D₁.geomMorph P + D₂.geomMorph P

omit [IsAlgClosed F] [W.IsElliptic] [GenusOnePlaceGate.IsCentred W] in
theorem kw_isogenyEndAddDatumSupply_of_addGeomMorphSupply
    (hgm : KwIsogenyEndAddGeomMorphSupply W) :
    KwIsogenyEndAddDatumSupply W := by
  intro D₁ D₂ h0
  obtain ⟨D₃, hD₃⟩ := hgm D₁ D₂ h0
  refine ⟨D₃, AddMonoidHom.ext fun P => ?_⟩
  change D₃.pointEnd' P = D₁.pointEnd' P + D₂.pointEnd' P
  rw [D₃.pointEnd_eq_geomMorph_sub_geomMorph_zero P,
    D₁.pointEnd_eq_geomMorph_sub_geomMorph_zero P,
    D₂.pointEnd_eq_geomMorph_sub_geomMorph_zero P, hD₃ P, hD₃ 0]
  abel

end GeomMorphWire
end ModularCurve
end

section

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

public section publicSection

theorem Place.mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

theorem Place.ramificationIndexAlong_pos (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') : 0 < Place.ramificationIndexAlong φ w := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  exact w.ramificationIndex_pos

theorem Place.ord_restrictAlong_ne_zero_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    (w.restrictAlong φ hφ).ord f ≠ 0 ↔ w.ord (φ f) ≠ 0 := by
  rw [w.ord_restrictAlong φ hφ f]
  have hpos := Place.ramificationIndexAlong_pos φ hφ w
  constructor
  · intro h hcon
    rcases mul_eq_zero.mp hcon with h1 | h1
    · omega
    · exact h h1
  · intro h hcon
    exact h (by rw [hcon, mul_zero])

end publicSection

end AlgebraicCurve

namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

public section publicSection

theorem algebraMap_polynomial_eq_mk_C (p : F[X]) :
    algebraMap F[X] W.CoordinateRing p = CoordinateRing.mk W (C p) :=
  rfl

theorem algebraMap_coordinateRing_ne_zero {r : W.CoordinateRing} (hr : r ≠ 0) :
    algebraMap W.CoordinateRing W.FunctionField r ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr hr

end publicSection

theorem mk_mem_XYIdeal_iff {x y : F} (h : W.Equation x y) (P : F[X][Y]) :
    CoordinateRing.mk W P ∈ XYIdeal W x (C y) ↔ P.evalEval x y = 0 := by
  have hmap : XYIdeal W x (C y)
      = Ideal.map (CoordinateRing.mk W) (Ideal.span {C (X - C x), Y - C (C y)}) := by
    rw [Ideal.map_span, Set.image_pair]
    rfl
  rw [hmap]
  constructor
  · intro hP
    obtain ⟨Q, hQ, hQP⟩ := (Ideal.mem_map_iff_of_surjective _ AdjoinRoot.mk_surjective).mp hP
    obtain ⟨c, hc⟩ := AdjoinRoot.mk_eq_mk.mp hQP
    have hQ0 : Q.evalEval x y = 0 :=
      mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mp hQ
    have hW0 : W.polynomial.evalEval x y = 0 := h
    have hPQ : P = Q - W.polynomial * c := by rw [← hc]; ring
    rw [hPQ]
    simp only [evalEval, eval_sub, eval_mul] at hQ0 hW0 ⊢
    rw [hQ0, hW0, zero_mul, sub_zero]
  · intro hP
    exact Ideal.mem_map_of_mem _ (mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr hP)

public section publicSection

theorem ord_placeOfEquation_ne_zero_iff [IsDedekindDomain W.CoordinateRing] {x y : F}
    (h : W.Equation x y) {r : W.CoordinateRing} (hr : r ≠ 0) :
    (placeOfEquation h).ord (algebraMap W.CoordinateRing W.FunctionField r) ≠ 0
      ↔ r ∈ XYIdeal W x (C y) := by
  rw [placeOfEquation, Place.ord_ofHeightOneSpectrum_ne_zero_iff _ hr,
    heightOneSpectrumOfEquation_asIdeal]

theorem ord_placeOfEquation_nonneg [IsDedekindDomain W.CoordinateRing] {x y : F}
    (h : W.Equation x y) (r : W.CoordinateRing) :
    0 ≤ (placeOfEquation h).ord (algebraMap W.CoordinateRing W.FunctionField r) :=
  AlgebraicCurve.Place.ord_nonneg_of_mem (placeOfEquation h) (isFinitePlace_placeOfEquation h r)

theorem ord_placeOfEquation_pos_iff [IsDedekindDomain W.CoordinateRing] {x y : F}
    (h : W.Equation x y) {r : W.CoordinateRing} (hr : r ≠ 0) :
    0 < (placeOfEquation h).ord (algebraMap W.CoordinateRing W.FunctionField r)
      ↔ r ∈ XYIdeal W x (C y) := by
  rw [← ord_placeOfEquation_ne_zero_iff h hr]
  have := ord_placeOfEquation_nonneg h r
  omega

theorem IsFinitePlace.mem_centre_iff_ord_ne_zero {v : Place F W.FunctionField}
    (hv : IsFinitePlace v) {r : W.CoordinateRing} (hr : r ≠ 0) :
    r ∈ hv.centre ↔ v.ord (algebraMap W.CoordinateRing W.FunctionField r) ≠ 0 := by
  have hr' : algebraMap W.CoordinateRing W.FunctionField r ≠ 0 :=
    algebraMap_coordinateRing_ne_zero hr
  rw [IsFinitePlace.centre, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ne_eq, v.ord_eq_zero_iff_adicValuation_eq_one hr']
  exact not_congr (v.adicValuation_coe_eq_one_iff (hv.ringHom r)).symm

theorem centre_placeOfEquation [IsDedekindDomain W.CoordinateRing] {x y : F}
    (h : W.Equation x y) :
    (isFinitePlace_placeOfEquation h).centre = XYIdeal W x (C y) := by
  ext r
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [Submodule.zero_mem]
  rw [(isFinitePlace_placeOfEquation h).mem_centre_iff_ord_ne_zero hr,
    ord_placeOfEquation_ne_zero_iff h hr]

theorem eq_placeOfEquation_of_le_centre [IsAlgClosed F] [IsDedekindDomain W.CoordinateRing]
    {v : Place F W.FunctionField} (hv : IsFinitePlace v) {x y : F} (h : W.Equation x y)
    (hle : XYIdeal W x (C y) ≤ hv.centre) : v = placeOfEquation h := by
  obtain ⟨x', y', h', hveq⟩ := (isFinitePlace_iff_exists_placeOfEquation v).mp hv
  subst hveq
  have hc : hv.centre = XYIdeal W x' (C y') := by
    rw [Subsingleton.elim hv (isFinitePlace_placeOfEquation h')]
    exact centre_placeOfEquation h'
  rw [hc] at hle
  have heq : XYIdeal W x (C y) = XYIdeal W x' (C y') :=
    (CoordinateRing.XYIdeal_isMaximal h).eq_of_le (CoordinateRing.XYIdeal_isMaximal h').ne_top
      hle
  obtain ⟨rfl, rfl⟩ := CoordinateRing.eq_of_XYIdeal_eq h' heq
  rfl

end publicSection

end Affine
end WeierstrassCurve

namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F] (W : Affine F)

variable {W}

@[expose] public def yGen (W : Affine F) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)

section OrdAtPoint

variable [IsDedekindDomain W.CoordinateRing]

public section publicSection

theorem ord_polyToFunctionField_pos_iff {x y : F} (h : W.Equation x y) {p : F[X]}
    (hp : p ≠ 0) :
    0 < (placeOfEquation h).ord (polyToFunctionField W p) ↔ p.eval x = 0 := by
  rw [polyToFunctionField_apply, algebraMap_polynomial_eq_mk_C,
    ord_placeOfEquation_pos_iff h (fun hcon => polyToFunctionField_ne_zero hp
      (by rw [polyToFunctionField_apply, algebraMap_polynomial_eq_mk_C, hcon, _root_.map_zero])),
    mk_mem_XYIdeal_iff h, Polynomial.evalEval_C]

end publicSection

end OrdAtPoint
end Affine
end WeierstrassCurve

end

section

universe u r s v

namespace WeierstrassCurve

variable {F : Type u} [Field F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic]

public lemma point_infinite : Infinite W.toAffine.Point := by
  refine Infinite.of_injective
    (fun x : F => Affine.Point.some x (WeierstrassCurve.Affine.exists_equation W x).choose
      ((Affine.equation_iff_nonsingular (W := W)).mp (WeierstrassCurve.Affine.exists_equation W
        x).choose_spec))
    fun x x' hxx' => ?_
  exact (Affine.Point.some.inj hxx').1

end WeierstrassCurve

end

section

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_sub_evalAt_pos (hrat : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring)
    (hne : f - algebraMap K F (v.evalAt f) ≠ 0) :
    0 < v.ord (f - algebraMap K F (v.evalAt f)) := by
  have hmem : f - algebraMap K F (v.evalAt f) ∈ v.toValuationSubring :=
    sub_mem hf (v.algebraMap_mem' _)
  rcases eq_or_ne (v.ord (f - algebraMap K F (v.evalAt f))) 0 with h0 | h0
  · exfalso
    refine v.evalAt_ne_zero hrat hne h0 ?_
    have hres : algebraMap K v.ResidueField
        (v.evalAt (f - algebraMap K F (v.evalAt f))) = 0 := by
      rw [v.algebraMap_evalAt hrat hmem]
      have hcoe : (⟨f - algebraMap K F (v.evalAt f), hmem⟩ : v.toValuationSubring)
          = ⟨f, hf⟩ - algebraMap K v.toValuationSubring (v.evalAt f) := by
        refine Subtype.ext ?_
        change f - algebraMap K F (v.evalAt f)
          = f - (algebraMap K v.toValuationSubring (v.evalAt f) : F)
        rw [Place.coe_algebraMap]
      rw [hcoe, map_sub, sub_eq_zero, ← v.algebraMap_evalAt hrat hf,
        IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    exact (map_eq_zero_iff _ (algebraMap K v.ResidueField).injective).mp hres
  · have hnonneg := AlgebraicCurve.Place.ord_nonneg_of_mem v hmem
    omega

end Place
end AlgebraicCurve
end

section

section

universe u

namespace WeierstrassCurve
namespace Affine

variable {F : Type u} [Field F]

section PointPullback

variable {W : Affine F}

local notation "ι" => algebraMap F W.FunctionField

public section publicSection

theorem eval₂_polynomial_of_equation_map {xP yP : W.FunctionField}
    (h : (W.map ι).toAffine.Equation xP yP) :
    W.polynomial.eval₂
      (Polynomial.aeval xP : F[X] →ₐ[F] W.FunctionField).toRingHom yP = 0 := by
  rw [equation_iff'] at h
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X]
  linear_combination h

end publicSection

@[expose] public def pointPullbackCoordHom {xP yP : W.FunctionField}
    (h : (W.map ι).toAffine.Equation xP yP) :
    W.CoordinateRing →ₐ[F] W.FunctionField where
  __ := AdjoinRoot.lift
    (Polynomial.aeval xP : F[X] →ₐ[F] W.FunctionField).toRingHom
    yP (eval₂_polynomial_of_equation_map h)
  commutes' c := by
    change AdjoinRoot.lift _ _ (eval₂_polynomial_of_equation_map h) (algebraMap F _ c)
      = algebraMap F W.FunctionField c
    rw [CoordinateRing.algebraMap_eq_mk_C_C, AdjoinRoot.lift_mk, eval₂_C]
    exact Polynomial.aeval_C _ c

theorem pointPullbackCoordHom_mk {xP yP : W.FunctionField}
    (h : (W.map ι).toAffine.Equation xP yP) (g : F[X][Y]) :
    pointPullbackCoordHom h (CoordinateRing.mk W g)
      = g.eval₂ (Polynomial.aeval xP : F[X] →ₐ[F] W.FunctionField).toRingHom yP :=
  AdjoinRoot.lift_mk (eval₂_polynomial_of_equation_map h) g

theorem pointPullbackCoordHom_comp_algebraMap {xP yP : W.FunctionField}
    (h : (W.map ι).toAffine.Equation xP yP) :
    (pointPullbackCoordHom h).toRingHom.comp (algebraMap F[X] W.CoordinateRing)
      = (Polynomial.aeval xP : F[X] →ₐ[F] W.FunctionField).toRingHom := by
  refine RingHom.ext fun p => ?_
  change pointPullbackCoordHom h (algebraMap F[X] _ p) = _
  rw [algebraMap_polynomial_eq_mk_C, pointPullbackCoordHom_mk, eval₂_C]

public section publicSection

theorem pointPullbackCoordHom_injective {xP yP : W.FunctionField}
    (h : (W.map ι).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    Function.Injective (pointPullbackCoordHom h) := by
  have hker : RingHom.ker (pointPullbackCoordHom h).toRingHom = ⊥ := by
    have : Module.Finite F[X] W.CoordinateRing :=
      Module.Finite.of_basis (CoordinateRing.basis W)
    refine Ideal.eq_bot_of_under_eq_bot (R := F[X]) ?_
    rw [Ideal.under_def, RingHom.comap_ker, pointPullbackCoordHom_comp_algebraMap,
      ← RingHom.injective_iff_ker_eq_bot]
    exact hx
  exact (RingHom.injective_iff_ker_eq_bot (pointPullbackCoordHom h).toRingHom).mpr hker

end publicSection

@[expose] public def pointPullbackHom {xP yP : W.FunctionField}
    (h : (W.map ι).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    W.FunctionField →ₐ[F] W.FunctionField :=
  IsFractionRing.liftAlgHom (pointPullbackCoordHom_injective h hx)

theorem pointPullbackHom_algebraMap {xP yP : W.FunctionField}
    (h : (W.map ι).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) (r : W.CoordinateRing) :
    pointPullbackHom h hx (algebraMap W.CoordinateRing W.FunctionField r)
      = pointPullbackCoordHom h r :=
  IsFractionRing.lift_algebraMap (pointPullbackCoordHom_injective h hx) r

theorem pointPullbackHom_polyToFunctionField_X {xP yP : W.FunctionField}
    (h : (W.map ι).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    pointPullbackHom h hx (polyToFunctionField W X) = xP := by
  rw [polyToFunctionField_apply, pointPullbackHom_algebraMap,
    algebraMap_polynomial_eq_mk_C, pointPullbackCoordHom_mk, eval₂_C]
  exact Polynomial.aeval_X _

theorem pointPullbackHom_yGen {xP yP : W.FunctionField}
    (h : (W.map ι).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    pointPullbackHom h hx (yGen W) = yP := by
  change pointPullbackHom h hx (algebraMap _ _ (CoordinateRing.mk W Y)) = _
  rw [pointPullbackHom_algebraMap, pointPullbackCoordHom_mk]
  exact eval₂_X _ _

end PointPullback

end Affine
end WeierstrassCurve
end
end

section

namespace WeierstrassCurve
namespace Affine

universe u

variable {F : Type u} [Field F]

section GenericPoint

variable {W : Affine F}

public section publicSection

theorem polyToFunctionField_eq_aeval (p : F[X]) :
    polyToFunctionField W p = Polynomial.aeval (polyToFunctionField W X) p := by
  have h1 : (polyToFunctionField W : F[X] →+* W.FunctionField)
      = algebraMap F[X] W.FunctionField :=
    (IsScalarTower.algebraMap_eq F[X] W.CoordinateRing W.FunctionField).symm
  have h2 : (IsScalarTower.toAlgHom F F[X] W.FunctionField : F[X] →ₐ[F] W.FunctionField)
      = Polynomial.aeval (polyToFunctionField W X) := by
    refine Polynomial.algHom_ext ?_
    rw [Polynomial.aeval_X, IsScalarTower.coe_toAlgHom', ← h1]
  calc polyToFunctionField W p = algebraMap F[X] W.FunctionField p := by rw [h1]
    _ = (IsScalarTower.toAlgHom F F[X] W.FunctionField : F[X] →ₐ[F] W.FunctionField) p := rfl
    _ = Polynomial.aeval (polyToFunctionField W X) p := by rw [h2]

theorem equation_map_polyToFunctionField_yGen :
    (W.map (algebraMap F W.FunctionField)).toAffine.Equation
      (polyToFunctionField W X) (yGen W) := by
  rw [equation_iff]
  have hrel := smul_basis_mul_Y (W' := W) 0 1
  rw [zero_smul, zero_add, one_smul, one_mul, one_mul, zero_sub] at hrel
  have h2 := congrArg (algebraMap W.CoordinateRing W.FunctionField) hrel
  rw [map_mul, algebraMap_smul_basis, _root_.map_neg, neg_mul, ← sub_eq_add_neg] at h2
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  simp only [map_add, map_mul, map_pow, polyToFunctionField_C] at h2
  rw [show yGen W = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)
    from rfl]
  simp only [polyToFunctionField_apply] at h2 ⊢
  linear_combination h2

end publicSection

end GenericPoint
end Affine
end WeierstrassCurve
end

section

namespace WeierstrassCurve
namespace Affine

universe u

variable {F : Type u} [Field F]

namespace AbstractSeam

variable {W : Affine F} {V : Affine F}
variable (ι : V.FunctionField →ₐ[F] W.FunctionField)
  (hι : ι.toRingHom.IsIntegral)
  {ξ η : W.FunctionField}
  (hX : ι (polyToFunctionField V (X : F[X])) = ξ)
  (hY : ι (yGen V) = η)

public section publicSection

include hX in
theorem map_XClass (c : F) :
    ι (algebraMap V.CoordinateRing V.FunctionField (XClass V c))
      = ξ - algebraMap F W.FunctionField c := by
  have h1 : algebraMap V.CoordinateRing V.FunctionField (XClass V c)
      = polyToFunctionField V (X : F[X]) - algebraMap F V.FunctionField c := by
    rw [← polyToFunctionField_C, ← map_sub]
    rfl
  rw [h1, map_sub, hX, AlgHom.commutes]

include hY in
theorem map_YClass (c : F) :
    ι (algebraMap V.CoordinateRing V.FunctionField (YClass V (C c)))
      = η - algebraMap F W.FunctionField c := by
  have h1 : algebraMap V.CoordinateRing V.FunctionField (YClass V (C c))
      = yGen V - algebraMap F V.FunctionField c := by
    rw [YClass, map_sub, map_sub, yGen]
    congr 1
  rw [h1, map_sub, hY, AlgHom.commutes]

end publicSection

section Cases

variable [IsDedekindDomain V.CoordinateRing]

public section publicSection

include hX hY in
theorem restrictAlong_placeOfEquation [IsAlgClosed F] [W.IsElliptic]
    {x y : F} (h : W.Equation x y) {a b : F} (h' : V.Equation a b)
    (hreg : ξ ∈ (placeOfEquation h).toValuationSubring)
    (hdx : 0 < (placeOfEquation h).ord (ξ - algebraMap F W.FunctionField a))
    (hdy : 0 < (placeOfEquation h).ord (η - algebraMap F W.FunctionField b)) :
    (placeOfEquation h).restrictAlong ι hι = placeOfEquation h' := by
  have hfin : IsFinitePlace ((placeOfEquation h).restrictAlong ι hι) :=
    isFinitePlace_of_mem _ (by
      rw [Place.mem_restrictAlong_iff, hX]
      exact hreg)
  refine eq_placeOfEquation_of_le_centre hfin h' ?_
  rw [XYIdeal, Ideal.span_le]
  intro r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · rw [SetLike.mem_coe, hfin.mem_centre_iff_ord_ne_zero (XClass_ne_zero _),
      Place.ord_restrictAlong_ne_zero_iff, map_XClass ι hX]
    omega
  · rw [SetLike.mem_coe, hfin.mem_centre_iff_ord_ne_zero (YClass_ne_zero _),
      Place.ord_restrictAlong_ne_zero_iff, map_YClass ι hY]
    omega

include hX in
theorem restrictAlong_eq_infinitePlace
    [GenusOnePlaceGate V] [GenusOnePlaceGate.IsCentred V]
    (v : AlgebraicCurve.Place F W.FunctionField)
    (hpole : ξ ∉ v.toValuationSubring) :
    v.restrictAlong ι hι = InfinitePlace.place := by
  refine InfinitePlace.eq_of_not_isFinitePlace _ ?_
  intro hfin
  refine hpole ?_
  rw [← hX]
  exact hfin (algebraMap F[X] V.CoordinateRing (X : F[X]))

end publicSection

end Cases
end AbstractSeam
end Affine
end WeierstrassCurve

end

section

section

namespace ModularCurve
namespace Es1a1

universe u

section CoordSeamPbd

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

def es1a8_coordSeamDataAt_pbd (φ : W.FunctionField →ₐ[F] W.FunctionField)
    (v : AlgebraicCurve.Place F W.FunctionField) : W.Point → Prop
  | .zero => φ (polyToFunctionField W X) ∉ v.toValuationSubring
  | .some x₃ y₃ _ =>
      0 < v.ord (φ (polyToFunctionField W X) - algebraMap F W.FunctionField x₃) ∧
        0 < v.ord (φ (yGen W) - algebraMap F W.FunctionField y₃)

omit [DecidableEq F] [CharZero F] [W.AbelTheorem] in
theorem es1a8_coordSeamDataAt_of_restrictAlong_pbd
    (φ : W.FunctionField →ₐ[F] W.FunctionField) (hφ : φ.toRingHom.IsIntegral)
    (v : AlgebraicCurve.Place F W.FunctionField) (Q : W.Point)
    (hres : v.restrictAlong φ hφ = placeOfPoint Q) :
    es1a8_coordSeamDataAt_pbd φ v Q := by
  cases Q with
  | zero =>
      rw [placeOfPoint_zero] at hres
      intro hmem
      have h1 : polyToFunctionField W X ∈ (v.restrictAlong φ hφ).toValuationSubring :=
        (Place.mem_restrictAlong_iff φ hφ v _).mpr hmem
      rw [hres] at h1
      have h2 : (0 : ℤ) ≤ (InfinitePlace.place :
          AlgebraicCurve.Place F W.FunctionField).ord (polyToFunctionField W X) :=
        AlgebraicCurve.Place.ord_nonneg_of_mem _ h1
      have h3 := ord_X_neg_of_not_isFinitePlace
        (InfinitePlace.place : AlgebraicCurve.Place F W.FunctionField)
        InfinitePlace.not_isFinitePlace
      omega
  | some x₃ y₃ h₃ =>
      rw [placeOfPoint_some] at hres
      have hpos := Place.ramificationIndexAlong_pos φ hφ v
      constructor
      · have hsrc : 0 < (placeOfEquation h₃.left).ord
            (polyToFunctionField W X - algebraMap F W.FunctionField x₃) := by
          rw [show polyToFunctionField W X - algebraMap F W.FunctionField x₃
              = polyToFunctionField W (X - C x₃) by rw [map_sub, polyToFunctionField_C]]
          refine (ord_polyToFunctionField_pos_iff h₃.left (X_sub_C_ne_zero x₃)).mpr ?_
          simp
        have htrans := Place.ord_restrictAlong φ hφ v
          (polyToFunctionField W X - algebraMap F W.FunctionField x₃)
        rw [hres, map_sub, AlgHom.commutes] at htrans
        rw [htrans]
        exact mul_pos (by exact_mod_cast hpos) hsrc
      · have hyeq : yGen W - algebraMap F W.FunctionField y₃
            = algebraMap W.CoordinateRing W.FunctionField
                ((-(C y₃) : F[X]) • (1 : W.CoordinateRing)
                  + (1 : F[X]) • CoordinateRing.mk W Y) := by
          rw [algebraMap_smul_basis,
            show algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)
              = yGen W from rfl]
          simp only [_root_.map_neg, polyToFunctionField_C, map_one, one_mul]
          ring
        have hyclass : ((-(C y₃) : F[X]) • (1 : W.CoordinateRing)
            + (1 : F[X]) • CoordinateRing.mk W Y) = CoordinateRing.YClass W (C y₃) := by
          simp only [CoordinateRing.smul, CoordinateRing.YClass, map_sub, _root_.map_neg,
            map_one, one_mul, mul_one]
          ring
        have hr0 : ((-(C y₃) : F[X]) • (1 : W.CoordinateRing)
            + (1 : F[X]) • CoordinateRing.mk W Y) ≠ 0 := by
          rw [hyclass]
          exact CoordinateRing.YClass_ne_zero _
        have hrmem : ((-(C y₃) : F[X]) • (1 : W.CoordinateRing)
            + (1 : F[X]) • CoordinateRing.mk W Y)
            ∈ CoordinateRing.XYIdeal W x₃ (C y₃) := by
          rw [hyclass, CoordinateRing.XYIdeal]
          exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
        have hsrc : 0 < (placeOfEquation h₃.left).ord
            (yGen W - algebraMap F W.FunctionField y₃) := by
          rw [hyeq]
          exact (ord_placeOfEquation_pos_iff h₃.left hr0).mpr hrmem
        have htrans := Place.ord_restrictAlong φ hφ v
          (yGen W - algebraMap F W.FunctionField y₃)
        rw [hres, map_sub, AlgHom.commutes] at htrans
        rw [htrans]
        exact mul_pos (by exact_mod_cast hpos) hsrc

end CoordSeamPbd
end Es1a1
end ModularCurve
end
end

section

section

namespace WeierstrassCurve
namespace Affine

universe u

variable {F : Type u} [Field F]

section AdjoinSurjective

variable {W : Affine F} (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

local notation "ι" => algebraMap F W.FunctionField

public section publicSection

theorem transcendental_polyToFunctionField_X :
    Transcendental F (polyToFunctionField W X) := by
  rw [transcendental_iff]
  intro p hp
  rw [← polyToFunctionField_eq_aeval] at hp
  exact polyToFunctionField_injective (by simpa using hp)

end publicSection

end AdjoinSurjective
end Affine
end WeierstrassCurve
end
end

section

section

universe u

public local instance instDecEqFunctionFieldEndst20Ps {F : Type u} [Field F]
    {W : WeierstrassCurve.Affine F} : DecidableEq W.FunctionField :=
  Classical.decEq _

namespace WeierstrassCurve
namespace Affine

variable {F : Type u} [Field F]

section DupDenominator

variable (W : Affine F)

theorem endst20_ps_yGen_ne_negY [CharZero F] :
    yGen W ≠ (W.map (algebraMap F W.FunctionField)).toAffine.negY
      (polyToFunctionField W X) (yGen W) := by
  intro hcon
  have heq := equation_map_polyToFunctionField_yGen (W := W)
  rw [equation_iff'] at heq
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
  simp only [negY, map_a₁, map_a₃] at hcon
  refine polyToFunctionField_ne_zero (W := W)
      (p := Polynomial.C (4 : F) * Polynomial.X ^ 3
        + Polynomial.C (W.a₁ ^ 2 + 4 * W.a₂) * Polynomial.X ^ 2
        + Polynomial.C (4 * W.a₄ + 2 * W.a₁ * W.a₃) * Polynomial.X
        + Polynomial.C (W.a₃ ^ 2 + 4 * W.a₆)) ?_ ?_
  · intro h0
    have h3 := congrArg (fun q => Polynomial.coeff q 3) h0
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero] at h3
    norm_num at h3
  · simp only [map_add, map_mul, map_pow, polyToFunctionField_C, map_ofNat]
    linear_combination
      (2 * yGen W + algebraMap F W.FunctionField W.a₁ * polyToFunctionField W X
          + algebraMap F W.FunctionField W.a₃) * hcon
        - 4 * heq

end DupDenominator

section DupCoordinates

variable (W : Affine F)

def endst20_ps_dupSlope : W.FunctionField :=
  (W.map (algebraMap F W.FunctionField)).toAffine.slope
    (polyToFunctionField W X) (polyToFunctionField W X) (yGen W) (yGen W)

def endst20_ps_dupX : W.FunctionField :=
  (W.map (algebraMap F W.FunctionField)).toAffine.addX
    (polyToFunctionField W X) (polyToFunctionField W X) (endst20_ps_dupSlope W)

theorem endst20_ps_dupSlope_eq_div [CharZero F] :
    endst20_ps_dupSlope W
      = (3 * polyToFunctionField W X ^ 2
            + 2 * (W.map (algebraMap F W.FunctionField)).toAffine.a₂ * polyToFunctionField W X
            + (W.map (algebraMap F W.FunctionField)).toAffine.a₄
            - (W.map (algebraMap F W.FunctionField)).toAffine.a₁ * yGen W)
          / (yGen W
              - (W.map (algebraMap F W.FunctionField)).toAffine.negY
                  (polyToFunctionField W X) (yGen W)) := by
  unfold endst20_ps_dupSlope
  exact slope_of_Y_ne rfl (endst20_ps_yGen_ne_negY W)

end DupCoordinates

section DupTranscendence

variable (W : Affine F)

theorem endst20_ps_yGen_sub_negY_sq :
    (yGen W - (W.map (algebraMap F W.FunctionField)).toAffine.negY
        (polyToFunctionField W X) (yGen W)) ^ 2
      = 4 * polyToFunctionField W X ^ 3
        + (algebraMap F W.FunctionField W.a₁ ^ 2 + 4 * algebraMap F W.FunctionField W.a₂)
            * polyToFunctionField W X ^ 2
        + (4 * algebraMap F W.FunctionField W.a₄
            + 2 * algebraMap F W.FunctionField W.a₁ * algebraMap F W.FunctionField W.a₃)
            * polyToFunctionField W X
        + (algebraMap F W.FunctionField W.a₃ ^ 2 + 4 * algebraMap F W.FunctionField W.a₆) := by
  have heq := equation_map_polyToFunctionField_yGen (W := W)
  rw [equation_iff'] at heq
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
  simp only [negY, map_a₁, map_a₃]
  linear_combination 4 * heq

theorem endst20_ps_dupX_mul_sq [CharZero F] :
    endst20_ps_dupX W
        * (yGen W - (W.map (algebraMap F W.FunctionField)).toAffine.negY
            (polyToFunctionField W X) (yGen W)) ^ 2
      = polyToFunctionField W X ^ 4
        - (2 * algebraMap F W.FunctionField W.a₄
            + algebraMap F W.FunctionField W.a₁ * algebraMap F W.FunctionField W.a₃)
            * polyToFunctionField W X ^ 2
        - 2 * (algebraMap F W.FunctionField W.a₃ ^ 2 + 4 * algebraMap F W.FunctionField W.a₆)
            * polyToFunctionField W X
        - (algebraMap F W.FunctionField W.a₁ ^ 2 * algebraMap F W.FunctionField W.a₆
            + 4 * algebraMap F W.FunctionField W.a₂ * algebraMap F W.FunctionField W.a₆
            - algebraMap F W.FunctionField W.a₁ * algebraMap F W.FunctionField W.a₃
                * algebraMap F W.FunctionField W.a₄
            + algebraMap F W.FunctionField W.a₂ * algebraMap F W.FunctionField W.a₃ ^ 2
            - algebraMap F W.FunctionField W.a₄ ^ 2) := by
  have hψ : yGen W - (W.map (algebraMap F W.FunctionField)).toAffine.negY
      (polyToFunctionField W X) (yGen W) ≠ 0 :=
    sub_ne_zero.mpr (endst20_ps_yGen_ne_negY W)
  have hs : endst20_ps_dupSlope W
      * (yGen W - (W.map (algebraMap F W.FunctionField)).toAffine.negY
          (polyToFunctionField W X) (yGen W))
      = 3 * polyToFunctionField W X ^ 2
        + 2 * (W.map (algebraMap F W.FunctionField)).toAffine.a₂ * polyToFunctionField W X
        + (W.map (algebraMap F W.FunctionField)).toAffine.a₄
        - (W.map (algebraMap F W.FunctionField)).toAffine.a₁ * yGen W := by
    rw [endst20_ps_dupSlope_eq_div W]
    exact div_mul_cancel₀ _ hψ
  have heq := equation_map_polyToFunctionField_yGen (W := W)
  rw [equation_iff'] at heq
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
  simp only [negY, map_a₁, map_a₂, map_a₃, map_a₄] at hs
  simp only [endst20_ps_dupX, addX, negY, map_a₁, map_a₂, map_a₃]
  grind

theorem endst20_ps_transcendental_dupX [IsAlgClosed F] [CharZero F] :
    Transcendental F (endst20_ps_dupX W) := by
  intro halg
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic halg
  have hq := endst20_ps_dupX_mul_sq W
  have hp2 := endst20_ps_yGen_sub_negY_sq W
  refine polyToFunctionField_ne_zero (W := W)
      (p := Polynomial.C c * (Polynomial.C (4 : F) * Polynomial.X ^ 3
          + Polynomial.C (W.a₁ ^ 2 + 4 * W.a₂) * Polynomial.X ^ 2
          + Polynomial.C (4 * W.a₄ + 2 * W.a₁ * W.a₃) * Polynomial.X
          + Polynomial.C (W.a₃ ^ 2 + 4 * W.a₆))
        - (Polynomial.X ^ 4
          - Polynomial.C (2 * W.a₄ + W.a₁ * W.a₃) * Polynomial.X ^ 2
          - Polynomial.C (2 * (W.a₃ ^ 2 + 4 * W.a₆)) * Polynomial.X
          - Polynomial.C (W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄
              + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2))) ?_ ?_
  · intro h0
    have h4 := congrArg (fun q => Polynomial.coeff q 4) h0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
      Polynomial.coeff_zero] at h4
    norm_num at h4
  · simp only [map_sub, map_add, map_mul, map_pow, polyToFunctionField_C, map_ofNat]
    grind

end DupTranscendence
end Affine
end WeierstrassCurve

namespace ModularCurve

local notation "psPsi11" =>
  (Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.C 4 * Polynomial.X ^ 2
    - Polynomial.C 40 * Polynomial.X - Polynomial.C 79 : Polynomial (AlgebraicClosure ℚ))
local notation "psN411" =>
  (Polynomial.X ^ 4 + Polynomial.C 20 * Polynomial.X ^ 2
    + Polynomial.C 158 * Polynomial.X + Polynomial.C 21 : Polynomial (AlgebraicClosure ℚ))
local notation "psP11[" b "]" =>
  (Polynomial.X ^ 6 - Polynomial.C 2 * Polynomial.X ^ 5 - Polynomial.C 50 * Polynomial.X ^ 4
    - Polynomial.C (4 * b + 397) * Polynomial.X ^ 3
    + Polynomial.C (4 * b - 103) * Polynomial.X ^ 2
    + Polynomial.C (40 * b - 728) * Polynomial.X
    + Polynomial.C (79 * b - 2871) : Polynomial (AlgebraicClosure ℚ))
local notation "psQ11[" b "]" =>
  (Polynomial.C (-8 * b - 4) * Polynomial.X ^ 3 + Polynomial.C (8 * b + 4) * Polynomial.X ^ 2
    + Polynomial.C (80 * b + 40) * Polynomial.X + Polynomial.C (158 * b + 79)
    : Polynomial (AlgebraicClosure ℚ))

end ModularCurve
end
end

section

section

namespace ModularCurve
namespace Es1a1

universe u

section AddLawCore

variable {F : Type u} [Field F]

public local instance instDecEqFunctionFieldEs1a6Add {W : WeierstrassCurve.Affine F} :
    DecidableEq W.FunctionField :=
  Classical.decEq _

variable (W : WeierstrassCurve.Affine F)

public section publicSection

theorem es1a6_add_equation (φ : W.FunctionField →ₐ[F] W.FunctionField) :
    (W.map (algebraMap F W.FunctionField)).toAffine.Equation
      (φ (polyToFunctionField W X)) (φ (yGen W)) := by
  have h := equation_map_polyToFunctionField_yGen (W := W)
  rw [equation_iff'] at h
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
  have h2 := congrArg φ h
  simp only [map_add, map_sub, map_mul, map_pow, _root_.map_zero, AlgHom.commutes] at h2
  rw [equation_iff']
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  linear_combination h2

end publicSection



variable (φ₁ φ₂ : W.FunctionField →ₐ[F] W.FunctionField)

@[expose] public def es1a6_addCollapse : Prop :=
  φ₁ (polyToFunctionField W X) = φ₂ (polyToFunctionField W X) ∧
    φ₁ (yGen W) = (W.map (algebraMap F W.FunctionField)).toAffine.negY
      (φ₂ (polyToFunctionField W X)) (φ₂ (yGen W))

public section publicSection

theorem es1a6_add_not_collapse_of_X_ne
    (hne : φ₁ (polyToFunctionField W X) ≠ φ₂ (polyToFunctionField W X)) :
    ¬ es1a6_addCollapse W φ₁ φ₂ :=
  fun hc => hne hc.1

end publicSection

@[expose] public def es1a6_addSumX : W.FunctionField :=
  (W.map (algebraMap F W.FunctionField)).toAffine.addX
    (φ₁ (polyToFunctionField W X)) (φ₂ (polyToFunctionField W X))
    ((W.map (algebraMap F W.FunctionField)).toAffine.slope
      (φ₁ (polyToFunctionField W X)) (φ₂ (polyToFunctionField W X))
      (φ₁ (yGen W)) (φ₂ (yGen W)))

@[expose] public def es1a6_addSumY : W.FunctionField :=
  (W.map (algebraMap F W.FunctionField)).toAffine.addY
    (φ₁ (polyToFunctionField W X)) (φ₂ (polyToFunctionField W X)) (φ₁ (yGen W))
    ((W.map (algebraMap F W.FunctionField)).toAffine.slope
      (φ₁ (polyToFunctionField W X)) (φ₂ (polyToFunctionField W X))
      (φ₁ (yGen W)) (φ₂ (yGen W)))

public section publicSection

theorem es1a6_addSum_equation (hcol : ¬ es1a6_addCollapse W φ₁ φ₂) :
    (W.map (algebraMap F W.FunctionField)).toAffine.Equation
      (es1a6_addSumX W φ₁ φ₂) (es1a6_addSumY W φ₁ φ₂) := by
  unfold es1a6_addSumX es1a6_addSumY
  exact equation_add (es1a6_add_equation W φ₁) (es1a6_add_equation W φ₂)
    (fun hxy => hcol hxy)

end publicSection


@[expose] public def es1a6_addSumPullbackHom (hcol : ¬ es1a6_addCollapse W φ₁ φ₂)
    (htr : Function.Injective (Polynomial.aeval (R := F) (es1a6_addSumX W φ₁ φ₂))) :
    W.FunctionField →ₐ[F] W.FunctionField :=
  pointPullbackHom (es1a6_addSum_equation W φ₁ φ₂ hcol) htr

public section publicSection

theorem es1a6_addSumPullbackHom_X (hcol : ¬ es1a6_addCollapse W φ₁ φ₂)
    (htr : Function.Injective (Polynomial.aeval (R := F) (es1a6_addSumX W φ₁ φ₂))) :
    es1a6_addSumPullbackHom W φ₁ φ₂ hcol htr (polyToFunctionField W X)
      = es1a6_addSumX W φ₁ φ₂ :=
  pointPullbackHom_polyToFunctionField_X _ _

theorem es1a6_addSumPullbackHom_yGen (hcol : ¬ es1a6_addCollapse W φ₁ φ₂)
    (htr : Function.Injective (Polynomial.aeval (R := F) (es1a6_addSumX W φ₁ φ₂))) :
    es1a6_addSumPullbackHom W φ₁ φ₂ hcol htr (yGen W) = es1a6_addSumY W φ₁ φ₂ :=
  pointPullbackHom_yGen _ _

end publicSection

theorem es1a6_add_sumX_isAlgebraic_constant_point [IsAlgClosed F]
    (hcol : ¬ es1a6_addCollapse W φ₁ φ₂)
    (halg : IsAlgebraic F (es1a6_addSumX W φ₁ φ₂)) :
    ∃ c d : F, es1a6_addSumX W φ₁ φ₂ = algebraMap F W.FunctionField c ∧
      es1a6_addSumY W φ₁ φ₂ = algebraMap F W.FunctionField d ∧ W.Equation c d := by
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic halg
  have heq := es1a6_addSum_equation W φ₁ φ₂ hcol
  rw [equation_iff'] at heq
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆] at heq
  rw [← hc] at heq
  have hq0 : (X ^ 2 + C (W.a₁ * c + W.a₃) * X
      - C (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) : F[X]) ≠ 0 := by
    intro hq
    have h2 := congrArg (fun q => Polynomial.coeff q 2) hq
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X,
      Polynomial.coeff_zero] at h2
    norm_num at h2
  have halgY : IsAlgebraic F (es1a6_addSumY W φ₁ φ₂) := by
    refine ⟨X ^ 2 + C (W.a₁ * c + W.a₃) * X
      - C (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆), hq0, ?_⟩
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C]
    linear_combination heq
  obtain ⟨d, hd⟩ := exists_algebraMap_eq_of_isAlgebraic halgY
  refine ⟨c, d, hc.symm, hd.symm, ?_⟩
  have hmap : (W.map (algebraMap F W.FunctionField)).toAffine.Equation
      (algebraMap F W.FunctionField c) (algebraMap F W.FunctionField d) := by
    rw [hc, hd]
    exact es1a6_addSum_equation W φ₁ φ₂ hcol
  exact (Affine.map_equation W (algebraMap F W.FunctionField).injective c d).mp hmap

theorem es1a6_add_sumX_transcendental_or_constant_point [IsAlgClosed F]
    (hcol : ¬ es1a6_addCollapse W φ₁ φ₂) :
    Transcendental F (es1a6_addSumX W φ₁ φ₂) ∨
      ∃ c d : F, es1a6_addSumX W φ₁ φ₂ = algebraMap F W.FunctionField c ∧
        es1a6_addSumY W φ₁ φ₂ = algebraMap F W.FunctionField d ∧ W.Equation c d := by
  by_cases halg : IsAlgebraic F (es1a6_addSumX W φ₁ φ₂)
  · exact Or.inr (es1a6_add_sumX_isAlgebraic_constant_point W φ₁ φ₂ hcol halg)
  · exact Or.inl halg

theorem es1a6_add_sumX_transcendental_of_forall_ne [IsAlgClosed F]
    (hnc : ∀ c : F, es1a6_addSumX W φ₁ φ₂ ≠ algebraMap F W.FunctionField c) :
    Transcendental F (es1a6_addSumX W φ₁ φ₂) := by
  intro halg
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic halg
  exact hnc c hc.symm

theorem es1a6_add_sumX_not_transcendental_of_eq_const (c : F)
    (hc : es1a6_addSumX W φ₁ φ₂ = algebraMap F W.FunctionField c) :
    ¬ Transcendental F (es1a6_addSumX W φ₁ φ₂) := by
  rw [hc]
  exact fun htr => htr (isAlgebraic_algebraMap c)

public section publicSection

theorem es1a6_add_aeval_sumX_injective_of_forall_ne [IsAlgClosed F]
    (hnc : ∀ c : F, es1a6_addSumX W φ₁ φ₂ ≠ algebraMap F W.FunctionField c) :
    Function.Injective (Polynomial.aeval (R := F) (es1a6_addSumX W φ₁ φ₂)) :=
  (injective_iff_map_eq_zero _).mpr fun p hp =>
    transcendental_iff.mp (es1a6_add_sumX_transcendental_of_forall_ne W φ₁ φ₂ hnc) p hp

end publicSection

end AddLawCore

section SeamEngines

variable {F : Type u} [Field F]

theorem es1a6_addSeam_restrictAlong_eq_placeOfEquation [IsAlgClosed F]
    {V W : WeierstrassCurve.Affine F} [IsDedekindDomain V.CoordinateRing]
    (ι : V.FunctionField →ₐ[F] W.FunctionField) (hι : ι.toRingHom.IsIntegral)
    {ξ η : W.FunctionField}
    (hX : ι (polyToFunctionField V (X : F[X])) = ξ) (hY : ι (yGen V) = η)
    (v : AlgebraicCurve.Place F W.FunctionField) {a b : F} (h' : V.Equation a b)
    (hreg : ξ ∈ v.toValuationSubring)
    (hdx : 0 < v.ord (ξ - algebraMap F W.FunctionField a))
    (hdy : 0 < v.ord (η - algebraMap F W.FunctionField b)) :
    v.restrictAlong ι hι = placeOfEquation h' := by
  have hfin : IsFinitePlace (v.restrictAlong ι hι) :=
    isFinitePlace_of_mem _ (by
      rw [Place.mem_restrictAlong_iff, hX]
      exact hreg)
  refine eq_placeOfEquation_of_le_centre hfin h' ?_
  rw [CoordinateRing.XYIdeal, Ideal.span_le]
  intro r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · rw [SetLike.mem_coe, hfin.mem_centre_iff_ord_ne_zero (CoordinateRing.XClass_ne_zero _),
      Place.ord_restrictAlong_ne_zero_iff, AbstractSeam.map_XClass ι hX]
    omega
  · rw [SetLike.mem_coe, hfin.mem_centre_iff_ord_ne_zero (CoordinateRing.YClass_ne_zero _),
      Place.ord_restrictAlong_ne_zero_iff, AbstractSeam.map_YClass ι hY]
    omega

variable [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

public local instance instDecEqFunctionFieldEs1a6AddSeam :
    DecidableEq W.FunctionField :=
  Classical.decEq _

variable (φ₁ φ₂ : W.FunctionField →ₐ[F] W.FunctionField)

omit [DecidableEq F] [CharZero F] [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W]
  [W.AbelTheorem] in
theorem es1a6_addSumSeam_some
    (hcol : ¬ es1a6_addCollapse W φ₁ φ₂)
    (htr : Function.Injective (Polynomial.aeval (R := F) (es1a6_addSumX W φ₁ φ₂)))
    (hι : (es1a6_addSumPullbackHom W φ₁ φ₂ hcol htr).toRingHom.IsIntegral)
    (v : AlgebraicCurve.Place F W.FunctionField) {x₃ y₃ : F} (h₃ : W.Equation x₃ y₃)
    (hdx : 0 < v.ord (es1a6_addSumX W φ₁ φ₂ - algebraMap F W.FunctionField x₃))
    (hdy : 0 < v.ord (es1a6_addSumY W φ₁ φ₂ - algebraMap F W.FunctionField y₃)) :
    v.restrictAlong (es1a6_addSumPullbackHom W φ₁ φ₂ hcol htr) hι
      = placeOfEquation h₃ := by
  have hreg : es1a6_addSumX W φ₁ φ₂ ∈ v.toValuationSubring := by
    by_cases hz : es1a6_addSumX W φ₁ φ₂ - algebraMap F W.FunctionField x₃ = 0
    · rw [sub_eq_zero.mp hz]
      exact v.algebraMap_mem' x₃
    · have hsub : es1a6_addSumX W φ₁ φ₂ - algebraMap F W.FunctionField x₃
          ∈ v.toValuationSubring :=
        AlgebraicCurve.Place.mem_of_ord_nonneg v hz hdx.le
      have h2 := add_mem hsub (v.algebraMap_mem' x₃)
      rwa [sub_add_cancel] at h2
  exact es1a6_addSeam_restrictAlong_eq_placeOfEquation
    (es1a6_addSumPullbackHom W φ₁ φ₂ hcol htr) hι
    (es1a6_addSumPullbackHom_X W φ₁ φ₂ hcol htr)
    (es1a6_addSumPullbackHom_yGen W φ₁ φ₂ hcol htr) v h₃ hreg hdx hdy

omit [CharZero F] in
omit [DecidableEq F] [W.AbelTheorem] in
theorem es1a6_addSumSeam_pole
    (hcol : ¬ es1a6_addCollapse W φ₁ φ₂)
    (htr : Function.Injective (Polynomial.aeval (R := F) (es1a6_addSumX W φ₁ φ₂)))
    (hι : (es1a6_addSumPullbackHom W φ₁ φ₂ hcol htr).toRingHom.IsIntegral)
    (v : AlgebraicCurve.Place F W.FunctionField)
    (hpole : es1a6_addSumX W φ₁ φ₂ ∉ v.toValuationSubring) :
    v.restrictAlong (es1a6_addSumPullbackHom W φ₁ φ₂ hcol htr) hι
      = (InfinitePlace.place : AlgebraicCurve.Place F W.FunctionField) :=
  AbstractSeam.restrictAlong_eq_infinitePlace
    (es1a6_addSumPullbackHom W φ₁ φ₂ hcol htr) hι
    (es1a6_addSumPullbackHom_X W φ₁ φ₂ hcol htr) v hpole

@[expose] public def es1a6_addSumSeamDataAt (v : AlgebraicCurve.Place F W.FunctionField) :
    W.Point → Prop
  | .zero => es1a6_addSumX W φ₁ φ₂ ∉ v.toValuationSubring
  | .some x₃ y₃ _ =>
      0 < v.ord (es1a6_addSumX W φ₁ φ₂ - algebraMap F W.FunctionField x₃) ∧
        0 < v.ord (es1a6_addSumY W φ₁ φ₂ - algebraMap F W.FunctionField y₃)

public section publicSection

omit [CharZero F] in
omit [DecidableEq F] [W.AbelTheorem] in
theorem es1a6_addSumSeam_of_data
    (hcol : ¬ es1a6_addCollapse W φ₁ φ₂)
    (htr : Function.Injective (Polynomial.aeval (R := F) (es1a6_addSumX W φ₁ φ₂)))
    (hι : (es1a6_addSumPullbackHom W φ₁ φ₂ hcol htr).toRingHom.IsIntegral)
    (P Q : W.Point)
    (hdat : es1a6_addSumSeamDataAt φ₁ φ₂ (placeOfPoint P) Q) :
    (placeOfPoint P).restrictAlong (es1a6_addSumPullbackHom W φ₁ φ₂ hcol htr) hι
      = placeOfPoint Q := by
  cases Q with
  | zero =>
      rw [placeOfPoint_zero]
      exact es1a6_addSumSeam_pole φ₁ φ₂ hcol htr hι (placeOfPoint P) hdat
  | some x₃ y₃ h₃ =>
      rw [placeOfPoint_some]
      exact es1a6_addSumSeam_some φ₁ φ₂ hcol htr hι (placeOfPoint P) h₃.left
        hdat.1 hdat.2

end publicSection

end SeamEngines
end Es1a1
end ModularCurve
end
end

section

section

namespace ModularCurve
namespace Es1a1

universe u

section CoordSeamEs1a11

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

@[expose] public def es1a11_coordSeamDataAt (φ : W.FunctionField →ₐ[F] W.FunctionField)
    (v : AlgebraicCurve.Place F W.FunctionField) : W.Point → Prop
  | .zero => φ (polyToFunctionField W X) ∉ v.toValuationSubring
  | .some x₃ y₃ _ =>
      0 < v.ord (φ (polyToFunctionField W X) - algebraMap F W.FunctionField x₃) ∧
        0 < v.ord (φ (yGen W) - algebraMap F W.FunctionField y₃)

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem es1a11_coordSeamDataAt_iff_pbd (φ : W.FunctionField →ₐ[F] W.FunctionField)
    (v : AlgebraicCurve.Place F W.FunctionField) (Q : W.Point) :
    es1a11_coordSeamDataAt φ v Q ↔ es1a8_coordSeamDataAt_pbd φ v Q := by
  cases Q <;> exact Iff.rfl

end CoordSeamEs1a11
end Es1a1
end ModularCurve
end
end

section

section

open AddMonoid.End

namespace ModularCurve
namespace Es1a1

section NegPullback

universe u

variable {F : Type u} [Field F]

def es1a4_negYGen (W : Affine F) : W.FunctionField :=
  (W.map (algebraMap F W.FunctionField)).toAffine.negY
    (polyToFunctionField W X) (yGen W)

theorem es1a4_negYGen_eq (W : Affine F) :
    es1a4_negYGen W
      = -(yGen W) - algebraMap F W.FunctionField W.a₁ * polyToFunctionField W X
          - algebraMap F W.FunctionField W.a₃ := rfl

theorem es1a4_negYGen_equation (W : Affine F) :
    (W.map (algebraMap F W.FunctionField)).toAffine.Equation
      (polyToFunctionField W X) (es1a4_negYGen W) :=
  (equation_neg _ _).mpr equation_map_polyToFunctionField_yGen

theorem es1a4_neg_aeval_injective (W : Affine F) :
    Function.Injective (Polynomial.aeval (R := F) (polyToFunctionField W X)) :=
  (injective_iff_map_eq_zero _).mpr fun p hp =>
    transcendental_iff.mp transcendental_polyToFunctionField_X p hp

def es1a4_negPullbackHom (W : Affine F) : W.FunctionField →ₐ[F] W.FunctionField :=
  pointPullbackHom (es1a4_negYGen_equation W) (es1a4_neg_aeval_injective W)

theorem es1a4_negPullbackHom_X (W : Affine F) :
    es1a4_negPullbackHom W (polyToFunctionField W X) = polyToFunctionField W X :=
  pointPullbackHom_polyToFunctionField_X _ _

theorem es1a4_negPullbackHom_yGen (W : Affine F) :
    es1a4_negPullbackHom W (yGen W) = es1a4_negYGen W :=
  pointPullbackHom_yGen _ _

theorem es1a4_negPullbackHom_polyToFunctionField (W : Affine F) (p : F[X]) :
    es1a4_negPullbackHom W (polyToFunctionField W p) = polyToFunctionField W p := by
  have h := polyToFunctionField_eq_aeval (W := W) p
  rw [h, ← Polynomial.aeval_algHom_apply, es1a4_negPullbackHom_X]

theorem es1a4_negPullbackHom_negYGen (W : Affine F) :
    es1a4_negPullbackHom W (es1a4_negYGen W) = yGen W := by
  rw [es1a4_negYGen_eq, map_sub, map_sub, _root_.map_neg, map_mul, AlgHom.commutes,
    AlgHom.commutes, es1a4_negPullbackHom_yGen, es1a4_negPullbackHom_X,
    es1a4_negYGen_eq]
  ring

theorem es1a4_negPullbackHom_sq_algebraMap (W : Affine F) (r : W.CoordinateRing) :
    es1a4_negPullbackHom W (es1a4_negPullbackHom W
        (algebraMap W.CoordinateRing W.FunctionField r))
      = algebraMap W.CoordinateRing W.FunctionField r := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
  rw [algebraMap_smul_basis,
    show algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) = yGen W
      from rfl]
  simp only [map_add, map_mul, es1a4_negPullbackHom_polyToFunctionField,
    es1a4_negPullbackHom_yGen, es1a4_negPullbackHom_negYGen]

theorem es1a4_negPullbackHom_involution (W : Affine F) (z : W.FunctionField) :
    es1a4_negPullbackHom W (es1a4_negPullbackHom W z) = z := by
  obtain ⟨r, s, _, hrs⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  rw [← hrs, map_div₀, map_div₀, es1a4_negPullbackHom_sq_algebraMap,
    es1a4_negPullbackHom_sq_algebraMap]

theorem es1a4_negPullbackHom_surjective (W : Affine F) :
    Function.Surjective (es1a4_negPullbackHom W) := fun z =>
  ⟨es1a4_negPullbackHom W z, es1a4_negPullbackHom_involution W z⟩

theorem es1a4_negPullbackHom_isIntegral (W : Affine F) :
    (es1a4_negPullbackHom W).toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ (es1a4_negPullbackHom_surjective W)

theorem es1a4_negPullbackHom_finiteAlong (W : Affine F) :
    FiniteAlong F (es1a4_negPullbackHom W) :=
  RingHom.Finite.of_surjective (es1a4_negPullbackHom W).toRingHom
    (es1a4_negPullbackHom_surjective W)

end NegPullback

section NegDatum

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]

def es1a4_negDatum (W : Affine F)
    :
    IsogenyEndDatum W where
  ι := es1a4_negPullbackHom W
  hι := es1a4_negPullbackHom_isIntegral W
  hfin := es1a4_negPullbackHom_finiteAlong W

variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

omit [DecidableEq F] [CharZero F] [W.GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem es1a4_negDatum_seam_some {x₀ y₀ : F} (h : W.Nonsingular x₀ y₀) :
    (placeOfEquation h.left).restrictAlong (es1a4_negPullbackHom W)
        (es1a4_negPullbackHom_isIntegral W)
      = placeOfEquation ((nonsingular_neg x₀ y₀).mpr h).left := by
  have hreg : polyToFunctionField W X ∈ (placeOfEquation h.left).toValuationSubring :=
    isFinitePlace_placeOfEquation h.left (algebraMap F[X] W.CoordinateRing X)
  have hdx : 0 < (placeOfEquation h.left).ord
      (polyToFunctionField W X - algebraMap F W.FunctionField x₀) := by
    rw [show polyToFunctionField W X - algebraMap F W.FunctionField x₀
        = polyToFunctionField W (X - C x₀) by rw [map_sub, polyToFunctionField_C]]
    refine (ord_polyToFunctionField_pos_iff h.left (X_sub_C_ne_zero x₀)).mpr ?_
    simp
  have hdy : 0 < (placeOfEquation h.left).ord
      (es1a4_negYGen W - algebraMap F W.FunctionField (W.negY x₀ y₀)) := by
    have hrbasis : -(CoordinateRing.YClass W (C y₀))
          - CoordinateRing.mk W (C (C W.a₁)) * CoordinateRing.XClass W x₀
        = (C y₀ - C W.a₁ * (X - C x₀)) • (1 : W.CoordinateRing)
          + (-1 : F[X]) • CoordinateRing.mk W Y := by
      simp only [CoordinateRing.smul, CoordinateRing.YClass, CoordinateRing.XClass,
        map_sub, map_mul, _root_.map_neg, map_one]
      ring
    have hr0 : -(CoordinateRing.YClass W (C y₀))
          - CoordinateRing.mk W (C (C W.a₁)) * CoordinateRing.XClass W x₀ ≠ 0 := by
      rw [hrbasis]
      intro hcon
      simpa using (CoordinateRing.smul_basis_eq_zero hcon).2
    have hrmem : -(CoordinateRing.YClass W (C y₀))
          - CoordinateRing.mk W (C (C W.a₁)) * CoordinateRing.XClass W x₀
        ∈ CoordinateRing.XYIdeal W x₀ (C y₀) :=
      sub_mem (neg_mem (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    have himg : es1a4_negYGen W - algebraMap F W.FunctionField (W.negY x₀ y₀)
        = algebraMap W.CoordinateRing W.FunctionField
            (-(CoordinateRing.YClass W (C y₀))
              - CoordinateRing.mk W (C (C W.a₁)) * CoordinateRing.XClass W x₀) := by
      rw [hrbasis, algebraMap_smul_basis,
        show algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)
          = yGen W from rfl, es1a4_negYGen_eq]
      simp only [negY, map_sub, _root_.map_neg, map_mul, map_one, polyToFunctionField_C]
      ring
    rw [himg]
    exact (ord_placeOfEquation_pos_iff h.left hr0).mpr hrmem
  exact AbstractSeam.restrictAlong_placeOfEquation (es1a4_negPullbackHom W)
    (es1a4_negPullbackHom_isIntegral W) (es1a4_negPullbackHom_X W)
    (es1a4_negPullbackHom_yGen W) h.left ((nonsingular_neg x₀ y₀).mpr h).left
    hreg hdx hdy

omit [CharZero F] in
omit [DecidableEq F] [W.AbelTheorem] in
theorem es1a4_negDatum_seam_zero :
    (InfinitePlace.place : AlgebraicCurve.Place F W.FunctionField).restrictAlong
        (es1a4_negPullbackHom W) (es1a4_negPullbackHom_isIntegral W)
      = InfinitePlace.place := by
  refine AbstractSeam.restrictAlong_eq_infinitePlace (es1a4_negPullbackHom W)
    (es1a4_negPullbackHom_isIntegral W) (es1a4_negPullbackHom_X W) _ ?_
  intro hmem
  have h1 : (0 : ℤ) ≤ (InfinitePlace.place : AlgebraicCurve.Place F W.FunctionField).ord
      (polyToFunctionField W X) :=
    AlgebraicCurve.Place.ord_nonneg_of_mem _ hmem
  have h2 : (InfinitePlace.place : AlgebraicCurve.Place F W.FunctionField).ord
      (polyToFunctionField W X) < 0 :=
    ord_X_neg_of_not_isFinitePlace _ InfinitePlace.not_isFinitePlace
  omega

omit [CharZero F] in
omit [DecidableEq F] [W.AbelTheorem] in
theorem es1a4_negDatum_seam (P : W.Point) :
    (placeOfPoint P).restrictAlong (es1a4_negDatum W).ι (es1a4_negDatum W).hι
      = placeOfPoint (-P) := by
  cases P with
  | zero =>
      rw [show -(Point.zero : W.Point) = Point.zero from rfl, placeOfPoint_zero]
      exact es1a4_negDatum_seam_zero
  | some x₀ y₀ h =>
      rw [Point.neg_some, placeOfPoint_some, placeOfPoint_some]
      exact es1a4_negDatum_seam_some h

end NegDatum
end Es1a1
end ModularCurve
end
end

section

section

namespace ModularCurve
namespace Es1a1

universe u

public local instance instDecEqFunctionFieldEs1a10NcPole {F : Type u} [Field F]
    {W : WeierstrassCurve.Affine F} :
    DecidableEq W.FunctionField :=
  Classical.decEq _

end Es1a1
end ModularCurve
end
end

section

section

namespace ModularCurve
namespace Es1a1

universe u

section VerticalCaseEngines

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

public local instance instDecEqFunctionFieldEs1a10NcVertical :
    DecidableEq W.FunctionField :=
  Classical.decEq _



end VerticalCaseEngines
end Es1a1
end ModularCurve
end
end

section

section

namespace ModularCurve
namespace Es1a1

universe u

public local instance instDecEqFunctionFieldEs1a9Nc {F : Type u} [Field F]
    {W : WeierstrassCurve.Affine F} :
    DecidableEq W.FunctionField :=
  Classical.decEq _

end Es1a1
end ModularCurve
end
end

section

section

namespace ModularCurve
namespace Mmr46

open ModularCurve.Es1a1

universe u

section GuardCarveEngine

variable {F : Type u} [Field F]
variable (W : WeierstrassCurve.Affine F)
variable (φ₁ φ₂ : W.FunctionField →ₐ[F] W.FunctionField)

theorem mmr46_gc_addSumX_ne_const_of_not_constPoint [IsAlgClosed F]
    (hcol : ¬ es1a6_addCollapse W φ₁ φ₂)
    (hres : ∀ c d : F, W.Equation c d →
      ¬ (es1a6_addSumX W φ₁ φ₂ = algebraMap F W.FunctionField c ∧
        es1a6_addSumY W φ₁ φ₂ = algebraMap F W.FunctionField d)) :
    ∀ c : F, es1a6_addSumX W φ₁ φ₂ ≠ algebraMap F W.FunctionField c := by
  intro c hc
  rcases es1a6_add_sumX_transcendental_or_constant_point W φ₁ φ₂ hcol with
    htr | ⟨c', d, hx, hy, heq⟩
  · exact es1a6_add_sumX_not_transcendental_of_eq_const W φ₁ φ₂ c hc htr
  · exact hres c' d heq ⟨hx, hy⟩

end GuardCarveEngine
end Mmr46
end ModularCurve
end
end

section

section

namespace ModularCurve
namespace Mmr73

open ModularCurve.Es1a1 ModularCurve.Mmr46 ModularCurve.Mmr48 ModularCurve.Mmr72

universe u

section PlaceEval

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

public section publicSection

theorem mmr73_cs_ord_neg (v : Place K F) (h : F) : v.ord (-h) = v.ord h := by
  have _pin := Classical.em True
  rcases eq_or_ne h 0 with rfl | hh
  · rw [_root_.neg_zero]
  · have h2 : v.ord (-h * -h) = v.ord (h * h) := by rw [neg_mul_neg]
    rw [v.ord_mul (neg_ne_zero.mpr hh) (neg_ne_zero.mpr hh), v.ord_mul hh hh] at h2
    omega

theorem mmr73_cs_evalAt_eq_of_ord_sub_pos (v : Place K F) (hv : v.IsRational)
    {f : F} {a : K} (hf : f ∈ v.toValuationSubring)
    (hpos : 0 < v.ord (f - algebraMap K F a)) : v.evalAt f = a := by
  have _pin := Classical.em True
  by_contra hne
  rcases eq_or_ne (f - algebraMap K F (v.evalAt f)) 0 with h0 | hne0
  · have hfa : f - algebraMap K F a = algebraMap K F (v.evalAt f - a) := by
      rw [map_sub, ← sub_eq_zero.mp h0]
    rw [hfa, AlgebraicCurve.Place.ord_algebraMap v] at hpos
    exact lt_irrefl 0 hpos
  · have hpos2 : 0 < v.ord (f - algebraMap K F (v.evalAt f)) :=
      v.ord_sub_evalAt_pos hv hf hne0
    have hkey : algebraMap K F (v.evalAt f - a)
        = (f - algebraMap K F a) + -(f - algebraMap K F (v.evalAt f)) := by
      rw [map_sub]; ring
    have hne2 : algebraMap K F (v.evalAt f - a) ≠ 0 := fun hcon =>
      hne (sub_eq_zero.mp ((algebraMap K F).injective
        (by rw [hcon, _root_.map_zero])))
    have hmin := v.min_ord_le_ord_add'
      (f := f - algebraMap K F a)
      (g := -(f - algebraMap K F (v.evalAt f)))
      (by rw [← hkey]; exact hne2)
    rw [← hkey, AlgebraicCurve.Place.ord_algebraMap v, mmr73_cs_ord_neg] at hmin
    exact absurd hmin (not_le.mpr (lt_min hpos hpos2))

end publicSection

end PlaceEval

section EvaluationSeam

attribute [local instance] ModularCurve.Es1a1.instDecEqFunctionFieldEs1a6Add

variable {F : Type u} [Field F] [IsAlgClosed F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W]

public section publicSection

omit [IsAlgClosed F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] in
theorem mmr73_cs_iota_ne_zero (D : IsogenyEndDatum W) {f : W.FunctionField}
    (hf : f ≠ 0) : D.ι f ≠ 0 := by
  have _pin := Classical.em True
  intro hcon
  exact hf (RingHom.injective
    (D.ι : W.FunctionField →+* W.FunctionField)
    (hcon.trans (_root_.map_zero
      (D.ι : W.FunctionField →+* W.FunctionField)).symm))

end publicSection

theorem mmr73_cs_geomMorph_ne_zero (D : IsogenyEndDatum W) (Q : W.Point)
    (hx : D.ι (polyToFunctionField W X) ∈ (placeOfPoint Q).toValuationSubring) :
    D.geomMorph Q ≠ 0 := by
  have _pin := Classical.em True
  intro hcon
  have hseam := D.placeOfPoint_geomMorph Q
  rw [hcon, Point.zero_def, placeOfPoint_zero] at hseam
  have hxmem : polyToFunctionField W X
      ∈ ((placeOfPoint Q).restrictAlong D.ι D.hι).toValuationSubring :=
    (Place.mem_restrictAlong_iff D.ι D.hι (placeOfPoint Q)
      (polyToFunctionField W X)).mpr hx
  rw [hseam] at hxmem
  exact InfinitePlace.not_isFinitePlace (isFinitePlace_of_mem _ hxmem)

public section publicSection

theorem mmr73_cs_geomMorph_some_coords (D : IsogenyEndDatum W) (Q : W.Point)
    {a b : F} {hab : W.Nonsingular a b}
    (hQ : D.geomMorph Q = Point.some a b hab)
    (hx : D.ι (polyToFunctionField W X) ∈ (placeOfPoint Q).toValuationSubring)
    (hy : D.ι (yGen W) ∈ (placeOfPoint Q).toValuationSubring) :
    (placeOfPoint Q).evalAt (D.ι (polyToFunctionField W X)) = a
      ∧ (placeOfPoint Q).evalAt (D.ι (yGen W)) = b := by
  have _pin := Classical.em True
  have hrat : (placeOfPoint Q).IsRational :=
    (placeOfPoint Q).isRational_of_deg_eq_one (deg_placeOfPoint Q)
  have hseam := D.placeOfPoint_geomMorph Q
  rw [hQ, placeOfPoint_some] at hseam
  have hXsub_eq : polyToFunctionField W X - algebraMap F W.FunctionField a
      = algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (C (X - C a))) := by
    rw [← polyToFunctionField_C (W := W) a, ← map_sub, polyToFunctionField_apply,
      algebraMap_polynomial_eq_mk_C]
  have hXmk_ne : CoordinateRing.mk W (C (X - C a)) ≠ 0 := by
    intro hcon
    apply polyToFunctionField_ne_zero (W := W) (Polynomial.X_sub_C_ne_zero a)
    rw [polyToFunctionField_apply, algebraMap_polynomial_eq_mk_C, hcon, _root_.map_zero]
  have hposX : 0 < (placeOfEquation hab.left).ord
      (polyToFunctionField W X - algebraMap F W.FunctionField a) := by
    rw [hXsub_eq, ord_placeOfEquation_pos_iff hab.left hXmk_ne,
      mk_mem_XYIdeal_iff hab.left]
    simp [Polynomial.evalEval]
  have hposwX : 0 < (placeOfPoint Q).ord
      (D.ι (polyToFunctionField W X) - algebraMap F W.FunctionField a) := by
    have hmap : D.ι (polyToFunctionField W X) - algebraMap F W.FunctionField a
        = D.ι (polyToFunctionField W X - algebraMap F W.FunctionField a) := by
      rw [map_sub, AlgHom.commutes]
    rw [hmap, Place.ord_restrictAlong D.ι D.hι (placeOfPoint Q), hseam]
    exact mul_pos
      (by exact_mod_cast Place.ramificationIndexAlong_pos D.ι D.hι (placeOfPoint Q))
      hposX
  have hYsub_eq : yGen W - algebraMap F W.FunctionField b
      = algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (Y - C (C b))) := by
    have h2 : algebraMap F W.FunctionField b
        = algebraMap W.CoordinateRing W.FunctionField
            (CoordinateRing.mk W (C (C b))) := by
      rw [← polyToFunctionField_C (W := W) b, polyToFunctionField_apply,
        algebraMap_polynomial_eq_mk_C]
    unfold yGen
    rw [h2, ← map_sub, ← map_sub]
  have hYmk_ne : CoordinateRing.mk W (Y - C (C b)) ≠ 0 := by
    intro hcon
    have hrep : CoordinateRing.mk W (Y - C (C b))
        = (-(C b) : F[X]) • (1 : W.CoordinateRing)
          + (1 : F[X]) • CoordinateRing.mk W Y := by
      rw [one_smul, Algebra.smul_def, mul_one, algebraMap_polynomial_eq_mk_C,
        map_sub, _root_.map_neg, _root_.map_neg]
      ring
    rw [hrep] at hcon
    exact one_ne_zero (CoordinateRing.smul_basis_eq_zero hcon).2
  have hposY : 0 < (placeOfEquation hab.left).ord
      (yGen W - algebraMap F W.FunctionField b) := by
    rw [hYsub_eq, ord_placeOfEquation_pos_iff hab.left hYmk_ne,
      mk_mem_XYIdeal_iff hab.left]
    simp [Polynomial.evalEval]
  have hposwY : 0 < (placeOfPoint Q).ord
      (D.ι (yGen W) - algebraMap F W.FunctionField b) := by
    have hmap : D.ι (yGen W) - algebraMap F W.FunctionField b
        = D.ι (yGen W - algebraMap F W.FunctionField b) := by
      rw [map_sub, AlgHom.commutes]
    rw [hmap, Place.ord_restrictAlong D.ι D.hι (placeOfPoint Q), hseam]
    exact mul_pos
      (by exact_mod_cast Place.ramificationIndexAlong_pos D.ι D.hι (placeOfPoint Q))
      hposY
  exact ⟨mmr73_cs_evalAt_eq_of_ord_sub_pos (placeOfPoint Q) hrat hx hposwX,
    mmr73_cs_evalAt_eq_of_ord_sub_pos (placeOfPoint Q) hrat hy hposwY⟩

end publicSection

theorem mmr73_cs_geomMorph_add_eq_of_addSum_const [DecidableEq F] (D₁ D₂ : IsogenyEndDatum W)
    (hX : D₁.ι (polyToFunctionField W X) ≠ D₂.ι (polyToFunctionField W X)) {c d : F}
    (hcd : W.Nonsingular c d) (hx : es1a6_addSumX W D₁.ι D₂.ι = algebraMap F W.FunctionField c)
    (hy : es1a6_addSumY W D₁.ι D₂.ι = algebraMap F W.FunctionField d) (Q : W.Point)
    (h1 : (placeOfPoint Q).ord (D₁.ι (polyToFunctionField W X)) = 0)
    (h2 : (placeOfPoint Q).ord (D₂.ι (polyToFunctionField W X)) = 0)
    (h3 : (placeOfPoint Q).ord (D₁.ι (yGen W)) = 0) (h4 : (placeOfPoint Q).ord (D₂.ι (yGen W)) = 0)
    (h5 : (placeOfPoint Q).ord
      (D₁.ι (polyToFunctionField W X) - D₂.ι (polyToFunctionField W X)) = 0) :
    D₁.geomMorph Q + D₂.geomMorph Q = Point.some c d hcd := by
  have _pin := Classical.em True
  have hrat : (placeOfPoint Q).IsRational :=
    (placeOfPoint Q).isRational_of_deg_eq_one (deg_placeOfPoint Q)
  have hxne : polyToFunctionField W X ≠ 0 :=
    polyToFunctionField_ne_zero Polynomial.X_ne_zero
  have hyne : yGen W ≠ 0 := Y_image_ne_zero
  have hf₁ne : D₁.ι (polyToFunctionField W X) ≠ 0 := mmr73_cs_iota_ne_zero D₁ hxne
  have hf₂ne : D₂.ι (polyToFunctionField W X) ≠ 0 := mmr73_cs_iota_ne_zero D₂ hxne
  have hg₁ne : D₁.ι (yGen W) ≠ 0 := mmr73_cs_iota_ne_zero D₁ hyne
  have hg₂ne : D₂.ι (yGen W) ≠ 0 := mmr73_cs_iota_ne_zero D₂ hyne
  have hδne : D₁.ι (polyToFunctionField W X) - D₂.ι (polyToFunctionField W X) ≠ 0 :=
    sub_ne_zero.mpr hX
  have hm₁x : D₁.ι (polyToFunctionField W X) ∈ (placeOfPoint Q).toValuationSubring :=
    AlgebraicCurve.Place.mem_of_ord_nonneg (placeOfPoint Q) hf₁ne h1.ge
  have hm₂x : D₂.ι (polyToFunctionField W X) ∈ (placeOfPoint Q).toValuationSubring :=
    AlgebraicCurve.Place.mem_of_ord_nonneg (placeOfPoint Q) hf₂ne h2.ge
  have hm₁y : D₁.ι (yGen W) ∈ (placeOfPoint Q).toValuationSubring :=
    AlgebraicCurve.Place.mem_of_ord_nonneg (placeOfPoint Q) hg₁ne h3.ge
  have hm₂y : D₂.ι (yGen W) ∈ (placeOfPoint Q).toValuationSubring :=
    AlgebraicCurve.Place.mem_of_ord_nonneg (placeOfPoint Q) hg₂ne h4.ge
  have hsome₁ : ∃ (a b : F) (hab : W.Nonsingular a b),
      D₁.geomMorph Q = Point.some a b hab := by
    rcases hP : D₁.geomMorph Q with _ | ⟨a, b, hab⟩
    · exact absurd (by rw [hP]; exact Point.zero_def.symm)
        (mmr73_cs_geomMorph_ne_zero D₁ Q hm₁x)
    · exact ⟨a, b, hab, rfl⟩
  have hsome₂ : ∃ (a b : F) (hab : W.Nonsingular a b),
      D₂.geomMorph Q = Point.some a b hab := by
    rcases hP : D₂.geomMorph Q with _ | ⟨a, b, hab⟩
    · exact absurd (by rw [hP]; exact Point.zero_def.symm)
        (mmr73_cs_geomMorph_ne_zero D₂ Q hm₂x)
    · exact ⟨a, b, hab, rfl⟩
  obtain ⟨a₁, b₁, hab₁, hP₁⟩ := hsome₁
  obtain ⟨a₂, b₂, hab₂, hP₂⟩ := hsome₂
  obtain ⟨ha₁, hb₁⟩ := mmr73_cs_geomMorph_some_coords D₁ Q hP₁ hm₁x hm₁y
  obtain ⟨ha₂, hb₂⟩ := mmr73_cs_geomMorph_some_coords D₂ Q hP₂ hm₂x hm₂y
  have hsubne : (placeOfPoint Q).evalAt
      (D₁.ι (polyToFunctionField W X) - D₂.ι (polyToFunctionField W X)) ≠ 0 :=
    (placeOfPoint Q).evalAt_ne_zero hrat hδne h5
  have hsubeq : (placeOfPoint Q).evalAt
      (D₁.ι (polyToFunctionField W X) - D₂.ι (polyToFunctionField W X))
      = a₁ - a₂ := by
    rw [(placeOfPoint Q).evalAt_sub hrat hm₁x hm₂x, ha₁, ha₂]
  have hane' : a₁ - a₂ ≠ 0 := hsubeq ▸ hsubne
  have hane : a₁ ≠ a₂ := sub_ne_zero.mp hane'
  obtain ⟨Λ, hΛdef⟩ : ∃ L : W.FunctionField, L = (D₁.ι (yGen W) - D₂.ι (yGen W))
      / (D₁.ι (polyToFunctionField W X) - D₂.ι (polyToFunctionField W X)) :=
    ⟨_, rfl⟩
  have hδinvord : (0 : ℤ) ≤ (placeOfPoint Q).ord
      ((D₁.ι (polyToFunctionField W X) - D₂.ι (polyToFunctionField W X))⁻¹) := by
    simp [(placeOfPoint Q).ord_inv, h5]
  have hΛmem : Λ ∈ (placeOfPoint Q).toValuationSubring := by
    rw [hΛdef, div_eq_mul_inv]
    exact mul_mem (sub_mem hm₁y hm₂y)
      (AlgebraicCurve.Place.mem_of_ord_nonneg (placeOfPoint Q) (inv_ne_zero hδne) hδinvord)
  have hΛmul : Λ * (D₁.ι (polyToFunctionField W X) - D₂.ι (polyToFunctionField W X))
      = D₁.ι (yGen W) - D₂.ι (yGen W) := by
    rw [hΛdef]
    exact div_mul_cancel₀ _ hδne
  have hslope : W.slope a₁ a₂ b₁ b₂ = (placeOfPoint Q).evalAt Λ := by
    rw [slope_of_X_ne hane, div_eq_iff hane', ← hb₁, ← hb₂,
      ← (placeOfPoint Q).evalAt_sub hrat hm₁y hm₂y, ← hsubeq,
      ← (placeOfPoint Q).evalAt_mul hrat hΛmem (sub_mem hm₁x hm₂x), hΛmul]
  have hΛΛ : Λ * Λ ∈ (placeOfPoint Q).toValuationSubring := mul_mem hΛmem hΛmem
  have hA1Λ : algebraMap F W.FunctionField W.a₁ * Λ
      ∈ (placeOfPoint Q).toValuationSubring :=
    mul_mem ((placeOfPoint Q).algebraMap_mem' W.a₁) hΛmem
  have hu1 : Λ * Λ + algebraMap F W.FunctionField W.a₁ * Λ
      ∈ (placeOfPoint Q).toValuationSubring := add_mem hΛΛ hA1Λ
  have hu2 : Λ * Λ + algebraMap F W.FunctionField W.a₁ * Λ
      - algebraMap F W.FunctionField W.a₂
      ∈ (placeOfPoint Q).toValuationSubring :=
    sub_mem hu1 ((placeOfPoint Q).algebraMap_mem' W.a₂)
  have hu3 : Λ * Λ + algebraMap F W.FunctionField W.a₁ * Λ
      - algebraMap F W.FunctionField W.a₂ - D₁.ι (polyToFunctionField W X)
      ∈ (placeOfPoint Q).toValuationSubring := sub_mem hu2 hm₁x
  have hU : Λ * Λ + algebraMap F W.FunctionField W.a₁ * Λ
      - algebraMap F W.FunctionField W.a₂ - D₁.ι (polyToFunctionField W X)
      - D₂.ι (polyToFunctionField W X)
      ∈ (placeOfPoint Q).toValuationSubring := sub_mem hu3 hm₂x
  have hBX : (placeOfPoint Q).evalAt
      (Λ * Λ + algebraMap F W.FunctionField W.a₁ * Λ
        - algebraMap F W.FunctionField W.a₂ - D₁.ι (polyToFunctionField W X)
        - D₂.ι (polyToFunctionField W X))
      = (placeOfPoint Q).evalAt Λ * (placeOfPoint Q).evalAt Λ
        + W.a₁ * (placeOfPoint Q).evalAt Λ - W.a₂ - a₁ - a₂ := by
    rw [(placeOfPoint Q).evalAt_sub hrat hu3 hm₂x,
      (placeOfPoint Q).evalAt_sub hrat hu2 hm₁x,
      (placeOfPoint Q).evalAt_sub hrat hu1 ((placeOfPoint Q).algebraMap_mem' W.a₂),
      (placeOfPoint Q).evalAt_add hrat hΛΛ hA1Λ,
      (placeOfPoint Q).evalAt_mul hrat hΛmem hΛmem,
      (placeOfPoint Q).evalAt_mul hrat ((placeOfPoint Q).algebraMap_mem' W.a₁) hΛmem,
      (placeOfPoint Q).evalAt_algebraMap W.a₁,
      (placeOfPoint Q).evalAt_algebraMap W.a₂, ha₁, ha₂]
  have hX0 : es1a6_addSumX W D₁.ι D₂.ι
      = Λ * Λ + algebraMap F W.FunctionField W.a₁ * Λ
        - algebraMap F W.FunctionField W.a₂ - D₁.ι (polyToFunctionField W X)
        - D₂.ι (polyToFunctionField W X) := by
    unfold es1a6_addSumX
    rw [slope_of_X_ne hX, ← hΛdef]
    simp only [addX, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂]
    ring
  have hY0 : es1a6_addSumY W D₁.ι D₂.ι
      = -(Λ * ((Λ * Λ + algebraMap F W.FunctionField W.a₁ * Λ
            - algebraMap F W.FunctionField W.a₂
            - D₁.ι (polyToFunctionField W X) - D₂.ι (polyToFunctionField W X))
          - D₁.ι (polyToFunctionField W X)) + D₁.ι (yGen W))
        - algebraMap F W.FunctionField W.a₁
            * (Λ * Λ + algebraMap F W.FunctionField W.a₁ * Λ
              - algebraMap F W.FunctionField W.a₂
              - D₁.ι (polyToFunctionField W X) - D₂.ι (polyToFunctionField W X))
        - algebraMap F W.FunctionField W.a₃ := by
    unfold es1a6_addSumY
    rw [slope_of_X_ne hX, ← hΛdef]
    simp only [addY, negAddY, negY, addX, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃]
    ring
  have hU1 : Λ * Λ + algebraMap F W.FunctionField W.a₁ * Λ
      - algebraMap F W.FunctionField W.a₂ - D₁.ι (polyToFunctionField W X)
      - D₂.ι (polyToFunctionField W X) - D₁.ι (polyToFunctionField W X)
      ∈ (placeOfPoint Q).toValuationSubring := sub_mem hU hm₁x
  have hV : Λ * (Λ * Λ + algebraMap F W.FunctionField W.a₁ * Λ
        - algebraMap F W.FunctionField W.a₂ - D₁.ι (polyToFunctionField W X)
        - D₂.ι (polyToFunctionField W X) - D₁.ι (polyToFunctionField W X))
      + D₁.ι (yGen W)
      ∈ (placeOfPoint Q).toValuationSubring :=
    add_mem (mul_mem hΛmem hU1) hm₁y
  have hW1 : -(Λ * (Λ * Λ + algebraMap F W.FunctionField W.a₁ * Λ
          - algebraMap F W.FunctionField W.a₂ - D₁.ι (polyToFunctionField W X)
          - D₂.ι (polyToFunctionField W X) - D₁.ι (polyToFunctionField W X))
        + D₁.ι (yGen W))
      - algebraMap F W.FunctionField W.a₁
          * (Λ * Λ + algebraMap F W.FunctionField W.a₁ * Λ
            - algebraMap F W.FunctionField W.a₂
            - D₁.ι (polyToFunctionField W X) - D₂.ι (polyToFunctionField W X))
      ∈ (placeOfPoint Q).toValuationSubring :=
    sub_mem (neg_mem hV)
      (mul_mem ((placeOfPoint Q).algebraMap_mem' W.a₁) hU)
  have hBY : (placeOfPoint Q).evalAt
      (-(Λ * ((Λ * Λ + algebraMap F W.FunctionField W.a₁ * Λ
            - algebraMap F W.FunctionField W.a₂
            - D₁.ι (polyToFunctionField W X) - D₂.ι (polyToFunctionField W X))
          - D₁.ι (polyToFunctionField W X)) + D₁.ι (yGen W))
        - algebraMap F W.FunctionField W.a₁
            * (Λ * Λ + algebraMap F W.FunctionField W.a₁ * Λ
              - algebraMap F W.FunctionField W.a₂
              - D₁.ι (polyToFunctionField W X) - D₂.ι (polyToFunctionField W X))
        - algebraMap F W.FunctionField W.a₃)
      = -((placeOfPoint Q).evalAt Λ
            * (((placeOfPoint Q).evalAt Λ * (placeOfPoint Q).evalAt Λ
                + W.a₁ * (placeOfPoint Q).evalAt Λ - W.a₂ - a₁ - a₂) - a₁) + b₁)
        - W.a₁ * ((placeOfPoint Q).evalAt Λ * (placeOfPoint Q).evalAt Λ
            + W.a₁ * (placeOfPoint Q).evalAt Λ - W.a₂ - a₁ - a₂)
        - W.a₃ := by
    rw [(placeOfPoint Q).evalAt_sub hrat hW1 ((placeOfPoint Q).algebraMap_mem' W.a₃),
      (placeOfPoint Q).evalAt_sub hrat (neg_mem hV)
        (mul_mem ((placeOfPoint Q).algebraMap_mem' W.a₁) hU),
      (placeOfPoint Q).evalAt_neg hrat hV,
      (placeOfPoint Q).evalAt_add hrat (mul_mem hΛmem hU1) hm₁y,
      (placeOfPoint Q).evalAt_mul hrat hΛmem hU1,
      (placeOfPoint Q).evalAt_sub hrat hU hm₁x,
      (placeOfPoint Q).evalAt_mul hrat ((placeOfPoint Q).algebraMap_mem' W.a₁) hU,
      hBX, (placeOfPoint Q).evalAt_algebraMap W.a₁,
      (placeOfPoint Q).evalAt_algebraMap W.a₃, ha₁, hb₁]
  rw [hP₁, hP₂, Point.add_of_X_ne hane]
  refine mmr48_sp_point_some_congr ?_ ?_ _ hcd
  · rw [hslope]
    have h0 : (placeOfPoint Q).evalAt (es1a6_addSumX W D₁.ι D₂.ι) = c := by
      rw [hx, (placeOfPoint Q).evalAt_algebraMap c]
    rw [hX0, hBX] at h0
    rw [← h0]
    simp only [addX]
    ring
  · rw [hslope]
    have h0 : (placeOfPoint Q).evalAt (es1a6_addSumY W D₁.ι D₂.ι) = d := by
      rw [hy, (placeOfPoint Q).evalAt_algebraMap d]
    rw [hY0, hBY] at h0
    rw [← h0]
    simp only [addY, negAddY, negY, addX]
    ring

end EvaluationSeam

section CofiniteEngine

variable {F : Type u} [Field F] {W : Affine F} [WeierstrassCurve.Affine.GenusOnePlaceGate W]

theorem mmr73_cs_finite_setOf_placeOfPoint_ord_ne_zero
    [HasPrincipalDivisors F W.FunctionField] {f : W.FunctionField} (hf : f ≠ 0) :
    {Q : W.Point | (placeOfPoint Q).ord f ≠ 0}.Finite := by
  have _pin := Classical.em True
  obtain ⟨Df, hDf, -⟩ :=
    HasPrincipalDivisors.exists_divisor (K := F) (F := W.FunctionField) f hf
  refine Set.Finite.subset
    (Set.Finite.preimage placeOfPoint_injective.injOn Df.support.finite_toSet) ?_
  intro Q hQ
  simp only [Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff]
  rw [hDf]
  exact hQ

end CofiniteEngine
end Mmr73
end ModularCurve
end
end

section

section

namespace ModularCurve

namespace Es1a1

universe u

section InputSeam

variable {F : Type u} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]

public section publicSection

theorem kw_coordSeamDataAt_geomMorph (D : IsogenyEndDatum W) (P : W.Point) :
    es1a11_coordSeamDataAt D.ι (placeOfPoint P) (D.geomMorph P) :=
  (es1a11_coordSeamDataAt_iff_pbd D.ι (placeOfPoint P) (D.geomMorph P)).mpr
    (es1a8_coordSeamDataAt_of_restrictAlong_pbd D.ι D.hι (placeOfPoint P)
      (D.geomMorph P) (D.placeOfPoint_geomMorph P))

end publicSection

end InputSeam
end Es1a1
end ModularCurve
end
end

section

section

namespace ModularCurve
namespace Es1a1

universe u

section AddLawCoreCmp

variable {F : Type u} [Field F]

variable (W : WeierstrassCurve.Affine F)

variable (φ₁ φ₂ : W.FunctionField →ₐ[F] W.FunctionField)

@[expose] public def es1a8_addCollapse_cmp : Prop :=
  φ₁ (polyToFunctionField W X) = φ₂ (polyToFunctionField W X) ∧
    φ₁ (yGen W) = (W.map (algebraMap F W.FunctionField)).toAffine.negY
      (φ₂ (polyToFunctionField W X)) (φ₂ (yGen W))

end AddLawCoreCmp

section HomExtCmp

variable {F : Type u} [Field F]

public section publicSection

theorem es1a8_functionField_algHom_ext_cmp {W : WeierstrassCurve.Affine F}
    {φ ψ : W.FunctionField →ₐ[F] W.FunctionField}
    (hX : φ (polyToFunctionField W X) = ψ (polyToFunctionField W X))
    (hY : φ (yGen W) = ψ (yGen W)) : φ = ψ := by
  have hpoly : ∀ p : F[X],
      φ (polyToFunctionField W p) = ψ (polyToFunctionField W p) := by
    intro p
    rw [polyToFunctionField_eq_aeval (W := W) p, ← Polynomial.aeval_algHom_apply,
      ← Polynomial.aeval_algHom_apply, hX]
  have hcoord : ∀ r : W.CoordinateRing,
      φ (algebraMap W.CoordinateRing W.FunctionField r)
        = ψ (algebraMap W.CoordinateRing W.FunctionField r) := by
    intro r
    obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
    rw [algebraMap_smul_basis,
      show algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) = yGen W
        from rfl]
    simp only [map_add, map_mul, hpoly, hY]
  refine AlgHom.ext fun z => ?_
  obtain ⟨r, s, _, hrs⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  rw [← hrs, map_div₀, map_div₀, hcoord r, hcoord s]

end publicSection

theorem es1a8_negYGen_map_cmp (W : WeierstrassCurve.Affine F)
    (φ : W.FunctionField →ₐ[F] W.FunctionField) :
    φ (es1a4_negYGen W)
      = (W.map (algebraMap F W.FunctionField)).toAffine.negY
          (φ (polyToFunctionField W X)) (φ (yGen W)) := by
  rw [es1a4_negYGen_eq]
  simp only [map_sub, _root_.map_neg, map_mul, AlgHom.commutes, negY,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

theorem es1a8_addCollapse_iota_comp_cmp {W : WeierstrassCurve.Affine F}
    {φ₁ φ₂ : W.FunctionField →ₐ[F] W.FunctionField}
    (hcol : es1a8_addCollapse_cmp W φ₁ φ₂) :
    φ₁ = φ₂.comp (es1a4_negPullbackHom W) := by
  refine es1a8_functionField_algHom_ext_cmp ?_ ?_
  · rw [AlgHom.comp_apply, es1a4_negPullbackHom_X]
    exact hcol.1
  · rw [AlgHom.comp_apply, es1a4_negPullbackHom_yGen, es1a8_negYGen_map_cmp]
    exact hcol.2

theorem es1a8_restrictAlong_congr_cmp {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : AlgebraicCurve.Place K L) {ι₁ ι₂ : L →ₐ[K] L} (h : ι₁ = ι₂)
    (h₁ : ι₁.toRingHom.IsIntegral) (h₂ : ι₂.toRingHom.IsIntegral) :
    w.restrictAlong ι₁ h₁ = w.restrictAlong ι₂ h₂ := by
  subst h
  rfl

end HomExtCmp

section CollapseHalfCmp

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

omit [CharZero F] in
omit [DecidableEq F] [W.AbelTheorem] in
theorem es1a8_addCollapse_geomMorph_eq_neg_cmp (D₁ D₂ : IsogenyEndDatum W)
    (hcol : es1a8_addCollapse_cmp W D₁.ι D₂.ι) (P : W.Point) :
    D₁.geomMorph P = -(D₂.geomMorph P) := by
  have hcomp : D₁.ι = D₂.ι.comp (es1a4_negPullbackHom W) :=
    es1a8_addCollapse_iota_comp_cmp hcol
  have hι' : (D₂.ι.comp (es1a4_negPullbackHom W)).toRingHom.IsIntegral :=
    hcomp ▸ D₁.hι
  refine placeOfPoint_injective ?_
  calc placeOfPoint (D₁.geomMorph P)
      = (placeOfPoint P).restrictAlong D₁.ι D₁.hι :=
        (D₁.placeOfPoint_geomMorph P).symm
    _ = (placeOfPoint P).restrictAlong (D₂.ι.comp (es1a4_negPullbackHom W)) hι' :=
        es1a8_restrictAlong_congr_cmp _ hcomp _ _
    _ = ((placeOfPoint P).restrictAlong D₂.ι D₂.hι).restrictAlong
          (es1a4_negPullbackHom W) (es1a4_negPullbackHom_isIntegral W) :=
        AlgebraicCurve.Place.restrictAlong_comp (es1a4_negPullbackHom W) D₂.ι
          (es1a4_negPullbackHom_isIntegral W) D₂.hι hι' (placeOfPoint P)
    _ = (placeOfPoint (D₂.geomMorph P)).restrictAlong
          (es1a4_negPullbackHom W) (es1a4_negPullbackHom_isIntegral W) := by
        rw [D₂.placeOfPoint_geomMorph P]
    _ = placeOfPoint (-(D₂.geomMorph P)) := es1a4_negDatum_seam (D₂.geomMorph P)

public section publicSection

theorem es1a8_addCollapse_pointEnd_add_eq_zero_cmp (D₁ D₂ : IsogenyEndDatum W)
    (hcol : es1a8_addCollapse_cmp W D₁.ι D₂.ι) :
    D₁.pointEnd' + D₂.pointEnd' = 0 := by
  refine AddMonoidHom.ext fun P => ?_
  change D₁.pointEnd' P + D₂.pointEnd' P = 0
  rw [D₁.pointEnd_eq_geomMorph_sub_geomMorph_zero P,
    D₂.pointEnd_eq_geomMorph_sub_geomMorph_zero P,
    es1a8_addCollapse_geomMorph_eq_neg_cmp D₁ D₂ hcol P,
    es1a8_addCollapse_geomMorph_eq_neg_cmp D₁ D₂ hcol 0]
  abel

end publicSection

theorem es1a8_add_not_collapse_of_pointEnd_add_ne_zero_cmp (D₁ D₂ : IsogenyEndDatum W)
    (h0 : D₁.pointEnd' + D₂.pointEnd' ≠ 0) :
    ¬ es1a8_addCollapse_cmp W D₁.ι D₂.ι :=
  fun hcol => h0 (es1a8_addCollapse_pointEnd_add_eq_zero_cmp D₁ D₂ hcol)

end CollapseHalfCmp

section IntegralityEngineCmp

variable {F : Type u} [Field F] {W : WeierstrassCurve.Affine F}

theorem es1a8_addInt_coordRing_isAlgebraic_cmp :
    Algebra.IsAlgebraic F[X] W.CoordinateRing := by
  have : Module.Finite F[X] W.CoordinateRing :=
    Module.Finite.of_basis (CoordinateRing.basis W)
  have : Algebra.IsIntegral F[X] W.CoordinateRing := Algebra.IsIntegral.of_finite _ _
  exact Algebra.IsIntegral.isAlgebraic

theorem es1a8_addInt_functionField_isAlgebraic_cmp :
    Algebra.IsAlgebraic W.CoordinateRing W.FunctionField := by
  constructor
  intro z
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  have hbne : algebraMap W.CoordinateRing W.FunctionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr
      (nonZeroDivisors.ne_zero hb)
  refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, ?_, ?_⟩
  · intro hcon
    have h1 := congrArg (fun q => Polynomial.coeff q 1) hcon
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_one,
      Polynomial.coeff_C, Polynomial.coeff_zero, mul_one] at h1
    norm_num at h1
    exact nonZeroDivisors.ne_zero hb h1
  · have ha : algebraMap W.CoordinateRing W.FunctionField a
        = z * algebraMap W.CoordinateRing W.FunctionField b := by
      rw [← hab]
      exact (div_mul_cancel₀ _ hbne).symm
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, ha]
    ring

theorem es1a8_addInt_algebraMap_injective_cmp :
    Function.Injective (algebraMap F[X] W.CoordinateRing) := by
  intro p q h
  have h0 : (p - q) • (1 : W.CoordinateRing) + (0 : F[X]) • CoordinateRing.mk W Y = 0 := by
    rw [zero_smul, add_zero, sub_smul, ← Algebra.algebraMap_eq_smul_one,
      ← Algebra.algebraMap_eq_smul_one, h, sub_self]
  exact sub_eq_zero.mp (CoordinateRing.smul_basis_eq_zero h0).1

theorem es1a8_addInt_basisX_cmp :
    IsTranscendenceBasis F (fun _ : PUnit.{u + 1} => polyToFunctionField W X) := by
  have h1 : Algebra.IsAlgebraic F[X] W.CoordinateRing :=
    es1a8_addInt_coordRing_isAlgebraic_cmp (W := W)
  have h2 : Algebra.IsAlgebraic W.CoordinateRing W.FunctionField :=
    es1a8_addInt_functionField_isAlgebraic_cmp (W := W)
  have h3 : FaithfulSMul F[X] W.CoordinateRing :=
    (faithfulSMul_iff_algebraMap_injective F[X] W.CoordinateRing).mpr
      es1a8_addInt_algebraMap_injective_cmp
  have h4 : FaithfulSMul W.CoordinateRing W.FunctionField :=
    (faithfulSMul_iff_algebraMap_injective W.CoordinateRing W.FunctionField).mpr
      (IsFractionRing.injective W.CoordinateRing W.FunctionField)
  have h5 := IsTranscendenceBasis.polynomial PUnit.{u + 1} F
  have h6 := h5.algebraMap_comp (A := W.CoordinateRing)
  have h7 := h6.algebraMap_comp (A := W.FunctionField)
  have h8 : (fun _ : PUnit.{u + 1} => polyToFunctionField W X)
      = (algebraMap W.CoordinateRing W.FunctionField
          ∘ (algebraMap F[X] W.CoordinateRing ∘ fun _ : PUnit.{u + 1} => (X : F[X]))) :=
    rfl
  rw [h8]
  exact h7

theorem es1a8_addInt_basis_of_transcendental_cmp {z : W.FunctionField}
    (hz : Transcendental F z) :
    IsTranscendenceBasis F ((↑) : ({z} : Set W.FunctionField) → W.FunctionField) := by
  have hind : AlgebraicIndepOn F id ({z} : Set W.FunctionField) :=
    algebraicIndependent_unique_type_iff.mpr (by simpa using hz)
  obtain ⟨t, hzt, ht⟩ := exists_isTranscendenceBasis_superset hind
  have hcard : Cardinal.mk ↥t = Cardinal.mk PUnit.{u + 1} :=
    IsTranscendenceBasis.cardinalMk_eq ht es1a8_addInt_basisX_cmp
  have hsub : t.Subsingleton := by
    have h1 : Cardinal.mk ↥t = 1 := by rw [hcard, Cardinal.mk_punit]
    exact Cardinal.mk_le_one_iff_set_subsingleton.mp h1.le
  have ht2 : t = {z} := hsub.eq_singleton_of_mem (hzt rfl)
  rw [ht2] at ht
  exact ht

theorem es1a8_addInt_isAlgebraic_adjoin_cmp {z : W.FunctionField}
    (hz : Transcendental F z) :
    Algebra.IsAlgebraic (IntermediateField.adjoin F ({z} : Set W.FunctionField))
      W.FunctionField := by
  have h := (es1a8_addInt_basis_of_transcendental_cmp hz).isAlgebraic_field
  rwa [Subtype.range_coe] at h

theorem es1a8_addInt_selfHom_isIntegral_cmp (ι : W.FunctionField →ₐ[F] W.FunctionField)
    (htr : Transcendental F (ι (polyToFunctionField W X))) :
    ι.toRingHom.IsIntegral := by
  intro w
  have hint : _root_.IsIntegral (IntermediateField.adjoin F
      ({ι (polyToFunctionField W X)} : Set W.FunctionField)) w :=
    isAlgebraic_iff_isIntegral.mp
      ((es1a8_addInt_isAlgebraic_adjoin_cmp htr).isAlgebraic w)
  obtain ⟨p, hpm, hp0⟩ := hint
  have hle : IntermediateField.adjoin F
      ({ι (polyToFunctionField W X)} : Set W.FunctionField) ≤ ι.fieldRange :=
    IntermediateField.adjoin_le_iff.mpr
      (Set.singleton_subset_iff.mpr ⟨polyToFunctionField W X, rfl⟩)
  refine ⟨p.map (((AlgEquiv.ofInjectiveField ι :
      W.FunctionField ≃ₐ[F] ι.fieldRange)).symm.toAlgHom.comp
    (IntermediateField.inclusion hle)).toRingHom, hpm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : ι.toRingHom.comp (((AlgEquiv.ofInjectiveField ι :
      W.FunctionField ≃ₐ[F] ι.fieldRange)).symm.toAlgHom.comp
      (IntermediateField.inclusion hle)).toRingHom
      = algebraMap (IntermediateField.adjoin F
          ({ι (polyToFunctionField W X)} : Set W.FunctionField)) W.FunctionField := by
    refine RingHom.ext fun u => ?_
    have h1 : (AlgEquiv.ofInjectiveField ι : W.FunctionField ≃ₐ[F] ι.fieldRange)
        ((AlgEquiv.ofInjectiveField ι : W.FunctionField ≃ₐ[F] ι.fieldRange).symm
          (IntermediateField.inclusion hle u))
        = IntermediateField.inclusion hle u :=
      (AlgEquiv.ofInjectiveField ι :
        W.FunctionField ≃ₐ[F] ι.fieldRange).apply_symm_apply _
    exact congrArg Subtype.val h1
  rw [hcomp]
  exact hp0

theorem es1a8_addInt_selfHom_finiteAlong_cmp (ι : W.FunctionField →ₐ[F] W.FunctionField)
    (htr : Transcendental F (ι (polyToFunctionField W X))) :
    FiniteAlong F ι := by
  have hint := es1a8_addInt_selfHom_isIntegral_cmp ι htr
  let : Algebra W.FunctionField W.FunctionField := ι.toRingHom.toAlgebra
  let : Module W.FunctionField W.FunctionField := Algebra.toModule
  change Module.Finite W.FunctionField W.FunctionField
  have hadj : IntermediateField.adjoin W.FunctionField
      ({polyToFunctionField W X, yGen W} : Set W.FunctionField) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    set L := IntermediateField.adjoin W.FunctionField
      ({polyToFunctionField W X, yGen W} : Set W.FunctionField) with hL
    have hconst : ∀ c : F, algebraMap F W.FunctionField c ∈ L := fun c => by
      rw [← ι.commutes c]
      exact L.algebraMap_mem _
    have hxmem : polyToFunctionField W X ∈ L :=
      IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
    have hymem : yGen W ∈ L :=
      IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
    have hpoly : ∀ p : F[X], polyToFunctionField W p ∈ L := fun p => by
      induction p using Polynomial.induction_on' with
      | add f g hf hg => rw [map_add]; exact add_mem hf hg
      | monomial n c =>
          rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, polyToFunctionField_C]
          exact mul_mem (hconst c) (pow_mem hxmem n)
    have hcr : ∀ r : W.CoordinateRing,
        algebraMap W.CoordinateRing W.FunctionField r ∈ L := fun r => by
      obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
      rw [algebraMap_smul_basis]
      exact add_mem (hpoly p) (mul_mem (hpoly q) hymem)
    obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
    rw [← hab]
    exact div_mem (hcr a) (hcr b)
  have : Finite ({polyToFunctionField W X, yGen W} : Set W.FunctionField) :=
    ((Set.finite_singleton (yGen W)).insert (polyToFunctionField W X)).to_subtype
  have h1 : FiniteDimensional W.FunctionField
      (IntermediateField.adjoin W.FunctionField
        ({polyToFunctionField W X, yGen W} : Set W.FunctionField)) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => hint z
  rw [hadj] at h1
  exact (IntermediateField.topEquiv (F := W.FunctionField)
    (E := W.FunctionField)).toLinearEquiv.finiteDimensional

end IntegralityEngineCmp
end Es1a1
end ModularCurve
end
end

section

section

namespace ModularCurve

namespace Es1a1

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

public abbrev kw_hk5f_addSumXNonConstGuardAt : Prop :=
  ∀ D₁ D₂ : IsogenyEndDatum W, D₁.pointEnd' + D₂.pointEnd' ≠ 0 →
    ∀ c : F, es1a6_addSumX W D₁.ι D₂.ι ≠ algebraMap F W.FunctionField c

abbrev kw_hk5f_addSumCoordSeamDataNCAt : Prop :=
  ∀ φ₁ φ₂ : W.FunctionField →ₐ[F] W.FunctionField,
    ¬ es1a6_addCollapse W φ₁ φ₂ →
    (∀ c : F, es1a6_addSumX W φ₁ φ₂ ≠ algebraMap F W.FunctionField c) →
    ∀ (v : AlgebraicCurve.Place F W.FunctionField) (Q₁ Q₂ : W.Point),
      es1a11_coordSeamDataAt φ₁ v Q₁ → es1a11_coordSeamDataAt φ₂ v Q₂ →
      es1a6_addSumSeamDataAt φ₁ φ₂ v (Q₁ + Q₂)

public abbrev kw_hk5f_addIntegralFiniteDataAt : Prop :=
  ∀ D₁ D₂ : IsogenyEndDatum W,
    ∀ (hcol : ¬ es1a6_addCollapse W D₁.ι D₂.ι)
      (htr : Function.Injective (Polynomial.aeval (R := F) (es1a6_addSumX W D₁.ι D₂.ι))),
      (es1a6_addSumPullbackHom W D₁.ι D₂.ι hcol htr).toRingHom.IsIntegral ∧
        FiniteAlong F (es1a6_addSumPullbackHom W D₁.ι D₂.ι hcol htr)

theorem kw_hk5f_addGeomMorphSupply_of_atoms
    (hg : kw_hk5f_addSumXNonConstGuardAt W)
    (hncseam : kw_hk5f_addSumCoordSeamDataNCAt W)
    (hifd : kw_hk5f_addIntegralFiniteDataAt W) :
    KwIsogenyEndAddGeomMorphSupply W := by
  intro D₁ D₂ h0
  have hcol : ¬ es1a6_addCollapse W D₁.ι D₂.ι := by
    have := es1a8_add_not_collapse_of_pointEnd_add_ne_zero_cmp D₁ D₂ h0
    rwa [show es1a8_addCollapse_cmp W D₁.ι D₂.ι = es1a6_addCollapse W D₁.ι D₂.ι from rfl]
      at this
  have hnc := hg D₁ D₂ h0
  have htr : Function.Injective
      (Polynomial.aeval (R := F) (es1a6_addSumX W D₁.ι D₂.ι)) :=
    es1a6_add_aeval_sumX_injective_of_forall_ne W D₁.ι D₂.ι hnc
  obtain ⟨hι, hfin⟩ := hifd D₁ D₂ hcol htr
  refine ⟨⟨es1a6_addSumPullbackHom W D₁.ι D₂.ι hcol htr, hι, hfin⟩, fun P => ?_⟩
  have h1 := kw_coordSeamDataAt_geomMorph D₁ P
  have h2 := kw_coordSeamDataAt_geomMorph D₂ P
  have hsum := hncseam D₁.ι D₂.ι hcol hnc (placeOfPoint P)
    (D₁.geomMorph P) (D₂.geomMorph P) h1 h2
  have hseam := es1a6_addSumSeam_of_data D₁.ι D₂.ι hcol htr hι P
    (D₁.geomMorph P + D₂.geomMorph P) hsum
  exact placeOfPoint_injective
    (((⟨_, hι, hfin⟩ : IsogenyEndDatum W).placeOfPoint_geomMorph P).symm.trans hseam)

end Es1a1
end ModularCurve
end
end

section

section

namespace ModularCurve
namespace Mmr62

open ModularCurve.Es1a1

section CollisionEngine

attribute [local instance] ModularCurve.Es1a1.instDecEqFunctionFieldEs1a6Add

universe u

variable {F : Type u} [Field F]

variable (W : WeierstrassCurve.Affine F)

variable (φ₁ φ₂ : W.FunctionField →ₐ[F] W.FunctionField)

theorem mmr62_cd_collision_yGen_eq
    (hx : φ₁ (polyToFunctionField W X) = φ₂ (polyToFunctionField W X))
    (hcol : ¬ es1a6_addCollapse W φ₁ φ₂) :
    φ₁ (yGen W) = φ₂ (yGen W) := by
  have _pin := Classical.em True
  rcases Y_eq_of_X_eq (es1a6_add_equation W φ₁) (es1a6_add_equation W φ₂) hx with h | h
  · exact h
  · exact absurd ⟨hx, h⟩ hcol

theorem mmr62_cd_phi_yGen_ne_negY [CharZero F]
    (φ : W.FunctionField →ₐ[F] W.FunctionField) :
    φ (yGen W) ≠ (W.map (algebraMap F W.FunctionField)).toAffine.negY
      (φ (polyToFunctionField W X)) (φ (yGen W)) := by
  have _pin := Classical.em True
  have hmap : φ ((W.map (algebraMap F W.FunctionField)).toAffine.negY
        (polyToFunctionField W X) (yGen W))
      = (W.map (algebraMap F W.FunctionField)).toAffine.negY
          (φ (polyToFunctionField W X)) (φ (yGen W)) := by
    simp only [negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_sub, _root_.map_neg,
      map_mul,
      AlgHom.commutes]
  intro hcon
  have h2 : φ (yGen W)
      = φ ((W.map (algebraMap F W.FunctionField)).toAffine.negY
          (polyToFunctionField W X) (yGen W)) := by
    rw [hmap]
    exact hcon
  exact endst20_ps_yGen_ne_negY W
    (RingHom.injective (φ : W.FunctionField →+* W.FunctionField) h2)

theorem mmr62_cd_map_dupSlope_eq_slope [CharZero F]
    (φ : W.FunctionField →ₐ[F] W.FunctionField) :
    φ (endst20_ps_dupSlope W)
      = (W.map (algebraMap F W.FunctionField)).toAffine.slope
          (φ (polyToFunctionField W X)) (φ (polyToFunctionField W X))
          (φ (yGen W)) (φ (yGen W)) := by
  have _pin := Classical.em True
  rw [endst20_ps_dupSlope_eq_div W,
    slope_of_Y_ne rfl (mmr62_cd_phi_yGen_ne_negY W φ)]
  simp only [negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄,
    map_div₀, map_add, map_sub, map_mul, map_pow, _root_.map_neg, map_ofNat,
    AlgHom.commutes]

theorem mmr62_cd_collision_addSumX_eq_map_dupX [CharZero F]
    (hx : φ₁ (polyToFunctionField W X) = φ₂ (polyToFunctionField W X))
    (hcol : ¬ es1a6_addCollapse W φ₁ φ₂) :
    es1a6_addSumX W φ₁ φ₂ = φ₂ (endst20_ps_dupX W) := by
  have _pin := Classical.em True
  have hy := mmr62_cd_collision_yGen_eq W φ₁ φ₂ hx hcol
  have hslope := mmr62_cd_map_dupSlope_eq_slope W φ₂
  unfold es1a6_addSumX endst20_ps_dupX
  rw [hx, hy, ← hslope]
  simp only [addX, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, map_add, map_sub, map_mul,
    map_pow, AlgHom.commutes]

theorem mmr62_cd_map_dupX_transcendental [IsAlgClosed F] [CharZero F]
    (φ : W.FunctionField →ₐ[F] W.FunctionField) :
    Transcendental F (φ (endst20_ps_dupX W)) := by
  have _pin := Classical.em True
  intro halg
  obtain ⟨p, hp0, hp⟩ := halg
  refine endst20_ps_transcendental_dupX W ⟨p, hp0, ?_⟩
  have h2 : φ (Polynomial.aeval (endst20_ps_dupX W) p) = 0 := by
    rw [← Polynomial.aeval_algHom_apply]
    exact hp
  exact RingHom.injective (φ : W.FunctionField →+* W.FunctionField)
    (h2.trans (_root_.map_zero (φ : W.FunctionField →+* W.FunctionField)).symm)

theorem mmr62_cd_collision_addSumX_transcendental [IsAlgClosed F] [CharZero F]
    (hx : φ₁ (polyToFunctionField W X) = φ₂ (polyToFunctionField W X))
    (hcol : ¬ es1a6_addCollapse W φ₁ φ₂) :
    Transcendental F (es1a6_addSumX W φ₁ φ₂) := by
  have _pin := Classical.em True
  rw [mmr62_cd_collision_addSumX_eq_map_dupX W φ₁ φ₂ hx hcol]
  exact mmr62_cd_map_dupX_transcendental W φ₂

theorem mmr62_cd_collision_addSumX_ne_const [IsAlgClosed F] [CharZero F]
    (hx : φ₁ (polyToFunctionField W X) = φ₂ (polyToFunctionField W X))
    (hcol : ¬ es1a6_addCollapse W φ₁ φ₂) (c : F) :
    es1a6_addSumX W φ₁ φ₂ ≠ algebraMap F W.FunctionField c := by
  have _pin := Classical.em True
  intro hc
  refine mmr62_cd_collision_addSumX_transcendental W φ₁ φ₂ hx hcol ?_
  rw [hc]
  exact isAlgebraic_algebraMap c

theorem mmr62_cd_not_collapse_of_not_collapse_cmp
    (h : ¬ es1a8_addCollapse_cmp W φ₁ φ₂) :
    ¬ es1a6_addCollapse W φ₁ φ₂ := by
  have _pin := Classical.em True
  intro hc
  exact h ⟨hc.1, hc.2⟩

end CollisionEngine
end Mmr62
end ModularCurve
end
end

section

section

namespace ModularCurve

namespace Es1a1

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

public section publicSection

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem kw_hk5f_addIntegralFiniteDataAt_proved : kw_hk5f_addIntegralFiniteDataAt W := by
  intro D₁ D₂ hcol htr
  have htrans : Transcendental F
      (es1a6_addSumPullbackHom W D₁.ι D₂.ι hcol htr (polyToFunctionField W X)) := by
    rw [es1a6_addSumPullbackHom_X]
    exact transcendental_iff_injective.mpr htr
  exact ⟨es1a8_addInt_selfHom_isIntegral_cmp _ htrans,
    es1a8_addInt_selfHom_finiteAlong_cmp _ htrans⟩

theorem kw_hk5f_addSumCoordSeamDataNCAt_proved
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    ∀ φ₁ φ₂ : W.FunctionField →ₐ[F] W.FunctionField,
      ¬ es1a6_addCollapse W φ₁ φ₂ →
      (∀ c : F, es1a6_addSumX W φ₁ φ₂ ≠ algebraMap F W.FunctionField c) →
      ∀ (v : AlgebraicCurve.Place F W.FunctionField) (Q₁ Q₂ : W.Point),
        es1a11_coordSeamDataAt φ₁ v Q₁ → es1a11_coordSeamDataAt φ₂ v Q₂ →
        es1a6_addSumSeamDataAt φ₁ φ₂ v (Q₁ + Q₂) := by
  intro φ₁ φ₂ hcol hnc v Q₁ Q₂ h1 h2
  have E := @WeierstrassCurve.Affine.FunctionField.addX_addY_specialize_at_place F _ _ _ W _
    instDecEqFunctionFieldEs1a6Add φ₁ φ₂
    (fun hc => hcol hc) hnc v Q₁ Q₂
    (fun h0 => by subst h0; exact h1) (fun a b h hs => by subst hs; exact h1)
    (fun h0 => by subst h0; exact h2) (fun a b h hs => by subst hs; exact h2)
  cases hQ : Q₁ + Q₂ with
  | zero => exact E.1 hQ
  | some a b h => exact E.2 a b h hQ

end publicSection

end Es1a1
end ModularCurve
end
end

section

section

namespace ModularCurve

namespace Es1a1

open ModularCurve.Mmr46 ModularCurve.Mmr62 ModularCurve.Mmr72 ModularCurve.Mmr73

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

omit [IsAlgClosed F] [W.IsElliptic] [GenusOnePlaceGate.IsCentred W] in
theorem kw_hk5f_two_datum_pointEnd_add_eq_geomMorph
    (D₁ D₂ : IsogenyEndDatum W) (Q : W.Point) :
    (D₁.pointEnd' + D₂.pointEnd') Q
      = (D₁.geomMorph Q + D₂.geomMorph Q) - (D₁.geomMorph 0 + D₂.geomMorph 0) := by
  have h : (D₁.pointEnd' + D₂.pointEnd') Q = D₁.pointEnd' Q + D₂.pointEnd' Q := rfl
  rw [h, D₁.pointEnd_eq_geomMorph_sub_geomMorph_zero Q,
    D₂.pointEnd_eq_geomMorph_sub_geomMorph_zero Q]
  abel

omit [GenusOnePlaceGate.IsCentred W] in
theorem kw_hk5f_pointEnd_add_eq_zero_of_cofinite_geomMorph_sum
    (D₁ D₂ : IsogenyEndDatum W) (T : W.Point)
    (hcof : {Q : W.Point | D₁.geomMorph Q + D₂.geomMorph Q ≠ T}.Finite) :
    D₁.pointEnd' + D₂.pointEnd' = 0 := by
  have : Infinite W.Point := WeierstrassCurve.point_infinite _
  refine mmr72_pp_end_eq_zero_of_cofinite_const (D₁.pointEnd' + D₂.pointEnd')
    (T - (D₁.geomMorph 0 + D₂.geomMorph 0)) (hcof.subset ?_)
  intro Q hQ hT
  exact hQ (by rw [kw_hk5f_two_datum_pointEnd_add_eq_geomMorph W D₁ D₂ Q, hT])

theorem kw_hk5f_collision_pointEnd_add_eq_zero
    (D₁ D₂ : IsogenyEndDatum W)
    (hX : D₁.ι (polyToFunctionField W X) = D₂.ι (polyToFunctionField W X))
    (c : F) (hx : es1a6_addSumX W D₁.ι D₂.ι = algebraMap F W.FunctionField c) :
    D₁.pointEnd' + D₂.pointEnd' = 0 := by
  by_cases hcol : es1a8_addCollapse_cmp W D₁.ι D₂.ι
  · exact es1a8_addCollapse_pointEnd_add_eq_zero_cmp D₁ D₂ hcol
  · exact absurd hx (mmr62_cd_collision_addSumX_ne_const W D₁.ι D₂.ι hX
      (mmr62_cd_not_collapse_of_not_collapse_cmp W D₁.ι D₂.ι hcol) c)

omit [W.AbelTheorem] in
theorem kw_hk5f_transversal_cofinite_geomMorph_sum
    (D₁ D₂ : IsogenyEndDatum W)
    (hX : D₁.ι (polyToFunctionField W X) ≠ D₂.ι (polyToFunctionField W X))
    (c d : F) (hEq : W.Equation c d)
    (hx : es1a6_addSumX W D₁.ι D₂.ι = algebraMap F W.FunctionField c)
    (hy : es1a6_addSumY W D₁.ι D₂.ι = algebraMap F W.FunctionField d) :
    ∃ T : W.Point, {Q : W.Point | D₁.geomMorph Q + D₂.geomMorph Q ≠ T}.Finite := by
  have : HasPrincipalDivisors F W.FunctionField := hasPrincipalDivisors_functionField _
  have hcd : W.Nonsingular c d :=
    (equation_iff_nonsingular_of_Δ_ne_zero isElliptic_Δ_ne_zero).mp hEq
  refine ⟨Point.some c d hcd, ?_⟩
  have hxne : polyToFunctionField W X ≠ 0 :=
    polyToFunctionField_ne_zero Polynomial.X_ne_zero
  have hyne : yGen W ≠ 0 := Y_image_ne_zero
  have hf₁ne : D₁.ι (polyToFunctionField W X) ≠ 0 := mmr73_cs_iota_ne_zero D₁ hxne
  have hf₂ne : D₂.ι (polyToFunctionField W X) ≠ 0 := mmr73_cs_iota_ne_zero D₂ hxne
  have hg₁ne : D₁.ι (yGen W) ≠ 0 := mmr73_cs_iota_ne_zero D₁ hyne
  have hg₂ne : D₂.ι (yGen W) ≠ 0 := mmr73_cs_iota_ne_zero D₂ hyne
  have hδne : D₁.ι (polyToFunctionField W X) - D₂.ι (polyToFunctionField W X) ≠ 0 :=
    sub_ne_zero.mpr hX
  refine Set.Finite.subset
    (((((mmr73_cs_finite_setOf_placeOfPoint_ord_ne_zero hf₁ne).union
      (mmr73_cs_finite_setOf_placeOfPoint_ord_ne_zero hf₂ne)).union
      (mmr73_cs_finite_setOf_placeOfPoint_ord_ne_zero hg₁ne)).union
      (mmr73_cs_finite_setOf_placeOfPoint_ord_ne_zero hg₂ne)).union
      (mmr73_cs_finite_setOf_placeOfPoint_ord_ne_zero hδne)) ?_
  intro Q hQ
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  by_contra hbad
  push Not at hbad
  obtain ⟨⟨⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩, hb5⟩ := hbad
  exact hQ (mmr73_cs_geomMorph_add_eq_of_addSum_const D₁ D₂ hX hcd hx hy Q
    hb1 hb2 hb3 hb4 hb5)

public section publicSection

theorem kw_hk5f_addSumXNonConstGuardAt_proved : kw_hk5f_addSumXNonConstGuardAt W := by
  intro D₁ D₂ h0
  refine mmr46_gc_addSumX_ne_const_of_not_constPoint W D₁.ι D₂.ι ?_ ?_
  · intro hc
    exact es1a8_add_not_collapse_of_pointEnd_add_ne_zero_cmp D₁ D₂ h0 ⟨hc.1, hc.2⟩
  · rintro c d hEq ⟨hx, hy⟩
    by_cases hX : D₁.ι (polyToFunctionField W X) = D₂.ι (polyToFunctionField W X)
    · exact h0 (kw_hk5f_collision_pointEnd_add_eq_zero W D₁ D₂ hX c hx)
    · obtain ⟨T, hT⟩ :=
        kw_hk5f_transversal_cofinite_geomMorph_sum W D₁ D₂ hX c d hEq hx hy
      exact h0 (kw_hk5f_pointEnd_add_eq_zero_of_cofinite_geomMorph_sum W D₁ D₂ T hT)

end publicSection

end Es1a1
end ModularCurve
end
end

section

section

namespace ModularCurve

namespace Es1a1

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

public section publicSection

theorem kw_hk5f_addGeomMorphSupply_proved :
    KwIsogenyEndAddGeomMorphSupply W :=
  kw_hk5f_addGeomMorphSupply_of_atoms W
    (kw_hk5f_addSumXNonConstGuardAt_proved W)
    (kw_hk5f_addSumCoordSeamDataNCAt_proved W)
    (kw_hk5f_addIntegralFiniteDataAt_proved W)

theorem kw_hk5f_addDatumSupply_proved :
    KwIsogenyEndAddDatumSupply W :=
  kw_isogenyEndAddDatumSupply_of_addGeomMorphSupply W
    (kw_hk5f_addGeomMorphSupply_proved W)

end publicSection

end Es1a1
end ModularCurve
end
end

end
end

section FunctionFieldBaseChange

universe u v w

open Polynomial IsDedekindDomain IsLocalRing WithZero WeierstrassCurve Affine CoordinateRing
  AlgebraicCurve
open scoped TensorProduct Polynomial.Bivariate

noncomputable section

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

public section publicSection

theorem exists_sub_algebraMap_mem {x y : F} (h : W.Equation x y) (r : W.CoordinateRing) :
    ∃ c : F, r - algebraMap F W.CoordinateRing c ∈ XYIdeal W x (C y) := by
  set e := quotientXYIdealEquiv (W' := W) (x := x) (y := C y) h
  refine ⟨e (Ideal.Quotient.mk _ r), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  apply e.injective
  rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes,
    Algebra.algebraMap_self_apply]

end publicSection

end WeierstrassCurve.Affine.CoordinateRing

public section publicSection

open scoped WeierstrassCurve in
theorem WeierstrassCurve.nonempty_pointTorsionBy_zmod {K : Type*} [Field K] [DecidableEq K]
    [IsAlgClosed K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : 1 ≤ n) :
    Nonempty (↥(Submodule.torsionBy ℤ W.toAffine.Point (n : ℤ)) ≃+ (Fin 2 → ZMod n)) := by
  obtain ⟨e⟩ := AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    (A := W.toAffine.Point) (n := n) (by omega)
    (fun d hd => WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed W (n := d)
      (by exact_mod_cast (Nat.pos_of_dvd_of_pos hd (by omega)).ne'))
  exact ⟨e.symm.trans (LinearEquiv.piFinTwo ℤ (fun _ : Fin 2 => ZMod n)).toAddEquiv.symm⟩

end publicSection

namespace ModularCurve

@[expose] public def kw_coordinateRingBasis {R : Type*} [CommRing R] (V : Affine R) :
    Module.Basis (ℕ × Fin 2) R V.CoordinateRing :=
  (Polynomial.basisMonomials R).smulTower (CoordinateRing.basis V)

end ModularCurve

namespace WeierstrassCurve.Affine

section

variable {F : Type*} [Field F] {W : Affine F}

public section publicSection

theorem kw_functionField_algHom_ext {L : Type*} [Field L] [Algebra F L]
    {f g : W.FunctionField →ₐ[F] L}
    (hX : f (polyToFunctionField W X) = g (polyToFunctionField W X))
    (hy : f (yGen W) = g (yGen W)) : f = g := by
  have hCR : ∀ r : W.CoordinateRing,
      f (algebraMap W.CoordinateRing W.FunctionField r)
        = g (algebraMap W.CoordinateRing W.FunctionField r) := by
    intro r
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
    have hFX : ∀ c : F[X], f (algebraMap W.CoordinateRing W.FunctionField
          (algebraMap F[X] W.CoordinateRing c))
        = g (algebraMap W.CoordinateRing W.FunctionField
          (algebraMap F[X] W.CoordinateRing c)) :=
      fun c => DFunLike.congr_fun
        (Polynomial.algHom_ext (f := (f.comp (IsScalarTower.toAlgHom F W.CoordinateRing
            W.FunctionField)).comp (IsScalarTower.toAlgHom F F[X] W.CoordinateRing))
          (g := (g.comp (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField)).comp
            (IsScalarTower.toAlgHom F F[X] W.CoordinateRing)) hX) c
    have hFX' : ∀ c : F[X], f (algebraMap W.CoordinateRing W.FunctionField
          (AdjoinRoot.mk W.polynomial (C c)))
        = g (algebraMap W.CoordinateRing W.FunctionField
          (AdjoinRoot.mk W.polynomial (C c))) := fun c => by
      rw [show AdjoinRoot.mk W.polynomial (C c) = algebraMap F[X] W.CoordinateRing c from rfl]
      exact hFX c
    have hy' : f (algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.mk W.polynomial Y))
        = g (algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.mk W.polynomial Y)) := hy
    induction p using Polynomial.induction_on with
    | C c => exact hFX' c
    | monomial n c _ => simp only [map_mul, map_pow, hy', hFX' c]
    | add p q hp hq => simp only [map_add, hp, hq]
  refine AlgHom.ext fun a => ?_
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) a
  simp only [map_div₀, hCR p, hCR q]

end publicSection

end

section PointPullbackTo

variable {F : Type u} [Field F] {W : Affine F} {L : Type v} [Field L] [Algebra F L]

public section publicSection

theorem eval₂_polynomial_of_equation_map_target {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP) :
    W.polynomial.eval₂
      (Polynomial.aeval xP : F[X] →ₐ[F] L).toRingHom yP = 0 := by
  rw [equation_iff'] at h
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X]
  linear_combination h

end publicSection

@[expose] public def pointPullbackCoordHomTo {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP) :
    W.CoordinateRing →ₐ[F] L where
  __ := AdjoinRoot.lift
    (Polynomial.aeval xP : F[X] →ₐ[F] L).toRingHom
    yP (eval₂_polynomial_of_equation_map_target h)
  commutes' c := by
    change AdjoinRoot.lift _ _ (eval₂_polynomial_of_equation_map_target h) (algebraMap F _ c)
      = algebraMap F L c
    rw [CoordinateRing.algebraMap_eq_mk_C_C, AdjoinRoot.lift_mk, eval₂_C]
    exact Polynomial.aeval_C _ c

public section publicSection

theorem pointPullbackCoordHomTo_mk {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP) (g : F[X][Y]) :
    pointPullbackCoordHomTo h (CoordinateRing.mk W g)
      = g.eval₂ (Polynomial.aeval xP : F[X] →ₐ[F] L).toRingHom yP :=
  AdjoinRoot.lift_mk (eval₂_polynomial_of_equation_map_target h) g

theorem pointPullbackCoordHomTo_comp_algebraMap {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP) :
    (pointPullbackCoordHomTo h).toRingHom.comp (algebraMap F[X] W.CoordinateRing)
      = (Polynomial.aeval xP : F[X] →ₐ[F] L).toRingHom := by
  refine RingHom.ext fun p => ?_
  change pointPullbackCoordHomTo h (algebraMap F[X] _ p) = _
  rw [algebraMap_polynomial_eq_mk_C, pointPullbackCoordHomTo_mk, eval₂_C]

theorem pointPullbackCoordHomTo_injective {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    Function.Injective (pointPullbackCoordHomTo h) := by
  have hker : RingHom.ker (pointPullbackCoordHomTo h).toRingHom = ⊥ := by
    have : Module.Finite F[X] W.CoordinateRing :=
      Module.Finite.of_basis (CoordinateRing.basis W)
    refine Ideal.eq_bot_of_under_eq_bot (R := F[X]) ?_
    rw [Ideal.under_def, RingHom.comap_ker, pointPullbackCoordHomTo_comp_algebraMap,
      ← RingHom.injective_iff_ker_eq_bot]
    exact hx
  exact (RingHom.injective_iff_ker_eq_bot (pointPullbackCoordHomTo h).toRingHom).mpr hker

end publicSection

@[expose] public def pointPullbackHomTo {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    W.FunctionField →ₐ[F] L :=
  IsFractionRing.liftAlgHom (pointPullbackCoordHomTo_injective h hx)

public section publicSection

theorem pointPullbackHomTo_algebraMap {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) (r : W.CoordinateRing) :
    pointPullbackHomTo h hx (algebraMap W.CoordinateRing W.FunctionField r)
      = pointPullbackCoordHomTo h r :=
  IsFractionRing.lift_algebraMap (pointPullbackCoordHomTo_injective h hx) r

theorem pointPullbackHomTo_polyToFunctionField_X {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    pointPullbackHomTo h hx (polyToFunctionField W X) = xP := by
  rw [polyToFunctionField_apply, pointPullbackHomTo_algebraMap,
    algebraMap_polynomial_eq_mk_C, pointPullbackCoordHomTo_mk, eval₂_C]
  exact Polynomial.aeval_X _

theorem pointPullbackHomTo_yGen {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    pointPullbackHomTo h hx (yGen W) = yP := by
  change pointPullbackHomTo h hx (algebraMap _ _ (CoordinateRing.mk W Y)) = _
  rw [pointPullbackHomTo_algebraMap, pointPullbackCoordHomTo_mk]
  exact eval₂_X _ _

end publicSection

end PointPullbackTo

end WeierstrassCurve.Affine

namespace ModularCurve

section GeomMorphBC

variable {K : Type*} [Field K] [DecidableEq K]
variable {E E' : Affine K} [GenusOnePlaceGate E] [AbelTheorem E]
  [GenusOnePlaceGate E'] [AbelTheorem E']
variable (ι : E'.FunctionField →ₐ[K] E.FunctionField)
variable (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) (hN : NormFormulaAlong K ι hfin)

@[expose] public def kw_fdn2_qephod_hend7_geomMorphBC : E.Point → E'.Point :=
  fun P => (placeOfPointEquiv E').symm ((placeOfPoint P).restrictAlong ι hι)

local notation "gBC" => kw_fdn2_qephod_hend7_geomMorphBC ι hι

public section publicSection

omit [DecidableEq K] [E.AbelTheorem] [E'.AbelTheorem] in
theorem kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC (P : E.Point) :
    (placeOfPoint P).restrictAlong ι hι = placeOfPoint (gBC P) :=
  (placeOfPoint_placeOfPointEquiv_symm E' _).symm

omit [DecidableEq K] [E.AbelTheorem] [E'.AbelTheorem] in
theorem kw_fdn2_qephod_hend7_pushforwardDegZero_pointDivisor_geomMorphBC (P : E.Point) :
    Pic0.pushforwardAlongDegZero ι hι (pointDivisor P)
      = pointDivisor (gBC P) - pointDivisor (gBC 0) := by
  refine Subtype.ext ?_
  rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, map_sub,
    pushforwardAlong_single_eq ι hι, pushforwardAlong_single_eq ι hι,
    kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι hι P,
    kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι hι 0]
  push_cast
  rw [coe_pointDivisor, coe_pointDivisor, sub_sub_sub_cancel_right]

omit [DecidableEq K] [E.AbelTheorem] [E'.AbelTheorem] in
theorem kw_fdn2_qephod_hend7_pushforwardHom_pointClass_eq_sub (P : E.Point) :
    Pic0.pushforwardAlongHom ι hι hfin hN
        (pointClass P)
      = pointClass (gBC P) - pointClass (gBC 0) := by
  change Pic0.pushforwardAlongHom ι hι hfin _ (Pic0.mk (pointDivisor P))
      = Pic0.mk (pointDivisor (gBC P)) - Pic0.mk (pointDivisor (gBC 0))
  rw [Pic0.pushforwardAlongHom_mk,
    kw_fdn2_qephod_hend7_pushforwardDegZero_pointDivisor_geomMorphBC ι hι P]
  rfl

theorem kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub (P : E.Point) :
    pointMapOfPushforward ι hι hfin hN P
      = gBC P - gBC 0 := by
  rw [pointMapOfPushforward_apply,
    kw_fdn2_qephod_hend7_pushforwardHom_pointClass_eq_sub ι hι hfin hN P, map_sub,
    genusOnePic0Equiv_apply, genusOnePic0Equiv_apply, pic0ToPoint_pointClass,
    pic0ToPoint_pointClass]

end publicSection

end GeomMorphBC

section ScalarExtension

variable {R₀ : Type u} [Field R₀] (W : WeierstrassCurve R₀)
variable (F : Type v) [Field F] [Algebra R₀ F]
variable (F' : Type w) [Field F'] [Algebra R₀ F']
variable [Algebra F F'] [IsScalarTower R₀ F F']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

public section publicSection

omit [Algebra R₀ F] [IsScalarTower R₀ F F'] in
theorem kw_transcendental_polyToFunctionField_X_over_baseGeneral :
    Transcendental F (polyToFunctionField (W⁄F') X) := by
  classical
  exact
    Transcendental.of_tower_top F (L := F')
      (transcendental_polyToFunctionField_X (W := (W⁄F')))

theorem kw_equation_map_polyToFunctionField_yGen_over_baseGeneral :
    ((W⁄F).map (algebraMap F (W⁄F').FunctionField)).toAffine.Equation
      (polyToFunctionField (W⁄F') X) (yGen (W⁄F')) := by
  classical
  have hcurve : (W⁄F).map (algebraMap F (W⁄F').FunctionField)
      = (W⁄F').map (algebraMap F' (W⁄F').FunctionField) := by
    change (W.map _).map _ = (W.map _).map _
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
    congr 1
    exact ((IsScalarTower.algebraMap_eq R₀ F (W⁄F').FunctionField).symm).trans
      (IsScalarTower.algebraMap_eq R₀ F' (W⁄F').FunctionField)
  exact hcurve ▸ equation_map_polyToFunctionField_yGen (W := (W⁄F'))

end publicSection

@[expose] public def kw_functionFieldMapAlongGeneral :
    (W⁄F).FunctionField →ₐ[F] (W⁄F').FunctionField :=
  pointPullbackHomTo (kw_equation_map_polyToFunctionField_yGen_over_baseGeneral W F F')
    ((injective_iff_map_eq_zero _).mpr fun p hp =>
      transcendental_iff.mp (kw_transcendental_polyToFunctionField_X_over_baseGeneral W F F') p
        hp)

public section publicSection

theorem kw_functionFieldMapAlongGeneral_polyToFunctionField_X :
    kw_functionFieldMapAlongGeneral W F F' (polyToFunctionField (W⁄F) X)
      = polyToFunctionField (W⁄F') X := by
  classical
  exact
    pointPullbackHomTo_polyToFunctionField_X _ _

theorem kw_functionFieldMapAlongGeneral_yGen :
    kw_functionFieldMapAlongGeneral W F F' (yGen (W⁄F)) = yGen (W⁄F') := by
  classical
  exact
    pointPullbackHomTo_yGen _ _

end publicSection

@[expose] public def KwFunctionFieldTensorIsDomainGeneral : Prop :=
  IsDomain ((W⁄F).FunctionField ⊗[F] F')

public scoped instance kw_isScalarTower_base_right_tensorGeneral :
    IsScalarTower R₀ F' ((W⁄F).FunctionField ⊗[F] F') := by
  refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => ?_)
  rw [RingHom.comp_apply, Algebra.TensorProduct.right_algebraMap_apply,
    IsScalarTower.algebraMap_apply R₀ F F',
    show algebraMap R₀ ((W⁄F).FunctionField ⊗[F] F') r
      = (algebraMap F ((W⁄F).FunctionField ⊗[F] F')) (algebraMap R₀ F r) from
        IsScalarTower.algebraMap_apply R₀ F ((W⁄F).FunctionField ⊗[F] F') r,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

section

variable [IsDomain ((W⁄F).FunctionField ⊗[F] F')]

public scoped instance kw_isScalarTower_base_right_fracTensorGeneral :
    IsScalarTower R₀ F' (FractionRing ((W⁄F).FunctionField ⊗[F] F')) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    (IsScalarTower.algebraMap_apply R₀ ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F')) r).trans <|
      (congrArg (algebraMap ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F')))
        (IsScalarTower.algebraMap_apply R₀ F' ((W⁄F).FunctionField ⊗[F] F') r)).trans
      (IsScalarTower.algebraMap_apply F' ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F')) (algebraMap R₀ F' r)).symm


end

public section publicSection

theorem kw_equation_tensorFracXYGeneral :
    ((W⁄F').map (algebraMap F' (FractionRing ((W⁄F).FunctionField ⊗[F] F')))).toAffine.Equation
      (algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')))
      (algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((yGen (W⁄F)) ⊗ₜ[F] (1 : F'))) := by
  classical
  have hcurve : (W⁄F').map (algebraMap F' (FractionRing ((W⁄F).FunctionField ⊗[F] F')))
      = W⁄(FractionRing ((W⁄F).FunctionField ⊗[F] F')) := by
    change (W.map _).map _ = W.map _
    rw [WeierstrassCurve.map_map]; congr 1
    exact (IsScalarTower.algebraMap_eq R₀ F'
      (FractionRing ((W⁄F).FunctionField ⊗[F] F'))).symm
  rw [hcurve]
  exact Equation.baseChange (W := W) (S := R₀)
    (f := (IsScalarTower.toAlgHom R₀ ((W⁄F).FunctionField ⊗[F] F')
            (FractionRing ((W⁄F).FunctionField ⊗[F] F'))).comp
          (Algebra.TensorProduct.includeLeft (R := F) (S := R₀)))
    (equation_map_polyToFunctionField_yGen (W := (W⁄F)))

omit [Algebra R₀ F'] [IsScalarTower R₀ F F'] in
theorem kw_transcendental_tensorFracXGeneral :
    Function.Injective (Polynomial.aeval (R := F')
      (algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')))) := by
  classical
  rw [show algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F'))
      = IsScalarTower.toAlgHom F' ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
          ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')) from rfl,
    Polynomial.aeval_algHom]
  refine (IsFractionRing.injective ((W⁄F).FunctionField ⊗[F] F')
    (FractionRing ((W⁄F).FunctionField ⊗[F] F'))).comp ?_
  have heq : (Polynomial.aeval (R := F')
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')
          : (W⁄F).FunctionField ⊗[F] F')).toRingHom
      = ((Algebra.TensorProduct.map
            (Polynomial.aeval (R := F) (polyToFunctionField (W⁄F) X))
            (AlgHom.id F F')).toRingHom.comp
          (Algebra.TensorProduct.comm F F' F[X]).toAlgHom.toRingHom).comp
          (polyEquivTensor' F F').toAlgHom.toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · change aeval _ (C c) = Algebra.TensorProduct.map _ _
          (Algebra.TensorProduct.comm F F' F[X] (polyEquivTensor' F F' (C c)))
      rw [show (polyEquivTensor' F F') (C c) = c ⊗ₜ[F] (1 : F[X]) from by
            rw [coe_polyEquivTensor', polyEquivTensor_apply, eval₂_C]; rfl,
        Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, Polynomial.aeval_C,
        Algebra.TensorProduct.right_algebraMap_apply, AlgHom.coe_id, id_eq, map_one]
    · change aeval _ (X : F'[X]) = Algebra.TensorProduct.map _ _
          (Algebra.TensorProduct.comm F F' F[X] (polyEquivTensor' F F' X))
      rw [show (polyEquivTensor' F F') X = (1:F') ⊗ₜ[F] (X : F[X]) from by
            rw [coe_polyEquivTensor', polyEquivTensor_apply, eval₂_X],
        Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, Polynomial.aeval_X,
        AlgHom.coe_id, id_eq, Polynomial.aeval_X]
  have hinj : Function.Injective
      (((Algebra.TensorProduct.map
          (Polynomial.aeval (R := F) (polyToFunctionField (W⁄F) X))
          (AlgHom.id F F')).toRingHom.comp
        (Algebra.TensorProduct.comm F F' F[X]).toAlgHom.toRingHom).comp
        (polyEquivTensor' F F').toAlgHom.toRingHom) :=
    ((Module.Flat.rTensor_preserves_injective_linearMap (M := F')
        (Polynomial.aeval (R := F) (polyToFunctionField (W⁄F) X)).toLinearMap
        ((injective_iff_map_eq_zero _).mpr fun p hp =>
          transcendental_iff.mp (transcendental_polyToFunctionField_X (W := (W⁄F))) p hp)).comp
      (Algebra.TensorProduct.comm F F' F[X]).injective).comp (polyEquivTensor' F F').injective
  intro p q hpq
  refine hinj ?_
  have := DFunLike.congr_fun heq
  exact (this p).symm.trans (hpq.trans (this q))

end publicSection

section

variable [IsDomain ((W⁄F).FunctionField ⊗[F] F')]

@[expose] public def kw_functionFieldTensorFracHomGeneral :
    (W⁄F').FunctionField →ₐ[F'] FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  pointPullbackHomTo (kw_equation_tensorFracXYGeneral W F F')
    (kw_transcendental_tensorFracXGeneral W F F')

public section publicSection

theorem kw_functionFieldTensorFracHomGeneral_X :
    kw_functionFieldTensorFracHomGeneral W F F' (polyToFunctionField (W⁄F') X)
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') _
          ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')) := by
  classical
  exact
    pointPullbackHomTo_polyToFunctionField_X _ _

theorem kw_functionFieldTensorFracHomGeneral_yGen :
    kw_functionFieldTensorFracHomGeneral W F F' (yGen (W⁄F'))
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') _ ((yGen (W⁄F)) ⊗ₜ[F] (1 : F')) := by
  classical
  exact
    pointPullbackHomTo_yGen _ _

theorem kw_functionFieldTensorFracHomGeneral_bijective :
    Function.Bijective (kw_functionFieldTensorFracHomGeneral W F F') := by
  classical
  refine ⟨(kw_functionFieldTensorFracHomGeneral W F F').injective, ?_⟩
  set ψ := kw_functionFieldTensorFracHomGeneral W F F'
  have hκ : (ψ.restrictScalars F).comp (kw_functionFieldMapAlongGeneral W F F')
      = (IsScalarTower.toAlgHom F ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F'))).comp
          (Algebra.TensorProduct.includeLeft (R := F)) := by
    refine kw_functionField_algHom_ext ?_ ?_
    · change ψ (kw_functionFieldMapAlongGeneral W F F' (polyToFunctionField (W⁄F) X)) = _
      rw [kw_functionFieldMapAlongGeneral_polyToFunctionField_X,
        kw_functionFieldTensorFracHomGeneral_X]
      rfl
    · change ψ (kw_functionFieldMapAlongGeneral W F F' (yGen (W⁄F))) = _
      rw [kw_functionFieldMapAlongGeneral_yGen, kw_functionFieldTensorFracHomGeneral_yGen]
      rfl
  have hT_sub : ∀ t : (W⁄F).FunctionField ⊗[F] F',
      algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing _) t ∈ ψ.toRingHom.fieldRange := by
    intro t
    induction t with
    | add _ _ hx hy => simp only [map_add]; exact add_mem hx hy
    | tmul a c =>
      rw [show (a ⊗ₜ[F] c : (W⁄F).FunctionField ⊗[F] F') = (a ⊗ₜ[F] 1) * (1 ⊗ₜ[F] c) from
            by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
        map_mul]
      refine mul_mem ?_ ⟨algebraMap F' _ c, ?_⟩
      · exact ⟨kw_functionFieldMapAlongGeneral W F F' a, DFunLike.congr_fun hκ a⟩
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ψ.commutes,
          IsScalarTower.algebraMap_apply F' ((W⁄F).FunctionField ⊗[F] F')
            (FractionRing ((W⁄F).FunctionField ⊗[F] F')),
          Algebra.TensorProduct.right_algebraMap_apply]
  intro z
  obtain ⟨t, s, _, rfl⟩ := IsFractionRing.div_surjective
    (A := (W⁄F).FunctionField ⊗[F] F') (K := FractionRing _) z
  exact div_mem (hT_sub t) (hT_sub s)

end publicSection

@[expose] public def kw_functionFieldTensorFracEquivGeneral :
    (W⁄F').FunctionField ≃ₐ[F'] FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  AlgEquiv.ofBijective _ (kw_functionFieldTensorFracHomGeneral_bijective W F F')

end

local notation3 "CR" => (W⁄F).toAffine.CoordinateRing
local notation3 "FFₗ" => (W⁄F).FunctionField

public section publicSection

omit [Algebra R₀ F'] [IsScalarTower R₀ F F'] in
theorem kw_coordinateRingMap_basisGeneral (i : ℕ × Fin 2) :
    CoordinateRing.map (W⁄F).toAffine (algebraMap F F')
        (kw_coordinateRingBasis (W⁄F).toAffine i)
      = kw_coordinateRingBasis ((W⁄F).toAffine.map (algebraMap F F')) i := by
  classical
  obtain ⟨n, j⟩ := i
  simp only [kw_coordinateRingBasis, Module.Basis.smulTower_apply,
    Polynomial.coe_basisMonomials, CoordinateRing.map_smul]
  congr 1
  · simp [Polynomial.map_monomial]
  · rcases j with ⟨j, hj⟩
    interval_cases j <;>
      simp [CoordinateRing.basis_apply, CoordinateRing.map,
        AdjoinRoot.lift_root, AdjoinRoot.powerBasis'_gen]

end publicSection

@[expose] public def kw_coordinateRingMapAlongGeneral :
    CR →ₐ[F] ((W⁄F).toAffine.map (algebraMap F F')).CoordinateRing where
  __ := CoordinateRing.map (W⁄F).toAffine (algebraMap F F')
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_ofClass]
    change CoordinateRing.map (W⁄F).toAffine (algebraMap F F') (algebraMap F CR r) = algebraMap F _
      r
    rw [IsScalarTower.algebraMap_apply F F[X] CR,
      show (algebraMap F F[X] r) = Polynomial.C r from rfl,
      show (algebraMap F[X] CR) (C r) = (C r : F[X]) • (1 : CR) by
        rw [Algebra.smul_def, mul_one],
      CoordinateRing.map_smul, map_one, Polynomial.map_C,
      IsScalarTower.algebraMap_apply F F' ((W⁄F).toAffine.map (algebraMap F F')).CoordinateRing,
      IsScalarTower.algebraMap_apply F' F'[X]
        ((W⁄F).toAffine.map (algebraMap F F')).CoordinateRing,
      show (algebraMap F' F'[X]) ((algebraMap F F') r) = Polynomial.C ((algebraMap F F') r)
        from rfl,
      Algebra.smul_def, mul_one]

public section publicSection

omit [Algebra R₀ F'] [IsScalarTower R₀ F F'] in
theorem kw_coordinateRingTensor_isDomainGeneral : IsDomain (CR ⊗[F] F') := by
  classical
  suffices h : IsDomain (F' ⊗[F] CR) by
    have := h
    exact Function.Injective.isDomain (Algebra.TensorProduct.comm F CR F').toRingHom
      (Algebra.TensorProduct.comm F CR F').injective
  set W'' := (W⁄F).toAffine.map (algebraMap F F') with hW''
  let θ : F' ⊗[F] CR →ₐ[F'] W''.CoordinateRing :=
    AlgHom.liftEquiv F F' CR W''.CoordinateRing (kw_coordinateRingMapAlongGeneral W F F')
  have hθ : Function.Injective θ := by
    let bT : Module.Basis (ℕ × Fin 2) F' (F' ⊗[F] CR) :=
      Algebra.TensorProduct.basis F' (kw_coordinateRingBasis (W⁄F).toAffine)
    let bD : Module.Basis (ℕ × Fin 2) F' W''.CoordinateRing := kw_coordinateRingBasis W''
    have key : ∀ i, θ.toLinearMap (bT i) = (bT.equiv bD (Equiv.refl _)) (bT i) := fun i => by
      rw [Module.Basis.equiv_apply, Equiv.refl_apply, AlgHom.toLinearMap_apply]
      simp only [bT, Algebra.TensorProduct.basis_apply, θ, AlgHom.liftEquiv_tmul, one_smul]
      exact kw_coordinateRingMap_basisGeneral W F F' i
    have heq : (θ : F' ⊗[F] CR → W''.CoordinateRing) = bT.equiv bD (Equiv.refl _) :=
      funext fun x => DFunLike.congr_fun (bT.ext key : θ.toLinearMap = _) x
    exact heq ▸ (bT.equiv bD (Equiv.refl _)).injective
  exact Function.Injective.isDomain θ.toRingHom hθ

omit [Algebra R₀ F'] [IsScalarTower R₀ F F'] in
theorem kw_functionFieldTensorIsDomain_dischargeGeneral :
    KwFunctionFieldTensorIsDomainGeneral W F F' := by
  classical
  change IsDomain (FFₗ ⊗[F] F')
  have hCR : IsDomain (CR ⊗[F] F') := kw_coordinateRingTensor_isDomainGeneral W F F'
  let : Algebra (CR ⊗[F] F') (FFₗ ⊗[F] F') :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F CR FFₗ)
      (AlgHom.id F F')).toRingHom.toAlgebra
  have hst : IsScalarTower CR (CR ⊗[F] F') (FFₗ ⊗[F] F') :=
    IsScalarTower.of_algebraMap_eq (R := CR) (S := CR ⊗[F] F') (A := FFₗ ⊗[F] F') fun c => by
      change Algebra.TensorProduct.map (IsScalarTower.toAlgHom F CR FFₗ) (AlgHom.id F F')
          (algebraMap CR (CR ⊗[F] F') c) = algebraMap CR (FFₗ ⊗[F] F') c
      rfl
  have hloc : IsLocalization
      (Algebra.algebraMapSubmonoid (CR ⊗[F] F') (nonZeroDivisors CR)) (FFₗ ⊗[F] F') :=
    IsLocalization.tensorProduct_tensorProduct F F' (nonZeroDivisors CR) FFₗ (by
      ext x; simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.map_tmul])
  have hle : Algebra.algebraMapSubmonoid (CR ⊗[F] F') (nonZeroDivisors CR)
      ≤ nonZeroDivisors (CR ⊗[F] F') := by
    rintro _ ⟨c, hc, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    have hinj : Function.Injective (algebraMap CR (CR ⊗[F] F')) :=
      Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F F').injective
    exact fun h => (nonZeroDivisors.ne_zero hc) (hinj (by
      simp only [_root_.map_zero] at h ⊢; exact h))
  exact IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Algebra.algebraMapSubmonoid (CR ⊗[F] F') (nonZeroDivisors CR)) _ hle

end publicSection

end ScalarExtension

public section publicSection

theorem fractionRing_span_and_independent
    {T : Type u} {T' : Type v} [CommRing T] [IsDomain T] [CommRing T'] [IsDomain T']
    {ι : Type*} [Fintype ι]
    (ιT : T' →+* T) (ιFr : FractionRing T' →+* FractionRing T)
    (hιT_inj : Function.Injective ιT) (hιT_fin : ιT.Finite)
    (hιFr_am : ∀ t, ιFr (algebraMap T' (FractionRing T') t) =
      algebraMap T (FractionRing T) (ιT t))
    (e : ι → T)
    (hspanT : ∀ t, ∃ c : ι → T', t = ∑ i, ιT (c i) * e i)
    (hliT : ∀ c : ι → T', ∑ i, ιT (c i) * e i = 0 → ∀ j, c j = 0) :
    (∀ z : FractionRing T, ∃ d : ι → FractionRing T',
      z = ∑ i, ιFr (d i) * algebraMap T (FractionRing T) (e i)) ∧
    (∀ d : ι → FractionRing T',
      ∑ i, ιFr (d i) * algebraMap T (FractionRing T) (e i) = 0 → ∀ j, d j = 0) := by
  classical
  let FrT := FractionRing T
  let FrT' := FractionRing T'
  let bFr : ι → FrT := fun i => algebraMap T FrT (e i)
  have hint : ∀ s : T, s ≠ 0 → ∃ (u : T) (s₀ : T'), s₀ ≠ 0 ∧ s * u = ιT s₀ := by
    intro s hs
    obtain ⟨p, hp_monic, hp_eval⟩ : ιT.IsIntegralElem s := hιT_fin.to_isIntegral s
    obtain ⟨q, hq_eq, hq_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p
      hp_monic.ne_zero 0
    simp only [Polynomial.C_0, sub_zero] at hq_eq hq_ndvd
    have hq0 : q.coeff 0 ≠ 0 := fun h => hq_ndvd (Polynomial.X_dvd_iff.mpr h)
    have hqs : q.eval₂ ιT s = 0 := by
      have h := hp_eval
      rw [hq_eq, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        mul_eq_zero] at h
      exact h.resolve_left (pow_ne_zero _ hs)
    have h3 : ιT (q.coeff 0) + s * (q.divX).eval₂ ιT s = 0 := by
      have h := congrArg (Polynomial.eval₂ ιT s) (Polynomial.divX_mul_X_add q)
      rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
        Polynomial.eval₂_C, hqs] at h
      simpa only [add_comm, mul_comm] using h
    exact ⟨(q.divX).eval₂ ιT s, -q.coeff 0, neg_ne_zero.mpr hq0,
      by rw [map_neg]; exact eq_neg_of_add_eq_zero_right h3⟩
  have hspanFr : ∀ z : FrT, ∃ d : ι → FrT', z = ∑ i, ιFr (d i) * bFr i := by
    intro z
    obtain ⟨t, s, _, rfl⟩ := IsFractionRing.div_surjective (A := T) (K := FrT) z
    rcases eq_or_ne s 0 with rfl | hs'
    · exact ⟨0, by simp⟩
    obtain ⟨u, s₀, hs₀, hsu⟩ := hint s hs'
    have hιTs₀ : ιT s₀ ≠ 0 := fun h => hs₀ (hιT_inj (h.trans (map_zero ιT).symm))
    have hu_ne : u ≠ 0 := fun h => hιTs₀ (by rw [← hsu, h, mul_zero])
    obtain ⟨c, hc⟩ := hspanT (t * u)
    refine ⟨fun i => (algebraMap T' FrT' s₀)⁻¹ * algebraMap T' FrT' (c i), ?_⟩
    have hum := (map_ne_zero_iff _ (IsFractionRing.injective T FrT)).mpr hu_ne
    have hz : (algebraMap T FrT t) / (algebraMap T FrT s)
        = (algebraMap T FrT (ιT s₀))⁻¹ * algebraMap T FrT (t * u) := by
      rw [← div_eq_inv_mul, ← hsu, map_mul, map_mul,
        ← div_mul_div_comm, div_self hum, mul_one]
    rw [hz, hc, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, ← hιFr_am s₀, ← hιFr_am (c i), ← map_inv₀ ιFr, mul_assoc]
  have hliFr : ∀ d : ι → FrT', ∑ i, ιFr (d i) * bFr i = 0 → ∀ j, d j = 0 := by
    intro d hd j
    obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors T') (Finset.univ.image d)
    choose p hp using fun i => hq (d i) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    have hq0 : (algebraMap T' FrT' (q : T')) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective T' FrT')).mpr (nonZeroDivisors.ne_zero q.2)
    have hp' : ∀ i, algebraMap T' FrT' (p i) = algebraMap T' FrT' (q : T') * d i := fun i => by
      rw [hp i, Algebra.smul_def]
    have hd' : algebraMap T FrT (∑ i, ιT (p i) * e i) = 0 := by
      have h1 : ∑ i, ιFr (algebraMap T' FrT' (q : T')) * (ιFr (d i) * bFr i) = 0 := by
        rw [← Finset.mul_sum, hd, mul_zero]
      rw [map_sum, ← h1]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← hιFr_am (p i), ← mul_assoc, ← map_mul, ← hp' i]
    have hpj : p j = 0 :=
      hliT p ((IsFractionRing.injective T FrT) (by simpa using hd')) j
    have hthis : algebraMap T' FrT' (q : T') * d j = 0 := by
      rw [← hp' j, hpj, map_zero]
    exact (mul_eq_zero.mp hthis).resolve_left hq0
  exact ⟨hspanFr, hliFr⟩

end publicSection

end ModularCurve

end
end FunctionFieldBaseChange

end privateSection
