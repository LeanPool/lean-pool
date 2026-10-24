/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Based on Prove2Me node
WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom
(f4d949d7-d2e9-583c-970a-d2c81be54545) by Claude (2026-09-05).

Proof based on Prove2Me submission dc1eabf7-1867-53e3-b324-7414996a1c99
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_Isogeny_ConditionalCurrency
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

import Mathlib.Algebra.Algebra.Field
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Order.CompletePartialOrder
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import LeanPool.FLTEichlerShimura.Theorems.Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_inv
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_normFormulaAlong
import LeanPool.FLTEichlerShimura.Theorems.Thm_PeriodPair_isUniformization_toPoint
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
import LeanPool.FLTEichlerShimura.Definitions.Def_EllipticCurve_FunctionFieldPullback
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum
import LeanPool.FLTEichlerShimura.Theorems.Thm_PeriodPair_discriminant_ne_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add_v2

/-!
# Cyclic kernel of order N descends along base change

Theorem statement:
`WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom`
(`f4d949d7-d2e9-583c-970a-d2c81be54545`), by Claude, 2026-09-05.

Proof: submission `dc1eabf7-1867-53e3-b324-7414996a1c99`, by Claude, 2026-09-05 (ACCEPTED); locally
adapted.

Let $R_0$ be a field, let $E_0,E_0'$ be elliptic Weierstrass curves over $R_0$, and let
$F_1\subseteq F_2$ be algebraically closed $R_0$-algebras of characteristic $0$ forming a scalar
tower over $R_0$ (all in one universe), such that the four base changes $E_0\otimes F_i$,
$E_0'\otimes F_i$ are elliptic and each of their affine models carries: a `GenusOnePlaceGate`, i.e.
a bijection between its group of points and the places of its function field over the base field,
all of degree $1$; the centredness condition that at the place attached to a point $(x,y)$ the
classes of $X-x$ and $Y-y$ are nonunits of the valuation subring; and `AbelTheorem`, i.e. a
degree-zero divisor is principal exactly when its divisor sum vanishes. Let $\chi$, resp. $\chi'$,
be $F_1$-algebra maps from the function field of $E_0\otimes F_1$, resp. $E_0'\otimes F_1$, to that
of $E_0\otimes F_2$, resp. $E_0'\otimes F_2$, carrying the coordinate function $x$ to $x$ and $y$ to
$y$. Let $\iota_1$ be an $F_1$-algebra map from the function field of $E_0'\otimes F_1$ to that of
$E_0\otimes F_1$ whose underlying ring map is integral, which makes the target a finite module over
the source, and which satisfies the pushforward norm formula (for nonzero $f$ and a divisor $D$ with
$D(w)=\mathrm{ord}_w f$ for all places $w$ upstairs, the pushforward of $D$ has value
$\mathrm{ord}_v(\mathrm{N}f)$ at each place $v$ downstairs); let $\iota_2$ be the analogous datum
over $F_2$, compatible with base change in the sense that $\iota_2(\chi'(x))=\chi(\iota_1(x))$ for
all $x$. Let $N$ be a nonzero natural number. If the kernel of the map $(E_0\otimes
F_2)(F_2)\to(E_0'\otimes F_2)(F_2)$ induced by divisor pushforward along $\iota_2$ is additively
cyclic of cardinality $N$, then the kernel of the corresponding map $(E_0\otimes
F_1)(F_1)\to(E_0'\otimes F_1)(F_1)$ induced by pushforward along $\iota_1$ is additively cyclic of
cardinality $N$ as well.

The statement transports the cyclicity and the order of the kernel of an isogeny, realised here as
the map on points coming from divisor pushforward along an inclusion of function fields, downwards
along an extension of algebraically closed fields of characteristic $0$ over a common base. It is
used by
[`WeierstrassCurve.Affine.
exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`]
(thm.html#WeierstrassCurve.Affine.
exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward),
which descends such a configuration to a countable intermediate field.

## Explanation of the source proof

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom.lean

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

noncomputable section

section

namespace WeierstrassCurve
namespace Affine

open Polynomial IsDedekindDomain WeierstrassCurve.Affine.CoordinateRing AlgebraicCurve
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] {W : Affine F}

namespace CoordinateRing

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

def heightOneSpectrumOfEquation {x y : F} (h : W.Equation x y) :
    HeightOneSpectrum W.CoordinateRing where
  asIdeal := XYIdeal W x (C y)
  isPrime := (XYIdeal_isMaximal h).isPrime
  ne_bot := XYIdeal_ne_bot x (C y)

@[scoped simp]
theorem heightOneSpectrumOfEquation_asIdeal {x y : F} (h : W.Equation x y) :
    (heightOneSpectrumOfEquation h).asIdeal = XYIdeal W x (C y) := rfl

theorem exists_sub_algebraMap_mem {x y : F} (h : W.Equation x y) (r : W.CoordinateRing) :
    ∃ c : F, r - algebraMap F W.CoordinateRing c ∈ XYIdeal W x (C y) := by
  set e := quotientXYIdealEquiv (W' := W) (x := x) (y := C y) h
  refine ⟨e (Ideal.Quotient.mk _ r), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  apply e.injective
  rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes,
    Algebra.algebraMap_self_apply]

end CoordinateRing

def IsFinitePlace (v : AlgebraicCurve.Place F W.FunctionField) : Prop :=
  ∀ r : W.CoordinateRing, algebraMap W.CoordinateRing W.FunctionField r ∈ v.toValuationSubring

def IsFinitePlace.ringHom {v : AlgebraicCurve.Place F W.FunctionField} (hv : IsFinitePlace v) :
    W.CoordinateRing →+* v.toValuationSubring where
  toFun r := ⟨algebraMap W.CoordinateRing W.FunctionField r, hv r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

@[scoped simp]
theorem IsFinitePlace.coe_ringHom_apply {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) (r : W.CoordinateRing) :
    (hv.ringHom r : W.FunctionField) = algebraMap W.CoordinateRing W.FunctionField r := rfl

def IsFinitePlace.centre {v : AlgebraicCurve.Place F W.FunctionField} (hv : IsFinitePlace v) :
    Ideal W.CoordinateRing :=
  (IsLocalRing.maximalIdeal v.toValuationSubring).comap hv.ringHom

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
    have := congrArg (fun a : v.toValuationSubring => (a : W.FunctionField)) ht
    simpa using this
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

variable [IsDedekindDomain W.CoordinateRing]

def placeOfEquation {x y : F} (h : W.Equation x y) :
    AlgebraicCurve.Place F W.FunctionField :=
  AlgebraicCurve.Place.ofHeightOneSpectrum (heightOneSpectrumOfEquation h)

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

scoped instance S13_instIsDedekindDomainCoordinateRing [IsAlgClosed F] [W.IsElliptic] :
    IsDedekindDomain W.CoordinateRing :=
  CoordinateRing.isDedekindDomain (W := W)

section CentredGate

variable [DecidableEq F] [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]

omit [DecidableEq F] in
@[scoped simp]
theorem placeOfPoint_some {x y : F} (h : W.Nonsingular x y) :
    placeOfPoint (.some x y h) = placeOfEquation h.left := by
  classical
  exact
    placeOfPoint_some_eq_ofHeightOneSpectrum h (heightOneSpectrumOfEquation h.left) rfl

namespace InfinitePlace

def place : AlgebraicCurve.Place F W.FunctionField := placeOfPoint (0 : W.Point)


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

end InfinitePlace

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

end CentredGate
end Affine
end WeierstrassCurve
end

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

section
open AlgebraicCurve WeierstrassCurve

namespace WeierstrassCurve
namespace Affine

section AutoNorm
variable {F : Type*} [Field F] [CharZero F]
variable {V W : Affine F} [V.IsElliptic] [W.IsElliptic]

omit [WeierstrassCurve.IsElliptic V] [WeierstrassCurve.IsElliptic W] in
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

end AutoNorm

end Affine
end WeierstrassCurve
end


namespace AlgebraicCurve
namespace Place


theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

end Place
end AlgebraicCurve

namespace WeierstrassCurve
namespace Affine
open WeierstrassCurve.Affine.CoordinateRing AlgebraicCurve Polynomial
open scoped Polynomial.Bivariate

section FinitePlaceOfMem
variable {F : Type*} [Field F] {W : Affine F}
variable (v : AlgebraicCurve.Place F W.FunctionField)

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

end FinitePlaceOfMem

end Affine
end WeierstrassCurve

namespace ModularCurve
open AlgebraicCurve in
open _root_.WeierstrassCurve
  _root_.WeierstrassCurve.Affine in
theorem kw_fdn2_qephod_hend7_pmopKerCard_proved
    (K : Type*) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [E'.IsElliptic] [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) :
    Nat.card ((pointMapOfPushforward ι hι hfin
      (normFormulaAlong_of_elliptic ι hfin)).ker) = finrankAlong K ι :=
  natCard_ker_pointMapOfPushforward_eq_finrankAlong E E' ι hι hfin _
end ModularCurve


section

section

section
open Polynomial  IsDedekindDomain
open scoped Polynomial.Bivariate
namespace AlgebraicCurve
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
open scoped AlgebraicCurve.Place in
theorem Place.ramificationIndexAlong_pos (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') : 0 < Place.ramificationIndexAlong φ w := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  exact w.ramificationIndex_pos

open scoped AlgebraicCurve.Place in
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

end AlgebraicCurve

namespace WeierstrassCurve
namespace Affine

open WeierstrassCurve.Affine.CoordinateRing  AlgebraicCurve

variable {F : Type*} [Field F] {W : Affine F}

theorem algebraMap_polynomial_eq_mk_C (p : F[X]) :
    algebraMap F[X] W.CoordinateRing p = CoordinateRing.mk W (C p) :=
  rfl

theorem algebraMap_coordinateRing_ne_zero {r : W.CoordinateRing} (hr : r ≠ 0) :
    algebraMap W.CoordinateRing W.FunctionField r ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr hr

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

end Affine
end WeierstrassCurve

namespace WeierstrassCurve
namespace Affine
open WeierstrassCurve.Affine.CoordinateRing  AlgebraicCurve

variable {F : Type*} [Field F] (W : Affine F)

variable {W}

def yGen (W : Affine F) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)

end Affine
end WeierstrassCurve
end
section
open Polynomial  IsDedekindDomain
open scoped Polynomial.Bivariate
namespace WeierstrassCurve
namespace Affine
open WeierstrassCurve.Affine.CoordinateRing  AlgebraicCurve
universe u
variable {F : Type u} [Field F]
section GenericPoint
variable {W : Affine F}

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

end GenericPoint
end Affine
end WeierstrassCurve
end


section

open Polynomial  IsDedekindDomain

open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine

open WeierstrassCurve.Affine.CoordinateRing  AlgebraicCurve

universe u

variable {F : Type u} [Field F]

namespace AbstractSeam

variable {W : Affine F} {V : Affine F}
variable (ι : V.FunctionField →ₐ[F] W.FunctionField)
  (hι : ι.toRingHom.IsIntegral)
  {ξ η : W.FunctionField}
  (hX : ι (polyToFunctionField V (X : F[X])) = ξ)
  (hY : ι (yGen V) = η)

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

section Cases

variable [IsDedekindDomain V.CoordinateRing]

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
theorem restrictAlong_eq_infinitePlace [V.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred V]
    (v : AlgebraicCurve.Place F W.FunctionField)
    (hpole : ξ ∉ v.toValuationSubring) :
    v.restrictAlong ι hι = InfinitePlace.place := by
  refine InfinitePlace.eq_of_not_isFinitePlace _ ?_
  intro hfin
  refine hpole ?_
  rw [← hX]
  exact hfin (algebraMap F[X] V.CoordinateRing (X : F[X]))

end Cases
end AbstractSeam
end Affine
end WeierstrassCurve

end

section
open Polynomial  WeierstrassCurve.Affine  WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine  Polynomial.Bivariate
section
namespace WeierstrassCurve
namespace Affine
open WeierstrassCurve.Affine.CoordinateRing  AlgebraicCurve
universe u
variable {F : Type u} [Field F]
section AdjoinSurjective
variable {W : Affine F} (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

theorem transcendental_polyToFunctionField_X :
    Transcendental F (polyToFunctionField W X) := by
  rw [transcendental_iff]
  intro p hp
  rw [← polyToFunctionField_eq_aeval] at hp
  exact polyToFunctionField_injective (by simpa using hp)

end AdjoinSurjective
end Affine
end WeierstrassCurve
end
end

section


section

open Polynomial  WeierstrassCurve  WeierstrassCurve.Affine

open scoped Polynomial.Bivariate

universe u

end
end
end

section


section

namespace WeierstrassCurve
namespace Affine
open AlgebraicCurve
section Gate
universe u
variable {F : Type u} [Field F] [DecidableEq F]
variable {W : Affine F} [GenusOnePlaceGate W]
variable (W)

def placeOfPointEquiv : W.Point ≃ AlgebraicCurve.Place F W.FunctionField :=
  pointEquivPlace (W := W)
omit [DecidableEq F] in
theorem placeOfPoint_placeOfPointEquiv_symm (w : AlgebraicCurve.Place F W.FunctionField) :
    placeOfPoint ((placeOfPointEquiv W).symm w) = w := by
  classical
  exact
    (placeOfPointEquiv W).apply_symm_apply w

end Gate
end Affine
end WeierstrassCurve
namespace ModularCurve
open WeierstrassCurve  WeierstrassCurve.Affine  Polynomial  AlgebraicCurve
universe u
attribute [local instance] Classical.propDecidable
section GeomMorphBC
variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {E E' : Affine K} [E.IsElliptic] [GenusOnePlaceGate E] [AbelTheorem E]
  [E'.IsElliptic] [GenusOnePlaceGate E'] [AbelTheorem E']
variable (ι : E'.FunctionField →ₐ[K] E.FunctionField)
variable (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) (hN : NormFormulaAlong K ι hfin)

def kw_fdn2_qephod_hend7_geomMorphBC : E.Point → E'.Point :=
  fun P => (placeOfPointEquiv E').symm ((placeOfPoint P).restrictAlong ι hι)

local notation "gBC" => kw_fdn2_qephod_hend7_geomMorphBC ι hι

omit [DecidableEq K] [IsAlgClosed K] [CharZero K] [WeierstrassCurve.IsElliptic E] [E.AbelTheorem]
  [WeierstrassCurve.IsElliptic E'] [E'.AbelTheorem] in
theorem kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC (P : E.Point) :
    (placeOfPoint P).restrictAlong ι hι = placeOfPoint (gBC P) :=
  (placeOfPoint_placeOfPointEquiv_symm E' _).symm

omit [DecidableEq K] [IsAlgClosed K] [CharZero K] [WeierstrassCurve.IsElliptic E] [E.AbelTheorem]
  [WeierstrassCurve.IsElliptic E'] [E'.AbelTheorem] in
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

include hfin in
omit [DecidableEq K] [IsAlgClosed K] [CharZero K] [WeierstrassCurve.IsElliptic E] [E.AbelTheorem]
  [WeierstrassCurve.IsElliptic E'] [E'.AbelTheorem] in
theorem kw_fdn2_qephod_hend7_pushforwardHom_pointClass_eq_sub (P : E.Point) :
    Pic0.pushforwardAlongHom ι hι hfin hN
        (pointClass P)
      = pointClass (gBC P) - pointClass (gBC 0) := by
  change Pic0.pushforwardAlongHom ι hι hfin _ (Pic0.mk (pointDivisor P))
      = Pic0.mk (pointDivisor (gBC P)) - Pic0.mk (pointDivisor (gBC 0))
  rw [Pic0.pushforwardAlongHom_mk,
    kw_fdn2_qephod_hend7_pushforwardDegZero_pointDivisor_geomMorphBC ι hι P]
  rfl

include hfin in
omit [IsAlgClosed K] [CharZero K] [WeierstrassCurve.IsElliptic E]
  [WeierstrassCurve.IsElliptic E'] in
theorem kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub (P : E.Point) :
    pointMapOfPushforward ι hι hfin hN P
      = gBC P - gBC 0 := by
  rw [pointMapOfPushforward_apply,
    kw_fdn2_qephod_hend7_pushforwardHom_pointClass_eq_sub ι hι hfin hN P, map_sub,
    genusOnePic0Equiv_apply, genusOnePic0Equiv_apply, pic0ToPoint_pointClass,
    pic0ToPoint_pointClass]
end GeomMorphBC
end ModularCurve
end
end

section



section

open WeierstrassCurve  Affine

namespace ModularCurve

universe u

section Setup

def kw_coordinateRingBasis {R : Type*} [CommRing R] (V : Affine R) :
    Module.Basis (ℕ × Fin 2) R V.CoordinateRing :=
  (Polynomial.basisMonomials R).smulTower (CoordinateRing.basis V)

end Setup

end ModularCurve
end

section



section

open WeierstrassCurve  WeierstrassCurve.Affine   AlgebraicCurve
open Polynomial
open scoped TensorProduct Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine

universe u
variable {F : Type u} [Field F] {W : Affine F}

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

end Affine
end WeierstrassCurve

end

section


section

open Polynomial  WeierstrassCurve  WeierstrassCurve.Affine

open scoped Polynomial.Bivariate

universe u

namespace WeierstrassCurve
namespace Affine

open WeierstrassCurve.Affine.CoordinateRing

variable {F : Type u} [Field F]

section PointPullbackTo

variable {W : Affine F} {L : Type u} [Field L] [Algebra F L]

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

def pointPullbackCoordHomTo {xP yP : L}
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

def pointPullbackHomTo {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    W.FunctionField →ₐ[F] L :=
  IsFractionRing.liftAlgHom (pointPullbackCoordHomTo_injective h hx)

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

end PointPullbackTo
end Affine
end WeierstrassCurve
end
end

section



section

open WeierstrassCurve  WeierstrassCurve.Affine   AlgebraicCurve
open Polynomial
open scoped TensorProduct Polynomial.Bivariate Polynomial

namespace ModularCurve

universe u

section SetupBCG

variable {R₀ : Type u} [Field R₀]
variable (W : WeierstrassCurve R₀) [W.IsElliptic]
variable (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [CharZero F]
variable (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']

variable [WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (W⁄F).toAffine]
variable [WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F').toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F').toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (W⁄F').toAffine]

omit [W.IsElliptic] [Algebra R₀ F] [DecidableEq F] [CharZero F] [DecidableEq F'] [CharZero F']
  [IsScalarTower R₀ F F'] [(toAffine W⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F)] [(toAffine W⁄F).AbelTheorem]
  [(toAffine W⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F')]
  [(toAffine W⁄F').AbelTheorem] in
theorem kw_transcendental_polyToFunctionField_X_over_baseGeneralNoAC :
    Transcendental F (polyToFunctionField (W⁄F') X) :=
  Transcendental.of_tower_top F (L := F')
    (transcendental_polyToFunctionField_X (W := (W⁄F')))

omit [W.IsElliptic] [DecidableEq F] [CharZero F] [DecidableEq F'] [CharZero F']
  [(toAffine W⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F)]
  [(toAffine W⁄F).AbelTheorem] [(toAffine W⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F')] [(toAffine W⁄F').AbelTheorem] in
theorem kw_equation_map_polyToFunctionField_yGen_over_baseGeneralNoAC :
    ((W⁄F).map (algebraMap F (W⁄F').FunctionField)).toAffine.Equation
      (polyToFunctionField (W⁄F') X) (yGen (W⁄F')) := by
  have hcurve : (W⁄F).map (algebraMap F (W⁄F').FunctionField)
      = (W⁄F').map (algebraMap F' (W⁄F').FunctionField) := by
    change (W.map _).map _ = (W.map _).map _
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
    congr 1
    exact ((IsScalarTower.algebraMap_eq R₀ F (W⁄F').FunctionField).symm).trans
      (IsScalarTower.algebraMap_eq R₀ F' (W⁄F').FunctionField)
  exact hcurve ▸ equation_map_polyToFunctionField_yGen (W := (W⁄F'))

def kw_functionFieldMapAlongGeneralNoAC : (W⁄F).FunctionField →ₐ[F] (W⁄F').FunctionField :=
  pointPullbackHomTo (kw_equation_map_polyToFunctionField_yGen_over_baseGeneralNoAC W F F')
    ((injective_iff_map_eq_zero _).mpr fun p hp =>
      transcendental_iff.mp (kw_transcendental_polyToFunctionField_X_over_baseGeneralNoAC W F F') p
        hp)

omit [W.IsElliptic] [DecidableEq F] [CharZero F] [DecidableEq F'] [CharZero F']
  [(toAffine W⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F)]
  [(toAffine W⁄F).AbelTheorem] [(toAffine W⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F')] [(toAffine W⁄F').AbelTheorem] in
theorem kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X :
    kw_functionFieldMapAlongGeneralNoAC W F F' (polyToFunctionField (W⁄F) X)
      = polyToFunctionField (W⁄F') X :=
  pointPullbackHomTo_polyToFunctionField_X _ _

omit [W.IsElliptic] [DecidableEq F] [CharZero F] [DecidableEq F'] [CharZero F']
  [(toAffine W⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F)]
  [(toAffine W⁄F).AbelTheorem] [(toAffine W⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F')] [(toAffine W⁄F').AbelTheorem] in
theorem kw_functionFieldMapAlongGeneralNoAC_yGen :
    kw_functionFieldMapAlongGeneralNoAC W F F' (yGen (W⁄F)) = yGen (W⁄F') :=
  pointPullbackHomTo_yGen _ _

end SetupBCG

end ModularCurve
end
end

section



section

open WeierstrassCurve  WeierstrassCurve.Affine   AlgebraicCurve
open Polynomial
open scoped TensorProduct Polynomial.Bivariate

namespace ModularCurve

universe u

section Setup

variable {R₀ : Type u} [Field R₀]
variable (W : WeierstrassCurve R₀) [W.IsElliptic]
variable (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']

variable [WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (W⁄F).toAffine]
variable [WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F').toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F').toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (W⁄F').toAffine]

omit [W.IsElliptic] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F] [DecidableEq F']
  [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F'] [(toAffine W⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F)] [(toAffine W⁄F).AbelTheorem]
  [(toAffine W⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F')]
  [(toAffine W⁄F').AbelTheorem] in
theorem kw_transcendental_polyToFunctionField_X_over_baseGeneral :
    Transcendental F (polyToFunctionField (W⁄F') X) :=
  Transcendental.of_tower_top F (L := F')
    (transcendental_polyToFunctionField_X (W := (W⁄F')))

omit [W.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F] [DecidableEq F']
  [IsAlgClosed F'] [CharZero F'] [(toAffine W⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F)] [(toAffine W⁄F).AbelTheorem]
  [(toAffine W⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F')]
  [(toAffine W⁄F').AbelTheorem] in
theorem kw_equation_map_polyToFunctionField_yGen_over_baseGeneral :
    ((W⁄F).map (algebraMap F (W⁄F').FunctionField)).toAffine.Equation
      (polyToFunctionField (W⁄F') X) (yGen (W⁄F')) := by
  have hcurve : (W⁄F).map (algebraMap F (W⁄F').FunctionField)
      = (W⁄F').map (algebraMap F' (W⁄F').FunctionField) := by
    change (W.map _).map _ = (W.map _).map _
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
    congr 1
    exact ((IsScalarTower.algebraMap_eq R₀ F (W⁄F').FunctionField).symm).trans
      (IsScalarTower.algebraMap_eq R₀ F' (W⁄F').FunctionField)
  exact hcurve ▸ equation_map_polyToFunctionField_yGen (W := (W⁄F'))

def kw_functionFieldMapAlongGeneral : (W⁄F).FunctionField →ₐ[F] (W⁄F').FunctionField :=
  pointPullbackHomTo (kw_equation_map_polyToFunctionField_yGen_over_baseGeneral W F F')
    ((injective_iff_map_eq_zero _).mpr fun p hp =>
      transcendental_iff.mp (kw_transcendental_polyToFunctionField_X_over_baseGeneral W F F') p
        hp)

omit [W.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F] [DecidableEq F']
  [IsAlgClosed F'] [CharZero F'] [(toAffine W⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F)] [(toAffine W⁄F).AbelTheorem]
  [(toAffine W⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F')]
  [(toAffine W⁄F').AbelTheorem] in
theorem kw_functionFieldMapAlongGeneral_polyToFunctionField_X :
    kw_functionFieldMapAlongGeneral W F F' (polyToFunctionField (W⁄F) X)
      = polyToFunctionField (W⁄F') X :=
  pointPullbackHomTo_polyToFunctionField_X _ _

omit [W.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F] [DecidableEq F']
  [IsAlgClosed F'] [CharZero F'] [(toAffine W⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F)] [(toAffine W⁄F).AbelTheorem]
  [(toAffine W⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F')]
  [(toAffine W⁄F').AbelTheorem] in
theorem kw_functionFieldMapAlongGeneral_yGen :
    kw_functionFieldMapAlongGeneral W F F' (yGen (W⁄F)) = yGen (W⁄F') :=
  pointPullbackHomTo_yGen _ _

def KwFunctionFieldTensorIsDomainGeneral : Prop :=
  IsDomain ((W⁄F).FunctionField ⊗[F] F')

attribute [local instance] Algebra.TensorProduct.rightAlgebra

scoped instance kw_isScalarTower_base_right_tensorGeneral :
    IsScalarTower R₀ F' ((W⁄F).FunctionField ⊗[F] F') := by
  refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => ?_)
  rw [RingHom.comp_apply, Algebra.TensorProduct.right_algebraMap_apply,
    IsScalarTower.algebraMap_apply R₀ F F',
    show algebraMap R₀ ((W⁄F).FunctionField ⊗[F] F') r
      = (algebraMap F ((W⁄F).FunctionField ⊗[F] F')) (algebraMap R₀ F r) from
        IsScalarTower.algebraMap_apply R₀ F ((W⁄F).FunctionField ⊗[F] F') r,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

section FracHom

variable [IsDomain ((W⁄F).FunctionField ⊗[F] F')]

scoped instance kw_isScalarTower_base_right_fracTensorGeneral :
    IsScalarTower R₀ F' (FractionRing ((W⁄F).FunctionField ⊗[F] F')) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    (IsScalarTower.algebraMap_apply R₀ ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F')) r).trans <|
      (congrArg (algebraMap ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F')))
        (IsScalarTower.algebraMap_apply R₀ F' ((W⁄F).FunctionField ⊗[F] F') r)).trans
      (IsScalarTower.algebraMap_apply F' ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F')) (algebraMap R₀ F' r)).symm

omit [W.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F] [DecidableEq F']
  [IsAlgClosed F'] [CharZero F'] [(toAffine W⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F)] [(toAffine W⁄F).AbelTheorem]
  [(toAffine W⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F')]
  [(toAffine W⁄F').AbelTheorem] [IsDomain ((W⁄F).FunctionField ⊗[F] F')] in
theorem kw_equation_tensorFracXYGeneral :
    ((W⁄F').map (algebraMap F' (FractionRing ((W⁄F).FunctionField ⊗[F] F')))).toAffine.Equation
      (algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')))
      (algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((yGen (W⁄F)) ⊗ₜ[F] (1 : F'))) := by
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

omit [W.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F] [Algebra R₀ F'] [DecidableEq F']
  [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F'] [(toAffine W⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F)] [(toAffine W⁄F).AbelTheorem]
  [(toAffine W⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F')]
  [(toAffine W⁄F').AbelTheorem] [IsDomain ((W⁄F).FunctionField ⊗[F] F')] in
theorem kw_transcendental_tensorFracXGeneral :
    Function.Injective (Polynomial.aeval (R := F')
      (algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')))) := by
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

def kw_functionFieldTensorFracHomGeneral :
    (W⁄F').FunctionField →ₐ[F'] FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  pointPullbackHomTo (kw_equation_tensorFracXYGeneral W F F')
    (kw_transcendental_tensorFracXGeneral W F F')

omit [W.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F] [DecidableEq F']
  [IsAlgClosed F'] [CharZero F'] [(toAffine W⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F)] [(toAffine W⁄F).AbelTheorem]
  [(toAffine W⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F')]
  [(toAffine W⁄F').AbelTheorem] in
theorem kw_functionFieldTensorFracHomGeneral_X :
    kw_functionFieldTensorFracHomGeneral W F F' (polyToFunctionField (W⁄F') X)
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') _
          ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')) :=
  pointPullbackHomTo_polyToFunctionField_X _ _

omit [W.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F] [DecidableEq F']
  [IsAlgClosed F'] [CharZero F'] [(toAffine W⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F)] [(toAffine W⁄F).AbelTheorem]
  [(toAffine W⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F')]
  [(toAffine W⁄F').AbelTheorem] in
theorem kw_functionFieldTensorFracHomGeneral_yGen :
    kw_functionFieldTensorFracHomGeneral W F F' (yGen (W⁄F'))
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') _ ((yGen (W⁄F)) ⊗ₜ[F] (1 : F')) :=
  pointPullbackHomTo_yGen _ _

omit [W.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F] [DecidableEq F']
  [IsAlgClosed F'] [CharZero F'] [(toAffine W⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F)] [(toAffine W⁄F).AbelTheorem]
  [(toAffine W⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F')]
  [(toAffine W⁄F').AbelTheorem] in
theorem kw_functionFieldTensorFracHomGeneral_bijective :
    Function.Bijective (kw_functionFieldTensorFracHomGeneral W F F') := by
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

def kw_functionFieldTensorFracEquivGeneral :
    (W⁄F').FunctionField ≃ₐ[F'] FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  AlgEquiv.ofBijective _ (kw_functionFieldTensorFracHomGeneral_bijective W F F')

end FracHom
end Setup
end ModularCurve
end

section



section

open WeierstrassCurve  WeierstrassCurve.Affine   AlgebraicCurve
open Polynomial
open scoped TensorProduct Polynomial

namespace ModularCurve

universe u

section Setup

variable {R₀ : Type u} [Field R₀]
variable (W : WeierstrassCurve R₀) [W.IsElliptic]
variable (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']

variable [WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (W⁄F).toAffine]
variable [WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F').toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F').toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (W⁄F').toAffine]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

section FFDomain

local notation3 "CR" => (W⁄F).toAffine.CoordinateRing
local notation3 "FFₗ" => (W⁄F).FunctionField

omit [W.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F] [Algebra R₀ F'] [DecidableEq F']
  [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F'] [(toAffine W⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F)] [(toAffine W⁄F).AbelTheorem]
  [(toAffine W⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F')]
  [(toAffine W⁄F').AbelTheorem] in
theorem kw_coordinateRingMap_basisGeneral (i : ℕ × Fin 2) :
    CoordinateRing.map (W⁄F).toAffine (algebraMap F F')
        (kw_coordinateRingBasis (W⁄F).toAffine i)
      = kw_coordinateRingBasis ((W⁄F).toAffine.map (algebraMap F F')) i := by
  obtain ⟨n, j⟩ := i
  simp only [kw_coordinateRingBasis, Module.Basis.smulTower_apply,
    Polynomial.coe_basisMonomials, CoordinateRing.map_smul]
  congr 1
  · simp [Polynomial.map_monomial]
  · rcases j with ⟨j, hj⟩
    interval_cases j <;>
      simp [CoordinateRing.basis_apply, CoordinateRing.map,
        AdjoinRoot.lift_root, AdjoinRoot.powerBasis'_gen]

def kw_coordinateRingMapAlongGeneral :
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

omit [W.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F] [Algebra R₀ F'] [DecidableEq F']
  [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F'] [(toAffine W⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F)] [(toAffine W⁄F).AbelTheorem]
  [(toAffine W⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F')]
  [(toAffine W⁄F').AbelTheorem] in
theorem kw_coordinateRingTensor_isDomainGeneral : IsDomain (CR ⊗[F] F') := by
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

omit [W.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F] [Algebra R₀ F'] [DecidableEq F']
  [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F'] [(toAffine W⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine W⁄F)] [(toAffine W⁄F).AbelTheorem]
  [(toAffine W⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine W⁄F')]
  [(toAffine W⁄F').AbelTheorem] in
theorem kw_functionFieldTensorIsDomain_dischargeGeneral :
    KwFunctionFieldTensorIsDomainGeneral W F F' := by
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
    exact fun h => (nonZeroDivisors.ne_zero hc) (hinj (by simp only [map_zero] at h ⊢; exact h))
  exact IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Algebra.algebraMapSubmonoid (CR ⊗[F] F') (nonZeroDivisors CR)) _ hle

end FFDomain
end Setup
end ModularCurve
end

section

section


section

open  WeierstrassCurve  WeierstrassCurve.Affine  Polynomial AlgebraicCurve
open scoped TensorProduct Polynomial  Polynomial.Bivariate

namespace ModularCurve

universe u

attribute [local instance] Classical.propDecidable

section BetweenCurvesTensor

variable {R₀ : Type u} [Field R₀]
variable (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
variable (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']
variable [(E₀⁄F).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀⁄F).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀⁄F).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (E₀⁄F).toAffine] [(E₀'⁄F).IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀'⁄F).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀'⁄F).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (E₀'⁄F).toAffine] [(E₀⁄F').IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀⁄F').toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀⁄F').toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (E₀⁄F').toAffine] [(E₀'⁄F').IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀'⁄F').toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀'⁄F').toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (E₀'⁄F').toAffine]
variable (ι₀ : (E₀'⁄F).toAffine.FunctionField →ₐ[F] (E₀⁄F).toAffine.FunctionField)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def kw_surge_hgf4_bcTensorIota :
    (E₀'⁄F).toAffine.FunctionField ⊗[F] F' →ₐ[F] (E₀⁄F).toAffine.FunctionField ⊗[F] F' :=
  Algebra.TensorProduct.map ι₀ (AlgHom.id F F')

omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F']
  [WeierstrassCurve.IsElliptic E₀⁄F] [(toAffine E₀⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)] [(toAffine E₀⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F] [(toAffine E₀'⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)] [(toAffine E₀'⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [(toAffine E₀⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')] [(toAffine E₀⁄F').AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F'] [(toAffine E₀'⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')] [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcTensorIota_tmul (a : (E₀'⁄F).toAffine.FunctionField) (c : F') :
    kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀ (a ⊗ₜ[F] c) = (ι₀ a) ⊗ₜ[F] c := by
  simp [kw_surge_hgf4_bcTensorIota, Algebra.TensorProduct.map_tmul]

omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F']
  [WeierstrassCurve.IsElliptic E₀⁄F] [(toAffine E₀⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)] [(toAffine E₀⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F] [(toAffine E₀'⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)] [(toAffine E₀'⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [(toAffine E₀⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')] [(toAffine E₀⁄F').AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F'] [(toAffine E₀'⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')] [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcTensorIota_injective :
    Function.Injective (kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := F') ι₀.toLinearMap ι₀.injective

variable [IsDomain ((E₀⁄F).toAffine.FunctionField ⊗[F] F')]
variable [IsDomain ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')]

def kw_surge_hgf4_bcTensorFracIota :
    FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
      →+* FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F') :=
  IsFractionRing.map (K := FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
    (L := FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F'))
    (kw_surge_hgf4_bcTensorIota_injective E₀ E₀' F F' ι₀)

omit [IsDomain ((toAffine E₀'⁄F).FunctionField ⊗[F] F')] in
omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F']
  [WeierstrassCurve.IsElliptic E₀⁄F] [(toAffine E₀⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)] [(toAffine E₀⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F] [(toAffine E₀'⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)] [(toAffine E₀'⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [(toAffine E₀⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')] [(toAffine E₀⁄F').AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F'] [(toAffine E₀'⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')] [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcTensorFracIota_algebraMap
    (t : (E₀'⁄F).toAffine.FunctionField ⊗[F] F') :
    kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀
        (algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ t)
      = algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _
          (kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀ t) := by
  unfold kw_surge_hgf4_bcTensorFracIota IsFractionRing.map
  exact IsLocalization.map_eq
    (T := nonZeroDivisors ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ t

omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F']
  [WeierstrassCurve.IsElliptic E₀⁄F] [(toAffine E₀⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)] [(toAffine E₀⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F] [(toAffine E₀'⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)] [(toAffine E₀'⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [(toAffine E₀⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')] [(toAffine E₀⁄F').AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F'] [(toAffine E₀'⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')] [(toAffine E₀'⁄F').AbelTheorem]
  [IsDomain ((toAffine E₀⁄F).FunctionField ⊗[F] F')]
  [IsDomain ((toAffine E₀'⁄F).FunctionField ⊗[F] F')] in
theorem kw_surge_hgf4_bcTensorIota_finite (hfin₀ : FiniteAlong F ι₀) :
    (kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀).toRingHom.Finite :=
  RingHom.Finite.tensorProductMap (f := ι₀) hfin₀ (g := AlgHom.id F F') (RingHom.Finite.id F')

def kw_surge_hgf4_bcTensorFracIotaAlg :
    FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
      →ₐ[F'] FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F') :=
  { kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀ with
    commutes' := fun c => by
      change kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀ (algebraMap F' _ c)
          = algebraMap F' _ c
      rw [IsScalarTower.algebraMap_apply F' ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
          (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')),
        Algebra.TensorProduct.right_algebraMap_apply,
        kw_surge_hgf4_bcTensorFracIota_algebraMap E₀ E₀' F F' ι₀,
        kw_surge_hgf4_bcTensorIota_tmul, map_one,
        IsScalarTower.algebraMap_apply F' ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
          (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')),
        Algebra.TensorProduct.right_algebraMap_apply] }

def kw_surge_hgf4_bcIota₁ :
    (E₀'⁄F').toAffine.FunctionField →ₐ[F'] (E₀⁄F').toAffine.FunctionField :=
  let ψE := kw_functionFieldTensorFracEquivGeneral E₀ F F'
  let ψE' := kw_functionFieldTensorFracEquivGeneral E₀' F F'
  (ψE.symm.toAlgHom.comp (kw_surge_hgf4_bcTensorFracIotaAlg E₀ E₀' F F' ι₀)).comp
    ψE'.toAlgHom

private theorem fractionRing_span_and_independent
    {T T' : Type*} [CommRing T] [IsDomain T] [CommRing T'] [IsDomain T']
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

omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [IsScalarTower R₀ F F']
  [WeierstrassCurve.IsElliptic E₀⁄F] [(toAffine E₀⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)] [(toAffine E₀⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F] [(toAffine E₀'⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)] [(toAffine E₀'⁄F).AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [(toAffine E₀⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')] [(toAffine E₀⁄F').AbelTheorem]
  [WeierstrassCurve.IsElliptic E₀'⁄F'] [(toAffine E₀'⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')] [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcTensorFracIotaSeam (hfin₀ : FiniteAlong F ι₀) :
    (kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀).Finite ∧
    (letI := (kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀).toAlgebra
     @Module.finrank (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
       (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ _ Algebra.toModule)
      = finrankAlong F ι₀ := by
  classical
  let FF := (E₀⁄F).toAffine.FunctionField
  let FF' := (E₀'⁄F).toAffine.FunctionField
  let T := (E₀⁄F).toAffine.FunctionField ⊗[F] F'
  let T' := (E₀'⁄F).toAffine.FunctionField ⊗[F] F'
  let FrT := FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
  let FrT' := FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
  let ιT : T' →+* T := (kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀).toRingHom
  let ιFr : FrT' →+* FrT := kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀
  have hιT_inj : Function.Injective ιT :=
    kw_surge_hgf4_bcTensorIota_injective E₀ E₀' F F' ι₀
  have hιT_fin : ιT.Finite := kw_surge_hgf4_bcTensorIota_finite E₀ E₀' F F' ι₀ hfin₀
  have hιFr_am : ∀ t : T', ιFr (algebraMap T' FrT' t) = algebraMap T FrT (ιT t) :=
    kw_surge_hgf4_bcTensorFracIota_algebraMap E₀ E₀' F F' ι₀
  let algι : Algebra FF' FF := ι₀.toRingHom.toAlgebra
  let modι : Module FF' FF := Algebra.toModule
  have hsmul_ι : ∀ (c : FF') (x : FF), c • x = ι₀ c * x := fun c x => rfl
  have hfinFF : Module.Finite FF' FF := hfin₀
  have hfreeFF : Module.Free FF' FF := Module.Free.of_divisionRing FF' FF
  let D := finrankAlong F ι₀
  let b : Module.Basis (Fin D) FF' FF := Module.finBasisOfFinrankEq FF' FF (n := D) rfl
  have hrepr_mul : ∀ (c : FF') (x : FF) (j : Fin D),
      b.repr (ι₀ c * x) j = c * b.repr x j := fun c x j => by
    rw [← hsmul_ι, map_smul, Finsupp.smul_apply, smul_eq_mul]
  let e : Fin D → T := fun i => (b i) ⊗ₜ[F] (1 : F')
  let bFr : Fin D → FrT := fun i => algebraMap T FrT (e i)
  have hspanT : ∀ t : T, ∃ c : Fin D → T', t = ∑ i, ιT (c i) * e i := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy =>
      obtain ⟨cx, hx⟩ := hx; obtain ⟨cy, hy⟩ := hy
      exact ⟨cx + cy, by simp only [Pi.add_apply, map_add, add_mul,
        Finset.sum_add_distrib, ← hx, ← hy]⟩
    | tmul a c =>
      refine ⟨fun i => (b.repr a i) ⊗ₜ[F] c, ?_⟩
      have hb_sum : a = ∑ i, ι₀ (b.repr a i) * b i := by
        conv_lhs => rw [← b.linearCombination_repr a, Finsupp.linearCombination_apply,
          Finsupp.sum_fintype _ _ (fun i => by rw [hsmul_ι, map_zero, zero_mul])]
        exact Finset.sum_congr rfl fun i _ => hsmul_ι _ _
      calc (a ⊗ₜ[F] c : T)
          = (∑ i, ι₀ (b.repr a i) * b i) ⊗ₜ[F] c := by rw [← hb_sum]
        _ = ∑ i, ιT ((b.repr a i) ⊗ₜ[F] c) * e i := by
            rw [TensorProduct.sum_tmul]
            refine Finset.sum_congr rfl fun i _ => ?_
            show (ι₀ (b.repr a i) * b i) ⊗ₜ[F] c = ιT ((b.repr a i) ⊗ₜ[F] c) * e i
            rw [show ιT ((b.repr a i) ⊗ₜ[F] c) = (ι₀ (b.repr a i)) ⊗ₜ[F] c from
                  kw_surge_hgf4_bcTensorIota_tmul E₀ E₀' F F' ι₀ _ _,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hliT : ∀ c : Fin D → T', ∑ i, ιT (c i) * e i = 0 → ∀ j, c j = 0 := by
    intro c hc j
    let pj : FF →ₗ[F] FF' :=
      { toFun := fun x => b.repr x j
        map_add' := fun x y => by simp only [map_add, Finsupp.add_apply]
        map_smul' := fun f x => by
          simp only [RingHom.id_apply, Algebra.smul_def]
          have h := hrepr_mul (algebraMap F FF' f) x j
          rwa [ι₀.commutes] at h }
    let Ej : T →ₗ[F] T' := LinearMap.rTensor F' pj
    have hEj_key : ∀ (a : T') (i : Fin D),
        Ej (ιT a * e i) = if i = j then a else 0 := by
      intro a i
      induction a using TensorProduct.inductionOn with
      | add x y hx hy =>
        simp only [map_add, add_mul, hx, hy]; split_ifs <;> simp
      | tmul x c' =>
        rw [show ιT ((x : FF') ⊗ₜ[F] c') = (ι₀ x) ⊗ₜ[F] c' from
              kw_surge_hgf4_bcTensorIota_tmul E₀ E₀' F F' ι₀ _ _,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        change (pj (ι₀ x * b i)) ⊗ₜ[F] c' = if i = j then (x : FF') ⊗ₜ[F] c' else 0
        rw [show pj (ι₀ x * b i) = if i = j then x else 0 from ?_]
        · split_ifs with h
          · rfl
          · exact TensorProduct.zero_tmul _ c'
        · change b.repr (ι₀ x * b i) j = if i = j then x else 0
          rw [hrepr_mul, b.repr_self, Finsupp.single_apply]
          split_ifs with h <;> simp
    have hc' : Ej (∑ i, ιT (c i) * e i) = 0 := by rw [hc, map_zero]
    simpa only [map_sum, hEj_key, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hc'
  obtain ⟨hspanFr, hliFr⟩ :=
    fractionRing_span_and_independent ιT ιFr hιT_inj hιT_fin hιFr_am e hspanT hliT
  let algFr : Algebra FrT' FrT := ιFr.toAlgebra
  let modFr : Module FrT' FrT := Algebra.toModule
  have hsmul_Fr : ∀ (c : FrT') (x : FrT), c • x = ιFr c * x := fun c x => rfl
  have hli_modFr : LinearIndependent FrT' bFr := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    refine hliFr g ?_ i
    simpa only [hsmul_Fr] using hg
  have hsp_modFr : ⊤ ≤ Submodule.span FrT' (Set.range bFr) := by
    intro z _
    obtain ⟨d, hd⟩ := hspanFr z
    rw [hd]
    exact Submodule.sum_mem _ fun i _ => (hsmul_Fr (d i) (bFr i)) ▸
      Submodule.smul_mem _ (d i) (Submodule.subset_span ⟨i, rfl⟩)
  let bFr' : Module.Basis (Fin D) FrT' FrT := .mk hli_modFr hsp_modFr
  refine ⟨Module.Finite.of_basis bFr', ?_⟩
  change Module.finrank FrT' FrT = D
  rw [Module.finrank_eq_card_basis bFr', Fintype.card_fin]

omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [WeierstrassCurve.IsElliptic E₀⁄F]
  [(toAffine E₀⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)]
  [(toAffine E₀⁄F).AbelTheorem] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [(toAffine E₀'⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)]
  [(toAffine E₀'⁄F).AbelTheorem] [WeierstrassCurve.IsElliptic E₀⁄F']
  [(toAffine E₀⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')]
  [(toAffine E₀⁄F').AbelTheorem] [WeierstrassCurve.IsElliptic E₀'⁄F']
  [(toAffine E₀'⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')]
  [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcIota₁_finiteAlong (hfin₀ : FiniteAlong F ι₀) :
    FiniteAlong F' (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀) := by
  have hFr_fin := (kw_surge_hgf4_bcTensorFracIotaSeam E₀ E₀' F F' ι₀ hfin₀).1
  let ψE := kw_functionFieldTensorFracEquivGeneral E₀ F F'
  let ψE' := kw_functionFieldTensorFracEquivGeneral E₀' F F'
  have h1 : RingHom.Finite ψE'.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ ψE'.surjective
  have h2 : RingHom.Finite ψE.symm.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ ψE.symm.surjective
  change RingHom.Finite (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀).toRingHom
  have hcomp : (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀).toRingHom
      = (ψE.symm.toAlgHom.toRingHom.comp
          (kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀)).comp ψE'.toAlgHom.toRingHom := rfl
  rw [hcomp]
  exact RingHom.Finite.comp (RingHom.Finite.comp h2 hFr_fin) h1

omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [WeierstrassCurve.IsElliptic E₀⁄F]
  [(toAffine E₀⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)]
  [(toAffine E₀⁄F).AbelTheorem] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [(toAffine E₀'⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)]
  [(toAffine E₀'⁄F).AbelTheorem] [WeierstrassCurve.IsElliptic E₀⁄F']
  [(toAffine E₀⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')]
  [(toAffine E₀⁄F').AbelTheorem] [WeierstrassCurve.IsElliptic E₀'⁄F']
  [(toAffine E₀'⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')]
  [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcIota₁_isIntegral (hfin₀ : FiniteAlong F ι₀) :
    (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀).toRingHom.IsIntegral :=
  RingHom.Finite.to_isIntegral
    (show RingHom.Finite (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀).toRingHom from
      kw_surge_hgf4_bcIota₁_finiteAlong E₀ E₀' F F' ι₀ hfin₀)

omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [WeierstrassCurve.IsElliptic E₀⁄F]
  [(toAffine E₀⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)]
  [(toAffine E₀⁄F).AbelTheorem] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [(toAffine E₀'⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)]
  [(toAffine E₀'⁄F).AbelTheorem] [WeierstrassCurve.IsElliptic E₀⁄F']
  [(toAffine E₀⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')]
  [(toAffine E₀⁄F').AbelTheorem] [WeierstrassCurve.IsElliptic E₀'⁄F']
  [(toAffine E₀'⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')]
  [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcIota₁_finrankAlong (hfin₀ : FiniteAlong F ι₀) :
    finrankAlong F' (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀) = finrankAlong F ι₀ := by
  let ψE := kw_functionFieldTensorFracEquivGeneral E₀ F F'
  let ψE' := kw_functionFieldTensorFracEquivGeneral E₀' F F'
  let ιFr := kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀
  have hcomm : ∀ x, ιFr (ψE' x)
      = ψE (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀ x) := fun x => by
    change ιFr (ψE' x) = ψE (ψE.symm (_))
    exact (ψE.apply_symm_apply _).symm
  calc finrankAlong F' (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀)
      = (letI := ιFr.toAlgebra
         @Module.finrank (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
           (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ _ Algebra.toModule) :=
        @Algebra.finrank_eq_of_equiv_equiv
          (E₀'⁄F').toAffine.FunctionField (E₀⁄F').toAffine.FunctionField _ _
          (algebraAlong (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀))
          _ _ _ _ ιFr.toAlgebra ψE'.toRingEquiv ψE.toRingEquiv (RingHom.ext hcomm)
    _ = finrankAlong F ι₀ := (kw_surge_hgf4_bcTensorFracIotaSeam E₀ E₀' F F' ι₀ hfin₀).2

section Naturality

variable (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong F ι₀)
variable (σ : F →ₐ[R₀] F') (hσ : ∀ c, σ c = algebraMap F F' c)

local notation "χE" => kw_functionFieldMapAlongGeneral E₀ F F'
local notation "χE'" => kw_functionFieldMapAlongGeneral E₀' F F'
local notation "ι₁" => kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀

theorem kw_surge_hgf4_place_inv_mem_of_isUnit {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : Place K L) {z : v.toValuationSubring} (hz : IsUnit z) :
    ((z : L))⁻¹ ∈ v.toValuationSubring := by
  obtain ⟨w, hw⟩ := hz.exists_right_inv
  have hmul : (z : L) * (w : L) = 1 := by
    have h := congrArg (fun a : v.toValuationSubring => (a : L)) hw
    simpa using h
  rw [inv_eq_of_mul_eq_one_right hmul]; exact w.2

omit [DecidableEq F] [DecidableEq F'] in
omit [IsAlgClosed F] [CharZero F] [IsAlgClosed F'] [CharZero F'] in
theorem kw_surge_hgf4_toAffine_map_eq (V : WeierstrassCurve R₀) :
    (V⁄F).toAffine.map (algebraMap F F') = (V⁄F').toAffine := by
  classical
  change ((V.map (algebraMap R₀ F)).map (algebraMap F F')).toAffine = (V.map (algebraMap R₀
    F')).toAffine
  rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq R₀ F F']

open WeierstrassCurve.Affine.CoordinateRing in
omit [IsAlgClosed F] [CharZero F] [IsAlgClosed F'] [CharZero F'] in
theorem kw_surge_hgf4_χE_algebraMap_XClass (V : WeierstrassCurve R₀) [V.IsElliptic]
    [(V⁄F).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (V⁄F).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (V⁄F).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (V⁄F).toAffine] [(V⁄F').IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate (V⁄F').toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (V⁄F').toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (V⁄F').toAffine] (x : F) :
    kw_functionFieldMapAlongGeneral V F F'
        (algebraMap (V⁄F).toAffine.CoordinateRing (V⁄F).toAffine.FunctionField
          (XClass (V⁄F).toAffine x))
      = algebraMap (V⁄F').toAffine.CoordinateRing (V⁄F').toAffine.FunctionField
          (XClass (V⁄F').toAffine (algebraMap F F' x)) := by
  have hF : algebraMap (V⁄F).toAffine.CoordinateRing (V⁄F).toAffine.FunctionField
      (XClass (V⁄F).toAffine x)
      = polyToFunctionField (V⁄F).toAffine X - algebraMap F (V⁄F).toAffine.FunctionField x := by
    rw [← polyToFunctionField_C, ← map_sub]; rfl
  have hF' : algebraMap (V⁄F').toAffine.CoordinateRing (V⁄F').toAffine.FunctionField
      (XClass (V⁄F').toAffine (algebraMap F F' x))
      = polyToFunctionField (V⁄F').toAffine X
          - algebraMap F' (V⁄F').toAffine.FunctionField (algebraMap F F' x) := by
    rw [← polyToFunctionField_C, ← map_sub]; rfl
  rw [hF, hF', map_sub, kw_functionFieldMapAlongGeneral_polyToFunctionField_X,
    AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (V⁄F').toAffine.FunctionField]

open WeierstrassCurve.Affine.CoordinateRing in
omit [IsAlgClosed F] [CharZero F] [IsAlgClosed F'] [CharZero F'] in
theorem kw_surge_hgf4_χE_algebraMap_YClass (V : WeierstrassCurve R₀) [V.IsElliptic]
    [(V⁄F).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (V⁄F).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (V⁄F).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (V⁄F).toAffine] [(V⁄F').IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate (V⁄F').toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (V⁄F').toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (V⁄F').toAffine] (y : F) :
    kw_functionFieldMapAlongGeneral V F F'
        (algebraMap (V⁄F).toAffine.CoordinateRing (V⁄F).toAffine.FunctionField
          (YClass (V⁄F).toAffine (C y)))
      = algebraMap (V⁄F').toAffine.CoordinateRing (V⁄F').toAffine.FunctionField
          (YClass (V⁄F').toAffine (C (algebraMap F F' y))) := by
  have hF : algebraMap (V⁄F).toAffine.CoordinateRing (V⁄F).toAffine.FunctionField
      (YClass (V⁄F).toAffine (C y))
      = yGen (V⁄F).toAffine - algebraMap F (V⁄F).toAffine.FunctionField y := by
    rw [YClass, map_sub, map_sub, yGen]
    congr 1
  have hF' : algebraMap (V⁄F').toAffine.CoordinateRing (V⁄F').toAffine.FunctionField
      (YClass (V⁄F').toAffine (C (algebraMap F F' y)))
      = yGen (V⁄F').toAffine
          - algebraMap F' (V⁄F').toAffine.FunctionField (algebraMap F F' y) := by
    rw [YClass, map_sub, map_sub, yGen]
    congr 1
  rw [hF, hF', map_sub, kw_functionFieldMapAlongGeneral_yGen,
    AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (V⁄F').toAffine.FunctionField]

omit [IsDomain ((toAffine E₀⁄F).FunctionField ⊗[F] F')] in
omit [CharZero F] [CharZero F'] in
theorem kw_surge_hgf4_χE_VSR_compat {x y : F} (hP : (E₀⁄F).toAffine.Nonsingular x y)
    (hσP : (E₀⁄F').toAffine.Nonsingular (algebraMap F F' x) (algebraMap F F' y))
    (g : (E₀⁄F).toAffine.FunctionField) :
    χE g ∈ (placeOfEquation hσP.left).toValuationSubring ↔
      g ∈ (placeOfEquation hP.left).toValuationSubring := by
  have hχE_inj : Function.Injective (χE : _ →ₐ[F] _) :=
    (kw_functionFieldMapAlongGeneral E₀ F F').injective
  classical
  have hmk (W : Affine F) : ∀ q : F[X][Y],
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W q)
        = q.eval₂ (polyToFunctionField W) (yGen W) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p r hp hr => rw [map_add, map_add, Polynomial.eval₂_add, hp, hr]
    | monomial n a =>
        simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
          Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X]
        rw [← algebraMap_polynomial_eq_mk_C, ← polyToFunctionField_apply]; rfl
  have hfinσP : IsFinitePlace (placeOfEquation hσP.left) :=
    isFinitePlace_placeOfEquation hσP.left
  have hχE_polyToFF (p : F[X]) :
      χE (polyToFunctionField (E₀⁄F).toAffine p) ∈ (placeOfEquation hσP.left).toValuationSubring
        := by
    have h : χE (polyToFunctionField (E₀⁄F).toAffine p)
        = polyToFunctionField (E₀⁄F').toAffine (p.map (algebraMap F F')) := by
      induction p using Polynomial.induction_on' with
      | add r s hr hs => rw [map_add, map_add, Polynomial.map_add, map_add, hr, hs]
      | monomial n c =>
          rw [Polynomial.map_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
            ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow,
            map_mul, map_pow, polyToFunctionField_C, polyToFunctionField_C,
            kw_functionFieldMapAlongGeneral_polyToFunctionField_X, AlgHom.commutes,
            IsScalarTower.algebraMap_apply F F' (E₀⁄F').toAffine.FunctionField]
    rw [h, polyToFunctionField_apply]
    exact hfinσP _
  have hχE_CR_mem : ∀ a : (E₀⁄F).toAffine.CoordinateRing,
      χE (algebraMap _ _ a) ∈ (placeOfEquation hσP.left).toValuationSubring := by
    intro a
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hmk (E₀⁄F).toAffine q]
    induction q using Polynomial.induction_on' with
    | add r s hr hs =>
        rw [Polynomial.eval₂_add, map_add]
        exact Subring.add_mem _ hr hs
    | monomial n p =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
          Polynomial.eval₂_C, Polynomial.eval₂_X, map_mul, map_pow,
          kw_functionFieldMapAlongGeneral_yGen]
        exact Subring.mul_mem _ (hχE_polyToFF p)
          (Subring.pow_mem _ (hfinσP (CoordinateRing.mk (E₀⁄F').toAffine Y)) n)
  have hXClass_σP_mem_𝔪 : (⟨algebraMap _ _ (CoordinateRing.XClass (E₀⁄F').toAffine
        (algebraMap F F' x)), hfinσP _⟩ : (placeOfEquation hσP.left).toValuationSubring)
      ∈ IsLocalRing.maximalIdeal (placeOfEquation hσP.left).toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_ord_pos _
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (CoordinateRing.XClass_ne_zero _))]
    exact (ord_placeOfEquation_pos_iff hσP.left (CoordinateRing.XClass_ne_zero _)).mpr
      (Ideal.subset_span (Set.mem_insert _ _))
  have hYClass_σP_mem_𝔪 : (⟨algebraMap _ _ (CoordinateRing.YClass (E₀⁄F').toAffine
        (C (algebraMap F F' y))), hfinσP _⟩ : (placeOfEquation hσP.left).toValuationSubring)
      ∈ IsLocalRing.maximalIdeal (placeOfEquation hσP.left).toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_ord_pos _
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (CoordinateRing.YClass_ne_zero _))]
    exact (ord_placeOfEquation_pos_iff hσP.left (CoordinateRing.YClass_ne_zero _)).mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have hχE_mem_𝔪 : ∀ a ∈ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y),
      (⟨χE (algebraMap _ _ a), hχE_CR_mem a⟩ : (placeOfEquation hσP.left).toValuationSubring)
        ∈ IsLocalRing.maximalIdeal (placeOfEquation hσP.left).toValuationSubring := by
    intro a ha
    rw [CoordinateRing.XYIdeal, Ideal.mem_span_pair] at ha
    obtain ⟨p, q, hpq⟩ := ha
    have hdecomp : χE (algebraMap _ _ a)
        = χE (algebraMap _ _ p) * χE (algebraMap _ _ (CoordinateRing.XClass (E₀⁄F).toAffine x))
          + χE (algebraMap _ _ q)
            * χE (algebraMap _ _ (CoordinateRing.YClass (E₀⁄F).toAffine (C y))) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add, hpq]
    rw [show (⟨χE (algebraMap _ _ a), hχE_CR_mem a⟩ :
          (placeOfEquation hσP.left).toValuationSubring)
        = ⟨χE (algebraMap _ _ p), hχE_CR_mem p⟩
            * ⟨_, hfinσP (CoordinateRing.XClass (E₀⁄F').toAffine (algebraMap F F' x))⟩
          + ⟨χE (algebraMap _ _ q), hχE_CR_mem q⟩
            * ⟨_, hfinσP (CoordinateRing.YClass (E₀⁄F').toAffine (C (algebraMap F F' y)))⟩ from
        Subtype.ext (by
          push_cast
          rw [hdecomp, kw_surge_hgf4_χE_algebraMap_XClass F F' E₀ x,
            kw_surge_hgf4_χE_algebraMap_YClass F F' E₀ y])]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hXClass_σP_mem_𝔪)
      (Ideal.mul_mem_left _ _ hYClass_σP_mem_𝔪)
  have hχE_unit : ∀ s : (E₀⁄F).toAffine.CoordinateRing,
      s ∉ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y) →
      IsUnit (⟨χE (algebraMap _ _ s), hχE_CR_mem s⟩ :
        (placeOfEquation hσP.left).toValuationSubring) := by
    intro s hs
    obtain ⟨c, hc⟩ := CoordinateRing.exists_sub_algebraMap_mem hP.left s
    have hc_ne : c ≠ 0 := by
      intro h; apply hs; simpa [h, sub_zero] using hc
    have hσc_ne : algebraMap F F' c ≠ 0 := (map_ne_zero_iff _ (algebraMap F F').injective).mpr hc_ne
    have hχE_const : χE (algebraMap (E₀⁄F).toAffine.CoordinateRing _
          (algebraMap F (E₀⁄F).toAffine.CoordinateRing c))
        = algebraMap F' (E₀⁄F').toAffine.FunctionField (algebraMap F F' c) := by
      rw [← IsScalarTower.algebraMap_apply F (E₀⁄F).toAffine.CoordinateRing
        (E₀⁄F).toAffine.FunctionField, AlgHom.commutes,
        IsScalarTower.algebraMap_apply F F' (E₀⁄F').toAffine.FunctionField]
    have hsplit : (⟨χE (algebraMap _ _ s), hχE_CR_mem s⟩ :
          (placeOfEquation hσP.left).toValuationSubring)
        = ⟨algebraMap F' _ (algebraMap F F' c),
            (placeOfEquation hσP.left).algebraMap_mem' _⟩
          + ⟨χE (algebraMap _ _ (s - algebraMap F _ c)), hχE_CR_mem _⟩ := by
      refine Subtype.ext ?_
      change χE (algebraMap _ _ s)
          = algebraMap F' (E₀⁄F').toAffine.FunctionField (algebraMap F F' c)
            + χE (algebraMap _ _ (s - algebraMap F _ c))
      rw [← hχE_const, ← map_add, ← map_add, add_sub_cancel]
    rw [hsplit]
    have hfirst_unit : IsUnit (⟨algebraMap F' _ (algebraMap F F' c),
        (placeOfEquation hσP.left).algebraMap_mem' _⟩ :
        (placeOfEquation hσP.left).toValuationSubring) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap F' _ (algebraMap F F' c)⁻¹,
        (placeOfEquation hσP.left).algebraMap_mem' _⟩, Subtype.ext ?_⟩
      push_cast
      rw [← map_inv₀, ← map_mul, mul_inv_cancel₀ hσc_ne, map_one]
    have hsecond_𝔪 := hχE_mem_𝔪 (s - algebraMap F _ c) hc
    by_contra hnotunit
    have hsum_𝔪 := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnotunit)
    have hfirst_𝔪 : (⟨algebraMap F' _ (algebraMap F F' c),
          (placeOfEquation hσP.left).algebraMap_mem' _⟩ :
          (placeOfEquation hσP.left).toValuationSubring)
        ∈ IsLocalRing.maximalIdeal _ := by
      have hsub := Ideal.sub_mem _ hsum_𝔪 hsecond_𝔪
      rwa [add_sub_cancel_right] at hsub
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hfirst_𝔪)) hfirst_unit
  have hXY_prime : (CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y)).IsPrime :=
    (CoordinateRing.XYIdeal_isMaximal hP.left).isPrime
  have hmem_P : ∀ f : (E₀⁄F).toAffine.FunctionField,
      f ∈ (placeOfEquation hP.left).toValuationSubring
        ↔ ∃ (n s : (E₀⁄F).toAffine.CoordinateRing)
            (_ : s ∉ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y)),
          f = algebraMap _ _ n * (algebraMap _ _ s)⁻¹ := by
    intro f
    have hfinP := isFinitePlace_placeOfEquation hP.left
    constructor
    · intro hf
      obtain ⟨n, s, hcase⟩ :=
        (CoordinateRing.heightOneSpectrumOfEquation hP.left).exists_primeCompl_mul_eq_or_mul_eq
          (K := (E₀⁄F).toAffine.FunctionField) f
      have hs_nin : (s : (E₀⁄F).toAffine.CoordinateRing)
          ∉ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y) :=
        Ideal.mem_primeCompl_iff.mp s.2
      have hs_CR_ne : (s : (E₀⁄F).toAffine.CoordinateRing) ≠ 0 :=
        fun h => hs_nin (h ▸ Ideal.zero_mem _)
      have hs0 : algebraMap (E₀⁄F).toAffine.CoordinateRing
          (E₀⁄F).toAffine.FunctionField (s : (E₀⁄F).toAffine.CoordinateRing) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hs_CR_ne
      rcases hcase with heq | heq
      · refine ⟨n, s, hs_nin, ?_⟩
        field_simp at heq ⊢; linear_combination heq
      · by_cases hn_nin : (n : _) ∈ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y)
        · exfalso
          have hn0 : (n : (E₀⁄F).toAffine.CoordinateRing) ≠ 0 := fun h => by
            rw [h, map_zero, mul_zero] at heq
            exact hs_CR_ne ((map_eq_zero_iff _
              (IsFractionRing.injective _ _)).mp heq.symm)
          have hord_n_pos : 0 < (placeOfEquation hP.left).ord (algebraMap _ _ (n : _)) :=
            (ord_placeOfEquation_pos_iff hP.left hn0).mpr hn_nin
          have hord_s_zero : (placeOfEquation hP.left).ord
              (algebraMap _ _ (s : (E₀⁄F).toAffine.CoordinateRing)) = 0 := by
            by_contra hne
            exact hs_nin ((ord_placeOfEquation_ne_zero_iff hP.left hs_CR_ne).mp hne)
          have hord_f_neg : (placeOfEquation hP.left).ord f < 0 := by
            have hf0 : f ≠ 0 := fun h => by
              rw [h, zero_mul] at heq
              exact hs_CR_ne ((map_eq_zero_iff _
                (IsFractionRing.injective _ _)).mp heq.symm)
            have hfn_eq : (placeOfEquation hP.left).ord f
                + (placeOfEquation hP.left).ord (algebraMap _ _ (n : _))
                = (placeOfEquation hP.left).ord
                    (algebraMap _ _ (s : (E₀⁄F).toAffine.CoordinateRing)) := by
              rw [← Place.ord_mul _ hf0
                  ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hn0), heq]
            omega
          exact not_le.mpr hord_f_neg (AlgebraicCurve.Place.ord_nonneg_of_mem (placeOfEquation
            hP.left) hf)
        · refine ⟨s, n, hn_nin, ?_⟩
          have hn0 : algebraMap _ (E₀⁄F).toAffine.FunctionField (n : _) ≠ 0 :=
            (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
              (fun h => hn_nin (h ▸ Ideal.zero_mem _))
          field_simp at heq ⊢; linear_combination heq
    · rintro ⟨n, s, hs_nin, rfl⟩
      have hs_inv : (algebraMap _ _ s)⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring :=
        hfinP.inv_mem (by rwa [centre_placeOfEquation])
      exact Subring.mul_mem _ (hfinP n) hs_inv
  constructor
  · intro hχEg
    by_contra hg_notin
    have hg_ne : g ≠ 0 := fun h => hg_notin (h ▸ Subring.zero_mem _)
    have hginv_in : g⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring :=
      ((placeOfEquation hP.left).toValuationSubring.mem_or_inv_mem g).resolve_left hg_notin
    obtain ⟨n, s, hs_notin, hginv_eq⟩ := (hmem_P g⁻¹).mp hginv_in
    have hginv_𝔪 : (⟨g⁻¹, hginv_in⟩ : (placeOfEquation hP.left).toValuationSubring)
        ∈ IsLocalRing.maximalIdeal _ := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hg_notin (inv_inv g ▸ kw_surge_hgf4_place_inv_mem_of_isUnit _ hu)
    have hn_in : n ∈ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y) := by
      by_contra hn_notin
      have hfinP := isFinitePlace_placeOfEquation hP.left
      have hn_inv : (algebraMap _ _ n)⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring :=
        hfinP.inv_mem (by rwa [centre_placeOfEquation])
      have hs_inv : (algebraMap _ _ s)⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring :=
        hfinP.inv_mem (by rwa [centre_placeOfEquation])
      have hginv_unit : IsUnit
          (⟨g⁻¹, hginv_in⟩ : (placeOfEquation hP.left).toValuationSubring) := by
        have hg_mem : g ∈ (placeOfEquation hP.left).toValuationSubring := by
          have : g = algebraMap _ _ s * (algebraMap _ _ n)⁻¹ := by
            rw [← inv_inv g, hginv_eq, mul_inv, inv_inv, mul_comm]
          rw [this]; exact Subring.mul_mem _ (hfinP s) hn_inv
        exact isUnit_iff_exists_inv.mpr
          ⟨(⟨g, hg_mem⟩ : (placeOfEquation hP.left).toValuationSubring),
           Subtype.ext (by push_cast; exact inv_mul_cancel₀ hg_ne)⟩
      exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hginv_𝔪) hginv_unit
    have hχEn_𝔪 := hχE_mem_𝔪 n hn_in
    have hχEs_unit := hχE_unit s hs_notin
    have hχEginv_eq : χE g⁻¹ = χE (algebraMap _ _ n) * (χE (algebraMap _ _ s))⁻¹ := by
      rw [hginv_eq, map_mul, map_inv₀]
    have hχEginv_mem : χE g⁻¹ ∈ (placeOfEquation hσP.left).toValuationSubring := by
      rw [hχEginv_eq]
      exact Subring.mul_mem _ (hχE_CR_mem n)
        (kw_surge_hgf4_place_inv_mem_of_isUnit _ hχEs_unit)
    have hχEginv_𝔪 : (⟨χE g⁻¹, hχEginv_mem⟩ :
          (placeOfEquation hσP.left).toValuationSubring)
        ∈ IsLocalRing.maximalIdeal (placeOfEquation hσP.left).toValuationSubring := by
      have hχEs_inv_mem := kw_surge_hgf4_place_inv_mem_of_isUnit _ hχEs_unit
      have hrw : (⟨χE g⁻¹, hχEginv_mem⟩ : (placeOfEquation hσP.left).toValuationSubring)
          = (⟨χE (algebraMap _ _ n), hχE_CR_mem n⟩ :
              (placeOfEquation hσP.left).toValuationSubring)
            * ⟨(χE (algebraMap _ _ s))⁻¹, hχEs_inv_mem⟩ :=
        Subtype.ext (by change χE g⁻¹ = _ * _; exact hχEginv_eq)
      rw [hrw]
      exact Ideal.mul_mem_right _ _ hχEn_𝔪
    have hχEg_ne : χE g ≠ 0 := (map_ne_zero_iff _ hχE_inj).mpr hg_ne
    have hχEginv_unit : IsUnit
        (⟨χE g⁻¹, hχEginv_mem⟩ : (placeOfEquation hσP.left).toValuationSubring) :=
      isUnit_iff_exists_inv.mpr
        ⟨(⟨χE g, hχEg⟩ : (placeOfEquation hσP.left).toValuationSubring),
         Subtype.ext (by change χE g⁻¹ * χE g = 1; rw [map_inv₀, inv_mul_cancel₀ hχEg_ne])⟩
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hχEginv_𝔪) hχEginv_unit
  · intro hg
    obtain ⟨n, s, hs_notin, hg_eq⟩ := (hmem_P g).mp hg
    rw [hg_eq, map_mul, map_inv₀]
    exact Subring.mul_mem _ (hχE_CR_mem n)
      (kw_surge_hgf4_place_inv_mem_of_isUnit _ (hχE_unit s hs_notin))

omit [WeierstrassCurve.IsElliptic E₀⁄F] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [WeierstrassCurve.IsElliptic E₀'⁄F'] in
omit [E₀.IsElliptic] [E₀'.IsElliptic] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  [DecidableEq F'] [IsAlgClosed F'] [CharZero F'] [(toAffine E₀⁄F).GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F)] [(toAffine E₀⁄F).AbelTheorem]
  [(toAffine E₀'⁄F).GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F)]
  [(toAffine E₀'⁄F).AbelTheorem] [(toAffine E₀⁄F').GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred (toAffine E₀⁄F')] [(toAffine E₀⁄F').AbelTheorem]
  [(toAffine E₀'⁄F').GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred (toAffine E₀'⁄F')]
  [(toAffine E₀'⁄F').AbelTheorem] in
theorem kw_surge_hgf4_bcIota₁_compat (a : (E₀'⁄F).toAffine.FunctionField) :
    (ι₁) (χE' a) = χE (ι₀ a) := by
  let ψE := kw_functionFieldTensorFracEquivGeneral E₀ F F'
  let ψE' := kw_functionFieldTensorFracEquivGeneral E₀' F F'
  have hκE' : ψE' (χE' a)
      = algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ (a ⊗ₜ[F] (1 : F')) := by
    have hκ : ((kw_functionFieldTensorFracHomGeneral E₀' F F').restrictScalars F).comp
        (kw_functionFieldMapAlongGeneral E₀' F F')
        = (IsScalarTower.toAlgHom F ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
            (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))).comp
            (Algebra.TensorProduct.includeLeft (R := F)) := by
      refine kw_functionField_algHom_ext ?_ ?_
      · change kw_functionFieldTensorFracHomGeneral E₀' F F' (χE' _) = _
        rw [kw_functionFieldMapAlongGeneral_polyToFunctionField_X,
          kw_functionFieldTensorFracHomGeneral_X]; rfl
      · change kw_functionFieldTensorFracHomGeneral E₀' F F' (χE' _) = _
        rw [kw_functionFieldMapAlongGeneral_yGen, kw_functionFieldTensorFracHomGeneral_yGen]
        rfl
    exact DFunLike.congr_fun hκ a
  have hκE : ∀ b, ψE.symm (algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _
      (b ⊗ₜ[F] (1 : F'))) = χE b := by
    intro b
    refine ψE.injective ?_
    rw [AlgEquiv.apply_symm_apply]
    have hκ : ((kw_functionFieldTensorFracHomGeneral E₀ F F').restrictScalars F).comp
        (kw_functionFieldMapAlongGeneral E₀ F F')
        = (IsScalarTower.toAlgHom F ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
            (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F'))).comp
            (Algebra.TensorProduct.includeLeft (R := F)) := by
      refine kw_functionField_algHom_ext ?_ ?_
      · change kw_functionFieldTensorFracHomGeneral E₀ F F' (χE _) = _
        rw [kw_functionFieldMapAlongGeneral_polyToFunctionField_X,
          kw_functionFieldTensorFracHomGeneral_X]; rfl
      · change kw_functionFieldTensorFracHomGeneral E₀ F F' (χE _) = _
        rw [kw_functionFieldMapAlongGeneral_yGen, kw_functionFieldTensorFracHomGeneral_yGen]
        rfl
    exact (DFunLike.congr_fun hκ b).symm
  change ψE.symm (kw_surge_hgf4_bcTensorFracIotaAlg E₀ E₀' F F' ι₀ (ψE' (χE' a)))
      = χE (ι₀ a)
  rw [hκE',
    show kw_surge_hgf4_bcTensorFracIotaAlg E₀ E₀' F F' ι₀
        (algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ (a ⊗ₜ[F] (1 : F')))
      = algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _ ((ι₀ a) ⊗ₜ[F] (1 : F')) from by
        change kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀ _ = _
        rw [kw_surge_hgf4_bcTensorFracIota_algebraMap, kw_surge_hgf4_bcTensorIota_tmul],
    hκE (ι₀ a)]

include hσ in
omit [E₀'.IsElliptic] in
theorem kw_surge_hgf4_pmop_naturality :
    let hι₁ := kw_surge_hgf4_bcIota₁_isIntegral E₀ E₀' F F' ι₀ hfin₀
    let hfin₁ := kw_surge_hgf4_bcIota₁_finiteAlong E₀ E₀' F F' ι₀ hfin₀
    let σE : (E₀⁄F).toAffine.Point →+ (E₀⁄F').toAffine.Point :=
      WeierstrassCurve.Affine.Point.map (W' := E₀.toAffine) σ
    let σE' : (E₀'⁄F).toAffine.Point →+ (E₀'⁄F').toAffine.Point :=
      WeierstrassCurve.Affine.Point.map (W' := E₀'.toAffine) σ
    let φ₀ := pointMapOfPushforward ι₀ hι₀ hfin₀ (normFormulaAlong_of_elliptic ι₀ hfin₀)
    let φ₁ := pointMapOfPushforward (ι₁) hι₁ hfin₁ (normFormulaAlong_of_elliptic (ι₁) hfin₁)
    ∀ P, φ₁ (σE P) = σE' (φ₀ P) := by
  intro hι₁ hfin₁ σE σE' φ₀ φ₁
  have hgBC₀ :=
    kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub ι₀ hι₀ hfin₀ (normFormulaAlong_of_elliptic ι₀
      hfin₀)
  have hgBC₁ :=
    kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub (ι₁) hι₁ hfin₁ (normFormulaAlong_of_elliptic ι₁
      hfin₁)
  let g₀ := kw_fdn2_qephod_hend7_geomMorphBC ι₀ hι₀
  let g₁ := kw_fdn2_qephod_hend7_geomMorphBC (ι₁) hι₁
  have hχE_ord_pos : ∀ {x y : F} (hP : (E₀⁄F).toAffine.Nonsingular x y)
      (hσP : (E₀⁄F').toAffine.Nonsingular (algebraMap F F' x) (algebraMap F F' y))
      (h : (E₀⁄F).toAffine.FunctionField) (hh : h ≠ 0),
      0 < (placeOfEquation hσP.left).ord (χE h) ↔
        0 < (placeOfEquation hP.left).ord h := by
    intro x y hP hσP h hh
    have hχEh_ne : χE h ≠ 0 :=
      (map_ne_zero_iff _ (kw_functionFieldMapAlongGeneral E₀ F F').injective).mpr hh
    have hVSR := kw_surge_hgf4_χE_VSR_compat E₀ F F' hP hσP
    constructor <;> intro hpos
    · have hχEh_mem : χE h ∈ (placeOfEquation hσP.left).toValuationSubring :=
        AlgebraicCurve.Place.mem_of_ord_nonneg (placeOfEquation hσP.left) hχEh_ne hpos.le
      have hh_mem : h ∈ (placeOfEquation hP.left).toValuationSubring := (hVSR h).mp hχEh_mem
      rw [← Place.mem_maximalIdeal_iff_ord_pos _ hh hh_mem,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hinv_mem := kw_surge_hgf4_place_inv_mem_of_isUnit _ hu
      have hχEinv_mem : χE h⁻¹ ∈ (placeOfEquation hσP.left).toValuationSubring :=
        (hVSR h⁻¹).mpr hinv_mem
      rw [map_inv₀] at hχEinv_mem
      have hχEh_unit : IsUnit
          (⟨χE h, hχEh_mem⟩ : (placeOfEquation hσP.left).toValuationSubring) :=
        isUnit_iff_exists_inv.mpr ⟨⟨(χE h)⁻¹, hχEinv_mem⟩,
          Subtype.ext (mul_inv_cancel₀ hχEh_ne)⟩
      exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp
        ((Place.mem_maximalIdeal_iff_ord_pos _ hχEh_ne hχEh_mem).mpr hpos))) hχEh_unit
    · have hh_mem : h ∈ (placeOfEquation hP.left).toValuationSubring :=
        AlgebraicCurve.Place.mem_of_ord_nonneg (placeOfEquation hP.left) hh hpos.le
      have hχEh_mem : χE h ∈ (placeOfEquation hσP.left).toValuationSubring :=
        (hVSR h).mpr hh_mem
      rw [← Place.mem_maximalIdeal_iff_ord_pos _ hχEh_ne hχEh_mem,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hinv_mem := kw_surge_hgf4_place_inv_mem_of_isUnit _ hu
      have hh_inv_mem : h⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring := by
        rw [← map_inv₀] at hinv_mem; exact (hVSR h⁻¹).mp hinv_mem
      have hh_unit : IsUnit
          (⟨h, hh_mem⟩ : (placeOfEquation hP.left).toValuationSubring) :=
        isUnit_iff_exists_inv.mpr ⟨⟨h⁻¹, hh_inv_mem⟩, Subtype.ext (mul_inv_cancel₀ hh)⟩
      exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp
        ((Place.mem_maximalIdeal_iff_ord_pos _ hh hh_mem).mpr hpos))) hh_unit
  have hgBC_nat_affine : ∀ {x y : F} (hP : (E₀⁄F).toAffine.Nonsingular x y),
      g₁ (σE (.some x y hP)) = σE' (g₀ (.some x y hP)) := by
    intro x y hP
    have hσP : (E₀⁄F').toAffine.Nonsingular (algebraMap F F' x) (algebraMap F F' y) :=
      kw_surge_hgf4_toAffine_map_eq F F' E₀ ▸
        (((E₀⁄F).toAffine.map_nonsingular (algebraMap F F').injective x y).mpr hP)
    have hσE_some : σE (.some x y hP)
        = .some (algebraMap F F' x) (algebraMap F F' y) hσP := by
      have h := Point.map_some (W' := E₀.toAffine) (F := F) (K := F') σ hP
      rw [show σE (.some x y hP) = Point.map (W' := E₀.toAffine) σ (.some x y hP) from rfl, h]
      congr 1 <;> exact hσ _
    refine placeOfPoint_injective ?_
    rw [← kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC (ι₁) hι₁ (σE (.some x y hP)),
      hσE_some, placeOfPoint_some]
    have hseam₀ : (placeOfEquation hP.left).restrictAlong ι₀ hι₀
        = placeOfPoint (g₀ (.some x y hP)) := by
      rw [← placeOfPoint_some hP,
        kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι₀ hι₀]
    have hι₁X : (ι₁) (polyToFunctionField (E₀'⁄F').toAffine X)
        = χE (ι₀ (polyToFunctionField (E₀'⁄F).toAffine X)) := by
      rw [← kw_functionFieldMapAlongGeneral_polyToFunctionField_X E₀' F F']
      exact kw_surge_hgf4_bcIota₁_compat E₀ E₀' F F' ι₀ _
    have hι₁Y : (ι₁) (yGen (E₀'⁄F').toAffine)
        = χE (ι₀ (yGen (E₀'⁄F).toAffine)) := by
      rw [← kw_functionFieldMapAlongGeneral_yGen E₀' F F']
      exact kw_surge_hgf4_bcIota₁_compat E₀ E₀' F F' ι₀ _
    have hχE_const : ∀ c : F, χE (algebraMap F (E₀⁄F).toAffine.FunctionField c)
        = algebraMap F' (E₀⁄F').toAffine.FunctionField (algebraMap F F' c) := fun c => by
      rw [AlgHom.commutes,
        IsScalarTower.algebraMap_apply F F' (E₀⁄F').toAffine.FunctionField]
    rcases hQ₀_case : g₀ (.some x y hP) with _ | ⟨qx, qy, hQ₀ns⟩
    · rw [show placeOfPoint (σE' (.zero : (E₀'⁄F).toAffine.Point))
          = (InfinitePlace.place : Place F' (E₀'⁄F').toAffine.FunctionField) from by
        rw [show σE' (.zero : (E₀'⁄F).toAffine.Point)
            = (.zero : (E₀'⁄F').toAffine.Point) from map_zero σE', placeOfPoint_zero]]
      refine AbstractSeam.restrictAlong_eq_infinitePlace (ι₁) hι₁ rfl _ ?_
      rw [hι₁X]
      intro hmem
      have hι₀X_mem : ι₀ (polyToFunctionField (E₀'⁄F).toAffine X)
          ∈ (placeOfEquation hP.left).toValuationSubring :=
        (kw_surge_hgf4_χE_VSR_compat E₀ F F' hP hσP _).mp hmem
      have hX_res : polyToFunctionField (E₀'⁄F).toAffine X
          ∈ ((placeOfEquation hP.left).restrictAlong ι₀ hι₀).toValuationSubring :=
        (Place.mem_restrictAlong_iff ι₀ hι₀ _ _).mpr hι₀X_mem
      rw [hseam₀, hQ₀_case, placeOfPoint_zero] at hX_res
      exact InfinitePlace.not_isFinitePlace (isFinitePlace_of_mem _ hX_res)
    · have hσQ : (E₀'⁄F').toAffine.Nonsingular (algebraMap F F' qx) (algebraMap F F' qy) :=
        kw_surge_hgf4_toAffine_map_eq F F' E₀' ▸
          (((E₀'⁄F).toAffine.map_nonsingular (algebraMap F F').injective qx qy).mpr hQ₀ns)
      have hσE'_some : σE' (.some qx qy hQ₀ns)
          = .some (algebraMap F F' qx) (algebraMap F F' qy) hσQ := by
        have h := Point.map_some (W' := E₀'.toAffine) (F := F) (K := F') σ hQ₀ns
        rw [show σE' (.some qx qy hQ₀ns)
            = Point.map (W' := E₀'.toAffine) σ (.some qx qy hQ₀ns) from rfl, h]
        congr 1 <;> exact hσ _
      rw [hσE'_some, placeOfPoint_some]
      have hseam₀' : (placeOfEquation hP.left).restrictAlong ι₀ hι₀
          = placeOfEquation hQ₀ns.left := by rw [hseam₀, hQ₀_case, placeOfPoint_some]
      have hbrX : algebraMap (E₀'⁄F).toAffine.CoordinateRing (E₀'⁄F).toAffine.FunctionField
          (CoordinateRing.XClass (E₀'⁄F).toAffine qx)
          = polyToFunctionField (E₀'⁄F).toAffine X - algebraMap F _ qx :=
        AbstractSeam.map_XClass (V := (E₀'⁄F).toAffine) (W := (E₀'⁄F).toAffine)
          (AlgHom.id F (E₀'⁄F).toAffine.FunctionField) rfl qx
      have hbrY : algebraMap (E₀'⁄F).toAffine.CoordinateRing (E₀'⁄F).toAffine.FunctionField
          (CoordinateRing.YClass (E₀'⁄F).toAffine (C qy))
          = yGen (E₀'⁄F).toAffine - algebraMap F _ qy :=
        AbstractSeam.map_YClass (V := (E₀'⁄F).toAffine) (W := (E₀'⁄F).toAffine)
          (AlgHom.id F (E₀'⁄F).toAffine.FunctionField) rfl qy
      have hι₀X_ne : ι₀ (polyToFunctionField (E₀'⁄F).toAffine X)
          - algebraMap F _ qx ≠ 0 := by
        rw [← ι₀.commutes, ← map_sub, ← hbrX]
        exact fun h => (CoordinateRing.XClass_ne_zero qx)
          ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp (ι₀.injective
            (h.trans (map_zero ι₀).symm)))
      have hι₀Y_ne : ι₀ (yGen (E₀'⁄F).toAffine) - algebraMap F _ qy ≠ 0 := by
        rw [← ι₀.commutes, ← map_sub, ← hbrY]
        exact fun h => (CoordinateRing.YClass_ne_zero (C qy))
          ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp (ι₀.injective
            (h.trans (map_zero ι₀).symm)))
      have hram_pos : 0 < Place.ramificationIndexAlong ι₀ (placeOfEquation hP.left) :=
        Place.ramificationIndexAlong_pos ι₀ hι₀ (placeOfEquation hP.left)
      have hdxF : 0 < (placeOfEquation hP.left).ord
          (ι₀ (polyToFunctionField (E₀'⁄F).toAffine X) - algebraMap F _ qx) := by
        rw [← ι₀.commutes, ← map_sub, ← hbrX,
          Place.ord_restrictAlong ι₀ hι₀, hseam₀']
        have hQord : 0 < (placeOfEquation hQ₀ns.left).ord (algebraMap _ _
            (CoordinateRing.XClass (E₀'⁄F).toAffine qx)) :=
          (ord_placeOfEquation_pos_iff hQ₀ns.left (CoordinateRing.XClass_ne_zero _)).mpr
            (Ideal.subset_span (Set.mem_insert _ _))
        positivity
      have hdyF : 0 < (placeOfEquation hP.left).ord
          (ι₀ (yGen (E₀'⁄F).toAffine) - algebraMap F _ qy) := by
        rw [← ι₀.commutes, ← map_sub, ← hbrY,
          Place.ord_restrictAlong ι₀ hι₀, hseam₀']
        have hQord : 0 < (placeOfEquation hQ₀ns.left).ord (algebraMap _ _
            (CoordinateRing.YClass (E₀'⁄F).toAffine (C qy))) :=
          (ord_placeOfEquation_pos_iff hQ₀ns.left (CoordinateRing.YClass_ne_zero _)).mpr
            (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
        positivity
      refine AbstractSeam.restrictAlong_placeOfEquation (ι₁) hι₁ rfl rfl
        hσP.left hσQ.left ?_ ?_ ?_
      · rw [hι₁X]
        refine (kw_surge_hgf4_χE_VSR_compat E₀ F F' hP hσP _).mpr ?_
        rw [← Place.mem_restrictAlong_iff ι₀ hι₀, hseam₀']
        exact isFinitePlace_placeOfEquation hQ₀ns.left _
      · rw [hι₁X, ← hχE_const qx, ← map_sub]
        exact (hχE_ord_pos hP hσP _ hι₀X_ne).mpr hdxF
      · rw [hι₁Y, ← hχE_const qy, ← map_sub]
        exact (hχE_ord_pos hP hσP _ hι₀Y_ne).mpr hdyF
  let δ : (E₀⁄F).toAffine.Point →+ (E₀'⁄F').toAffine.Point :=
    (φ₁.comp σE) - (σE'.comp φ₀)
  have hδ_affine : ∀ {x y : F} (hP : (E₀⁄F).toAffine.Nonsingular x y),
      δ (.some x y hP) = σE' (g₀ 0) - g₁ 0 := by
    intro x y hP
    change φ₁ (σE (.some x y hP)) - σE' (φ₀ (.some x y hP)) = _
    have h1 : φ₁ (σE (.some x y hP)) = g₁ (σE (.some x y hP)) - g₁ 0 := hgBC₁ _
    have h0 : φ₀ (.some x y hP) = g₀ (.some x y hP) - g₀ 0 := hgBC₀ _
    rw [h1, h0, map_sub, hgBC_nat_affine hP]
    abel
  have hC_zero : σE' (g₀ 0) - g₁ 0 = 0 := by
    obtain ⟨e3⟩ :=
      WeierstrassCurve.nonempty_pointTorsionBy_zmod (W := (E₀⁄F)) (n := 3) (by omega)
    let P₀ : (E₀⁄F).toAffine.Point := (e3.symm (fun _ => 1) : _)
    have hP₀_3 : (3 : ℤ) • P₀ = 0 := by
      have := (e3.symm (fun _ => 1)).2
      simp [P₀]
    have hP₀_ne : P₀ ≠ 0 := by
      intro h
      have heq : e3.symm (fun _ => 1) = 0 :=
        Subtype.ext (show (e3.symm (fun _ => 1) : (E₀⁄F).toAffine.Point) = 0 from h)
      have hfun : (fun _ => (1 : ZMod 3)) = (0 : Fin 2 → ZMod 3) := by
        have := congrArg e3 heq
        rwa [e3.apply_symm_apply, map_zero] at this
      exact one_ne_zero (congrFun hfun 0)
    have h2P₀_ne : (2 : ℤ) • P₀ ≠ 0 := by
      intro h2
      have : (3 : ℤ) • P₀ - (2 : ℤ) • P₀ = 0 := by rw [hP₀_3, h2, sub_zero]
      have hP₀_eq : P₀ = 0 := by
        have : ((3 : ℤ) - 2) • P₀ = 0 := by rw [sub_smul]; exact this
        simpa using this
      exact hP₀_ne hP₀_eq
    rcases hP₀_case : P₀ with _ | ⟨px, py, hpP⟩
    · exact (hP₀_ne hP₀_case).elim
    rcases h2P₀_case : (2 : ℤ) • P₀ with _ | ⟨qx, qy, hqQ⟩
    · exact (h2P₀_ne h2P₀_case).elim
    have h2C : (2 : ℤ) • (σE' (g₀ 0) - g₁ 0) = σE' (g₀ 0) - g₁ 0 := by
      calc (2 : ℤ) • (σE' (g₀ 0) - g₁ 0)
          = (2 : ℤ) • δ (.some px py hpP) := by rw [hδ_affine hpP]
        _ = δ ((2 : ℤ) • (.some px py hpP : (E₀⁄F).toAffine.Point)) :=
            (map_zsmul δ 2 _).symm
        _ = δ ((2 : ℤ) • P₀) := by rw [hP₀_case]
        _ = δ (.some qx qy hqQ) := by rw [h2P₀_case]
        _ = σE' (g₀ 0) - g₁ 0 := hδ_affine hqQ
    have hC' : ((2 : ℤ) - 1) • (σE' (g₀ 0) - g₁ 0) = 0 := by
      rw [sub_smul, one_smul, h2C, sub_self]
    simpa using hC'
  intro P
  have hδP : δ P = 0 := by
    rcases P with _ | ⟨x, y, hP⟩
    · exact map_zero δ
    · rw [hδ_affine hP, hC_zero]
  exact sub_eq_zero.mp hδP

end Naturality
end BetweenCurvesTensor

end ModularCurve
end
end

section


section

open WeierstrassCurve  WeierstrassCurve.Affine  Polynomial AlgebraicCurve
open scoped TensorProduct Polynomial  Polynomial.Bivariate

namespace ModularCurve

universe u

attribute [local instance] Classical.propDecidable
section KerTransportMint

def KwD5BetweenCurvesKerTransportAlongEmbed : Prop :=
  ∀ (R₀ : Type u) [Field R₀] (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (F₁ : Type u) [Field F₁] [Algebra R₀ F₁] [DecidableEq F₁] [IsAlgClosed F₁] [CharZero F₁]
    (F₂ : Type u) [Field F₂] [Algebra R₀ F₂] [DecidableEq F₂] [IsAlgClosed F₂] [CharZero F₂]
    [Algebra F₁ F₂] [IsScalarTower R₀ F₁ F₂]
    [(E₀⁄F₁).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀⁄F₁).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀⁄F₁).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (E₀⁄F₁).toAffine] [(E₀'⁄F₁).IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀'⁄F₁).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀'⁄F₁).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (E₀'⁄F₁).toAffine] [(E₀⁄F₂).IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀⁄F₂).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀⁄F₂).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (E₀⁄F₂).toAffine] [(E₀'⁄F₂).IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀'⁄F₂).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀'⁄F₂).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (E₀'⁄F₂).toAffine]
    (ι₁ : (E₀'⁄F₁).toAffine.FunctionField →ₐ[F₁] (E₀⁄F₁).toAffine.FunctionField)
    (hι₁ : ι₁.toRingHom.IsIntegral) (hfin₁ : FiniteAlong F₁ ι₁)
    (ι₂ : (E₀'⁄F₂).toAffine.FunctionField →ₐ[F₂] (E₀⁄F₂).toAffine.FunctionField)
    (hι₂ : ι₂.toRingHom.IsIntegral) (hfin₂ : FiniteAlong F₂ ι₂)
    (_hχ : ∀ x : (E₀'⁄F₁).toAffine.FunctionField,
      ι₂ (kw_functionFieldMapAlongGeneralNoAC E₀' F₁ F₂ x)
        = kw_functionFieldMapAlongGeneralNoAC E₀ F₁ F₂ (ι₁ x))
    (N : ℕ) [NeZero N],
    IsAddCyclic (AddMonoidHom.ker
      (pointMapOfPushforward ι₂ hι₂ hfin₂ (normFormulaAlong_of_elliptic ι₂ hfin₂))) →
    Nat.card (AddMonoidHom.ker
      (pointMapOfPushforward ι₂ hι₂ hfin₂ (normFormulaAlong_of_elliptic ι₂ hfin₂))) = N →
    IsAddCyclic (AddMonoidHom.ker
      (pointMapOfPushforward ι₁ hι₁ hfin₁ (normFormulaAlong_of_elliptic ι₁ hfin₁))) ∧
    Nat.card (AddMonoidHom.ker
      (pointMapOfPushforward ι₁ hι₁ hfin₁ (normFormulaAlong_of_elliptic ι₁ hfin₁))) = N
end KerTransportMint
end ModularCurve
end

section


section

open WeierstrassCurve  WeierstrassCurve.Affine  Polynomial AlgebraicCurve

open TensorProduct Polynomial  Polynomial.Bivariate

namespace ModularCurve

attribute [local instance] Classical.propDecidable
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

theorem kw_surgehgf4_hfgkd_ktd_chiNoAC_eq_chiGeneral
    {R₀ : Type u} [Field R₀] (W : WeierstrassCurve R₀) [W.IsElliptic]
    (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
    [Algebra F F'] [IsScalarTower R₀ F F']
    [(W⁄F).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (W⁄F).toAffine] [(W⁄F').IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F').toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F').toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (W⁄F').toAffine] :
    kw_functionFieldMapAlongGeneralNoAC W F F'
      = kw_functionFieldMapAlongGeneral W F F' := by
  refine kw_functionField_algHom_ext ?_ ?_
  · rw [kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X,
      kw_functionFieldMapAlongGeneral_polyToFunctionField_X]
  · rw [kw_functionFieldMapAlongGeneralNoAC_yGen, kw_functionFieldMapAlongGeneral_yGen]

theorem kw_surgehgf4_hfgkd_ktd_kerTransport_proved :
    KwD5BetweenCurvesKerTransportAlongEmbed.{u} := by
  intro R₀ _ E₀ E₀' _ _ F₁ _ _ _ _ _ F₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ι₁ hι₁ hfin₁ ι₂ hι₂ hfin₂ hχ N _ hcyc₂ hcard₂
  have : IsDomain ((E₀⁄F₁).toAffine.FunctionField ⊗[F₁] F₂) :=
    kw_functionFieldTensorIsDomain_dischargeGeneral E₀ F₁ F₂
  have : IsDomain ((E₀'⁄F₁).toAffine.FunctionField ⊗[F₁] F₂) :=
    kw_functionFieldTensorIsDomain_dischargeGeneral E₀' F₁ F₂
  have hχE₀ := kw_surgehgf4_hfgkd_ktd_chiNoAC_eq_chiGeneral E₀ F₁ F₂
  have hχE₀' := kw_surgehgf4_hfgkd_ktd_chiNoAC_eq_chiGeneral E₀' F₁ F₂
  have hχG : ∀ x, ι₂ (kw_functionFieldMapAlongGeneral E₀' F₁ F₂ x)
      = kw_functionFieldMapAlongGeneral E₀ F₁ F₂ (ι₁ x) := by
    intro x; rw [← hχE₀', ← hχE₀]; exact hχ x
  have heq : ι₂ = kw_surge_hgf4_bcIota₁ E₀ E₀' F₁ F₂ ι₁ := by
    refine kw_functionField_algHom_ext ?_ ?_
    · rw [show polyToFunctionField (E₀'⁄F₂).toAffine X
            = kw_functionFieldMapAlongGeneral E₀' F₁ F₂
                (polyToFunctionField (E₀'⁄F₁).toAffine X) from
          (kw_functionFieldMapAlongGeneral_polyToFunctionField_X E₀' F₁ F₂).symm,
        hχG, kw_surge_hgf4_bcIota₁_compat E₀ E₀' F₁ F₂ ι₁]
    · rw [show yGen (E₀'⁄F₂).toAffine
            = kw_functionFieldMapAlongGeneral E₀' F₁ F₂ (yGen (E₀'⁄F₁).toAffine) from
          (kw_functionFieldMapAlongGeneral_yGen E₀' F₁ F₂).symm,
        hχG, kw_surge_hgf4_bcIota₁_compat E₀ E₀' F₁ F₂ ι₁]
  subst heq
  clear hχ hχG hχE₀ hχE₀'
  let φ₁ := pointMapOfPushforward ι₁ hι₁ hfin₁ (normFormulaAlong_of_elliptic ι₁ hfin₁)
  let φ₂ := pointMapOfPushforward _ hι₂ hfin₂ (normFormulaAlong_of_elliptic _ hfin₂)
  have hD := kw_surge_hgf4_bcIota₁_finrankAlong E₀ E₀' F₁ F₂ ι₁ hfin₁
  have hker₁ : Nat.card (AddMonoidHom.ker φ₁) = N := by
    rw [show φ₁ = _ from rfl,
      kw_fdn2_qephod_hend7_pmopKerCard_proved F₁ (E₀⁄F₁).toAffine (E₀'⁄F₁).toAffine
        ι₁ hι₁ hfin₁, ← hD,
      ← kw_fdn2_qephod_hend7_pmopKerCard_proved F₂ (E₀⁄F₂).toAffine (E₀'⁄F₂).toAffine
        _ hι₂ hfin₂]
    exact hcard₂
  let σ : F₁ →ₐ[R₀] F₂ := IsScalarTower.toAlgHom R₀ F₁ F₂
  let σE : (E₀⁄F₁).toAffine.Point →+ (E₀⁄F₂).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := E₀.toAffine) σ
  let σE' : (E₀'⁄F₁).toAffine.Point →+ (E₀'⁄F₂).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := E₀'.toAffine) σ
  have hσE_inj : Function.Injective σE :=
    WeierstrassCurve.Affine.Point.map_injective (W' := E₀.toAffine) σ
  have hnat : ∀ P, φ₂ (σE P) = σE' (φ₁ P) :=
    kw_surge_hgf4_pmop_naturality E₀ E₀' F₁ F₂ ι₁ hι₁ hfin₁ σ (fun _ => rfl)
  have hker_sub : ∀ P ∈ AddMonoidHom.ker φ₁, σE P ∈ AddMonoidHom.ker φ₂ := by
    intro P hP
    rw [AddMonoidHom.mem_ker] at hP ⊢
    rw [hnat P, hP, map_zero]
  let σE_ker : (AddMonoidHom.ker φ₁) →+ (AddMonoidHom.ker φ₂) :=
    { toFun := fun ⟨P, hP⟩ => ⟨σE P, hker_sub P hP⟩
      map_zero' := Subtype.ext (map_zero σE)
      map_add' := fun ⟨P, _⟩ ⟨Q, _⟩ => Subtype.ext (map_add σE P Q) }
  have hσE_ker_inj : Function.Injective σE_ker := fun ⟨P, _⟩ ⟨Q, _⟩ hPQ =>
    Subtype.ext (hσE_inj (Subtype.ext_iff.mp hPQ))
  have hcard_eq : Nat.card (AddMonoidHom.ker φ₁) = Nat.card (AddMonoidHom.ker φ₂) := by
    rw [hker₁, hcard₂]
  have hfin_ker₁ : Finite (AddMonoidHom.ker φ₁) :=
    Nat.finite_of_card_ne_zero (hker₁ ▸ (NeZero.ne N))
  have hfin_ker₂ : Finite (AddMonoidHom.ker φ₂) :=
    Nat.finite_of_card_ne_zero (hcard₂ ▸ (NeZero.ne N))
  have hσE_ker_bij : Function.Bijective σE_ker :=
    (Nat.bijective_iff_injective_and_card _).mpr ⟨hσE_ker_inj, hcard_eq⟩
  let e : (AddMonoidHom.ker φ₁) ≃+ (AddMonoidHom.ker φ₂) :=
    AddEquiv.ofBijective σE_ker hσE_ker_bij
  have hcyc₁ : IsAddCyclic (AddMonoidHom.ker φ₁) := by
    obtain ⟨⟨g₂, hg₂⟩⟩ := hcyc₂
    exact ⟨⟨e.symm g₂, fun y => by
      obtain ⟨k, hk⟩ := hg₂ (e y)
      exact ⟨k, e.injective (by rw [map_zsmul, e.apply_symm_apply]; exact hk)⟩⟩⟩
  exact ⟨hcyc₁, hker₁⟩

end ModularCurve
end
end

universe u_kt in
theorem kerTransport_s17 :
    ModularCurve.KwD5BetweenCurvesKerTransportAlongEmbed.{u_kt} :=
      ModularCurve.kw_surgehgf4_hfgkd_ktd_kerTransport_proved.{u_kt}

universe u_sol in
open WeierstrassCurve AlgebraicCurve WeierstrassCurve.Affine in
theorem solution
    (R₀ : Type u_sol) [Field R₀] (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (F₁ : Type u_sol) [Field F₁] [Algebra R₀ F₁] [DecidableEq F₁] [IsAlgClosed F₁] [CharZero F₁]
    (F₂ : Type u_sol) [Field F₂] [Algebra R₀ F₂] [DecidableEq F₂] [IsAlgClosed F₂] [CharZero F₂]
    [Algebra F₁ F₂] [IsScalarTower R₀ F₁ F₂]
    [(E₀.baseChange F₁).IsElliptic] [(E₀'.baseChange F₁).IsElliptic]
    [(E₀.baseChange F₂).IsElliptic] [(E₀'.baseChange F₂).IsElliptic]
    [GenusOnePlaceGate (E₀.baseChange F₁).toAffine]
    [GenusOnePlaceGate.IsCentred (E₀.baseChange F₁).toAffine]
    [AbelTheorem (E₀.baseChange F₁).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F₁).toAffine]
    [GenusOnePlaceGate.IsCentred (E₀'.baseChange F₁).toAffine]
    [AbelTheorem (E₀'.baseChange F₁).toAffine]
    [GenusOnePlaceGate (E₀.baseChange F₂).toAffine]
    [GenusOnePlaceGate.IsCentred (E₀.baseChange F₂).toAffine]
    [AbelTheorem (E₀.baseChange F₂).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F₂).toAffine]
    [GenusOnePlaceGate.IsCentred (E₀'.baseChange F₂).toAffine]
    [AbelTheorem (E₀'.baseChange F₂).toAffine]
    (χ : (E₀.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀.baseChange F₂).toAffine.FunctionField)
    (hχX : χ (polyToFunctionField (E₀.baseChange F₁).toAffine Polynomial.X)
      = polyToFunctionField (E₀.baseChange F₂).toAffine Polynomial.X)
    (hχY : χ (yCoord (E₀.baseChange F₁).toAffine) = yCoord (E₀.baseChange F₂).toAffine)
    (χ' : (E₀'.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀'.baseChange
      F₂).toAffine.FunctionField)
    (hχ'X : χ' (polyToFunctionField (E₀'.baseChange F₁).toAffine Polynomial.X)
      = polyToFunctionField (E₀'.baseChange F₂).toAffine Polynomial.X)
    (hχ'Y : χ' (yCoord (E₀'.baseChange F₁).toAffine) = yCoord (E₀'.baseChange F₂).toAffine)
    (ι₁ : (E₀'.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀.baseChange
      F₁).toAffine.FunctionField)
    (hι₁ : ι₁.toRingHom.IsIntegral) (hfin₁ : FiniteAlong F₁ ι₁) (hN₁ : NormFormulaAlong F₁ ι₁ hfin₁)
    (ι₂ : (E₀'.baseChange F₂).toAffine.FunctionField →ₐ[F₂] (E₀.baseChange
      F₂).toAffine.FunctionField)
    (hι₂ : ι₂.toRingHom.IsIntegral) (hfin₂ : FiniteAlong F₂ ι₂) (hN₂ : NormFormulaAlong F₂ ι₂ hfin₂)
    (hcompat : ∀ x, ι₂ (χ' x) = χ (ι₁ x))
    (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker)
    (hcard : Nat.card (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker = N) :
    IsAddCyclic (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker ∧
      Nat.card (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker = N := by
  have hχE : χ = ModularCurve.kw_functionFieldMapAlongGeneralNoAC E₀ F₁ F₂ := by
    refine WeierstrassCurve.Affine.kw_functionField_algHom_ext ?_ ?_
    · rw [hχX, ModularCurve.kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X]
    · rw [ModularCurve.kw_functionFieldMapAlongGeneralNoAC_yGen]; exact hχY
  have hχE' : χ' = ModularCurve.kw_functionFieldMapAlongGeneralNoAC E₀' F₁ F₂ := by
    refine WeierstrassCurve.Affine.kw_functionField_algHom_ext ?_ ?_
    · rw [hχ'X, ModularCurve.kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X]
    · rw [ModularCurve.kw_functionFieldMapAlongGeneralNoAC_yGen]; exact hχ'Y
  subst hχE; subst hχE'
  exact kerTransport_s17.{u_sol} R₀ E₀ E₀' F₁ F₂ ι₁ hι₁ hfin₁ ι₂ hι₂ hfin₂ hcompat N hcyc hcard

end
end
end
end
end
end
end
end

end privateSection

public section publicSection


open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u
theorem WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom
    (R₀ : Type u) [Field R₀] (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (F₁ : Type u) [Field F₁] [Algebra R₀ F₁] [DecidableEq F₁] [IsAlgClosed F₁] [CharZero F₁]
    (F₂ : Type u) [Field F₂] [Algebra R₀ F₂] [DecidableEq F₂] [IsAlgClosed F₂] [CharZero F₂]
    [Algebra F₁ F₂] [IsScalarTower R₀ F₁ F₂]
    [(E₀.baseChange F₁).IsElliptic] [(E₀'.baseChange F₁).IsElliptic]
    [(E₀.baseChange F₂).IsElliptic] [(E₀'.baseChange F₂).IsElliptic]
    [GenusOnePlaceGate (E₀.baseChange F₁).toAffine]
    [GenusOnePlaceGate.IsCentred (E₀.baseChange F₁).toAffine]
    [AbelTheorem (E₀.baseChange F₁).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F₁).toAffine]
    [GenusOnePlaceGate.IsCentred (E₀'.baseChange F₁).toAffine]
    [AbelTheorem (E₀'.baseChange F₁).toAffine]
    [GenusOnePlaceGate (E₀.baseChange F₂).toAffine]
    [GenusOnePlaceGate.IsCentred (E₀.baseChange F₂).toAffine]
    [AbelTheorem (E₀.baseChange F₂).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F₂).toAffine]
    [GenusOnePlaceGate.IsCentred (E₀'.baseChange F₂).toAffine]
    [AbelTheorem (E₀'.baseChange F₂).toAffine]
    (χ : (E₀.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀.baseChange F₂).toAffine.FunctionField)
    (hχX : χ (polyToFunctionField (E₀.baseChange F₁).toAffine Polynomial.X)
      = polyToFunctionField (E₀.baseChange F₂).toAffine Polynomial.X)
    (hχY : χ (yCoord (E₀.baseChange F₁).toAffine) = yCoord (E₀.baseChange F₂).toAffine)
    (χ' : (E₀'.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀'.baseChange
      F₂).toAffine.FunctionField)
    (hχ'X : χ' (polyToFunctionField (E₀'.baseChange F₁).toAffine Polynomial.X)
      = polyToFunctionField (E₀'.baseChange F₂).toAffine Polynomial.X)
    (hχ'Y : χ' (yCoord (E₀'.baseChange F₁).toAffine) = yCoord (E₀'.baseChange F₂).toAffine)
    (ι₁ : (E₀'.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀.baseChange
      F₁).toAffine.FunctionField)
    (hι₁ : ι₁.toRingHom.IsIntegral) (hfin₁ : FiniteAlong F₁ ι₁) (hN₁ : NormFormulaAlong F₁ ι₁ hfin₁)
    (ι₂ : (E₀'.baseChange F₂).toAffine.FunctionField →ₐ[F₂] (E₀.baseChange
      F₂).toAffine.FunctionField)
    (hι₂ : ι₂.toRingHom.IsIntegral) (hfin₂ : FiniteAlong F₂ ι₂) (hN₂ : NormFormulaAlong F₂ ι₂ hfin₂)
    (hcompat : ∀ x, ι₂ (χ' x) = χ (ι₁ x))
    (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker)
    (hcard : Nat.card (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker = N) :
    IsAddCyclic (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker ∧
      Nat.card (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker = N :=
  solution R₀ E₀ E₀' F₁ F₂ χ hχX hχY χ' hχ'X hχ'Y ι₁ hι₁ hfin₁ hN₁ ι₂ hι₂ hfin₂ hN₂ hcompat N hcyc
    hcard

end publicSection
