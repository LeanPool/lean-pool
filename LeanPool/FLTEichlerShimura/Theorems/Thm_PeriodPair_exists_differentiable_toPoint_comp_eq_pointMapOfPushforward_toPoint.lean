/-
Based on Prove2Me node
PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint
(e5395f79-d46c-5b66-a6aa-c05a04dab723) by Claude (2026-09-05).

Proof based on Prove2Me submission 8fe161dd-bc82-51ec-93f4-d8f706ef4404
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_Isogeny_ConditionalCurrency
public import LeanPool.FLTEichlerShimura.Definitions.Def_PeriodPair_Uniformization
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Homotopy.Lifting
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_inv
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_normFormulaAlong
import LeanPool.FLTEichlerShimura.Theorems.Thm_PeriodPair_isUniformization_toPoint
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong
import LeanPool.FLTEichlerShimura.Definitions.Def_EllipticCurve_FunctionFieldPullback
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum
import LeanPool.FLTEichlerShimura.Theorems.Thm_PeriodPair_discriminant_ne_zero
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add_v2
import LeanPool.FLTEichlerShimura.Definitions.Def_P2M_Util

/-!
# Lifting a function-field map of complex tori to an entire function

Theorem statement: `PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint`
(`e5395f79-d46c-5b66-a6aa-c05a04dab723`), by Claude, 2026-09-05.

Proof: submission `8fe161dd-bc82-51ec-93f4-d8f706ef4404`, by Claude, 2026-09-05 (ACCEPTED); locally
adapted.

Let $L$ and $L'$ be period pairs, and assume $L.g_2^3 - 27\,L.g_3^2 \neq 0$ and $L'.g_2^3 -
27\,L'.g_3^2 \neq 0$, so that the associated Weierstrass curves $y^2 = x^3 - (g_2/4)x - (g_3/4)$
over $\mathbb{C}$ (with $a_1=a_2=a_3=0$) are elliptic. Each of the two affine curves is assumed to
carry: a `GenusOnePlaceGate`, i.e. a bijection between its points and the places of its function
field over $\mathbb{C}$, all of these places having degree $1$; the centring condition, i.e. at the
place attached to a nonsingular point $(x,y)$ the images in the function field of the
coordinate-ring classes of $X$ and of $Y - y$ lie in the nonunits of the valuation subring; and
`AbelTheorem`, i.e. a divisor of degree $0$ is principal exactly when its `divisorSum` vanishes. Let
$\iota$ be a $\mathbb{C}$-algebra homomorphism from the function field of $L'$'s curve to that of
$L$'s curve, with $\iota$ integral as a ring homomorphism, making the target a finite module over
the source along $\iota$ (`FiniteAlong`), and satisfying the pushforward norm formula along $\iota$:
for every nonzero $f$ in the larger field and every divisor $D$ with $D(w) =
\operatorname{ord}_w(f)$ at all places $w$, the pushforward of $D$ satisfies $(\iota_* D)(v) =
\operatorname{ord}_v(\mathrm{N}(f))$ at all places $v$ of the smaller field. The conclusion asserts
the existence of an entire function $F : \mathbb{C} \to \mathbb{C}$ with $F(0)$ in the lattice of
$L'$ such that for every $z \in \mathbb{C}$ one has $\pi_{L'}(F(z)) = \varphi(\pi_L(z))$, where
$\pi_L$ denotes the uniformisation $z \mapsto 0$ for $z$ in the lattice and $z \mapsto (\wp(z),
\wp'(z))$ otherwise, and $\varphi$ is `pointMapOfPushforward`, the additive homomorphism from the
points of $L$'s curve to those of $L'$'s curve obtained by transporting the pushforward along
$\iota$ on degree-zero divisor classes through the two genus-one identifications of points with
$\mathrm{Pic}^0$.

This is the analytic lifting statement for a rational map between complex tori: the induced
homomorphism on points, defined here divisor-theoretically as a pushforward on $\mathrm{Pic}^0$, is
covered by a holomorphic map of the universal covers $\mathbb{C} \to \mathbb{C}$ sending $0$ into
the target lattice. It is used in the passage from such a map to the lattice-theoretic data of a
scaled sublattice of finite index with cyclic quotient.

## Explanation of the source proof

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean

<!-- Generated by add_prove2me_provenance.py -->
-/


section privateSection

set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_OVERLONG_302e4807


noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing.smul_basis_eq_zero \
  slope_of_X_ne slope CoordinateRing map Point.some Point.some.injEq Point.X_eq_iff Nonsingular \
  negAddY Point.zero_def FunctionField Point CoordinateRing.mk addX nonsingular_neg \
  equation_iff_nonsingular Point.some_ne_zero addY Point.add_of_X_ne equation_iff polynomial \
  Point.neg_some pushforwardAlong_single_eq pointMapOfPushforward pointMapOfPushforward_apply \
  IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint \
  deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem \
  pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot \
  hasPrincipalDivisors_functionField natCard_ker_pointMapOfPushforward_eq_finrankAlong \
  polyToFunctionField polyToFunctionField_apply polyToFunctionField_C polyToFunctionField_ne_zero \
  algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "Polynomial \
  P2MW.S_OVERLONG_302e4807.Polynomial \
  IsDedekindDomain \
  P2MW.S_OVERLONG_302e4807.IsDedekindD\
  omain WeierstrassCurve.Affine.CoordinateRing~evalAt \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine.CoordinateRing \
  AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve"
p2m_open_scoped "Polynomial.Bivariate \
  P2MW.S_OVERLONG_302e4807.Polynomial.\
  Bivariate"

variable {F : Type*} [Field F] {W : Affine F}

theorem S13_ofHeightOneSpectrum_injective {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R W.FunctionField] [IsFractionRing R W.FunctionField] [Algebra F R]
    [IsScalarTower F R W.FunctionField] :
    Function.Injective (AlgebraicCurve.Place.ofHeightOneSpectrum (K := F) (R := R) (F :=
      W.FunctionField)) := by
  intro w₁ w₂ h
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := W.FunctionField) ?_
  rw [Valuation.isEquiv_iff_valuationSubring]
  exact congrArg AlgebraicCurve.Place.toValuationSubring h

namespace CoordinateRing
p2m_export "WeierstrassCurve.Affine.CoordinateRing" "smul_basis_eq_zero XYIdeal \
  quotientXYIdealEquiv YClass mk map exists_smul_basis_eq XClass smul_basis_mul_Y isDedekindDomain \
  exists_eq_XYIdeal XYIdeal_isMaximal XYIdeal_ne_bot"
p2m_open "WeierstrassCurve.Affine.CoordinateRing~evalAt"

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

p2m_open "WeierstrassCurve.Affine.CoordinateRing~evalAt \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine.CoordinateRing"

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

theorem placeOfEquation_injective {x₁ y₁ x₂ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h₂ : W.Equation x₂ y₂) (h : placeOfEquation h₁ = placeOfEquation h₂) :
    x₁ = x₂ ∧ y₁ = y₂ :=
  eq_of_XYIdeal_eq h₂
    (congrArg HeightOneSpectrum.asIdeal (S13_ofHeightOneSpectrum_injective h))

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
omit [IsDedekindDomain W.CoordinateRing] [GenusOnePlaceGate.IsCentred W] in
private theorem _root_.WeierstrassCurve.Affine.InfinitePlace.deg_eq_one :
    (place : AlgebraicCurve.Place F W.FunctionField).deg = 1 := by
  classical
  exact
    deg_placeOfPoint (W := W) 0

p2m_export "WeierstrassCurve.Affine.InfinitePlace" "deg_eq_one"

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
theorem placeOfPoint_zero' : placeOfPoint (0 : W.Point) = InfinitePlace.place := by
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
theorem placeOfPoint_surjective (_hΔ : W.Δ ≠ 0) : Function.Surjective (placeOfPoint (W := W)) := by
  classical
  exact
    (pointEquivPlace (W := W)).surjective

omit [DecidableEq F] in
omit [IsDedekindDomain W.CoordinateRing] [GenusOnePlaceGate.IsCentred W] in
theorem placeOfPoint_surjective' : Function.Surjective (placeOfPoint (W := W)) := by
  classical
  exact
    (pointEquivPlace (W := W)).surjective

end CentredGate
end Affine
end WeierstrassCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing.smul_basis_eq_zero \
  slope_of_X_ne slope CoordinateRing map Point.some Point.some.injEq Point.X_eq_iff Nonsingular \
  negAddY Point.zero_def FunctionField Point CoordinateRing.mk addX nonsingular_neg \
  equation_iff_nonsingular Point.some_ne_zero addY Point.add_of_X_ne equation_iff polynomial \
  Point.neg_some pushforwardAlong_single_eq pointMapOfPushforward pointMapOfPushforward_apply \
  IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint \
  deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem \
  pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot \
  hasPrincipalDivisors_functionField natCard_ker_pointMapOfPushforward_eq_finrankAlong \
  polyToFunctionField polyToFunctionField_apply polyToFunctionField_C polyToFunctionField_ne_zero \
  algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve"

scoped instance instHasPrincipalDivisorsFunctionField_s13 {F : Type*} [Field F] [CharZero F]
    {W : Affine F} : HasPrincipalDivisors F W.FunctionField :=
  hasPrincipalDivisors_functionField W

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

namespace IsogenyEndDatum
p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "pointEnd pointEnd_apply pointEnd_eq_of_seam \
  hfin hι mk ι"
p2m_open "WeierstrassCurve.Affine.IsogenyEndDatum"

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]

omit [DecidableEq F] [W.GenusOnePlaceGate] [W.AbelTheorem] in
omit [IsAlgClosed F] [WeierstrassCurve.IsElliptic W] in
private theorem _root_.WeierstrassCurve.Affine.IsogenyEndDatum.normFormulaAlong_auto (D :
  IsogenyEndDatum W) :
    NormFormulaAlong F D.ι D.hfin :=
  normFormulaAlong_of_elliptic D.ι D.hfin

p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "normFormulaAlong_auto"

private def _root_.WeierstrassCurve.Affine.IsogenyEndDatum.pointEnd' (D : IsogenyEndDatum W) :
    AddMonoid.End W.Point := D.pointEnd D.normFormulaAlong_auto

p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "pointEnd'"
omit [IsAlgClosed F] [WeierstrassCurve.IsElliptic W] in
theorem pointEnd_eq_pointEnd' (D : IsogenyEndDatum W) (hN : NormFormulaAlong F D.ι D.hfin) :
    D.pointEnd hN = D.pointEnd' := rfl

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

end IsogenyEndDatum
end Affine
end WeierstrassCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing.smul_basis_eq_zero \
  slope_of_X_ne slope CoordinateRing map Point.some Point.some.injEq Point.X_eq_iff Nonsingular \
  negAddY Point.zero_def FunctionField Point CoordinateRing.mk addX nonsingular_neg \
  equation_iff_nonsingular Point.some_ne_zero addY Point.add_of_X_ne equation_iff polynomial \
  Point.neg_some pushforwardAlong_single_eq pointMapOfPushforward pointMapOfPushforward_apply \
  IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint \
  deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem \
  pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot \
  hasPrincipalDivisors_functionField natCard_ker_pointMapOfPushforward_eq_finrankAlong \
  polyToFunctionField polyToFunctionField_apply polyToFunctionField_C polyToFunctionField_ne_zero \
  algebraMap_smul_basis"
end Affine
end WeierstrassCurve
p2m_open_scoped "WeierstrassCurve WeierstrassCurve.Affine" in
scoped instance WeierstrassCurve.Affine.instHasPrincipalDivisorsFunctionField_s13e2
    {F : Type*} [Field F] [CharZero F] (W : WeierstrassCurve.Affine F) :
    AlgebraicCurve.HasPrincipalDivisors F W.FunctionField :=
  WeierstrassCurve.Affine.hasPrincipalDivisors_functionField W


namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongDegZero Pic0.coe_pushforwardAlongDegZero \
  Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk algebraAlong isScalarTower_along \
  isIntegral_along FiniteAlong NormFormulaAlong finrankAlong Place.ramificationIndexAlong \
  Place.ord_restrictAlong SeparableAlong Place.restrict_fiber_finite Place Place.ext \
  Place.coe_algebraMap HasPrincipalDivisors Pic0 Pic0.mk Place.ofHeightOneSpectrum \
  Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor \
  Place.toValuationSubring Place.evalAt Place.ofHeightOneSpectrum_injective \
  Place.ord_ofHeightOneSpectrum_ne_zero_iff normFormulaAlong"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong ramificationIndexAlong ord_restrictAlong \
  ramificationIndex_pos restrict_fiber_finite ext coe_algebraMap ResidueField deg adicValuation \
  adicValuation_ne_zero ord ord_mul ord_inv ord_unit_smul_zpow exists_unit_mul_zpow \
  ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' algebraMap_mem' \
  toValuationSubring mk mem_of_eval_monic_eq_zero IsRational evalAt algebraMap_evalAt \
  ofHeightOneSpectrum_injective ord_ofHeightOneSpectrum_ne_zero_iff evalAt_ne_zero evalAt_congr \
  ord_algebraMap evalAt_algebraMap evalAt_mul evalAt_inv"
end Place
end AlgebraicCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongDegZero Pic0.coe_pushforwardAlongDegZero \
  Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk algebraAlong isScalarTower_along \
  isIntegral_along FiniteAlong NormFormulaAlong finrankAlong Place.ramificationIndexAlong \
  Place.ord_restrictAlong SeparableAlong Place.restrict_fiber_finite Place Place.ext \
  Place.coe_algebraMap HasPrincipalDivisors Pic0 Pic0.mk Place.ofHeightOneSpectrum \
  Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor \
  Place.toValuationSubring Place.evalAt Place.ofHeightOneSpectrum_injective \
  Place.ord_ofHeightOneSpectrum_ne_zero_iff normFormulaAlong"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong ramificationIndexAlong ord_restrictAlong \
  ramificationIndex_pos restrict_fiber_finite ext coe_algebraMap ResidueField deg adicValuation \
  adicValuation_ne_zero ord ord_mul ord_inv ord_unit_smul_zpow exists_unit_mul_zpow \
  ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' algebraMap_mem' \
  toValuationSubring mk mem_of_eval_monic_eq_zero IsRational evalAt algebraMap_evalAt \
  ofHeightOneSpectrum_injective ord_ofHeightOneSpectrum_ne_zero_iff evalAt_ne_zero evalAt_congr \
  ord_algebraMap evalAt_algebraMap evalAt_mul evalAt_inv"
p2m_open "AlgebraicCurve.Place~ord_nonneg_of_mem~mem_of_ord_nonneg~mem_iff_ord_nonneg"

section MoreSinglePlace
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.isRational_of_deg_eq_one (h : v.deg = 1) :
    v.IsRational := by
  intro x
  have hbot : (⊥ : Subalgebra K v.ResidueField) = ⊤ :=
    Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr h
  have hx : x ∈ (⊥ : Subalgebra K v.ResidueField) := by
    rw [hbot]
    exact Algebra.mem_top
  exact Algebra.mem_bot.mp hx

p2m_export "AlgebraicCurve.Place" "isRational_of_deg_eq_one"

private theorem _root_.AlgebraicCurve.Place.evalAt_div (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring)
    (hg : g ≠ 0) (hg0 : v.ord g = 0) :
    v.evalAt (f / g) = v.evalAt f / v.evalAt g := by
  have hginv : g⁻¹ ∈ v.toValuationSubring :=
    AlgebraicCurve.Place.mem_of_ord_nonneg v (inv_ne_zero hg) (by
      rw [v.ord_inv, hg0]; exact neg_nonneg.mpr le_rfl)
  rw [div_eq_mul_inv, v.evalAt_mul hv hf hginv, v.evalAt_inv hv hg hg0, div_eq_mul_inv]

p2m_export "AlgebraicCurve.Place" "evalAt_div"
end MoreSinglePlace

theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

end Place
end AlgebraicCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing.smul_basis_eq_zero \
  slope_of_X_ne slope CoordinateRing map Point.some Point.some.injEq Point.X_eq_iff Nonsingular \
  negAddY Point.zero_def FunctionField Point CoordinateRing.mk addX nonsingular_neg \
  equation_iff_nonsingular Point.some_ne_zero addY Point.add_of_X_ne equation_iff polynomial \
  Point.neg_some pushforwardAlong_single_eq pointMapOfPushforward pointMapOfPushforward_apply \
  IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint \
  deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem \
  pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot \
  hasPrincipalDivisors_functionField natCard_ker_pointMapOfPushforward_eq_finrankAlong \
  polyToFunctionField polyToFunctionField_apply polyToFunctionField_C polyToFunctionField_ne_zero \
  algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"
p2m_open "WeierstrassCurve.Affine.CoordinateRing~evalAt \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine.CoordinateRing \
  AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve Polynomial \
  P2MW.S_OVERLONG_302e4807.Polynomial"
p2m_open_scoped "Polynomial.Bivariate \
  P2MW.S_OVERLONG_302e4807.Polynomial.\
  Bivariate"

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

section RationalPlaceOfEquation
variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]
  [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [IsDedekindDomain W.CoordinateRing]

theorem isRational_placeOfEquation {r s : F} (hrs : W.Equation r s) :
    (placeOfEquation hrs).IsRational := by
  classical
  apply (placeOfEquation hrs).isRational_of_deg_eq_one
  rw [← placeOfPoint_some (equation_iff_nonsingular.mp hrs)]
  exact GenusOnePlaceGate.deg_eq_one _

end RationalPlaceOfEquation
end Affine
end WeierstrassCurve

namespace ModularCurve
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg\
  " in
open _root_.WeierstrassCurve
  _root_.P2MW.S_OVERLONG_302e4807.WeierstrassCurve
  _root_.WeierstrassCurve.Affine
  _root_.P2MW.S_OVERLONG_302e4807.WeierstrassCurve.Affine
  _root_.P2MW.S_OVERLONG_302e4807.AlgebraicCurve
  in
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
p2m_open "Complex Filter \
  P2MW.S_OVERLONG_302e4807.Filter Set"

p2m_open_scoped "PeriodPair \
  P2MW.S_OVERLONG_302e4807.PeriodPair"

namespace PeriodPair
p2m_export "PeriodPair" "isClosed_lattice derivWeierstrassP_neg weierstrassP_neg lattice \
  weierstrassP_add_coe lattice_eq_span_range_basis ω₁ mk analyticOnNhd_derivWeierstrassP g₃ \
  deriv_weierstrassP ω₂ derivWeierstrassP_add_coe mem_lattice G g₂ analyticOnNhd_weierstrassP \
  weierstrassCurve weierstrassCurve_a₁ weierstrassCurve_a₂ weierstrassCurve_a₃ \
  equation_weierstrassP DiscriminantNeZero toPoint toPoint_of_mem toPoint_zero toPoint_of_notMem \
  IsUniformization jLattice scale_indep scale discriminant_ne_zero isUniformization_toPoint"
p2m_open "PeriodPair"

variable (L : PeriodPair)

private theorem _root_.PeriodPair.kw_discriminantNeZero :
    L.DiscriminantNeZero := L.discriminant_ne_zero

p2m_export "PeriodPair" "kw_discriminantNeZero"

private theorem _root_.PeriodPair.kw_isUniformization :
    L.IsUniformization L.kw_discriminantNeZero :=
  L.isUniformization_toPoint _

p2m_export "PeriodPair" "kw_isUniformization"

private theorem _root_.PeriodPair.kw_toPoint_add (hD : L.DiscriminantNeZero) (z w : ℂ) :
    L.toPoint hD (z + w) = L.toPoint hD z + L.toPoint hD w :=
  (L.isUniformization_toPoint hD).1 z w

p2m_export "PeriodPair" "kw_toPoint_add"

theorem kw_toPoint_surjective (hD : L.DiscriminantNeZero) : Function.Surjective (L.toPoint hD) :=
  (L.isUniformization_toPoint hD).2.1

theorem kw_toPoint_eq_zero_iff (hD : L.DiscriminantNeZero) (z : ℂ) :
    L.toPoint hD z = 0 ↔ z ∈ L.lattice :=
  ⟨(L.isUniformization_toPoint hD).2.2 z, fun hz => L.toPoint_of_mem hD hz⟩

scoped instance kw_instIsElliptic : L.weierstrassCurve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr L.kw_discriminantNeZero.weierstrassCurve_Δ_ne_zero⟩

section Liouville

private theorem _root_.PeriodPair.sub_fract_mem_lattice (z : ℂ) :
    z - ZSpan.fract L.basis z ∈ L.lattice := by
  rw [L.lattice_eq_span_range_basis]
  have h := (ZSpan.fract_eq_fract L.basis (ZSpan.fract L.basis z) z).mp
    (by rw [ZSpan.fract_eq_self.mpr (ZSpan.fract_mem_fundamentalDomain L.basis z)])
  simpa [neg_add_eq_sub] using h

p2m_export "PeriodPair" "sub_fract_mem_lattice"

private theorem _root_.PeriodPair.apply_eq_apply_of_differentiable_of_forall_periodic {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hper : ∀ l ∈ L.lattice, ∀ z, f (z + l) = f z) (z w : ℂ) :
    f z = f w := by
  apply hf.apply_eq_apply_of_bounded
  have hrange : range f ⊆ f '' closure (ZSpan.fundamentalDomain L.basis) := by
    rintro - ⟨u, rfl⟩
    refine ⟨ZSpan.fract L.basis u, subset_closure (ZSpan.fract_mem_fundamentalDomain _ u), ?_⟩
    have h := hper _ (L.sub_fract_mem_lattice u) (ZSpan.fract L.basis u)
    rw [add_sub_cancel] at h
    exact h.symm
  refine Bornology.IsBounded.subset ?_ hrange
  refine (IsCompact.image ?_ hf.continuous).isBounded
  exact Metric.isCompact_of_isClosed_isBounded isClosed_closure
    (ZSpan.fundamentalDomain_isBounded L.basis).closure

p2m_export "PeriodPair" "apply_eq_apply_of_differentiable_of_forall_periodic"
end Liouville

section ToPointLemmas

theorem toPoint_add_mem (h : L.DiscriminantNeZero) (z : ℂ) {l : ℂ} (hl : l ∈ L.lattice) :
    L.toPoint h (z + l) = L.toPoint h z := by
  by_cases hz : z ∈ L.lattice
  · rw [L.toPoint_of_mem h hz, L.toPoint_of_mem h (add_mem hz hl)]
  · have hzl : z + l ∉ L.lattice := fun hmem => hz (by simpa using sub_mem hmem hl)
    rw [L.toPoint_of_notMem h hz, L.toPoint_of_notMem h hzl]
    have hP : ℘[L] (z + l) = ℘[L] z := L.weierstrassP_add_coe z ⟨l, hl⟩
    have hP' : ℘'[L] (z + l) = ℘'[L] z := L.derivWeierstrassP_add_coe z ⟨l, hl⟩
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hP, by rw [hP']⟩

theorem toPoint_neg (h : L.DiscriminantNeZero) (z : ℂ) :
    L.toPoint h (-z) = -L.toPoint h z := by
  by_cases hz : z ∈ L.lattice
  · rw [L.toPoint_of_mem h hz, L.toPoint_of_mem h (neg_mem hz)]; rfl
  · have hnz : -z ∉ L.lattice := fun hmem => hz (by simpa using neg_mem hmem)
    rw [L.toPoint_of_notMem h hz, L.toPoint_of_notMem h hnz,
      WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    refine ⟨L.weierstrassP_neg z, ?_⟩
    rw [L.derivWeierstrassP_neg]
    show -℘'[L] z / 2 = L.weierstrassCurve.toAffine.negY (℘[L] z) (℘'[L] z / 2)
    rw [WeierstrassCurve.Affine.negY, weierstrassCurve_a₁, weierstrassCurve_a₃]
    ring

end ToPointLemmas

section Isogeny

private theorem _root_.PeriodPair.apply_eq_apply_of_continuous_of_mapsTo_lattice {f : ℂ → ℂ}
    (hf : Continuous f)
    (hmem : ∀ z, f z ∈ L.lattice) (z w : ℂ) : f z = f w := by
  refine IsPreconnected.constant_of_mapsTo (isPreconnected_univ) ?_
    hf.continuousOn (fun u _ => hmem u) (mem_univ z) (mem_univ w)
  rw [isDiscrete_iff_discreteTopology]
  exact inferInstanceAs (DiscreteTopology L.lattice)

p2m_export "PeriodPair" "apply_eq_apply_of_continuous_of_mapsTo_lattice"

theorem exists_smul_mem_and_apply_eq_of_forall_sub_mem (L' : PeriodPair) {F : ℂ → ℂ}
    (hF : Differentiable ℂ F)
    (hper : ∀ l ∈ L.lattice, ∀ z, F (z + l) - F z ∈ L'.lattice) :
    ∃ α : ℂ, (∀ l ∈ L.lattice, α * l ∈ L'.lattice) ∧ ∀ z, F z = F 0 + α * z := by
  have hFc : Continuous F := hF.continuous
  have hconst : ∀ l ∈ L.lattice, ∀ z, F (z + l) - F z = F l - F 0 := by
    intro l hl z
    have h := L'.apply_eq_apply_of_continuous_of_mapsTo_lattice
      (f := fun u => F (u + l) - F u)
      ((hFc.comp (continuous_id.add continuous_const)).sub hFc) (hper l hl) z 0
    simpa using h
  have hadd : ∀ z w, F (z + w) = F z + F w - F 0 := by
    intro z w
    have hper' : ∀ l ∈ L.lattice, ∀ u,
        (fun u => F (u + w) - F u) (u + l) = (fun u => F (u + w) - F u) u := by
      intro l hl u
      have h1 := hconst l hl (u + w)
      have h2 := hconst l hl u
      rw [show u + w + l = u + l + w by ring] at h1
      simp only
      linear_combination h1 - h2
    have h := L.apply_eq_apply_of_differentiable_of_forall_periodic
      (f := fun u => F (u + w) - F u)
      ((hF.comp (differentiable_id.add_const w)).sub hF) hper' z 0
    simp only [zero_add] at h
    linear_combination h
  set α : ℂ := deriv F 0 with hα
  have hderiv : ∀ z, deriv F z = α := by
    intro z
    have hfun : (fun w => F (z + w)) = fun w => F w + (F z - F 0) := by
      funext w
      rw [hadd z w]; ring
    have h1 : deriv (fun w => F (z + w)) 0 = deriv F z := by
      rw [deriv_comp_const_add]
      simp
    have h2 : deriv (fun w => F w + (F z - F 0)) 0 = deriv F 0 := by
      rw [deriv_add_const]
    rw [← h1, hfun, h2]
  have haffine : ∀ z, F z = F 0 + α * z := by
    have hG : Differentiable ℂ fun z => F z - α * z :=
      hF.sub (differentiable_id.const_mul α)
    have hG' : ∀ z, deriv (fun z => F z - α * z) z = 0 := by
      intro z
      have hd : HasDerivAt (fun z => F z - α * z) (deriv F z - α * 1) z :=
        (hF z).hasDerivAt.sub ((hasDerivAt_id z).const_mul α)
      rw [hd.deriv, hderiv z]
      ring
    intro z
    have h := is_const_of_deriv_eq_zero hG hG' z 0
    simp only [mul_zero, sub_zero] at h
    linear_combination h
  refine ⟨α, fun l hl => ?_, haffine⟩
  have h := hper l hl 0
  rw [zero_add, haffine l] at h
  simpa using h

end Isogeny

section Scale

variable (α : ℂˣ)

private def mulLeftR (a : ℂ) : ℂ →ₗ[ℝ] ℂ := Algebra.lmul ℝ ℂ a

@[scoped simp] private theorem mulLeftR_apply (a z : ℂ) : mulLeftR a z = a * z := rfl

private theorem mulLeftR_injective {a : ℂ} (ha : a ≠ 0) :
    Function.Injective (mulLeftR a) := fun _ _ h => by
  simpa using mul_left_cancel₀ ha h

private def mulLeftZ (a : ℂ) : ℂ →ₗ[ℤ] ℂ := (mulLeftR a).restrictScalars ℤ

@[scoped simp] private theorem mulLeftZ_apply (a z : ℂ) : mulLeftZ a z = a * z := rfl

private theorem _root_.PeriodPair.scale_lattice :
    (L.scale α).lattice = Submodule.map (mulLeftZ (α : ℂ)) L.lattice := by
  unfold lattice scale
  rw [Submodule.map_span]
  congr 1
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, mulLeftZ_apply]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨L.ω₁, Or.inl rfl, rfl⟩
    · exact ⟨L.ω₂, Or.inr rfl, rfl⟩
  · rintro ⟨w, hw | hw, rfl⟩ <;> simp [hw]

p2m_export "PeriodPair" "scale_lattice"
theorem mem_scale_lattice_iff {z : ℂ} :
    z ∈ (L.scale α).lattice ↔ ∃ l ∈ L.lattice, z = (α : ℂ) * l := by
  rw [scale_lattice, Submodule.mem_map]; simp only [mulLeftZ_apply]; tauto

private def _root_.PeriodPair.scaleLatticeEquiv : L.lattice ≃ₗ[ℤ] (L.scale α).lattice :=
  (Submodule.equivMapOfInjective (mulLeftZ (α : ℂ))
    (fun _ _ h => mul_left_cancel₀ α.ne_zero (by simpa using h)) L.lattice).trans
    (LinearEquiv.ofEq _ _ (L.scale_lattice α).symm)

p2m_export "PeriodPair" "scaleLatticeEquiv"
@[scoped simp] theorem scaleLatticeEquiv_apply (l : L.lattice) :
    ((L.scaleLatticeEquiv α l : (L.scale α).lattice) : ℂ) = (α : ℂ) * (l : ℂ) := rfl

end Scale

section Homogeneity

variable (α : ℂˣ)

theorem G_scale (n : ℕ) : (L.scale α).G n = ((α : ℂ) ^ n)⁻¹ * L.G n := by
  unfold G
  rw [← (L.scaleLatticeEquiv α).toEquiv.tsum_eq]
  simp only [LinearEquiv.coe_toEquiv, scaleLatticeEquiv_apply, mul_pow, mul_inv]
  exact tsum_mul_left

theorem g₂_scale : (L.scale α).g₂ = ((α : ℂ) ^ 4)⁻¹ * L.g₂ := by
  unfold g₂; rw [G_scale]; ring

theorem g₃_scale : (L.scale α).g₃ = ((α : ℂ) ^ 6)⁻¹ * L.g₃ := by
  unfold g₃; rw [G_scale]; ring

theorem discriminant_scale :
    (L.scale α).g₂ ^ 3 - 27 * (L.scale α).g₃ ^ 2
      = ((α : ℂ) ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  rw [g₂_scale, g₃_scale]; ring

theorem g₂_cubed_scale : (L.scale α).g₂ ^ 3 = ((α : ℂ) ^ 12)⁻¹ * L.g₂ ^ 3 := by
  rw [g₂_scale, mul_pow, inv_pow, ← pow_mul]

theorem jLattice_scale : (L.scale α).jLattice = L.jLattice := by
  have hα : ((α : ℂ) ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ α.ne_zero)
  unfold jLattice
  rw [discriminant_scale, g₂_cubed_scale, mul_left_comm (1728 : ℂ), mul_div_mul_left _ _ hα]

theorem discriminantNeZero_scale_iff :
    (L.scale α).DiscriminantNeZero ↔ L.DiscriminantNeZero := by
  unfold DiscriminantNeZero
  rw [discriminant_scale]
  simp only [mul_ne_zero_iff, and_iff_right (inv_ne_zero (pow_ne_zero 12 α.ne_zero))]

end Homogeneity

section LatticeDependence

variable {L L' : PeriodPair}

private def latticeEquivOfEq (h : L.lattice = L'.lattice) : L.lattice ≃ L'.lattice where
  toFun l := ⟨(l : ℂ), h ▸ l.2⟩
  invFun l := ⟨(l : ℂ), h.symm ▸ l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem G_eq_of_lattice_eq (h : L.lattice = L'.lattice) (n : ℕ) : L.G n = L'.G n :=
  (latticeEquivOfEq h).tsum_eq fun l => ((l : ℂ) ^ n)⁻¹

theorem g₂_eq_of_lattice_eq (h : L.lattice = L'.lattice) : L.g₂ = L'.g₂ := by
  unfold g₂; rw [G_eq_of_lattice_eq h]

theorem g₃_eq_of_lattice_eq (h : L.lattice = L'.lattice) : L.g₃ = L'.g₃ := by
  unfold g₃; rw [G_eq_of_lattice_eq h]

theorem jLattice_eq_of_lattice_eq (h : L.lattice = L'.lattice) : L.jLattice = L'.jLattice := by
  unfold jLattice; rw [g₂_eq_of_lattice_eq h, g₃_eq_of_lattice_eq h]

end LatticeDependence

section Gates

theorem gate_scale_mul (α β : ℂˣ) :
    ((L.scale α).scale β).lattice = (L.scale (β * α)).lattice := by
  ext z
  simp only [mem_scale_lattice_iff, Units.val_mul]
  constructor
  · rintro ⟨-, ⟨l, hl, rfl⟩, rfl⟩; exact ⟨l, hl, (mul_assoc _ _ _).symm⟩
  · rintro ⟨l, hl, rfl⟩; exact ⟨(α : ℂ) * l, ⟨l, hl, rfl⟩, mul_assoc _ _ _⟩

end Gates

private theorem _root_.PeriodPair.kw_countable_lattice : (L.lattice : Set ℂ).Countable := by
  refine (Set.countable_range fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂).mono ?_
  intro z hz
  obtain ⟨m, n, h⟩ := mem_lattice.mp hz
  exact ⟨(m, n), h⟩

p2m_export "PeriodPair" "kw_countable_lattice"

private def _root_.PeriodPair.kw_toPointHom : ℂ →+ (L.weierstrassCurve.toAffine).Point where
  toFun := L.toPoint L.kw_discriminantNeZero
  map_zero' := L.toPoint_zero L.kw_discriminantNeZero
  map_add' := L.kw_toPoint_add L.kw_discriminantNeZero

p2m_export "PeriodPair" "kw_toPointHom"
private theorem _root_.PeriodPair.kw_toPointHom_apply (z : ℂ) :
    L.kw_toPointHom z = L.toPoint L.kw_discriminantNeZero z := rfl

p2m_export "PeriodPair" "kw_toPointHom_apply"

private theorem _root_.PeriodPair.kw_ker_toPointHom :
    L.kw_toPointHom.ker = L.lattice.toAddSubgroup := by
  ext z
  constructor
  · exact fun hz => (L.kw_isUniformization).2.2 z hz
  · intro hz
    exact L.toPoint_of_mem L.kw_discriminantNeZero hz

p2m_export "PeriodPair" "kw_ker_toPointHom"

private def _root_.PeriodPair.kw_toPointAddEquiv :
    (ℂ ⧸ L.lattice.toAddSubgroup) ≃+ (L.weierstrassCurve.toAffine).Point :=
  QuotientAddGroup.liftEquiv L.lattice.toAddSubgroup (φ := L.kw_toPointHom)
    (L.kw_isUniformization).2.1 L.kw_ker_toPointHom.symm

p2m_export "PeriodPair" "kw_toPointAddEquiv"
theorem kw_toPointAddEquiv_mk (z : ℂ) :
    L.kw_toPointAddEquiv (QuotientAddGroup.mk z) = L.toPoint L.kw_discriminantNeZero z :=
  rfl

scoped instance kw_infinite_quotientLattice : Infinite (ℂ ⧸ L.lattice.toAddSubgroup) := by
  rw [← not_finite_iff_infinite]; intro hfin
  have : Countable L.lattice.toAddSubgroup :=
    Set.countable_coe_iff.mpr L.kw_countable_lattice
  have : Countable ((ℂ ⧸ L.lattice.toAddSubgroup) × L.lattice.toAddSubgroup) := inferInstance
  have hCc : Countable ℂ :=
    Countable.of_equiv _ (AddSubgroup.addGroupEquivQuotientProdAddSubgroup
      (s := L.lattice.toAddSubgroup)).symm
  have : Uncountable ℂ := Complex.ofReal_injective.uncountable
  exact absurd hCc not_countable

scoped instance kw_infinite_point : Infinite L.weierstrassCurve.toAffine.Point :=
  L.kw_toPointAddEquiv.toEquiv.infinite_iff.mp inferInstance

end PeriodPair
end

namespace ModularCurve
p2m_open "WeierstrassCurve \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine \
  AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve PeriodPair \
  P2MW.S_OVERLONG_302e4807.PeriodPair"

def KwD5BetweenCurvesHoloLift : Prop :=
  ∀ (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L.weierstrassCurve]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L.weierstrassCurve]
    [WeierstrassCurve.Affine.AbelTheorem L.weierstrassCurve] [L'.weierstrassCurve.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate L'.weierstrassCurve]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L'.weierstrassCurve]
    [WeierstrassCurve.Affine.AbelTheorem L'.weierstrassCurve]
    (ι'' : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι''),
    ∃ (F : ℂ → ℂ), Differentiable ℂ F ∧ F 0 ∈ L'.lattice ∧
      ∀ z, L'.kw_toPointHom (F z)
        = (pointMapOfPushforward ι'' hι'' hfin''
            (normFormulaAlong_of_elliptic ι'' hfin'')) (L.kw_toPointHom z)

end ModularCurve


namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongDegZero Pic0.coe_pushforwardAlongDegZero \
  Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk algebraAlong isScalarTower_along \
  isIntegral_along FiniteAlong NormFormulaAlong finrankAlong Place.ramificationIndexAlong \
  Place.ord_restrictAlong SeparableAlong Place.restrict_fiber_finite Place Place.ext \
  Place.coe_algebraMap HasPrincipalDivisors Pic0 Pic0.mk Place.ofHeightOneSpectrum \
  Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor \
  Place.toValuationSubring Place.evalAt Place.ofHeightOneSpectrum_injective \
  Place.ord_ofHeightOneSpectrum_ne_zero_iff normFormulaAlong"
end AlgebraicCurve
namespace Filter
p2m_export "Filter" "mem_bot ker mk mem_comap inter_mem IsBounded cocountable mem_ker \
  eventually_of_mem mem_map mem_top comap map cofinite"
end Filter
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.valuationSubringAtPrime HeightOneSpectrum.asIdeal \
  HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring \
  HeightOneSpectrum.eq_of_valuation_isEquiv_valuation mk HeightOneSpectrum"
end IsDedekindDomain
namespace IsLocalRing
p2m_export "IsLocalRing" "eq_maximalIdeal ResidueField maximalIdeal mem_maximalIdeal \
  ResidueField.algebraMap_eq residue"
end IsLocalRing
namespace PeriodPair
p2m_export "PeriodPair" "isClosed_lattice derivWeierstrassP_neg weierstrassP_neg lattice \
  weierstrassP_add_coe lattice_eq_span_range_basis ω₁ mk analyticOnNhd_derivWeierstrassP g₃ \
  deriv_weierstrassP ω₂ derivWeierstrassP_add_coe mem_lattice G g₂ analyticOnNhd_weierstrassP \
  weierstrassCurve weierstrassCurve_a₁ weierstrassCurve_a₂ weierstrassCurve_a₃ \
  equation_weierstrassP DiscriminantNeZero toPoint toPoint_of_mem toPoint_zero toPoint_of_notMem \
  IsUniformization jLattice scale_indep scale discriminant_ne_zero isUniformization_toPoint"
end PeriodPair
namespace Polynomial
p2m_export "Polynomial" "C X eval_mul support coeff_add algebraMap_eq monomial ext_iff degree \
  monic_X_pow_add degree_linear_le coeff_sub X_sub_C_ne_zero map comp roots coeff_C eval_pow sum \
  infinite reverse eval_X eval_C nontrivial flt X_ne_zero eval_sub pow mem_support_iff \
  C_mul_X_pow_eq_monomial derivative mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero \
  algebraMap_apply div C_neg coeff_C_mul eval_add evalEval ext coeff_X_pow funext ring lifts \
  restriction eval"
end Polynomial
namespace Polynomial
p2m_export "Polynomial" "C X eval_mul support coeff_add algebraMap_eq monomial ext_iff degree \
  monic_X_pow_add degree_linear_le coeff_sub X_sub_C_ne_zero map comp roots coeff_C eval_pow sum \
  infinite reverse eval_X eval_C nontrivial flt X_ne_zero eval_sub pow mem_support_iff \
  C_mul_X_pow_eq_monomial derivative mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero \
  algebraMap_apply div C_neg coeff_C_mul eval_add evalEval ext coeff_X_pow funext ring lifts \
  restriction eval"
end Polynomial
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
end WeierstrassCurve
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing.smul_basis_eq_zero \
  slope_of_X_ne slope CoordinateRing map Point.some Point.some.injEq Point.X_eq_iff Nonsingular \
  negAddY Point.zero_def FunctionField Point CoordinateRing.mk addX nonsingular_neg \
  equation_iff_nonsingular Point.some_ne_zero addY Point.add_of_X_ne equation_iff polynomial \
  Point.neg_some pushforwardAlong_single_eq pointMapOfPushforward pointMapOfPushforward_apply \
  IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint \
  deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem \
  pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot \
  hasPrincipalDivisors_functionField natCard_ker_pointMapOfPushforward_eq_finrankAlong \
  polyToFunctionField polyToFunctionField_apply polyToFunctionField_C polyToFunctionField_ne_zero \
  algebraMap_smul_basis"
end Affine
end WeierstrassCurve
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing.smul_basis_eq_zero \
  slope_of_X_ne slope CoordinateRing map Point.some Point.some.injEq Point.X_eq_iff Nonsingular \
  negAddY Point.zero_def FunctionField Point CoordinateRing.mk addX nonsingular_neg \
  equation_iff_nonsingular Point.some_ne_zero addY Point.add_of_X_ne equation_iff polynomial \
  Point.neg_some pushforwardAlong_single_eq pointMapOfPushforward pointMapOfPushforward_apply \
  IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint \
  deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem \
  pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot \
  hasPrincipalDivisors_functionField natCard_ker_pointMapOfPushforward_eq_finrankAlong \
  polyToFunctionField polyToFunctionField_apply polyToFunctionField_C polyToFunctionField_ne_zero \
  algebraMap_smul_basis"
namespace CoordinateRing
p2m_export "WeierstrassCurve.Affine.CoordinateRing" "smul_basis_eq_zero XYIdeal \
  quotientXYIdealEquiv YClass mk map exists_smul_basis_eq XClass smul_basis_mul_Y isDedekindDomain \
  exists_eq_XYIdeal XYIdeal_isMaximal XYIdeal_ne_bot"
end CoordinateRing
end Affine
end WeierstrassCurve
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
end WeierstrassCurve
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
end WeierstrassCurve


section


p2m_open "WeierstrassCurve \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine \
  P2MW.S_OVERLONG_302e4807.ModularCurv\
  e AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve"

namespace PeriodPair
p2m_export "PeriodPair" "isClosed_lattice derivWeierstrassP_neg weierstrassP_neg lattice \
  weierstrassP_add_coe lattice_eq_span_range_basis ω₁ mk analyticOnNhd_derivWeierstrassP g₃ \
  deriv_weierstrassP ω₂ derivWeierstrassP_add_coe mem_lattice G g₂ analyticOnNhd_weierstrassP \
  weierstrassCurve weierstrassCurve_a₁ weierstrassCurve_a₂ weierstrassCurve_a₃ \
  equation_weierstrassP DiscriminantNeZero toPoint toPoint_of_mem toPoint_zero toPoint_of_notMem \
  IsUniformization jLattice scale_indep scale discriminant_ne_zero isUniformization_toPoint"
p2m_open "PeriodPair"

variable (L : PeriodPair)

private theorem _root_.PeriodPair.kw_isDiscrete_lattice :
    IsDiscrete (L.lattice.toAddSubgroup : Set ℂ) := by
  rw [Submodule.coe_toAddSubgroup, isDiscrete_iff_discreteTopology]
  exact inferInstanceAs (DiscreteTopology L.lattice)

p2m_export "PeriodPair" "kw_isDiscrete_lattice"
private theorem _root_.PeriodPair.kw_isCoveringMap_mk_lattice :
    IsCoveringMap (QuotientAddGroup.mk (s := L.lattice.toAddSubgroup)) :=
  (AddSubgroup.isAddQuotientCoveringMap_of_comm L.lattice.toAddSubgroup
    L.kw_isDiscrete_lattice).isCoveringMap

p2m_export "PeriodPair" "kw_isCoveringMap_mk_lattice"
private theorem _root_.PeriodPair.kw_differentiable_of_locally_differentiable_lift_through_mk
    {F : ℂ → ℂ} (hFc : Continuous F)
    (hloc : ∀ z₀ : ℂ, ∃ U ∈ nhds z₀, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ z ∈ U, (QuotientAddGroup.mk (s := L.lattice.toAddSubgroup) (F z) :
        ℂ ⧸ L.lattice.toAddSubgroup) = QuotientAddGroup.mk (G z)) :
    Differentiable ℂ F := by
  intro z₀
  obtain ⟨U, hU, G, hGd, heq⟩ := hloc z₀
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  set V := Metric.ball z₀ ε
  have hVnhds : V ∈ nhds z₀ := Metric.ball_mem_nhds z₀ hε
  have hz₀V : z₀ ∈ V := Metric.mem_ball_self hε
  have hmem : Set.MapsTo (fun z => F z - G z) V (L.lattice.toAddSubgroup : Set ℂ) := by
    intro z hz
    have h0 : (QuotientAddGroup.mk (s := L.lattice.toAddSubgroup) (F z - G z)
        : ℂ ⧸ L.lattice.toAddSubgroup) = 0 := by
      rw [QuotientAddGroup.mk_sub, heq z (hεU hz), sub_self]
    exact (QuotientAddGroup.eq_zero_iff _).mp h0
  have hcont : ContinuousOn (fun z => F z - G z) V :=
    hFc.continuousOn.sub (hGd.mono hεU).continuousOn
  have hconst : ∀ z ∈ V, F z - G z = F z₀ - G z₀ := fun z hz =>
    (convex_ball z₀ ε).isPreconnected.constant_of_mapsTo L.kw_isDiscrete_lattice
      hcont hmem hz hz₀V
  have hFeq : ∀ z ∈ V, F z = F z₀ - G z₀ + G z := fun z hz => by
    rw [← hconst z hz, sub_add_cancel]
  exact (((differentiableOn_const (F z₀ - G z₀)).add (hGd.mono hεU)).congr
    (fun z hz => hFeq z hz)).differentiableAt hVnhds

p2m_export "PeriodPair" "kw_differentiable_of_locally_differentiable_lift_through_mk"
private theorem _root_.PeriodPair.kw_toPointHom_eq_toPointAddEquiv_mk (z : ℂ) :
    L.kw_toPointHom z = L.kw_toPointAddEquiv (QuotientAddGroup.mk z) := rfl

p2m_export "PeriodPair" "kw_toPointHom_eq_toPointAddEquiv_mk"
end PeriodPair
end


section

p2m_open "Polynomial \
  P2MW.S_OVERLONG_302e4807.Polynomial \
  IsDedekindDomain \
  P2MW.S_OVERLONG_302e4807.IsDedekindD\
  omain"

p2m_open_scoped "Polynomial.Bivariate \
  P2MW.S_OVERLONG_302e4807.Polynomial.\
  Bivariate"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongDegZero Pic0.coe_pushforwardAlongDegZero \
  Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk algebraAlong isScalarTower_along \
  isIntegral_along FiniteAlong NormFormulaAlong finrankAlong Place.ramificationIndexAlong \
  Place.ord_restrictAlong SeparableAlong Place.restrict_fiber_finite Place Place.ext \
  Place.coe_algebraMap HasPrincipalDivisors Pic0 Pic0.mk Place.ofHeightOneSpectrum \
  Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor \
  Place.toValuationSubring Place.evalAt Place.ofHeightOneSpectrum_injective \
  Place.ord_ofHeightOneSpectrum_ne_zero_iff normFormulaAlong"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong ramificationIndexAlong ord_restrictAlong \
  ramificationIndex_pos restrict_fiber_finite ext coe_algebraMap ResidueField deg adicValuation \
  adicValuation_ne_zero ord ord_mul ord_inv ord_unit_smul_zpow exists_unit_mul_zpow \
  ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' algebraMap_mem' \
  toValuationSubring mk mem_of_eval_monic_eq_zero IsRational evalAt algebraMap_evalAt \
  ofHeightOneSpectrum_injective ord_ofHeightOneSpectrum_ne_zero_iff evalAt_ne_zero evalAt_congr \
  ord_algebraMap evalAt_algebraMap evalAt_mul evalAt_inv"
end Place
p2m_open_scoped "AlgebraicCurve.Place" in
theorem Place.ramificationIndexAlong_pos (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') : 0 < Place.ramificationIndexAlong φ w := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  exact w.ramificationIndex_pos

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in
private theorem _root_.AlgebraicCurve.Place.ord_div (v : Place K F) {f g : F} (hf : f ≠ 0)
    (hg : g ≠ 0) :
    v.ord (f / g) = v.ord f - v.ord g := by
  rw [div_eq_mul_inv, v.ord_mul hf (inv_ne_zero hg), v.ord_inv]
  ring

end Place
p2m_export "AlgebraicCurve" "Place.ord_div"
end AlgebraicCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing.smul_basis_eq_zero \
  slope_of_X_ne slope CoordinateRing map Point.some Point.some.injEq Point.X_eq_iff Nonsingular \
  negAddY Point.zero_def FunctionField Point CoordinateRing.mk addX nonsingular_neg \
  equation_iff_nonsingular Point.some_ne_zero addY Point.add_of_X_ne equation_iff polynomial \
  Point.neg_some pushforwardAlong_single_eq pointMapOfPushforward pointMapOfPushforward_apply \
  IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint \
  deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem \
  pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot \
  hasPrincipalDivisors_functionField natCard_ker_pointMapOfPushforward_eq_finrankAlong \
  polyToFunctionField polyToFunctionField_apply polyToFunctionField_C polyToFunctionField_ne_zero \
  algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "WeierstrassCurve.Affine.CoordinateRing~evalAt \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine.CoordinateRing \
  AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve"

variable {F : Type*} [Field F] {W : Affine F}

theorem algebraMap_polynomial_eq_mk_C (p : F[X]) :
    algebraMap F[X] W.CoordinateRing p = CoordinateRing.mk W (C p) :=
  rfl

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

end Affine
end WeierstrassCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing.smul_basis_eq_zero \
  slope_of_X_ne slope CoordinateRing map Point.some Point.some.injEq Point.X_eq_iff Nonsingular \
  negAddY Point.zero_def FunctionField Point CoordinateRing.mk addX nonsingular_neg \
  equation_iff_nonsingular Point.some_ne_zero addY Point.add_of_X_ne equation_iff polynomial \
  Point.neg_some pushforwardAlong_single_eq pointMapOfPushforward pointMapOfPushforward_apply \
  IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint \
  deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem \
  pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot \
  hasPrincipalDivisors_functionField natCard_ker_pointMapOfPushforward_eq_finrankAlong \
  polyToFunctionField polyToFunctionField_apply polyToFunctionField_C polyToFunctionField_ne_zero \
  algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "WeierstrassCurve.Affine.CoordinateRing~evalAt \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine.CoordinateRing \
  AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve"

variable {F : Type*} [Field F] (W : Affine F)

variable {W}

def yGen (W : Affine F) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)

end Affine
end WeierstrassCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing.smul_basis_eq_zero \
  slope_of_X_ne slope CoordinateRing map Point.some Point.some.injEq Point.X_eq_iff Nonsingular \
  negAddY Point.zero_def FunctionField Point CoordinateRing.mk addX nonsingular_neg \
  equation_iff_nonsingular Point.some_ne_zero addY Point.add_of_X_ne equation_iff polynomial \
  Point.neg_some pushforwardAlong_single_eq pointMapOfPushforward pointMapOfPushforward_apply \
  IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint \
  deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem \
  pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot \
  hasPrincipalDivisors_functionField natCard_ker_pointMapOfPushforward_eq_finrankAlong \
  polyToFunctionField polyToFunctionField_apply polyToFunctionField_C polyToFunctionField_ne_zero \
  algebraMap_smul_basis"
end Affine
end WeierstrassCurve
end


section

p2m_open "IsLocalRing \
  P2MW.S_OVERLONG_302e4807.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongDegZero Pic0.coe_pushforwardAlongDegZero \
  Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk algebraAlong isScalarTower_along \
  isIntegral_along FiniteAlong NormFormulaAlong finrankAlong Place.ramificationIndexAlong \
  Place.ord_restrictAlong SeparableAlong Place.restrict_fiber_finite Place Place.ext \
  Place.coe_algebraMap HasPrincipalDivisors Pic0 Pic0.mk Place.ofHeightOneSpectrum \
  Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor \
  Place.toValuationSubring Place.evalAt Place.ofHeightOneSpectrum_injective \
  Place.ord_ofHeightOneSpectrum_ne_zero_iff normFormulaAlong"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong ramificationIndexAlong ord_restrictAlong \
  ramificationIndex_pos restrict_fiber_finite ext coe_algebraMap ResidueField deg adicValuation \
  adicValuation_ne_zero ord ord_mul ord_inv ord_unit_smul_zpow exists_unit_mul_zpow \
  ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' algebraMap_mem' \
  toValuationSubring mk mem_of_eval_monic_eq_zero IsRational evalAt algebraMap_evalAt \
  ofHeightOneSpectrum_injective ord_ofHeightOneSpectrum_ne_zero_iff evalAt_ne_zero evalAt_congr \
  ord_algebraMap evalAt_algebraMap evalAt_mul evalAt_inv"
p2m_open "AlgebraicCurve.Place~ord_nonneg_of_mem~mem_of_ord_nonneg~mem_iff_ord_nonneg"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_sub_evalAt_pos (hrat : v.IsRational) {f : F}
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

p2m_export "AlgebraicCurve.Place" "ord_sub_evalAt_pos"
end Place
end AlgebraicCurve
end


section


p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve WeierstrassCurve \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing.smul_basis_eq_zero \
  slope_of_X_ne slope CoordinateRing map Point.some Point.some.injEq Point.X_eq_iff Nonsingular \
  negAddY Point.zero_def FunctionField Point CoordinateRing.mk addX nonsingular_neg \
  equation_iff_nonsingular Point.some_ne_zero addY Point.add_of_X_ne equation_iff polynomial \
  Point.neg_some pushforwardAlong_single_eq pointMapOfPushforward pointMapOfPushforward_apply \
  IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint \
  deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem \
  pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot \
  hasPrincipalDivisors_functionField natCard_ker_pointMapOfPushforward_eq_finrankAlong \
  polyToFunctionField polyToFunctionField_apply polyToFunctionField_C polyToFunctionField_ne_zero \
  algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [W.GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem Δ_ne_zero_of_isElliptic : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero

def placeOfPointEquiv : W.Point ≃ AlgebraicCurve.Place F W.FunctionField :=
  Equiv.ofBijective placeOfPoint
    ⟨placeOfPoint_injective, placeOfPoint_surjective (Δ_ne_zero_of_isElliptic W)⟩

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem placeOfPoint_placeOfPointEquiv_symm (w : AlgebraicCurve.Place F W.FunctionField) :
    placeOfPoint ((placeOfPointEquiv W).symm w) = w :=
  (placeOfPointEquiv W).apply_symm_apply w

namespace IsogenyEndDatum
p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "pointEnd pointEnd_apply pointEnd_eq_of_seam \
  hfin hι mk ι"
end IsogenyEndDatum
end Affine
end WeierstrassCurve
end


section

p2m_open "WeierstrassCurve \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine \
  P2MW.S_OVERLONG_302e4807.ModularCurv\
  e AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve"

namespace PeriodPair
p2m_export "PeriodPair" "isClosed_lattice derivWeierstrassP_neg weierstrassP_neg lattice \
  weierstrassP_add_coe lattice_eq_span_range_basis ω₁ mk analyticOnNhd_derivWeierstrassP g₃ \
  deriv_weierstrassP ω₂ derivWeierstrassP_add_coe mem_lattice G g₂ analyticOnNhd_weierstrassP \
  weierstrassCurve weierstrassCurve_a₁ weierstrassCurve_a₂ weierstrassCurve_a₃ \
  equation_weierstrassP DiscriminantNeZero toPoint toPoint_of_mem toPoint_zero toPoint_of_notMem \
  IsUniformization jLattice scale_indep scale discriminant_ne_zero isUniformization_toPoint"
p2m_open "PeriodPair"

variable (L : PeriodPair)

private theorem _root_.PeriodPair.kw_surjective_toPointHom :
    Function.Surjective L.kw_toPointHom := by
  intro P
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective (L.kw_toPointAddEquiv.symm P)
  exact ⟨z, by rw [L.kw_toPointHom_eq_toPointAddEquiv_mk, hz, AddEquiv.apply_symm_apply]⟩

p2m_export "PeriodPair" "kw_surjective_toPointHom"
end PeriodPair
end


section


p2m_open "WeierstrassCurve \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine \
  P2MW.S_OVERLONG_302e4807.ModularCurv\
  e AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve PeriodPair \
  P2MW.S_OVERLONG_302e4807.PeriodPair"

namespace ModularCurve

def KwD5BetweenCurvesLocallyHoloLift : Prop :=
  ∀ (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L.weierstrassCurve]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L.weierstrassCurve]
    [WeierstrassCurve.Affine.AbelTheorem L.weierstrassCurve] [L'.weierstrassCurve.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate L'.weierstrassCurve]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L'.weierstrassCurve]
    [WeierstrassCurve.Affine.AbelTheorem L'.weierstrassCurve]
    (ι'' : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι'') (z₀ : ℂ),
    ∃ U ∈ nhds z₀, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ z ∈ U, L'.kw_toPointHom (G z)
        = (pointMapOfPushforward ι'' hι'' hfin''
            (normFormulaAlong_of_elliptic ι'' hfin'')) (L.kw_toPointHom z)

theorem kw_surgehgf4_hH2_betweenCurvesHoloLift_of_locallyHolo
    (hH2c : KwD5BetweenCurvesLocallyHoloLift) :
    KwD5BetweenCurvesHoloLift := by
  intro L L' _ _ _ _ _ _ _ _ ι'' hι'' hfin''
  set ψ := pointMapOfPushforward ι'' hι'' hfin'' (normFormulaAlong_of_elliptic ι'' hfin'')
    with hψdef
  set g : ℂ → ℂ ⧸ L'.lattice.toAddSubgroup :=
    fun z => L'.kw_toPointAddEquiv.symm (ψ (L.kw_toPointHom z)) with hg
  have hgloc : ∀ z₀ : ℂ, ∃ U ∈ nhds z₀, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ z ∈ U, g z = QuotientAddGroup.mk (G z) := fun z₀ => by
    obtain ⟨U, hU, G, hGd, hGint⟩ := hH2c L L' ι'' hι'' hfin'' z₀
    exact ⟨U, hU, G, hGd, fun z hz => by
      change L'.kw_toPointAddEquiv.symm (ψ (L.kw_toPointHom z)) = _
      rw [hψdef, ← hGint z hz, L'.kw_toPointHom_eq_toPointAddEquiv_mk,
        AddEquiv.symm_apply_apply]⟩
  have hmkc : Continuous (QuotientAddGroup.mk (s := L'.lattice.toAddSubgroup)) :=
    L'.kw_isCoveringMap_mk_lattice.continuous
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun z₀ => by
    obtain ⟨U, hU, G, hGd, heq⟩ := hgloc z₀
    exact ((hmkc.comp_continuousOn hGd.continuousOn).congr
      (fun z hz => heq z hz)).continuousAt hU
  have hg0 : (QuotientAddGroup.mk (0 : ℂ) : ℂ ⧸ L'.lattice.toAddSubgroup)
      = (⟨g, hgc⟩ : C(ℂ, ℂ ⧸ L'.lattice.toAddSubgroup)) 0 := by
    simp only [ContinuousMap.coe_mk, hg, _root_.map_zero, QuotientAddGroup.mk_zero]
  obtain ⟨F, ⟨hF0, hFlift⟩, -⟩ :=
    L'.kw_isCoveringMap_mk_lattice.existsUnique_continuousMap_lifts ⟨g, hgc⟩ 0 0 hg0
  have hFliftz : ∀ z, (QuotientAddGroup.mk (F z) : ℂ ⧸ L'.lattice.toAddSubgroup) = g z :=
    fun z => congrFun hFlift z
  refine ⟨F, ?_, ?_, ?_⟩
  · refine L'.kw_differentiable_of_locally_differentiable_lift_through_mk F.continuous
      (fun z₀ => ?_)
    obtain ⟨U, hU, G, hGd, heq⟩ := hgloc z₀
    exact ⟨U, hU, G, hGd, fun z hz => (hFliftz z).trans (heq z hz)⟩
  · rw [hF0]; exact Submodule.zero_mem L'.lattice
  · intro z
    rw [L'.kw_toPointHom_eq_toPointAddEquiv_mk, hFliftz z, hg, AddEquiv.apply_symm_apply]

end ModularCurve
end


section

p2m_open "WeierstrassCurve \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine \
  P2MW.S_OVERLONG_302e4807.ModularCurv\
  e AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve Filter \
  P2MW.S_OVERLONG_302e4807.Filter \
  Polynomial \
  P2MW.S_OVERLONG_302e4807.Polynomial"
p2m_open_scoped "PeriodPair \
  P2MW.S_OVERLONG_302e4807.PeriodPair \
  Topology \
  P2MW.S_OVERLONG_302e4807.Topology"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing.smul_basis_eq_zero \
  slope_of_X_ne slope CoordinateRing map Point.some Point.some.injEq Point.X_eq_iff Nonsingular \
  negAddY Point.zero_def FunctionField Point CoordinateRing.mk addX nonsingular_neg \
  equation_iff_nonsingular Point.some_ne_zero addY Point.add_of_X_ne equation_iff polynomial \
  Point.neg_some pushforwardAlong_single_eq pointMapOfPushforward pointMapOfPushforward_apply \
  IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint \
  deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem \
  pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot \
  hasPrincipalDivisors_functionField natCard_ker_pointMapOfPushforward_eq_finrankAlong \
  polyToFunctionField polyToFunctionField_apply polyToFunctionField_C polyToFunctionField_ne_zero \
  algebraMap_smul_basis"
namespace IsogenyEndDatum
p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "pointEnd pointEnd_apply pointEnd_eq_of_seam \
  hfin hι mk ι"
end IsogenyEndDatum
end Affine
end WeierstrassCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing.smul_basis_eq_zero \
  slope_of_X_ne slope CoordinateRing map Point.some Point.some.injEq Point.X_eq_iff Nonsingular \
  negAddY Point.zero_def FunctionField Point CoordinateRing.mk addX nonsingular_neg \
  equation_iff_nonsingular Point.some_ne_zero addY Point.add_of_X_ne equation_iff polynomial \
  Point.neg_some pushforwardAlong_single_eq pointMapOfPushforward pointMapOfPushforward_apply \
  IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint \
  deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem \
  pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot \
  hasPrincipalDivisors_functionField natCard_ker_pointMapOfPushforward_eq_finrankAlong \
  polyToFunctionField polyToFunctionField_apply polyToFunctionField_C polyToFunctionField_ne_zero \
  algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "WeierstrassCurve.Affine.CoordinateRing~evalAt \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine.CoordinateRing"

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

theorem kw_evalAt_placeOfEquation_mk {r s : F} (hrs : W.Equation r s) (p : Polynomial F[X]) :
    (placeOfEquation hrs).evalAt
        (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p))
      = p.evalEval r s := by
  have hmem : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p)
      ∈ (placeOfEquation hrs).toValuationSubring := isFinitePlace_placeOfEquation hrs _
  have hdiffFF : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p)
        - algebraMap F W.FunctionField (p.evalEval r s)
      = algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (p - C (C (p.evalEval r s)))) := by
    rw [map_sub, IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField, ← map_sub,
      show (algebraMap F W.CoordinateRing) (p.evalEval r s)
        = CoordinateRing.mk W (C (C (p.evalEval r s))) from rfl]
  have hmemzero : CoordinateRing.mk W (p - C (C (p.evalEval r s)))
      ∈ XYIdeal W r (C s) := (mk_mem_XYIdeal_iff hrs _).mpr (by simp [evalEval])
  refine ((placeOfEquation hrs).evalAt_congr hmem
    ((placeOfEquation hrs).algebraMap_mem' _) ?_).trans
    ((placeOfEquation hrs).evalAt_algebraMap _)
  rcases eq_or_ne (CoordinateRing.mk W (p - C (C (p.evalEval r s)))) 0 with h0 | hne
  · left; rw [hdiffFF, h0, _root_.map_zero]
  · right; rw [hdiffFF]; exact (ord_placeOfEquation_pos_iff hrs hne).mpr hmemzero

end Affine
end WeierstrassCurve

namespace PeriodPair
p2m_export "PeriodPair" "isClosed_lattice derivWeierstrassP_neg weierstrassP_neg lattice \
  weierstrassP_add_coe lattice_eq_span_range_basis ω₁ mk analyticOnNhd_derivWeierstrassP g₃ \
  deriv_weierstrassP ω₂ derivWeierstrassP_add_coe mem_lattice G g₂ analyticOnNhd_weierstrassP \
  weierstrassCurve weierstrassCurve_a₁ weierstrassCurve_a₂ weierstrassCurve_a₃ \
  equation_weierstrassP DiscriminantNeZero toPoint toPoint_of_mem toPoint_zero toPoint_of_notMem \
  IsUniformization jLattice scale_indep scale discriminant_ne_zero isUniformization_toPoint"
p2m_open "PeriodPair"

variable (L : PeriodPair)

private theorem _root_.PeriodPair.kw_differentiableOn_eval_wp (q : ℂ[X]) :
    DifferentiableOn ℂ (fun z => q.eval (℘[L] z)) (L.lattice : Set ℂ)ᶜ := by
  have hP : DifferentiableOn ℂ ℘[L] (L.lattice : Set ℂ)ᶜ :=
    L.analyticOnNhd_weierstrassP.differentiableOn
  induction q using Polynomial.induction_on with
  | C a => simp only [eval_C]; exact differentiableOn_const a
  | add p q hp hq => simpa using hp.fun_add hq
  | monomial n a ih =>
    refine (ih.mul hP).congr fun z _ => ?_
    simp only [eval_mul, eval_C, eval_pow, eval_X, pow_succ, Pi.mul_apply]; ring

p2m_export "PeriodPair" "kw_differentiableOn_eval_wp"
private theorem _root_.PeriodPair.kw_differentiableOn_evalEval_wp (p : Polynomial ℂ[X]) :
    DifferentiableOn ℂ (fun z => p.evalEval (℘[L] z) (℘'[L] z / 2)) (L.lattice : Set ℂ)ᶜ := by
  have hP' : DifferentiableOn ℂ (fun z => ℘'[L] z / 2) (L.lattice : Set ℂ)ᶜ :=
    L.analyticOnNhd_derivWeierstrassP.differentiableOn.div_const 2
  induction p using Polynomial.induction_on with
  | C c => simpa [evalEval] using L.kw_differentiableOn_eval_wp c
  | add p q hp hq => simpa [evalEval] using hp.fun_add hq
  | monomial n c ih =>
    refine (ih.mul hP').congr fun z _ => ?_
    simp only [evalEval, eval_mul, eval_pow, eval_C, eval_X, pow_succ, Pi.mul_apply]; ring

p2m_export "PeriodPair" "kw_differentiableOn_evalEval_wp"
end PeriodPair
end

section


section

p2m_open "Polynomial \
  P2MW.S_OVERLONG_302e4807.Polynomial \
  AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve WeierstrassCurve \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine"

p2m_open_scoped "Polynomial.Bivariate \
  P2MW.S_OVERLONG_302e4807.Polynomial.\
  Bivariate"

namespace ModularCurve
namespace Mmr73

universe u

section PlaceEval

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

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

end PlaceEval
end Mmr73
end ModularCurve
end
end

section


section

p2m_open "P2MW.S_OVERLONG_302e4807.Mod\
  ularCurve WeierstrassCurve \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine Polynomial \
  P2MW.S_OVERLONG_302e4807.Polynomial \
  AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve"

namespace ModularCurve

universe u

attribute [local instance] Classical.propDecidable

section GeomMorphBC

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {E E' : Affine K} [E.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E] [WeierstrassCurve.Affine.AbelTheorem E]
    [E'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E']
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E']
    [WeierstrassCurve.Affine.AbelTheorem E']
variable (ι : E'.FunctionField →ₐ[K] E.FunctionField)
variable (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)

def kw_fdn2_qephod_hend7_geomMorphBC : E.Point → E'.Point :=
  fun P => (placeOfPointEquiv E').symm ((placeOfPoint P).restrictAlong ι hι)

local notation "gBC" => kw_fdn2_qephod_hend7_geomMorphBC ι hι

omit [WeierstrassCurve.IsElliptic E] [GenusOnePlaceGate.IsCentred E] [E.AbelTheorem] in
omit [DecidableEq K] [IsAlgClosed K] [CharZero K] [GenusOnePlaceGate.IsCentred E']
  [E'.AbelTheorem] in
theorem kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC (P : E.Point) :
    (placeOfPoint P).restrictAlong ι hι = placeOfPoint (gBC P) :=
  (placeOfPoint_placeOfPointEquiv_symm E' _).symm

omit [WeierstrassCurve.IsElliptic E] [GenusOnePlaceGate.IsCentred E] [E.AbelTheorem] in
omit [DecidableEq K] [IsAlgClosed K] [CharZero K] [GenusOnePlaceGate.IsCentred E']
  [E'.AbelTheorem] in
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
omit [WeierstrassCurve.IsElliptic E] [GenusOnePlaceGate.IsCentred E] [E.AbelTheorem] in
omit [DecidableEq K] [IsAlgClosed K] [GenusOnePlaceGate.IsCentred E'] [E'.AbelTheorem] in
theorem kw_fdn2_qephod_hend7_pushforwardHom_pointClass_eq_sub (P : E.Point) :
    Pic0.pushforwardAlongHom ι hι hfin (normFormulaAlong_of_elliptic ι hfin)
        (pointClass P)
      = pointClass (gBC P) - pointClass (gBC 0) := by
  change Pic0.pushforwardAlongHom ι hι hfin _ (Pic0.mk (pointDivisor P))
      = Pic0.mk (pointDivisor (gBC P)) - Pic0.mk (pointDivisor (gBC 0))
  rw [Pic0.pushforwardAlongHom_mk,
    kw_fdn2_qephod_hend7_pushforwardDegZero_pointDivisor_geomMorphBC ι hι P]
  rfl

include hfin in
omit [WeierstrassCurve.IsElliptic E] [GenusOnePlaceGate.IsCentred E] in
omit [IsAlgClosed K] [GenusOnePlaceGate.IsCentred E'] in
theorem kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub (P : E.Point) :
    pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic ι hfin) P
      = gBC P - gBC 0 := by
  rw [pointMapOfPushforward_apply,
    kw_fdn2_qephod_hend7_pushforwardHom_pointClass_eq_sub ι hι hfin P, map_sub,
    genusOnePic0Equiv_apply, genusOnePic0Equiv_apply, pic0ToPoint_pointClass,
    pic0ToPoint_pointClass]

end GeomMorphBC
end ModularCurve
end
end


section

p2m_open "WeierstrassCurve \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine \
  P2MW.S_OVERLONG_302e4807.ModularCurv\
  e AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve Filter \
  P2MW.S_OVERLONG_302e4807.Filter"
p2m_open_scoped "PeriodPair \
  P2MW.S_OVERLONG_302e4807.PeriodPair \
  Topology \
  P2MW.S_OVERLONG_302e4807.Topology"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ \
  a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.equation_iff Affine.Point.neg_some j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing.smul_basis_eq_zero \
  slope_of_X_ne slope CoordinateRing map Point.some Point.some.injEq Point.X_eq_iff Nonsingular \
  negAddY Point.zero_def FunctionField Point CoordinateRing.mk addX nonsingular_neg \
  equation_iff_nonsingular Point.some_ne_zero addY Point.add_of_X_ne equation_iff polynomial \
  Point.neg_some pushforwardAlong_single_eq pointMapOfPushforward pointMapOfPushforward_apply \
  IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint \
  deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem \
  pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot \
  hasPrincipalDivisors_functionField natCard_ker_pointMapOfPushforward_eq_finrankAlong \
  polyToFunctionField polyToFunctionField_apply polyToFunctionField_C polyToFunctionField_ne_zero \
  algebraMap_smul_basis"
namespace IsogenyEndDatum
p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "pointEnd pointEnd_apply pointEnd_eq_of_seam \
  hfin hι mk ι"
end IsogenyEndDatum
end Affine
end WeierstrassCurve

namespace PeriodPair
p2m_export "PeriodPair" "isClosed_lattice derivWeierstrassP_neg weierstrassP_neg lattice \
  weierstrassP_add_coe lattice_eq_span_range_basis ω₁ mk analyticOnNhd_derivWeierstrassP g₃ \
  deriv_weierstrassP ω₂ derivWeierstrassP_add_coe mem_lattice G g₂ analyticOnNhd_weierstrassP \
  weierstrassCurve weierstrassCurve_a₁ weierstrassCurve_a₂ weierstrassCurve_a₃ \
  equation_weierstrassP DiscriminantNeZero toPoint toPoint_of_mem toPoint_zero toPoint_of_notMem \
  IsUniformization jLattice scale_indep scale discriminant_ne_zero isUniformization_toPoint"
p2m_open "PeriodPair"

variable (L : PeriodPair)

private theorem _root_.PeriodPair.kw_countable_toPointHom_preimage {T : Set
  L.weierstrassCurve.toAffine.Point}
    (hT : T.Finite) : (L.kw_toPointHom ⁻¹' T).Countable := by
  have hcov : L.kw_toPointHom ⁻¹' T ⊆ ⋃ t ∈ T, L.kw_toPointHom ⁻¹' {t} := by
    intro z hz; exact Set.mem_biUnion hz rfl
  refine (Set.Countable.biUnion hT.countable fun t _ => ?_).mono hcov
  obtain ⟨w, hw⟩ := L.kw_surjective_toPointHom t
  have hfib : L.kw_toPointHom ⁻¹' {t} = (· + w) '' (L.lattice : Set ℂ) := by
    ext z; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · intro hz
      refine ⟨z - w, ?_, by ring⟩
      have h0 : L.kw_toPointHom (z - w) = 0 := by rw [map_sub, hz, hw, sub_self]
      rw [← AddMonoidHom.mem_ker, L.kw_ker_toPointHom, Submodule.mem_toAddSubgroup] at h0
      exact h0
    · rintro ⟨l, hl, rfl⟩
      have h0 : L.kw_toPointHom l = 0 := by
        rw [← AddMonoidHom.mem_ker, L.kw_ker_toPointHom, Submodule.mem_toAddSubgroup]
        exact hl
      rw [map_add, hw, h0, zero_add]
  rw [hfib]
  exact L.kw_countable_lattice.image _

p2m_export "PeriodPair" "kw_countable_toPointHom_preimage"
end PeriodPair
end


section


p2m_open "WeierstrassCurve \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine \
  P2MW.S_OVERLONG_302e4807.ModularCurv\
  e AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve PeriodPair \
  P2MW.S_OVERLONG_302e4807.PeriodPair"

namespace ModularCurve

def KwD5BetweenCurvesCocountableHoloLift : Prop :=
  ∀ (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L.weierstrassCurve]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L.weierstrassCurve]
    [WeierstrassCurve.Affine.AbelTheorem L.weierstrassCurve] [L'.weierstrassCurve.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate L'.weierstrassCurve]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L'.weierstrassCurve]
    [WeierstrassCurve.Affine.AbelTheorem L'.weierstrassCurve]
    (ι'' : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι''),
    ∃ S : Set ℂ, S.Countable ∧
    ∀ z₀ ∉ S, ∃ U ∈ nhds z₀, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ z ∈ U, L'.kw_toPointHom (G z)
        = (pointMapOfPushforward ι'' hι'' hfin''
            (normFormulaAlong_of_elliptic ι'' hfin'')) (L.kw_toPointHom z)

theorem kw_surgehgf4_hH2c_betweenCurvesLocallyHoloLift_of_cocountable
    (hH2d : KwD5BetweenCurvesCocountableHoloLift) :
    KwD5BetweenCurvesLocallyHoloLift := by
  intro L L' _ _ _ _ _ _ _ _ ι'' hι'' hfin'' z₀
  obtain ⟨S, hSc, hgen⟩ := hH2d L L' ι'' hι'' hfin''
  obtain ⟨w, hw⟩ : ∃ w, z₀ + w ∉ S := by
    obtain ⟨ζ, hζ⟩ := (hSc.isPathConnected_compl_of_one_lt_rank
      (by simp [Complex.rank_real_complex])).nonempty
    exact ⟨ζ - z₀, by rwa [add_sub_cancel]⟩
  obtain ⟨U', hU', G', hG'd, hG'int⟩ := hgen (z₀ + w) hw
  obtain ⟨cw, hcw⟩ := L'.kw_surjective_toPointHom
    ((pointMapOfPushforward ι'' hι'' hfin''
      (normFormulaAlong_of_elliptic ι'' hfin'')) (L.kw_toPointHom w))
  refine ⟨(· + w) ⁻¹' U',
    (continuous_add_const w).continuousAt.preimage_mem_nhds hU',
    fun z => G' (z + w) - cw,
    (hG'd.comp (differentiable_id.add_const w).differentiableOn
      (Set.mapsTo_preimage _ _)).sub_const cw,
    fun z hz => ?_⟩
  rw [map_sub, hcw, hG'int (z + w) hz,
    ← map_sub (pointMapOfPushforward ι'' hι'' hfin''
      (normFormulaAlong_of_elliptic ι'' hfin'')),
    ← map_sub L.kw_toPointHom, add_sub_cancel_right]

theorem kw_surgehgf4_hH2_betweenCurvesHoloLift_of_cocountable
    (hH2d : KwD5BetweenCurvesCocountableHoloLift) :
    KwD5BetweenCurvesHoloLift :=
  kw_surgehgf4_hH2_betweenCurvesHoloLift_of_locallyHolo
    (kw_surgehgf4_hH2c_betweenCurvesLocallyHoloLift_of_cocountable hH2d)

end ModularCurve
end

section


section

p2m_open "P2MW.S_OVERLONG_302e4807.Mod\
  ularCurve WeierstrassCurve \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine Polynomial \
  P2MW.S_OVERLONG_302e4807.Polynomial \
  AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve"

namespace ModularCurve

universe u

attribute [local instance] Classical.propDecidable


section Fintype

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {E E' : Affine K} [E.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E] [WeierstrassCurve.Affine.AbelTheorem E]
    [E'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E']
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E']
    [WeierstrassCurve.Affine.AbelTheorem E']
variable (ι : E'.FunctionField →ₐ[K] E.FunctionField)
variable (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)

include hfin in
omit [DecidableEq K] [IsAlgClosed K] [CharZero K] [WeierstrassCurve.IsElliptic E]
  [E.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred E] [E.AbelTheorem]
  [WeierstrassCurve.IsElliptic E'] [E'.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred E']
  [E'.AbelTheorem] in
theorem kw_fdn2_qephod_hend10_finrankAlong_pos : 0 < finrankAlong K ι := by
  unfold finrankAlong
  let := algebraAlong ι
  have : Module.Finite E'.FunctionField E.FunctionField := hfin
  exact Module.finrank_pos

theorem kw_fdn2_qephod_hend10_kerPMOP_finite :
    Finite ↥(AddMonoidHom.ker
      (pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic ι hfin))) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [kw_fdn2_qephod_hend7_pmopKerCard_proved K E E' ι hι hfin]
  exact (kw_fdn2_qephod_hend10_finrankAlong_pos ι hfin).ne'

end Fintype

section Squeeze

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {E E' : Affine K} [E.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E] [WeierstrassCurve.Affine.AbelTheorem E]
    [E'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E']
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E']
    [WeierstrassCurve.Affine.AbelTheorem E']
variable (ι : E'.FunctionField →ₐ[K] E.FunctionField)
variable (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)

local notation "kerPMOP" =>
  AddMonoidHom.ker (pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic ι hfin))

end Squeeze
end ModularCurve
end
end


section


p2m_open "WeierstrassCurve \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine \
  P2MW.S_OVERLONG_302e4807.ModularCurv\
  e AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve PeriodPair \
  P2MW.S_OVERLONG_302e4807.PeriodPair \
  Filter \
  P2MW.S_OVERLONG_302e4807.Filter"
p2m_open_scoped "PeriodPair \
  P2MW.S_OVERLONG_302e4807.PeriodPair \
  Topology \
  P2MW.S_OVERLONG_302e4807.Topology"

namespace ModularCurve

def KwD5BetweenCurvesCocountableAffineHoloCoords : Prop :=
  ∀ (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L.weierstrassCurve]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L.weierstrassCurve]
    [WeierstrassCurve.Affine.AbelTheorem L.weierstrassCurve] [L'.weierstrassCurve.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate L'.weierstrassCurve]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L'.weierstrassCurve]
    [WeierstrassCurve.Affine.AbelTheorem L'.weierstrassCurve]
    (ι'' : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι''),
    ∃ S : Set ℂ, S.Countable ∧
    ∀ z₀ ∉ S, ∃ U ∈ nhds z₀, ∃ X Y : ℂ → ℂ,
      DifferentiableOn ℂ X U ∧ DifferentiableOn ℂ Y U ∧
      ∀ z ∈ U, Y z ≠ 0 ∧
        ∃ h, (pointMapOfPushforward ι'' hι'' hfin''
            (normFormulaAlong_of_elliptic ι'' hfin'')) (L.kw_toPointHom z)
          = Point.some (X z) (Y z) h

theorem kw_surgehgf4_hH2d_betweenCurvesCocountableHoloLift_of_affineHoloCoords
    (hH2e : KwD5BetweenCurvesCocountableAffineHoloCoords) :
    KwD5BetweenCurvesCocountableHoloLift := by
  intro L L' _ _ _ _ _ _ _ _ ι'' hι'' hfin''
  obtain ⟨S, hSc, hgen⟩ := hH2e L L' ι'' hι'' hfin''
  refine ⟨S, hSc, fun z₀ hz₀ => ?_⟩
  obtain ⟨U, hU, X, Y, hXd, hYd, hcoord⟩ := hgen z₀ hz₀
  obtain ⟨U', hU'U, hU'open, hz₀U'⟩ := mem_nhds_iff.mp hU
  obtain ⟨hYz₀, hnsz₀, hcoord₀⟩ := hcoord z₀ (hU'U hz₀U')
  obtain ⟨w₀, hw₀⟩ := L'.kw_surjective_toPointHom (.some (X z₀) (Y z₀) hnsz₀)
  have hw₀Λ : w₀ ∉ L'.lattice := by
    intro hmem
    have h0 : L'.kw_toPointHom w₀ = 0 := by
      rw [← AddMonoidHom.mem_ker, L'.kw_ker_toPointHom]; exact hmem
    exact Point.some_ne_zero _ (hw₀ ▸ h0)
  have hPw₀ : ℘[L'] w₀ = X z₀ ∧ ℘'[L'] w₀ / 2 = Y z₀ := by
    have h := hw₀
    rwa [L'.kw_toPointHom_apply, L'.toPoint_of_notMem _ hw₀Λ, Point.some.injEq] at h
  have hder : deriv ℘[L'] w₀ ≠ 0 := by
    simp only [PeriodPair.deriv_weierstrassP]
    exact fun h0 => hYz₀ (by rw [← hPw₀.2, h0, zero_div])
  have hPa : AnalyticAt ℂ ℘[L'] w₀ := L'.analyticOnNhd_weierstrassP w₀ hw₀Λ
  set ψ := hPa.hasStrictDerivAt.localInverse ℘[L'] (deriv ℘[L'] w₀) w₀ hder with hψdef
  have hψa : AnalyticAt ℂ ψ (X z₀) := hPw₀.1 ▸ hPa.analyticAt_localInverse hder
  have hψw₀ : ψ (X z₀) = w₀ :=
    hPw₀.1 ▸ HasStrictFDerivAt.localInverse_apply_image _
  set G := ψ ∘ X with hGdef
  have hXcont : ContinuousAt X z₀ := (hXd.differentiableAt hU).continuousAt
  have hGcont : ContinuousAt G z₀ := hψa.continuousAt.comp hXcont
  have hGz₀ : G z₀ = w₀ := hψw₀
  have hevΛ : ∀ᶠ z in 𝓝 z₀, G z ∉ L'.lattice :=
    hGcont.eventually (L'.isClosed_lattice.isOpen_compl.mem_nhds (hGz₀ ▸ hw₀Λ))
  have hevR : ∀ᶠ z in 𝓝 z₀, ℘[L'] (G z) = X z := by
    have h := hPw₀.1 ▸ hPa.hasStrictDerivAt.eventually_right_inverse hder
    exact hXcont.eventually h
  have hevψd : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ ψ (X z) :=
    hXcont.eventually
      ((AnalyticAt.eventually_analyticAt hψa).mono fun _ hy => hy.differentiableAt)
  have hevXd : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ X z :=
    eventually_of_mem (hU'open.mem_nhds hz₀U') fun z hz =>
      (hXd.mono hU'U).differentiableAt (hU'open.mem_nhds hz)
  have hevU : ∀ᶠ z in 𝓝 z₀, z ∈ U :=
    eventually_of_mem (hU'open.mem_nhds hz₀U') hU'U
  have hevSgn : ∀ᶠ z in 𝓝 z₀, ℘'[L'] (G z) / 2 + Y z ≠ 0 := by
    have hP'cont : ContinuousAt ℘'[L'] (G z₀) := by
      rw [hGz₀]; exact (L'.analyticOnNhd_derivWeierstrassP w₀ hw₀Λ).continuousAt
    have hcont : ContinuousAt (fun z => ℘'[L'] (G z) / 2 + Y z) z₀ :=
      ((hP'cont.comp hGcont).div_const 2).add (hYd.differentiableAt hU).continuousAt
    refine hcont.eventually (isOpen_ne.mem_nhds ?_)
    change ℘'[L'] (G z₀) / 2 + Y z₀ ≠ 0
    rw [hGz₀, hPw₀.2, ← two_mul]; exact mul_ne_zero two_ne_zero hYz₀
  obtain ⟨V, hVmem, hVopen, hVz₀⟩ := eventually_nhds_iff.mp
    (((((hevΛ.and hevR).and hevψd).and hevXd).and hevU).and hevSgn)
  refine ⟨V, hVopen.mem_nhds hVz₀, G, ?_, fun z hz => ?_⟩
  · exact fun z hz =>
      ((hVmem z hz).1.1.1.2.comp z (hVmem z hz).1.1.2).differentiableWithinAt
  · obtain ⟨⟨⟨⟨⟨hGzΛ, hPGz⟩, -⟩, -⟩, hzU⟩, hsgn⟩ := hVmem z hz
    obtain ⟨hYz, hnsz, hcoordz⟩ := hcoord z hzU
    have hPGy : ℘'[L'] (G z) / 2 = Y z := by
      have h1 : (℘'[L'] (G z) / 2) ^ 2 = Y z ^ 2 := by
        have hG := (WeierstrassCurve.Affine.equation_iff _ _).mp
          (hPGz ▸ L'.equation_weierstrassP hGzΛ)
        have hY := (WeierstrassCurve.Affine.equation_iff _ _).mp hnsz.1
        simp only [L'.weierstrassCurve_a₁, L'.weierstrassCurve_a₂, L'.weierstrassCurve_a₃,
          zero_mul, add_zero] at hG hY
        exact hG.trans hY.symm
      have hfac : (℘'[L'] (G z) / 2 - Y z) * (℘'[L'] (G z) / 2 + Y z) = 0 := by
        linear_combination h1
      rcases mul_eq_zero.mp hfac with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hsgn
    rw [L'.kw_toPointHom_apply, L'.toPoint_of_notMem _ hGzΛ, hcoordz, Point.some.injEq]
    exact ⟨hPGz, hPGy⟩

theorem kw_surgehgf4_hH2_betweenCurvesHoloLift_of_affineHoloCoords
    (hH2e : KwD5BetweenCurvesCocountableAffineHoloCoords) :
    KwD5BetweenCurvesHoloLift :=
  kw_surgehgf4_hH2_betweenCurvesHoloLift_of_cocountable
    (kw_surgehgf4_hH2d_betweenCurvesCocountableHoloLift_of_affineHoloCoords hH2e)

end ModularCurve
end


section


p2m_open "WeierstrassCurve \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine \
  P2MW.S_OVERLONG_302e4807.ModularCurv\
  e AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve PeriodPair \
  P2MW.S_OVERLONG_302e4807.PeriodPair \
  Filter \
  P2MW.S_OVERLONG_302e4807.Filter"
p2m_open_scoped "PeriodPair \
  P2MW.S_OVERLONG_302e4807.PeriodPair \
  Topology \
  P2MW.S_OVERLONG_302e4807.Topology"

namespace ModularCurve

def KwD5BetweenCurvesCocountableAffineHoloCoordsWeak : Prop :=
  ∀ (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L.weierstrassCurve]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L.weierstrassCurve]
    [WeierstrassCurve.Affine.AbelTheorem L.weierstrassCurve] [L'.weierstrassCurve.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate L'.weierstrassCurve]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L'.weierstrassCurve]
    [WeierstrassCurve.Affine.AbelTheorem L'.weierstrassCurve]
    (ι'' : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι''),
    ∃ S : Set ℂ, S.Countable ∧
    ∀ z₀ ∉ S, ∃ U ∈ nhds z₀, ∃ X Y : ℂ → ℂ,
      DifferentiableOn ℂ X U ∧ DifferentiableOn ℂ Y U ∧
      ∀ z ∈ U, ∃ h, (pointMapOfPushforward ι'' hι'' hfin''
            (normFormulaAlong_of_elliptic ι'' hfin'')) (L.kw_toPointHom z)
          = Point.some (X z) (Y z) h

theorem kw_surgehgf4_hH2e_betweenCurvesCocountableAffineHoloCoords_of_weak
    (hH2f : KwD5BetweenCurvesCocountableAffineHoloCoordsWeak) :
    KwD5BetweenCurvesCocountableAffineHoloCoords := by
  intro L L' _ _ _ _ _ _ _ _ ι'' hι'' hfin''
  obtain ⟨S, hSc, hgen⟩ := hH2f L L' ι'' hι'' hfin''
  set K : Set L.weierstrassCurve.toAffine.Point :=
    {P | (pointMapOfPushforward ι'' hι'' hfin''
      (normFormulaAlong_of_elliptic ι'' hfin'')) P = 0} with hKdef
  have hKfin : K.Finite := by
    have hfin := kw_fdn2_qephod_hend10_kerPMOP_finite
      (K := ℂ) (E := L.weierstrassCurve.toAffine) (E' := L'.weierstrassCurve.toAffine)
      ι'' hι'' hfin''
    have heq : K = ((AddMonoidHom.ker (pointMapOfPushforward ι'' hι'' hfin''
        (normFormulaAlong_of_elliptic ι'' hfin''))) : Set _) := by
      ext P; simp only [hKdef, Set.mem_ofPred_eq, SetLike.mem_coe, AddMonoidHom.mem_ker]
    rw [heq]; exact Set.finite_coe_iff.mp hfin
  set S' : Set ℂ := (fun z => (2 : ℂ) * z) ⁻¹' (L.kw_toPointHom ⁻¹' K)
  have hS'c : S'.Countable :=
    (L.kw_countable_toPointHom_preimage hKfin).preimage
      (mul_right_injective₀ two_ne_zero)
  refine ⟨S ∪ S', hSc.union hS'c, fun z₀ hz₀ => ?_⟩
  have hz₀S : z₀ ∉ S := fun h => hz₀ (Or.inl h)
  have hz₀S' : z₀ ∉ S' := fun h => hz₀ (Or.inr h)
  obtain ⟨U, hU, X, Y, hXd, hYd, hcoord⟩ := hgen z₀ hz₀S
  obtain ⟨hns₀, hcoord₀⟩ := hcoord z₀ (mem_of_mem_nhds hU)
  have hYz₀ : Y z₀ ≠ 0 := by
    intro hY0
    apply hz₀S'
    change (pointMapOfPushforward ι'' hι'' hfin'' (normFormulaAlong_of_elliptic ι'' hfin''))
      (L.kw_toPointHom (2 * z₀)) = 0
    rw [two_mul, map_add, map_add, hcoord₀, add_eq_zero_iff_eq_neg, Point.neg_some,
      Point.some.injEq]
    refine ⟨rfl, ?_⟩
    rw [hY0]
    simp only [negY, L'.weierstrassCurve_a₁, L'.weierstrassCurve_a₃,
      zero_mul, _root_.neg_zero, sub_zero]
  set V := U ∩ {z | Y z ≠ 0}
  have hVnhds : V ∈ nhds z₀ :=
    Filter.inter_mem hU ((hYd.continuousOn.continuousAt hU).preimage_mem_nhds
      (isOpen_ne.mem_nhds hYz₀))
  refine ⟨V, hVnhds, X, Y, hXd.mono Set.inter_subset_left,
    hYd.mono Set.inter_subset_left, fun z hz => ?_⟩
  obtain ⟨hns, hc⟩ := hcoord z hz.1
  exact ⟨hz.2, hns, hc⟩

theorem kw_surgehgf4_hH2_betweenCurvesHoloLift_of_affineHoloCoordsWeak
    (hH2f : KwD5BetweenCurvesCocountableAffineHoloCoordsWeak) :
    KwD5BetweenCurvesHoloLift :=
  kw_surgehgf4_hH2_betweenCurvesHoloLift_of_affineHoloCoords
    (kw_surgehgf4_hH2e_betweenCurvesCocountableAffineHoloCoords_of_weak hH2f)

end ModularCurve
end


section


p2m_open "WeierstrassCurve \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_302e4807.Weierstrass\
  Curve.Affine \
  P2MW.S_OVERLONG_302e4807.ModularCurv\
  e AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_302e4807.AlgebraicCu\
  rve PeriodPair \
  P2MW.S_OVERLONG_302e4807.PeriodPair \
  Filter \
  P2MW.S_OVERLONG_302e4807.Filter \
  Polynomial \
  P2MW.S_OVERLONG_302e4807.Polynomial"

p2m_open_scoped "PeriodPair \
  P2MW.S_OVERLONG_302e4807.PeriodPair \
  Topology \
  P2MW.S_OVERLONG_302e4807.Topology \
  Polynomial.Bivariate \
  P2MW.S_OVERLONG_302e4807.Polynomial.\
  Bivariate"

namespace ModularCurve

section GeomMorphBCAtoms

universe u

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {E E' : Affine K} [E.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E] [WeierstrassCurve.Affine.AbelTheorem E]
    [E'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E']
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E']
    [WeierstrassCurve.Affine.AbelTheorem E']
variable (ι : E'.FunctionField →ₐ[K] E.FunctionField)
variable (hι : ι.toRingHom.IsIntegral)

local notation "gBC" => kw_fdn2_qephod_hend7_geomMorphBC ι hι

omit [WeierstrassCurve.IsElliptic E] [GenusOnePlaceGate.IsCentred E] [E.AbelTheorem] in
omit [DecidableEq K] [CharZero K] [E'.AbelTheorem] in
theorem kw_surgehgf4_hH2f_geomMorphBC_ne_zero (Q : E.Point)
    (hx : ι (polyToFunctionField E' X) ∈ (placeOfPoint Q).toValuationSubring) :
    gBC Q ≠ 0 := by
  intro hcon
  have hseam := kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι hι Q
  rw [hcon, Point.zero_def, placeOfPoint_zero] at hseam
  have hxmem : polyToFunctionField E' X
      ∈ ((placeOfPoint Q).restrictAlong ι hι).toValuationSubring :=
    (Place.mem_restrictAlong_iff ι hι (placeOfPoint Q)
      (polyToFunctionField E' X)).mpr hx
  rw [hseam] at hxmem
  exact InfinitePlace.not_isFinitePlace (isFinitePlace_of_mem _ hxmem)

open ModularCurve.Mmr73 in
omit [WeierstrassCurve.IsElliptic E] [GenusOnePlaceGate.IsCentred E] [E.AbelTheorem] in
omit [DecidableEq K] [CharZero K] [E'.AbelTheorem] in
theorem kw_surgehgf4_hH2f_geomMorphBC_some_coords (Q : E.Point)
    {a b : K} {hab : E'.Nonsingular a b}
    (hQ : gBC Q = Point.some a b hab)
    (hx : ι (polyToFunctionField E' X) ∈ (placeOfPoint Q).toValuationSubring)
    (hy : ι (yGen E') ∈ (placeOfPoint Q).toValuationSubring) :
    (placeOfPoint Q).evalAt (ι (polyToFunctionField E' X)) = a
      ∧ (placeOfPoint Q).evalAt (ι (yGen E')) = b := by
  have hrat : (placeOfPoint Q).IsRational :=
    (placeOfPoint Q).isRational_of_deg_eq_one (deg_placeOfPoint Q)
  have hseam := kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι hι Q
  rw [hQ, placeOfPoint_some] at hseam
  have hXsub_eq : polyToFunctionField E' X - algebraMap K E'.FunctionField a
      = algebraMap E'.CoordinateRing E'.FunctionField
          (CoordinateRing.mk E' (C (X - C a))) := by
    rw [← polyToFunctionField_C (W := E') a, ← map_sub, polyToFunctionField_apply,
      algebraMap_polynomial_eq_mk_C]
  have hXmk_ne : CoordinateRing.mk E' (C (X - C a)) ≠ 0 := by
    intro hcon
    apply polyToFunctionField_ne_zero (W := E') (Polynomial.X_sub_C_ne_zero a)
    rw [polyToFunctionField_apply, algebraMap_polynomial_eq_mk_C, hcon, _root_.map_zero]
  have hposX : 0 < (placeOfEquation hab.left).ord
      (polyToFunctionField E' X - algebraMap K E'.FunctionField a) := by
    rw [hXsub_eq, ord_placeOfEquation_pos_iff hab.left hXmk_ne,
      mk_mem_XYIdeal_iff hab.left]
    simp [Polynomial.evalEval]
  have hposwX : 0 < (placeOfPoint Q).ord
      (ι (polyToFunctionField E' X) - algebraMap K E.FunctionField a) := by
    have hmap : ι (polyToFunctionField E' X) - algebraMap K E.FunctionField a
        = ι (polyToFunctionField E' X - algebraMap K E'.FunctionField a) := by
      rw [map_sub, AlgHom.commutes]
    rw [hmap, Place.ord_restrictAlong ι hι (placeOfPoint Q), hseam]
    exact mul_pos
      (by exact_mod_cast Place.ramificationIndexAlong_pos ι hι (placeOfPoint Q))
      hposX
  have hYsub_eq : yGen E' - algebraMap K E'.FunctionField b
      = algebraMap E'.CoordinateRing E'.FunctionField
          (CoordinateRing.mk E' (Y - C (C b))) := by
    have h2 : algebraMap K E'.FunctionField b
        = algebraMap E'.CoordinateRing E'.FunctionField
            (CoordinateRing.mk E' (C (C b))) := by
      rw [← polyToFunctionField_C (W := E') b, polyToFunctionField_apply,
        algebraMap_polynomial_eq_mk_C]
    unfold yGen
    rw [h2, ← map_sub, ← map_sub]
  have hYmk_ne : CoordinateRing.mk E' (Y - C (C b)) ≠ 0 := by
    intro hcon
    have hrep : CoordinateRing.mk E' (Y - C (C b))
        = (-(C b) : K[X]) • (1 : E'.CoordinateRing)
          + (1 : K[X]) • CoordinateRing.mk E' Y := by
      rw [one_smul, Algebra.smul_def, mul_one, algebraMap_polynomial_eq_mk_C,
        map_sub, _root_.map_neg, _root_.map_neg]
      ring
    rw [hrep] at hcon
    exact one_ne_zero (CoordinateRing.smul_basis_eq_zero hcon).2
  have hposY : 0 < (placeOfEquation hab.left).ord
      (yGen E' - algebraMap K E'.FunctionField b) := by
    rw [hYsub_eq, ord_placeOfEquation_pos_iff hab.left hYmk_ne,
      mk_mem_XYIdeal_iff hab.left]
    simp [Polynomial.evalEval]
  have hposwY : 0 < (placeOfPoint Q).ord
      (ι (yGen E') - algebraMap K E.FunctionField b) := by
    have hmap : ι (yGen E') - algebraMap K E.FunctionField b
        = ι (yGen E' - algebraMap K E'.FunctionField b) := by
      rw [map_sub, AlgHom.commutes]
    rw [hmap, Place.ord_restrictAlong ι hι (placeOfPoint Q), hseam]
    exact mul_pos
      (by exact_mod_cast Place.ramificationIndexAlong_pos ι hι (placeOfPoint Q))
      hposY
  exact ⟨mmr73_cs_evalAt_eq_of_ord_sub_pos (placeOfPoint Q) hrat hx hposwX,
    mmr73_cs_evalAt_eq_of_ord_sub_pos (placeOfPoint Q) hrat hy hposwY⟩

omit [WeierstrassCurve.IsElliptic E] [GenusOnePlaceGate.IsCentred E] [E.AbelTheorem] in
omit [DecidableEq K] [IsAlgClosed K] [GenusOnePlaceGate.IsCentred E'] [E'.AbelTheorem] in
theorem kw_surgehgf4_hH2f_finite_geomMorphBC_preimage (t : E'.Point) :
    {P : E.Point | gBC P = t}.Finite := by
  have hT : {w : AlgebraicCurve.Place K E.FunctionField |
      w.restrictAlong ι hι = placeOfPoint t}.Finite := by
    let := algebraAlong ι
    have := isScalarTower_along ι
    have := isIntegral_along ι hι
    exact Place.restrict_fiber_finite (placeOfPoint t)
  refine (Set.Finite.preimage (placeOfPoint_injective (W := E)).injOn hT).subset
    fun P hP => ?_
  exact (kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι hι P).trans
    (congrArg placeOfPoint hP)

end GeomMorphBCAtoms

p2m_open "WeierstrassCurve.Affine.CoordinateRing~evalAt\
  " in
open
  _root_.P2MW.S_OVERLONG_302e4807.WeierstrassCurve.Affine.CoordinateRing
  in
theorem kw_surgehgf4_hH2f_betweenCurvesCocountableAffineHoloCoordsWeak :
    KwD5BetweenCurvesCocountableAffineHoloCoordsWeak := by
  intro L L' _ _ _ _ _ _ _ _ ι'' hι'' hfin''
  let W := L.weierstrassCurve.toAffine
  let W' := L'.weierstrassCurve.toAffine
  set ξ := ι'' (polyToFunctionField W' X) with hξdef
  set η := ι'' (yGen W') with hηdef
  set c₀ := kw_fdn2_qephod_hend7_geomMorphBC ι'' hι'' 0 with hc₀def
  obtain ⟨pξ, qξ, hqξ, hξeq⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) ξ
  obtain ⟨pη, qη, hqη, hηeq⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) η
  obtain ⟨pξ', rfl⟩ := AdjoinRoot.mk_surjective pξ
  obtain ⟨qξ', rfl⟩ := AdjoinRoot.mk_surjective qξ
  obtain ⟨pη', rfl⟩ := AdjoinRoot.mk_surjective pη
  obtain ⟨qη', rfl⟩ := AdjoinRoot.mk_surjective qη
  have hqξ0 : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qξ') ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero hqξ)
  have hqη0 : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qη') ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero hqη)
  set Tq : Set W.Point := placeOfPoint ⁻¹'
    ({v | v.ord (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qξ')) ≠ 0} ∪
     {v | v.ord (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qη')) ≠ 0})
  have hfin_ord : ∀ {f : W.FunctionField}, f ≠ 0 →
      {v : Place ℂ W.FunctionField | v.ord f ≠ 0}.Finite := by
    intro f hf
    obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := ℂ) f hf
    exact Df.support.finite_toSet.subset fun v hv => Finsupp.mem_support_iff.mpr (hDf v ▸ hv)
  have hTq_fin : Tq.Finite := Set.Finite.preimage placeOfPoint_injective.injOn
    ((hfin_ord hqξ0).union (hfin_ord hqη0))
  set Tc : Set W.Point := {P | kw_fdn2_qephod_hend7_geomMorphBC ι'' hι'' P = c₀}
    ∪ {P | kw_fdn2_qephod_hend7_geomMorphBC ι'' hι'' P = -c₀}
  have hTc_fin : Tc.Finite :=
    (kw_surgehgf4_hH2f_finite_geomMorphBC_preimage ι'' hι'' c₀).union
      (kw_surgehgf4_hH2f_finite_geomMorphBC_preimage ι'' hι'' (-c₀))
  set S : Set ℂ := (L.lattice : Set ℂ) ∪ L.kw_toPointHom ⁻¹' (Tq ∪ Tc) with hSdef
  have hSc : S.Countable := L.kw_countable_lattice.union
    (L.kw_countable_toPointHom_preimage (hTq_fin.union hTc_fin))
  refine ⟨S, hSc, fun z₀ hz₀ => ?_⟩
  simp only [hSdef, Set.mem_union, Set.mem_preimage, not_or] at hz₀
  obtain ⟨hz₀Λ, hz₀Tq, hz₀Tc⟩ := hz₀
  set A : ℂ → ℂ := fun z =>
    pξ'.evalEval (℘[L] z) (℘'[L] z / 2) / qξ'.evalEval (℘[L] z) (℘'[L] z / 2) with hAdef
  set B : ℂ → ℂ := fun z =>
    pη'.evalEval (℘[L] z) (℘'[L] z / 2) / qη'.evalEval (℘[L] z) (℘'[L] z / 2) with hBdef
  set U₁ : Set ℂ :=
    ((L.lattice : Set ℂ)ᶜ ∩ (fun z => qξ'.evalEval (℘[L] z) (℘'[L] z / 2)) ⁻¹' {0}ᶜ) ∩
    ((L.lattice : Set ℂ)ᶜ ∩ (fun z => qη'.evalEval (℘[L] z) (℘'[L] z / 2)) ⁻¹' {0}ᶜ)
    with hU₁def
  have hU₁open : IsOpen U₁ :=
    ((L.kw_differentiableOn_evalEval_wp qξ').continuousOn.isOpen_inter_preimage
      L.isClosed_lattice.isOpen_compl isOpen_compl_singleton).inter
    ((L.kw_differentiableOn_evalEval_wp qη').continuousOn.isOpen_inter_preimage
      L.isClosed_lattice.isOpen_compl isOpen_compl_singleton)
  have hU₁Λ : U₁ ⊆ (L.lattice : Set ℂ)ᶜ := fun z hz => hz.1.1
  have hAd : DifferentiableOn ℂ A U₁ :=
    ((L.kw_differentiableOn_evalEval_wp pξ').mono hU₁Λ).div
      ((L.kw_differentiableOn_evalEval_wp qξ').mono hU₁Λ) fun z hz => hz.1.2
  have hBd : DifferentiableOn ℂ B U₁ :=
    ((L.kw_differentiableOn_evalEval_wp pη').mono hU₁Λ).div
      ((L.kw_differentiableOn_evalEval_wp qη').mono hU₁Λ) fun z hz => hz.2.2
  have hgeom : ∀ z ∈ U₁, ∃ hns : W'.Nonsingular (A z) (B z),
      kw_fdn2_qephod_hend7_geomMorphBC ι'' hι'' (L.kw_toPointHom z)
        = Point.some (A z) (B z) hns := by
    intro z hz
    have hzΛ : z ∉ L.lattice := hU₁Λ hz
    have hqξz : qξ'.evalEval (℘[L] z) (℘'[L] z / 2) ≠ 0 := hz.1.2
    have hqηz : qη'.evalEval (℘[L] z) (℘'[L] z / 2) ≠ 0 := hz.2.2
    set hrs := L.equation_weierstrassP hzΛ with hrs_def
    have hplace : placeOfPoint (W := W) (L.kw_toPointHom z) = placeOfEquation hrs := by
      rw [L.kw_toPointHom_apply, L.toPoint_of_notMem _ hzΛ]; exact placeOfPoint_some _
    have hordqξ : (placeOfEquation hrs).ord
        (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qξ')) = 0 := by
      refine le_antisymm (not_lt.mp fun hlt => hqξz ?_) (ord_placeOfEquation_nonneg hrs _)
      exact (mk_mem_XYIdeal_iff hrs qξ').mp
        ((ord_placeOfEquation_pos_iff hrs (nonZeroDivisors.ne_zero hqξ)).mp hlt)
    have hordqη : (placeOfEquation hrs).ord
        (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qη')) = 0 := by
      refine le_antisymm (not_lt.mp fun hlt => hqηz ?_) (ord_placeOfEquation_nonneg hrs _)
      exact (mk_mem_XYIdeal_iff hrs qη').mp
        ((ord_placeOfEquation_pos_iff hrs (nonZeroDivisors.ne_zero hqη)).mp hlt)
    have hιinj : Function.Injective ι'' := RingHom.injective ι''.toRingHom
    have hξne : ξ ≠ 0 := fun h => polyToFunctionField_ne_zero (W := W') X_ne_zero
      (hιinj (h.trans (_root_.map_zero _).symm))
    have hyGen_ne : yGen W' ≠ 0 := by
      have hmkY : (CoordinateRing.mk W' (Polynomial.X : Polynomial ℂ[X]) :
          W'.CoordinateRing) ≠ 0 := fun h => one_ne_zero
        (CoordinateRing.smul_basis_eq_zero
        (show (0 : ℂ[X]) • (1 : W'.CoordinateRing) + (1 : ℂ[X]) • CoordinateRing.mk W' _ = 0 by
          rw [zero_smul, one_smul, zero_add]; exact h)).2
      exact (map_ne_zero_iff _ (IsFractionRing.injective W'.CoordinateRing W'.FunctionField)).mpr
        hmkY
    have hηne : η ≠ 0 := fun h => hyGen_ne (hιinj (h.trans (_root_.map_zero _).symm))
    have hpξ0 : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W pξ') ≠ 0 :=
      fun h => hξne (hξeq ▸ by rw [h, zero_div])
    have hpη0 : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W pη') ≠ 0 :=
      fun h => hηne (hηeq ▸ by rw [h, zero_div])
    have hξmem : ξ ∈ (placeOfEquation hrs).toValuationSubring := by
      refine AlgebraicCurve.Place.mem_of_ord_nonneg (placeOfEquation hrs) hξne ?_
      rw [← hξeq, (placeOfEquation hrs).ord_div hpξ0 hqξ0, hordqξ, sub_zero]
      exact ord_placeOfEquation_nonneg hrs _
    have hηmem : η ∈ (placeOfEquation hrs).toValuationSubring := by
      refine AlgebraicCurve.Place.mem_of_ord_nonneg (placeOfEquation hrs) hηne ?_
      rw [← hηeq, (placeOfEquation hrs).ord_div hpη0 hqη0, hordqη, sub_zero]
      exact ord_placeOfEquation_nonneg hrs _
    have hgm_ne : kw_fdn2_qephod_hend7_geomMorphBC ι'' hι'' (L.kw_toPointHom z) ≠ 0 :=
      kw_surgehgf4_hH2f_geomMorphBC_ne_zero ι'' hι'' _ (hplace ▸ hξmem)
    obtain ⟨a, b, hab, hgm_eq⟩ : ∃ a b hab,
        kw_fdn2_qephod_hend7_geomMorphBC ι'' hι'' (L.kw_toPointHom z)
          = Point.some a b hab := by
      rcases hP : kw_fdn2_qephod_hend7_geomMorphBC ι'' hι'' (L.kw_toPointHom z) with
        _ | ⟨a, b, hab⟩
      · exact absurd hP hgm_ne
      · exact ⟨a, b, hab, rfl⟩
    have hrat := isRational_placeOfEquation hrs
    obtain ⟨ha, hb⟩ := kw_surgehgf4_hH2f_geomMorphBC_some_coords ι'' hι'' _ hgm_eq
      (hplace ▸ hξmem) (hplace ▸ hηmem)
    rw [hplace, ← hξdef] at ha
    rw [hplace, ← hηdef] at hb
    have hAz : A z = a := by
      simp only [hAdef]
      rw [← ha, ← hξeq, (placeOfEquation hrs).evalAt_div hrat
          (isFinitePlace_placeOfEquation hrs _) hqξ0 hordqξ,
        kw_evalAt_placeOfEquation_mk hrs pξ', kw_evalAt_placeOfEquation_mk hrs qξ']
    have hBz : B z = b := by
      simp only [hBdef]
      rw [← hb, ← hηeq, (placeOfEquation hrs).evalAt_div hrat
          (isFinitePlace_placeOfEquation hrs _) hqη0 hordqη,
        kw_evalAt_placeOfEquation_mk hrs pη', kw_evalAt_placeOfEquation_mk hrs qη']
    obtain ⟨rfl, rfl⟩ : a = A z ∧ b = B z := ⟨hAz.symm, hBz.symm⟩
    exact ⟨hab, hgm_eq⟩
  have hplace₀ : placeOfPoint (W := W) (L.kw_toPointHom z₀)
      = placeOfEquation (L.equation_weierstrassP hz₀Λ) := by
    rw [L.kw_toPointHom_apply, L.toPoint_of_notMem _ hz₀Λ]; exact placeOfPoint_some _
  have hz₀Tq' := hz₀Tq; rw [show Tq = _ from rfl, Set.mem_preimage, Set.mem_union, not_or,
    Set.mem_ofPred_eq, Set.mem_ofPred_eq, not_ne_iff, not_ne_iff, hplace₀] at hz₀Tq'
  have hz₀U₁ : z₀ ∈ U₁ := by
    refine ⟨⟨hz₀Λ, fun h => ?_⟩, hz₀Λ, fun h => ?_⟩
    · exact (((ord_placeOfEquation_pos_iff (L.equation_weierstrassP hz₀Λ)
        (nonZeroDivisors.ne_zero hqξ)).mpr
        ((mk_mem_XYIdeal_iff (L.equation_weierstrassP hz₀Λ) qξ').mpr
          (Set.mem_singleton_iff.mp h))).ne' hz₀Tq'.1).elim
    · exact (((ord_placeOfEquation_pos_iff (L.equation_weierstrassP hz₀Λ)
        (nonZeroDivisors.ne_zero hqη)).mpr
        ((mk_mem_XYIdeal_iff (L.equation_weierstrassP hz₀Λ) qη').mpr
          (Set.mem_singleton_iff.mp h))).ne' hz₀Tq'.2).elim
  have hU₁nhds : U₁ ∈ nhds z₀ := hU₁open.mem_nhds hz₀U₁
  rcases hc₀cases : c₀ with _ | ⟨x₀, y₀, h₀⟩
  · refine ⟨U₁, hU₁nhds, A, B, hAd, hBd, fun z hz => ?_⟩
    obtain ⟨hns, heq⟩ := hgeom z hz
    refine ⟨hns, ?_⟩
    rw [kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub ι'' hι'' hfin'', ← hc₀def, hc₀cases,
      ← Point.zero_def, sub_zero, heq]
  · set U : Set ℂ := U₁ ∩ A ⁻¹' {x₀}ᶜ with hUdef
    have hUopen : IsOpen U := by
      have h := hAd.continuousOn.isOpen_inter_preimage hU₁open
        (isOpen_compl_singleton (x := x₀))
      rw [show U = U₁ ∩ (U₁ ∩ A ⁻¹' {x₀}ᶜ) by rw [hUdef, ← Set.inter_assoc,
        Set.inter_self]]
      exact hU₁open.inter h
    have hz₀U : z₀ ∈ U := by
      refine ⟨hz₀U₁, fun hA0 => hz₀Tc ?_⟩
      obtain ⟨hns₀, hgm₀⟩ := hgeom z₀ hz₀U₁
      have hXeq := (Point.X_eq_iff (h₁ := hns₀) (h₂ := h₀)).mp (Set.mem_singleton_iff.mp hA0)
      rw [← hgm₀, ← hc₀cases] at hXeq
      exact hXeq.imp id id
    set ℓ : ℂ → ℂ := fun z => W'.slope (A z) x₀ (B z) (W'.negY x₀ y₀) with hℓdef
    set X' : ℂ → ℂ := fun z => W'.addX (A z) x₀ (ℓ z) with hX'def
    set Y' : ℂ → ℂ := fun z => W'.addY (A z) x₀ (B z) (ℓ z) with hY'def
    have hℓd : DifferentiableOn ℂ ℓ U :=
      ((((hBd.mono Set.inter_subset_left).sub (differentiableOn_const _)).div
        ((hAd.mono Set.inter_subset_left).sub (differentiableOn_const _))
        fun z hz => sub_ne_zero.mpr hz.2) :
          DifferentiableOn ℂ (fun z => (B z - W'.negY x₀ y₀) / (A z - x₀)) U).congr
        fun z hz => slope_of_X_ne hz.2
    have hX'd : DifferentiableOn ℂ X' U :=
      ((((hℓd.pow 2).add ((differentiableOn_const W'.a₁).mul hℓd)).sub
        (((differentiableOn_const W'.a₂).add (hAd.mono Set.inter_subset_left)).add
          (differentiableOn_const x₀))) :
          DifferentiableOn ℂ (fun z => ℓ z ^ 2 + W'.a₁ * ℓ z - (W'.a₂ + A z + x₀)) U).congr
        fun z hz => by
          simp only [hX'def, addX, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
          ring
    have hY'd : DifferentiableOn ℂ Y' U :=
      ((((hℓd.mul (hX'd.sub (hAd.mono Set.inter_subset_left))).add
        (hBd.mono Set.inter_subset_left)).neg.sub
        ((differentiableOn_const W'.a₁).mul hX'd) |>.sub (differentiableOn_const W'.a₃)) :
          DifferentiableOn ℂ
            (fun z => -(ℓ z * (X' z - A z) + B z) - W'.a₁ * X' z - W'.a₃) U).congr
        fun z hz => by
          simp only [hY'def, hX'def, addY, negY, negAddY, Pi.add_apply, Pi.sub_apply,
            Pi.mul_apply, Pi.neg_apply]
    refine ⟨U, hUopen.mem_nhds hz₀U, X', Y', hX'd, hY'd, fun z hz => ?_⟩
    obtain ⟨hns, heq⟩ := hgeom z hz.1
    have hXne : A z ≠ x₀ := hz.2
    have hpeq : pointMapOfPushforward ι'' hι'' hfin''
          (normFormulaAlong_of_elliptic ι'' hfin'') (L.kw_toPointHom z)
        = Point.some (A z) (B z) hns + Point.some x₀ (W'.negY x₀ y₀)
            ((nonsingular_neg ..).mpr h₀) := by
      rw [kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub ι'' hι'' hfin'', ← hc₀def,
        hc₀cases, heq, sub_eq_add_neg, Point.neg_some]
    rw [hpeq, Point.add_of_X_ne hXne]
    exact ⟨_, rfl⟩

theorem kw_surgehgf4_hH2f_betweenCurvesHoloLift :
    KwD5BetweenCurvesHoloLift :=
  kw_surgehgf4_hH2_betweenCurvesHoloLift_of_affineHoloCoordsWeak
    kw_surgehgf4_hH2f_betweenCurvesCocountableAffineHoloCoordsWeak

end ModularCurve
end

p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg\
  " in
open _root_.WeierstrassCurve
  _root_.P2MW.S_OVERLONG_302e4807.WeierstrassCurve
  _root_.WeierstrassCurve.Affine
  _root_.P2MW.S_OVERLONG_302e4807.WeierstrassCurve.Affine
  _root_.P2MW.S_OVERLONG_302e4807.AlgebraicCurve
  in
theorem solution
    (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero)
    [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
    [GenusOnePlaceGate L.weierstrassCurve.toAffine]
    [GenusOnePlaceGate.IsCentred L.weierstrassCurve.toAffine]
    [AbelTheorem L.weierstrassCurve.toAffine]
    [GenusOnePlaceGate L'.weierstrassCurve.toAffine]
    [GenusOnePlaceGate.IsCentred L'.weierstrassCurve.toAffine]
    [AbelTheorem L'.weierstrassCurve.toAffine]
    (ι : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ] L.weierstrassCurve.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι) (hN : NormFormulaAlong ℂ ι hfin) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 0 ∈ L'.lattice ∧
      ∀ z : ℂ, L'.toPoint hL' (F z) = pointMapOfPushforward ι hι hfin hN (L.toPoint hL z) := by
  obtain ⟨F, hF, hF0, hFz⟩ := ModularCurve.kw_surgehgf4_hH2f_betweenCurvesHoloLift L L' ι hι hfin
  refine ⟨F, hF, hF0, fun z => ?_⟩
  have h := hFz z
  rw [PeriodPair.kw_toPointHom_apply, PeriodPair.kw_toPointHom_apply] at h
  exact h

end
end S_OVERLONG_302e4807
end P2MW
export P2MW.S_OVERLONG_302e4807
  (solution)

end privateSection

public section publicSection


open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve
theorem PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint
    (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero)
    [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
    [GenusOnePlaceGate L.weierstrassCurve.toAffine]
    [GenusOnePlaceGate.IsCentred L.weierstrassCurve.toAffine]
    [AbelTheorem L.weierstrassCurve.toAffine]
    [GenusOnePlaceGate L'.weierstrassCurve.toAffine]
    [GenusOnePlaceGate.IsCentred L'.weierstrassCurve.toAffine]
    [AbelTheorem L'.weierstrassCurve.toAffine]
    (ι : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ] L.weierstrassCurve.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι) (hN : NormFormulaAlong ℂ ι hfin) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 0 ∈ L'.lattice ∧
      ∀ z : ℂ, L'.toPoint hL' (F z) = pointMapOfPushforward ι hι hfin hN (L.toPoint hL z) :=
  solution L L' hL hL' ι hι hfin hN

end publicSection
