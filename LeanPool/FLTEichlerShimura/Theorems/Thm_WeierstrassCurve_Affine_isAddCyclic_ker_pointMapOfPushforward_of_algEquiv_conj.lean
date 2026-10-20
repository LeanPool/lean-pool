/-
Based on Prove2Me node
WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj
(8486e300-4d51-5173-820b-eb8a99a80e39) by Claude (2026-09-05).

Proof based on Prove2Me submission 6e56b01c-9c56-52e6-8c9b-7db76fb51146
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Mathlib.Basic.Complex.Basic
public import LeanPool.FLTEichlerShimura.Definitions.Def_Isogeny_ConditionalCurrency
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PicardGroup
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_inv
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
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
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add_v2
import LeanPool.FLTEichlerShimura.Definitions.Def_P2M_Util

/-!
# Cyclic kernel and its order transport along function-field isomorphisms

Theorem statement: `WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj`
(`8486e300-4d51-5173-820b-eb8a99a80e39`), by Claude, 2026-09-05.

Proof: submission `6e56b01c-9c56-52e6-8c9b-7db76fb51146`, by Claude, 2026-09-05 (ACCEPTED); locally
adapted.

Let $E,E',D,D'$ be affine Weierstrass curves over $\mathbb{C}$, each elliptic and each carrying the
three project structures: a `GenusOnePlaceGate` (a bijection between the group of points of the
curve and the places of its function field over $\mathbb{C}$, all of which have degree $1$), its
`IsCentred` refinement (at the place attached to a point $(x,y)$, the images in the function field
of the coordinate-ring classes of $X-x$ and of $Y-y$ lie in the nonunits of the valuation subring),
and `AbelTheorem` (a divisor of degree $0$ is principal exactly when its divisor sum vanishes). Let
$\iota : \mathbb{C}(E') \to \mathbb{C}(E)$ be a $\mathbb{C}$-algebra map whose underlying ring
homomorphism is integral, such that $\mathbb{C}(E)$ is a finite module over $\mathbb{C}(E')$ along
$\iota$ and the pushforward norm formula holds along $\iota$: for every nonzero $f \in
\mathbb{C}(E)$ and every divisor $D$ with $D(w) = \operatorname{ord}_w f$ for all places $w$ of
$\mathbb{C}(E)$, the pushforward of $D$ satisfies $(\iota_* D)(v) = \operatorname{ord}_v(N(f))$ at
every place $v$ of $\mathbb{C}(E')$. Let $e_E : \mathbb{C}(D) \simeq \mathbb{C}(E)$ and $e_{E'} :
\mathbb{C}(D') \simeq \mathbb{C}(E')$ be $\mathbb{C}$-algebra isomorphisms, and let $\iota'' :
\mathbb{C}(D') \to \mathbb{C}(D)$ be a $\mathbb{C}$-algebra map, again integral, finite and
satisfying the norm formula, which makes the square commute: $e_E(\iota''(x)) = \iota(e_{E'}(x))$
for all $x$. Here `pointMapOfPushforward` denotes the homomorphism of point groups obtained by
transporting the pushforward map on degree-zero divisor classes through the isomorphisms between
points and $\mathrm{Pic}^0$ supplied by the gates, so that $\iota$ gives a map $E(\mathbb{C}) \to
E'(\mathbb{C})$ and $\iota''$ a map $D(\mathbb{C}) \to D'(\mathbb{C})$. Assuming the kernel of the
map attached to $\iota$ is cyclic, the conclusion is that the kernel of the map attached to
$\iota''$ is cyclic as well, and that the two kernels have the same cardinality.

This is the transport statement saying that the cyclicity of the kernel of a pushforward point map,
and the order of that kernel, depend only on the function-field data up to $\mathbb{C}$-algebra
isomorphism of the source and target function fields. It feeds the step
[`WeierstrassCurve.Affine.
eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward`]
(thm.html#WeierstrassCurve.Affine.
eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward),
where a cyclic kernel of prescribed order between two complex elliptic curves is converted into the
vanishing of the corresponding modular polynomial at the pair of $j$-invariants.

## Explanation of the source proof

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj.lean

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_OVERLONG_b277e395

set_option linter.unusedVariables false

noncomputable section

section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map mk a₄ a₂ a₆ Affine.Point.some \
  Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ Affine.Point.neg_some \
  baseChange j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate Affine.AbelTheorem \
  Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing map baseChange Point.some \
  Point.some.injEq Nonsingular FunctionField Point CoordinateRing.mk equation_iff_nonsingular \
  polynomial Point.neg_some pointMapOfPushforward IsogenyEndDatum IsogenyEndDatum.pointEnd \
  isogenyEndSubring GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one deg_placeOfPoint \
  pointClass AbelTheorem genusOnePic0Equiv GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal hasPrincipalDivisors_functionField \
  natCard_ker_pointMapOfPushforward_eq_finrankAlong polyToFunctionField polyToFunctionField_C \
  algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "Polynomial IsDedekindDomain WeierstrassCurve.Affine.CoordinateRing~evalAt \
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve.Affine.CoordinateRing \
  AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_b277e395.AlgebraicCu\
  rve"
open scoped Polynomial.Bivariate

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
p2m_export "WeierstrassCurve.Affine.CoordinateRing" "XYIdeal quotientXYIdealEquiv YClass mk map \
  exists_smul_basis_eq XClass smul_basis_mul_Y isDedekindDomain exists_eq_XYIdeal \
  XYIdeal_isMaximal XYIdeal_ne_bot"
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
  P2MW.S_OVERLONG_b277e395.Weierstrass\
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
end

section
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_b277e395.AlgebraicCu\
  rve WeierstrassCurve \
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map mk a₄ a₂ a₆ Affine.Point.some \
  Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ Affine.Point.neg_some \
  baseChange j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate Affine.AbelTheorem \
  Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing map baseChange Point.some \
  Point.some.injEq Nonsingular FunctionField Point CoordinateRing.mk equation_iff_nonsingular \
  polynomial Point.neg_some pointMapOfPushforward IsogenyEndDatum IsogenyEndDatum.pointEnd \
  isogenyEndSubring GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one deg_placeOfPoint \
  pointClass AbelTheorem genusOnePic0Equiv GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal hasPrincipalDivisors_functionField \
  natCard_ker_pointMapOfPushforward_eq_finrankAlong polyToFunctionField polyToFunctionField_C \
  algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_b277e395.AlgebraicCu\
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
private theorem _root_.WeierstrassCurve.Affine.IsogenyEndDatum.pointEnd'_eq_of_seam
    (D : IsogenyEndDatum W) (g : W.Point → W.Point) (hg0 : g 0 = 0)
    (hg : ∀ P, (placeOfPoint P).restrictAlong D.ι D.hι = placeOfPoint (g P)) (P : W.Point) :
    D.pointEnd' P = g P :=
  pointEnd_eq_of_seam D _ g hg0 hg P

p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "pointEnd'_eq_of_seam"
end IsogenyEndDatum
end Affine
end WeierstrassCurve
end

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map Affine.CoordinateRing mk a₄ a₂ a₆ \
  Affine.Point.some Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ \
  Affine.Point.neg_some baseChange j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate \
  Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing map baseChange Point.some \
  Point.some.injEq Nonsingular FunctionField Point CoordinateRing.mk equation_iff_nonsingular \
  polynomial Point.neg_some pointMapOfPushforward IsogenyEndDatum IsogenyEndDatum.pointEnd \
  isogenyEndSubring GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one deg_placeOfPoint \
  pointClass AbelTheorem genusOnePic0Equiv GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal hasPrincipalDivisors_functionField \
  natCard_ker_pointMapOfPushforward_eq_finrankAlong polyToFunctionField polyToFunctionField_C \
  algebraMap_smul_basis"
end Affine
end WeierstrassCurve
p2m_open_scoped "WeierstrassCurve WeierstrassCurve.Affine" in
scoped instance WeierstrassCurve.Affine.instHasPrincipalDivisorsFunctionField_s13e2
    {F : Type*} [Field F] [CharZero F] (W : WeierstrassCurve.Affine F) :
    AlgebraicCurve.HasPrincipalDivisors F W.FunctionField :=
  WeierstrassCurve.Affine.hasPrincipalDivisors_functionField W


namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk algebraAlong \
  isScalarTower_along isIntegral_along FiniteAlong NormFormulaAlong finrankAlong \
  Divisor.pushforwardAlong Divisor.pushforwardAlong_single SeparableAlong Place.restrictInclusion \
  Place Place.ext Divisor HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective \
  Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring Place.toValuationSubring \
  Place.ofHeightOneSpectrum_injective normFormulaAlong Divisor.pushforwardAlong_pushforwardAlong'"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong inertiaDegAlong restrictInclusion ext \
  ResidueField deg adicValuation adicValuation_ne_zero ord ord_inv ord_unit_smul_zpow \
  exists_unit_mul_zpow ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' \
  algebraMap_mem' toValuationSubring mk mem_of_eval_monic_eq_zero IsRational evalAt \
  ofHeightOneSpectrum_injective evalAt_mul evalAt_inv"
end Place
end AlgebraicCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk algebraAlong \
  isScalarTower_along isIntegral_along FiniteAlong NormFormulaAlong finrankAlong \
  Divisor.pushforwardAlong Divisor.pushforwardAlong_single SeparableAlong Place.restrictInclusion \
  Place Place.ext Divisor HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective \
  Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring Place.toValuationSubring \
  Place.ofHeightOneSpectrum_injective normFormulaAlong Divisor.pushforwardAlong_pushforwardAlong'"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong inertiaDegAlong restrictInclusion ext \
  ResidueField deg adicValuation adicValuation_ne_zero ord ord_inv ord_unit_smul_zpow \
  exists_unit_mul_zpow ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' \
  algebraMap_mem' toValuationSubring mk mem_of_eval_monic_eq_zero IsRational evalAt \
  ofHeightOneSpectrum_injective evalAt_mul evalAt_inv"
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

theorem evalAt_div (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ≠ 0) (hg0 : v.ord g = 0) :
    v.evalAt (f / g) = v.evalAt f / v.evalAt g := by
  have hginv : g⁻¹ ∈ v.toValuationSubring :=
    AlgebraicCurve.Place.mem_of_ord_nonneg v (inv_ne_zero hg) (by
      rw [v.ord_inv, hg0]; exact neg_nonneg.mpr le_rfl)
  rw [div_eq_mul_inv, v.evalAt_mul hv hf hginv, v.evalAt_inv hv hg hg0, div_eq_mul_inv]

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
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map mk a₄ a₂ a₆ Affine.Point.some \
  Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ Affine.Point.neg_some \
  baseChange j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate Affine.AbelTheorem \
  Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing map baseChange Point.some \
  Point.some.injEq Nonsingular FunctionField Point CoordinateRing.mk equation_iff_nonsingular \
  polynomial Point.neg_some pointMapOfPushforward IsogenyEndDatum IsogenyEndDatum.pointEnd \
  isogenyEndSubring GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one deg_placeOfPoint \
  pointClass AbelTheorem genusOnePic0Equiv GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal hasPrincipalDivisors_functionField \
  natCard_ker_pointMapOfPushforward_eq_finrankAlong polyToFunctionField polyToFunctionField_C \
  algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"
p2m_open "WeierstrassCurve.Affine.CoordinateRing~evalAt \
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve.Affine.CoordinateRing \
  AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_b277e395.AlgebraicCu\
  rve Polynomial"
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
  _root_.P2MW.S_OVERLONG_b277e395.WeierstrassCurve
  _root_.WeierstrassCurve.Affine
  _root_.P2MW.S_OVERLONG_b277e395.WeierstrassCurve.Affine
  _root_.P2MW.S_OVERLONG_b277e395.AlgebraicCurve
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

set_option linter.unusedVariables false

section
open Complex Filter Set

p2m_open_scoped "PeriodPair \
  P2MW.S_OVERLONG_b277e395.PeriodPair"

namespace PeriodPair
p2m_export "PeriodPair" "derivWeierstrassP_neg weierstrassP_neg lattice weierstrassP_add_coe \
  lattice_eq_span_range_basis ω₁ mk g₃ ω₂ derivWeierstrassP_add_coe mem_lattice G g₂ \
  weierstrassCurve weierstrassCurve_a₁ weierstrassCurve_a₃ DiscriminantNeZero toPoint \
  toPoint_of_mem toPoint_zero toPoint_of_notMem IsUniformization jLattice scale_indep scale \
  discriminant_ne_zero isUniformization_toPoint"
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
theorem kw_toPointHom_apply (z : ℂ) :
    L.kw_toPointHom z = L.toPoint L.kw_discriminantNeZero z := rfl

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
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve.Affine \
  AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_b277e395.AlgebraicCu\
  rve PeriodPair \
  P2MW.S_OVERLONG_b277e395.PeriodPair"

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

section

p2m_open "WeierstrassCurve \
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve.Affine \
  AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_b277e395.AlgebraicCu\
  rve"

namespace ModularCurve

section ConjHelpers

variable {K : Type*} [Field K]
variable {E E' F F' : WeierstrassCurve.Affine K}

def kw_fdn2_qephod_hend21_conjSeam
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) :
    F'.FunctionField →ₐ[K] F.FunctionField :=
  (eE.symm.toAlgHom.comp ι).comp eE'.toAlgHom

theorem kw_fdn2_qephod_hend21_conjSeam_isIntegral
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral) :
    (kw_fdn2_qephod_hend21_conjSeam eE eE' ι).toRingHom.IsIntegral :=
  RingHom.IsIntegral.trans eE'.toAlgHom.toRingHom (eE.symm.toAlgHom.comp ι).toRingHom
    (RingHom.isIntegral_of_surjective _ eE'.surjective)
    (RingHom.IsIntegral.trans ι.toRingHom eE.symm.toAlgHom.toRingHom hι
      (RingHom.isIntegral_of_surjective _ eE.symm.surjective))

theorem kw_fdn2_qephod_hend21_conjSeam_finiteAlong
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hfin : FiniteAlong K ι) :
    FiniteAlong K (kw_fdn2_qephod_hend21_conjSeam eE eE' ι) := by
  have hfin' : RingHom.Finite ι.toRingHom := hfin
  have h1 : RingHom.Finite eE'.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ eE'.surjective
  have h2 : RingHom.Finite eE.symm.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ eE.symm.surjective
  have hcomp : RingHom.Finite
      (kw_fdn2_qephod_hend21_conjSeam eE eE' ι).toRingHom :=
    RingHom.Finite.comp (g := (eE.symm.toAlgHom.comp ι).toRingHom)
      (RingHom.Finite.comp (g := eE.symm.toAlgHom.toRingHom) h2 hfin') h1
  exact hcomp

theorem kw_fdn2_qephod_hend21_finrankAlong_conj
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) :
    finrankAlong K (kw_fdn2_qephod_hend21_conjSeam eE eE' ι) = finrankAlong K ι := by
  refine @Algebra.finrank_eq_of_equiv_equiv F'.FunctionField F.FunctionField _ _
    (algebraAlong (kw_fdn2_qephod_hend21_conjSeam eE eE' ι))
    E'.FunctionField E.FunctionField _ _ (algebraAlong ι)
    eE'.toRingEquiv eE.toRingEquiv (RingHom.ext fun x => ?_)
  change ι (eE' x) = eE (eE.symm (ι (eE' x)))
  exact (eE.apply_symm_apply _).symm

end ConjHelpers
end ModularCurve
end

section

section

open IsDedekindDomain

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk algebraAlong \
  isScalarTower_along isIntegral_along FiniteAlong NormFormulaAlong finrankAlong \
  Divisor.pushforwardAlong Divisor.pushforwardAlong_single SeparableAlong Place.restrictInclusion \
  Place Place.ext Divisor HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective \
  Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring Place.toValuationSubring \
  Place.ofHeightOneSpectrum_injective normFormulaAlong Divisor.pushforwardAlong_pushforwardAlong'"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

section Tower
variable {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
  [Algebra K F] [Algebra K F'] [Algebra K F'']
variable (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong inertiaDegAlong restrictInclusion ext \
  ResidueField deg adicValuation adicValuation_ne_zero ord ord_inv ord_unit_smul_zpow \
  exists_unit_mul_zpow ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' \
  algebraMap_mem' toValuationSubring mk mem_of_eval_monic_eq_zero IsRational evalAt \
  ofHeightOneSpectrum_injective evalAt_mul evalAt_inv"
end Place
p2m_open_scoped "AlgebraicCurve.Place" in
theorem Place.restrictAlong_restrictAlong (hφ : φ.toRingHom.IsIntegral)
    (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral)
    (W : Place K F'') :
    (W.restrictAlong χ hχ).restrictAlong φ hφ = W.restrictAlong (χ.comp φ) hχφ := by
  exact Place.ext (SetLike.ext fun _ => Iff.rfl)
variable (K) in
def InertiaDegComp (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) : Prop :=
  ∀ W : Place K F'',
    W.inertiaDegAlong (χ.comp φ) hχφ
      = W.inertiaDegAlong χ hχ * (W.restrictAlong χ hχ).inertiaDegAlong φ hφ
namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "pushforwardAlong pushforwardAlong_single pushforward degree \
  pushforwardAlong_pushforwardAlong'"
end Divisor
p2m_open_scoped "AlgebraicCurve.Divisor" in
theorem Divisor.pushforwardAlong_pushforwardAlong (hφ : φ.toRingHom.IsIntegral)
    (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral)
    (hf : InertiaDegComp K φ χ hφ hχ hχφ) (D : Divisor K F'') :
    Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong χ hχ D)
      = Divisor.pushforwardAlong (χ.comp φ) hχφ D := by
  have key : (Divisor.pushforwardAlong φ hφ).comp (Divisor.pushforwardAlong χ hχ)
      = Divisor.pushforwardAlong (χ.comp φ) hχφ := by
    refine Finsupp.addHom_ext fun W n => ?_
    change Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong χ hχ (Finsupp.single W n))
        = Divisor.pushforwardAlong (χ.comp φ) hχφ (Finsupp.single W n)
    rw [Divisor.pushforwardAlong_single, Divisor.pushforwardAlong_single,
      Divisor.pushforwardAlong_single, Place.restrictAlong_restrictAlong φ χ hφ hχ hχφ, hf W]
    refine congrArg (Finsupp.single _) ?_
    push_cast
    ring
  exact DFunLike.congr_fun key D

end Tower
end AlgebraicCurve
end

section

section

open IsDedekindDomain

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk algebraAlong \
  isScalarTower_along isIntegral_along FiniteAlong NormFormulaAlong finrankAlong \
  Divisor.pushforwardAlong Divisor.pushforwardAlong_single SeparableAlong Place.restrictInclusion \
  Place Place.ext Divisor HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective \
  Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring Place.toValuationSubring \
  Place.ofHeightOneSpectrum_injective normFormulaAlong Divisor.pushforwardAlong_pushforwardAlong'"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

section InertiaTower

variable {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
  [Algebra K F] [Algebra K F'] [Algebra K F'']

namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong inertiaDegAlong restrictInclusion ext \
  ResidueField deg adicValuation adicValuation_ne_zero ord ord_inv ord_unit_smul_zpow \
  exists_unit_mul_zpow ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' \
  algebraMap_mem' toValuationSubring mk mem_of_eval_monic_eq_zero IsRational evalAt \
  ofHeightOneSpectrum_injective evalAt_mul evalAt_inv"
p2m_open "AlgebraicCurve.Place~ord_nonneg_of_mem~mem_of_ord_nonneg~mem_iff_ord_nonneg"

def restrictInclusionAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    (w.restrictAlong φ hφ).toValuationSubring →+* w.toValuationSubring :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  Place.restrictInclusion F w

scoped instance (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    IsLocalHom (restrictInclusionAlong φ hφ w) := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  exact inferInstanceAs (IsLocalHom (Place.restrictInclusion F w))

def restrictResidueMapAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') : (w.restrictAlong φ hφ).ResidueField →+* w.ResidueField :=
  IsLocalRing.ResidueField.map (restrictInclusionAlong φ hφ w)

variable (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')

theorem inertiaDegAlong_comp (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) :
    InertiaDegComp K φ χ hφ hχ hχφ := by
  intro W
  set w : Place K F' := W.restrictAlong χ hχ with hw
  let iA : Algebra (W.restrictAlong (χ.comp φ) hχφ).ResidueField W.ResidueField :=
    (restrictResidueMapAlong (χ.comp φ) hχφ W).toAlgebra
  let iB : Algebra w.ResidueField W.ResidueField :=
    (restrictResidueMapAlong χ hχ W).toAlgebra
  let iC : Algebra (W.restrictAlong (χ.comp φ) hχφ).ResidueField w.ResidueField :=
    (restrictResidueMapAlong φ hφ w).toAlgebra
  have : IsScalarTower (W.restrictAlong (χ.comp φ) hχφ).ResidueField
      w.ResidueField W.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change restrictResidueMapAlong (χ.comp φ) hχφ W (IsLocalRing.residue _ a)
      = restrictResidueMapAlong χ hχ W
          (restrictResidueMapAlong φ hφ w (IsLocalRing.residue _ a))
    rw [restrictResidueMapAlong, restrictResidueMapAlong, restrictResidueMapAlong,
      IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue]
    exact congrArg _ (Subtype.ext rfl)
  change Module.finrank (W.restrictAlong (χ.comp φ) hχφ).ResidueField W.ResidueField
    = Module.finrank w.ResidueField W.ResidueField
        * Module.finrank (W.restrictAlong (χ.comp φ) hχφ).ResidueField w.ResidueField
  rw [← Module.finrank_mul_finrank
    (W.restrictAlong (χ.comp φ) hχφ).ResidueField w.ResidueField W.ResidueField]
  exact Nat.mul_comm _ _

private theorem _root_.AlgebraicCurve.Divisor.pushforwardAlong_pushforwardAlong'
    (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) (D : Divisor K F'') :
    Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong χ hχ D)
      = Divisor.pushforwardAlong (χ.comp φ) hχφ D :=
  Divisor.pushforwardAlong_pushforwardAlong φ χ hφ hχ hχφ
    (inertiaDegAlong_comp φ χ hφ hχ hχφ) D

end Place
end InertiaTower

section JointFiber

variable {K F F₁ F₂ Z : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z]
  [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z]

namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong inertiaDegAlong restrictInclusion ext \
  ResidueField deg adicValuation adicValuation_ne_zero ord ord_inv ord_unit_smul_zpow \
  exists_unit_mul_zpow ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' \
  algebraMap_mem' toValuationSubring mk mem_of_eval_monic_eq_zero IsRational evalAt \
  ofHeightOneSpectrum_injective evalAt_mul evalAt_inv"
end Place
end JointFiber
end AlgebraicCurve
end

section

section


p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_b277e395.AlgebraicCu\
  rve WeierstrassCurve \
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map mk a₄ a₂ a₆ Affine.Point.some \
  Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ Affine.Point.neg_some \
  baseChange j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate Affine.AbelTheorem \
  Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing map baseChange Point.some \
  Point.some.injEq Nonsingular FunctionField Point CoordinateRing.mk equation_iff_nonsingular \
  polynomial Point.neg_some pointMapOfPushforward IsogenyEndDatum IsogenyEndDatum.pointEnd \
  isogenyEndSubring GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one deg_placeOfPoint \
  pointClass AbelTheorem genusOnePic0Equiv GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal hasPrincipalDivisors_functionField \
  natCard_ker_pointMapOfPushforward_eq_finrankAlong polyToFunctionField polyToFunctionField_C \
  algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

namespace IsogenyEndDatum
p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "pointEnd pointEnd_apply pointEnd_eq_of_seam \
  hfin hι mk ι"
p2m_open "WeierstrassCurve.Affine.IsogenyEndDatum"

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem isIntegral_algHomId :
    (AlgHom.id F W.FunctionField).toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ Function.surjective_id

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem finiteAlong_algHomId : FiniteAlong F (AlgHom.id F W.FunctionField) := by
  unfold FiniteAlong algebraAlong
  exact Module.Finite.self _

def idDatum : IsogenyEndDatum W where
  ι := AlgHom.id F W.FunctionField
  hι := isIntegral_algHomId W
  hfin := finiteAlong_algHomId W

omit [DecidableEq F] [IsAlgClosed F] [CharZero F] [WeierstrassCurve.IsElliptic W]
  [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W] [W.AbelTheorem] in
theorem restrictAlong_algHomId (w : AlgebraicCurve.Place F W.FunctionField) :
    w.restrictAlong (AlgHom.id F W.FunctionField) (isIntegral_algHomId W) = w :=
  AlgebraicCurve.Place.ext (SetLike.ext fun _ => Iff.rfl)

omit [GenusOnePlaceGate.IsCentred W] in
omit [IsAlgClosed F] [WeierstrassCurve.IsElliptic W] in
theorem idDatum_pointEnd : (idDatum W).pointEnd' = 1 := by
  refine AddMonoidHom.ext fun P => ?_
  exact (idDatum W).pointEnd'_eq_of_seam id rfl (fun Q => restrictAlong_algHomId W _) P
end IsogenyEndDatum
namespace IsogenyEndDatum
p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "pointEnd pointEnd_apply pointEnd_eq_of_seam \
  hfin hι mk ι"
end IsogenyEndDatum
end Affine
end WeierstrassCurve
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map mk a₄ a₂ a₆ Affine.Point.some \
  Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ Affine.Point.neg_some \
  baseChange j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate Affine.AbelTheorem \
  Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
p2m_open "WeierstrassCurve"
section JNonIntBridge
variable (W : WeierstrassCurve ℚ) [W.IsElliptic]
  {K : Type*} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
local instance instIsEllipticBaseChangeJNonInt :
    ((W : WeierstrassCurve ℚ).baseChange K).IsElliptic :=
  inferInstanceAs (((W : WeierstrassCurve ℚ).map (algebraMap ℚ K)).IsElliptic)
end JNonIntBridge
end WeierstrassCurve
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map mk a₄ a₂ a₆ Affine.Point.some \
  Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ Affine.Point.neg_some \
  baseChange j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate Affine.AbelTheorem \
  Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
p2m_open "WeierstrassCurve"
section BridgeOrdering
variable (W : WeierstrassCurve ℚ) [W.IsElliptic]
  {K : Type*} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
local instance instIsEllipticBaseChangeBridgeOrd :
    ((W : WeierstrassCurve ℚ).baseChange K).IsElliptic :=
  inferInstanceAs (((W : WeierstrassCurve ℚ).map (algebraMap ℚ K)).IsElliptic)
end BridgeOrdering
end WeierstrassCurve
end

section

section


p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_b277e395.AlgebraicCu\
  rve WeierstrassCurve \
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve.Affine"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk algebraAlong \
  isScalarTower_along isIntegral_along FiniteAlong NormFormulaAlong finrankAlong \
  Divisor.pushforwardAlong Divisor.pushforwardAlong_single SeparableAlong Place.restrictInclusion \
  Place Place.ext Divisor HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective \
  Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring Place.toValuationSubring \
  Place.ofHeightOneSpectrum_injective normFormulaAlong Divisor.pushforwardAlong_pushforwardAlong'"
namespace Pic0
p2m_export "AlgebraicCurve.Pic0" "pushforwardAlongHom pushforwardAlongHom_mk mk mk_surjective"
p2m_open "AlgebraicCurve.Pic0 \
  AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

variable {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
variable [Algebra K F] [Algebra K F'] [Algebra K F'']
variable (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
variable (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
variable (hχφ : (χ.comp φ).toRingHom.IsIntegral)
variable (hfinφ : FiniteAlong K φ) (hfinχ : FiniteAlong K χ) (hfinχφ : FiniteAlong K (χ.comp φ))
variable (hNφ : NormFormulaAlong K φ hfinφ) (hNχ : NormFormulaAlong K χ hfinχ)
variable (hNχφ : NormFormulaAlong K (χ.comp φ) hfinχφ)

theorem pushforwardAlongHom_comp_apply (c : Pic0 K F'') :
    Pic0.pushforwardAlongHom (χ.comp φ) hχφ hfinχφ hNχφ c
      = Pic0.pushforwardAlongHom φ hφ hfinφ hNφ
          (Pic0.pushforwardAlongHom χ hχ hfinχ hNχ c) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk]
  exact congrArg Pic0.mk (Subtype.ext
    (Divisor.pushforwardAlong_pushforwardAlong' φ χ hφ hχ hχφ D).symm)

end Pic0
end AlgebraicCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map mk a₄ a₂ a₆ Affine.Point.some \
  Affine.Point.some.injEq reduction IsIntegral toAffine Affine.Point Δ Affine.Point.neg_some \
  baseChange j Affine.IsogenyEndDatum Affine.GenusOnePlaceGate Affine.AbelTheorem \
  Affine.GenusOnePlaceGate.IsCentred Affine.hasPrincipalDivisors_functionField"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing map baseChange Point.some \
  Point.some.injEq Nonsingular FunctionField Point CoordinateRing.mk equation_iff_nonsingular \
  polynomial Point.neg_some pointMapOfPushforward IsogenyEndDatum IsogenyEndDatum.pointEnd \
  isogenyEndSubring GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one deg_placeOfPoint \
  pointClass AbelTheorem genusOnePic0Equiv GenusOnePlaceGate.deg_eq_one \
  GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum \
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain \
  CoordinateRing.exists_eq_XYIdeal hasPrincipalDivisors_functionField \
  natCard_ker_pointMapOfPushforward_eq_finrankAlong polyToFunctionField polyToFunctionField_C \
  algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

namespace IsogenyEndDatum
p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "pointEnd pointEnd_apply pointEnd_eq_of_seam \
  hfin hι mk ι"
end IsogenyEndDatum
end Affine
end WeierstrassCurve
end

section


section

p2m_open_scoped "PeriodPair \
  P2MW.S_OVERLONG_b277e395.PeriodPair \
  UpperHalfPlane MatrixGroups"
p2m_open "PeriodPair \
  P2MW.S_OVERLONG_b277e395.PeriodPair \
  Polynomial QuaternionAlgebra \
  P2MW.S_OVERLONG_b277e395.ModularCurv\
  e"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_b277e395.AlgebraicCu\
  rve WeierstrassCurve \
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve.Affine Matrix"

namespace ModularCurve

def KwD5BetweenCurvesPMOPConjKerEquiv : Prop :=
  ∀ (E E' : WeierstrassCurve.Affine ℂ) [E.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E] [WeierstrassCurve.Affine.AbelTheorem E]
    [E'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E']
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E']
    [WeierstrassCurve.Affine.AbelTheorem E']
    (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι)
    (L L' : PeriodPair) [L.weierstrassCurve.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate L.weierstrassCurve]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L.weierstrassCurve]
    [WeierstrassCurve.Affine.AbelTheorem L.weierstrassCurve] [L'.weierstrassCurve.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate L'.weierstrassCurve]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L'.weierstrassCurve]
    [WeierstrassCurve.Affine.AbelTheorem L'.weierstrassCurve]
    (eE : L.weierstrassCurve.toAffine.FunctionField ≃ₐ[ℂ] E.FunctionField)
    (eE' : L'.weierstrassCurve.toAffine.FunctionField ≃ₐ[ℂ] E'.FunctionField),
    let ι'' := kw_fdn2_qephod_hend21_conjSeam eE eE' ι
    ∀ (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι''),
    IsAddCyclic (AddMonoidHom.ker (pointMapOfPushforward ι hι hfin
        (normFormulaAlong_of_elliptic ι hfin))) →
    IsAddCyclic (AddMonoidHom.ker (pointMapOfPushforward ι'' hι'' hfin''
        (normFormulaAlong_of_elliptic ι'' hfin'')))
end ModularCurve
end
end

section


section

namespace ModularCurve

p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_b277e395.AlgebraicCu\
  rve"

section Engines

variable {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
variable [Algebra K F] [Algebra K F'] [Algebra K F'']

theorem finiteAlong_comp {φ : F →ₐ[K] F'} {ψ : F' →ₐ[K] F''}
    (hφ : FiniteAlong K φ) (hψ : FiniteAlong K ψ) : FiniteAlong K (ψ.comp φ) := by
  let := algebraAlong φ
  let := algebraAlong ψ
  let := algebraAlong (ψ.comp φ)
  have : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite F F' := hφ
  have : Module.Finite F' F'' := hψ
  exact Module.Finite.trans F' F''

end Engines
end ModularCurve
end
end

section

p2m_open_scoped "PeriodPair \
  P2MW.S_OVERLONG_b277e395.PeriodPair \
  UpperHalfPlane MatrixGroups"
p2m_open "PeriodPair \
  P2MW.S_OVERLONG_b277e395.PeriodPair \
  Polynomial QuaternionAlgebra \
  P2MW.S_OVERLONG_b277e395.ModularCurv\
  e"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg \
  P2MW.S_OVERLONG_b277e395.AlgebraicCu\
  rve WeierstrassCurve \
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve WeierstrassCurve.Affine \
  P2MW.S_OVERLONG_b277e395.Weierstrass\
  Curve.Affine Matrix"

section


namespace ModularCurve

section PMOPComp

variable {W₁ W₂ W₃ : WeierstrassCurve.Affine ℂ}
  [W₁.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W₁]
  [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W₁] [WeierstrassCurve.Affine.AbelTheorem W₁]
  [W₂.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W₂]
  [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W₂] [WeierstrassCurve.Affine.AbelTheorem W₂]
  [W₃.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W₃]
  [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W₃] [WeierstrassCurve.Affine.AbelTheorem W₃]

omit [GenusOnePlaceGate.IsCentred W₁] [GenusOnePlaceGate.IsCentred W₂]
  [GenusOnePlaceGate.IsCentred W₃] in
omit [WeierstrassCurve.IsElliptic W₁] [WeierstrassCurve.IsElliptic W₂]
  [WeierstrassCurve.IsElliptic W₃] in
theorem kw_surgehgf4_pck_pmop_comp_apply
    (φ : W₂.FunctionField →ₐ[ℂ] W₃.FunctionField)
    (χ : W₁.FunctionField →ₐ[ℂ] W₂.FunctionField)
    (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hφχ : (φ.comp χ).toRingHom.IsIntegral)
    (hfinφ : FiniteAlong ℂ φ) (hfinχ : FiniteAlong ℂ χ)
    (hfinφχ : FiniteAlong ℂ (φ.comp χ)) (P : W₃.Point) :
    pointMapOfPushforward (φ.comp χ) hφχ hfinφχ
        (normFormulaAlong_of_elliptic (φ.comp χ) hfinφχ) P
      = pointMapOfPushforward χ hχ hfinχ (normFormulaAlong_of_elliptic χ hfinχ)
          (pointMapOfPushforward φ hφ hfinφ (normFormulaAlong_of_elliptic φ hfinφ) P) := by
  change genusOnePic0Equiv W₁ (Pic0.pushforwardAlongHom (φ.comp χ) _ _ _
        ((genusOnePic0Equiv W₃).symm P))
    = genusOnePic0Equiv W₁ (Pic0.pushforwardAlongHom χ _ _ _
        ((genusOnePic0Equiv W₂).symm
          (genusOnePic0Equiv W₂ (Pic0.pushforwardAlongHom φ _ _ _
            ((genusOnePic0Equiv W₃).symm P)))))
  rw [AddEquiv.symm_apply_apply]
  exact congrArg (genusOnePic0Equiv W₁)
    (Pic0.pushforwardAlongHom_comp_apply χ φ hχ hφ hφχ hfinχ hfinφ hfinφχ
      (normFormulaAlong_of_elliptic χ hfinχ) (normFormulaAlong_of_elliptic φ hfinφ)
      (normFormulaAlong_of_elliptic (φ.comp χ) hfinφχ)
      ((genusOnePic0Equiv W₃).symm P))

end PMOPComp

section PMOPEquiv

variable {W V : WeierstrassCurve.Affine ℂ} [W.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]
    [V.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate V]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred V] [WeierstrassCurve.Affine.AbelTheorem V]

omit [GenusOnePlaceGate.IsCentred W] in
omit [WeierstrassCurve.IsElliptic W] in
theorem kw_surgehgf4_pck_pmop_id
    (hι : (AlgHom.id ℂ W.FunctionField).toRingHom.IsIntegral)
    (hfin : FiniteAlong ℂ (AlgHom.id ℂ W.FunctionField)) (P : W.Point) :
    pointMapOfPushforward (AlgHom.id ℂ W.FunctionField) hι hfin
        (normFormulaAlong_of_elliptic _ hfin) P = P := by
  have h := IsogenyEndDatum.idDatum_pointEnd W
  calc pointMapOfPushforward (AlgHom.id ℂ W.FunctionField) hι hfin
          (normFormulaAlong_of_elliptic _ hfin) P
      = (IsogenyEndDatum.idDatum W).pointEnd' P := rfl
    _ = P := by rw [h]; rfl

omit [WeierstrassCurve.IsElliptic W] [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W]
  [W.AbelTheorem] [WeierstrassCurve.IsElliptic V] [V.GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred V] [V.AbelTheorem] in
theorem kw_surgehgf4_pck_algEquiv_isIntegral
    (e : W.FunctionField ≃ₐ[ℂ] V.FunctionField) :
    e.toAlgHom.toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ e.surjective

omit [WeierstrassCurve.IsElliptic W] [W.GenusOnePlaceGate] [GenusOnePlaceGate.IsCentred W]
  [W.AbelTheorem] [WeierstrassCurve.IsElliptic V] [V.GenusOnePlaceGate]
  [GenusOnePlaceGate.IsCentred V] [V.AbelTheorem] in
theorem kw_surgehgf4_pck_algEquiv_finiteAlong
    (e : W.FunctionField ≃ₐ[ℂ] V.FunctionField) :
    FiniteAlong ℂ (e.toAlgHom (R := ℂ)) := by
  change @Module.Finite W.FunctionField V.FunctionField _ _ (algebraAlong e.toAlgHom).toModule
  let := algebraAlong e.toAlgHom
  exact Module.Finite.of_surjective
    (Algebra.linearMap W.FunctionField V.FunctionField) e.surjective

omit [GenusOnePlaceGate.IsCentred W] [GenusOnePlaceGate.IsCentred V] in
omit [WeierstrassCurve.IsElliptic W] [WeierstrassCurve.IsElliptic V] in
theorem kw_surgehgf4_pck_pmop_congr
    {ι ι' : W.FunctionField →ₐ[ℂ] V.FunctionField} (h : ι = ι')
    {hι : ι.toRingHom.IsIntegral} {hfin : FiniteAlong ℂ ι}
    {hι' : ι'.toRingHom.IsIntegral} {hfin' : FiniteAlong ℂ ι'} (P : V.Point) :
    pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic ι hfin) P
      = pointMapOfPushforward ι' hι' hfin' (normFormulaAlong_of_elliptic ι' hfin') P := by
  subst h; rfl

omit [GenusOnePlaceGate.IsCentred V] in
omit [WeierstrassCurve.IsElliptic V] in
omit [GenusOnePlaceGate.IsCentred W] in
omit [WeierstrassCurve.IsElliptic W] in
theorem kw_surgehgf4_pck_pmop_equiv_left_inv
    (e : W.FunctionField ≃ₐ[ℂ] V.FunctionField) (P : W.Point) :
    pointMapOfPushforward e.toAlgHom
        (kw_surgehgf4_pck_algEquiv_isIntegral e)
        (kw_surgehgf4_pck_algEquiv_finiteAlong e)
        (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong e))
        (pointMapOfPushforward e.symm.toAlgHom
          (kw_surgehgf4_pck_algEquiv_isIntegral e.symm)
          (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)
          (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)) P)
      = P := by
  have heq : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id ℂ W.FunctionField :=
    AlgHom.ext fun x => e.symm_apply_apply x
  have hι'' : (e.symm.toAlgHom.comp e.toAlgHom).toRingHom.IsIntegral :=
    heq ▸ (IsogenyEndDatum.idDatum W).hι
  have hfin'' : FiniteAlong ℂ (e.symm.toAlgHom.comp e.toAlgHom) :=
    heq ▸ (IsogenyEndDatum.idDatum W).hfin
  have hcomp := kw_surgehgf4_pck_pmop_comp_apply e.symm.toAlgHom e.toAlgHom
    (kw_surgehgf4_pck_algEquiv_isIntegral e.symm)
    (kw_surgehgf4_pck_algEquiv_isIntegral e) hι''
    (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)
    (kw_surgehgf4_pck_algEquiv_finiteAlong e) hfin'' P
  rw [← hcomp,
    kw_surgehgf4_pck_pmop_congr heq (hι' := (IsogenyEndDatum.idDatum W).hι)
      (hfin' := (IsogenyEndDatum.idDatum W).hfin) P]
  exact kw_surgehgf4_pck_pmop_id (IsogenyEndDatum.idDatum W).hι
    (IsogenyEndDatum.idDatum W).hfin P

omit [GenusOnePlaceGate.IsCentred W] in
omit [WeierstrassCurve.IsElliptic W] in
omit [GenusOnePlaceGate.IsCentred V] in
omit [WeierstrassCurve.IsElliptic V] in
theorem kw_surgehgf4_pck_pmop_equiv_right_inv
    (e : W.FunctionField ≃ₐ[ℂ] V.FunctionField) (P : V.Point) :
    pointMapOfPushforward e.symm.toAlgHom
        (kw_surgehgf4_pck_algEquiv_isIntegral e.symm)
        (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)
        (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm))
        (pointMapOfPushforward e.toAlgHom
          (kw_surgehgf4_pck_algEquiv_isIntegral e)
          (kw_surgehgf4_pck_algEquiv_finiteAlong e)
          (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong e)) P)
      = P := by
  have h := kw_surgehgf4_pck_pmop_equiv_left_inv e.symm P
  rw [kw_surgehgf4_pck_pmop_congr
      (show e.symm.symm.toAlgHom = e.toAlgHom from congrArg _ e.symm_symm)] at h
  exact h

omit [GenusOnePlaceGate.IsCentred W] in
omit [WeierstrassCurve.IsElliptic W] [GenusOnePlaceGate.IsCentred V] in
omit [WeierstrassCurve.IsElliptic V] in
theorem kw_surgehgf4_pck_pmop_equiv_bijective
    (e : W.FunctionField ≃ₐ[ℂ] V.FunctionField) :
    Function.Bijective (pointMapOfPushforward e.toAlgHom
        (kw_surgehgf4_pck_algEquiv_isIntegral e)
        (kw_surgehgf4_pck_algEquiv_finiteAlong e)
        (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong e))) := by
  refine ⟨?_, ?_⟩
  · intro P Q hPQ
    have := congrArg (pointMapOfPushforward e.symm.toAlgHom
      (kw_surgehgf4_pck_algEquiv_isIntegral e.symm)
      (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)
      (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm))) hPQ
    rwa [kw_surgehgf4_pck_pmop_equiv_right_inv,
      kw_surgehgf4_pck_pmop_equiv_right_inv] at this
  · intro Q
    exact ⟨pointMapOfPushforward e.symm.toAlgHom
      (kw_surgehgf4_pck_algEquiv_isIntegral e.symm)
      (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)
      (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)) Q,
      kw_surgehgf4_pck_pmop_equiv_left_inv e Q⟩

end PMOPEquiv

section ConjSeamFactor

variable {E E' F F' : WeierstrassCurve.Affine ℂ}
  [E.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E]
  [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E] [WeierstrassCurve.Affine.AbelTheorem E]
  [E'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E']
  [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E'] [WeierstrassCurve.Affine.AbelTheorem E']
  [F.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate F]
  [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred F] [WeierstrassCurve.Affine.AbelTheorem F]
  [F'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate F']
  [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred F'] [WeierstrassCurve.Affine.AbelTheorem F']
variable (eE : F.FunctionField ≃ₐ[ℂ] E.FunctionField)
  (eE' : F'.FunctionField ≃ₐ[ℂ] E'.FunctionField)
  (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField)
  (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι)

omit [GenusOnePlaceGate.IsCentred E] [GenusOnePlaceGate.IsCentred E']
  [GenusOnePlaceGate.IsCentred F] [GenusOnePlaceGate.IsCentred F'] in
omit [WeierstrassCurve.IsElliptic E] [WeierstrassCurve.IsElliptic E']
  [WeierstrassCurve.IsElliptic F] [WeierstrassCurve.IsElliptic F'] in
theorem kw_surgehgf4_pck_pmop_conjSeam_factor
    (hι'' : (kw_fdn2_qephod_hend21_conjSeam eE eE' ι).toRingHom.IsIntegral)
    (hfin'' : FiniteAlong ℂ (kw_fdn2_qephod_hend21_conjSeam eE eE' ι))
    (P : F.Point) :
    pointMapOfPushforward (kw_fdn2_qephod_hend21_conjSeam eE eE' ι) hι'' hfin''
        (normFormulaAlong_of_elliptic _ hfin'') P
      = pointMapOfPushforward eE'.toAlgHom
          (kw_surgehgf4_pck_algEquiv_isIntegral eE')
          (kw_surgehgf4_pck_algEquiv_finiteAlong eE')
          (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong eE'))
          (pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic ι hfin)
            (pointMapOfPushforward eE.symm.toAlgHom
              (kw_surgehgf4_pck_algEquiv_isIntegral eE.symm)
              (kw_surgehgf4_pck_algEquiv_finiteAlong eE.symm)
              (normFormulaAlong_of_elliptic _
                (kw_surgehgf4_pck_algEquiv_finiteAlong eE.symm)) P)) := by
  have h1 := kw_surgehgf4_pck_pmop_comp_apply
    (eE.symm.toAlgHom.comp ι) eE'.toAlgHom
    (RingHom.IsIntegral.trans ι.toRingHom eE.symm.toAlgHom.toRingHom hι
      (kw_surgehgf4_pck_algEquiv_isIntegral eE.symm))
    (kw_surgehgf4_pck_algEquiv_isIntegral eE') hι''
    (ModularCurve.finiteAlong_comp hfin (kw_surgehgf4_pck_algEquiv_finiteAlong eE.symm))
    (kw_surgehgf4_pck_algEquiv_finiteAlong eE') hfin'' P
  have h2 := kw_surgehgf4_pck_pmop_comp_apply eE.symm.toAlgHom ι
    (kw_surgehgf4_pck_algEquiv_isIntegral eE.symm) hι
    (RingHom.IsIntegral.trans ι.toRingHom eE.symm.toAlgHom.toRingHom hι
      (kw_surgehgf4_pck_algEquiv_isIntegral eE.symm))
    (kw_surgehgf4_pck_algEquiv_finiteAlong eE.symm) hfin
    (ModularCurve.finiteAlong_comp hfin (kw_surgehgf4_pck_algEquiv_finiteAlong eE.symm)) P
  calc pointMapOfPushforward (kw_fdn2_qephod_hend21_conjSeam eE eE' ι) hι'' hfin''
          (normFormulaAlong_of_elliptic _ hfin'') P
      = pointMapOfPushforward eE'.toAlgHom _ _ _
          (pointMapOfPushforward (eE.symm.toAlgHom.comp ι) _ _ _ P) := h1
    _ = _ := congrArg _ h2


omit [GenusOnePlaceGate.IsCentred E] [GenusOnePlaceGate.IsCentred F'] in
omit [WeierstrassCurve.IsElliptic E] [GenusOnePlaceGate.IsCentred E']
  [GenusOnePlaceGate.IsCentred F] [WeierstrassCurve.IsElliptic F'] in
omit [WeierstrassCurve.IsElliptic E'] [WeierstrassCurve.IsElliptic F] in
theorem kw_surgehgf4_pck_proved_core
    (hι'' : (kw_fdn2_qephod_hend21_conjSeam eE eE' ι).toRingHom.IsIntegral)
    (hfin'' : FiniteAlong ℂ (kw_fdn2_qephod_hend21_conjSeam eE eE' ι)) :
    IsAddCyclic (AddMonoidHom.ker (pointMapOfPushforward ι hι hfin
        (normFormulaAlong_of_elliptic ι hfin))) →
    IsAddCyclic (AddMonoidHom.ker (pointMapOfPushforward
        (kw_fdn2_qephod_hend21_conjSeam eE eE' ι) hι'' hfin''
        (normFormulaAlong_of_elliptic _ hfin''))) := by
  intro hcyc
  have hAbij := kw_surgehgf4_pck_pmop_equiv_bijective eE.symm
  have hBinj := (kw_surgehgf4_pck_pmop_equiv_bijective eE').injective
  have hker_iff : ∀ x : F.Point,
      x ∈ AddMonoidHom.ker (pointMapOfPushforward
          (kw_fdn2_qephod_hend21_conjSeam eE eE' ι) hι'' hfin''
          (normFormulaAlong_of_elliptic _ hfin''))
        ↔ pointMapOfPushforward eE.symm.toAlgHom
            (kw_surgehgf4_pck_algEquiv_isIntegral eE.symm)
            (kw_surgehgf4_pck_algEquiv_finiteAlong eE.symm)
            (normFormulaAlong_of_elliptic _
              (kw_surgehgf4_pck_algEquiv_finiteAlong eE.symm)) x
          ∈ AddMonoidHom.ker (pointMapOfPushforward ι hι hfin
              (normFormulaAlong_of_elliptic ι hfin)) := by
    intro x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker,
      kw_surgehgf4_pck_pmop_conjSeam_factor eE eE' ι hι hfin hι'' hfin'' x]
    exact ⟨fun h => hBinj (h.trans (map_zero _).symm),
      fun h => by rw [h, map_zero]⟩
  obtain ⟨⟨g, hg⟩⟩ := hcyc
  obtain ⟨g', hg'⟩ := hAbij.surjective (g : E.Point)
  refine ⟨⟨⟨g', (hker_iff g').mpr (hg' ▸ g.2)⟩, ?_⟩⟩
  rintro ⟨y, hy⟩
  obtain ⟨k, hk⟩ := hg ⟨_, (hker_iff y).mp hy⟩
  refine ⟨k, Subtype.ext (hAbij.injective ?_)⟩
  have hk' := congrArg Subtype.val hk
  simp only [AddSubgroup.coe_zsmul] at hk'
  calc (pointMapOfPushforward eE.symm.toAlgHom _ _ _)
          ((k • (⟨g', _⟩ : AddMonoidHom.ker _) : AddMonoidHom.ker _) : F.Point)
      = (pointMapOfPushforward eE.symm.toAlgHom _ _ _) (k • g') := by
        rw [AddSubgroup.coe_zsmul]
    _ = k • (pointMapOfPushforward eE.symm.toAlgHom _ _ _) g' := map_zsmul _ k g'
    _ = k • (g : E.Point) := by rw [hg']
    _ = _ := hk'

end ConjSeamFactor


theorem kw_surgehgf4_pck_proved : KwD5BetweenCurvesPMOPConjKerEquiv :=
  fun _ _ _ _ _ _ _ _ _ _ ι hι hfin _ _ _ _ _ _ _ _ _ _ eE eE' hι'' hfin'' =>
    kw_surgehgf4_pck_proved_core eE eE' ι hι hfin hι'' hfin''

end ModularCurve
end
end

theorem pck_s17 :
    ModularCurve.KwD5BetweenCurvesPMOPConjKerEquiv := ModularCurve.kw_surgehgf4_pck_proved

p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg\
  " in
open _root_.WeierstrassCurve
  _root_.P2MW.S_OVERLONG_b277e395.WeierstrassCurve
  _root_.WeierstrassCurve.Affine
  _root_.P2MW.S_OVERLONG_b277e395.WeierstrassCurve.Affine
  _root_.P2MW.S_OVERLONG_b277e395.AlgebraicCurve
  in
theorem solution
    (E E' D D' : WeierstrassCurve.Affine ℂ) [E.IsElliptic] [E'.IsElliptic] [D.IsElliptic]
    [D'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    [GenusOnePlaceGate D] [GenusOnePlaceGate.IsCentred D] [AbelTheorem D]
    [GenusOnePlaceGate D'] [GenusOnePlaceGate.IsCentred D'] [AbelTheorem D']
    (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong ℂ ι)
    (hN : NormFormulaAlong ℂ ι hfin)
    (eE : D.FunctionField ≃ₐ[ℂ] E.FunctionField) (eE' : D'.FunctionField ≃ₐ[ℂ] E'.FunctionField)
    (ι'' : D'.FunctionField →ₐ[ℂ] D.FunctionField) (hconj : ∀ x, eE (ι'' x) = ι (eE' x))
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι'')
    (hN'' : NormFormulaAlong ℂ ι'' hfin'')
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker) :
    IsAddCyclic (pointMapOfPushforward ι'' hι'' hfin'' hN'').ker ∧
      Nat.card (pointMapOfPushforward ι'' hι'' hfin'' hN'').ker = Nat.card (pointMapOfPushforward ι
        hι hfin hN).ker := by
  have hι''eq : ι'' = ModularCurve.kw_fdn2_qephod_hend21_conjSeam eE eE' ι := by
    apply AlgHom.ext
    intro x
    apply eE.injective
    rw [hconj x]
    change ι (eE' x) = eE (eE.symm (ι (eE' x)))
    exact (eE.apply_symm_apply _).symm
  subst hι''eq
  refine ⟨?_, ?_⟩
  · exact ModularCurve.kw_surgehgf4_pck_proved_core eE eE' ι hι hfin hι'' hfin'' hcyc
  · rw [natCard_ker_pointMapOfPushforward_eq_finrankAlong,
      natCard_ker_pointMapOfPushforward_eq_finrankAlong,
      ModularCurve.kw_fdn2_qephod_hend21_finrankAlong_conj]

end
end
end
end
end
end S_OVERLONG_b277e395
end P2MW
export P2MW.S_OVERLONG_b277e395
  (solution)

end privateSection

public section publicSection


open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve
theorem WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj
    (E E' D D' : WeierstrassCurve.Affine ℂ) [E.IsElliptic] [E'.IsElliptic] [D.IsElliptic]
    [D'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    [GenusOnePlaceGate D] [GenusOnePlaceGate.IsCentred D] [AbelTheorem D]
    [GenusOnePlaceGate D'] [GenusOnePlaceGate.IsCentred D'] [AbelTheorem D']
    (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong ℂ ι)
    (hN : NormFormulaAlong ℂ ι hfin)
    (eE : D.FunctionField ≃ₐ[ℂ] E.FunctionField) (eE' : D'.FunctionField ≃ₐ[ℂ] E'.FunctionField)
    (ι'' : D'.FunctionField →ₐ[ℂ] D.FunctionField) (hconj : ∀ x, eE (ι'' x) = ι (eE' x))
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι'')
    (hN'' : NormFormulaAlong ℂ ι'' hfin'')
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker) :
    IsAddCyclic (pointMapOfPushforward ι'' hι'' hfin'' hN'').ker ∧
      Nat.card (pointMapOfPushforward ι'' hι'' hfin'' hN'').ker = Nat.card (pointMapOfPushforward ι
        hι hfin hN).ker :=
  solution E E' D D' ι hι hfin hN eE eE' ι'' hconj hι'' hfin'' hN'' hcyc

end publicSection
