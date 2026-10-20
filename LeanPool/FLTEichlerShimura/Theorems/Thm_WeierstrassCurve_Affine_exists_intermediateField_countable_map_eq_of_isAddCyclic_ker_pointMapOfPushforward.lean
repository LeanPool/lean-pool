/-
Based on Prove2Me node
WeierstrassCurve.Affine.
exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
(0a40ab42-17dc-59b1-8b65-ce60e1b9c70a) by Claude (2026-09-05).

Proof based on Prove2Me submission 6b155adb-686e-5360-9630-4ed2fb76951c
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_Isogeny_ConditionalCurrency
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Data.Rat.Encodable
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PicardGroup
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_inv
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_normFormulaAlong
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_GenusOnePlaceGate_ext_of_isCentred
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong
import LeanPool.FLTEichlerShimura.Definitions.Def_EllipticCurve_FunctionFieldPullback
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add_v2
import LeanPool.FLTEichlerShimura.Definitions.Defs_IsogenyEndDatum_sharedLibrary
import LeanPool.FLTEichlerShimura.Definitions.Defs_WeierstrassCurve_veluSharedLibrary
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_adjoin_yCoord_eq_top

/-!
# Cyclic degree-N function-field seams descend to countable subfields

Theorem statement:
`WeierstrassCurve.Affine.
exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`
(`0a40ab42-17dc-59b1-8b65-ce60e1b9c70a`), by Claude, 2026-09-05.

Proof: submission `6b155adb-686e-5360-9630-4ed2fb76951c`, by Claude, 2026-09-05 (ACCEPTED); locally
adapted.

Let $K$ be an algebraically closed field of characteristic $0$, and let $E,E'$ be elliptic
Weierstrass curves in affine form over $K$, each equipped with a `GenusOnePlaceGate` (a bijection
between the group of points and the places of the function field over $K$, all places having degree
$1$) which is centred (for every nonsingular $(x,y)$ the images of the classes of $X-x$ and $Y-y$
lie in the nonunits of the valuation subring of the place attached to the point $(x,y)$) and
satisfying `AbelTheorem` (a divisor of degree $0$ is principal exactly when its divisor sum
vanishes). Let $\iota : K(E') \to K(E)$ be a $K$-algebra homomorphism which is integral, makes
$K(E)$ a finite module over $K(E')$, and satisfies the pushforward norm formula `NormFormulaAlong`.
Let $N \neq 0$ be a natural number and assume the kernel of the induced homomorphism
`pointMapOfPushforward` $\colon E(K) \to E'(K)$ (transport of the pushforward of degree-zero divisor
classes along the two $\mathrm{Pic}^0$ identifications) is cyclic of cardinality $N$. Then, for the
canonical $\mathbb{Q}$-algebra structure on $K$, there exist a countable intermediate field $K_0$ of
$\mathbb{Q} \subseteq K$, elliptic Weierstrass curves $E_0,E_0'$ over $K_0$ whose base changes along
$K_0 \to K$ are $E$ and $E'$ and whose base changes to $\overline{K_0}$ are elliptic, and an
integral, finite $\overline{K_0}$-algebra homomorphism $\iota_0$ from the function field of $E_0'
\times_{K_0} \overline{K_0}$ to that of $E_0 \times_{K_0} \overline{K_0}$, such that for every
choice of gate, centredness and Abel data on the two base-changed affine curves and every witness of
the pushforward norm formula for $\iota_0$, the kernel of the resulting `pointMapOfPushforward` is
cyclic of cardinality $N$.

This is the first half of the Lefschetz-principle descent: the data of a finite function-field
embedding with cyclic kernel of order $N$ is defined over a finitely generated, hence countable,
subfield of $K$, and the conclusion is stated in the form that quantifies universally over the
admissible genus-one gate data on the descended curves rather than supplying it. It feeds the
transfer to $\mathbb{C}$ used in
`eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward`
which identifies the pair of $j$-invariants as a root of the modular polynomial of level $N$.

## Explanation of the source proof

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward.lean

<!-- Generated by add_prove2me_provenance.py -->
-/

set_option maxHeartbeats 3200000

section privateSection

open WeierstrassCurve Affine CoordinateRing
  IntermediateField AlgebraicCurve Polynomial IsDedekindDomain

open scoped Polynomial.Bivariate TensorProduct

set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

noncomputable section

namespace WeierstrassCurve

namespace Affine

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

@[scoped simp]
theorem IsFinitePlace.coe_ringHom_apply {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) (r : W.CoordinateRing) :
    (hv.ringHom r : W.FunctionField) = algebraMap W.CoordinateRing W.FunctionField r := rfl

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

theorem placeOfEquation_injective {x₁ y₁ x₂ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h₂ : W.Equation x₂ y₂) (h : placeOfEquation h₁ = placeOfEquation h₂) :
    x₁ = x₂ ∧ y₁ = y₂ :=
  eq_of_XYIdeal_eq h₂
    (congrArg HeightOneSpectrum.asIdeal (S13_ofHeightOneSpectrum_injective h))

section CentredGate

variable [DecidableEq F] [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]

namespace InfinitePlace

omit [DecidableEq F] in
omit [IsDedekindDomain W.CoordinateRing] [GenusOnePlaceGate.IsCentred W] in
private theorem deg_eq_one :
    (place : AlgebraicCurve.Place F W.FunctionField).deg = 1 := by
  classical
  exact
    deg_placeOfPoint (W := W) 0

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
theorem placeOfPoint_surjective' : Function.Surjective (placeOfPoint (W := W)) := by
  classical
  exact
    (pointEquivPlace (W := W)).surjective

end CentredGate
end Affine
end WeierstrassCurve

namespace WeierstrassCurve

namespace Affine

scoped instance instHasPrincipalDivisorsFunctionField_s13 {F : Type*} [Field F] [CharZero F]
    {W : Affine F} : HasPrincipalDivisors F W.FunctionField :=
  hasPrincipalDivisors_functionField W

section AutoNorm
variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {V W : Affine F} [V.IsElliptic] [W.IsElliptic]

end AutoNorm

namespace IsogenyEndDatum

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]

omit [WeierstrassCurve.IsElliptic W] in
theorem pointEnd_eq_pointEnd' (D : IsogenyEndDatum W) (hN : NormFormulaAlong F D.ι D.hfin) :
    D.pointEnd hN = D.pointEnd' := rfl

end IsogenyEndDatum
end Affine
end WeierstrassCurve

scoped instance WeierstrassCurve.Affine.instHasPrincipalDivisorsFunctionField_s13e2
    {F : Type*} [Field F] [CharZero F] (W : WeierstrassCurve.Affine F) :
    AlgebraicCurve.HasPrincipalDivisors F W.FunctionField :=
  WeierstrassCurve.Affine.hasPrincipalDivisors_functionField W

namespace AlgebraicCurve

namespace Place

section MoreSinglePlace
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

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

namespace Affine

section FinitePlaceOfMem
variable {F : Type*} [Field F] {W : Affine F}
variable (v : AlgebraicCurve.Place F W.FunctionField)

end FinitePlaceOfMem

section RationalPlaceOfEquation
variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} [W.IsElliptic]
  [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [IsDedekindDomain W.CoordinateRing]

end RationalPlaceOfEquation
end Affine
end WeierstrassCurve

namespace ModularCurve

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

noncomputable local instance (priority := 50) s13DecEqAlgebraicClosure {K₀ : Type*} [Field K₀] :
    DecidableEq (AlgebraicClosure K₀) := Classical.decEq _

namespace WeierstrassCurve

namespace Affine

section S13GlobalGate
variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F] (W : Affine F)
    [W.IsElliptic]

theorem s13_exists_gate : ∃ (g : GenusOnePlaceGate W),
    @GenusOnePlaceGate.IsCentred F _ W g ∧ @AbelTheorem F _ _ g _ := by
  have : IsDedekindDomain W.CoordinateRing := CoordinateRing.isDedekindDomain W
  have : AlgebraicCurve.HasPrincipalDivisors F W.FunctionField :=
    hasPrincipalDivisors_functionField W
  exact exists_genusOnePlaceGate_isCentred_and_abelTheorem (W := W)

noncomputable scoped instance (priority := 50) s13GlobalGate : GenusOnePlaceGate W :=
  (s13_exists_gate W).choose
scoped instance (priority := 50) s13GlobalGate_isCentred : GenusOnePlaceGate.IsCentred W :=
  (s13_exists_gate W).choose_spec.1
scoped instance (priority := 50) s13GlobalGate_abelTheorem : AbelTheorem W := (s13_exists_gate
  W).choose_spec.2

end S13GlobalGate
end Affine
end WeierstrassCurve

namespace WeierstrassCurve

namespace Affine

section S13FiniteOverRatFunc

variable {F : Type*} [Field F] (W : Affine F)

scoped instance s13_finiteDimensional_ratFunc_functionField : FiniteDimensional (RatFunc F)
  W.FunctionField := by
  have h1 : FiniteDimensional (RatFunc F)
      (IntermediateField.adjoin (RatFunc F) {yCoord W}) :=
    IntermediateField.adjoin.finiteDimensional isIntegral_yCoord
  rw [adjoin_yCoord_eq_top] at h1
  exact (IntermediateField.topEquiv
    (F := RatFunc F) (E := W.FunctionField)).toLinearEquiv.finiteDimensional

end S13FiniteOverRatFunc
end Affine
end WeierstrassCurve

universe uK

section

namespace ModularCurve

universe u

section Setup

variable (W : WeierstrassCurve ℚ) [W.IsElliptic]
variable (F : Type u) [Field F] [Algebra ℚ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type u) [Field F'] [Algebra ℚ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower ℚ F F']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation3 "CR" => (W⁄F).toAffine.CoordinateRing
local notation3 "FF" => (W⁄F).FunctionField

def kw_coordinateRingBasis {R : Type*} [CommRing R] (V : Affine R) :
    Module.Basis (ℕ × Fin 2) R V.CoordinateRing :=
  (Polynomial.basisMonomials R).smulTower (CoordinateRing.basis V)

end Setup
end ModularCurve
end

section

namespace WeierstrassCurve

namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

end Affine
end WeierstrassCurve

namespace WeierstrassCurve

namespace Affine

variable {F : Type*} [Field F] (W : Affine F)

variable {W}

end Affine
end WeierstrassCurve

end

section

namespace ModularCurve

universe u

attribute [local instance] Classical.propDecidable

section FGFieldDescentMint

def KwD5BetweenCurvesFGFieldDescent : Prop :=
  ∀ (K : Type uK) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E] [WeierstrassCurve.Affine.AbelTheorem E]
    [E'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E']
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E']
    [WeierstrassCurve.Affine.AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)
    (N : ℕ) [NeZero N],
    IsAddCyclic (AddMonoidHom.ker
      (pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic ι hfin))) →
    Nat.card (AddMonoidHom.ker
      (pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic ι hfin))) = N →
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    ∃ (K₀ : IntermediateField ℚ K) (_ : Countable K₀)
      (E₀ E₀' : WeierstrassCurve K₀) (_ : E₀.IsElliptic) (_ : E₀'.IsElliptic)
      (_ : E₀.map (algebraMap K₀ K) = E) (_ : E₀'.map (algebraMap K₀ K) = E')
      (_ : (E₀⁄(AlgebraicClosure K₀)).IsElliptic) (_ : (E₀'⁄(AlgebraicClosure K₀)).IsElliptic)
      (ι₀ : (E₀'⁄(AlgebraicClosure K₀)).toAffine.FunctionField →ₐ[AlgebraicClosure K₀]
        (E₀⁄(AlgebraicClosure K₀)).toAffine.FunctionField)
      (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong (AlgebraicClosure K₀) ι₀),
      IsAddCyclic (AddMonoidHom.ker
        (pointMapOfPushforward ι₀ hι₀ hfin₀ (normFormulaAlong_of_elliptic ι₀ hfin₀))) ∧
      Nat.card (AddMonoidHom.ker
        (pointMapOfPushforward ι₀ hι₀ hfin₀ (normFormulaAlong_of_elliptic ι₀ hfin₀))) = N

end FGFieldDescentMint
end ModularCurve
end

section

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

namespace WeierstrassCurve

namespace Affine

universe u

variable {F : Type u} [Field F]

section GenericPoint

variable {W : Affine F}

end GenericPoint
end Affine
end WeierstrassCurve
end

section

open WeierstrassCurve.Affine.Point

section

namespace WeierstrassCurve

namespace Affine

universe u

variable {F : Type u} [Field F]

section AdjoinSurjective

variable {W : Affine F} (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

local notation "ι" => algebraMap F W.FunctionField

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

universe u

namespace WeierstrassCurve

namespace Affine

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

section

namespace ModularCurve

universe u

section SetupBCG

variable {R₀ : Type u} [Field R₀]
variable (W : WeierstrassCurve R₀) [W.IsElliptic]
variable (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [CharZero F]
variable (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']

omit [DecidableEq F] [DecidableEq F'] in
omit [W.IsElliptic] [Algebra R₀ F] [CharZero F] [CharZero F'] [IsScalarTower R₀ F F'] in
theorem kw_transcendental_polyToFunctionField_X_over_baseGeneralNoAC :
    Transcendental F (polyToFunctionField (W⁄F') X) := by
  classical
  exact
    Transcendental.of_tower_top F (L := F')
      (transcendental_polyToFunctionField_X (W := (W⁄F')))

omit [DecidableEq F] [DecidableEq F'] in
omit [W.IsElliptic] [CharZero F] [CharZero F'] in
theorem kw_equation_map_polyToFunctionField_yGen_over_baseGeneralNoAC :
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

def kw_functionFieldMapAlongGeneralNoAC : (W⁄F).FunctionField →ₐ[F] (W⁄F').FunctionField :=
  pointPullbackHomTo (kw_equation_map_polyToFunctionField_yGen_over_baseGeneralNoAC W F F')
    ((injective_iff_map_eq_zero _).mpr fun p hp =>
      transcendental_iff.mp (kw_transcendental_polyToFunctionField_X_over_baseGeneralNoAC W F F') p
        hp)

omit [DecidableEq F] [DecidableEq F'] in
omit [W.IsElliptic] [CharZero F] [CharZero F'] in
theorem kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X :
    kw_functionFieldMapAlongGeneralNoAC W F F' (polyToFunctionField (W⁄F) X)
      = polyToFunctionField (W⁄F') X := by
  classical
  exact
    pointPullbackHomTo_polyToFunctionField_X _ _

omit [DecidableEq F] [DecidableEq F'] in
omit [W.IsElliptic] [CharZero F] [CharZero F'] in
theorem kw_functionFieldMapAlongGeneralNoAC_yGen :
    kw_functionFieldMapAlongGeneralNoAC W F F' (yGen (W⁄F)) = yGen (W⁄F') := by
  classical
  exact
    pointPullbackHomTo_yGen _ _

def KwFunctionFieldTensorIsDomainGeneralNoAC : Prop :=
  IsDomain ((W⁄F).FunctionField ⊗[F] F')

attribute [local instance] Algebra.TensorProduct.rightAlgebra

scoped instance kw_isScalarTower_base_right_tensorGeneralNoAC :
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

scoped instance kw_isScalarTower_base_right_fracTensorGeneralNoAC :
    IsScalarTower R₀ F' (FractionRing ((W⁄F).FunctionField ⊗[F] F')) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    (IsScalarTower.algebraMap_apply R₀ ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F')) r).trans <|
      (congrArg (algebraMap ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F')))
        (IsScalarTower.algebraMap_apply R₀ F' ((W⁄F).FunctionField ⊗[F] F') r)).trans
      (IsScalarTower.algebraMap_apply F' ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F')) (algebraMap R₀ F' r)).symm

omit [DecidableEq F] [DecidableEq F'] in
omit [W.IsElliptic] [CharZero F] [CharZero F'] [IsDomain ((W⁄F).FunctionField ⊗[F] F')] in
theorem kw_equation_tensorFracXYGeneralNoAC :
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

omit [DecidableEq F] [DecidableEq F'] in
omit [W.IsElliptic] [CharZero F] [Algebra R₀ F'] [CharZero F'] [IsScalarTower R₀ F F']
  [IsDomain ((W⁄F).FunctionField ⊗[F] F')] in
theorem kw_transcendental_tensorFracXGeneralNoAC :
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

def kw_functionFieldTensorFracHomGeneralNoAC :
    (W⁄F').FunctionField →ₐ[F'] FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  pointPullbackHomTo (kw_equation_tensorFracXYGeneralNoAC W F F')
    (kw_transcendental_tensorFracXGeneralNoAC W F F')

omit [DecidableEq F] [DecidableEq F'] in
omit [W.IsElliptic] [CharZero F] [CharZero F'] in
theorem kw_functionFieldTensorFracHomGeneralNoAC_X :
    kw_functionFieldTensorFracHomGeneralNoAC W F F' (polyToFunctionField (W⁄F') X)
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') _
          ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')) := by
  classical
  exact
    pointPullbackHomTo_polyToFunctionField_X _ _

omit [DecidableEq F] [DecidableEq F'] in
omit [W.IsElliptic] [CharZero F] [CharZero F'] in
theorem kw_functionFieldTensorFracHomGeneralNoAC_yGen :
    kw_functionFieldTensorFracHomGeneralNoAC W F F' (yGen (W⁄F'))
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') _ ((yGen (W⁄F)) ⊗ₜ[F] (1 : F')) := by
  classical
  exact
    pointPullbackHomTo_yGen _ _

omit [DecidableEq F] [DecidableEq F'] in
omit [W.IsElliptic] [CharZero F] [CharZero F'] in
theorem kw_functionFieldTensorFracHomGeneralNoAC_bijective :
    Function.Bijective (kw_functionFieldTensorFracHomGeneralNoAC W F F') := by
  classical
  refine ⟨(kw_functionFieldTensorFracHomGeneralNoAC W F F').injective, ?_⟩
  set ψ := kw_functionFieldTensorFracHomGeneralNoAC W F F'
  have hκ : (ψ.restrictScalars F).comp (kw_functionFieldMapAlongGeneralNoAC W F F')
      = (IsScalarTower.toAlgHom F ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F'))).comp
          (Algebra.TensorProduct.includeLeft (R := F)) := by
    refine kw_functionField_algHom_ext ?_ ?_
    · change ψ (kw_functionFieldMapAlongGeneralNoAC W F F' (polyToFunctionField (W⁄F) X)) = _
      rw [kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X,
        kw_functionFieldTensorFracHomGeneralNoAC_X]
      rfl
    · change ψ (kw_functionFieldMapAlongGeneralNoAC W F F' (yGen (W⁄F))) = _
      rw [kw_functionFieldMapAlongGeneralNoAC_yGen, kw_functionFieldTensorFracHomGeneralNoAC_yGen]
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
      · exact ⟨kw_functionFieldMapAlongGeneralNoAC W F F' a, DFunLike.congr_fun hκ a⟩
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ψ.commutes,
          IsScalarTower.algebraMap_apply F' ((W⁄F).FunctionField ⊗[F] F')
            (FractionRing ((W⁄F).FunctionField ⊗[F] F')),
          Algebra.TensorProduct.right_algebraMap_apply]
  intro z
  obtain ⟨t, s, _, rfl⟩ := IsFractionRing.div_surjective
    (A := (W⁄F).FunctionField ⊗[F] F') (K := FractionRing _) z
  exact div_mem (hT_sub t) (hT_sub s)

def kw_functionFieldTensorFracEquivGeneralNoAC :
    (W⁄F').FunctionField ≃ₐ[F'] FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  AlgEquiv.ofBijective _ (kw_functionFieldTensorFracHomGeneralNoAC_bijective W F F')

end FracHom
end SetupBCG

section SetupBCGD

variable {R₀ : Type u} [Field R₀]
variable (W : WeierstrassCurve R₀) [W.IsElliptic]
variable (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [CharZero F]
variable (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section FFDomain

local notation3 "CR" => (W⁄F).toAffine.CoordinateRing
local notation3 "FFₗ" => (W⁄F).FunctionField

omit [DecidableEq F] [DecidableEq F'] in
omit [W.IsElliptic] [CharZero F] [Algebra R₀ F'] [CharZero F'] [IsScalarTower R₀ F F'] in
theorem kw_coordinateRingMap_basisGeneralNoAC (i : ℕ × Fin 2) :
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

def kw_coordinateRingMapAlongGeneralNoAC :
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

omit [DecidableEq F] [DecidableEq F'] in
omit [W.IsElliptic] [CharZero F] [Algebra R₀ F'] [CharZero F'] [IsScalarTower R₀ F F'] in
theorem kw_coordinateRingTensor_isDomainGeneralNoAC : IsDomain (CR ⊗[F] F') := by
  classical
  suffices h : IsDomain (F' ⊗[F] CR) by
    have := h
    exact Function.Injective.isDomain (Algebra.TensorProduct.comm F CR F').toRingHom
      (Algebra.TensorProduct.comm F CR F').injective
  set W'' := (W⁄F).toAffine.map (algebraMap F F') with hW''
  let θ : F' ⊗[F] CR →ₐ[F'] W''.CoordinateRing :=
    AlgHom.liftEquiv F F' CR W''.CoordinateRing (kw_coordinateRingMapAlongGeneralNoAC W F F')
  have hθ : Function.Injective θ := by
    let bT : Module.Basis (ℕ × Fin 2) F' (F' ⊗[F] CR) :=
      Algebra.TensorProduct.basis F' (kw_coordinateRingBasis (W⁄F).toAffine)
    let bD : Module.Basis (ℕ × Fin 2) F' W''.CoordinateRing := kw_coordinateRingBasis W''
    have key : ∀ i, θ.toLinearMap (bT i) = (bT.equiv bD (Equiv.refl _)) (bT i) := fun i => by
      rw [Module.Basis.equiv_apply, Equiv.refl_apply, AlgHom.toLinearMap_apply]
      simp only [bT, Algebra.TensorProduct.basis_apply, θ, AlgHom.liftEquiv_tmul, one_smul]
      exact kw_coordinateRingMap_basisGeneralNoAC W F F' i
    have heq : (θ : F' ⊗[F] CR → W''.CoordinateRing) = bT.equiv bD (Equiv.refl _) :=
      funext fun x => DFunLike.congr_fun (bT.ext key : θ.toLinearMap = _) x
    exact heq ▸ (bT.equiv bD (Equiv.refl _)).injective
  exact Function.Injective.isDomain θ.toRingHom hθ

omit [DecidableEq F] [DecidableEq F'] in
omit [W.IsElliptic] [CharZero F] [Algebra R₀ F'] [CharZero F'] [IsScalarTower R₀ F F'] in
theorem kw_functionFieldTensorIsDomain_dischargeGeneralNoAC :
    KwFunctionFieldTensorIsDomainGeneralNoAC W F F' := by
  classical
  change IsDomain (FFₗ ⊗[F] F')
  have hCR : IsDomain (CR ⊗[F] F') := kw_coordinateRingTensor_isDomainGeneralNoAC W F F'
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

end FFDomain
end SetupBCGD
end ModularCurve
end

section

namespace ModularCurve

section Carriers

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {K₀ : IntermediateField ℚ K}
variable (E₀ : WeierstrassCurve K₀) [E₀.IsElliptic]

local notation "E" => E₀.map (algebraMap K₀ K)

def kw_iA_polyDescend (p : Polynomial K) (hmem : ∀ j, p.coeff j ∈ K₀) : Polynomial K₀ :=
  ∑ j ∈ p.support, Polynomial.C (⟨p.coeff j, hmem j⟩ : K₀) * Polynomial.X ^ j

omit [DecidableEq K] in
theorem kw_iA_polyDescend_map (p : Polynomial K) (hmem : ∀ j, p.coeff j ∈ K₀) :
    (kw_iA_polyDescend p hmem).map (algebraMap K₀ K) = p := by
  classical
  unfold kw_iA_polyDescend; rw [Polynomial.map_sum]
  conv_rhs => rw [p.as_sum_support_C_mul_X_pow]
  exact Finset.sum_congr rfl fun j _ => by
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]; rfl

def kw_iA_crCoeffsIn (c : (E).toAffine.CoordinateRing) : Prop :=
  ∀ (i : Fin 2) (j : ℕ),
    ((CoordinateRing.basis (E).toAffine).repr c i).coeff j ∈ K₀

def kw_iA_crDescend (c : (E).toAffine.CoordinateRing) (hmem : kw_iA_crCoeffsIn E₀ c) :
    E₀.toAffine.CoordinateRing :=
  ∑ i : Fin 2, (kw_iA_polyDescend
      ((CoordinateRing.basis (E).toAffine).repr c i) (hmem i))
    • (CoordinateRing.basis E₀.toAffine) i

omit [DecidableEq K] in
omit [E₀.IsElliptic] in
theorem kw_iA_crDescend_map (c : (E).toAffine.CoordinateRing)
    (hmem : kw_iA_crCoeffsIn E₀ c) :
    CoordinateRing.map E₀.toAffine (algebraMap K₀ K) (kw_iA_crDescend E₀ c hmem) = c := by
  classical
  unfold kw_iA_crDescend; rw [map_sum]
  conv_rhs => rw [← (CoordinateRing.basis (E).toAffine).sum_repr c]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [CoordinateRing.map_smul]; congr 1
  · exact kw_iA_polyDescend_map _ (hmem i)
  · rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with h | h
    · exact h ▸ by rw [CoordinateRing.basis_zero, CoordinateRing.basis_zero, map_one]
    · exact h ▸ by rw [CoordinateRing.basis_one, CoordinateRing.basis_one,
        CoordinateRing.map_mk, Polynomial.map_X]

omit [DecidableEq K] in
omit [E₀.IsElliptic] in
theorem kw_iA_phiEquation :
    (E₀.map (algebraMap K₀ (E).toAffine.FunctionField)).toAffine.Equation
      (polyToFunctionField (E).toAffine X) (yGen (E).toAffine) := by
  classical
  have h : E₀.map (algebraMap K₀ (E).toAffine.FunctionField)
      = (E).map (algebraMap K (E).toAffine.FunctionField) := by
    rw [show (algebraMap K₀ (E).toAffine.FunctionField)
        = (algebraMap K (E).toAffine.FunctionField).comp (algebraMap K₀ K) from
      IsScalarTower.algebraMap_eq K₀ K (E).toAffine.FunctionField,
      ← WeierstrassCurve.map_map]
  exact h ▸ equation_map_polyToFunctionField_yGen (W := (E).toAffine)

omit [DecidableEq K] in
omit [E₀.IsElliptic] in
theorem kw_iA_phiTranscendental :
    Function.Injective
      (Polynomial.aeval (R := K₀) (polyToFunctionField (E).toAffine X)) := by
  classical
  exact
    (injective_iff_map_eq_zero _).mpr fun p hp => transcendental_iff.mp
      ((transcendental_polyToFunctionField_X (W := (E).toAffine)).restrictScalars
        (R := K₀) (algebraMap K₀ K).injective) p hp

def kw_iA_phi : E₀.toAffine.FunctionField →ₐ[K₀] (E).toAffine.FunctionField :=
  pointPullbackHomTo (kw_iA_phiEquation E₀) (kw_iA_phiTranscendental E₀)

omit [DecidableEq K] in
omit [Algebra ℚ K] in
theorem kw_iA_polyToFF_eq_aeval (W : WeierstrassCurve.Affine K) :
    polyToFunctionField W = (Polynomial.aeval (R := K) (polyToFunctionField W X)).toRingHom := by
  classical
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C,
      polyToFunctionField_apply,
      show (algebraMap (Polynomial K) W.CoordinateRing) (C c)
        = (algebraMap K W.CoordinateRing) c from
        (IsScalarTower.algebraMap_apply K (Polynomial K) W.CoordinateRing c).symm,
      ← IsScalarTower.algebraMap_apply K W.CoordinateRing W.FunctionField]
  · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]

omit [DecidableEq K] in
omit [E₀.IsElliptic] in
theorem kw_iA_phiCRCompat (c₀ : E₀.toAffine.CoordinateRing) :
    kw_iA_phi E₀ (algebraMap E₀.toAffine.CoordinateRing E₀.toAffine.FunctionField c₀)
      = algebraMap (E).toAffine.CoordinateRing (E).toAffine.FunctionField
          (CoordinateRing.map E₀.toAffine (algebraMap K₀ K) c₀) := by
  classical
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective c₀
  unfold kw_iA_phi
  rw [pointPullbackHomTo_algebraMap, CoordinateRing.map_mk]
  revert g
  suffices h : ((pointPullbackCoordHomTo (kw_iA_phiEquation E₀)).toRingHom.comp
        (CoordinateRing.mk E₀.toAffine))
      = ((algebraMap (E).toAffine.CoordinateRing (E).toAffine.FunctionField).comp
          (CoordinateRing.mk (E).toAffine)).comp
        (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap K₀ K))) by
    intro g; exact congrFun (congrArg DFunLike.coe h) g
  refine Polynomial.ringHom_ext (fun p => ?_) ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.coe_mapRingHom, Polynomial.map_C]
    rw [← algebraMap_polynomial_eq_mk_C, ← algebraMap_polynomial_eq_mk_C,
      ← polyToFunctionField_apply]
    have hlhs := congrFun (congrArg DFunLike.coe
      (pointPullbackCoordHomTo_comp_algebraMap (kw_iA_phiEquation E₀))) p
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hlhs
    rw [hlhs, show polyToFunctionField (E).toAffine (p.map (algebraMap K₀ K))
        = (Polynomial.aeval (R := K) (polyToFunctionField (E).toAffine X))
            (p.map (algebraMap K₀ K)) from
      congrFun (congrArg DFunLike.coe (kw_iA_polyToFF_eq_aeval (E).toAffine)) _]
    exact (Polynomial.aeval_map_algebraMap K (polyToFunctionField (E).toAffine X) p).symm
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.coe_mapRingHom, Polynomial.map_X]
    rw [pointPullbackCoordHomTo_mk, Polynomial.eval₂_X]; rfl

omit [DecidableEq K] in
omit [E₀.IsElliptic] in
theorem kw_iA_ffDescend_exists (x : (E).toAffine.FunctionField)
    (hnum : kw_iA_crCoeffsIn E₀
      (IsLocalization.sec (nonZeroDivisors (E).toAffine.CoordinateRing) x).1)
    (hden : kw_iA_crCoeffsIn E₀
      ((IsLocalization.sec (nonZeroDivisors (E).toAffine.CoordinateRing) x).2 :
        (E).toAffine.CoordinateRing)) :
    ∃ x₀ : E₀.toAffine.FunctionField, kw_iA_phi E₀ x₀ = x := by
  classical
  let s := IsLocalization.sec (nonZeroDivisors (E).toAffine.CoordinateRing) x
  have hdenNZ : (s.2 : (E).toAffine.CoordinateRing) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  refine ⟨algebraMap _ _ (kw_iA_crDescend E₀ s.1 hnum)
    / algebraMap _ _ (kw_iA_crDescend E₀ (↑s.2) hden), ?_⟩
  have hFFdenNZ : algebraMap (E).toAffine.CoordinateRing (E).toAffine.FunctionField
      (s.2 : (E).toAffine.CoordinateRing) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hdenNZ
  rw [map_div₀, kw_iA_phiCRCompat, kw_iA_phiCRCompat,
    kw_iA_crDescend_map E₀ s.1 hnum, kw_iA_crDescend_map E₀ _ hden,
    div_eq_iff hFFdenNZ]
  exact (IsLocalization.sec_spec (nonZeroDivisors (E).toAffine.CoordinateRing) x).symm

end Carriers

section Assembly

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {K₀ : IntermediateField ℚ K}
variable (E₀ : WeierstrassCurve K₀) [E₀.IsElliptic]

local notation "E" => E₀.map (algebraMap K₀ K)

def kw_iA_CoeffsHyp (D : IsogenyEndDatum (E).toAffine) : Prop :=
  (kw_iA_crCoeffsIn E₀ (IsLocalization.sec (nonZeroDivisors (E).toAffine.CoordinateRing)
      (D.ι (polyToFunctionField (E).toAffine X))).1
    ∧ kw_iA_crCoeffsIn E₀ ((IsLocalization.sec (nonZeroDivisors
        (E).toAffine.CoordinateRing) (D.ι (polyToFunctionField (E).toAffine X))).2 :
      (E).toAffine.CoordinateRing))
  ∧ (kw_iA_crCoeffsIn E₀ (IsLocalization.sec (nonZeroDivisors (E).toAffine.CoordinateRing)
      (D.ι (yGen (E).toAffine))).1
    ∧ kw_iA_crCoeffsIn E₀ ((IsLocalization.sec (nonZeroDivisors
        (E).toAffine.CoordinateRing) (D.ι (yGen (E).toAffine))).2 :
      (E).toAffine.CoordinateRing))

end Assembly
end ModularCurve
end

section

namespace ModularCurve

section CoeffSet

variable {K : Type uK} [Field K] [DecidableEq K]

def kw_iCa_crRepr (E : WeierstrassCurve K) (c : E.toAffine.CoordinateRing)
    (i : Fin 2) : Polynomial K :=
  (CoordinateRing.basis E.toAffine).repr c i

def kw_iCa_crCoeffSet (E : WeierstrassCurve K) (c : E.toAffine.CoordinateRing) :
    Finset K :=
  ((kw_iCa_crRepr E c 0).support.image (kw_iCa_crRepr E c 0).coeff) ∪
  ((kw_iCa_crRepr E c 1).support.image (kw_iCa_crRepr E c 1).coeff)

def kw_iCa_ffNum (E : WeierstrassCurve K) (x : E.toAffine.FunctionField) :
    E.toAffine.CoordinateRing :=
  (IsLocalization.sec (nonZeroDivisors E.toAffine.CoordinateRing) x).1

def kw_iCa_ffDen (E : WeierstrassCurve K) (x : E.toAffine.FunctionField) :
    E.toAffine.CoordinateRing :=
  ((IsLocalization.sec (nonZeroDivisors E.toAffine.CoordinateRing) x).2 :
    E.toAffine.CoordinateRing)

def kw_iCa_ffCoeffSet (E : WeierstrassCurve K) (x : E.toAffine.FunctionField) :
    Finset K :=
  kw_iCa_crCoeffSet E (kw_iCa_ffNum E x) ∪ kw_iCa_crCoeffSet E (kw_iCa_ffDen E x)

theorem kw_iCa_crRepr_coeff_mem (E : WeierstrassCurve K)
    (c : E.toAffine.CoordinateRing) (i : Fin 2) (j : ℕ) :
    (kw_iCa_crRepr E c i).coeff j ∈ (↑(kw_iCa_crCoeffSet E c) : Set K) ∪ {0} := by
  by_cases hj : j ∈ (kw_iCa_crRepr E c i).support
  · refine Or.inl ?_
    simp only [kw_iCa_crCoeffSet, Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with h | h
    · exact h ▸ Or.inl ⟨j, hj, rfl⟩
    · exact h ▸ Or.inr ⟨j, hj, rfl⟩
  · exact Or.inr (by simpa using Polynomial.notMem_support_iff.mp hj)

end CoeffSet

section Canonical

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K]
variable (E : WeierstrassCurve K) [E.IsElliptic] (D : IsogenyEndDatum E.toAffine)

theorem kw_iCa_crCoeffsIn_of_ffCoeffSet_subset (E' : WeierstrassCurve K)
    (x : E'.toAffine.FunctionField) {K₀' : IntermediateField ℚ K}
    (hsub : (↑(kw_iCa_ffCoeffSet E' x) : Set K) ⊆ K₀') (i : Fin 2) (j : ℕ) :
    ((CoordinateRing.basis E'.toAffine).repr (kw_iCa_ffNum E' x) i).coeff j ∈ K₀' ∧
    ((CoordinateRing.basis E'.toAffine).repr (kw_iCa_ffDen E' x) i).coeff j ∈ K₀' := by
  have hN := kw_iCa_crRepr_coeff_mem E' (kw_iCa_ffNum E' x) i j
  have hD := kw_iCa_crRepr_coeff_mem E' (kw_iCa_ffDen E' x) i j
  unfold kw_iCa_crRepr at hN hD
  refine ⟨?_, ?_⟩
  · rcases hN with hN | hN
    · exact hsub (by simp only [kw_iCa_ffCoeffSet, Finset.coe_union]; exact Or.inl hN)
    · simp only [Set.mem_singleton_iff] at hN; exact hN ▸ zero_mem K₀'
  · rcases hD with hD | hD
    · exact hsub (by simp only [kw_iCa_ffCoeffSet, Finset.coe_union]; exact Or.inr hD)
    · simp only [Set.mem_singleton_iff] at hD; exact hD ▸ zero_mem K₀'

end Canonical
end ModularCurve
end

section

namespace ModularCurve

section Exchange

variable {K : Type*} [Field K] (W : WeierstrassCurve.Affine K)

theorem kw_iPFA_isTranscendenceBasis_coord :
    IsTranscendenceBasis K
      (fun _ : Fin 1 => algebraMap (RatFunc K) W.FunctionField RatFunc.X) := by
  have : Algebra.IsAlgebraic (RatFunc K) (RatFunc K) :=
    Algebra.IsAlgebraic.of_finite (RatFunc K) (RatFunc K)
  have : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := Polynomial K) (K := RatFunc K) (C := RatFunc K)).mpr inferInstance
  have : FaithfulSMul (Polynomial K) (RatFunc K) :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial K) (RatFunc K)).mpr
      (IsFractionRing.injective (Polynomial K) (RatFunc K))
  have : Algebra.IsAlgebraic (RatFunc K) W.FunctionField :=
    Algebra.IsAlgebraic.of_finite (RatFunc K) W.FunctionField
  have : FaithfulSMul (RatFunc K) W.FunctionField :=
    (faithfulSMul_iff_algebraMap_injective (RatFunc K) W.FunctionField).mpr
      (algebraMap (RatFunc K) W.FunctionField).injective
  have h0 : IsTranscendenceBasis K (fun _ : Fin 1 => (Polynomial.X : Polynomial K)) :=
    IsTranscendenceBasis.polynomial (ι := Fin 1) (R := K)
  have h1 := h0.algebraMap_comp (A := RatFunc K)
  have h2 := h1.algebraMap_comp (A := W.FunctionField)
  have hfun : (algebraMap (RatFunc K) W.FunctionField ∘
      (algebraMap (Polynomial K) (RatFunc K) ∘ fun _ : Fin 1 => (Polynomial.X : Polynomial K)))
      = fun _ : Fin 1 => algebraMap (RatFunc K) W.FunctionField RatFunc.X := by
    funext i; simp only [Function.comp_apply]; rw [RatFunc.algebraMap_X]
  rwa [hfun] at h2

theorem kw_iPFA_isAlgebraic_adjoin_transcendental {g : W.FunctionField}
    (hg : Transcendental K g) :
    Algebra.IsAlgebraic (↥K⟮g⟯) W.FunctionField := by
  classical
  have hgind : AlgebraicIndepOn K id ({g} : Set W.FunctionField) := by
    refine algebraicIndependent_unique_type_iff.mpr ?_
    simpa using hg
  obtain ⟨s, hgs, hbasis⟩ := exists_isTranscendenceBasis_superset hgind
  have hcard := hbasis.lift_cardinalMk_eq (kw_iPFA_isTranscendenceBasis_coord W)
  simp only [Cardinal.mk_fin, Nat.cast_one, Cardinal.lift_one, Cardinal.lift_eq_one] at hcard
  have hsub : s.Subsingleton := Cardinal.mk_le_one_iff_set_subsingleton.mp hcard.le
  have hseq : s = {g} := hsub.eq_singleton_of_mem (hgs rfl)
  subst hseq
  rw [hbasis.isAlgebraic_iff]
  intro i
  have hi : (i : W.FunctionField) = g := i.2
  rw [hi]
  have h1 := isAlgebraic_algebraMap (R := ↥K⟮g⟯) (A := W.FunctionField)
    (IntermediateField.AdjoinSimple.gen K g)
  rwa [IntermediateField.AdjoinSimple.algebraMap_gen] at h1

theorem kw_iPFA_finiteDimensional_adjoin_transcendental {g : W.FunctionField}
    (hg : Transcendental K g) :
    FiniteDimensional (↥K⟮g⟯) W.FunctionField := by
  classical
  have halg : Algebra.IsAlgebraic (↥K⟮g⟯) W.FunctionField :=
    kw_iPFA_isAlgebraic_adjoin_transcendental W hg
  obtain ⟨s, hs⟩ :=
    Module.finite_def.mp (inferInstance : Module.Finite (RatFunc K) W.FunctionField)
  set t : W.FunctionField := algebraMap (RatFunc K) W.FunctionField RatFunc.X with ht
  set E : IntermediateField (↥K⟮g⟯) W.FunctionField :=
    IntermediateField.adjoin (↥K⟮g⟯) (insert t (↑s : Set W.FunctionField)) with hE
  have htE : t ∈ E := IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have hrange : ∀ r : RatFunc K, algebraMap (RatFunc K) W.FunctionField r ∈ E := by
    intro r
    have hr : r ∈ IntermediateField.adjoin K {(RatFunc.X : RatFunc K)} := by
      rw [RatFunc.adjoin_X]; exact IntermediateField.mem_top
    have hmap : algebraMap (RatFunc K) W.FunctionField r ∈
        (IntermediateField.adjoin K {(RatFunc.X : RatFunc K)}).map
          (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField) := ⟨r, hr, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at hmap
    have himg : (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField)
        (RatFunc.X : RatFunc K) = t := rfl
    rw [himg] at hmap
    have hle : IntermediateField.adjoin K {t} ≤ E.restrictScalars K :=
      IntermediateField.adjoin_simple_le_iff.mpr
        ((IntermediateField.mem_restrictScalars K).mpr htE)
    exact (IntermediateField.mem_restrictScalars K).mp (hle hmap)
  have hmem : ∀ x : W.FunctionField, x ∈ E := by
    intro x
    have hx : x ∈ Submodule.span (RatFunc K) (↑s : Set W.FunctionField) := by
      rw [hs]; exact Submodule.mem_top
    refine Submodule.span_induction (fun y hy => ?_) ?_ (fun y z _ _ hy hz => ?_)
      (fun r y _ hy => ?_) hx
    · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hy)
    · exact zero_mem E
    · exact add_mem hy hz
    · rw [Algebra.smul_def]
      exact mul_mem (hrange _) hy
  have heqTop : E = ⊤ := eq_top_iff.mpr (fun x _ => hmem x)
  have hfinE : FiniteDimensional (↥K⟮g⟯) (↥E) :=
    IntermediateField.finiteDimensional_adjoin
      (S := insert t (↑s : Set W.FunctionField))
      (fun z _ => isAlgebraic_iff_isIntegral.mp (halg.isAlgebraic z))
  rw [heqTop] at hfinE
  exact (IntermediateField.topEquiv (F := ↥K⟮g⟯) (E := W.FunctionField))
    |>.toLinearEquiv.finiteDimensional

end Exchange
end ModularCurve
end

section

namespace ModularCurve

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section FinrankEq

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {K₀ : IntermediateField ℚ K}
variable (E₀ : WeierstrassCurve K₀) [E₀.IsElliptic]
variable (D : IsogenyEndDatum (E₀.map (algebraMap K₀ K)).toAffine)
variable (hcoeffs : kw_iA_CoeffsHyp E₀ D)

local notation "E" => E₀.map (algebraMap K₀ K)

theorem kw_iPFE_functionField_ringHom_ext {F : Type*} [Field F] {W : Affine F}
    {L : Type*} [Field L] {f g : W.FunctionField →+* L}
    (hF : ∀ r : F, f (algebraMap F W.FunctionField r) = g (algebraMap F W.FunctionField r))
    (hX : f (polyToFunctionField W X) = g (polyToFunctionField W X))
    (hy : f (yGen W) = g (yGen W)) : f = g := by
  let : Algebra F L := (f.comp (algebraMap F W.FunctionField)).toAlgebra
  let f' : W.FunctionField →ₐ[F] L := { f with commutes' := fun _ => rfl }
  let g' : W.FunctionField →ₐ[F] L := { g with commutes' := fun r => (hF r).symm }
  have heq : f' = g' := kw_functionField_algHom_ext hX hy
  exact congrArg AlgHom.toRingHom heq

end FinrankEq
end ModularCurve
end

section

namespace ModularCurve

section Phi

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {K₀ : IntermediateField ℚ K}
variable (E : WeierstrassCurve K) [E.IsElliptic]
variable (E₀ : WeierstrassCurve K₀) [E₀.IsElliptic]

omit [DecidableEq K] in
omit [E.IsElliptic] [E₀.IsElliptic] in
theorem kw_iotaDescentCurve_map_FF (hmap : E₀.map (algebraMap K₀ K) = E) :
    E₀.map (algebraMap K₀ E.toAffine.FunctionField)
      = E.map (algebraMap K E.toAffine.FunctionField) := by
  classical
  have htower : (algebraMap K₀ E.toAffine.FunctionField)
      = (algebraMap K E.toAffine.FunctionField).comp (algebraMap K₀ K) :=
    IsScalarTower.algebraMap_eq K₀ K E.toAffine.FunctionField
  rw [htower, ← WeierstrassCurve.map_map, hmap]

omit [DecidableEq K] in
omit [E.IsElliptic] [E₀.IsElliptic] in
theorem kw_iotaDescentPhi_equation (hmap : E₀.map (algebraMap K₀ K) = E) :
    (E₀.map (algebraMap K₀ E.toAffine.FunctionField)).toAffine.Equation
      (polyToFunctionField E.toAffine X) (yGen E.toAffine) := by
  classical
  rw [kw_iotaDescentCurve_map_FF E E₀ hmap]
  exact equation_map_polyToFunctionField_yGen (W := E.toAffine)

omit [DecidableEq K] in
omit [E.IsElliptic] in
theorem kw_iotaDescentPhi_transcendental :
    Function.Injective
      (Polynomial.aeval (R := K₀) (polyToFunctionField E.toAffine X)) := by
  classical
  have hK : Transcendental K (polyToFunctionField E.toAffine X) :=
    transcendental_polyToFunctionField_X (W := E.toAffine)
  have hK₀ : Transcendental K₀ (polyToFunctionField E.toAffine X) :=
    hK.restrictScalars (R := K₀) (algebraMap K₀ K).injective
  exact (injective_iff_map_eq_zero _).mpr
    (fun p hp => transcendental_iff.mp hK₀ p hp)

variable (hmap : E₀.map (algebraMap K₀ K) = E)

def kw_iotaDescentPhi : E₀.toAffine.FunctionField →ₐ[K₀] E.toAffine.FunctionField :=
  pointPullbackHomTo (kw_iotaDescentPhi_equation E E₀ hmap)
    (kw_iotaDescentPhi_transcendental E)

omit [DecidableEq K] in
omit [E.IsElliptic] [E₀.IsElliptic] in
theorem kw_iotaDescentPhi_X :
    kw_iotaDescentPhi E E₀ hmap (polyToFunctionField E₀.toAffine X)
      = polyToFunctionField E.toAffine X := by
  classical
  exact
    pointPullbackHomTo_polyToFunctionField_X _ _

omit [DecidableEq K] in
omit [E.IsElliptic] [E₀.IsElliptic] in
theorem kw_iotaDescentPhi_yGen :
    kw_iotaDescentPhi E E₀ hmap (yGen E₀.toAffine) = yGen E.toAffine := by
  classical
  exact
    pointPullbackHomTo_yGen _ _

end Phi
end ModularCurve
end

section

open Cardinal

namespace ModularCurve

universe u

attribute [local instance] Classical.propDecidable

section CountableBridge

theorem kw_fdn2_qephod_hend2fgd1_countable_of_fg {K : Type uK} [Field K] [Algebra ℚ K]
    {K₀ : IntermediateField ℚ K} (hfg : K₀.FG) : Countable (↥K₀) := by
  obtain ⟨s, hs⟩ := hfg
  rw [← hs]
  have h2 : Cardinal.lift.{0} (Cardinal.mk ↥(IntermediateField.adjoin ℚ (↑s : Set K))) ≤
    Cardinal.aleph0 :=
    (IntermediateField.lift_cardinalMk_adjoin_le ℚ (↑s : Set K)).trans
      (max_le (max_le (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0)
        (Cardinal.lift_le_aleph0.mpr (Set.Countable.le_aleph0 s.countable_toSet))) le_rfl)
  exact Cardinal.mk_le_aleph0_iff.mp (Cardinal.lift_le_aleph0.mp h2)

end CountableBridge

section SubfieldDescentMint

def KwD5BetweenCurvesSubfieldDescent : Prop :=
  ∀ (K : Type uK) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E] [WeierstrassCurve.Affine.AbelTheorem E]
    [E'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E']
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E']
    [WeierstrassCurve.Affine.AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField)
    (_hι : ι.toRingHom.IsIntegral) (_hfin : FiniteAlong K ι),
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    ∃ (K₀ : IntermediateField ℚ K) (_ : K₀.FG)
      (E₀ E₀' : WeierstrassCurve K₀) (_ : E₀.IsElliptic) (_ : E₀'.IsElliptic)
      (hE₀map : E₀.map (algebraMap K₀ K) = E) (hE₀'map : E₀'.map (algebraMap K₀ K) = E')
      (ι' : E₀'.toAffine.FunctionField →ₐ[K₀] E₀.toAffine.FunctionField)
      (_hι' : ι'.toRingHom.IsIntegral) (_hfin' : FiniteAlong K₀ ι')
      (_hfinrank : finrankAlong K₀ ι' = finrankAlong K ι),
      ∀ x : E₀'.toAffine.FunctionField,
        ι (kw_iotaDescentPhi E' E₀' hE₀'map x)
          = kw_iotaDescentPhi E E₀ hE₀map (ι' x)

end SubfieldDescentMint

section KerDescendMint

def KwD5BetweenCurvesKerDescendAlgClosed : Prop :=
  ∀ (K : Type uK) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E] [WeierstrassCurve.Affine.AbelTheorem E]
    [E'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E']
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E']
    [WeierstrassCurve.Affine.AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)
    (N : ℕ) [NeZero N],
    IsAddCyclic (AddMonoidHom.ker
      (pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic ι hfin))) →
    Nat.card (AddMonoidHom.ker
      (pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic ι hfin))) = N →
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    ∀ (K₀ : IntermediateField ℚ K)
      (E₀ E₀' : WeierstrassCurve K₀) [E₀.IsElliptic] [E₀'.IsElliptic]
      (hE₀map : E₀.map (algebraMap K₀ K) = E) (hE₀'map : E₀'.map (algebraMap K₀ K) = E')
      (ι' : E₀'.toAffine.FunctionField →ₐ[K₀] E₀.toAffine.FunctionField)
      (_hι' : ι'.toRingHom.IsIntegral) (_hfin' : FiniteAlong K₀ ι'),
      (∀ x : E₀'.toAffine.FunctionField,
        ι (kw_iotaDescentPhi E' E₀' hE₀'map x)
          = kw_iotaDescentPhi E E₀ hE₀map (ι' x)) →
    ∃ (_ : (E₀⁄(AlgebraicClosure (↥K₀))).IsElliptic)
      (_ : (E₀'⁄(AlgebraicClosure (↥K₀))).IsElliptic)
      (ι₀ : (E₀'⁄(AlgebraicClosure (↥K₀))).toAffine.FunctionField
        →ₐ[AlgebraicClosure (↥K₀)] (E₀⁄(AlgebraicClosure (↥K₀))).toAffine.FunctionField)
      (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong (AlgebraicClosure (↥K₀)) ι₀),
      IsAddCyclic (AddMonoidHom.ker
        (pointMapOfPushforward ι₀ hι₀ hfin₀ (normFormulaAlong_of_elliptic ι₀ hfin₀))) ∧
      Nat.card (AddMonoidHom.ker
        (pointMapOfPushforward ι₀ hι₀ hfin₀ (normFormulaAlong_of_elliptic ι₀ hfin₀))) = N

end KerDescendMint

section Reduce

theorem kw_fdn2_qephod_hend2fgd1_bcFGDescent_of_two
    (hSD : KwD5BetweenCurvesSubfieldDescent.{uK})
    (hKD : KwD5BetweenCurvesKerDescendAlgClosed.{uK}) :
    KwD5BetweenCurvesFGFieldDescent.{uK} := by
  intro K _ _ _ _ E E' _ _ _ _ _ _ _ _ ι hι hfin N _ hcyc hcard
  let : Algebra ℚ K := DivisionRing.toRatAlgebra
  obtain ⟨K₀, hfg, E₀, E₀', hE₀ell, hE₀'ell, hE₀map, hE₀'map,
    ι', hι', hfin', _hfinrank, hcompat⟩ := hSD K E E' ι hι hfin
  have : E₀.IsElliptic := hE₀ell
  have : E₀'.IsElliptic := hE₀'ell
  have : Countable (↥K₀) := kw_fdn2_qephod_hend2fgd1_countable_of_fg hfg
  obtain ⟨hE₀ACell, hE₀'ACell, ι₀, hι₀, hfin₀, hcyc₀, hcard₀⟩ :=
    hKD K E E' ι hι hfin N hcyc hcard K₀ E₀ E₀' hE₀map hE₀'map ι' hι' hfin' hcompat
  exact ⟨K₀, inferInstance, E₀, E₀', hE₀ell, hE₀'ell, hE₀map, hE₀'map,
    hE₀ACell, hE₀'ACell, ι₀, hι₀, hfin₀, hcyc₀, hcard₀⟩

end Reduce
end ModularCurve
end

section

namespace ModularCurve

universe u

attribute [local instance] Classical.propDecidable

section BCNoACEngine

variable {R₀ : Type u} [Field R₀]
variable (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
variable (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [CharZero F]
variable (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']
variable [(E₀⁄F).IsElliptic] [(E₀'⁄F).IsElliptic] [(E₀⁄F').IsElliptic] [(E₀'⁄F').IsElliptic]
variable (ι' : (E₀'⁄F).toAffine.FunctionField →ₐ[F] (E₀⁄F).toAffine.FunctionField)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def kw_surgehgf4_hfgkd_bcTensorIota :
    (E₀'⁄F).toAffine.FunctionField ⊗[F] F' →ₐ[F] (E₀⁄F).toAffine.FunctionField ⊗[F] F' :=
  Algebra.TensorProduct.map ι' (AlgHom.id F F')

omit [DecidableEq F] [DecidableEq F'] in
omit [E₀.IsElliptic] [E₀'.IsElliptic] [CharZero F] [Algebra R₀ F'] [CharZero F']
  [IsScalarTower R₀ F F'] [WeierstrassCurve.IsElliptic E₀⁄F] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [WeierstrassCurve.IsElliptic E₀'⁄F'] in
theorem kw_surgehgf4_hfgkd_bcTensorIota_tmul (a : (E₀'⁄F).toAffine.FunctionField)
    (c : F') :
    kw_surgehgf4_hfgkd_bcTensorIota E₀ E₀' F F' ι' (a ⊗ₜ[F] c) = (ι' a) ⊗ₜ[F] c := by
  classical
  simp [kw_surgehgf4_hfgkd_bcTensorIota, Algebra.TensorProduct.map_tmul]

omit [DecidableEq F] [DecidableEq F'] in
omit [E₀.IsElliptic] [E₀'.IsElliptic] [CharZero F] [Algebra R₀ F'] [CharZero F']
  [IsScalarTower R₀ F F'] [WeierstrassCurve.IsElliptic E₀⁄F] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [WeierstrassCurve.IsElliptic E₀'⁄F'] in
theorem kw_surgehgf4_hfgkd_bcTensorIota_injective :
    Function.Injective (kw_surgehgf4_hfgkd_bcTensorIota E₀ E₀' F F' ι') := by
  classical
  exact
    Module.Flat.rTensor_preserves_injective_linearMap (M := F') ι'.toLinearMap ι'.injective

omit [DecidableEq F] [DecidableEq F'] in
scoped instance kw_surgehgf4_hfgkd_tensorIsDomain_E' :
    IsDomain ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') := by
  classical
  exact
    kw_functionFieldTensorIsDomain_dischargeGeneralNoAC E₀' F F'

def kw_surgehgf4_hfgkd_bcTensorFracIota :
    FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
      →+* FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F') :=
  IsFractionRing.map (K := FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
    (L := FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F'))
    (kw_surgehgf4_hfgkd_bcTensorIota_injective E₀ E₀' F F' ι')

omit [DecidableEq F] [DecidableEq F'] in
omit [E₀'.IsElliptic] [WeierstrassCurve.IsElliptic E₀⁄F] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [WeierstrassCurve.IsElliptic E₀'⁄F'] in
omit [E₀.IsElliptic] [CharZero F] [Algebra R₀ F'] [CharZero F'] [IsScalarTower R₀ F F'] in
theorem kw_surgehgf4_hfgkd_bcTensorFracIota_algebraMap
    (t : (E₀'⁄F).toAffine.FunctionField ⊗[F] F') :
    kw_surgehgf4_hfgkd_bcTensorFracIota E₀ E₀' F F' ι'
        (algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ t)
      = algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _
          (kw_surgehgf4_hfgkd_bcTensorIota E₀ E₀' F F' ι' t) := by
  classical
  unfold kw_surgehgf4_hfgkd_bcTensorFracIota IsFractionRing.map
  exact IsLocalization.map_eq
    (T := nonZeroDivisors ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ t

omit [DecidableEq F] [DecidableEq F'] in
omit [E₀.IsElliptic] [E₀'.IsElliptic] [CharZero F] [Algebra R₀ F'] [CharZero F']
  [IsScalarTower R₀ F F'] [WeierstrassCurve.IsElliptic E₀⁄F] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [WeierstrassCurve.IsElliptic E₀'⁄F'] in
theorem kw_surgehgf4_hfgkd_bcTensorIota_finite (hfin' : FiniteAlong F ι') :
    (kw_surgehgf4_hfgkd_bcTensorIota E₀ E₀' F F' ι').toRingHom.Finite := by
  classical
  exact
    RingHom.Finite.tensorProductMap (f := ι') hfin' (g := AlgHom.id F F')
      (RingHom.Finite.id F')

def kw_surgehgf4_hfgkd_bcTensorFracIotaAlg :
    FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
      →ₐ[F'] FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F') :=
  { kw_surgehgf4_hfgkd_bcTensorFracIota E₀ E₀' F F' ι' with
    commutes' := fun c => by
      change kw_surgehgf4_hfgkd_bcTensorFracIota E₀ E₀' F F' ι'
          (algebraMap F' _ c) = algebraMap F' _ c
      rw [IsScalarTower.algebraMap_apply F' ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
          (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')),
        Algebra.TensorProduct.right_algebraMap_apply,
        kw_surgehgf4_hfgkd_bcTensorFracIota_algebraMap E₀ E₀' F F' ι',
        kw_surgehgf4_hfgkd_bcTensorIota_tmul, map_one,
        IsScalarTower.algebraMap_apply F' ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
          (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')),
        Algebra.TensorProduct.right_algebraMap_apply] }

def kw_surgehgf4_hfgkd_bcIota₁NoAC :
    (E₀'⁄F').toAffine.FunctionField →ₐ[F'] (E₀⁄F').toAffine.FunctionField :=
  let ψE := kw_functionFieldTensorFracEquivGeneralNoAC E₀ F F'
  let ψE' := kw_functionFieldTensorFracEquivGeneralNoAC E₀' F F'
  (ψE.symm.toAlgHom.comp (kw_surgehgf4_hfgkd_bcTensorFracIotaAlg E₀ E₀' F F' ι')).comp
    ψE'.toAlgHom

omit [DecidableEq F] [DecidableEq F'] in
omit [WeierstrassCurve.IsElliptic E₀⁄F] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [WeierstrassCurve.IsElliptic E₀'⁄F'] in
omit [E₀'.IsElliptic] in
omit [E₀.IsElliptic] [CharZero F] [Algebra R₀ F'] [CharZero F'] [IsScalarTower R₀ F F'] in
theorem kw_surgehgf4_hfgkd_bcTensorFracIotaSeam (hfin' : FiniteAlong F ι') :
    (kw_surgehgf4_hfgkd_bcTensorFracIota E₀ E₀' F F' ι').Finite ∧
    (letI := (kw_surgehgf4_hfgkd_bcTensorFracIota E₀ E₀' F F' ι').toAlgebra
     @Module.finrank (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
       (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ _ Algebra.toModule)
      = finrankAlong F ι' := by
  classical
  let FF := (E₀⁄F).toAffine.FunctionField
  let FF' := (E₀'⁄F).toAffine.FunctionField
  let T := (E₀⁄F).toAffine.FunctionField ⊗[F] F'
  let T' := (E₀'⁄F).toAffine.FunctionField ⊗[F] F'
  let FrT := FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
  let FrT' := FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
  let ιT : T' →+* T := (kw_surgehgf4_hfgkd_bcTensorIota E₀ E₀' F F' ι').toRingHom
  let ιFr : FrT' →+* FrT := kw_surgehgf4_hfgkd_bcTensorFracIota E₀ E₀' F F' ι'
  have hιT_inj : Function.Injective ιT :=
    kw_surgehgf4_hfgkd_bcTensorIota_injective E₀ E₀' F F' ι'
  have hιT_fin : ιT.Finite :=
    kw_surgehgf4_hfgkd_bcTensorIota_finite E₀ E₀' F F' ι' hfin'
  have hιFr_am : ∀ t : T', ιFr (algebraMap T' FrT' t) = algebraMap T FrT (ιT t) :=
    kw_surgehgf4_hfgkd_bcTensorFracIota_algebraMap E₀ E₀' F F' ι'
  let algι : Algebra FF' FF := ι'.toRingHom.toAlgebra
  let modι : Module FF' FF := Algebra.toModule
  have hsmul_ι : ∀ (c : FF') (x : FF), c • x = ι' c * x := fun c x => rfl
  have hfinFF : Module.Finite FF' FF := hfin'
  have hfreeFF : Module.Free FF' FF := Module.Free.of_divisionRing FF' FF
  let D := finrankAlong F ι'
  let b : Module.Basis (Fin D) FF' FF := Module.finBasisOfFinrankEq FF' FF (n := D) rfl
  have hrepr_mul : ∀ (c : FF') (x : FF) (j : Fin D),
      b.repr (ι' c * x) j = c * b.repr x j := fun c x j => by
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
      have hb_sum : a = ∑ i, ι' (b.repr a i) * b i := by
        conv_lhs => rw [← b.linearCombination_repr a, Finsupp.linearCombination_apply,
          Finsupp.sum_fintype _ _ (fun i => by rw [hsmul_ι, _root_.map_zero, zero_mul])]
        exact Finset.sum_congr rfl fun i _ => hsmul_ι _ _
      calc (a ⊗ₜ[F] c : T)
          = (∑ i, ι' (b.repr a i) * b i) ⊗ₜ[F] c := by rw [← hb_sum]
        _ = ∑ i, ιT ((b.repr a i) ⊗ₜ[F] c) * e i := by
            rw [TensorProduct.sum_tmul]
            refine Finset.sum_congr rfl fun i _ => ?_
            show (ι' (b.repr a i) * b i) ⊗ₜ[F] c = ιT ((b.repr a i) ⊗ₜ[F] c) * e i
            rw [show ιT ((b.repr a i) ⊗ₜ[F] c) = (ι' (b.repr a i)) ⊗ₜ[F] c from
                  kw_surgehgf4_hfgkd_bcTensorIota_tmul E₀ E₀' F F' ι' _ _,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hliT : ∀ c : Fin D → T', ∑ i, ιT (c i) * e i = 0 → ∀ j, c j = 0 := by
    intro c hc j
    let pj : FF →ₗ[F] FF' :=
      { toFun := fun x => b.repr x j
        map_add' := fun x y => by simp only [map_add, Finsupp.add_apply]
        map_smul' := fun f x => by
          simp only [RingHom.id_apply, Algebra.smul_def]
          have h := hrepr_mul (algebraMap F FF' f) x j
          rwa [ι'.commutes] at h }
    let Ej : T →ₗ[F] T' := LinearMap.rTensor F' pj
    have hEj_key : ∀ (a : T') (i : Fin D),
        Ej (ιT a * e i) = if i = j then a else 0 := by
      intro a i
      induction a using TensorProduct.inductionOn with
      | add x y hx hy =>
        simp only [map_add, add_mul, hx, hy]; split_ifs <;> simp
      | tmul x c' =>
        rw [show ιT ((x : FF') ⊗ₜ[F] c') = (ι' x) ⊗ₜ[F] c' from
              kw_surgehgf4_hfgkd_bcTensorIota_tmul E₀ E₀' F F' ι' _ _,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        change (pj (ι' x * b i)) ⊗ₜ[F] c' = if i = j then (x : FF') ⊗ₜ[F] c' else 0
        rw [show pj (ι' x * b i) = if i = j then x else 0 from ?_]
        · split_ifs with h
          · rfl
          · exact TensorProduct.zero_tmul _ c'
        · change b.repr (ι' x * b i) j = if i = j then x else 0
          rw [hrepr_mul, b.repr_self, Finsupp.single_apply]
          split_ifs with h <;> simp
    have hc' : Ej (∑ i, ιT (c i) * e i) = 0 := by rw [hc, _root_.map_zero]
    simpa only [map_sum, hEj_key, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hc'
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
      by rw [_root_.map_neg]; exact eq_neg_of_add_eq_zero_right h3⟩
  have hspanFr : ∀ z : FrT, ∃ d : Fin D → FrT', z = ∑ i, ιFr (d i) * bFr i := by
    intro z
    obtain ⟨t, s, _, rfl⟩ := IsFractionRing.div_surjective (A := T) (K := FrT) z
    rcases eq_or_ne s 0 with rfl | hs'
    · exact ⟨0, by simp⟩
    obtain ⟨u, s₀, hs₀, hsu⟩ := hint s hs'
    have hιTs₀ : ιT s₀ ≠ 0 := fun h => hs₀ (hιT_inj (h.trans (_root_.map_zero ιT).symm))
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
  have hliFr : ∀ d : Fin D → FrT', ∑ i, ιFr (d i) * bFr i = 0 → ∀ j, d j = 0 := by
    intro d hd j
    obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors T') (Finset.univ.image d)
    choose p hp using fun i => hq (d i) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    have hq0 : (algebraMap T' FrT' (q : T')) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective T' FrT')).mpr (nonZeroDivisors.ne_zero q.2)
    have hp' : ∀ i, algebraMap T' FrT' (p i) = algebraMap T' FrT' (q : T') * d i := fun i =>
      by rw [hp i, Algebra.smul_def]
    have hd' : algebraMap T FrT (∑ i, ιT (p i) * e i) = 0 := by
      have h1 : ∑ i, ιFr (algebraMap T' FrT' (q : T')) * (ιFr (d i) * bFr i) = 0 := by
        rw [← Finset.mul_sum, hd, mul_zero]
      rw [map_sum, ← h1]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← hιFr_am (p i), ← mul_assoc, ← map_mul, ← hp' i]
    have hpj : p j = 0 :=
      hliT p ((IsFractionRing.injective T FrT) (by simpa using hd')) j
    have hthis : algebraMap T' FrT' (q : T') * d j = 0 := by
      rw [← hp' j, hpj, _root_.map_zero]
    exact (mul_eq_zero.mp hthis).resolve_left hq0
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

omit [DecidableEq F] [DecidableEq F'] in
omit [WeierstrassCurve.IsElliptic E₀⁄F] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [WeierstrassCurve.IsElliptic E₀'⁄F'] in
omit [E₀'.IsElliptic] in
omit [E₀.IsElliptic] [CharZero F] [CharZero F'] in
theorem kw_surgehgf4_hfgkd_bcIota₁NoAC_finiteAlong (hfin' : FiniteAlong F ι') :
    FiniteAlong F' (kw_surgehgf4_hfgkd_bcIota₁NoAC E₀ E₀' F F' ι') := by
  classical
  have hFr_fin := (kw_surgehgf4_hfgkd_bcTensorFracIotaSeam E₀ E₀' F F' ι' hfin').1
  let ψE := kw_functionFieldTensorFracEquivGeneralNoAC E₀ F F'
  let ψE' := kw_functionFieldTensorFracEquivGeneralNoAC E₀' F F'
  have h1 : RingHom.Finite ψE'.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ ψE'.surjective
  have h2 : RingHom.Finite ψE.symm.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ ψE.symm.surjective
  change RingHom.Finite (kw_surgehgf4_hfgkd_bcIota₁NoAC E₀ E₀' F F' ι').toRingHom
  have hcomp : (kw_surgehgf4_hfgkd_bcIota₁NoAC E₀ E₀' F F' ι').toRingHom
      = (ψE.symm.toAlgHom.toRingHom.comp
          (kw_surgehgf4_hfgkd_bcTensorFracIota E₀ E₀' F F' ι')).comp
        ψE'.toAlgHom.toRingHom := rfl
  rw [hcomp]
  exact RingHom.Finite.comp (RingHom.Finite.comp h2 hFr_fin) h1

omit [DecidableEq F] [DecidableEq F'] in
omit [WeierstrassCurve.IsElliptic E₀⁄F] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [WeierstrassCurve.IsElliptic E₀'⁄F'] in
omit [E₀'.IsElliptic] in
omit [E₀.IsElliptic] [CharZero F] [CharZero F'] in
theorem kw_surgehgf4_hfgkd_bcIota₁NoAC_isIntegral (hfin' : FiniteAlong F ι') :
    (kw_surgehgf4_hfgkd_bcIota₁NoAC E₀ E₀' F F' ι').toRingHom.IsIntegral := by
  classical
  exact
    RingHom.Finite.to_isIntegral
      (show RingHom.Finite (kw_surgehgf4_hfgkd_bcIota₁NoAC E₀ E₀' F F' ι').toRingHom from
        kw_surgehgf4_hfgkd_bcIota₁NoAC_finiteAlong E₀ E₀' F F' ι' hfin')

omit [DecidableEq F] [DecidableEq F'] in
omit [WeierstrassCurve.IsElliptic E₀⁄F] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [WeierstrassCurve.IsElliptic E₀'⁄F'] in
omit [E₀'.IsElliptic] in
omit [E₀.IsElliptic] [CharZero F] [CharZero F'] in
theorem kw_surgehgf4_hfgkd_bcIota₁NoAC_finrankAlong (hfin' : FiniteAlong F ι') :
    finrankAlong F' (kw_surgehgf4_hfgkd_bcIota₁NoAC E₀ E₀' F F' ι')
      = finrankAlong F ι' := by
  classical
  let ψE := kw_functionFieldTensorFracEquivGeneralNoAC E₀ F F'
  let ψE' := kw_functionFieldTensorFracEquivGeneralNoAC E₀' F F'
  let ιFr := kw_surgehgf4_hfgkd_bcTensorFracIota E₀ E₀' F F' ι'
  have hcomm : ∀ x, ιFr (ψE' x)
      = ψE (kw_surgehgf4_hfgkd_bcIota₁NoAC E₀ E₀' F F' ι' x) := fun x => by
    change ιFr (ψE' x) = ψE (ψE.symm (_))
    exact (ψE.apply_symm_apply _).symm
  calc finrankAlong F' (kw_surgehgf4_hfgkd_bcIota₁NoAC E₀ E₀' F F' ι')
      = (letI := ιFr.toAlgebra
         @Module.finrank (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
           (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ _ Algebra.toModule) :=
        @Algebra.finrank_eq_of_equiv_equiv
          (E₀'⁄F').toAffine.FunctionField (E₀⁄F').toAffine.FunctionField _ _
          (algebraAlong (kw_surgehgf4_hfgkd_bcIota₁NoAC E₀ E₀' F F' ι'))
          _ _ _ _ ιFr.toAlgebra ψE'.toRingEquiv ψE.toRingEquiv (RingHom.ext hcomm)
    _ = finrankAlong F ι' :=
        (kw_surgehgf4_hfgkd_bcTensorFracIotaSeam E₀ E₀' F F' ι' hfin').2

omit [DecidableEq F] [DecidableEq F'] in
omit [WeierstrassCurve.IsElliptic E₀⁄F] [WeierstrassCurve.IsElliptic E₀'⁄F]
  [WeierstrassCurve.IsElliptic E₀⁄F'] [WeierstrassCurve.IsElliptic E₀'⁄F'] in
omit [E₀'.IsElliptic] in
omit [E₀.IsElliptic] [CharZero F] [CharZero F'] in
theorem kw_surgehgf4_hfgkd_bcIota₁NoAC_compat (a : (E₀'⁄F).toAffine.FunctionField) :
    kw_surgehgf4_hfgkd_bcIota₁NoAC E₀ E₀' F F' ι'
        (kw_functionFieldMapAlongGeneralNoAC E₀' F F' a)
      = kw_functionFieldMapAlongGeneralNoAC E₀ F F' (ι' a) := by
  classical
  let ψE := kw_functionFieldTensorFracEquivGeneralNoAC E₀ F F'
  let ψE' := kw_functionFieldTensorFracEquivGeneralNoAC E₀' F F'
  let χE := kw_functionFieldMapAlongGeneralNoAC E₀ F F'
  let χE' := kw_functionFieldMapAlongGeneralNoAC E₀' F F'
  have hκE' : ψE' (χE' a)
      = algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ (a ⊗ₜ[F] (1 : F')) := by
    have hκ : ((kw_functionFieldTensorFracHomGeneralNoAC E₀' F F').restrictScalars F).comp
        χE'
        = (IsScalarTower.toAlgHom F ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
            (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))).comp
            (Algebra.TensorProduct.includeLeft (R := F)) := by
      refine kw_functionField_algHom_ext ?_ ?_
      · change kw_functionFieldTensorFracHomGeneralNoAC E₀' F F' (χE' _) = _
        rw [kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X,
          kw_functionFieldTensorFracHomGeneralNoAC_X]; rfl
      · change kw_functionFieldTensorFracHomGeneralNoAC E₀' F F' (χE' _) = _
        rw [kw_functionFieldMapAlongGeneralNoAC_yGen,
          kw_functionFieldTensorFracHomGeneralNoAC_yGen]; rfl
    exact DFunLike.congr_fun hκ a
  have hκE : ∀ b, ψE.symm (algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _
      (b ⊗ₜ[F] (1 : F'))) = χE b := by
    intro b
    refine ψE.injective ?_
    rw [AlgEquiv.apply_symm_apply]
    have hκ : ((kw_functionFieldTensorFracHomGeneralNoAC E₀ F F').restrictScalars F).comp
        χE
        = (IsScalarTower.toAlgHom F ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
            (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F'))).comp
            (Algebra.TensorProduct.includeLeft (R := F)) := by
      refine kw_functionField_algHom_ext ?_ ?_
      · change kw_functionFieldTensorFracHomGeneralNoAC E₀ F F' (χE _) = _
        rw [kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X,
          kw_functionFieldTensorFracHomGeneralNoAC_X]; rfl
      · change kw_functionFieldTensorFracHomGeneralNoAC E₀ F F' (χE _) = _
        rw [kw_functionFieldMapAlongGeneralNoAC_yGen,
          kw_functionFieldTensorFracHomGeneralNoAC_yGen]; rfl
    exact (DFunLike.congr_fun hκ b).symm
  change ψE.symm (kw_surgehgf4_hfgkd_bcTensorFracIotaAlg E₀ E₀' F F' ι' (ψE' (χE' a)))
      = χE (ι' a)
  rw [hκE',
    show kw_surgehgf4_hfgkd_bcTensorFracIotaAlg E₀ E₀' F F' ι'
        (algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ (a ⊗ₜ[F] (1 : F')))
      = algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _ ((ι' a) ⊗ₜ[F] (1 : F')) from by
        change kw_surgehgf4_hfgkd_bcTensorFracIota E₀ E₀' F F' ι' _ = _
        rw [kw_surgehgf4_hfgkd_bcTensorFracIota_algebraMap,
          kw_surgehgf4_hfgkd_bcTensorIota_tmul],
    hκE (ι' a)]

end BCNoACEngine

section KerTransportMint

def KwD5BetweenCurvesKerTransportAlongEmbed : Prop :=
  ∀ (R₀ : Type uK) [Field R₀] (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (F₁ : Type uK) [Field F₁] [Algebra R₀ F₁] [DecidableEq F₁] [IsAlgClosed F₁] [CharZero F₁]
    (F₂ : Type uK) [Field F₂] [Algebra R₀ F₂] [DecidableEq F₂] [IsAlgClosed F₂] [CharZero F₂]
    [Algebra F₁ F₂] [IsScalarTower R₀ F₁ F₂]
    [(E₀⁄F₁).IsElliptic] [(E₀'⁄F₁).IsElliptic] [(E₀⁄F₂).IsElliptic] [(E₀'⁄F₂).IsElliptic]
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

def KwD5BetweenCurvesChiCompChiEqPhi : Prop :=
  ∀ (K : Type uK) [Field K] [DecidableEq K] [CharZero K],
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    ∀ (K₀ : IntermediateField ℚ K) (W : WeierstrassCurve ↥K₀) [W.IsElliptic]
      (F₁ : Type uK) [Field F₁] [Algebra (↥K₀) F₁] [DecidableEq F₁] [CharZero F₁]
      [Algebra F₁ K] [IsScalarTower (↥K₀) F₁ K]
      [(W.map (algebraMap (↥K₀) K)).IsElliptic]
      (a : W.toAffine.FunctionField),
    kw_functionFieldMapAlongGeneralNoAC W F₁ K
      (kw_functionFieldMapAlongGeneralNoAC W (↥K₀) F₁ a)
    = kw_iotaDescentPhi (W.map (algebraMap (↥K₀) K)) W rfl a

end KerTransportMint

section Reduce

set_option synthInstance.maxHeartbeats 8000000 in
theorem kw_surgehgf4_hfgkd_hKD_of_kerTransport
    (hKT : KwD5BetweenCurvesKerTransportAlongEmbed.{uK})
    (hχB : KwD5BetweenCurvesChiCompChiEqPhi.{uK}) :
    KwD5BetweenCurvesKerDescendAlgClosed.{uK} := by
  intro K _ _ _ _ E E' _ _ _ _ _ _ _ _ ι hι hfin N _ hcyc hcard K₀ E₀ E₀' _ _
    hE₀map hE₀'map ι' hι' hfin' hcompat
  let : Algebra ℚ K := DivisionRing.toRatAlgebra
  subst hE₀map; subst hE₀'map
  have : CharZero (AlgebraicClosure (↥K₀)) :=
    charZero_of_injective_algebraMap (algebraMap (↥K₀) (AlgebraicClosure (↥K₀))).injective
  have : (E₀⁄(↥K₀)).IsElliptic :=
    inferInstanceAs ((E₀.map (algebraMap (↥K₀) (↥K₀))).IsElliptic)
  have : (E₀'⁄(↥K₀)).IsElliptic :=
    inferInstanceAs ((E₀'.map (algebraMap (↥K₀) (↥K₀))).IsElliptic)
  have hE₀AC : (E₀⁄(AlgebraicClosure (↥K₀))).IsElliptic :=
    inferInstanceAs ((E₀.map (algebraMap (↥K₀) (AlgebraicClosure (↥K₀)))).IsElliptic)
  have hE₀'AC : (E₀'⁄(AlgebraicClosure (↥K₀))).IsElliptic :=
    inferInstanceAs ((E₀'.map (algebraMap (↥K₀) (AlgebraicClosure (↥K₀)))).IsElliptic)
  have : (E₀⁄K).IsElliptic :=
    inferInstanceAs ((E₀.map (algebraMap (↥K₀) K)).IsElliptic)
  have : (E₀'⁄K).IsElliptic :=
    inferInstanceAs ((E₀'.map (algebraMap (↥K₀) K)).IsElliptic)
  have : IsDedekindDomain (E₀.map (algebraMap (↥K₀) K)).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (E₀.map (algebraMap (↥K₀) K))
  have : IsDedekindDomain (E₀'.map (algebraMap (↥K₀) K)).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (E₀'.map (algebraMap (↥K₀) K))
  have hgE : ‹WeierstrassCurve.Affine.GenusOnePlaceGate (E₀.map (algebraMap (↥K₀) K))›
      = WeierstrassCurve.Affine.s13GlobalGate (E₀.map (algebraMap (↥K₀) K)).toAffine :=
    WeierstrassCurve.Affine.GenusOnePlaceGate.ext_of_isCentred _ _ ‹_›
      (WeierstrassCurve.Affine.s13GlobalGate_isCentred _)
  have hgE' : ‹WeierstrassCurve.Affine.GenusOnePlaceGate (E₀'.map (algebraMap (↥K₀) K))›
      = WeierstrassCurve.Affine.s13GlobalGate (E₀'.map (algebraMap (↥K₀) K)).toAffine :=
    WeierstrassCurve.Affine.GenusOnePlaceGate.ext_of_isCentred _ _ ‹_›
      (WeierstrassCurve.Affine.s13GlobalGate_isCentred _)
  subst hgE
  subst hgE'
  let ι₀ : (E₀'⁄(AlgebraicClosure (↥K₀))).toAffine.FunctionField →ₐ[(AlgebraicClosure (↥K₀))]
    (E₀⁄(AlgebraicClosure (↥K₀))).toAffine.FunctionField :=
    kw_surgehgf4_hfgkd_bcIota₁NoAC E₀ E₀' (↥K₀) (AlgebraicClosure (↥K₀)) ι'
  have hι₀ : ι₀.toRingHom.IsIntegral :=
    kw_surgehgf4_hfgkd_bcIota₁NoAC_isIntegral E₀ E₀' (↥K₀) (AlgebraicClosure (↥K₀)) ι' hfin'
  have hfin₀ : FiniteAlong (AlgebraicClosure (↥K₀)) ι₀ :=
    kw_surgehgf4_hfgkd_bcIota₁NoAC_finiteAlong E₀ E₀' (↥K₀) (AlgebraicClosure (↥K₀)) ι' hfin'
  let τ : (AlgebraicClosure (↥K₀)) →ₐ[↥K₀] K := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure (↥K₀)) K := τ.toRingHom.toAlgebra
  have : IsScalarTower (↥K₀) (AlgebraicClosure (↥K₀)) K :=
    IsScalarTower.of_algebraMap_eq fun r => (τ.commutes r).symm
  have hD3 : ∀ a, ι₀ (kw_functionFieldMapAlongGeneralNoAC E₀' (↥K₀) (AlgebraicClosure (↥K₀)) a)
      = kw_functionFieldMapAlongGeneralNoAC E₀ (↥K₀) (AlgebraicClosure (↥K₀)) (ι' a) :=
    kw_surgehgf4_hfgkd_bcIota₁NoAC_compat E₀ E₀' (↥K₀) (AlgebraicClosure (↥K₀)) ι'
  clear_value ι₀ τ
  have hχΦE : ∀ a : E₀.toAffine.FunctionField,
      kw_functionFieldMapAlongGeneralNoAC E₀ (AlgebraicClosure (↥K₀)) K
        (kw_functionFieldMapAlongGeneralNoAC E₀ (↥K₀) (AlgebraicClosure (↥K₀)) a)
      = kw_iotaDescentPhi (E₀.map (algebraMap (↥K₀) K)) E₀ rfl a :=
    hχB K K₀ E₀ (AlgebraicClosure (↥K₀))
  have hχΦE' : ∀ a : E₀'.toAffine.FunctionField,
      kw_functionFieldMapAlongGeneralNoAC E₀' (AlgebraicClosure (↥K₀)) K
        (kw_functionFieldMapAlongGeneralNoAC E₀' (↥K₀) (AlgebraicClosure (↥K₀)) a)
      = kw_iotaDescentPhi (E₀'.map (algebraMap (↥K₀) K)) E₀' rfl a :=
    hχB K K₀ E₀' (AlgebraicClosure (↥K₀))
  have hχ : ∀ x : (E₀'⁄(AlgebraicClosure (↥K₀))).toAffine.FunctionField,
      ι (kw_functionFieldMapAlongGeneralNoAC E₀' (AlgebraicClosure (↥K₀)) K x)
        = kw_functionFieldMapAlongGeneralNoAC E₀ (AlgebraicClosure (↥K₀)) K (ι₀ x) := by
    have hext := kw_iPFE_functionField_ringHom_ext
      (F := AlgebraicClosure (↥K₀)) (W := (E₀'⁄(AlgebraicClosure (↥K₀))).toAffine)
      (f := ι.toRingHom.comp
        (kw_functionFieldMapAlongGeneralNoAC E₀' (AlgebraicClosure (↥K₀)) K).toRingHom)
      (g := (kw_functionFieldMapAlongGeneralNoAC E₀ (AlgebraicClosure (↥K₀)) K).toRingHom.comp
        ι₀.toRingHom)
      (fun r => by
        have h1 : ι ((kw_functionFieldMapAlongGeneralNoAC E₀' (AlgebraicClosure (↥K₀)) K)
          (algebraMap _ _ r)) = algebraMap (AlgebraicClosure (↥K₀)) ((E₀⁄K).toAffine.FunctionField)
          r :=
          by
          rw [(kw_functionFieldMapAlongGeneralNoAC E₀' (AlgebraicClosure (↥K₀)) K).commutes r,
            IsScalarTower.algebraMap_apply (AlgebraicClosure (↥K₀)) K
            ((E₀'⁄K).toAffine.FunctionField) r]
          exact (ι.commutes _).trans (IsScalarTower.algebraMap_apply (AlgebraicClosure (↥K₀)) K
            ((E₀⁄K).toAffine.FunctionField) r).symm
        have h2 : (kw_functionFieldMapAlongGeneralNoAC E₀ (AlgebraicClosure (↥K₀)) K) (ι₀
          (algebraMap _ _ r)) = algebraMap (AlgebraicClosure (↥K₀)) ((E₀⁄K).toAffine.FunctionField)
          r :=
          by
          rw [ι₀.commutes r, (kw_functionFieldMapAlongGeneralNoAC E₀ (AlgebraicClosure (↥K₀))
            K).commutes r]
        exact h1.trans h2.symm)
      (by
        have key : ι ((kw_functionFieldMapAlongGeneralNoAC E₀' (AlgebraicClosure (↥K₀)) K)
          ((kw_functionFieldMapAlongGeneralNoAC E₀' (↥K₀) (AlgebraicClosure (↥K₀)))
          (polyToFunctionField (E₀'⁄(↥K₀)) X)))
            = (kw_functionFieldMapAlongGeneralNoAC E₀ (AlgebraicClosure (↥K₀)) K) (ι₀
              ((kw_functionFieldMapAlongGeneralNoAC E₀' (↥K₀) (AlgebraicClosure (↥K₀)))
              (polyToFunctionField (E₀'⁄(↥K₀)) X))) := by
          rw [hD3, hχΦE, hχΦE']; exact hcompat _
        rw [kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X] at key
        exact key)
      (by
        have key : ι ((kw_functionFieldMapAlongGeneralNoAC E₀' (AlgebraicClosure (↥K₀)) K)
          ((kw_functionFieldMapAlongGeneralNoAC E₀' (↥K₀) (AlgebraicClosure (↥K₀))) (yGen
          (E₀'⁄(↥K₀)))))
            = (kw_functionFieldMapAlongGeneralNoAC E₀ (AlgebraicClosure (↥K₀)) K) (ι₀
              ((kw_functionFieldMapAlongGeneralNoAC E₀' (↥K₀) (AlgebraicClosure (↥K₀))) (yGen
              (E₀'⁄(↥K₀))))) := by
          rw [hD3, hχΦE, hχΦE']; exact hcompat _
        rw [kw_functionFieldMapAlongGeneralNoAC_yGen] at key
        exact key)
    exact fun x => DFunLike.congr_fun hext x
  have hKT_inst :=
    hKT (↥K₀) E₀ E₀' (AlgebraicClosure (↥K₀)) K ι₀ hι₀ hfin₀ ι hι hfin hχ N hcyc hcard
  exact ⟨hE₀AC, hE₀'AC, ι₀, hι₀, hfin₀, hKT_inst.1, hKT_inst.2⟩

end Reduce

section UpdatedWires

theorem kw_surgehgf4_hfgkd_bcFGDescent_of_three
    (hSD : KwD5BetweenCurvesSubfieldDescent.{uK})
    (hKT : KwD5BetweenCurvesKerTransportAlongEmbed.{uK})
    (hχB : KwD5BetweenCurvesChiCompChiEqPhi.{uK}) :
    KwD5BetweenCurvesFGFieldDescent.{uK} :=
  kw_fdn2_qephod_hend2fgd1_bcFGDescent_of_two hSD
    (kw_surgehgf4_hfgkd_hKD_of_kerTransport hKT hχB)

end UpdatedWires
end ModularCurve
end

section

namespace ModularCurve

section BCCanonical

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable (E E' : WeierstrassCurve K) [E.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E] [WeierstrassCurve.Affine.AbelTheorem E]
    [E'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E']
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E']
    [WeierstrassCurve.Affine.AbelTheorem E']
variable (ι : E'.toAffine.FunctionField →ₐ[K] E.toAffine.FunctionField)

def kw_surgehgf4_hSD_genSet : Set K :=
  ({E.a₁, E.a₂, E.a₃, E.a₄, E.a₆} : Set K) ∪ {E'.a₁, E'.a₂, E'.a₃, E'.a₄, E'.a₆} ∪
    ↑(kw_iCa_ffCoeffSet E (ι (polyToFunctionField E'.toAffine Polynomial.X))) ∪
    ↑(kw_iCa_ffCoeffSet E (ι (yGen E'.toAffine)))

omit [Algebra ℚ K] [IsAlgClosed K] [CharZero K] [E.IsElliptic] [GenusOnePlaceGate E]
  [GenusOnePlaceGate.IsCentred E] [AbelTheorem E] [E'.IsElliptic] [GenusOnePlaceGate E']
  [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E'] in
theorem kw_surgehgf4_hSD_genSet_finite : (kw_surgehgf4_hSD_genSet E E' ι).Finite := by
  unfold kw_surgehgf4_hSD_genSet
  exact (((((Set.finite_singleton _).insert _ |>.insert _ |>.insert _ |>.insert _).union
      ((Set.finite_singleton _).insert _ |>.insert _ |>.insert _ |>.insert _)).union
    (Finset.finite_toSet _)).union (Finset.finite_toSet _))

def kw_surgehgf4_hSD_K₀ : IntermediateField ℚ K :=
  IntermediateField.adjoin ℚ (kw_surgehgf4_hSD_genSet E E' ι)

omit [IsAlgClosed K] [CharZero K] [E.IsElliptic] [GenusOnePlaceGate E]
  [GenusOnePlaceGate.IsCentred E] [AbelTheorem E] [E'.IsElliptic] [GenusOnePlaceGate E']
  [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E'] in
theorem kw_surgehgf4_hSD_K₀_fg : (kw_surgehgf4_hSD_K₀ E E' ι).FG :=
  ⟨(kw_surgehgf4_hSD_genSet_finite E E' ι).toFinset, by rw [Set.Finite.coe_toFinset]; rfl⟩

omit [IsAlgClosed K] [CharZero K] [E.IsElliptic] [GenusOnePlaceGate E]
  [GenusOnePlaceGate.IsCentred E] [AbelTheorem E] [E'.IsElliptic] [GenusOnePlaceGate E']
  [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E'] in
theorem kw_surgehgf4_hSD_K₀_mem_E :
    E.a₁ ∈ kw_surgehgf4_hSD_K₀ E E' ι ∧ E.a₂ ∈ kw_surgehgf4_hSD_K₀ E E' ι ∧
    E.a₃ ∈ kw_surgehgf4_hSD_K₀ E E' ι ∧ E.a₄ ∈ kw_surgehgf4_hSD_K₀ E E' ι ∧
    E.a₆ ∈ kw_surgehgf4_hSD_K₀ E E' ι := by
  have h : ({E.a₁, E.a₂, E.a₃, E.a₄, E.a₆} : Set K) ⊆ kw_surgehgf4_hSD_K₀ E E' ι :=
    fun x hx => IntermediateField.subset_adjoin ℚ _ (Or.inl (Or.inl (Or.inl hx)))
  exact ⟨h (Or.inl rfl), h (Or.inr (Or.inl rfl)), h (Or.inr (Or.inr (Or.inl rfl))),
    h (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), h (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩

omit [IsAlgClosed K] [CharZero K] [E.IsElliptic] [GenusOnePlaceGate E]
  [GenusOnePlaceGate.IsCentred E] [AbelTheorem E] [E'.IsElliptic] [GenusOnePlaceGate E']
  [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E'] in
theorem kw_surgehgf4_hSD_K₀_mem_E' :
    E'.a₁ ∈ kw_surgehgf4_hSD_K₀ E E' ι ∧ E'.a₂ ∈ kw_surgehgf4_hSD_K₀ E E' ι ∧
    E'.a₃ ∈ kw_surgehgf4_hSD_K₀ E E' ι ∧ E'.a₄ ∈ kw_surgehgf4_hSD_K₀ E E' ι ∧
    E'.a₆ ∈ kw_surgehgf4_hSD_K₀ E E' ι := by
  have h : ({E'.a₁, E'.a₂, E'.a₃, E'.a₄, E'.a₆} : Set K) ⊆ kw_surgehgf4_hSD_K₀ E E' ι :=
    fun x hx => IntermediateField.subset_adjoin ℚ _ (Or.inl (Or.inl (Or.inr hx)))
  exact ⟨h (Or.inl rfl), h (Or.inr (Or.inl rfl)), h (Or.inr (Or.inr (Or.inl rfl))),
    h (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), h (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩

omit [IsAlgClosed K] [CharZero K] [E.IsElliptic] [GenusOnePlaceGate E]
  [GenusOnePlaceGate.IsCentred E] [AbelTheorem E] [E'.IsElliptic] [GenusOnePlaceGate E']
  [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E'] in
theorem kw_surgehgf4_hSD_ffCoeffSet_subset_X :
    (↑(kw_iCa_ffCoeffSet E (ι (polyToFunctionField E'.toAffine Polynomial.X))) : Set K)
      ⊆ kw_surgehgf4_hSD_K₀ E E' ι :=
  fun _ hc => IntermediateField.subset_adjoin ℚ _ (Or.inl (Or.inr hc))

omit [IsAlgClosed K] [CharZero K] [E.IsElliptic] [GenusOnePlaceGate E]
  [GenusOnePlaceGate.IsCentred E] [AbelTheorem E] [E'.IsElliptic] [GenusOnePlaceGate E']
  [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E'] in
theorem kw_surgehgf4_hSD_ffCoeffSet_subset_Y :
    (↑(kw_iCa_ffCoeffSet E (ι (yGen E'.toAffine))) : Set K)
      ⊆ kw_surgehgf4_hSD_K₀ E E' ι :=
  fun _ hc => IntermediateField.subset_adjoin ℚ _ (Or.inr hc)

def kw_surgehgf4_hSD_E₀ : WeierstrassCurve (kw_surgehgf4_hSD_K₀ E E' ι) where
  a₁ := ⟨E.a₁, (kw_surgehgf4_hSD_K₀_mem_E E E' ι).1⟩
  a₂ := ⟨E.a₂, (kw_surgehgf4_hSD_K₀_mem_E E E' ι).2.1⟩
  a₃ := ⟨E.a₃, (kw_surgehgf4_hSD_K₀_mem_E E E' ι).2.2.1⟩
  a₄ := ⟨E.a₄, (kw_surgehgf4_hSD_K₀_mem_E E E' ι).2.2.2.1⟩
  a₆ := ⟨E.a₆, (kw_surgehgf4_hSD_K₀_mem_E E E' ι).2.2.2.2⟩

omit [IsAlgClosed K] [CharZero K] [E.IsElliptic] [GenusOnePlaceGate E]
  [GenusOnePlaceGate.IsCentred E] [AbelTheorem E] [E'.IsElliptic] [GenusOnePlaceGate E']
  [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E'] in
theorem kw_surgehgf4_hSD_E₀_map :
    (kw_surgehgf4_hSD_E₀ E E' ι).map (algebraMap (kw_surgehgf4_hSD_K₀ E E' ι) K) = E := by
  ext <;> rfl

scoped instance kw_surgehgf4_hSD_E₀_isElliptic : (kw_surgehgf4_hSD_E₀ E E' ι).IsElliptic := by
  constructor; rw [isUnit_iff_ne_zero]; intro h0
  have : (algebraMap (kw_surgehgf4_hSD_K₀ E E' ι) K) (kw_surgehgf4_hSD_E₀ E E' ι).Δ
      = E.Δ := by rw [← WeierstrassCurve.map_Δ, kw_surgehgf4_hSD_E₀_map]
  rw [h0, _root_.map_zero] at this; exact E.isUnit_Δ.ne_zero this.symm

def kw_surgehgf4_hSD_E₀' : WeierstrassCurve (kw_surgehgf4_hSD_K₀ E E' ι) where
  a₁ := ⟨E'.a₁, (kw_surgehgf4_hSD_K₀_mem_E' E E' ι).1⟩
  a₂ := ⟨E'.a₂, (kw_surgehgf4_hSD_K₀_mem_E' E E' ι).2.1⟩
  a₃ := ⟨E'.a₃, (kw_surgehgf4_hSD_K₀_mem_E' E E' ι).2.2.1⟩
  a₄ := ⟨E'.a₄, (kw_surgehgf4_hSD_K₀_mem_E' E E' ι).2.2.2.1⟩
  a₆ := ⟨E'.a₆, (kw_surgehgf4_hSD_K₀_mem_E' E E' ι).2.2.2.2⟩

omit [IsAlgClosed K] [CharZero K] [E.IsElliptic] [GenusOnePlaceGate E]
  [GenusOnePlaceGate.IsCentred E] [AbelTheorem E] [E'.IsElliptic] [GenusOnePlaceGate E']
  [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E'] in
theorem kw_surgehgf4_hSD_E₀'_map :
    (kw_surgehgf4_hSD_E₀' E E' ι).map (algebraMap (kw_surgehgf4_hSD_K₀ E E' ι) K)
      = E' := by ext <;> rfl

scoped instance kw_surgehgf4_hSD_E₀'_isElliptic :
    (kw_surgehgf4_hSD_E₀' E E' ι).IsElliptic := by
  constructor; rw [isUnit_iff_ne_zero]; intro h0
  have : (algebraMap (kw_surgehgf4_hSD_K₀ E E' ι) K) (kw_surgehgf4_hSD_E₀' E E' ι).Δ
      = E'.Δ := by rw [← WeierstrassCurve.map_Δ, kw_surgehgf4_hSD_E₀'_map]
  rw [h0, _root_.map_zero] at this; exact E'.isUnit_Δ.ne_zero this.symm

end BCCanonical

section BCPinned

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {K₀ : IntermediateField ℚ K}
variable (E₀ E₀' : WeierstrassCurve K₀) [E₀.IsElliptic] [E₀'.IsElliptic]

variable (ι : (E₀'.map (algebraMap K₀ K)).toAffine.FunctionField
  →ₐ[K] (E₀.map (algebraMap K₀ K)).toAffine.FunctionField)

def kw_surgehgf4_hSD_CoeffsHyp : Prop :=
  (kw_iA_crCoeffsIn E₀ (IsLocalization.sec (nonZeroDivisors (E₀.map (algebraMap K₀
    K)).toAffine.CoordinateRing)
      (ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine Polynomial.X))).1
    ∧ kw_iA_crCoeffsIn E₀ ((IsLocalization.sec (nonZeroDivisors
        (E₀.map (algebraMap K₀ K)).toAffine.CoordinateRing) (ι (polyToFunctionField (E₀'.map
          (algebraMap K₀ K)).toAffine Polynomial.X))).2 :
      (E₀.map (algebraMap K₀ K)).toAffine.CoordinateRing))
  ∧ (kw_iA_crCoeffsIn E₀ (IsLocalization.sec (nonZeroDivisors (E₀.map (algebraMap K₀
    K)).toAffine.CoordinateRing)
      (ι (yGen (E₀'.map (algebraMap K₀ K)).toAffine))).1
    ∧ kw_iA_crCoeffsIn E₀ ((IsLocalization.sec (nonZeroDivisors
        (E₀.map (algebraMap K₀ K)).toAffine.CoordinateRing) (ι (yGen (E₀'.map (algebraMap K₀
          K)).toAffine))).2 :
      (E₀.map (algebraMap K₀ K)).toAffine.CoordinateRing))

variable (hcoeffs : kw_surgehgf4_hSD_CoeffsHyp E₀ E₀' ι)

def kw_surgehgf4_hSD_xP : E₀.toAffine.FunctionField :=
  Classical.choose (kw_iA_ffDescend_exists E₀ (ι (polyToFunctionField (E₀'.map (algebraMap K₀
    K)).toAffine Polynomial.X))
    hcoeffs.1.1 hcoeffs.1.2)

def kw_surgehgf4_hSD_yP : E₀.toAffine.FunctionField :=
  Classical.choose (kw_iA_ffDescend_exists E₀ (ι (yGen (E₀'.map (algebraMap K₀ K)).toAffine))
    hcoeffs.2.1 hcoeffs.2.2)

omit [DecidableEq K] in
omit [IsAlgClosed K] [CharZero K] [E₀'.IsElliptic] in
omit [E₀.IsElliptic] in
theorem kw_surgehgf4_hSD_xP_spec :
    kw_iA_phi E₀ (kw_surgehgf4_hSD_xP E₀ E₀' ι hcoeffs)
      = ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine Polynomial.X) := by
  classical
  exact
    Classical.choose_spec (kw_iA_ffDescend_exists E₀ _ hcoeffs.1.1 hcoeffs.1.2)

omit [DecidableEq K] in
omit [IsAlgClosed K] [CharZero K] [E₀'.IsElliptic] in
omit [E₀.IsElliptic] in
theorem kw_surgehgf4_hSD_yP_spec :
    kw_iA_phi E₀ (kw_surgehgf4_hSD_yP E₀ E₀' ι hcoeffs) = ι (yGen (E₀'.map (algebraMap K₀
        K)).toAffine) := by
  classical
  exact
    Classical.choose_spec (kw_iA_ffDescend_exists E₀ _ hcoeffs.2.1 hcoeffs.2.2)

omit [DecidableEq K] in
omit [IsAlgClosed K] [CharZero K] [E₀'.IsElliptic] in
omit [E₀.IsElliptic] in
theorem kw_surgehgf4_hSD_equation :
    (E₀'.map (algebraMap K₀ E₀.toAffine.FunctionField)).toAffine.Equation
      (kw_surgehgf4_hSD_xP E₀ E₀' ι hcoeffs) (kw_surgehgf4_hSD_yP E₀ E₀' ι hcoeffs) := by
  classical
  set xP := kw_surgehgf4_hSD_xP E₀ E₀' ι hcoeffs with hxP
  set yP := kw_surgehgf4_hSD_yP E₀ E₀' ι hcoeffs with hyP
  have hι : ((E₀'.map (algebraMap K₀ K)).map (algebraMap K (E₀.map (algebraMap K₀
    K)).toAffine.FunctionField)).toAffine.Equation
      (ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine Polynomial.X)) (ι (yGen (E₀'.map
        (algebraMap K₀ K)).toAffine)) := by
    have h₀ := equation_map_polyToFunctionField_yGen (W := (E₀'.map (algebraMap K₀ K)).toAffine)
    rw [Affine.equation_iff] at h₀ ⊢
    have h₁ := congrArg ι h₀
    simp only [map_add, map_mul, map_pow, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, AlgHom.commutes] at h₁ ⊢
    linear_combination h₁
  rw [Affine.equation_iff] at hι ⊢
  have hΦx : kw_iA_phi E₀ xP = ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine
    Polynomial.X) :=
    hxP ▸ kw_surgehgf4_hSD_xP_spec E₀ E₀' ι hcoeffs
  have hΦy : kw_iA_phi E₀ yP = ι (yGen (E₀'.map (algebraMap K₀ K)).toAffine) :=
    hyP ▸ kw_surgehgf4_hSD_yP_spec E₀ E₀' ι hcoeffs
  have hΦc : ∀ (c : K₀), kw_iA_phi E₀ (algebraMap K₀ E₀.toAffine.FunctionField c)
      = algebraMap K (E₀.map (algebraMap K₀ K)).toAffine.FunctionField (algebraMap K₀ K c) :=
    fun c => ((kw_iA_phi E₀).commutes c).trans
      (IsScalarTower.algebraMap_apply K₀ K (E₀.map (algebraMap K₀ K)).toAffine.FunctionField c)
  have hΦinj : Function.Injective (kw_iA_phi E₀) := (kw_iA_phi E₀).toRingHom.injective
  refine hΦinj ?_
  simp only [map_add, map_mul, map_pow, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hι ⊢
  rw [hΦc, hΦc, hΦc, hΦc, hΦc, hΦx, hΦy]
  exact hι

omit [DecidableEq K] in
omit [IsAlgClosed K] [CharZero K] [E₀'.IsElliptic] in
omit [E₀.IsElliptic] in
theorem kw_surgehgf4_hSD_transcendental :
    Function.Injective
      (Polynomial.aeval (R := K₀) (kw_surgehgf4_hSD_xP E₀ E₀' ι hcoeffs)) := by
  classical
  refine (injective_iff_map_eq_zero _).mpr fun p hp => ?_
  have hK : Transcendental K (ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine
    Polynomial.X)) :=
    by
    intro halg
    obtain ⟨r, hr0, hreval⟩ := halg
    refine (transcendental_polyToFunctionField_X (W := (E₀'.map (algebraMap K₀ K)).toAffine)) ⟨r,
      hr0, ?_⟩
    apply ι.toRingHom.injective
    rw [_root_.map_zero, ← hreval]
    exact (Polynomial.aeval_algHom_apply ι _ r).symm
  have hιX : Transcendental K₀ (ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine
    Polynomial.X)) :=
    hK.restrictScalars (R := K₀) (algebraMap K₀ K).injective
  refine transcendental_iff.mp hιX p ?_
  calc Polynomial.aeval (R := K₀) (ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine
    Polynomial.X)) p
      = Polynomial.aeval (R := K₀)
          (kw_iA_phi E₀ (kw_surgehgf4_hSD_xP E₀ E₀' ι hcoeffs)) p := by
        rw [kw_surgehgf4_hSD_xP_spec]
    _ = kw_iA_phi E₀ (Polynomial.aeval (R := K₀) (kw_surgehgf4_hSD_xP E₀ E₀' ι hcoeffs) p) :=
        Polynomial.aeval_algHom_apply (kw_iA_phi E₀) _ p
    _ = kw_iA_phi E₀ 0 := by rw [hp]
    _ = 0 := _root_.map_zero _

def kw_surgehgf4_hSD_ι' : E₀'.toAffine.FunctionField →ₐ[K₀] E₀.toAffine.FunctionField :=
  pointPullbackHomTo (kw_surgehgf4_hSD_equation E₀ E₀' ι hcoeffs)
    (kw_surgehgf4_hSD_transcendental E₀ E₀' ι hcoeffs)

omit [DecidableEq K] in
omit [IsAlgClosed K] [CharZero K] [E₀'.IsElliptic] in
omit [E₀.IsElliptic] in
theorem kw_surgehgf4_hSD_ι'_X :
    kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs (polyToFunctionField E₀'.toAffine Polynomial.X)
      = kw_surgehgf4_hSD_xP E₀ E₀' ι hcoeffs := by
  classical
  exact
    pointPullbackHomTo_polyToFunctionField_X _ _

omit [DecidableEq K] in
omit [IsAlgClosed K] [CharZero K] [E₀'.IsElliptic] in
omit [E₀.IsElliptic] in
theorem kw_surgehgf4_hSD_ι'_yGen :
    kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs (yGen E₀'.toAffine)
      = kw_surgehgf4_hSD_yP E₀ E₀' ι hcoeffs := by
  classical
  exact
    pointPullbackHomTo_yGen _ _

omit [DecidableEq K] in
omit [IsAlgClosed K] [CharZero K] in
omit [E₀'.IsElliptic] in
theorem kw_surgehgf4_hSD_phiE'_X :
    kw_iA_phi E₀' (polyToFunctionField E₀'.toAffine Polynomial.X)
      = polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine Polynomial.X := by
  classical
  exact
    pointPullbackHomTo_polyToFunctionField_X _ _

omit [DecidableEq K] in
omit [IsAlgClosed K] [CharZero K] in
omit [E₀'.IsElliptic] in
theorem kw_surgehgf4_hSD_phiE'_yGen :
    kw_iA_phi E₀' (yGen E₀'.toAffine) = yGen (E₀'.map (algebraMap K₀ K)).toAffine := by
  classical
  exact
    pointPullbackHomTo_yGen _ _

omit [DecidableEq K] in
omit [IsAlgClosed K] [CharZero K] [E₀'.IsElliptic] in
omit [E₀.IsElliptic] in
theorem kw_surgehgf4_hSD_phiCompat :
    (ι.restrictScalars K₀).comp (kw_iA_phi E₀')
      = (kw_iA_phi E₀).comp (kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs) := by
  classical
  refine kw_functionField_algHom_ext ?_ ?_
  · change ι (kw_iA_phi E₀' (polyToFunctionField E₀'.toAffine Polynomial.X))
        = kw_iA_phi E₀ (kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs
            (polyToFunctionField E₀'.toAffine Polynomial.X))
    rw [kw_surgehgf4_hSD_phiE'_X, kw_surgehgf4_hSD_ι'_X, kw_surgehgf4_hSD_xP_spec]
  · change ι (kw_iA_phi E₀' (yGen E₀'.toAffine))
        = kw_iA_phi E₀ (kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs (yGen E₀'.toAffine))
    rw [kw_surgehgf4_hSD_phiE'_yGen, kw_surgehgf4_hSD_ι'_yGen, kw_surgehgf4_hSD_yP_spec]

omit [DecidableEq K] in
omit [IsAlgClosed K] [CharZero K] [E₀'.IsElliptic] in
omit [E₀.IsElliptic] in
theorem kw_surgehgf4_hSD_phiCompat_apply (x : E₀'.toAffine.FunctionField) :
    ι (kw_iA_phi E₀' x) = kw_iA_phi E₀ (kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs x) := by
  classical
  exact
    DFunLike.congr_fun (kw_surgehgf4_hSD_phiCompat E₀ E₀' ι hcoeffs) x

omit [DecidableEq K] in
omit [IsAlgClosed K] [CharZero K] [E₀'.IsElliptic] in
omit [E₀.IsElliptic] in
theorem kw_surgehgf4_hSD_finiteAlong :
    FiniteAlong K₀ (kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs) := by
  classical
  set ι' := kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs
  set xP := kw_surgehgf4_hSD_xP E₀ E₀' ι hcoeffs
  have hxPtr : Transcendental K₀ xP :=
    transcendental_iff_injective.mpr (kw_surgehgf4_hSD_transcendental E₀ E₀' ι hcoeffs)
  have hfd : FiniteDimensional (↥(K₀ : Type uK)⟮xP⟯) E₀.toAffine.FunctionField :=
    kw_iPFA_finiteDimensional_adjoin_transcendental E₀.toAffine hxPtr
  have hxPrange : xP ∈ ι'.fieldRange :=
    ⟨polyToFunctionField E₀'.toAffine Polynomial.X, kw_surgehgf4_hSD_ι'_X E₀ E₀' ι hcoeffs⟩
  have hle : (K₀ : Type uK)⟮xP⟯ ≤ ι'.fieldRange :=
    IntermediateField.adjoin_simple_le_iff.mpr hxPrange
  let algIncl : Algebra (↥(K₀ : Type uK)⟮xP⟯) (↥ι'.fieldRange) :=
    (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have towIncl : IsScalarTower (↥(K₀ : Type uK)⟮xP⟯) (↥ι'.fieldRange)
      E₀.toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have hfdR : FiniteDimensional (↥ι'.fieldRange) E₀.toAffine.FunctionField :=
    FiniteDimensional.right (↥(K₀ : Type uK)⟮xP⟯) (↥ι'.fieldRange) E₀.toAffine.FunctionField
  change ι'.toRingHom.Finite
  let ρ : E₀'.toAffine.FunctionField →+* ↥ι'.fieldRange :=
    { toFun := fun x => ⟨ι' x, x, rfl⟩
      map_one' := Subtype.ext (map_one ι')
      map_mul' := fun a b => Subtype.ext (map_mul ι' a b)
      map_zero' := Subtype.ext (_root_.map_zero ι')
      map_add' := fun a b => Subtype.ext (map_add ι' a b) }
  have hsurj : Function.Surjective ρ := by rintro ⟨y, x, rfl⟩; exact ⟨x, rfl⟩
  have hfactor : ι'.toRingHom
      = (algebraMap (↥ι'.fieldRange) E₀.toAffine.FunctionField).comp ρ := by ext x; rfl
  rw [hfactor]
  exact RingHom.Finite.comp hfdR (RingHom.Finite.of_surjective _ hsurj)

omit [DecidableEq K] in
omit [IsAlgClosed K] [CharZero K] [E₀'.IsElliptic] in
omit [E₀.IsElliptic] in
theorem kw_surgehgf4_hSD_isIntegral :
    (kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs).toRingHom.IsIntegral := by
  classical
  exact
    RingHom.Finite.to_isIntegral
      (f := (kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs).toRingHom)
      (kw_surgehgf4_hSD_finiteAlong E₀ E₀' ι hcoeffs)

def KwD5BCSubfieldDescentPinnedFinrankEq : Prop :=
  finrankAlong K₀ (kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs) = finrankAlong K ι

end BCPinned

section RouteCBridge

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {K₀ : IntermediateField ℚ K}
variable (E₀ E₀' : WeierstrassCurve K₀) [E₀.IsElliptic] [E₀'.IsElliptic]

def kw_surgehgf4_hSD_ιMpr
    {W W' : WeierstrassCurve K}
    (heq : E₀.map (algebraMap K₀ K) = W) (heq' : E₀'.map (algebraMap K₀ K) = W')
    (ι : W'.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField) :
    (E₀'.map (algebraMap K₀ K)).toAffine.FunctionField
      →ₐ[K] (E₀.map (algebraMap K₀ K)).toAffine.FunctionField :=
  Eq.mpr (congrArg (fun V => V.toAffine.FunctionField
      →ₐ[K] (E₀.map (algebraMap K₀ K)).toAffine.FunctionField) heq')
    (Eq.mpr (congrArg (fun V => W'.toAffine.FunctionField →ₐ[K] V.toAffine.FunctionField)
        heq) ι)

omit [DecidableEq K] in
omit [IsAlgClosed K] [CharZero K] in
omit [E₀.IsElliptic] in
theorem kw_surgehgf4_hSD_phi_eq_iotaDescentPhi :
    kw_iA_phi E₀ = kw_iotaDescentPhi (E₀.map (algebraMap K₀ K)) E₀ rfl := by
  classical
  refine kw_functionField_algHom_ext ?_ ?_
  · exact (pointPullbackHomTo_polyToFunctionField_X _ _).trans
      (kw_iotaDescentPhi_X _ _ rfl).symm
  · exact (pointPullbackHomTo_yGen _ _).trans (kw_iotaDescentPhi_yGen _ _ rfl).symm

omit [DecidableEq K] in
omit [IsAlgClosed K] [CharZero K] in
theorem kw_surgehgf4_hSD_instance_cast
    {W W' : WeierstrassCurve K} [W.IsElliptic] [W'.IsElliptic]
    (heq : E₀.map (algebraMap K₀ K) = W) (heq' : E₀'.map (algebraMap K₀ K) = W')
    (ι : W'.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField)
    (_hι : ι.toRingHom.IsIntegral) (_hfin : FiniteAlong K ι) (hfg : K₀.FG)
    (hcoeffs : kw_surgehgf4_hSD_CoeffsHyp E₀ E₀'
      (kw_surgehgf4_hSD_ιMpr E₀ E₀' heq heq' ι))
    (hFrEq : KwD5BCSubfieldDescentPinnedFinrankEq E₀ E₀'
      (kw_surgehgf4_hSD_ιMpr E₀ E₀' heq heq' ι) hcoeffs) :
    ∃ (K₀ : IntermediateField ℚ K) (_ : K₀.FG)
      (E₀ E₀' : WeierstrassCurve K₀) (_ : E₀.IsElliptic) (_ : E₀'.IsElliptic)
      (hE₀map : E₀.map (algebraMap K₀ K) = W) (hE₀'map : E₀'.map (algebraMap K₀ K) = W')
      (ι' : E₀'.toAffine.FunctionField →ₐ[K₀] E₀.toAffine.FunctionField)
      (_hι' : ι'.toRingHom.IsIntegral) (_hfin' : FiniteAlong K₀ ι')
      (_hfinrank : finrankAlong K₀ ι' = finrankAlong K ι),
      ∀ x : E₀'.toAffine.FunctionField,
        ι (kw_iotaDescentPhi W' E₀' hE₀'map x)
          = kw_iotaDescentPhi W E₀ hE₀map (ι' x) := by
  classical
  subst heq; subst heq'
  refine ⟨K₀, hfg, E₀, E₀', inferInstance, inferInstance, rfl, rfl,
    kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs,
    kw_surgehgf4_hSD_isIntegral E₀ E₀' ι hcoeffs,
    kw_surgehgf4_hSD_finiteAlong E₀ E₀' ι hcoeffs, hFrEq, fun x => ?_⟩
  rw [← kw_surgehgf4_hSD_phi_eq_iotaDescentPhi E₀,
      ← kw_surgehgf4_hSD_phi_eq_iotaDescentPhi E₀']
  exact kw_surgehgf4_hSD_phiCompat_apply E₀ E₀' ι hcoeffs x

omit [E₀.IsElliptic] [E₀'.IsElliptic] in
omit [IsAlgClosed K] [CharZero K] in
theorem kw_surgehgf4_hSD_coeffsHyp_cast
    {W W' : WeierstrassCurve K} [W.IsElliptic] [W'.IsElliptic]
    (heq : E₀.map (algebraMap K₀ K) = W) (heq' : E₀'.map (algebraMap K₀ K) = W')
    (ι : W'.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField)
    (hX : (↑(kw_iCa_ffCoeffSet W (ι (polyToFunctionField W'.toAffine Polynomial.X))) : Set K)
      ⊆ (K₀ : Set K))
    (hY : (↑(kw_iCa_ffCoeffSet W (ι (yGen W'.toAffine))) : Set K) ⊆ (K₀ : Set K)) :
    kw_surgehgf4_hSD_CoeffsHyp E₀ E₀' (kw_surgehgf4_hSD_ιMpr E₀ E₀' heq heq' ι) := by
  subst heq; subst heq'
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_, fun i j => ?_⟩
  · exact (kw_iCa_crCoeffsIn_of_ffCoeffSet_subset _ _ hX i j).1
  · exact (kw_iCa_crCoeffsIn_of_ffCoeffSet_subset _ _ hX i j).2
  · exact (kw_iCa_crCoeffsIn_of_ffCoeffSet_subset _ _ hY i j).1
  · exact (kw_iCa_crCoeffsIn_of_ffCoeffSet_subset _ _ hY i j).2

end RouteCBridge

section Wire

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable (E E' : WeierstrassCurve K) [E.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E] [WeierstrassCurve.Affine.AbelTheorem E]
    [E'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E']
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E']
    [WeierstrassCurve.Affine.AbelTheorem E']
variable (ι : E'.toAffine.FunctionField →ₐ[K] E.toAffine.FunctionField)

def kw_surgehgf4_hSD_ιCast :
    ((kw_surgehgf4_hSD_E₀' E E' ι).map
        (algebraMap (kw_surgehgf4_hSD_K₀ E E' ι) K)).toAffine.FunctionField
      →ₐ[K] ((kw_surgehgf4_hSD_E₀ E E' ι).map
        (algebraMap (kw_surgehgf4_hSD_K₀ E E' ι) K)).toAffine.FunctionField :=
  kw_surgehgf4_hSD_ιMpr (kw_surgehgf4_hSD_E₀ E E' ι) (kw_surgehgf4_hSD_E₀' E E' ι)
    (kw_surgehgf4_hSD_E₀_map E E' ι) (kw_surgehgf4_hSD_E₀'_map E E' ι) ι

omit [IsAlgClosed K] [CharZero K] [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E]
  [AbelTheorem E] [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E'] in
theorem kw_surgehgf4_hSD_hcoeffs_canonical :
    kw_surgehgf4_hSD_CoeffsHyp (kw_surgehgf4_hSD_E₀ E E' ι)
      (kw_surgehgf4_hSD_E₀' E E' ι) (kw_surgehgf4_hSD_ιCast E E' ι) :=
  kw_surgehgf4_hSD_coeffsHyp_cast (kw_surgehgf4_hSD_E₀ E E' ι)
    (kw_surgehgf4_hSD_E₀' E E' ι) (kw_surgehgf4_hSD_E₀_map E E' ι)
    (kw_surgehgf4_hSD_E₀'_map E E' ι) ι
    (kw_surgehgf4_hSD_ffCoeffSet_subset_X E E' ι)
    (kw_surgehgf4_hSD_ffCoeffSet_subset_Y E E' ι)

def KwD5BCSubfieldDescentCanonicalFinrankEq : Prop :=
  ∀ hcoeffs,
    KwD5BCSubfieldDescentPinnedFinrankEq (kw_surgehgf4_hSD_E₀ E E' ι)
      (kw_surgehgf4_hSD_E₀' E E' ι) (kw_surgehgf4_hSD_ιCast E E' ι) hcoeffs

end Wire

theorem kw_surgehgf4_hSD_of_canonicalFinrankEq
    (hFrEq : ∀ (K : Type uK) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
      (E E' : WeierstrassCurve.Affine K) [E.IsElliptic]
      [WeierstrassCurve.Affine.GenusOnePlaceGate E]
      [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E]
      [WeierstrassCurve.Affine.AbelTheorem E] [E'.IsElliptic]
      [WeierstrassCurve.Affine.GenusOnePlaceGate E']
      [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E']
      [WeierstrassCurve.Affine.AbelTheorem E']
      (ι : E'.FunctionField →ₐ[K] E.FunctionField)
      (_hι : ι.toRingHom.IsIntegral) (_hfin : FiniteAlong K ι),
      letI : Algebra ℚ K := DivisionRing.toRatAlgebra
      KwD5BCSubfieldDescentCanonicalFinrankEq E E' ι) :
    KwD5BetweenCurvesSubfieldDescent.{uK} := by
  intro K _ _ _ _ E E' _ _ _ _ _ _ _ _ ι hι hfin
  let : Algebra ℚ K := DivisionRing.toRatAlgebra
  exact kw_surgehgf4_hSD_instance_cast (kw_surgehgf4_hSD_E₀ E E' ι)
    (kw_surgehgf4_hSD_E₀' E E' ι) (kw_surgehgf4_hSD_E₀_map E E' ι)
    (kw_surgehgf4_hSD_E₀'_map E E' ι) ι hι hfin
    (kw_surgehgf4_hSD_K₀_fg E E' ι) (kw_surgehgf4_hSD_hcoeffs_canonical E E' ι)
    (hFrEq K E E' ι hι hfin (kw_surgehgf4_hSD_hcoeffs_canonical E E' ι))

end ModularCurve
end

section

namespace ModularCurve

theorem kw_surgehgf4_hfgkd_chiCompChiEqPhi_proved :
    KwD5BetweenCurvesChiCompChiEqPhi.{uK} := by
  intro K _ _ _ K₀ W _ F₁ _ _ _ _ _ _ _
  let χ₁ := kw_functionFieldMapAlongGeneralNoAC W (↥K₀) F₁
  let χ₂ := kw_functionFieldMapAlongGeneralNoAC W F₁ K
  let Φ := kw_iotaDescentPhi (W.map (algebraMap (↥K₀) K)) W rfl
  suffices h : (χ₂.toRingHom.comp χ₁.toRingHom
      : W.toAffine.FunctionField →+* (W.map (algebraMap (↥K₀) K)).toAffine.FunctionField)
      = Φ.toRingHom from fun a => DFunLike.congr_fun h a
  refine kw_iPFE_functionField_ringHom_ext (F := ↥K₀) (W := W.toAffine)
    (fun r => ?hF) ?hX ?hy
  case hF =>
    change χ₂ (χ₁ (algebraMap (↥K₀) W.toAffine.FunctionField r))
      = Φ (algebraMap (↥K₀) W.toAffine.FunctionField r)
    rw [Φ.commutes]
    rw [IsScalarTower.algebraMap_apply (↥K₀) K
      (W.map (algebraMap (↥K₀) K)).toAffine.FunctionField]
    erw [χ₁.commutes]
    rw [IsScalarTower.algebraMap_apply (↥K₀) F₁ (W⁄F₁).FunctionField]
    erw [χ₂.commutes]
    rw [IsScalarTower.algebraMap_apply F₁ K (W⁄K).FunctionField,
      ← IsScalarTower.algebraMap_apply (↥K₀) F₁ K]
    rfl
  case hX =>
    change χ₂ (χ₁ (polyToFunctionField W.toAffine X))
      = Φ (polyToFunctionField W.toAffine X)
    erw [kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X W (↥K₀) F₁,
      kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X W F₁ K,
      kw_iotaDescentPhi_X (W.map (algebraMap (↥K₀) K)) W rfl]
    rfl
  case hy =>
    change χ₂ (χ₁ (yGen W.toAffine)) = Φ (yGen W.toAffine)
    erw [kw_functionFieldMapAlongGeneralNoAC_yGen W (↥K₀) F₁,
      kw_functionFieldMapAlongGeneralNoAC_yGen W F₁ K,
      kw_iotaDescentPhi_yGen (W.map (algebraMap (↥K₀) K)) W rfl]
    rfl

end ModularCurve
end

section

namespace ModularCurve

attribute [local instance] Classical.propDecidable

section Bridge

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {K₀ : IntermediateField ℚ K}
variable (E₀ : WeierstrassCurve K₀) [E₀.IsElliptic]

attribute [-instance] IntermediateField.instAlgebraSubtypeMem in
def kw_surgehgf4_cfe_fχ :
    E₀.toAffine.FunctionField →+* (E₀.map (algebraMap K₀ K)).toAffine.FunctionField :=
  (kw_functionFieldMapAlongGeneralNoAC E₀ (↥K₀) K).toRingHom

attribute [-instance] IntermediateField.instAlgebraSubtypeMem in
omit [DecidableEq K] in
omit [IsAlgClosed K] in
omit [CharZero K] [E₀.IsElliptic] in
theorem kw_surgehgf4_cfe_fχ_apply (a : E₀.toAffine.FunctionField) :
    kw_surgehgf4_cfe_fχ E₀ a = kw_functionFieldMapAlongGeneralNoAC E₀ (↥K₀) K a := by
  classical
  exact
    rfl

attribute [-instance] IntermediateField.instAlgebraSubtypeMem in
omit [DecidableEq K] in
omit [IsAlgClosed K] in
omit [CharZero K] [E₀.IsElliptic] in
theorem kw_surgehgf4_cfe_chi_const (r : ↥K₀) :
    kw_functionFieldMapAlongGeneralNoAC E₀ (↥K₀) K
        (algebraMap (↥K₀) E₀.toAffine.FunctionField r)
      = algebraMap K (E₀.map (algebraMap K₀ K)).toAffine.FunctionField
          (algebraMap (↥K₀) K r) := by
  classical
  erw [(kw_functionFieldMapAlongGeneralNoAC E₀ (↥K₀) K).commutes r]
  exact IsScalarTower.algebraMap_apply (↥K₀) K (E₀⁄K).FunctionField r

omit [DecidableEq K] in
omit [IsAlgClosed K] in
omit [CharZero K] [E₀.IsElliptic] in
theorem kw_surgehgf4_cfe_fχ_eq_phi :
    kw_surgehgf4_cfe_fχ E₀ = (kw_iA_phi E₀).toRingHom := by
  classical
  refine kw_iPFE_functionField_ringHom_ext (F := ↥K₀) (W := E₀.toAffine)
    (fun r => ?hF) ?hX ?hy
  case hF =>
    change kw_surgehgf4_cfe_fχ E₀ (algebraMap (↥K₀) E₀.toAffine.FunctionField r)
      = kw_iA_phi E₀ (algebraMap (↥K₀) E₀.toAffine.FunctionField r)
    rw [(kw_iA_phi E₀).commutes r,
      IsScalarTower.algebraMap_apply (↥K₀) K
        (E₀.map (algebraMap K₀ K)).toAffine.FunctionField,
      kw_surgehgf4_cfe_fχ_apply, kw_surgehgf4_cfe_chi_const]
  case hX =>
    change kw_surgehgf4_cfe_fχ E₀ (polyToFunctionField E₀.toAffine X)
      = kw_iA_phi E₀ (polyToFunctionField E₀.toAffine X)
    rw [kw_surgehgf4_cfe_fχ_apply]
    erw [kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X E₀ (↥K₀) K]
  case hy =>
    change kw_surgehgf4_cfe_fχ E₀ (yGen E₀.toAffine) = kw_iA_phi E₀ (yGen E₀.toAffine)
    rw [kw_surgehgf4_cfe_fχ_apply]
    erw [kw_functionFieldMapAlongGeneralNoAC_yGen E₀ (↥K₀) K]

omit [DecidableEq K] in
omit [IsAlgClosed K] in
omit [CharZero K] [E₀.IsElliptic] in
theorem kw_surgehgf4_cfe_chi_eq_phi_apply (a : E₀.toAffine.FunctionField) :
    kw_functionFieldMapAlongGeneralNoAC E₀ (↥K₀) K a = kw_iA_phi E₀ a := by
  classical
  rw [← kw_surgehgf4_cfe_fχ_apply]
  exact DFunLike.congr_fun (kw_surgehgf4_cfe_fχ_eq_phi E₀) a

end Bridge

section BCPinnedDischarge

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {K₀ : IntermediateField ℚ K}
variable (E₀ E₀' : WeierstrassCurve K₀)

scoped instance kw_surgehgf4_cfe_instE₀'K₀ [E₀'.IsElliptic] : (E₀'⁄(↥K₀)).IsElliptic :=
  inferInstanceAs ((E₀'.map (algebraMap (↥K₀) (↥K₀))).IsElliptic)

scoped instance kw_surgehgf4_cfe_instE₀'K [E₀'.IsElliptic] : (E₀'⁄K).IsElliptic :=
  inferInstanceAs ((E₀'.map (algebraMap (↥K₀) K)).IsElliptic)

variable (ι : (E₀'.map (algebraMap K₀ K)).toAffine.FunctionField
  →ₐ[K] (E₀.map (algebraMap K₀ K)).toAffine.FunctionField)
variable (hcoeffs : kw_surgehgf4_hSD_CoeffsHyp E₀ E₀' ι)

omit [DecidableEq K] [IsAlgClosed K] [CharZero K] in
theorem kw_surgehgf4_cfe_bcIota₁NoAC_eq_ι :
    kw_surgehgf4_hfgkd_bcIota₁NoAC E₀ E₀' (↥K₀) K
        (kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs) = ι := by
  classical
  set ι' := kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs with hι'_def
  refine kw_functionField_algHom_ext ?_ ?_
  · have key : ι (kw_functionFieldMapAlongGeneralNoAC E₀' (↥K₀) K (polyToFunctionField
      (E₀'⁄(↥K₀)).toAffine X))
        = kw_surgehgf4_hfgkd_bcIota₁NoAC E₀ E₀' (↥K₀) K ι'
            (kw_functionFieldMapAlongGeneralNoAC E₀' (↥K₀) K (polyToFunctionField
              (E₀'⁄(↥K₀)).toAffine X)) := by
      rw [kw_surgehgf4_hfgkd_bcIota₁NoAC_compat, kw_surgehgf4_cfe_chi_eq_phi_apply E₀,
        kw_surgehgf4_cfe_chi_eq_phi_apply E₀']
      exact kw_surgehgf4_hSD_phiCompat_apply E₀ E₀' ι hcoeffs _
    rw [kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X] at key
    exact key.symm
  · have key : ι (kw_functionFieldMapAlongGeneralNoAC E₀' (↥K₀) K (yGen (E₀'⁄(↥K₀)).toAffine))
        = kw_surgehgf4_hfgkd_bcIota₁NoAC E₀ E₀' (↥K₀) K ι'
            (kw_functionFieldMapAlongGeneralNoAC E₀' (↥K₀) K (yGen (E₀'⁄(↥K₀)).toAffine)) := by
      rw [kw_surgehgf4_hfgkd_bcIota₁NoAC_compat, kw_surgehgf4_cfe_chi_eq_phi_apply E₀,
        kw_surgehgf4_cfe_chi_eq_phi_apply E₀']
      exact kw_surgehgf4_hSD_phiCompat_apply E₀ E₀' ι hcoeffs _
    rw [kw_functionFieldMapAlongGeneralNoAC_yGen] at key
    exact key.symm

omit [DecidableEq K] [IsAlgClosed K] [CharZero K] in
theorem kw_surgehgf4_cfe_pinnedFinrankEq :
    KwD5BCSubfieldDescentPinnedFinrankEq E₀ E₀' ι hcoeffs := by
  classical
  have hfin' : FiniteAlong (↥K₀) (kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs) :=
    kw_surgehgf4_hSD_finiteAlong E₀ E₀' ι hcoeffs
  have hD2 := kw_surgehgf4_hfgkd_bcIota₁NoAC_finrankAlong E₀ E₀' (↥K₀) K
    (kw_surgehgf4_hSD_ι' E₀ E₀' ι hcoeffs) hfin'
  have heq := kw_surgehgf4_cfe_bcIota₁NoAC_eq_ι E₀ E₀' ι hcoeffs
  unfold KwD5BCSubfieldDescentPinnedFinrankEq
  rw [heq] at hD2
  exact hD2.symm

end BCPinnedDischarge

section Canonical

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] (E E' : WeierstrassCurve K)
  (ι : E'.toAffine.FunctionField →ₐ[K] E.toAffine.FunctionField)

theorem kw_surgehgf4_cfe_canonicalFinrankEq :
    KwD5BCSubfieldDescentCanonicalFinrankEq E E' ι := fun hcoeffs =>
  kw_surgehgf4_cfe_pinnedFinrankEq (kw_surgehgf4_hSD_E₀ E E' ι)
    (kw_surgehgf4_hSD_E₀' E E' ι) (kw_surgehgf4_hSD_ιCast E E' ι) hcoeffs

end Canonical

section Wires

theorem kw_surgehgf4_cfe_hSD_discharge : KwD5BetweenCurvesSubfieldDescent.{uK} := by
  refine kw_surgehgf4_hSD_of_canonicalFinrankEq ?_
  intro K _ _ _ _ E E' _ _ _ _ _ _ _ _ ι _hι _hfin
  let : Algebra ℚ K := DivisionRing.toRatAlgebra
  exact kw_surgehgf4_cfe_canonicalFinrankEq E E' ι

theorem kw_surgehgf4_cfe_bcFGDescent_of_two
    (hKT : KwD5BetweenCurvesKerTransportAlongEmbed.{uK})
    (hχB : KwD5BetweenCurvesChiCompChiEqPhi.{uK}) :
    KwD5BetweenCurvesFGFieldDescent.{uK} :=
  kw_surgehgf4_hfgkd_bcFGDescent_of_three kw_surgehgf4_cfe_hSD_discharge hKT hχB

end Wires
end ModularCurve

end

namespace ModularCurve

theorem s13_stub_ktd : KwD5BetweenCurvesKerTransportAlongEmbed.{uK} := by
  intro R₀ _ E₀ E₀' _ _ F₁ _ _ _ _ _ F₂ _ _ _ _ _ _ _ _ _ _ _ ι₁ hι₁ hfin₁ ι₂ hι₂ hfin₂ hχ N _ hcyc
    hcard
  exact WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom R₀ E₀ E₀'
    F₁ F₂
    (kw_functionFieldMapAlongGeneralNoAC E₀ F₁ F₂)
    (kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X E₀ F₁ F₂)
    (kw_functionFieldMapAlongGeneralNoAC_yGen E₀ F₁ F₂)
    (kw_functionFieldMapAlongGeneralNoAC E₀' F₁ F₂)
    (kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X E₀' F₁ F₂)
    (kw_functionFieldMapAlongGeneralNoAC_yGen E₀' F₁ F₂)
    ι₁ hι₁ hfin₁ (WeierstrassCurve.Affine.normFormulaAlong_of_elliptic ι₁ hfin₁)
    ι₂ hι₂ hfin₂ (WeierstrassCurve.Affine.normFormulaAlong_of_elliptic ι₂ hfin₂)
    hχ N hcyc hcard

theorem s13_bcFGDescent : KwD5BetweenCurvesFGFieldDescent.{uK} :=
  kw_surgehgf4_cfe_bcFGDescent_of_two s13_stub_ktd kw_surgehgf4_hfgkd_chiCompChiEqPhi_proved
end ModularCurve

open _root_.WeierstrassCurve _root_.WeierstrassCurve.Affine in
theorem solution
    {K : Type uK} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong K ι)
    (hN : NormFormulaAlong K ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N) :
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    ∃ (K₀ : IntermediateField ℚ K) (_ : Countable K₀)
      (E₀ E₀' : WeierstrassCurve K₀) (_ : E₀.IsElliptic) (_ : E₀'.IsElliptic)
      (_ : E₀.map (algebraMap K₀ K) = E) (_ : E₀'.map (algebraMap K₀ K) = E')
      (_ : (E₀.baseChange (AlgebraicClosure K₀)).IsElliptic)
      (_ : (E₀'.baseChange (AlgebraicClosure K₀)).IsElliptic)
      (ι₀ : (E₀'.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField →ₐ[AlgebraicClosure K₀]
        (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField)
      (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong (AlgebraicClosure K₀) ι₀),
      ∀ [DecidableEq (AlgebraicClosure K₀)]
        [GenusOnePlaceGate (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate.IsCentred (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [AbelTheorem (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate.IsCentred (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        [AbelTheorem (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        (hN₀ : NormFormulaAlong (AlgebraicClosure K₀) ι₀ hfin₀),
        IsAddCyclic (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker ∧
          Nat.card (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker = N := by
  classical
  have hFG := ModularCurve.s13_bcFGDescent K E E' ι hι hfin N hcyc hcard
  obtain ⟨K₀, hK₀, E₀, E₀', hE₀, hE₀', hmap, hmap', hAC, hAC', ι₀, hι₀, hfin₀, hcyc₀, hcard₀⟩ := hFG
  refine ⟨K₀, hK₀, E₀, E₀', hE₀, hE₀', hmap, hmap', hAC, hAC', ι₀, hι₀, hfin₀, ?_⟩
  intro instDec g gc ga g' gc' ga' hN₀
  have hdec : instDec = s13DecEqAlgebraicClosure := Subsingleton.elim _ _
  subst hdec
  have : IsDedekindDomain (E₀.baseChange (AlgebraicClosure ↥K₀)).toAffine.CoordinateRing :=
    @CoordinateRing.isDedekindDomain _ _ _ (E₀.baseChange (AlgebraicClosure ↥K₀)) hAC
  have : IsDedekindDomain (E₀'.baseChange (AlgebraicClosure ↥K₀)).toAffine.CoordinateRing :=
    @CoordinateRing.isDedekindDomain _ _ _ (E₀'.baseChange (AlgebraicClosure ↥K₀)) hAC'
  have hg : g = @WeierstrassCurve.Affine.s13GlobalGate _ _ _ _ _ (E₀.baseChange (AlgebraicClosure
    ↥K₀)).toAffine hAC :=
    GenusOnePlaceGate.ext_of_isCentred _ _ gc
      (@WeierstrassCurve.Affine.s13GlobalGate_isCentred _ _ _ _ _ (E₀.baseChange (AlgebraicClosure
        ↥K₀)).toAffine hAC)
  have hg' : g' = @WeierstrassCurve.Affine.s13GlobalGate _ _ _ _ _ (E₀'.baseChange (AlgebraicClosure
    ↥K₀)).toAffine hAC' :=
    GenusOnePlaceGate.ext_of_isCentred _ _ gc'
      (@WeierstrassCurve.Affine.s13GlobalGate_isCentred _ _ _ _ _ (E₀'.baseChange (AlgebraicClosure
        ↥K₀)).toAffine hAC')
  subst hg
  subst hg'
  exact ⟨hcyc₀, hcard₀⟩

end

end privateSection

public section publicSection

open AlgebraicCurve

namespace WeierstrassCurve.Affine

universe u

theorem exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong K ι)
    (hN : NormFormulaAlong K ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N) :
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    ∃ (K₀ : IntermediateField ℚ K) (_ : Countable K₀)
      (E₀ E₀' : WeierstrassCurve K₀) (_ : E₀.IsElliptic) (_ : E₀'.IsElliptic)
      (_ : E₀.map (algebraMap K₀ K) = E) (_ : E₀'.map (algebraMap K₀ K) = E')
      (_ : (E₀.baseChange (AlgebraicClosure K₀)).IsElliptic)
      (_ : (E₀'.baseChange (AlgebraicClosure K₀)).IsElliptic)
      (ι₀ : (E₀'.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField →ₐ[AlgebraicClosure K₀]
        (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField)
      (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong (AlgebraicClosure K₀) ι₀),
      ∀ [DecidableEq (AlgebraicClosure K₀)]
        [GenusOnePlaceGate (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate.IsCentred (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [AbelTheorem (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate.IsCentred (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        [AbelTheorem (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        (hN₀ : NormFormulaAlong (AlgebraicClosure K₀) ι₀ hfin₀),
        IsAddCyclic (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker ∧
          Nat.card (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker = N :=
      solution E E' ι hι hfin hN N hcyc hcard

end WeierstrassCurve.Affine

end publicSection
