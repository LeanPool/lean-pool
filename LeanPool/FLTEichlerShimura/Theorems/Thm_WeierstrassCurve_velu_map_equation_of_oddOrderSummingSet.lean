/-
Based on Prove2Me node WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet
(99841a34-31c0-570f-ae9f-f8802f859369) by Claude (2026-09-05).

Proof based on Prove2Me submission 368c886c-4d95-5623-a9cf-0bde6782ce35
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_OddOrderSummingSet
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_VeluPointMap

import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.TotallySplit

import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_RatFuncPlaceClassification
import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_RatPointHom
import LeanPool.FLTEichlerShimura.Definitions.Defs_AlgebraicCurve_residueTheorem_sharedLibrary
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import LeanPool.FLTEichlerShimura.Definitions.Defs_WeierstrassCurve_veluSharedLibrary
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ord_eq_neg_log_of_valuationSubring_eq
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_ramificationIdx_fiberCenter
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_finite_setOf_ord_ne_zero_of_finiteDimensional
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_adjoin_yCoord_eq_top
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_sum_support

/-!
# Vélu's formulas land on the quotient curve (odd order)

Theorem statement: `WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet`
(`99841a34-31c0-570f-ae9f-f8802f859369`), by Claude, 2026-09-05.

Proof: submission `368c886c-4d95-5623-a9cf-0bde6782ce35`, by Claude, 2026-09-05 (ACCEPTED); locally
adapted.

Let $L$ be an algebraically closed field in which $2 \neq 0$, and let $W$ be a Weierstrass curve
over $L$ with invertible discriminant. Let $n$ be a natural number and let $Q$ be an affine point of
$W$ whose additive order equals $2n+1$. Put $S = W.\mathrm{oddOrderSummingSet}\,Q\,n$, the finite
subset of $L \times L$ obtained as the image of $\{1,\dots,n\}$ under $k \mapsto$ the coordinate
pair of $k \cdot Q$ (the point at infinity being sent to $(0,0)$). For $P = (x_P,y_P)$ write $g^x_P
= 3x_P^2 + 2a_2x_P + a_4 - a_1y_P$, $g^y_P = -(2y_P + a_1x_P + a_3)$, $t_P = 2g^x_P - a_1g^y_P$,
$u_P = (g^y_P)^2$, and let $t = \sum_{P \in S} t_P$, $w = \sum_{P \in S}
W.\mathrm{veluW}\,x_P\,y_P$. Then for any $x, y \in L$ satisfying the affine Weierstrass equation of
$W$ and such that $x \neq x_P$ for every $P \in S$, the pair $\bigl(\mathrm{veluX}_S(x),
\mathrm{veluY}_S(x,y)\bigr)$, given by the Vélu sums $x + \sum_{P}\bigl(t_P/(x-x_P) +
u_P/(x-x_P)^2\bigr)$ and $y - \sum_P\bigl(u_P(2y+a_1x+a_3)/(x-x_P)^3 +
t_P(a_1(x-x_P)+y-y_P)/(x-x_P)^2 + (a_1u_P - g^x_Pg^y_P)/(x-x_P)^2\bigr)$, satisfies the affine
Weierstrass equation of the curve with coefficients $a_1, a_2, a_3$, $a_4 - 5t$, $a_6 - b_2 t - 7w$.

This is the part of Vélu's Théorème 1 asserting that the explicit coordinate maps attached to a
summing set for the odd cyclic subgroup $\langle Q \rangle$ carry affine points of $W$ (away from
the kernel abscissae) to points of the quotient curve; the group-homomorphism properties are treated
separately. It is used in the construction of the Vélu isogeny at the level of function fields and
in the comparison of $2$-division values on $W$ and on the quotient curve.

## Explanation of the source proof

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet.lean

<!-- Generated by add_prove2me_provenance.py -->
-/

noncomputable section privateSection

open Polynomial IsDedekindDomain WithZero IsLocalRing

open scoped Polynomial.Bivariate

namespace AlgebraicCurve

namespace RationalFunctionField

variable (K : Type*) [Field K]

section PlaceInfty

variable [DecidableEq (RatFunc K)]

theorem inftyValuation_isEquiv_adicValuation :
    (RatFunc.inftyValuation K).IsEquiv (placeInfty K).adicValuation :=
  (placeInfty K).isEquiv_adicValuation_of_valuationSubring_eq rfl

end PlaceInfty
open scoped Place

variable {K}

theorem finite_setOf_valuation_ne_one {f : RatFunc K} (hf : f ≠ 0) :
    {w : HeightOneSpectrum K[X] | w.valuation (RatFunc K) f ≠ 1}.Finite := by
  have hnum : (Ideal.span {f.num} : Ideal K[X]) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using RatFunc.num_ne_zero hf
  have hden : (Ideal.span {f.denom} : Ideal K[X]) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using f.denom_ne_zero
  refine Set.Finite.subset ((Ideal.finite_factors hnum).union (Ideal.finite_factors hden))
    fun w hw => ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, Ideal.dvd_span_singleton] at hcon
  refine hw ?_
  have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.num) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hcon.1
  have h2 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hcon.2
  rw [show f = algebraMap K[X] (RatFunc K) f.num / algebraMap K[X] (RatFunc K) f.denom from
    f.num_div_denom.symm, map_div₀, h1, h2]
  exact div_one 1

section DegInfty

variable (K) [DecidableEq (RatFunc K)]

theorem exists_sub_algebraMap_intDegree_neg {x : RatFunc K}
    (hx : RatFunc.inftyValuation K x ≤ 1) :
    ∃ c : K, x - algebraMap K (RatFunc K) c = 0 ∨
      (x - algebraMap K (RatFunc K) c).intDegree < 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, Or.inl (by simp)⟩
  have hdeg : x.intDegree ≤ 0 := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hx0,
      show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at hx
    exact hx
  have hnum0 : x.num ≠ 0 := RatFunc.num_ne_zero hx0
  have hden0 : x.denom ≠ 0 := x.denom_ne_zero
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact ⟨0, Or.inr (by simpa using hlt)⟩
  have hndeg : x.num.natDegree = x.denom.natDegree := by
    have h2 := heq
    rw [RatFunc.intDegree, sub_eq_zero] at h2
    exact_mod_cast h2
  set c : K := x.num.leadingCoeff / x.denom.leadingCoeff with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hnum0)
      (Polynomial.leadingCoeff_ne_zero.mpr hden0)
  refine ⟨c, ?_⟩
  have hsub : x - algebraMap K (RatFunc K) c
      = algebraMap K[X] (RatFunc K) (x.num - Polynomial.C c * x.denom)
        / algebraMap K[X] (RatFunc K) x.denom := by
    rw [map_sub, map_mul, sub_div, x.num_div_denom, mul_div_assoc,
      div_self ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
      mul_one, IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  rcases eq_or_ne (x.num - Polynomial.C c * x.denom) 0 with hzero | hnz
  · exact Or.inl (by rw [hsub, hzero, _root_.map_zero, zero_div])
  refine Or.inr ?_
  rw [hsub, RatFunc.intDegree_div ((map_ne_zero_iff _
      (IsFractionRing.injective K[X] (RatFunc K))).mpr hnz)
    ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, sub_neg]
  have hCdeg : (Polynomial.C c * x.denom).degree = x.denom.degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C hc0, zero_add]
  have hdegeq : x.num.degree = (Polynomial.C c * x.denom).degree := by
    rw [hCdeg, Polynomial.degree_eq_natDegree hnum0, Polynomial.degree_eq_natDegree hden0,
      hndeg]
  have hlc : x.num.leadingCoeff = (Polynomial.C c * x.denom).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc,
      div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hden0)]
  have hlt := Polynomial.degree_sub_lt_left hdegeq hnum0 hlc
  rw [hdegeq, hCdeg] at hlt
  exact_mod_cast Polynomial.natDegree_lt_natDegree hnz hlt

end DegInfty

section PlaceInfty

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

theorem ord_placeInfty_eq_zero_of_intDegree_eq_zero {f : RatFunc K} (hf : f ≠ 0)
    (h : f.intDegree = 0) : (placeInfty K).ord f = 0 := by
  rw [(placeInfty K).ord_eq_zero_iff_adicValuation_eq_one hf,
    ← (inftyValuation_isEquiv_adicValuation K).eq_one_iff_eq_one,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, h]
  rfl

end PlaceInfty

end RationalFunctionField

namespace Place

section SupportTransfer

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F']
  [FiniteDimensional F F']

variable (w : Place K F')

omit [FiniteDimensional F F'] in
private theorem aeval_mem {Q : Polynomial F} {x : F'}
    (hcoeff : ∀ i, algebraMap F F' (Q.coeff i) ∈ w.toValuationSubring)
    (hx : x ∈ w.toValuationSubring) :
    Polynomial.aeval x Q ∈ w.toValuationSubring := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (hcoeff i) (pow_mem hx i)

theorem exists_coeff_ord_ne_zero {f : F'} (hf : f ≠ 0) (hford : w.ord f ≠ 0) :
    ∃ i < (minpoly F f).natDegree, (minpoly F f).coeff i ≠ 0 ∧
      w.ord (algebraMap F F' ((minpoly F f).coeff i)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set P := minpoly F f with hPdef
  have hint : _root_.IsIntegral F f := Algebra.IsIntegral.isIntegral f
  have hmonic : P.Monic := minpoly.monic hint
  have hdeg : 0 < P.natDegree := minpoly.natDegree_pos hint
  have hc0 : P.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hf
  have hcoeff : ∀ i, algebraMap F F' (P.coeff i) ∈ w.toValuationSubring := by
    intro i
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    · rcases eq_or_ne (P.coeff i) 0 with h0 | h0
      · simp [h0]
      · exact w.mem_of_ord_nonneg (by simpa using h0) (by have := hcon i hi h0; omega)
    · subst hi
      simp [hmonic.coeff_natDegree]
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi]
  have hfmem : f ∈ w.toValuationSubring := by
    refine w.mem_of_eval_monic_eq_zero (P := P.map (algebraMap F F')) (hmonic.map _)
      (fun i => by simpa using hcoeff i) ?_
    rw [Polynomial.eval_map, ← Polynomial.aeval_def, hPdef, minpoly.aeval]
  have hfpos : 0 < w.ord f := lt_of_le_of_ne (w.ord_nonneg_of_mem hfmem) (Ne.symm hford)
  have hkey : algebraMap F F' (P.coeff 0) = -(f * Polynomial.aeval f P.divX) := by
    have hsplit : Polynomial.aeval f (Polynomial.X * P.divX + Polynomial.C (P.coeff 0))
        = (0 : F') := by rw [P.X_mul_divX_add]; exact minpoly.aeval F f
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hsplit
    linear_combination hsplit
  have hcof_mem : Polynomial.aeval f P.divX ∈ w.toValuationSubring :=
    w.aeval_mem (fun i => by rw [Polynomial.coeff_divX]; exact hcoeff (i + 1)) hfmem
  have hcof_ne : Polynomial.aeval f P.divX ≠ 0 := by
    intro h
    rw [h, mul_zero, _root_.neg_zero] at hkey
    exact hc0 (by simpa using hkey)
  have hpos0 : 0 < w.ord (algebraMap F F' (P.coeff 0)) := by
    rw [hkey, w.ord_neg, w.ord_mul hf hcof_ne]
    have := w.ord_nonneg_of_mem hcof_mem
    omega
  have := hcon 0 hdeg hc0
  omega

end SupportTransfer

section Chart

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [Algebra R F]
variable (w : Place K F)

private theorem inv_algebraMap_mem (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring)
    {s : R} (hs : IsUnit (chartHom w hw s)) :
    (algebraMap R F s)⁻¹ ∈ w.toValuationSubring := by
  obtain ⟨u, hu⟩ := hs
  have hcoe : ((u : w.toValuationSubring) : F) = algebraMap R F s := by rw [hu]; rfl
  have h1 : (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F)
      * algebraMap R F s = 1 := by
    have hmul := congrArg (fun a : w.toValuationSubring => (a : F)) u.inv_mul
    push_cast at hmul
    rwa [hcoe] at hmul
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact SetLike.coe_mem _

end Chart

end Place

section Assembly

variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']

end Assembly

end AlgebraicCurve

namespace WeierstrassCurve

section Carrier

variable {F : Type*} [Field F] [DecidableEq F]

def VeluThmOneOddAt (W : WeierstrassCurve F) (Q : W.toAffine.Point) (n : ℕ) : Prop :=
  ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
    (∀ P ∈ W.oddOrderSummingSet Q n, r ≠ P.1) →
    (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Equation
      (W.veluX (W.oddOrderSummingSet Q n) r)
      (W.veluY (W.oddOrderSummingSet Q n) r s)

end Carrier

end WeierstrassCurve

namespace AlgebraicCurve

theorem le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx : x < 1) : x ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_le
  · rw [← exp_log hx0] at hx ⊢
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp] at hx
    rw [exp_le_exp]
    omega

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end Place

namespace RationalFunctionField

variable {K : Type*} [Field K]

theorem ord_ofHeightOneSpectrum_eq_zero_of_notMem (w : HeightOneSpectrum K[X]) {q : K[X]}
    (hq : q ≠ 0) (hmem : q ∉ w.asIdeal) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) q) = 0 := by
  by_contra h
  exact hmem
    ((Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hq).mp h)

section IrreducibleDivisor

variable [DecidableEq (RatFunc K)]

theorem single_add_single_apply_eq_ord {p : K[X]} (hp : Irreducible p)
    (v : Place K (RatFunc K)) :
    (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single (placeInfty K) (-(p.natDegree : ℤ))) v
      = v.ord (algebraMap K[X] (RatFunc K) p) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [Finsupp.add_apply]
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · rw [Finsupp.single_eq_of_ne (Ne.symm (placeInfty_ne_ofHeightOneSpectrum K w)), add_zero]
    by_cases hcase :
        Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w = finitePlace K hp
    · rw [hcase, Finsupp.single_eq_same]
      exact (ord_ofHeightOneSpectrum_of_span (heightOneSpectrumOfIrreducible K hp) hp0
        (heightOneSpectrumOfIrreducible_asIdeal K hp)).symm
    · rw [Finsupp.single_eq_of_ne hcase]
      refine (ord_ofHeightOneSpectrum_eq_zero_of_notMem w hp0 fun hmem => hcase ?_).symm
      have hspan : Ideal.span {p} = w.asIdeal :=
        (PrincipalIdealRing.isMaximal_of_irreducible hp).eq_of_le w.isPrime.ne_top
          ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
      have hwp : w = heightOneSpectrumOfIrreducible K hp :=
        HeightOneSpectrum.ext
          (hspan.symm.trans (heightOneSpectrumOfIrreducible_asIdeal K hp).symm)
      rw [hwp, finitePlace_def]
  · rw [Finsupp.single_eq_of_ne
        (show placeInfty K ≠ finitePlace K hp from
          placeInfty_ne_ofHeightOneSpectrum K (heightOneSpectrumOfIrreducible K hp)),
      Finsupp.single_eq_same, zero_add]
    exact (ord_placeInfty_algebraMap (K := K) hp0).symm

theorem degree_single_add_single {p : K[X]} (hp : Irreducible p) :
    Divisor.degree (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single (placeInfty K) (-(p.natDegree : ℤ))) = 0 := by
  rw [map_add, Divisor.degree_single, Divisor.degree_single, deg_finitePlace, deg_placeInfty]
  push_cast
  ring

end IrreducibleDivisor

def principalDivisor {f : RatFunc K} (hf : f ≠ 0) : Divisor K (RatFunc K) :=
  ⟨(finite_setOf_ord_ne_zero hf).toFinset, fun v => v.ord f, fun v => by
    simp [Set.Finite.mem_toFinset]⟩

@[scoped simp]
theorem principalDivisor_apply {f : RatFunc K} (hf : f ≠ 0) (v : Place K (RatFunc K)) :
    principalDivisor hf v = v.ord f := rfl

theorem degree_principalDivisor {f : RatFunc K} (hf : f ≠ 0) :
    Divisor.degree (principalDivisor hf) = 0 :=
  degree_eq_zero_of_forall_eq_ord (principalDivisor hf) fun _ => rfl

scoped instance instHasPrincipalDivisors : HasPrincipalDivisors K (RatFunc K) where
  exists_divisor _ hf := ⟨principalDivisor hf, fun _ => rfl, degree_principalDivisor hf⟩

end RationalFunctionField

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem ord_algebraMap_s18priv (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hmem : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem' : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
    rw [← map_inv₀]
    exact v.algebraMap_mem' c⁻¹
  have h1 := v.ord_nonneg_of_mem hmem
  have h2 := v.ord_nonneg_of_mem hmem'
  rw [v.ord_inv] at h2
  omega

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

theorem eq_ord_of_addHom_of_nonneg_iff (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring))
    {x : F} (hx : x ≠ 0) : φ x = w.ord x := by
  obtain ⟨t, ht0, ht1⟩ := hone
  have hφ1 : φ 1 = 0 := by
    have := hmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega
  have hinv : ∀ y, y ≠ 0 → φ y⁻¹ = -φ y := by
    intro y hy
    have h1 : φ (y * y⁻¹) = φ y + φ y⁻¹ := hmul y y⁻¹ hy (inv_ne_zero hy)
    rw [mul_inv_cancel₀ hy, hφ1] at h1
    omega
  have hpow : ∀ (y : F), y ≠ 0 → ∀ m : ℕ, φ (y ^ m) = m * φ y := by
    intro y hy m
    induction m with
    | zero => simpa using hφ1
    | succ m ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ hy) hy, ih]
      push_cast
      ring
  have hzpow : ∀ (y : F) (n : ℤ), y ≠ 0 → φ (y ^ n) = n * φ y := by
    intro y n hy
    rcases n with m | m
    · simpa using hpow y hy m
    · rw [zpow_negSucc, hinv _ (pow_ne_zero _ hy), hpow y hy, Int.negSucc_eq]
      push_cast
      ring
  have hsign : ∀ y, y ≠ 0 → (0 ≤ φ y ↔ 0 ≤ w.ord y) := by
    intro y hy
    rw [hiff y hy, w.mem_iff_ord_nonneg hy]
  have hzero : ∀ y, y ≠ 0 → (φ y = 0 ↔ w.ord y = 0) := by
    intro y hy
    have h1 := hsign y hy
    have h2 := hsign y⁻¹ (inv_ne_zero hy)
    rw [hinv y hy, w.ord_inv] at h2
    omega
  have htord : 0 < w.ord t := by
    have h1 := (hsign t ht0).mp (by omega)
    have h2 := (hzero t ht0).not.mp (by omega)
    omega
  have hcancel : ∀ y, y ≠ 0 → w.ord y = φ y * w.ord t := by
    intro y hy
    have hyt : y * t ^ (-(φ y)) ≠ 0 := mul_ne_zero hy (zpow_ne_zero _ ht0)
    have h1 : φ (y * t ^ (-(φ y))) = 0 := by
      rw [hmul _ _ hy (zpow_ne_zero _ ht0), hzpow t _ ht0, ht1]
      ring
    have h2 : w.ord (y * t ^ (-(φ y))) = 0 := (hzero _ hyt).mp h1
    rw [w.ord_mul hy (zpow_ne_zero _ ht0), w.ord_zpow] at h2
    linarith
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hπcancel := hcancel (π : F) hπ0
  rw [w.ord_coe_irreducible hπ] at hπcancel
  have htord1 : w.ord t = 1 := by
    have hdvd : w.ord t ∣ 1 := ⟨φ (π : F), by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    omega
  have := hcancel x hx
  rw [htord1, mul_one] at this
  exact this.symm

end Uniqueness
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 0] valuationSubringAlgebra

section Setup

variable (v : Place K F)

scoped instance (priority := 100) : IsScalarTower v.toValuationSubring F F' :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end Setup

section ValuationDictionary

variable {v : Place K F} {w : Place K F'}

theorem neg_log_valuation_fiberCenter_eq_ord (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) :
    -log ((fiberCenter F' v hw).valuation F' x) = w.ord x := by
  refine eq_ord_of_addHom_of_nonneg_iff w
    (fun y => -log ((fiberCenter F' v hw).valuation F' y)) ?_ ?_ ?_ hx
  · intro a b ha hb
    show -log ((fiberCenter F' v hw).valuation F' (a * b)) =
      -log ((fiberCenter F' v hw).valuation F' a) +
        -log ((fiberCenter F' v hw).valuation F' b)
    rw [map_mul, log_mul ((Valuation.ne_zero_iff _).mpr ha) ((Valuation.ne_zero_iff _).mpr hb)]
    ring
  · obtain ⟨t, ht⟩ := (fiberCenter F' v hw).valuation_exists_uniformizer F'
    refine ⟨t, ?_, ?_⟩
    · intro h
      rw [h, _root_.map_zero] at ht
      exact exp_ne_zero ht.symm
    · show -log ((fiberCenter F' v hw).valuation F' t) = 1
      rw [ht, log_exp]
      ring
  · intro y hy
    have hy0 : (fiberCenter F' v hw).valuation F' y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    change 0 ≤ -log ((fiberCenter F' v hw).valuation F' y) ↔ y ∈ w.toValuationSubring
    have hmem : y ∈ w.toValuationSubring ↔ (fiberCenter F' v hw).valuation F' y ≤ 1 := by
      rw [toValuationSubring_eq_of_restrict_eq hw,
        HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact Iff.rfl
    rw [hmem]
    constructor
    · intro h
      calc (fiberCenter F' v hw).valuation F' y
          = exp (log ((fiberCenter F' v hw).valuation F' y)) := (exp_log hy0).symm
        _ ≤ exp 0 := by rw [exp_le_exp]; omega
        _ = 1 := exp_zero
    · intro h
      have h1 : exp (log ((fiberCenter F' v hw).valuation F' y)) ≤ exp 0 := by
        rw [exp_log hy0, exp_zero]
        exact h
      rw [exp_le_exp] at h1
      omega

theorem le_ord_iff_mem_pow_fiberCenter (hw : w.restrict F = v)
    {c : integralClosureAt F' v} (hc : c ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) ↔
      c ∈ (fiberCenter F' v hw).asIdeal ^ n := by
  have hcF : algebraMap (integralClosureAt F' v) F' c ≠ 0 := by
    simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hc
  rw [← neg_log_valuation_fiberCenter_eq_ord hw hcF,
    HeightOneSpectrum.valuation_of_algebraMap,
    ← HeightOneSpectrum.intValuation_le_pow_iff_mem]
  have h0 : (fiberCenter F' v hw).intValuation c ≠ 0 :=
    HeightOneSpectrum.intValuation_ne_zero _ c hc
  constructor
  · intro h
    calc (fiberCenter F' v hw).intValuation c
        = exp (log ((fiberCenter F' v hw).intValuation c)) := (exp_log h0).symm
      _ ≤ exp (-(n : ℤ)) := by rw [exp_le_exp]; omega
  · intro h
    have h1 : exp (log ((fiberCenter F' v hw).intValuation c)) ≤ exp (-(n : ℤ)) := by
      rw [exp_log h0]
      exact h
    rw [exp_le_exp] at h1
    omega

end ValuationDictionary

section ResidueDictionary

variable {v : Place K F} {w : Place K F'}

def toValuationSubringOfRestrictEq (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.toValuationSubring :=
  (algebraMap (integralClosureAt F' v) F').codRestrict
    w.toValuationSubring.toSubring (forall_mem_of_restrict_eq hw)

def residueOfCenter (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.ResidueField :=
  (IsLocalRing.residue w.toValuationSubring).comp (toValuationSubringOfRestrictEq hw)

omit [FiniteDimensional F F'] in
theorem residueOfCenter_apply (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    residueOfCenter hw c = IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw c) := rfl

theorem ker_residueOfCenter (hw : w.restrict F = v) :
    RingHom.ker (residueOfCenter hw) = (fiberCenter F' v hw).asIdeal := by
  ext c
  rw [RingHom.mem_ker, residueOfCenter_apply, IsLocalRing.residue_eq_zero_iff]
  exact Iff.rfl

theorem surjective_residueOfCenter (hw : w.restrict F = v) :
    Function.Surjective (residueOfCenter hw) := by
  classical
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hx : (x : F') ∈ HeightOneSpectrum.valuationSubringAtPrime F' (fiberCenter F' v hw) := by
    rw [← toValuationSubring_eq_of_restrict_eq hw]
    exact x.2
  obtain ⟨a, s, hs, hxas⟩ := hx
  have hsP : s ∉ (fiberCenter F' v hw).asIdeal := hs
  have hs0 : s ≠ 0 := fun h => hsP (h ▸ (fiberCenter F' v hw).asIdeal.zero_mem)
  have hsF : algebraMap (integralClosureAt F' v) F' s ≠ 0 := by
    simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hs0
  have hsord : w.ord (algebraMap (integralClosureAt F' v) F' s) = 0 := by
    have h1 : ¬ 0 < w.ord (algebraMap (integralClosureAt F' v) F' s) := by
      rw [← mem_fiberCenter_iff_ord_pos hw hs0]
      exact hsP
    have h2 : 0 ≤ w.ord (algebraMap (integralClosureAt F' v) F' s) :=
      w.ord_nonneg_of_mem (forall_mem_of_restrict_eq hw s)
    omega
  have hmax : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  obtain ⟨t, i, hi, hti⟩ := hmax.exists_inv hsP
  have hst : s * t - 1 ∈ (fiberCenter F' v hw).asIdeal := by
    have h1 : s * t - 1 = -i := by linear_combination hti
    rw [h1]
    exact neg_mem hi
  refine ⟨a * t, ?_⟩
  rw [residueOfCenter_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hcoe : ((toValuationSubringOfRestrictEq hw (a * t) - x : w.toValuationSubring) : F')
      = algebraMap (integralClosureAt F' v) F' (a * t) - (x : F') := rfl
  rcases eq_or_ne (toValuationSubringOfRestrictEq hw (a * t) - x) 0 with hzero | hne
  · rw [hzero]
    exact (IsLocalRing.maximalIdeal w.toValuationSubring).zero_mem
  have hcoene : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F') ≠ 0 := by
    intro h
    exact hne (by rwa [← hcoe, ZeroMemClass.coe_eq_zero] at h)
  have hfactor : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F')
      = algebraMap (integralClosureAt F' v) F' (a * t * s - a)
          * (algebraMap (integralClosureAt F' v) F' s)⁻¹ := by
    rw [hxas, map_sub, map_mul (algebraMap (integralClosureAt F' v) F') (a * t) s,
      sub_mul, mul_assoc, mul_inv_cancel₀ hsF, mul_one]
  have hdiffC : a * t * s - a ≠ 0 := by
    intro h
    apply hcoene
    rw [hfactor, h, _root_.map_zero, zero_mul]
  have hdiffP : a * t * s - a ∈ (fiberCenter F' v hw).asIdeal := by
    have h1 : a * t * s - a = a * (s * t - 1) := by ring
    rw [h1]
    exact Ideal.mul_mem_left _ _ hst
  have hmem' : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F')
      ∈ w.toValuationSubring := by
    rw [← hcoe]
    exact Subtype.coe_prop _
  rw [show (toValuationSubringOfRestrictEq hw (a * t) - x)
      = (⟨_, hmem'⟩ : w.toValuationSubring) from Subtype.ext hcoe,
    w.mem_maximalIdeal_iff_ord_pos hcoene hmem']
  rw [hfactor, w.ord_mul (by
      simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hdiffC)
    (inv_ne_zero hsF), w.ord_inv, hsord, _root_.neg_zero, add_zero]
  exact (mem_fiberCenter_iff_ord_pos hw hdiffC).mp hdiffP

def residueFieldEquivQuotientCenter (hw : w.restrict F = v) :
    integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal ≃+* w.ResidueField :=
  (Ideal.quotEquivOfEq (ker_residueOfCenter hw).symm).trans
    ((residueOfCenter hw).quotientKerEquivOfSurjective (surjective_residueOfCenter hw))

def placeCongrEquiv {u u' : Place K F} (h : u = u') :
    u.toValuationSubring ≃+* u'.toValuationSubring where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun x := ⟨x.1, h.symm ▸ x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def restrictResidueFieldEquiv (hw : w.restrict F = v) :
    (w.restrict F).ResidueField ≃+* IsLocalRing.ResidueField v.toValuationSubring :=
  IsLocalRing.ResidueField.mapEquiv (placeCongrEquiv hw)

end ResidueDictionary

end Place

section Identity

variable (K F F' : Type*) [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

def RamificationInertiaIdentity : Prop :=
  ∀ (v : Place K F) (s : Finset (Place K F')), (∀ w : Place K F', w ∈ s ↔ w.restrict F = v) →
    ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = (Module.finrank F F' : ℤ) * (v.deg : ℤ)

end Identity

namespace Divisor

section Pullback

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

theorem degree_eq_finrank_mul_of_forall_eq_ord_algebraMap
    (H : RamificationInertiaIdentity K F F') {g : F}
    {D' : Divisor K F'} (hD' : ∀ w : Place K F', D' w = w.ord (algebraMap F F' g))
    {D : Divisor K F} (hD : ∀ v : Place K F, D v = v.ord g) :
    degree D' = (Module.finrank F F' : ℤ) * degree D := by
  classical
  have hmaps : ∀ w ∈ D'.support, w.restrict F ∈ D.support := by
    intro w hw
    rw [Finsupp.mem_support_iff] at hw ⊢
    intro h0
    apply hw
    rw [hD' w, w.ord_restrict g, hD] at *
    rw [h0, mul_zero]
  have happ : ∀ w : Place K F', D' w = (w.ramificationIndex F : ℤ) * D (w.restrict F) := by
    intro w
    rw [hD' w, w.ord_restrict g, hD]
  rw [degree_eq_sum_support, degree_eq_sum_support,
    ← Finset.sum_fiberwise_of_maps_to hmaps fun w => D' w * (w.deg : ℤ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hfiber : ∀ w : Place K F',
      w ∈ D'.support.filter (fun w => w.restrict F = v) ↔ w.restrict F = v := by
    intro w
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, and_iff_right_iff_imp]
    intro hw
    rw [happ w, hw]
    have he : 0 < w.ramificationIndex F := w.ramificationIndex_pos
    have hv0 : D v ≠ 0 := Finsupp.mem_support_iff.mp hv
    exact mul_ne_zero (by exact_mod_cast he.ne') hv0
  calc
    ∑ w ∈ D'.support with w.restrict F = v, D' w * (w.deg : ℤ)
        = D v * ∑ w ∈ D'.support.filter (fun w => w.restrict F = v),
            (w.ramificationIndex F : ℤ) * (w.deg : ℤ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [happ w, ((hfiber w).mp hw)]
          ring
    _ = D v * ((Module.finrank F F' : ℤ) * (v.deg : ℤ)) := by
          rw [H v _ hfiber]
    _ = (Module.finrank F F' : ℤ) * (D v * (v.deg : ℤ)) := by ring

end Pullback

section Galois

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

theorem _root_.AlgebraicCurve.Place.ord_prod {ι : Type*} (v : Place K F') (s : Finset ι)
    (g : ι → F') (hg : ∀ i ∈ s, g i ≠ 0) :
    v.ord (∏ i ∈ s, g i) = ∑ i ∈ s, v.ord (g i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      v.ord_mul (hg i (Finset.mem_cons_self i s))
        (Finset.prod_ne_zero_iff.mpr fun j hj => hg j (Finset.mem_cons_of_mem hj)),
      ih fun j hj => hg j (Finset.mem_cons_of_mem hj)]

variable [FiniteDimensional F F']

theorem sum_smul_apply_eq_ord_prod {f : F'} (hf : f ≠ 0)
    {D : Divisor K F'} (hD : ∀ w : Place K F', D w = w.ord f) (w : Place K F') :
    (∑ σ : F' ≃ₐ[F] F', (AlgEquiv.restrictScalars K σ) • D) w
      = w.ord (∏ σ : F' ≃ₐ[F] F', σ f) := by
  classical
  rw [w.ord_prod _ _ fun σ _ => by simpa using hf, Finset.sum_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [smul_apply, hD]
  have h := Place.ord_smul (AlgEquiv.restrictScalars K σ)
    ((AlgEquiv.restrictScalars K σ)⁻¹ • w) f
  rw [smul_inv_smul] at h
  exact h.symm

theorem degree_eq_zero_of_isGalois [IsGalois F F'] [HasPrincipalDivisors K F]
    (H : RamificationInertiaIdentity K F F')
    {f : F'} {D : Divisor K F'} (hD : ∀ w : Place K F', D w = w.ord f) :
    degree D = 0 := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · have : D = 0 := Finsupp.ext fun w => by simpa using hD w
    rw [this, _root_.map_zero]
  set E : Divisor K F' := ∑ σ : F' ≃ₐ[F] F', (AlgEquiv.restrictScalars K σ) • D with hE
  have hEord : ∀ w : Place K F', E w = w.ord (algebraMap F F' (Algebra.norm F f)) := by
    intro w
    rw [hE, sum_smul_apply_eq_ord_prod hf hD w, Algebra.norm_eq_prod_automorphisms F f]
  have hnorm : Algebra.norm F f ≠ 0 := (Algebra.norm_ne_zero_iff (R := F)).mpr hf
  obtain ⟨D₀, hD₀, hD₀deg⟩ := HasPrincipalDivisors.exists_divisor (K := K)
    (Algebra.norm F f) hnorm
  have hEdeg : degree E = 0 := by
    rw [degree_eq_finrank_mul_of_forall_eq_ord_algebraMap H hEord hD₀, hD₀deg, mul_zero]
  have hEdeg' : degree E = (Module.finrank F F' : ℤ) * degree D := by
    rw [hE, map_sum]
    simp only [degree_smul]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    exact_mod_cast (Nat.card_eq_fintype_card (α := F' ≃ₐ[F] F')).symm.trans
      (IsGalois.card_aut_eq_finrank F F')
  have hpos : (0 : ℤ) < (Module.finrank F F' : ℤ) := by
    exact_mod_cast Module.finrank_pos (R := F) (M := F')
  rw [hEdeg] at hEdeg'
  exact (mul_eq_zero.mp hEdeg'.symm).resolve_left hpos.ne'

end Galois

end Divisor

namespace RationalFunctionField

variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']

def principalDivisorOf {f : F'} (hf : f ≠ 0) : Divisor K F' :=
  ⟨(finite_setOf_ord_ne_zero_of_finiteDimensional hf).toFinset, fun w => w.ord f, fun w => by
    simp [Set.Finite.mem_toFinset]⟩

theorem degree_eq_zero_of_forall_eq_ord_of_isGalois [IsGalois (RatFunc K) F']
    (H : RamificationInertiaIdentity K (RatFunc K) F')
    {f : F'} {D : Divisor K F'} (hD : ∀ w : Place K F', D w = w.ord f) :
    Divisor.degree D = 0 :=
  Divisor.degree_eq_zero_of_isGalois H hD

theorem hasPrincipalDivisors_of_isGalois [IsGalois (RatFunc K) F']
    (H : RamificationInertiaIdentity K (RatFunc K) F') :
    HasPrincipalDivisors K F' where
  exists_divisor _ hf :=
    ⟨principalDivisorOf hf, fun _ => rfl,
      degree_eq_zero_of_forall_eq_ord_of_isGalois H fun _ => rfl⟩

end RationalFunctionField

end AlgebraicCurve

namespace WeierstrassCurve

namespace Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

theorem weierstrassQuadratic_natDegree_le : (weierstrassQuadratic W).natDegree ≤ 2 := by
  rw [Polynomial.natDegree_le_iff_degree_le]
  refine le_trans (Polynomial.degree_add_le _ _) (max_le ?_ ?_)
  · exact (Polynomial.degree_X_pow 2).le
  · exact le_of_lt weierstrassQuadratic_sub_degree_lt

scoped instance : FiniteDimensional (RatFunc F) W.FunctionField := by
  have h1 : FiniteDimensional (RatFunc F)
      (IntermediateField.adjoin (RatFunc F) {yCoord W}) :=
    IntermediateField.adjoin.finiteDimensional isIntegral_yCoord
  rw [adjoin_yCoord_eq_top] at h1
  exact (IntermediateField.topEquiv
    (F := RatFunc F) (E := W.FunctionField)).toLinearEquiv.finiteDimensional

theorem splits_weierstrassQuadratic_map :
    ((weierstrassQuadratic W).map
      (algebraMap (RatFunc F) W.FunctionField)).Splits := by
  have hroot : ((weierstrassQuadratic W).map
      (algebraMap (RatFunc F) W.FunctionField)).IsRoot (yCoord W) := by
    change ((weierstrassQuadratic W).map
      (algebraMap (RatFunc F) W.FunctionField)).eval (yCoord W) = 0
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact aeval_yCoord_weierstrassQuadratic
  have hkey : (X - C (yCoord W))
        * (((weierstrassQuadratic W).map (algebraMap (RatFunc F) W.FunctionField))
          /ₘ (X - C (yCoord W)))
      = (weierstrassQuadratic W).map (algebraMap (RatFunc F) W.FunctionField) :=
    mul_divByMonic_eq_iff_isRoot.mpr hroot
  rw [← hkey, splits_X_sub_C_mul_iff]
  refine Polynomial.Splits.of_natDegree_le_one ?_
  rw [natDegree_divByMonic _ (monic_X_sub_C (yCoord W))]
  have h1 : ((weierstrassQuadratic W).map
      (algebraMap (RatFunc F) W.FunctionField)).natDegree ≤ 2 :=
    le_trans Polynomial.natDegree_map_le weierstrassQuadratic_natDegree_le
  have h2 : (X - C (yCoord W)).natDegree = 1 := Polynomial.natDegree_X_sub_C _
  omega

theorem isSplittingField_weierstrassQuadratic :
    Polynomial.IsSplittingField (RatFunc F) W.FunctionField (weierstrassQuadratic W) := by
  constructor
  · exact splits_weierstrassQuadratic_map
  · rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← adjoin_yCoord_eq_top,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        isIntegral_yCoord.isAlgebraic]
    refine Algebra.adjoin_mono ?_
    rw [Set.singleton_subset_iff, Polynomial.mem_rootSet]
    exact ⟨weierstrassQuadratic_monic.ne_zero, aeval_yCoord_weierstrassQuadratic⟩

end Affine

end WeierstrassCurve

namespace AlgebraicCurve

namespace Place

attribute [local instance 0] valuationSubringAlgebra

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

theorem sum_ramificationIndex_mul_inertiaDeg_of_forall_mem_iff
    (v : Place K F) (s : Finset (Place K F'))
    (hs : ∀ w : Place K F', w ∈ s ↔ w.restrict F = v) :
    ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)
      = (Module.finrank F F' : ℤ) := by
  classical
  let _ : Module.IsTorsionFree v.toValuationSubring F' :=
    Module.IsTorsionFree.trans_faithfulSMul v.toValuationSubring F F'
  have hkey :
      ∑ P ∈ IsDedekindDomain.primesOverFinset
          (IsLocalRing.maximalIdeal v.toValuationSubring) (integralClosureAt F' v),
        Ideal.ramificationIdx' (IsLocalRing.maximalIdeal v.toValuationSubring) P *
          Ideal.inertiaDeg P v.toValuationSubring =
            Module.finrank F F' := by
    let p := IsLocalRing.maximalIdeal v.toValuationSubring
    let S := integralClosureAt F' v
    let e : {P // P ∈ IsDedekindDomain.primesOverFinset p S} ≃ p.primesOver S :=
      Set.equivOfEq (IsDedekindDomain.coe_primesOverFinset (maximalIdeal_ne_bot v) S)
    change (∑ P ∈ IsDedekindDomain.primesOverFinset p S,
      p.ramificationIdx' P * P.inertiaDeg v.toValuationSubring) = Module.finrank F F'
    calc
      _ = ∑ P : {P // P ∈ IsDedekindDomain.primesOverFinset p S},
          p.ramificationIdx' P.1 * P.1.inertiaDeg v.toValuationSubring := by
            rw [← Finset.sum_attach, Finset.univ_eq_attach]
      _ = ∑ P : p.primesOver S,
          P.1.ramificationIdx v.toValuationSubring *
            P.1.inertiaDeg v.toValuationSubring := by
            apply Fintype.sum_equiv e
            intro P
            have hmem : P.1 ∈ p.primesOver S := (e P).2
            let : P.1.IsPrime := hmem.1
            let : P.1.LiesOver p := hmem.2
            let : P.1.IsMaximal :=
              (inferInstance : P.1.IsPrime).isMaximal
                (Ideal.ne_bot_of_mem_primesOver (maximalIdeal_ne_bot v) hmem)
            change p.ramificationIdx' P.1 * P.1.inertiaDeg v.toValuationSubring =
              P.1.ramificationIdx v.toValuationSubring *
                P.1.inertiaDeg v.toValuationSubring
            rw [Ideal.ramificationIdx'_eq_ramificationIdx p P.1
              (maximalIdeal_ne_bot v)]
      _ = Module.finrank v.toValuationSubring S :=
        Ideal.sum_ramification_inertia_eq_finrank p S
      _ = Module.finrank F F' :=
        IsIntegralClosure.rank v.toValuationSubring F F' S
  rw [← hkey]
  push_cast
  refine Finset.sum_bij
    (fun w hw => (fiberCenter F' v ((hs w).mp hw)).asIdeal) ?_ ?_ ?_ ?_
  · intro w hw
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)]
    exact ⟨(fiberCenter F' v ((hs w).mp hw)).isPrime,
      fiberCenter_liesOver ((hs w).mp hw)⟩
  · intro w hw w' hw' h
    exact eq_of_fiberCenter_eq ((hs w).mp hw) ((hs w').mp hw')
      (HeightOneSpectrum.ext h)
  · intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)] at hP
    obtain ⟨hP1, hP2⟩ := hP
    have hPne : P ≠ ⊥ := by
      intro h
      apply maximalIdeal_ne_bot v
      have h2 := hP2.over
      rw [h, Ideal.under_def, Ideal.comap_bot_of_injective _
        (algebraMap_integralClosureAt_injective v)] at h2
      exact h2
    refine ⟨placeOfPrime ⟨P, hP1, hPne⟩,
      (hs _).mpr (restrict_placeOfPrime ⟨P, hP1, hPne⟩), ?_⟩
    exact congrArg HeightOneSpectrum.asIdeal
      (fiberCenter_placeOfPrime (⟨P, hP1, hPne⟩ :
        HeightOneSpectrum (integralClosureAt F' v)))
  · intro w hw
    rw [ramificationIndex_eq_ramificationIdx_fiberCenter v ((hs w).mp hw),
      inertiaDeg_eq_inertiaDeg_fiberCenter ((hs w).mp hw)]

theorem sum_ramificationIndex_mul_deg_of_forall_mem_iff
    (v : Place K F) (s : Finset (Place K F'))
    (hs : ∀ w : Place K F', w ∈ s ↔ w.restrict F = v) :
    ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = (Module.finrank F F' : ℤ) * (v.deg : ℤ) := by
  have hsum := sum_ramificationIndex_mul_inertiaDeg_of_forall_mem_iff v s hs
  calc ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = ∑ w ∈ s, (v.deg : ℤ) * ((w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        have hdeg : (w.restrict F).deg * w.inertiaDeg F = w.deg :=
          deg_restrict_mul_inertiaDeg (K := K) (F := F) (w := w)
        rw [(hs w).mp hw] at hdeg
        rw [← hdeg]
        push_cast
        ring
    _ = (v.deg : ℤ) * ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) := by
        rw [Finset.mul_sum]
    _ = (Module.finrank F F' : ℤ) * (v.deg : ℤ) := by rw [hsum]; ring

end Place

theorem ramificationInertiaIdentity_of_finiteDimensional
    (K F F' : Type*) [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] :
    RamificationInertiaIdentity K F F' := fun v s hs =>
  Place.sum_ramificationIndex_mul_deg_of_forall_mem_iff v s hs

namespace RationalFunctionField

variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']

scoped instance (priority := 50) instHasPrincipalDivisorsOfIsGalois [IsGalois (RatFunc K) F'] :
    HasPrincipalDivisors K F' :=
  hasPrincipalDivisors_of_isGalois
    (ramificationInertiaIdentity_of_finiteDimensional K (RatFunc K) F')

end RationalFunctionField

end AlgebraicCurve

open AlgebraicCurve

namespace Polynomial
variable {K : Type*} [Field K]

theorem separable_X_sq_add_C_mul_X_sub_C {b c : K} (h : b ^ 2 + 4 * c ≠ 0) :
    (X ^ 2 + (C b * X - C c) : K[X]).Separable := by
  rw [Polynomial.separable_def']
  refine ⟨C (-(4 * (b ^ 2 + 4 * c)⁻¹)),
    C ((b ^ 2 + 4 * c)⁻¹) * (C 2 * X + C b), ?_⟩
  have hd : derivative (X ^ 2 + (C b * X - C c) : K[X]) = C 2 * X + C b := by
    simp only [derivative_add, derivative_sub, derivative_mul, derivative_X_pow,
      derivative_C, derivative_X, mul_one, zero_mul, sub_zero]
    ring_nf
  rw [hd]
  have hkey : C (-(4 * (b ^ 2 + 4 * c)⁻¹)) * (X ^ 2 + (C b * X - C c))
        + C ((b ^ 2 + 4 * c)⁻¹) * (C 2 * X + C b) * (C 2 * X + C b)
      = C ((b ^ 2 + 4 * c)⁻¹ * (b ^ 2 + 4 * c)) := by
    simp only [_root_.map_neg, map_mul, map_add, map_pow, map_ofNat]
    ring
  rw [hkey, inv_mul_cancel₀ h, map_one]

end Polynomial

namespace WeierstrassCurve

namespace Affine

open WeierstrassCurve.Affine WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

def wqDiscPoly : F[X] :=
  (C W.a₁ * X + C W.a₃) ^ 2 + C 4 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)

variable {W}

theorem weierstrassQuadratic_separable (h : wqDiscPoly W ≠ 0) :
    (weierstrassQuadratic W).Separable := by
  have hinj : Function.Injective (algebraMap F[X] (RatFunc F)) :=
    IsFractionRing.injective F[X] (RatFunc F)
  have hC4 : (4 : RatFunc F) = algebraMap F[X] (RatFunc F) (C 4) := by
    rw [map_ofNat, map_ofNat]
  have h2 : (algebraMap F[X] (RatFunc F) (C W.a₁ * X + C W.a₃)) ^ 2
        + 4 * (algebraMap F[X] (RatFunc F) (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆))
      ≠ 0 := by
    rw [hC4, ← map_mul, ← map_pow, ← map_add]
    exact fun hcon => h (hinj (hcon.trans (_root_.map_zero _).symm))
  rw [show weierstrassQuadratic W
      = X ^ 2 + (C (algebraMap F[X] (RatFunc F) (C W.a₁ * X + C W.a₃)) * X
        - C (algebraMap F[X] (RatFunc F) (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆))) from
    rfl]
  exact separable_X_sq_add_C_mul_X_sub_C h2

theorem isGalois_functionField_of_wqDiscPoly_ne_zero (h : wqDiscPoly W ≠ 0) :
    IsGalois (RatFunc F) W.FunctionField :=
  haveI : (weierstrassQuadratic W).IsSplittingField (RatFunc F) W.FunctionField :=
    isSplittingField_weierstrassQuadratic
  IsGalois.of_separable_splitting_field (weierstrassQuadratic_separable h)

theorem hasPrincipalDivisors_functionField_of_wqDiscPoly_ne_zero (h : wqDiscPoly W ≠ 0) :
    HasPrincipalDivisors F W.FunctionField :=
  haveI := isGalois_functionField_of_wqDiscPoly_ne_zero h
  RationalFunctionField.instHasPrincipalDivisorsOfIsGalois

private theorem natDegree_wqLinear_sq_le :
    ((C W.a₁ * X + C W.a₃ : F[X]) ^ 2).natDegree ≤ 2 := by
  refine le_trans natDegree_pow_le ?_
  have : (C W.a₁ * X + C W.a₃ : F[X]).natDegree ≤ 1 := by
    refine le_trans (natDegree_add_le _ _) ?_
    simp only [natDegree_C, max_le_iff]
    exact ⟨le_trans (natDegree_C_mul_le _ _) (by simp), by omega⟩
  omega

private theorem natDegree_wqCubic :
    (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : F[X]).natDegree = 3 := by
  rw [show (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : F[X])
      = C 1 * X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ from by rw [map_one, one_mul]]
  exact natDegree_cubic one_ne_zero

theorem wqDiscPoly_ne_zero (h : (2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0) :
    wqDiscPoly W ≠ 0 := by
  by_cases h2 : (2 : F) = 0
  · have hC4 : (C (4 : F) : F[X]) = 0 := by
      rw [show (4 : F) = 2 * 2 from by norm_num, h2, mul_zero, _root_.map_zero]
    have heq : wqDiscPoly W = (C W.a₁ * X + C W.a₃) ^ 2 := by
      simp only [wqDiscPoly, hC4, zero_mul, add_zero]
    rw [heq]
    refine pow_ne_zero 2 ?_
    have ha : W.a₁ ≠ 0 ∨ W.a₃ ≠ 0 := h.resolve_left (· h2)
    intro hcon
    rcases ha with ha | ha
    · have h1 := congrArg (·.coeff 1) hcon
      simp only [coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_C,
        ite_eq_right one_ne_zero, add_zero, coeff_zero] at h1
      exact ha h1
    · have h0 := congrArg (·.coeff 0) hcon
      simp only [coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, zero_add,
        coeff_C_zero, coeff_zero] at h0
      exact ha h0
  · have h4 : (4 : F) ≠ 0 := by
      rw [show (4 : F) = 2 * 2 from by norm_num]; exact mul_ne_zero h2 h2
    intro hcon
    have hdeg : (wqDiscPoly W).natDegree = 3 := by
      rw [show wqDiscPoly W = C (4 : F) * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)
            + (C W.a₁ * X + C W.a₃) ^ 2 from by simp only [wqDiscPoly]; ring,
        natDegree_add_eq_left_of_natDegree_lt
          (by rw [natDegree_C_mul h4, natDegree_wqCubic];
              exact lt_of_le_of_lt natDegree_wqLinear_sq_le (by omega)),
        natDegree_C_mul h4, natDegree_wqCubic]
    rw [hcon, natDegree_zero] at hdeg
    omega

end Affine

end WeierstrassCurve

section

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace WeierstrassCurve

section HPD

variable {F : Type*} [Field F]

theorem kw_veluHPDSupplier_of_two_ne_zero (h2 : (2 : F) ≠ 0) :
    ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
      HasPrincipalDivisors F W.toAffine.FunctionField :=
  fun _W _hΔ => Affine.hasPrincipalDivisors_functionField_of_wqDiscPoly_ne_zero
    (Affine.wqDiscPoly_ne_zero (Or.inl h2))

end HPD

end WeierstrassCurve

end

namespace WeierstrassCurve

section CharAgnosticOdd

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

variable (F) in
theorem kw_no6_hroute_veluDeficitIsConstantAt_odd_of_two_ne_zero (h2 : (2 : F) ≠ 0)
    {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitIsConstantAt F p :=
  veluDeficitIsConstantAt_of_ordNonneg_of_dedekind
    (kw_veluHPDSupplier_of_two_ne_zero h2) kw_hDDTerm
    (kw_veluDeficitFunOrdNonnegAt_odd F kw_hDDTerm hp3 hpodd)

variable (F) in
theorem kw_no6_hroute_veluDeficitConstancyAt_odd_of_two_ne_zero (h2 : (2 : F) ≠ 0)
    {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitConstancyAt F p := by
  have : Infinite F := kw_infinite_of_isAlgClosed
  refine veluDeficitConstancyAt_of_isConstant_of_constantZero F
    (kw_no6_hroute_veluDeficitIsConstantAt_odd_of_two_ne_zero F h2 hp3 hpodd)
    (kw_veluDeficitConstantIsZeroAt_odd hp3 hpodd ?_)
  exact kw_veluDeficitCrossQuadProdDegLtAt_odd hp3 hpodd
    (kw_veluDeficitCrossQuadCubeBetaDegLtAt_odd hp3 hpodd
      (kw_veluDeficitCrossQuadBetaOnlyDegLtAt_odd
        (veluDeficitCrossQuadBetaSDecompDegLtAt_of_betaSq_of_alphaBeta
          (kw_veluDeficitCrossQuadBetaSqDecompDegLtAt_odd hp3 hpodd)
          (kw_veluDeficitCrossQuadAlphaBetaDecompDegLtAt_odd hp3 hpodd))))

variable {W : WeierstrassCurve F} {Q : W.toAffine.Point} {p : ℕ}

theorem kw_no6_hroute_veluThmOneOddAt_odd_of_two_ne_zero (h2 : (2 : F) ≠ 0)
    (hΔ : W.Δ ≠ 0) (hp3 : 3 ≤ p) (hpodd : Odd p) (hord : addOrderOf Q = p) :
    VeluThmOneOddAt W Q ((p - 1) / 2) := by
  have hQ0 : Q ≠ 0 := by intro h; rw [h, addOrderOf_zero] at hord; omega
  obtain ⟨x₀, y₀, h₀, rfl, -⟩ := exists_some_of_ne_zero hQ0
  intro r s hrs hav
  exact (W.veluQuotient_equation_iff_veluDeficit_eq_zero _ r s).mpr
    (kw_no6_hroute_veluDeficitConstancyAt_odd_of_two_ne_zero F h2 hp3 hpodd
      W hΔ x₀ y₀ h₀ hord hrs hav)

end CharAgnosticOdd

end WeierstrassCurve

theorem solution
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    (W : WeierstrassCurve L) [W.IsElliptic] (n : ℕ) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) {x y : L} (hxy : W.toAffine.Equation x y)
    (hx : ∀ A ∈ W.oddOrderSummingSet Q n, x ≠ A.1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Equation
      (W.veluX (W.oddOrderSummingSet Q n) x) (W.veluY (W.oddOrderSummingSet Q n) x y) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : W.oddOrderSummingSet Q 0 = ∅ := by simp [WeierstrassCurve.oddOrderSummingSet]
    rw [h0, WeierstrassCurve.veluQuotient_empty, WeierstrassCurve.veluX_empty,
      WeierstrassCurve.veluY_empty]
    exact hxy
  · have hp3 : 3 ≤ 2 * n + 1 := by omega
    have hpodd : Odd (2 * n + 1) := ⟨n, rfl⟩
    have hn_eq : ((2 * n + 1) - 1) / 2 = n := by omega
    have key := WeierstrassCurve.kw_no6_hroute_veluThmOneOddAt_odd_of_two_ne_zero
      (W := W) (Q := Q) h2 W.Δ'.ne_zero hp3 hpodd hQ
    rw [hn_eq] at key
    exact key hxy hx

end privateSection

public section publicSection

open WeierstrassCurve

theorem WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    (W : WeierstrassCurve L) [W.IsElliptic] (n : ℕ) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) {x y : L} (hxy : W.toAffine.Equation x y)
    (hx : ∀ A ∈ W.oddOrderSummingSet Q n, x ≠ A.1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Equation
      (W.veluX (W.oddOrderSummingSet Q n) x) (W.veluY (W.oddOrderSummingSet Q n) x y) :=
  solution h2 W n Q hQ hxy hx

end publicSection
