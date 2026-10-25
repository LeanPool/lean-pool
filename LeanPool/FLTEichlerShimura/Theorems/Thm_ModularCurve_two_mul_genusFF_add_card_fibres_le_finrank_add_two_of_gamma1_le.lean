/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Based on Prove2Me node ModularCurve.two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le
(cb08000f-90f3-517d-ad94-c089495b2122) by Claude (2026-09-05).

Proof based on Prove2Me submission 42a0726f-f7f5-5092-b94c-6cadd93ca7fe
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_Repartitions
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_JqCoeff
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_X1

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_D_ne_zero_of_ord_eq_one
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_one
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import LeanPool.FLTEichlerShimura.Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_transcendental_jqModC
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_sum_support
import LeanPool.FLTEichlerShimura.Definitions.Def_P2M_Util
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star

/-!
# Riemann–Hurwitz inequality for j on X(Γ) over ℚ̄

Theorem statement: `ModularCurve.two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le`
(`cb08000f-90f3-517d-ad94-c089495b2122`), by Claude, 2026-09-05.

Proof: submission `42a0726f-f7f5-5092-b94c-6cadd93ca7fe`, by Claude, 2026-09-05 (ACCEPTED); locally
adapted.

Let $M$ be a nonzero natural number and let $\Gamma$ be a subgroup of $\mathrm{SL}(2,\mathbb{Z})$
containing $\Gamma_1(M)$. Let $F_0 =$ [`ModularCurve.qExpFunctionFieldC ℚ
Γ`](def/ModularCurve_X1.html#L101) be the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$
by the quotients $p_f/p_g$ of integral $q$-expansions of modular forms $f,g$ of a common weight on
$\Gamma$ (viewed in $\mathrm{GL}(2,\mathbb{R})$), the denominator series being nonzero, and let $F$
be its base change `laurentBaseChange`, namely the subfield of $\bar{\mathbb{Q}}((q))$ generated
over $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ` by the coefficientwise image of $F_0$. Let $y \in F$
be an element whose underlying Laurent series is `jqModC`, i.e. $q^{-1}$ times the power series
$E_4^3 \cdot \eta^{-24}$-type numerator `jNum` with coefficients mapped into $\bar{\mathbb{Q}}$.
Places of $F/\bar{\mathbb{Q}}$ are valuation subrings of $F$ containing $\bar{\mathbb{Q}}$, distinct
from $F$ itself and principal, with $\mathrm{ord}$ the associated normalised integer valuation, and
`genusFF` is the $\bar{\mathbb{Q}}$-dimension of the first cohomology $H^1$ of the zero divisor. The
assertion is that twice the genus of $F/\bar{\mathbb{Q}}$, plus the numbers (as `Nat.card` of the
corresponding subtypes of places) of places where $y$ has a pole, where $y$ has a zero, and where
$y-1728$ has a zero, is at most $[F : \bar{\mathbb{Q}}(y)] + 2$, the degree being the
$\bar{\mathbb{Q}}(y)$-finrank of $F$ for $\bar{\mathbb{Q}}(y)$ the intermediate field generated by
$y$.

This is the Riemann–Hurwitz count, in inequality form, for the covering $j \colon X(\Gamma) \to X(1)
= \mathbb{P}^1_j$ realised on the $q$-expansion model of the function field of $X(\Gamma)$ over
$\bar{\mathbb{Q}}$: the ramification of $j$ occurs only above $j = \infty, 0, 1728$. It is used to
obtain the corresponding equality
[`ModularCurve.two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le`]
(thm.html#ModularCurve.two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le)
and, from there, the comparison of genera between the $q$-expansion model over $\bar{\mathbb{Q}}$
and the reduction used for the modular curves $X_H$.

## Explanation of the source proof

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ModularCurve_two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le.lean

<!-- Generated by add_prove2me_provenance.py -->
-/


section privateSection


open AlgebraicCurve Divisor

namespace P2MW.S_OVERLONG_7a292264


noncomputable section

open scoped MatrixGroups
p2m_open "AlgebraicCurve IntermediateField KaehlerDifferential ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC coeffMap coeffMap_single coeffMap_coeffMap \
  coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange \
  coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff jqModC map_jqModC \
  ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728 \
  JOneES.exists_transcendental_finiteDimensional_laurentBaseChange transcendental_jqModC"
namespace RiemannHurwitzCount
p2m_open "ModularCurve"

universe u v

section Package

variable (k : Type u) [Field k] {F : Type v} [Field F] [Algebra k F]
  (x : F) (hx : Transcendental k x) (hfin : FiniteDimensional k⟮x⟯ F)
  (hsep : Algebra.IsSeparable k⟮x⟯ F)

include hx hfin hsep

theorem isCurveOver_pkg : IsCurveOver k F :=
  AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable k F x hx hfin hsep

omit hsep in
theorem essFiniteType_pkg : Algebra.EssFiniteType k F :=
  AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfin

theorem with_ratFunc {P : Prop}
    (h : ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F],
      algebraMap (RatFunc k) F RatFunc.X = x →
      Module.finrank (RatFunc k) F = Module.finrank k⟮x⟯ F → P) : P := by
  have := hfin
  have := hsep
  let e : RatFunc k ≃ₐ[k] k⟮x⟯ := RatFunc.algEquivOfTranscendental x hx
  let : Algebra (RatFunc k) F := ((algebraMap k⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc k) F) (e.symm.toRingEquiv : k⟮x⟯ →+* RatFunc k)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap k⟮x⟯ F) := by
    ext y
    change algebraMap k⟮x⟯ F (e (e.symm y)) = algebraMap k⟮x⟯ F y
    rw [e.apply_symm_apply]
  have : IsScalarTower k (RatFunc k) F := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap k F a = algebraMap k⟮x⟯ F (e (algebraMap k (RatFunc k) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  have hfd : FiniteDimensional (RatFunc k) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have : Algebra.IsSeparable (RatFunc k) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have hX : algebraMap (RatFunc k) F RatFunc.X = x := by
    change algebraMap k⟮x⟯ F (e RatFunc.X) = x
    have h := RatFunc.algEquivOfTranscendental_X x hx
    exact h
  have hn : Module.finrank (RatFunc k) F = Module.finrank k⟮x⟯ F :=
    Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl F) (by ext y; rfl)
  exact h hX hn

variable [IsAlgClosed k]

theorem hasCanonicalDivisor_pkg : HasCanonicalDivisor (K := k) (F := F) := by
  have := isCurveOver_pkg k x hx hfin hsep
  have := essFiniteType_pkg k x hx hfin
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

theorem dCoordGenerates_pkg : ∀ v : Place k F, v.DCoordGenerates := by
  have := isCurveOver_pkg k x hx hfin hsep
  have := essFiniteType_pkg k x hx hfin
  exact AlgebraicCurve.dCoordGenerates_of_isCurveOver

theorem riemannRoch_and_constantsAreBase_pkg :
    haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
    FunctionFieldRiemannRoch k F ∧ ConstantsAreBase k F := by
  classical
  have := hfin
  have := isCurveOver_pkg k x hx hfin hsep
  have := hasCanonicalDivisor_pkg k x hx hfin hsep
  have := dCoordGenerates_pkg k x hx hfin hsep
  have : IsCurveOver k (RatFunc k) := AlgebraicCurve.isCurveOver_ratFunc k
  have : Algebra.EssFiniteType (Polynomial k) (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial k))
  have : Algebra.EssFiniteType k (RatFunc k) :=
    Algebra.EssFiniteType.comp k (Polynomial k) (RatFunc k)
  have : ∀ v : Place k (RatFunc k), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  refine with_ratFunc k x hx hfin hsep ?_
  intro _ _ _ _ _ _
  have : Algebra.IsIntegral (RatFunc k) F := Algebra.IsIntegral.of_finite _ _
  exact ⟨AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver,
    AlgebraicCurve.constantsAreBase_of_isAlgClosed k F⟩

theorem genus_eq_genusFF_pkg :
    haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
    genus k F = genusFF k F := by
  have := isCurveOver_pkg k x hx hfin hsep
  have := hasCanonicalDivisor_pkg k x hx hfin hsep
  have := dCoordGenerates_pkg k x hx hfin hsep
  have := essFiniteType_pkg k x hx hfin
  have rr := riemannRoch_and_constantsAreBase_pkg k x hx hfin hsep
  have hSG : StichtenothGenusExists k F :=
    AlgebraicCurve.stichtenothGenusExists_of_isCurveOver rr.2
  have wda : WeilDualityAdelic k F :=
    AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists rr.1 hSG
  exact AlgebraicCurve.genus_eq_genusFF rr.1 wda rr.2

theorem degree_canonical_pkg :
    haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
    ∀ {ω : Ω[F⁄k]} (hω : ω ≠ 0),
      Divisor.degree (canonicalDivisorOf hω) = 2 * (genusFF k F : ℤ) - 2 := by
  intro ω hω
  have := isCurveOver_pkg k x hx hfin hsep
  have := hasCanonicalDivisor_pkg k x hx hfin hsep
  have := dCoordGenerates_pkg k x hx hfin hsep
  have rr := riemannRoch_and_constantsAreBase_pkg k x hx hfin hsep
  rw [← genus_eq_genusFF_pkg k x hx hfin hsep]
  exact AlgebraicCurve.degree_canonicalDivisor_eq_of_riemannRoch rr.1 rr.2 hω

end Package

section Bridge

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [PerfectField K]
  (x : F) [FiniteDimensional K⟮x⟯ F]

omit [PerfectField K] [FiniteDimensional K⟮x⟯ F] in
theorem exists_dCoord_eq_D (v : Place K F) : ∃ t : F, v.ord t = 1 ∧ v.dCoord = D K F t :=
  ⟨((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F),
    v.ord_coe_irreducible
      (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec, rfl⟩

omit [PerfectField K] [FiniteDimensional K⟮x⟯ F] in
theorem coeff_unique {η : Ω[F⁄K]} (hη : η ≠ 0) {a b : F} (h : a • η = b • η) : a = b := by
  have h0 : (a - b) • η = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hη

include x in
theorem ordDiff_eq_ordDifferential (v : Place K F) [v.DCoordGenerates]
    (ω : Ω[F⁄K]) : v.ordDiff ω = v.ordDifferential ω := by
  obtain ⟨t₂, ht₂, hdc⟩ := exists_dCoord_eq_D v
  have ht₁ : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt v.exists_ord_eq_one
  have hc_smul : Place.diffCoeff v.uniformizer_alt (D K F t₂) • D K F v.uniformizer_alt = D K F t₂
    :=
    Place.diffCoeff_smul_D_of_ord_eq_one x v ht₁ _
  have hc'_smul : Place.diffCoeff t₂ (D K F v.uniformizer_alt) • D K F t₂ = D K F v.uniformizer_alt
    :=
    Place.diffCoeff_smul_D_of_ord_eq_one x v ht₂ _
  have hD₁ : D K F v.uniformizer_alt ≠ 0 := Place.D_ne_zero_of_ord_eq_one x v ht₁
  have hcc' : Place.diffCoeff t₂ (D K F v.uniformizer_alt) *
      Place.diffCoeff v.uniformizer_alt (D K F t₂) = 1 := by
    refine coeff_unique hD₁ ?_
    rw [mul_smul, hc_smul, hc'_smul, one_smul]
  have hc0 : Place.diffCoeff v.uniformizer_alt (D K F t₂) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcc'
    exact zero_ne_one hcc'
  have hc'0 : Place.diffCoeff t₂ (D K F v.uniformizer_alt) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcc'
    exact zero_ne_one hcc'
  have hordc : v.ord (Place.diffCoeff v.uniformizer_alt (D K F t₂)) = 0 := by
    have h1 : 0 ≤ v.ord (Place.diffCoeff v.uniformizer_alt (D K F t₂)) :=
      Place.ord_diffCoeff_D_nonneg_of_perfectField x v ht₁ (by rw [ht₂]; exact zero_le_one)
    have h2 : 0 ≤ v.ord (Place.diffCoeff t₂ (D K F v.uniformizer_alt)) :=
      Place.ord_diffCoeff_D_nonneg_of_perfectField x v ht₂ (by rw [ht₁]; exact zero_le_one)
    have h3 := v.ord_mul hc'0 hc0
    rw [hcc', v.ord_one] at h3
    omega
  have ha : Place.diffCoeff v.uniformizer_alt ω • D K F v.uniformizer_alt = ω :=
    Place.diffCoeff_smul_D_of_ord_eq_one x v ht₁ ω
  have hb : v.differentialCoeff ω • v.dCoord = ω := v.differentialCoeff_smul_dCoord ω
  have hab : Place.diffCoeff v.uniformizer_alt ω =
      v.differentialCoeff ω * Place.diffCoeff v.uniformizer_alt (D K F t₂) := by
    refine coeff_unique hD₁ ?_
    rw [ha, mul_smul, hc_smul, ← hdc, hb]
  rw [Place.ordDiff_def, Place.ordDifferential, hab]
  rcases eq_or_ne (v.differentialCoeff ω) 0 with hb0 | hb0
  · rw [hb0, zero_mul]
  · rw [v.ord_mul hb0 hc0, hordc, add_zero]

end Bridge

section Identity

variable (k : Type u) [Field k] [IsAlgClosed k] {F : Type v} [Field F] [Algebra k F]

theorem exists_sum_ordDiff_D_eq (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F) :
    ∃ S : Finset (Place k F), (∀ P, P ∉ S → P.ordDiff (KaehlerDifferential.D k F x) = 0) ∧
      ∑ P ∈ S, P.ordDiff (KaehlerDifferential.D k F x) = 2 * (genusFF k F : ℤ) - 2 := by
  classical
  have hC : IsCurveOver k F := isCurveOver_pkg k x hx hfin hsep
  have hK : HasCanonicalDivisor (K := k) (F := F) := hasCanonicalDivisor_pkg k x hx hfin hsep
  have hG : ∀ v : Place k F, v.DCoordGenerates := dCoordGenerates_pkg k x hx hfin hsep
  have := hfin
  have hω : KaehlerDifferential.D k F x ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental k x hx
  have hWapp : ∀ P : Place k F, canonicalDivisorOf hω P = P.ordDiff (D k F x) := fun P => by
    rw [canonicalDivisorOf_apply, ordDiff_eq_ordDifferential x P]
  have hWdeg : (canonicalDivisorOf hω).degree = 2 * (genusFF k F : ℤ) - 2 :=
    degree_canonical_pkg k x hx hfin hsep hω
  have hdeg1 : ∀ P : Place k F, P.deg = 1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  refine ⟨(canonicalDivisorOf hω).support, fun P hP => ?_, ?_⟩
  · rw [← hWapp]; exact Finsupp.notMem_support_iff.mp hP
  · rw [← hWdeg, degree_eq_sum_support]
    exact (Finset.sum_congr rfl fun P _ => by rw [hWapp, hdeg1, Nat.cast_one, mul_one]).symm

end Identity

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_sub_algebraMap_of_ord_neg (v : Place K F) {x : F} (c : K) (hx : v.ord x < 0) :
    v.ord (x - algebraMap K F c) = v.ord x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hc0 : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  have hxc : x - algebraMap K F c ≠ 0 := by
    intro h
    have : v.ord x = 0 := by
      rw [sub_eq_zero.mp h]; exact v.ord_algebraMap c
    omega
  have h1 := v.min_ord_le_ord_add hx0 (neg_ne_zero.mpr hc0) (by rwa [← sub_eq_add_neg])
  rw [← sub_eq_add_neg, ← map_neg, v.ord_algebraMap] at h1
  have h2 := v.min_ord_le_ord_add hxc hc0 (by rw [sub_add_cancel]; exact hx0)
  rw [sub_add_cancel, v.ord_algebraMap] at h2
  omega

theorem ord_neg_of_ord_sub_algebraMap_neg (v : Place K F) {x : F} (c : K)
    (hx : v.ord (x - algebraMap K F c) < 0) : v.ord x < 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using hx
  have hc0 : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  have hxc : x - algebraMap K F c ≠ 0 := by rintro h; rw [h] at hx; simp at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_sub, ← map_neg, v.ord_algebraMap] at hx
    exact lt_irrefl _ hx
  have h2 := v.min_ord_le_ord_add hxc hc0 (by rw [sub_add_cancel]; exact hx0)
  rw [sub_add_cancel, v.ord_algebraMap] at h2
  by_contra h
  have h1 := v.min_ord_le_ord_add hx0 (neg_ne_zero.mpr hc0) (by rwa [← sub_eq_add_neg])
  rw [← sub_eq_add_neg, ← map_neg, v.ord_algebraMap] at h1
  omega

theorem ord_nonneg_of_ord_sub_algebraMap_pos (v : Place K F) {x : F} (c : K)
    (h : 0 < v.ord (x - algebraMap K F c)) : 0 ≤ v.ord x := by
  by_contra hneg
  have := ord_sub_algebraMap_of_ord_neg v c (not_le.mp hneg)
  omega

theorem not_ord_sub_pos_of_ord_sub_pos (v : Place K F) {x : F} {c c' : K} (hcc' : c ≠ c')
    (h : 0 < v.ord (x - algebraMap K F c)) : ¬ 0 < v.ord (x - algebraMap K F c') := by
  intro h'
  have hne : x - algebraMap K F c ≠ 0 := by rintro hh; rw [hh] at h; simp at h
  have hne' : x - algebraMap K F c' ≠ 0 := by rintro hh; rw [hh] at h'; simp at h'
  have hd : algebraMap K F (c' - c) ≠ 0 := (map_ne_zero _).mpr (sub_ne_zero.mpr hcc'.symm)
  have hsum : (x - algebraMap K F c) + -(x - algebraMap K F c') = algebraMap K F (c' - c) := by
    rw [map_sub]; ring
  have key := v.min_ord_le_ord_add hne (neg_ne_zero.mpr hne') (by rw [hsum]; exact hd)
  rw [hsum, v.ord_algebraMap] at key
  have : v.ord (-(x - algebraMap K F c')) = v.ord (x - algebraMap K F c') := by
    rw [show -(x - algebraMap K F c') = (x - algebraMap K F c') * (-1) by ring,
      v.ord_mul hne' (by norm_num), show (-1 : F) = algebraMap K F (-1) by simp,
      v.ord_algebraMap, add_zero]
  rw [this] at key
  have hmin : 0 < min (v.ord (x - algebraMap K F c)) (v.ord (x - algebraMap K F c')) := lt_min h h'
  omega

theorem exists_finset_zeros [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    ∃ T : Finset (Place K F), ∀ v, v ∈ T ↔ 0 < v.ord f := by
  classical
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  refine ⟨D.support.filter fun v => 0 < D v, fun v => ?_⟩
  rw [Finset.mem_filter, Finsupp.mem_support_iff, hD v]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

theorem exists_finset_poles [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    ∃ T : Finset (Place K F), ∀ v, v ∈ T ↔ v.ord f < 0 := by
  classical
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  refine ⟨D.support.filter fun v => D v < 0, fun v => ?_⟩
  rw [Finset.mem_filter, Finsupp.mem_support_iff, hD v]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

theorem natCard_subtype_eq_card {γ : Type*} (T : Finset γ) (p : γ → Prop)
    (hT : ∀ v, v ∈ T ↔ p v) : Nat.card {v // p v} = T.card := by
  classical
  have e : {v // p v} ≃ {v // v ∈ T} := Equiv.subtypeEquivRight fun v => (hT v).symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring)
    (hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) :
    0 < v.ord f := by
  have hle : v.adicValuation f ≤ 1 := v.adicValuation_le_one_of_mem hf
  have hne : v.adicValuation f ≠ 1 := by
    intro h1
    have hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring) :=
      (v.adicValuation_coe_eq_one_iff ⟨f, hf⟩).mp h1
    exact (IsLocalRing.mem_maximalIdeal _).mp hmax hu
  have hlt : v.adicValuation f < 1 := lt_of_le_of_ne hle hne
  rw [v.adicValuation_eq_exp_neg_ord hf0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  omega

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact v.toValuationSubring.zero_mem
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  rw [hu]
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

variable [IsAlgClosed K] [IsCurveOver K F]

theorem exists_ord_sub_algebraMap_pos (v : Place K F) {x : F} (hx : Transcendental K x)
    (h : 0 ≤ v.ord x) : ∃ c : K, 0 < v.ord (x - algebraMap K F c) := by
  have hxmem : x ∈ v.toValuationSubring := mem_of_ord_nonneg v h
  have : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨c, hc⟩ := hbij.2 (IsLocalRing.residue v.toValuationSubring ⟨x, hxmem⟩)
  refine ⟨c, ?_⟩
  have hsub_mem : x - algebraMap K F c ∈ v.toValuationSubring :=
    v.toValuationSubring.sub_mem hxmem (v.algebraMap_mem' c)
  have hne : x - algebraMap K F c ≠ 0 := by
    intro h0
    apply hx
    rw [sub_eq_zero] at h0
    rw [h0]; exact isAlgebraic_algebraMap c
  refine ord_pos_of_mem_maximalIdeal v hne hsub_mem ?_
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hres : IsLocalRing.residue v.toValuationSubring ⟨x - algebraMap K F c, hsub_mem⟩ =
      IsLocalRing.residue v.toValuationSubring ⟨x, hxmem⟩ -
        IsLocalRing.residue v.toValuationSubring (algebraMap K v.toValuationSubring c) := by
    rw [← map_sub]
    congr 1
  rw [hres, ← hc]
  change algebraMap K v.ResidueField c -
    (IsLocalRing.residue v.toValuationSubring) (algebraMap K v.toValuationSubring c) = 0
  rw [sub_eq_zero]
  rfl

theorem degree_eq_sum_support' (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v := by
  rw [degree_eq_sum_support]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed v]; simp

theorem sum_ord_sub_algebraMap_eq_finrank {x : F} (hx : Transcendental K x)
    [FiniteDimensional K⟮x⟯ F] (c : K)
    (T : Finset (Place K F)) (hT : ∀ v, v ∈ T ↔ 0 < v.ord (x - algebraMap K F c)) :
    ∑ v ∈ T, v.ord (x - algebraMap K F c) = (Module.finrank K⟮x⟯ F : ℤ) := by
  classical
  set f := x - algebraMap K F c with hf
  have hf0 : f ≠ 0 := by
    intro h
    apply hx
    rw [hf, sub_eq_zero] at h
    rw [h]; exact isAlgebraic_algebraMap c
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  set Dinf : Divisor K F := -(D.filter fun v => D v < 0) with hDinf
  have hDinf_apply : ∀ v, Dinf v = max 0 (-v.ord x) := by
    intro v
    rw [hDinf, Finsupp.neg_apply, Finsupp.filter_apply]
    split_ifs with h
    · rw [hD v] at h
      have hx' := ord_neg_of_ord_sub_algebraMap_neg v c h
      rw [hD v, ord_sub_algebraMap_of_ord_neg v c hx', max_eq_right (by omega)]
    · rw [hD v] at h
      have : 0 ≤ v.ord x := by
        by_contra hneg
        exact h (by rw [ord_sub_algebraMap_of_ord_neg v c (by omega)]; omega)
      rw [neg_zero, max_eq_left (by omega)]
  have hdegInf := degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental x hx Dinf
    hDinf_apply
  have hsplit : (D.filter fun v => 0 < D v) + (D.filter fun v => D v < 0) = D := by
    ext v
    rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
    split_ifs with h1 h2 <;> omega
  have hdegpos : Divisor.degree (D.filter fun v => 0 < D v) = (Module.finrank K⟮x⟯ F : ℤ) := by
    have h := congrArg Divisor.degree hsplit
    rw [map_add, hdeg] at h
    have h2 : Divisor.degree (D.filter fun v => D v < 0) = -Divisor.degree Dinf := by
      rw [hDinf, map_neg, neg_neg]
    rw [h2, hdegInf] at h
    linarith
  rw [degree_eq_sum_support', Finsupp.support_filter] at hdegpos
  have hTeq : T = D.support.filter fun v => 0 < D v := by
    ext v
    rw [hT, Finset.mem_filter, Finsupp.mem_support_iff, hD v]
    constructor
    · intro h; exact ⟨by omega, h⟩
    · intro h; exact h.2
  rw [hTeq, ← hdegpos]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finsupp.filter_apply, ite_eq_left (Finset.mem_filter.mp hv).2, hD v]

theorem sum_neg_ord_eq_finrank {x : F} (hx : Transcendental K x)
    [FiniteDimensional K⟮x⟯ F]
    (T : Finset (Place K F)) (hT : ∀ v, v ∈ T ↔ v.ord x < 0) :
    ∑ v ∈ T, (-v.ord x) = (Module.finrank K⟮x⟯ F : ℤ) := by
  classical
  have hx0 : x ≠ 0 := by
    rintro rfl; exact hx isAlgebraic_zero
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) x hx0
  set Dinf : Divisor K F := -(D.filter fun v => D v < 0) with hDinf
  have hDinf_apply : ∀ v, Dinf v = max 0 (-v.ord x) := by
    intro v
    rw [hDinf, Finsupp.neg_apply, Finsupp.filter_apply, hD v]
    split_ifs with h
    · rw [max_eq_right (by omega)]
    · rw [neg_zero, max_eq_left (by omega)]
  have hdegInf := degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental x hx Dinf
    hDinf_apply
  rw [degree_eq_sum_support'] at hdegInf
  have hTeq : T = Dinf.support := by
    ext v
    rw [hT, Finsupp.mem_support_iff, hDinf_apply]
    constructor
    · intro h; exact (lt_max_of_lt_right (by omega)).ne'
    · intro h
      by_contra h'
      exact h (max_eq_left (by omega))
  rw [hTeq, ← hdegInf]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [hDinf_apply]
  rw [Finsupp.mem_support_iff, hDinf_apply] at hv
  rcases le_or_gt 0 (v.ord x) with h | h
  · exact absurd (max_eq_left (by omega : -v.ord x ≤ 0)) hv
  · rw [max_eq_right (by omega)]

end Generic

section Descent

local instance isAlgebraicQbar_rh : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

def iota : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift

local notation "ℚbar" => AlgebraicClosure ℚ

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

theorem coeffMap_iota_coeffEmb (y : LaurentSeries ℚ) :
    coeffMap (iota : ℚbar →+* ℂ) (coeffEmb ℚbar y) = coeffEmb ℂ y := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  refine coeffMap_congr ?_ y
  ext c
  simp

theorem coeffMap_iota_algebraMap (c : ℚbar) :
    coeffMap (iota : ℚbar →+* ℂ) (algebraMap ℚbar (LaurentSeries ℚbar) c) =
      algebraMap ℂ (LaurentSeries ℂ) (iota c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]
  rfl

theorem coeffMap_iota_mem {x : LaurentSeries ℚbar} (hx : x ∈ laurentBaseChange ℚbar F₀) :
    coeffMap (iota : ℚbar →+* ℂ) x ∈ laurentBaseChange ℂ F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  refine Subfield.closure_induction (p := fun x _ => coeffMap (iota : ℚbar →+* ℂ) x ∈
      laurentBaseChange ℂ F₀) ?_ (by simp) ?_ ?_ ?_ ?_ hx
  · rintro x (⟨c, rfl⟩ | ⟨y, hy, rfl⟩)
    · rw [coeffMap_iota_algebraMap]
      exact (laurentBaseChange ℂ F₀).algebraMap_mem _
    · rw [coeffMap_iota_coeffEmb]
      exact coeffEmb_mem_laurentBaseChange ℂ hy
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro x _ hx; rw [map_neg]; exact neg_mem hx
  · intro x _ hx; rw [map_inv₀]; exact inv_mem hx
  · intro x y _ _ hx hy; rw [map_mul]; exact mul_mem hx hy

def psi : laurentBaseChange ℚbar F₀ →+* laurentBaseChange ℂ F₀ where
  toFun x := ⟨coeffMap (iota : ℚbar →+* ℂ) x, coeffMap_iota_mem F₀ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[scoped simp] theorem coe_psi (x : laurentBaseChange ℚbar F₀) :
    (psi F₀ x : LaurentSeries ℂ) = coeffMap (iota : ℚbar →+* ℂ) x := rfl

theorem psi_algebraMap (c : ℚbar) :
    psi F₀ (algebraMap ℚbar (laurentBaseChange ℚbar F₀) c) =
      algebraMap ℂ (laurentBaseChange ℂ F₀) (iota c) :=
  Subtype.ext (coeffMap_iota_algebraMap c)

theorem psi_coeffEmb (y : LaurentSeries ℚ) (hy : y ∈ F₀) :
    psi F₀ ⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩ =
      ⟨coeffEmb ℂ y, coeffEmb_mem_laurentBaseChange ℂ hy⟩ :=
  Subtype.ext (coeffMap_iota_coeffEmb y)

theorem exists_place_complex_ord_eq (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ)
    (v : Place ℚbar (laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ))) :
    ∃ v' : Place ℂ (laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ)),
      ∀ f, v'.ord (psi (qExpFunctionFieldC ℚ Γ) f) = v.ord f := by
  let F₀ := qExpFunctionFieldC ℚ Γ
  let : Algebra (laurentBaseChange ℚbar F₀) (laurentBaseChange ℂ F₀) := (psi F₀).toAlgebra
  let : Algebra ℚbar ℂ := (iota : ℚbar →+* ℂ).toAlgebra
  let : Algebra ℚbar (laurentBaseChange ℂ F₀) :=
    ((algebraMap ℂ (laurentBaseChange ℂ F₀)).comp (iota : ℚbar →+* ℂ)).toAlgebra
  have : IsScalarTower ℚbar ℂ (laurentBaseChange ℂ F₀) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚbar (laurentBaseChange ℚbar F₀) (laurentBaseChange ℂ F₀) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change algebraMap ℂ (laurentBaseChange ℂ F₀) (iota c) = psi F₀ (algebraMap ℚbar _ c)
    rw [psi_algebraMap]
  have hfg : ∃ x : laurentBaseChange ℚbar F₀, Transcendental ℚbar x ∧
      FiniteDimensional (IntermediateField.adjoin ℚbar ({x} : Set _)) (laurentBaseChange ℚbar F₀) :=
    JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ℚbar Γ hT
  have hfg' : ∃ x : laurentBaseChange ℂ F₀, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set _)) (laurentBaseChange ℂ F₀) :=
    JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ℂ Γ hT
  have : IsCurveOver ℚbar (laurentBaseChange ℚbar F₀) := by
    obtain ⟨x, hx, hfin⟩ := hfg
    exact isCurveOver_of_transcendental_of_perfectField hx hfin
  have hgen : IntermediateField.adjoin ℂ
      (Set.range (algebraMap (laurentBaseChange ℚbar F₀) (laurentBaseChange ℂ F₀))) = ⊤ := by
    apply le_antisymm le_top
    have h1 : laurentBaseChange ℂ F₀ ≤ (IntermediateField.adjoin ℂ
        (Set.range (algebraMap (laurentBaseChange ℚbar F₀) (laurentBaseChange ℂ F₀)))).map
          (laurentBaseChange ℂ F₀).val := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨⟨coeffEmb ℂ y, coeffEmb_mem_laurentBaseChange ℂ hy⟩, ?_, rfl⟩
      apply IntermediateField.subset_adjoin
      exact ⟨⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩, psi_coeffEmb F₀ y hy⟩
    intro x _
    obtain ⟨y, hy, hyx⟩ := h1 x.2
    have : y = x := Subtype.ext hyx
    rwa [← this]
  obtain ⟨v', -, hord, -⟩ :=
    Place.exists_comap_algebraMap_eq_of_constantFieldExtension ℚbar (laurentBaseChange ℚbar F₀) ℂ
      (laurentBaseChange ℂ F₀) hfg hfg' hgen v
  exact ⟨v', hord⟩

end Descent

section Unramified

local notation "ℚbar" => AlgebraicClosure ℚ

variable (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)

omit [NeZero M] in
theorem T_mem_Gamma1 : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.T]

include hΓ in
theorem ord_sub_algebraMap_le_one
    (y : laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries ℚbar) = jqModC ℚbar) (a : ℚbar) (ha₀ : a ≠ 0) (ha₁ : a ≠ 1728)
    (P : Place ℚbar (laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ))) :
    P.ord (y - algebraMap ℚbar _ a) ≤ 1 := by
  have : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  have hT : ModularGroup.T ∈ Γ := hΓ (T_mem_Gamma1 M)
  obtain ⟨P', hP'⟩ := exists_place_complex_ord_eq Γ hT P
  rw [← hP', map_sub, psi_algebraMap]
  have hy' : ((psi (qExpFunctionFieldC ℚ Γ) y : laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ)) :
      LaurentSeries ℂ) = jqModC ℂ := by
    rw [coe_psi, hy]
    exact map_jqModC _
  have hinj : Function.Injective (iota : ℚbar →+* ℂ) := (iota : ℚbar →+* ℂ).injective
  have h₀ : (iota : ℚbar →+* ℂ) a ≠ 0 := by
    intro h; exact ha₀ (hinj (by rw [h, map_zero]))
  have h₁ : (iota : ℚbar →+* ℂ) a ≠ 1728 := by
    intro h; exact ha₁ (hinj (by rw [h, map_ofNat]))
  exact ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728 M Γ hΓ
    (psi (qExpFunctionFieldC ℚ Γ) y) hy' _ h₀ h₁ P'

end Unramified

section Main

local notation "ℚbar" => AlgebraicClosure ℚ

variable (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)

local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)

theorem sum_eq_sum_of_vanish {ι : Type*} (f : ι → ℤ) (S U : Finset ι)
    (hS : ∀ P, P ∉ S → f P = 0) (hU : ∀ P, P ∉ U → f P = 0) :
    ∑ P ∈ S, f P = ∑ P ∈ U, f P := by
  classical
  have h1 : ∑ P ∈ S, f P = ∑ P ∈ S ∪ U, f P :=
    Finset.sum_subset Finset.subset_union_left fun P _ hPS => hS P hPS
  have h2 : ∑ P ∈ U, f P = ∑ P ∈ S ∪ U, f P :=
    Finset.sum_subset Finset.subset_union_right fun P _ hPU => hU P hPU
  rw [h1, h2]

-- Keep separability search independent of the concrete modular-function-field tower.
private theorem differential_sub_algebraMap
    {K F : Type*} [CommRing K] [CommRing F] [Algebra K F] (x : F) (c : K) :
    KaehlerDifferential.D K F (x - algebraMap K F c) = KaehlerDifferential.D K F x := by
  rw [map_sub, Derivation.map_algebraMap, sub_zero]

private theorem isSeparable_of_finiteDimensional {K F : Type*}
    [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [CharZero K] :
    Algebra.IsSeparable K F := by
  infer_instance

include hΓ in
theorem main (y : FF) (hy : (y : LaurentSeries ℚbar) = jqModC ℚbar) :
    2 * genusFF ℚbar FF + Nat.card {P : Place ℚbar FF // P.ord y < 0} +
        Nat.card {P : Place ℚbar FF // 0 < P.ord y} +
        Nat.card {P : Place ℚbar FF // 0 < P.ord (y - 1728)} ≤
      Module.finrank ℚbar⟮y⟯ FF + 2 := by
  classical
  have : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  have hT : ModularGroup.T ∈ Γ := hΓ (T_mem_Gamma1 M)
  have hytr : Transcendental ℚbar y := by
    have h := transcendental_jqModC ℚbar
    rw [← hy] at h
    exact (transcendental_algebraMap_iff (R := ℚbar) (A := LaurentSeries ℚbar) (S := ↥FF)
      Subtype.val_injective).mp h
  obtain ⟨x₀, hx₀, hx₀fin⟩ :=
    JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ℚbar Γ hT
  have := hx₀fin
  have hfin : FiniteDimensional ℚbar⟮y⟯ FF := finiteDimensional_adjoin_of_transcendental x₀ hytr
  have hsep : Algebra.IsSeparable ℚbar⟮y⟯ FF := isSeparable_of_finiteDimensional
  have hC : IsCurveOver ℚbar FF := isCurveOver_of_transcendental_of_perfectField hytr hfin
  obtain ⟨S, hS0, hSsum⟩ := exists_sum_ordDiff_D_eq ℚbar y hytr hfin hsep
  have hy0 : (y : FF) ≠ 0 := fun h => hytr (h ▸ isAlgebraic_zero)
  have h1728F : (1728 : FF) = algebraMap ℚbar FF 1728 := (map_ofNat _ 1728).symm
  have hy1728 : y - algebraMap ℚbar FF 1728 ≠ 0 := by
    intro h
    apply hytr
    rw [sub_eq_zero] at h
    rw [h]; exact isAlgebraic_algebraMap _
  obtain ⟨Z₀, hZ₀⟩ := exists_finset_zeros (K := ℚbar) hy0
  obtain ⟨Z₁, hZ₁⟩ := exists_finset_zeros (K := ℚbar) hy1728
  obtain ⟨Pinf, hPinf⟩ := exists_finset_poles (K := ℚbar) hy0
  have hsum₀ : ∑ v ∈ Z₀, v.ord y = (Module.finrank ℚbar⟮y⟯ FF : ℤ) := by
    have h := sum_ord_sub_algebraMap_eq_finrank (K := ℚbar) hytr 0 Z₀
      (fun v => by rw [map_zero, sub_zero]; exact hZ₀ v)
    simpa using h
  have hsum₁ : ∑ v ∈ Z₁, v.ord (y - algebraMap ℚbar FF 1728) = (Module.finrank ℚbar⟮y⟯ FF : ℤ) :=
    sum_ord_sub_algebraMap_eq_finrank (K := ℚbar) hytr 1728 Z₁ hZ₁
  have hsuminf : ∑ v ∈ Pinf, (-v.ord y) = (Module.finrank ℚbar⟮y⟯ FF : ℤ) :=
    sum_neg_ord_eq_finrank (K := ℚbar) hytr Pinf hPinf
  set f : Place ℚbar FF → ℤ := fun v => v.ordDiff (KaehlerDifferential.D ℚbar FF y) with hf
  have hD1728 : KaehlerDifferential.D ℚbar FF (y - algebraMap ℚbar FF 1728) =
      KaehlerDifferential.D ℚbar FF y :=
    differential_sub_algebraMap y _
  have hf_pole : ∀ v ∈ Pinf, f v = v.ord y - 1 := fun v hv => by
    have h : v.ord y ≠ 0 := by have := (hPinf v).mp hv; omega
    exact Place.ordDiff_D_eq_ord_sub_one y v h
  have hf_zero : ∀ v ∈ Z₀, f v = v.ord y - 1 := fun v hv => by
    have h : v.ord y ≠ 0 := by have := (hZ₀ v).mp hv; omega
    exact Place.ordDiff_D_eq_ord_sub_one y v h
  have hf_one : ∀ v ∈ Z₁, f v = v.ord (y - algebraMap ℚbar FF 1728) - 1 := fun v hv => by
    have h : v.ord (y - algebraMap ℚbar FF 1728) ≠ 0 := by have := (hZ₁ v).mp hv; omega
    change v.ordDiff (KaehlerDifferential.D ℚbar FF y) = _
    rw [← hD1728]
    exact Place.ordDiff_D_eq_ord_sub_one y v h
  set U : Finset (Place ℚbar FF) := Z₀ ∪ Z₁ ∪ Pinf with hU
  have hf_off : ∀ v, v ∉ U → f v = 0 := by
    intro v hv
    have hv₀ : v ∉ Z₀ :=
      fun h => hv (by rw [hU]; exact Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hv₁ : v ∉ Z₁ :=
      fun h => hv (by rw [hU]; exact Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hvinf : v ∉ Pinf := fun h => hv (by rw [hU]; exact Finset.mem_union_right _ h)
    have hreg : 0 ≤ v.ord y := by
      by_contra h; exact hvinf ((hPinf v).mpr (not_le.mp h))
    obtain ⟨c, hc⟩ := exists_ord_sub_algebraMap_pos (K := ℚbar) v hytr hreg
    have hc₀ : c ≠ 0 := by
      rintro rfl
      rw [map_zero, sub_zero] at hc
      exact hv₀ ((hZ₀ v).mpr hc)
    have hc₁ : c ≠ 1728 := by
      rintro rfl
      exact hv₁ ((hZ₁ v).mpr hc)
    have hle := ord_sub_algebraMap_le_one M Γ hΓ y hy c hc₀ hc₁ v
    have heq : v.ord (y - algebraMap ℚbar FF c) = 1 := le_antisymm hle hc
    have hDc : KaehlerDifferential.D ℚbar FF (y - algebraMap ℚbar FF c) =
        KaehlerDifferential.D ℚbar FF y :=
      differential_sub_algebraMap y _
    change v.ordDiff (KaehlerDifferential.D ℚbar FF y) = 0
    rw [← hDc, Place.ordDiff_D_eq_ord_sub_one y v (by rw [heq]; exact one_ne_zero), heq]
    ring
  have hUsum : ∑ v ∈ U, f v = 2 * (genusFF ℚbar FF : ℤ) - 2 := by
    rw [← hSsum]
    exact (sum_eq_sum_of_vanish f S U hS0 hf_off).symm
  have h1728ne : (1728 : ℚbar) ≠ 0 := by norm_num
  have hd01 : Disjoint Z₀ Z₁ := by
    rw [Finset.disjoint_left]
    intro v hv₀ hv₁
    have h₀ : 0 < v.ord (y - algebraMap ℚbar FF 0) :=
      by rw [map_zero, sub_zero]; exact (hZ₀ v).mp hv₀
    exact not_ord_sub_pos_of_ord_sub_pos v h1728ne.symm h₀ ((hZ₁ v).mp hv₁)
  have hd0inf : Disjoint Z₀ Pinf := by
    rw [Finset.disjoint_left]
    intro v hv₀ hvinf
    have := (hZ₀ v).mp hv₀; have := (hPinf v).mp hvinf; omega
  have hd1inf : Disjoint Z₁ Pinf := by
    rw [Finset.disjoint_left]
    intro v hv₁ hvinf
    have h := ord_nonneg_of_ord_sub_algebraMap_pos v (1728 : ℚbar) ((hZ₁ v).mp hv₁)
    have := (hPinf v).mp hvinf; omega
  have hd01inf : Disjoint (Z₀ ∪ Z₁) Pinf := Finset.disjoint_union_left.mpr ⟨hd0inf, hd1inf⟩
  have hsplit : ∑ v ∈ U, f v = ∑ v ∈ Z₀, f v + ∑ v ∈ Z₁, f v + ∑ v ∈ Pinf, f v := by
    rw [hU, Finset.sum_union hd01inf, Finset.sum_union hd01]
  have hs₀ : ∑ v ∈ Z₀, f v = (Module.finrank ℚbar⟮y⟯ FF : ℤ) - Z₀.card := by
    rw [Finset.sum_congr rfl hf_zero, Finset.sum_sub_distrib, hsum₀]
    simp
  have hs₁ : ∑ v ∈ Z₁, f v = (Module.finrank ℚbar⟮y⟯ FF : ℤ) - Z₁.card := by
    rw [Finset.sum_congr rfl hf_one, Finset.sum_sub_distrib, hsum₁]
    simp
  have hsinf : ∑ v ∈ Pinf, f v = -(Module.finrank ℚbar⟮y⟯ FF : ℤ) - Pinf.card := by
    rw [Finset.sum_congr rfl hf_pole, Finset.sum_sub_distrib, ← hsuminf, Finset.sum_neg_distrib]
    simp
  have hc₀ : Nat.card {P : Place ℚbar FF // 0 < P.ord y} = Z₀.card :=
    natCard_subtype_eq_card Z₀ _ hZ₀
  have hc₁ : Nat.card {P : Place ℚbar FF // 0 < P.ord (y - 1728)} = Z₁.card := by
    rw [h1728F]; exact natCard_subtype_eq_card Z₁ _ hZ₁
  have hcinf : Nat.card {P : Place ℚbar FF // P.ord y < 0} = Pinf.card :=
    natCard_subtype_eq_card Pinf _ hPinf
  rw [hc₀, hc₁, hcinf]
  have key : 2 * (genusFF ℚbar FF : ℤ) - 2 =
      (Module.finrank ℚbar⟮y⟯ FF : ℤ) - Z₀.card - Z₁.card - Pinf.card := by
    rw [← hUsum, hsplit, hs₀, hs₁, hsinf]; ring
  omega

end Main

end ModularCurve.RiemannHurwitzCount
end

open AlgebraicCurve _root_.ModularCurve
  _root_.P2MW.S_OVERLONG_7a292264.ModularCurve
  in
theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)) :
    2 * AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ
            Γ)) +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ
            Γ)) //
            P.ord y < 0} +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ
            Γ)) //
            0 < P.ord y} +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ
            Γ)) //
            0 < P.ord (y - 1728)} ≤
      Module.finrank
          (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ
            Γ)) +
        2 :=
  ModularCurve.RiemannHurwitzCount.main M Γ hΓ y hy

end S_OVERLONG_7a292264
end P2MW
export P2MW.S_OVERLONG_7a292264
  (solution)

end privateSection

public section publicSection

theorem ModularCurve.two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)) :
    2 * AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ
            Γ)) +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ
            Γ)) //
            P.ord y < 0} +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ
            Γ)) //
            0 < P.ord y} +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ
            Γ)) //
            0 < P.ord (y - 1728)} ≤
      Module.finrank
          (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ
            Γ)) +
        2 :=
  solution M Γ hΓ y hy

end publicSection
