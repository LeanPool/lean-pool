/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Based on Prove2Me node ModularCurve.transcendental_coeffEmb_jq
(e4976549-c26d-5fc7-8aba-41c0ae2c4c8b) by Claude (2026-09-05).

Proof based on Prove2Me submission 0b41c60f-705b-5a9d-b0e3-9d4859e93387
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_QAdicPlace
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_LaurentCoeff

import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_ModularUnit
import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_CuspidalClass
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_ord_cuspInftyBar
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_order_coeffEmb
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries_inv
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isIntegral_adjoin
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ord_smul_of_ne_zero
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_map_algHom
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_isScalarTower
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk
import LeanPool.FLTEichlerShimura.Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Pic0_addOrderOf_mk_dvd_of_isPrincipal
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_coeffEmb_injective
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_cuspZeroBar_ne_cuspInftyBar
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_transcendental_jqModC
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_coeffEmb_jq
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionField
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_full_eq_of_prime
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_nonempty_modularPolynomialData_of_squarefree
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jqNModC
import Mathlib.Algebra.Algebra.Rat
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_isCusp_cuspZeroBar
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_isCusp_cuspInftyBar
import LeanPool.FLTEichlerShimura.Definitions.Def_P2M_Util

/-!
# Transcendence of j in the base-changed modular function field

Theorem statement: `ModularCurve.transcendental_coeffEmb_jq`
(`e4976549-c26d-5fc7-8aba-41c0ae2c4c8b`), by Claude, 2026-09-05.

Proof: submission `0b41c60f-705b-5a9d-b0e3-9d4859e93387`, by Claude, 2026-09-05 (ACCEPTED); locally
adapted.

Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure and let $N$ be a nonzero natural
number. Write $jq \in \mathbb{Q}((q))$ for the Laurent series $q^{-1}\cdot jNumQ$, where $jNumQ$ is
the power series `jNum` with its integer coefficients pushed to $\mathbb{Q}$; thus $jq$ is the
$q$-expansion of the modular invariant $j$. Let `modularFunctionFieldFull N` be the intermediate
field of $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ the set of series
$qExpand_{\mathbb{Q}}\, d\, jq$ for the nonzero divisors $d$ of $N$, and let `coeffEmb L` be the
ring homomorphism $\mathbb{Q}((q)) \to L((q))$ applying the structure map $\mathbb{Q} \to L$ to each
coefficient. Finally let `laurentBaseChange L (modularFunctionFieldFull N)` be the intermediate
field of $L((q))$ generated over $L$ by the image under `coeffEmb L` of `modularFunctionFieldFull
N`. The assertion is that the element of this intermediate field determined by
$\mathrm{coeffEmb}_L(jq)$, which lies there because $jq$ belongs to `modularFunctionFieldFull N`, is
transcendental over $L$: it satisfies no nonzero polynomial with coefficients in $L$.

This records the classical transcendence of the $q$-expansion of $j$ over the field of constants,
now for an arbitrary field $L$ of characteristic zero and after base change of the modular function
field of level $N$ to $L((q))$. It supplies the transcendence hypothesis needed to treat the
base-changed field as a function field of one variable over $L$, and is invoked throughout the
analysis of places of the modular curve and of the fibres of its models, in particular for the
places attached to $j$ and to $j_N$.

## Explanation of the source proof

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ModularCurve_transcendental_coeffEmb_jq.lean

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection


namespace P2MW.S_ModularCurve_transcendental_coeffEmb_jq

open ModularCurve AlgebraicCurve IntermediateField
open scoped Pointwise

noncomputable section

namespace DivUSol

local notation "𝕂" => AlgebraicClosure ℚ

variable (ℓ : ℕ)

section inf
variable [NeZero ℓ]

def ubar (hmem : modularUnitSeries ℓ ∈ modularFunctionFieldFull ℓ) : modularFunctionFieldBar ℓ :=
  ⟨coeffEmb 𝕂 (modularUnitSeries ℓ), coeffEmb_mem_laurentBaseChange 𝕂 hmem⟩

theorem coe_ubar (hmem : modularUnitSeries ℓ ∈ modularFunctionFieldFull ℓ) :
    (ubar ℓ hmem : LaurentSeries 𝕂) = coeffEmb 𝕂 (modularUnitSeries ℓ) := rfl

theorem coeffEmb_modularUnitSeries_ne_zero : coeffEmb 𝕂 (modularUnitSeries ℓ) ≠ 0 := by
  intro h
  exact modularUnitSeries_ne_zero ℓ (coeffEmb_injective 𝕂 (by rw [h, map_zero]))

theorem ubar_ne_zero (hmem : modularUnitSeries ℓ ∈ modularFunctionFieldFull ℓ) :
    ubar ℓ hmem ≠ 0 := by
  intro h
  exact coeffEmb_modularUnitSeries_ne_zero ℓ (by rw [← coe_ubar ℓ hmem, h]; rfl)

theorem ord_inf (hmem : modularUnitSeries ℓ ∈ modularFunctionFieldFull ℓ) :
    (cuspInftyBar ℓ).ord (ubar ℓ hmem) = 1 - (ℓ : ℤ) := by
  rw [ord_cuspInftyBar, coe_ubar, order_coeffEmb, order_modularUnitSeries]

end inf

variable [Fact ℓ.Prime]

theorem coeffEmb_smul (c : ℚ) (x : LaurentSeries ℚ) :
    coeffEmb 𝕂 (c • x) = (c : 𝕂) • coeffEmb 𝕂 x := by
  rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, map_mul]
  congr 1
  ext k
  simp

theorem fricke_ubar (hmem : modularUnitSeries ℓ ∈ modularFunctionFieldFull ℓ) :
    ((frickeInvolutionBar ℓ (ubar ℓ hmem) : modularFunctionFieldBar ℓ) : LaurentSeries 𝕂) =
      ((ℓ : 𝕂) ^ 12) • (coeffEmb 𝕂 (modularUnitSeries ℓ))⁻¹ := by
  have h := coe_geomAut_coeffEmb 𝕂 (modularFunctionFieldFull ℓ) (frickeInvolutionFull ℓ)
    ⟨modularUnitSeries ℓ, hmem⟩
  rw [coe_frickeInvolutionFull_modularUnitSeries ℓ hmem, coeffEmb_smul, map_inv₀] at h
  rw [frickeInvolutionBar_def]
  push_cast at h
  exact h

theorem fricke_ubar_elt (hmem : modularUnitSeries ℓ ∈ modularFunctionFieldFull ℓ) :
    frickeInvolutionBar ℓ (ubar ℓ hmem) =
      algebraMap 𝕂 (modularFunctionFieldBar ℓ) ((ℓ : 𝕂) ^ 12) * (ubar ℓ hmem)⁻¹ := by
  apply Subtype.ext
  rw [fricke_ubar, ← HahnSeries.C_mul_eq_smul, HahnSeries.C_eq_algebraMap]
  simp [coe_ubar]

theorem ell_pow_ne_zero : ((ℓ : 𝕂) ^ 12) ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne ℓ))

theorem fricke_symm_ubar (hmem : modularUnitSeries ℓ ∈ modularFunctionFieldFull ℓ) :
    (frickeInvolutionBar ℓ).symm (ubar ℓ hmem) = ((((ℓ : 𝕂) ^ 12))⁻¹ • ubar ℓ hmem)⁻¹ := by
  apply (frickeInvolutionBar ℓ).injective
  rw [AlgEquiv.apply_symm_apply, map_inv₀, Algebra.smul_def, map_mul, AlgEquiv.commutes,
    fricke_ubar_elt,
    ← mul_assoc, ← map_mul, inv_mul_cancel₀ (ell_pow_ne_zero ℓ), map_one, one_mul, inv_inv]

theorem ord_zero (hmem : modularUnitSeries ℓ ∈ modularFunctionFieldFull ℓ) :
    (cuspZeroBar ℓ).ord (ubar ℓ hmem) = (ℓ : ℤ) - 1 := by
  have key : (frickeInvolutionBar ℓ • cuspInftyBar ℓ).ord (ubar ℓ hmem) =
      (cuspInftyBar ℓ).ord ((frickeInvolutionBar ℓ).symm (ubar ℓ hmem)) := by
    conv_lhs => rw [← (frickeInvolutionBar ℓ).apply_symm_apply (ubar ℓ hmem)]
    exact Place.ord_smul _ _ _
  rw [cuspZeroBar_def, key, fricke_symm_ubar, Place.ord_inv,
    Place.ord_smul_of_ne_zero _ (inv_ne_zero (ell_pow_ne_zero ℓ)), ord_inf]
  ring

def jb :
    modularFunctionFieldBar ℓ := ⟨coeffEmb 𝕂 jq, coeffEmb_mem_laurentBaseChange 𝕂 (jq_mem_full ℓ)⟩

theorem coe_jb : (jb ℓ : LaurentSeries 𝕂) = coeffEmb 𝕂 jq := rfl

theorem isCusp_inf : IsCusp (jb ℓ) (cuspInftyBar ℓ) := isCusp_cuspInftyBar ℓ

theorem isCusp_zero : IsCusp (jb ℓ) (cuspZeroBar ℓ) :=
  isCusp_cuspZeroBar ℓ (isFrickeAutFull_frickeInvolutionFull_prime ℓ)

def coeffEmbₐ : LaurentSeries ℚ →ₐ[ℚ] LaurentSeries 𝕂 := (coeffEmb 𝕂).toRatAlgHom

theorem coeffEmbₐ_apply (x : LaurentSeries ℚ) : coeffEmbₐ x = coeffEmb 𝕂 x := rfl

theorem isScalarTower_rat :
    @IsScalarTower ℚ 𝕂 (LaurentSeries 𝕂) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun r =>
    RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ (LaurentSeries 𝕂))
      ((algebraMap 𝕂 (LaurentSeries 𝕂)).comp (algebraMap ℚ 𝕂))) r

attribute [local instance] isScalarTower_rat

theorem isIntegral_ubar (hmem : modularUnitSeries ℓ ∈ modularFunctionFieldFull ℓ) :
    IsIntegral (Algebra.adjoin 𝕂 {jb ℓ}) (ubar ℓ hmem) := by
  have h1 := isIntegral_adjoin_map_algHom coeffEmbₐ (isIntegral_adjoin_jq_modularUnitSeries ℓ)
  rw [coeffEmbₐ_apply, coeffEmbₐ_apply] at h1
  have h2 := isIntegral_adjoin_of_isScalarTower (L := 𝕂) h1
  exact isIntegral_adjoin_intermediateField_mk (modularFunctionFieldBar ℓ) _ _ h2

theorem isIntegral_ubar_inv (hmem : modularUnitSeries ℓ ∈ modularFunctionFieldFull ℓ) :
    IsIntegral (Algebra.adjoin 𝕂 {jb ℓ}) (ubar ℓ hmem)⁻¹ := by
  have h1 := isIntegral_adjoin_map_algHom coeffEmbₐ (isIntegral_adjoin_jq_modularUnitSeries_inv ℓ)
  rw [coeffEmbₐ_apply, coeffEmbₐ_apply, map_inv₀] at h1
  have h2 := isIntegral_adjoin_of_isScalarTower (L := 𝕂) h1
  have hxi : (coeffEmb 𝕂 (modularUnitSeries ℓ))⁻¹ ∈ modularFunctionFieldBar ℓ :=
    inv_mem (coeffEmb_mem_laurentBaseChange 𝕂 hmem)
  have h3 := isIntegral_adjoin_intermediateField_mk (modularFunctionFieldBar ℓ) (jb ℓ).2 hxi h2
  have e : (⟨(coeffEmb 𝕂 (modularUnitSeries ℓ))⁻¹, hxi⟩ : modularFunctionFieldBar ℓ) = (ubar ℓ
    hmem)⁻¹ :=
    Subtype.ext rfl
  rw [e] at h3
  exact h3

theorem ord_of_not_isCusp (hmem : modularUnitSeries ℓ ∈ modularFunctionFieldFull ℓ)
    (w : Place 𝕂 (modularFunctionFieldBar ℓ)) (hw : ¬ IsCusp (jb ℓ) w)
    : w.ord (ubar ℓ hmem) = 0 := by
  rw [isCusp_iff, not_not] at hw
  exact Place.ord_eq_zero_of_isIntegral_adjoin w hw (isIntegral_ubar ℓ hmem) (isIntegral_ubar_inv ℓ
    hmem)

theorem smul_cuspidalDivisor_apply (hmem : modularUnitSeries ℓ ∈ modularFunctionFieldFull ℓ)
    (v : Place 𝕂 (modularFunctionFieldBar ℓ)) :
    (((ℓ : ℤ) - 1) • cuspidalDivisor ℓ) v = v.ord (ubar ℓ hmem) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hne : cuspZeroBar ℓ ≠ cuspInftyBar ℓ :=
    cuspZeroBar_ne_cuspInftyBar ℓ (isFrickeAutFull_frickeInvolutionFull_prime ℓ) hℓ.one_lt
  simp only [cuspidalDivisor_def, Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.single_apply,
    smul_eq_mul]
  by_cases hc : IsCusp (jb ℓ) v
  · rcases eq_cuspInftyBar_or_eq_cuspZeroBar ℓ v hc with rfl | rfl
    · rw [ite_eq_right hne, ite_eq_left rfl, ord_inf]; ring
    · rw [ite_eq_left rfl, ite_eq_right hne.symm, ord_zero]; ring
  · have h1 : cuspZeroBar ℓ ≠ v := fun h => hc (h ▸ isCusp_zero ℓ)
    have h2 : cuspInftyBar ℓ ≠ v := fun h => hc (h ▸ isCusp_inf ℓ)
    rw [ite_eq_right h1, ite_eq_right h2, ord_of_not_isCusp ℓ hmem v hc]; ring

theorem isPrincipal_smul_cuspidalDivisor :
    Divisor.IsPrincipal (((ℓ : ℤ) - 1) • cuspidalDivisor ℓ) :=
  ⟨ubar ℓ (modularUnitSeries_mem_modularFunctionFieldFull ℓ), ubar_ne_zero ℓ _,
    smul_cuspidalDivisor_apply ℓ _⟩

theorem smul_cuspidalClass_eq_zero : ((ℓ : ℤ) - 1) • cuspidalClass ℓ = 0 := by
  rw [cuspidalClass_def]
  exact Pic0.zsmul_mk_eq_zero_of_isPrincipal _ _
    (by rw [coe_cuspidalDivisor₀]; exact isPrincipal_smul_cuspidalDivisor ℓ)

theorem addOrderOf_cuspidalClass_dvd : addOrderOf (cuspidalClass ℓ) ∣ ℓ - 1 := by
  have hℓ : ℓ.Prime := Fact.out
  rw [cuspidalClass_def]
  refine Pic0.addOrderOf_mk_dvd_of_isPrincipal _ _ ?_
  rw [coe_cuspidalDivisor₀, ← natCast_zsmul, Nat.cast_sub hℓ.one_le, Nat.cast_one]
  exact isPrincipal_smul_cuspidalDivisor ℓ

theorem bar_eq_restrictScalars :
    modularFunctionFieldBar ℓ =
      (IntermediateField.adjoin (IntermediateField.adjoin 𝕂 ({jqModC 𝕂} : Set (LaurentSeries 𝕂)))
        ({jqNModC 𝕂 ℓ} : Set (LaurentSeries 𝕂))).restrictScalars 𝕂 := by
  have hℓ : ℓ.Prime := Fact.out
  change laurentBaseChange 𝕂 (modularFunctionFieldFull ℓ) = _
  rw [full_eq_of_prime hℓ, laurentBaseChange_modularFunctionField]
  exact (adjoin_simple_adjoin_simple 𝕂 (jqModC 𝕂) (jqNModC 𝕂 ℓ)).symm

theorem mem_bar_iff (x : LaurentSeries 𝕂) :
    x ∈ modularFunctionFieldBar ℓ ↔ x ∈ 𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯ := by
  rw [bar_eq_restrictScalars ℓ, mem_restrictScalars]

def jTr : (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯) ≃+* modularFunctionFieldBar ℓ where
  toFun x := ⟨x, (mem_bar_iff ℓ _).mpr x.2⟩
  invFun y := ⟨y, (mem_bar_iff ℓ _).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem coe_jTr (x : 𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯) :
    ((jTr ℓ x : modularFunctionFieldBar ℓ) : LaurentSeries 𝕂) = x := by
  ext; rfl

def e₁ : (𝕂⟮jb ℓ⟯ : IntermediateField 𝕂 (modularFunctionFieldBar ℓ)) ≃ₐ[𝕂] 𝕂⟮jqModC 𝕂⟯ :=
  (liftAlgEquiv 𝕂⟮jb ℓ⟯).trans (equivOfEq (by rw [lift_adjoin_simple, coe_jb, coeffEmb_jq]))

theorem coe_e₁ (x : (𝕂⟮jb ℓ⟯ : IntermediateField 𝕂 (modularFunctionFieldBar ℓ))) :
    ((e₁ ℓ x : 𝕂⟮jqModC 𝕂⟯) : LaurentSeries 𝕂) = ((x : modularFunctionFieldBar ℓ) : LaurentSeries 𝕂)
      := by
  ext; rfl

theorem compat :
    (algebraMap (𝕂⟮jb ℓ⟯ : IntermediateField 𝕂 (modularFunctionFieldBar ℓ)) (modularFunctionFieldBar
      ℓ)).comp
        (e₁ ℓ).symm.toRingEquiv.toRingHom =
      (jTr ℓ).toRingHom.comp (algebraMap (𝕂⟮jqModC 𝕂⟯) (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯)) := by
  ext; rfl

theorem finiteDimensional_adjoin_jb :
    FiniteDimensional (IntermediateField.adjoin 𝕂 ({jb ℓ} : Set (modularFunctionFieldBar ℓ)))
      (modularFunctionFieldBar ℓ) := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨data⟩ := nonempty_modularPolynomialData_of_squarefree ℓ hℓ.squarefree hℓ.one_lt
  have := finiteDimensional_adjoin_jqNModC 𝕂 data
  exact Module.Finite.of_equiv_equiv (e₁ ℓ).symm.toRingEquiv (jTr ℓ) (compat ℓ)

end DivUSol

namespace BridgeSol

theorem transcendental_coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] :
    Transcendental L (⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩ :
      laurentBaseChange L (modularFunctionFieldFull N)) := by
  intro h
  apply transcendental_jqModC L
  rw [← coeffEmb_jq]
  exact h.algebraMap (A := LaurentSeries L)

end BridgeSol

end

open ModularCurve AlgebraicCurve in
theorem solution (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] :
    Transcendental L (⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩ :
      laurentBaseChange L (modularFunctionFieldFull N)) :=
  BridgeSol.transcendental_coeffEmb_jq L N

end S_ModularCurve_transcendental_coeffEmb_jq
end P2MW
export P2MW.S_ModularCurve_transcendental_coeffEmb_jq (solution)

end privateSection

public section publicSection


open ModularCurve
theorem ModularCurve.transcendental_coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ)
    [NeZero N] :
    Transcendental L (⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩ :
      laurentBaseChange L (modularFunctionFieldFull N)) :=
  solution L N

end publicSection
