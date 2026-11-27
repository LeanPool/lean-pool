/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.TraceNormSandwich

/-!
# The centered Hilbert--Schmidt trace identity

For compact positive A and positive B, a genuine eigenbasis of A proves
Tr((A-B)^2) + 2 Tr(sqrt(B) A sqrt(B)) = Tr(A^2) + Tr(B^2).
Every term is an extended nonnegative trace, so this identity does not
subtract infinities. It later yields the exact Q_2-1 identity for densities.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ContinuousFunctionalCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem positiveTrace_square_eq_basisHilbertSchmidtSquare {ι : Type*}
    (b : HilbertBasis ι ℂ E) {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) :
    positiveTrace (A * A) = basisHilbertSchmidtSquare b A := by
  have h : A.adjoint.comp A = A * A := by rw [hA.adjoint_eq]; rfl
  rw [← h, positiveTrace_adjoint_comp b A]

theorem positiveTrace_square_difference_add {A B : E →L[ℂ] E}
    (hcA : IsCompactOperator A) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    positiveTrace ((A - B) * (A - B)) +
        2 * positiveTrace (CFC.sqrt B * A * CFC.sqrt B) =
      positiveTrace (A * A) + positiveTrace (B * B) := by
  let b := compactSelfAdjointBasis hcA hA.isSelfAdjoint
  let a : operatorEigenIndex A → ℝ := fun i => i.1.re
  let d : operatorEigenIndex A → ℝ := fun i => a i * (inner ℂ (b i) (B (b i))).re
  have ha₀ : ∀ i, 0 ≤ a i := operatorEigenFamily_eigenvalue_nonneg hA
  have hdiag₀ (i : operatorEigenIndex A) : 0 ≤ (inner ℂ (b i) (B (b i))).re :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hB).re_inner_nonneg_right _
  have hd₀ (i : operatorEigenIndex A) : 0 ≤ d i := mul_nonneg (ha₀ i) (hdiag₀ i)
  have ha (i : operatorEigenIndex A) : A (b i) = a i • b i := by
    simpa only [a, RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal] using
      compactSelfAdjointBasis_apply_operator hcA hA.isSelfAdjoint i
  have hcross (i : operatorEigenIndex A) : (inner ℂ (A (b i)) (B (b i))).re = d i := by
    change RCLike.re (inner ℂ (A (b i)) (B (b i))) = d i
    rw [ha, inner_smul_left_eq_smul, RCLike.smul_re]
    rfl
  have hentry (i : operatorEigenIndex A) :
      ‖(A - B) (b i)‖ ^ 2 + 2 * d i = ‖A (b i)‖ ^ 2 + ‖B (b i)‖ ^ 2 := by
    rw [sub_apply, @norm_sub_sq ℂ]
    simp only [RCLike.re_eq_complex_re, hcross]
    ring
  have hsqrt (i : operatorEigenIndex A) :
      (inner ℂ (b i) ((CFC.sqrt A * B * CFC.sqrt A) (b i))).re = d i := by
    change RCLike.re (inner ℂ (b i) ((CFC.sqrt A * B * CFC.sqrt A) (b i))) = d i
    rw [mul_apply_eq_comp, mul_apply_eq_comp, ← adjoint_inner_left,
      (CFC.sqrt_nonneg A).isSelfAdjoint.adjoint_eq,
      hilbertEigenbasis_sqrt_apply b hA ha,
      map_smul_of_tower, inner_smul_left_eq_smul, inner_smul_right_eq_smul,
      RCLike.smul_re, RCLike.smul_re]
    change Real.sqrt (a i) * (Real.sqrt (a i) * (inner ℂ (b i) (B (b i))).re) =
      a i * (inner ℂ (b i) (B (b i))).re
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (ha₀ i)]
  have hcrossTrace : positiveTrace (CFC.sqrt B * A * CFC.sqrt B) =
      ∑' i, ENNReal.ofReal (d i) := by
    rw [positiveTrace_sqrt_sandwich_swap hB hA,
      positiveTrace_eq_tsum_diagonal b
        ((CFC.sqrt_nonneg A).isSelfAdjoint.conjugate_nonneg hB)]
    exact tsum_congr fun i => congrArg ENNReal.ofReal (hsqrt i)
  have hentry' (i : operatorEigenIndex A) :
      ENNReal.ofReal (‖(A - B) (b i)‖ ^ 2) + 2 * ENNReal.ofReal (d i) =
        ENNReal.ofReal (‖A (b i)‖ ^ 2) + ENNReal.ofReal (‖B (b i)‖ ^ 2) := by
    calc
      _ = ENNReal.ofReal (‖(A - B) (b i)‖ ^ 2 + 2 * d i) := by
        rw [ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (by norm_num) (hd₀ i)),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ = _ := by
        rw [hentry, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  rw [positiveTrace_square_eq_basisHilbertSchmidtSquare b (hA.isSelfAdjoint.sub hB.isSelfAdjoint),
    positiveTrace_square_eq_basisHilbertSchmidtSquare b hA.isSelfAdjoint,
    positiveTrace_square_eq_basisHilbertSchmidtSquare b hB.isSelfAdjoint,
    hcrossTrace, basisHilbertSchmidtSquare, basisHilbertSchmidtSquare,
    basisHilbertSchmidtSquare, ← ENNReal.tsum_mul_left, ← tsum_add,
    ← tsum_add]
  exact tsum_congr hentry'

end VacuumBellSeparation.Gaussian
