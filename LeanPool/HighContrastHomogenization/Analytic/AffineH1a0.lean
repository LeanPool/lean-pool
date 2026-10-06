/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineH1a0Skew
public import LeanPool.HighContrastHomogenization.Analytic.ClosureH1a
public import LeanPool.HighContrastHomogenization.Analytic.NormEquivalence

/-!
# High-contrast homogenization: Analytic.AffineH1a0

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine transport of coefficient-weighted zero-trace data

An invertible linear pullback transports the complete `H¹_{a,0}` class.  The
compactly supported approximants are composed with the matrix map, while their
gradients and the limiting weak gradient transform by the transpose matrix.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The coefficient-weighted zero-trace class is covariant under every
invertible linear change of variables. -/
theorem memH1a0_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) {b : CoeffField d}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hUfin : volume U ≠ ⊤) {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemH1a0 b U u Du) :
    MemH1a0 (affineCoefficient L hL b) (matImage L⁻¹ U)
      (fun y ↦ u (matVecMul L y))
      (fun y ↦ matVecMul (matTranspose L) (Du (matVecMul L y))) := by
  have huInt : IntegrableOn u U volume :=
    integrableOn_of_memH1a0_class hu
  have hDuInt : ∀ i, IntegrableOn (fun x ↦ Du x i) U volume :=
    fun i ↦ integrableOn_grad_of_memH1a0_class hlam hell hUfin hu i
  obtain ⟨hpair, hweak, v, hvtest, hvh1, hvskew⟩ := hu
  refine ⟨isMeasurableGradientPair_affinePullback hL hU hpair,
    hasWeakGradientOn_affinePullback_of_integrable hL hU huInt hDuInt hweak,
    fun n y ↦ v n (matVecMul L y), fun n ↦ isLocalTest_comp_matVecMul hL (hvtest n),
    ?_, ?_⟩
  · let K : ℝ≥0∞ :=
      max ((ENNReal.ofReal |L.det|⁻¹) ^ 2) (ENNReal.ofReal |L.det|⁻¹)
    have hK : K ≠ ⊤ := by simp [K]
    have hgrad : ∀ n,
        (fun y ↦ smoothGrad (fun z ↦ v n (matVecMul L z)) y -
            matVecMul (matTranspose L) (Du (matVecMul L y))) =
          fun y ↦ matVecMul (matTranspose L)
            (smoothGrad (v n) (matVecMul L y) - Du (matVecMul L y)) := by
      intro n
      funext y
      rw [smoothGrad_comp_matVecMul L (hvtest n).contDiff]
      ext i
      simp only [Pi.sub_apply, matVecMul, matTranspose, Matrix.transpose_apply]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hbound : ∀ n,
        h1sNormSqOn (affineCoefficient L hL b) (matImage L⁻¹ U)
            (fun y ↦ v n (matVecMul L y) - u (matVecMul L y))
            (fun y ↦ smoothGrad (fun z ↦ v n (matVecMul L z)) y -
              matVecMul (matTranspose L) (Du (matVecMul L y))) ≤
          K * h1sNormSqOn b U (fun x ↦ v n x - u x)
            (fun x ↦ smoothGrad (v n) x - Du x) := by
      intro n
      rw [hgrad n]
      exact h1sNormSqOn_affinePullback_le hL hU b
        (fun x ↦ v n x - u x) (fun x ↦ smoothGrad (v n) x - Du x)
    have hmajor := ENNReal.Tendsto.const_mul hvh1 (Or.inr hK)
    rw [mul_zero] at hmajor
    exact tendsto_zero_of_le_of_tendsto_zero hbound hmajor
  · let K : ℝ≥0∞ := ENNReal.ofReal (|L.det|⁻¹ * max |L.det| 1)
    have hK : K ≠ ⊤ := ENNReal.ofReal_ne_top
    have hgrad : ∀ n,
        (fun y ↦ smoothGrad (fun z ↦ v n (matVecMul L z)) y -
            matVecMul (matTranspose L) (Du (matVecMul L y))) =
          fun y ↦ matVecMul (matTranspose L)
            (smoothGrad (v n) (matVecMul L y) - Du (matVecMul L y)) := by
      intro n
      funext y
      rw [smoothGrad_comp_matVecMul L (hvtest n).contDiff]
      ext i
      simp only [Pi.sub_apply, matVecMul, matTranspose, Matrix.transpose_apply]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hbound : ∀ n,
        skewFluxDualNorm (affineCoefficient L hL b) (matImage L⁻¹ U)
            (fun y ↦ smoothGrad (fun z ↦ v n (matVecMul L z)) y -
              matVecMul (matTranspose L) (Du (matVecMul L y))) ≤
          K * skewFluxDualNorm b U (fun x ↦ smoothGrad (v n) x - Du x) := by
      intro n
      rw [hgrad n]
      exact skewFluxDualNorm_affinePullback_le hL hU b
        (fun x ↦ smoothGrad (v n) x - Du x)
    have hmajor := ENNReal.Tendsto.const_mul hvskew (Or.inr hK)
    rw [mul_zero] at hmajor
    exact tendsto_zero_of_le_of_tendsto_zero hbound hmajor

end

end HighContrast
end HCPolySupport
