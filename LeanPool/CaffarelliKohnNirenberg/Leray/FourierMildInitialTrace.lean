/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalUniqueness

/-!
# The initial value of the mild trajectory

The heat multiplier is the identity at zero time, and the Stokes integral
vanishes at zero time.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem heatMultiplier_zero_ae :
    heatMultiplier 0 (le_refl (0 : ℝ)) =ᵐ[volume]
      (fun _ : L2Vec3 => (1 : ℂ)) := by
  have hcoe : heatMultiplier 0 (le_refl (0 : ℝ)) =ᵐ[volume]
      heatSymbol 0 := by
    unfold heatMultiplier
    exact MemLp.coeFn_toLp _
  filter_upwards [hcoe] with ξ hξ
  simpa [heatSymbol] using hξ

private theorem heatSemigroup_zero (v : ComplexVectorL2) :
    heatSemigroup 0 (le_refl (0 : ℝ)) v = v := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  change ℱ.symm (heatMultiplier 0 (le_refl _) • ℱ v) = v
  apply ℱ.injective
  rw [ℱ.apply_symm_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (heatMultiplier 0 (le_refl _)) (ℱ v),
    heatMultiplier_zero_ae] with ξ hprod hone
  simpa [hone] using hprod

private theorem realPartVectorL2_complexifyVectorL2 (b : RealVectorL2) :
    realPartVectorL2 (complexifyVectorL2 b) = b := by
  apply Lp.ext
  filter_upwards [realPartValue.coeFn_compLpL (complexifyVectorL2 b),
    complexifyValue.coeFn_compLpL b] with x hreal hcomplex
  change (realPartValue.compLpL 2 volume
    (complexifyValue.compLpL 2 volume b)) x = b x
  change (realPartValue.compLpL 2 volume
    (complexifyValue.compLpL 2 volume b)) x =
      realPartValue ((complexifyValue.compLpL 2 volume b) x) at hreal
  rw [hreal, hcomplex]
  apply PiLp.ext
  intro i
  simp [realPartValue, realPartValueLinear, complexifyValue,
    complexifyValueLinear, complexifyFrequency]

/-- The heat evolution at zero time is the identity on real spatial `L²`. -/
theorem realHeatOperator_zero (b : RealVectorL2) :
    realHeatOperator 0 (le_refl (0 : ℝ)) b = b := by
  rw [realHeatOperator, heatSemigroup_zero]
  exact realPartVectorL2_complexifyVectorL2 b

end CKN.Leray

end
