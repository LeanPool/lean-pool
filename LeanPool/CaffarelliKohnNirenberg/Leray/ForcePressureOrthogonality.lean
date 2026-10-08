/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageForce
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierJApproximationOrthogonality
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierLimit

/-!
# The force-pressure gradient is orthogonal to divergence-free fields

By Plancherel and the self-adjointness of the frequency projection, the Leray
projection fixes the pairing with every weakly divergence-free field. Hence
the field (I - ℙ) f of `lem:force-pressure` is L²-orthogonal to all weakly
divergence-free fields.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem forcePressure_inner_realPartValue (z : ComplexVec3) (y : L2Vec3) :
    inner ℝ (realPartValue z) y = (inner ℂ z (complexifyValue y)).re := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [realPartValue, realPartValueLinear, complexifyValue, complexifyValueLinear,
    complexifyFrequency, Complex.mul_re, mul_comm]

private theorem forcePressure_inner_complexifyValue (a b : L2Vec3) :
    inner ℝ a b = (inner ℂ (complexifyValue a) (complexifyValue b)).re := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [complexifyValue, complexifyValueLinear, complexifyFrequency, mul_comm]

private theorem forcePressure_integral_re {F : L2Vec3 → ℂ}
    (hF : Integrable F volume) :
    ∫ ξ, (F ξ).re = (∫ ξ, F ξ).re :=
  Complex.reCLM.integral_comp_comm hF

/-- The real pairing of a real part is the real part of the complex pairing
with the complexification. -/
theorem inner_realPartVectorL2_eq_re (Z : ComplexVectorL2) (w : RealVectorL2) :
    inner ℝ (realPartVectorL2 Z) w = (inner ℂ Z (complexifyVectorL2 w)).re := by
  rw [L2.inner_def, L2.inner_def,
    ← forcePressure_integral_re (L2.integrable_inner Z (complexifyVectorL2 w))]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume)
      realPartValue Z,
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyValue w]
    with ξ h1 h2
  change inner ℝ ((realPartValue.compLpL 2 volume Z) ξ) (w ξ) =
    (inner ℂ (Z ξ) ((complexifyValue.compLpL 2 volume w) ξ)).re
  rw [h1, h2]
  exact forcePressure_inner_realPartValue _ _

/-- Complexification preserves the real L² pairing. -/
theorem inner_complexifyVectorL2_re (v w : RealVectorL2) :
    (inner ℂ (complexifyVectorL2 v) (complexifyVectorL2 w)).re = inner ℝ v w := by
  rw [L2.inner_def, L2.inner_def,
    ← forcePressure_integral_re
      (L2.integrable_inner (complexifyVectorL2 v) (complexifyVectorL2 w))]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume)
      complexifyValue v,
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyValue w]
    with ξ h1 h2
  change (inner ℂ ((complexifyValue.compLpL 2 volume v) ξ)
      ((complexifyValue.compLpL 2 volume w) ξ)).re = inner ℝ (v ξ) (w ξ)
  rw [h1, h2]
  exact (forcePressure_inner_complexifyValue _ _).symm

/-- The Leray projection does not change the pairing with a field whose
Fourier transform is orthogonal to the frequency almost everywhere. -/
theorem inner_lerayProjectionL2_of_fourierOrthogonal (Z W : ComplexVectorL2)
    (hW : ∀ᵐ ξ ∂volume, inner ℂ (complexifyFrequency ξ)
        ((MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3) W ξ) = 0) :
    inner ℂ (lerayProjectionL2 Z) W = inner ℂ Z W := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  have h1 : inner ℂ (lerayProjectionL2 Z) W =
      inner ℂ (lerayFourierMultiplier (ℱ Z)) (ℱ W) := by
    change inner ℂ (ℱ.symm (lerayFourierMultiplier (ℱ Z))) W = _
    rw [← ℱ.inner_map_map, ℱ.apply_symm_apply]
  rw [h1, ← ℱ.inner_map_map Z W, L2.inner_def, L2.inner_def]
  have hmult := measurableFourierMultiplier_ae_eq
    (fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
    lerayApplyFormula_measurable 1
    (by
      intro ξ z
      rw [← leraySymbol_apply_eq_formula]
      simpa using leraySymbol_norm_le ξ z)
    (ℱ Z)
  apply integral_congr_ae
  filter_upwards [hmult, hW] with ξ hξ hWξ
  change inner ℂ (lerayFourierMultiplier (ℱ Z) ξ) (ℱ W ξ) = inner ℂ (ℱ Z ξ) (ℱ W ξ)
  have hξ' : lerayFourierMultiplier (ℱ Z) ξ = lerayApplyFormula ξ (ℱ Z ξ) := hξ
  rw [hξ', ← leraySymbol_apply_eq_formula, leraySymbol,
    Submodule.inner_starProjection_left_eq_right]
  congr 1
  rw [Submodule.starProjection_eq_self_iff, lerayAxis,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  exact hWξ

/-- The real Leray projection fixes the pairing with every field whose
representative is weakly divergence-free. -/
theorem realLerayProjection_inner_of_isWeakDivFree (v w : RealVectorL2)
    (hw : CKN.IsWeakDivFreeL2 (realVectorL2Representative w)) :
    inner ℝ (realLerayProjection v) w = inner ℝ v w := by
  have hJ : CKN.IsInJ (realVectorL2Representative w) :=
    CKN.isInJ_iff_weakDivFree.2 hw
  have horth := realVectorL2_fourierOrthogonal_of_isInJ w hJ
  rw [realLerayProjection, inner_realPartVectorL2_eq_re,
    inner_lerayProjectionL2_of_fourierOrthogonal _ _ horth,
    inner_complexifyVectorL2_re]

/-- The force-pressure gradient field (I - ℙ) f of `lem:force-pressure` is
L²-orthogonal to every weakly divergence-free field. -/
theorem forcePressureGradientL2_inner_eq_zero (v w : RealVectorL2)
    (hw : CKN.IsWeakDivFreeL2 (realVectorL2Representative w)) :
    inner ℝ (forcePressureGradientL2 v) w = 0 := by
  rw [forcePressureGradientL2, inner_sub_left,
    realLerayProjection_inner_of_isWeakDivFree v w hw, sub_self]

end CKN.Leray
