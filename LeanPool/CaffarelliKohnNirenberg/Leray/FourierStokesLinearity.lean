/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierRealification

/-!
# Linearity of the Fourier Stokes operator

The pointwise multiplier defining `K(t)` is linear in its tensor input.
This API is used to obtain continuity estimates for the Volterra term in
`lem:reg-local-mild`.
-/

public section

open MeasureTheory

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

private theorem stokesApplyFormula_add (t : ℝ) (ξ : L2Vec3)
    (F G : ComplexTensor3) :
    stokesApplyFormula t ξ (F + G) =
      stokesApplyFormula t ξ F + stokesApplyFormula t ξ G := by
  rw [← stokesFrequencySymbol_apply_eq_formula,
    ← stokesFrequencySymbol_apply_eq_formula,
    ← stokesFrequencySymbol_apply_eq_formula]
  exact (stokesFrequencySymbol t ξ).map_add F G

private theorem stokesApplyFormula_smul (t : ℝ) (ξ : L2Vec3)
    (c : ℂ) (F : ComplexTensor3) :
    stokesApplyFormula t ξ (c • F) = c • stokesApplyFormula t ξ F := by
  rw [← stokesFrequencySymbol_apply_eq_formula,
    ← stokesFrequencySymbol_apply_eq_formula]
  exact (stokesFrequencySymbol t ξ).map_smul c F

/-- The Stokes Fourier multiplier preserves addition of tensor inputs. -/
theorem stokesFourierMultiplier_add {t : ℝ} (ht : 0 < t)
    (F G : Lp (α := L2Vec3) ComplexTensor3 2 (volume : Measure L2Vec3)) :
    stokesFourierMultiplier ht (F + G) =
      stokesFourierMultiplier ht F + stokesFourierMultiplier ht G := by
  apply Lp.ext
  filter_upwards [
    measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula t p.1 p.2)
      (stokesApplyFormula_measurable t)
      (1 / Real.sqrt (2 * Real.exp 1 * t))
      (by intro ξ T; exact stokesApplyFormula_norm_le ht ξ T) (F + G),
    measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula t p.1 p.2)
      (stokesApplyFormula_measurable t)
      (1 / Real.sqrt (2 * Real.exp 1 * t))
      (by intro ξ T; exact stokesApplyFormula_norm_le ht ξ T) F,
    measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula t p.1 p.2)
      (stokesApplyFormula_measurable t)
      (1 / Real.sqrt (2 * Real.exp 1 * t))
      (by intro ξ T; exact stokesApplyFormula_norm_le ht ξ T) G,
    Lp.coeFn_add F G,
    Lp.coeFn_add (stokesFourierMultiplier ht F)
      (stokesFourierMultiplier ht G)] with ξ hsum hF hG hFG hOut
  have hsum' : stokesFourierMultiplier ht (F + G) ξ =
      stokesApplyFormula t ξ ((F + G) ξ) := by
    simpa [stokesFourierMultiplier] using hsum
  have hF' : stokesFourierMultiplier ht F ξ = stokesApplyFormula t ξ (F ξ) := by
    simpa [stokesFourierMultiplier] using hF
  have hG' : stokesFourierMultiplier ht G ξ = stokesApplyFormula t ξ (G ξ) := by
    simpa [stokesFourierMultiplier] using hG
  calc
    stokesFourierMultiplier ht (F + G) ξ =
        stokesApplyFormula t ξ ((F + G) ξ) := hsum'
    _ = stokesApplyFormula t ξ (F ξ + G ξ) := by
      rw [hFG, Pi.add_apply]
    _ = stokesApplyFormula t ξ (F ξ) + stokesApplyFormula t ξ (G ξ) := by
      exact stokesApplyFormula_add t ξ (F ξ) (G ξ)
    _ = stokesFourierMultiplier ht F ξ + stokesFourierMultiplier ht G ξ := by
      rw [hF', hG']
    _ = (stokesFourierMultiplier ht F + stokesFourierMultiplier ht G) ξ := hOut.symm

/-- The Stokes Fourier multiplier preserves complex scalar multiplication. -/
theorem stokesFourierMultiplier_smul {t : ℝ} (ht : 0 < t)
    (c : ℂ) (F : Lp (α := L2Vec3) ComplexTensor3 2 (volume : Measure L2Vec3)) :
    stokesFourierMultiplier ht (c • F) =
      c • stokesFourierMultiplier ht F := by
  apply Lp.ext
  filter_upwards [
    measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula t p.1 p.2)
      (stokesApplyFormula_measurable t)
      (1 / Real.sqrt (2 * Real.exp 1 * t))
      (by intro ξ T; exact stokesApplyFormula_norm_le ht ξ T) (c • F),
    measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula t p.1 p.2)
      (stokesApplyFormula_measurable t)
      (1 / Real.sqrt (2 * Real.exp 1 * t))
      (by intro ξ T; exact stokesApplyFormula_norm_le ht ξ T) F,
    Lp.coeFn_smul c F,
    Lp.coeFn_smul c (stokesFourierMultiplier ht F)] with ξ hmul hF hsmul hOut
  have hmul' : stokesFourierMultiplier ht (c • F) ξ =
      stokesApplyFormula t ξ ((c • F) ξ) := by
    simpa [stokesFourierMultiplier] using hmul
  have hF' : stokesFourierMultiplier ht F ξ = stokesApplyFormula t ξ (F ξ) := by
    simpa [stokesFourierMultiplier] using hF
  calc
    stokesFourierMultiplier ht (c • F) ξ =
        stokesApplyFormula t ξ ((c • F) ξ) := hmul'
    _ = stokesApplyFormula t ξ (c • F ξ) := by
      rw [hsmul, Pi.smul_apply]
    _ = c • stokesApplyFormula t ξ (F ξ) := by
      exact stokesApplyFormula_smul t ξ c (F ξ)
    _ = c • stokesFourierMultiplier ht F ξ := by rw [hF']
    _ = (c • stokesFourierMultiplier ht F) ξ := hOut.symm

/-- The physical Stokes operator is additive in the tensor field. -/
theorem stokesL2Operator_add {t : ℝ} (ht : 0 < t)
    (F G : Lp (α := L2Vec3) ComplexTensor3 2 (volume : Measure L2Vec3)) :
    stokesL2Operator ht (F + G) =
      stokesL2Operator ht F + stokesL2Operator ht G := by
  let ℱT := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
  let ℱV := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  change ℱV.symm (stokesFourierMultiplier ht (ℱT (F + G))) = _
  change ℱV.symm (stokesFourierMultiplier ht (ℱT (F + G))) =
    ℱV.symm (stokesFourierMultiplier ht (ℱT F)) +
      ℱV.symm (stokesFourierMultiplier ht (ℱT G))
  rw [ℱT.map_add, stokesFourierMultiplier_add ht, ℱV.symm.map_add]

/-- The physical Stokes operator commutes with complex scalar multiplication. -/
theorem stokesL2Operator_smul {t : ℝ} (ht : 0 < t)
    (c : ℂ) (F : Lp (α := L2Vec3) ComplexTensor3 2 (volume : Measure L2Vec3)) :
    stokesL2Operator ht (c • F) =
      c • stokesL2Operator ht F := by
  let ℱT := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
  let ℱV := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  change ℱV.symm (stokesFourierMultiplier ht (ℱT (c • F))) = _
  change ℱV.symm (stokesFourierMultiplier ht (ℱT (c • F))) =
    c • ℱV.symm (stokesFourierMultiplier ht (ℱT F))
  rw [ℱT.map_smul, stokesFourierMultiplier_smul ht, ℱV.symm.map_smul]

/-- The real Stokes operator preserves addition. -/
theorem realStokesOperator_add {t : ℝ} (ht : 0 < t)
    (F G : RealTensorL2) :
    realStokesOperator ht (F + G) =
      realStokesOperator ht F + realStokesOperator ht G := by
  simp only [realStokesOperator, map_add, stokesL2Operator_add ht]

/-- The real Stokes operator commutes with real scalar multiplication. -/
theorem realStokesOperator_smul {t : ℝ} (ht : 0 < t)
    (c : ℝ) (F : RealTensorL2) :
    realStokesOperator ht (c • F) =
      c • realStokesOperator ht F := by
  change realPartVectorL2
      (stokesL2Operator ht (complexifyTensorL2 (c • F))) = _
  rw [complexifyTensorL2.map_smul]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c,
    stokesL2Operator_smul ht]
  change realPartVectorL2
      ((c : ℂ) • stokesL2Operator ht (complexifyTensorL2 F)) = _
  change realPartVectorL2
      ((c : ℂ) • stokesL2Operator ht (complexifyTensorL2 F)) =
    c • realPartVectorL2 (stokesL2Operator ht (complexifyTensorL2 F))
  calc
    realPartVectorL2
        ((c : ℂ) • stokesL2Operator ht (complexifyTensorL2 F)) =
        realPartVectorL2
          (c • stokesL2Operator ht (complexifyTensorL2 F)) :=
      congrArg realPartVectorL2
        (RCLike.real_smul_eq_coe_smul (K := ℂ) c
          (stokesL2Operator ht (complexifyTensorL2 F))).symm
    _ = c • realPartVectorL2 (stokesL2Operator ht (complexifyTensorL2 F)) :=
      realPartVectorL2.map_smul c
        (stokesL2Operator ht (complexifyTensorL2 F))

end CKN.Leray

end
