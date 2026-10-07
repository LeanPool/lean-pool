/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselStokesOperator
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTensorBesselEmbedding

/-!
# Physical realization of the complete Bessel Stokes operator

The spatial realization of the complete Stokes output agrees with applying
the physical Stokes operator to the spatial realization of its input.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The scalar physical Fourier weight for the inverse Bessel-potential operator. -/
@[expose]
def physicalBesselInverseWeight (s : ℝ) (ξ : L2Vec3) : ℂ :=
  (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)

private theorem physicalBesselInverseWeight_continuous (s : ℝ) :
    Continuous (physicalBesselInverseWeight s) := by
  have hbase : Continuous (fun ξ : L2Vec3 => (1 + ‖ξ‖ ^ 2 : ℝ)) := by
    fun_prop
  have hpow : Continuous (fun ξ : L2Vec3 =>
      (1 + ‖ξ‖ ^ 2 : ℝ) ^ (-s / 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro ξ
    exact (Real.continuousAt_rpow_const _ _
      (Or.inl (by positivity))).comp hbase.continuousAt
  exact Complex.continuous_ofReal.comp hpow

theorem physicalBesselInverseWeight_memLp (s : ℝ) (hs : 0 ≤ s) :
    MemLp (physicalBesselInverseWeight s) ∞ volume := by
  apply memLp_top_of_bound
    (physicalBesselInverseWeight_continuous s).aestronglyMeasurable 1
  filter_upwards [] with ξ
  have hbase : 1 ≤ (1 + ‖ξ‖ ^ 2 : ℝ) := by
    have hsq : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    linarith only [hsq]
  have hexp : -s / 2 ≤ 0 := by linarith only [hs]
  have hbound := Real.rpow_le_one_of_one_le_of_nonpos hbase hexp
  change ‖(((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact hbound

/-- The `L∞` representative of the physical inverse Bessel Fourier weight. -/
@[expose]
def physicalBesselInverseWeightLp (s : ℝ) (hs : 0 ≤ s) :
    Lp (α := L2Vec3) ℂ ∞ :=
  (physicalBesselInverseWeight_memLp s hs).toLp
    (physicalBesselInverseWeight s)

private theorem physicalBesselInverseWeightLp_ae_eq (s : ℝ) (hs : 0 ≤ s) :
    (fun ξ : L2Vec3 => physicalBesselInverseWeightLp s hs ξ) =ᵐ[volume]
      physicalBesselInverseWeight s :=
  (physicalBesselInverseWeight_memLp s hs).coeFn_toLp

/-- The tensor-valued physical Bessel symbol obtained by scaling a tensor by the inverse weight. -/
@[expose]
def physicalTensorBesselSymbol
    (s : ℝ) (p : L2Vec3 × ComplexTensor3) : ComplexTensor3 :=
  physicalBesselInverseWeight s p.1 • p.2

theorem physicalTensorBesselSymbol_measurable (s : ℝ) :
    Measurable (physicalTensorBesselSymbol s) := by
  unfold physicalTensorBesselSymbol physicalBesselInverseWeight
  fun_prop

theorem physicalTensorBesselSymbol_norm_le (s : ℝ) (hs : 0 ≤ s)
    (ξ : L2Vec3) (v : ComplexTensor3) :
    ‖physicalTensorBesselSymbol s (ξ, v)‖ ≤ ‖v‖ := by
  have hbase : 1 ≤ (1 + ‖ξ‖ ^ 2 : ℝ) := by
    have hsq : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    linarith only [hsq]
  have hexp : -s / 2 ≤ 0 := by linarith only [hs]
  have hweight := Real.rpow_le_one_of_one_le_of_nonpos hbase hexp
  change ‖physicalBesselInverseWeight s ξ • v‖ ≤ ‖v‖
  rw [norm_smul]
  unfold physicalBesselInverseWeight
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact (mul_le_mul_of_nonneg_right hweight (norm_nonneg v)).trans_eq
    (one_mul _)

/-- The bounded Fourier multiplier defined by the physical tensor Bessel symbol. -/
@[expose]
def physicalTensorBesselMultiplier (s : ℝ) (hs : 0 ≤ s)
    (F : ComplexTensorL2) : ComplexTensorL2 :=
  measurableFourierMultiplier
    (physicalTensorBesselSymbol s)
    (physicalTensorBesselSymbol_measurable s)
    1
    (fun ξ v => by simpa only [one_mul] using
      physicalTensorBesselSymbol_norm_le s hs ξ v)
    F

private theorem physicalTensorBesselMultiplier_eq_smul (s : ℝ) (hs : 0 ≤ s)
    (F : ComplexTensorL2) :
    physicalTensorBesselMultiplier s hs F =
      physicalBesselInverseWeightLp s hs • F := by
  apply Lp.ext
  filter_upwards [
    measurableFourierMultiplier_ae_eq
      (physicalTensorBesselSymbol s)
      (physicalTensorBesselSymbol_measurable s) 1
      (fun ξ v => by simpa only [one_mul] using
        physicalTensorBesselSymbol_norm_le s hs ξ v) F,
    physicalBesselInverseWeightLp_ae_eq s hs,
    Lp.coeFn_lpSMul (r := 2) (physicalBesselInverseWeightLp s hs) F]
      with ξ hM hW hS
  change physicalTensorBesselMultiplier s hs F ξ =
    physicalTensorBesselSymbol s (ξ, F ξ) at hM
  calc
    physicalTensorBesselMultiplier s hs F ξ =
        physicalTensorBesselSymbol s (ξ, F ξ) := hM
    _ = physicalBesselInverseWeight s ξ • F ξ := rfl
    _ = physicalBesselInverseWeightLp s hs ξ • F ξ := by rw [hW]
    _ = (physicalBesselInverseWeightLp s hs • F) ξ := hS.symm

private theorem physicalTensorBesselSobolevToL2_fourier_eq
    (s : ℝ) (hs : 0 ≤ s)
    (F : BesselPotentialSpace L2Vec3 ComplexTensor3 s 2) :
    (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3)
        (regularisedTensorBesselSobolevToL2 s hs F) =
      physicalBesselInverseWeightLp s hs •
        (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3) F.toLp := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
  simp only [regularisedTensorBesselSobolevToL2, LinearMap.mkContinuous_apply]
  change ℱ (ℱ.symm (physicalTensorBesselMultiplier s hs (ℱ F.toLp))) = _
  rw [ℱ.apply_symm_apply, physicalTensorBesselMultiplier_eq_smul]

private theorem physicalStokesMultiplier_smul {t : ℝ} (ht : 0 < t)
    (w : Lp (α := L2Vec3) ℂ ∞) (F : ComplexTensorL2) :
    stokesFourierMultiplier ht (w • F) = w • stokesFourierMultiplier ht F := by
  apply Lp.ext
  filter_upwards [
    measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula t p.1 p.2)
      (stokesApplyFormula_measurable t)
      (1 / Real.sqrt (2 * Real.exp 1 * t))
      (by intro ξ v; exact stokesApplyFormula_norm_le ht ξ v) (w • F),
    measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula t p.1 p.2)
      (stokesApplyFormula_measurable t)
      (1 / Real.sqrt (2 * Real.exp 1 * t))
      (by intro ξ v; exact stokesApplyFormula_norm_le ht ξ v) F,
    Lp.coeFn_lpSMul (r := 2) w F,
    Lp.coeFn_lpSMul (r := 2) w (stokesFourierMultiplier ht F)]
      with ξ hmul hF hsmul hOut
  have hmul' : stokesFourierMultiplier ht (w • F) ξ =
      stokesApplyFormula t ξ ((w • F) ξ) := by
    simpa [stokesFourierMultiplier] using hmul
  have hF' : stokesFourierMultiplier ht F ξ =
      stokesApplyFormula t ξ (F ξ) := by
    simpa [stokesFourierMultiplier] using hF
  calc
    stokesFourierMultiplier ht (w • F) ξ =
        stokesApplyFormula t ξ ((w • F) ξ) := hmul'
    _ = stokesApplyFormula t ξ (w ξ • F ξ) := by
      rw [hsmul]
      rfl
    _ = w ξ • stokesApplyFormula t ξ (F ξ) := by
      calc
        stokesApplyFormula t ξ (w ξ • F ξ) =
            stokesFrequencySymbol t ξ (w ξ • F ξ) :=
          (stokesFrequencySymbol_apply_eq_formula t ξ _).symm
        _ = w ξ • stokesFrequencySymbol t ξ (F ξ) :=
          (stokesFrequencySymbol t ξ).map_smul (w ξ) (F ξ)
        _ = w ξ • stokesApplyFormula t ξ (F ξ) := by
          rw [stokesFrequencySymbol_apply_eq_formula]
    _ = w ξ • stokesFourierMultiplier ht F ξ := by rw [hF']
    _ = (w • stokesFourierMultiplier ht F) ξ := hOut.symm

/-- The spatial L² realization intertwines the complete Bessel Stokes
operator with the physical L² Stokes operator. -/
theorem regularisedBesselStokesOperator_physical
    {t : ℝ} (ht : 0 < t) (k : ℕ)
    (F : BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2) :
    regularisedBesselSobolevToL2 ((2 * k : ℕ) : ℝ) (by positivity)
      (regularisedBesselStokesOperator ht k F) =
    stokesL2Operator ht
      (regularisedTensorBesselSobolevToL2 ((2 * k : ℕ) : ℝ)
        (by positivity) F) := by
  let s : ℝ := (2 * k : ℕ)
  let hs : 0 ≤ s := by dsimp [s]; positivity
  let ℱT := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
  let ℱV := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  have hweight :
      (fun ξ : L2Vec3 => physicalBesselInverseWeightLp s hs ξ) =ᵐ[volume]
        physicalBesselInverseWeight s :=
    physicalBesselInverseWeightLp_ae_eq s hs
  have hTensor :
      ℱT (regularisedTensorBesselSobolevToL2 s hs F) =
        physicalBesselInverseWeightLp s hs • ℱT F.toLp :=
    physicalTensorBesselSobolevToL2_fourier_eq s hs F
  have hOutputToLp : (regularisedBesselStokesOperator ht k F).toLp =
      stokesL2Operator ht F.toLp := by
    unfold regularisedBesselStokesOperator
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      BesselPotentialSpace.toLpₗᵢ_apply]
    have h := (BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexVec3
      ((2 * k : ℕ) : ℝ) 2).apply_symm_apply
        (regularisedStokesL2CLM ht F.toLp)
    rw [BesselPotentialSpace.toLpₗᵢ_apply] at h
    exact h
  have hStokesFourier (G : ComplexTensorL2) :
      ℱV (stokesL2Operator ht G) =
        stokesFourierMultiplier ht (ℱT G) := by
    change ℱV (ℱV.symm (stokesFourierMultiplier ht (ℱT G))) = _
    exact ℱV.apply_symm_apply _
  have hOutputFourier :
      ℱV (regularisedBesselSobolevToL2 s hs
        (regularisedBesselStokesOperator ht k F)) =
      physicalBesselInverseWeightLp s hs •
        ℱV (regularisedBesselStokesOperator ht k F).toLp := by
    apply Lp.ext
    filter_upwards [
      regularisedBesselSobolevToL2_fourier_ae s hs
        (regularisedBesselStokesOperator ht k F),
      hweight,
      Lp.coeFn_lpSMul (r := 2) (physicalBesselInverseWeightLp s hs)
        (ℱV (regularisedBesselStokesOperator ht k F).toLp)]
        with ξ hFourier hweightξ hSmul
    calc
      ℱV (regularisedBesselSobolevToL2 s hs
          (regularisedBesselStokesOperator ht k F)) ξ =
          physicalBesselInverseWeight s ξ •
            ℱV (regularisedBesselStokesOperator ht k F).toLp ξ := hFourier
      _ = physicalBesselInverseWeightLp s hs ξ •
          ℱV (regularisedBesselStokesOperator ht k F).toLp ξ := by
        rw [hweightξ]
      _ = (physicalBesselInverseWeightLp s hs •
          ℱV (regularisedBesselStokesOperator ht k F).toLp) ξ := hSmul.symm
  apply ℱV.injective
  calc
    ℱV (regularisedBesselSobolevToL2 s hs
        (regularisedBesselStokesOperator ht k F)) =
        physicalBesselInverseWeightLp s hs •
          ℱV (regularisedBesselStokesOperator ht k F).toLp := hOutputFourier
    _ = stokesFourierMultiplier ht
          (physicalBesselInverseWeightLp s hs • ℱT F.toLp) := by
      rw [hOutputToLp, hStokesFourier]
      exact (physicalStokesMultiplier_smul ht
        (physicalBesselInverseWeightLp s hs) (ℱT F.toLp)).symm
    _ = stokesFourierMultiplier ht (ℱT (regularisedTensorBesselSobolevToL2 s hs F)) := by
      rw [hTensor]
    _ = ℱV (stokesL2Operator ht
          (regularisedTensorBesselSobolevToL2 s hs F)) :=
      (hStokesFourier (regularisedTensorBesselSobolevToL2 s hs F)).symm

end CKN.Leray

end
