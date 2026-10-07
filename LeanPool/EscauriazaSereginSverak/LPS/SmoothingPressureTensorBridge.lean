/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingPressureFrequency
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselClampedTensorPhysical
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTensorBesselEmbedding
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumPressure
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselGlobalPath
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalVelocity

/-!
# High-order tensor frequency realization for pressure

The tensor Bessel realization is an inverse polynomial Fourier
multiplier. The double-Riesz pressure map can therefore use the same
high-order frequency lift as the regularized tensor.
-/

public section

open CKN

open MeasureTheory FourierTransform Complex Set
open scoped ENNReal FourierTransform Real


noncomputable section

namespace ESS

open CKN.Leray
open CKN.Foundation.Parabolic

/-- The Bessel multiplier of order `2 * k` acting on a complex tensor. -/
@[expose] def lpsTensorBesselSymbol (k : ℕ)
    (p : L2Vec3 × ComplexTensor3) : ComplexTensor3 :=
  (((1 + ‖p.1‖ ^ 2) ^ (-((2 * k : ℕ) : ℝ) / 2) : ℝ) : ℂ) • p.2

private theorem lps_tensorBesselSymbol_measurable (k : ℕ) :
    Measurable (lpsTensorBesselSymbol k) := by
  unfold lpsTensorBesselSymbol
  fun_prop

private theorem lps_tensorBesselSymbol_norm_le
    (k : ℕ) (ξ : L2Vec3) (F : ComplexTensor3) :
    ‖lpsTensorBesselSymbol k (ξ, F)‖ ≤ 1 * ‖F‖ := by
  have hb : 1 ≤ (1 + ‖ξ‖ ^ 2 : ℝ) := by
    have hs := sq_nonneg ‖ξ‖
    linarith only [hs]
  have he : -((2 * k : ℕ) : ℝ) / 2 ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity))
      (by norm_num)
  have hw := Real.rpow_le_one_of_one_le_of_nonpos hb he
  unfold lpsTensorBesselSymbol
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _), one_mul]
  exact mul_le_of_le_one_left (norm_nonneg F) hw

/-- The tensor Bessel embedding has the inverse Bessel weight in
Fourier coordinates at every even order (`prop:lps-smoothing`). -/
theorem lps_tensorBessel_fourier_ae
    (k : ℕ)
    (W : BesselPotentialSpace L2Vec3 ComplexTensor3
      ((2 * k : ℕ) : ℝ) 2) :
    (Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ComplexTensor3)
      (CKN.Leray.regularisedTensorBesselSobolevToL2
        ((2 * k : ℕ) : ℝ) (by positivity) W) :
        L2Vec3 → ComplexTensor3) =ᵐ[volume]
      fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (-((2 * k : ℕ) : ℝ) / 2) : ℝ) : ℂ) •
        (Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ComplexTensor3)
          W.toLp : L2Vec3 → ComplexTensor3) ξ := by
  let ℱ := Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ComplexTensor3)
  let m := lpsTensorBesselSymbol k
  have hm : Measurable m := lps_tensorBesselSymbol_measurable k
  have hb : ∀ ξ F, ‖m (ξ, F)‖ ≤ 1 * ‖F‖ := by
    intro ξ F
    exact lps_tensorBesselSymbol_norm_le k ξ F
  change ℱ (ℱ.symm (CKN.Leray.measurableFourierMultiplier m hm 1 hb
    (ℱ W.toLp))) =ᵐ[volume] _
  rw [ℱ.apply_symm_apply]
  filter_upwards [CKN.Leray.measurableFourierMultiplier_ae_eq
    m hm 1 hb (ℱ W.toLp)] with ξ hξ
  rw [hξ]
  rfl

/-- The clamped physical real velocity path associated with a regularized
solution on a finite interval. -/
@[expose] def lpsRegR12RealCurvePath
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a) (T : ℝ) :
    C(CKN.Leray.RegularizedMildTimeInterval T, RealVectorL2) :=
  ⟨fun t => CKN.Leray.regR12Curve ρ ε hε a ha t.1,
    (CKN.Leray.regularizedGlobalMildCurve_continuous ρ ε hε _
      (CKN.Leray.regUniformMollifiedInitial_mildJData ρ ε hε ha)).comp
        continuous_subtype_val⟩

/-- The high-Bessel Fourier tensor frequency trajectory. -/
@[expose] def lpsRegR12HighTensorFreq
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2))
    (t : ℝ) : ComplexTensorL2 :=
  Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
    (CKN.Leray.regularisedBesselClampedTensorPath ρ ε hε
      (n + 2) T hT v t).toLp

/-- The high-Bessel tensor frequency path is continuous. -/
theorem lps_regR12HighTensorFreq_continuous
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2)) :
    Continuous (lpsRegR12HighTensorFreq ρ ε hε n T hT v) := by
  unfold lpsRegR12HighTensorFreq
  have h := (Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3).continuous.comp
    ((BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexTensor3 _ 2).continuous.comp
      (CKN.Leray.regularisedBesselClampedTensorPath_continuous
        ρ ε hε (n + 2) T hT v))
  simpa only [Function.comp_def, BesselPotentialSpace.toLpₗᵢ_apply] using h

private theorem lps_pressureApplyFormula_smul
    (ξ : L2Vec3) (c : ℂ) (F : ComplexTensor3) :
    CKN.Leray.pressureApplyFormula ξ (c • F) =
      c • CKN.Leray.pressureApplyFormula ξ F := by
  calc
    CKN.Leray.pressureApplyFormula ξ (c • F) =
        CKN.Leray.pressureFrequencySymbol ξ (c • F) :=
          (CKN.Leray.pressureFrequencySymbol_apply_eq_formula ξ _).symm
    _ = c • CKN.Leray.pressureFrequencySymbol ξ F := map_smul _ _ _
    _ = c • CKN.Leray.pressureApplyFormula ξ F := by
      rw [CKN.Leray.pressureFrequencySymbol_apply_eq_formula]

/-- The canonical pressure Fourier field is the double-Riesz image of
the high-Bessel tensor lift, with the inverse high-order weight
(`prop:lps-smoothing`). -/
theorem lps_regR12Pressure_fourier_high_ae
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2))
    (hv : ∀ t : CKN.Leray.RegularizedMildTimeInterval T,
      CKN.Leray.regularisedBesselSobolevToL2CLM
        ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v t) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha t.1))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (Lp.fourierTransformₗᵢ L2Vec3 ℂ
      (CKN.Leray.pressureL2Operator (CKN.Leray.complexifyTensorL2
        (CKN.Leray.regularizedMildTensor ρ ε hε
          (CKN.Leray.regR12Curve ρ ε hε a ha t)))) : L2Vec3 → ℂ) =ᵐ[volume]
      fun ξ => (((1 + ‖ξ‖ ^ 2) ^
        (-((2 * (n + 2) : ℕ) : ℝ) / 2) : ℝ) : ℂ) •
        CKN.Leray.pressureApplyFormula ξ
          ((lpsRegR12HighTensorFreq ρ ε hε n T hT v t : ComplexTensorL2) ξ) := by
  let V : RealTensorL2 := CKN.Leray.regularizedMildTensor ρ ε hε
    (CKN.Leray.regR12Curve ρ ε hε a ha t)
  let W := CKN.Leray.regularisedBesselClampedTensorPath ρ ε hε
    (n + 2) T hT v t
  have hphys : CKN.Leray.regularisedTensorBesselSobolevToL2
      ((2 * (n + 2) : ℕ) : ℝ) (by positivity) W =
      CKN.Leray.complexifyTensorL2 V := by
    have h := CKN.Leray.regularisedBesselClampedTensorPath_real_toLp
      ρ ε hε (n + 2) T hT v
      (lpsRegR12RealCurvePath ρ ε hε a ha T) hv t
    have hcurve : lpsRegR12RealCurvePath ρ ε hε a ha T ⟨t, ht⟩ =
        CKN.Leray.regR12Curve ρ ε hε a ha t := rfl
    simpa only [CKN.Leray.regularizedMildClampedTensorTrajectory,
      CKN.Leray.regularizedMildTimeClamp_eq_of_mem T hT ht, hcurve] using h
  have htensor := lps_tensorBessel_fourier_ae (n + 2) W
  rw [hphys] at htensor
  have hp := CKN.Leray.fourier_pressureL2Operator
    (CKN.Leray.complexifyTensorL2 V)
  filter_upwards [hp, htensor] with ξ hpξ htξ
  rw [hpξ, htξ, lps_pressureApplyFormula_smul]
  rfl

end ESS
