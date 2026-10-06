/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalVelocityReg
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12PressureSlice
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalBounds
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselClampedTensorPhysical
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselTensorPhysicalRealification
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumPressureId
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedGlobalR1
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedPressure
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedEnergyForm
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierLeray

/-!
# The canonical pressure of the global regularized curve

The pressure is the canonical mollification-limit pressure of the global
regularized mild curve. On each finite interval, the regularized tensor has an
H⁴ lift; applying the double-Riesz Fourier symbol to that lift supplies a
continuous pressure representative and its first spatial derivatives.
-/

public section

open MeasureTheory FourierTransform Complex Set
open scoped ENNReal FourierTransform Real Topology ComplexInnerProductSpace

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

abbrev RegR12TensorH4 :=
  BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * 2 : ℕ) : ℝ) 2

abbrev RegR12ScalarH4 :=
  BesselPotentialSpace L2Vec3 ℂ ((2 * 2 : ℕ) : ℝ) 2

abbrev RegR12ScalarL2 := Lp (α := L2Vec3) ℂ 2

theorem regR12PressureApplyFormula_add (ξ : L2Vec3)
    (F G : ComplexTensor3) :
    pressureApplyFormula ξ (F + G) = pressureApplyFormula ξ F + pressureApplyFormula ξ G := by
  calc
    pressureApplyFormula ξ (F + G) = pressureFrequencySymbol ξ (F + G) :=
      (pressureFrequencySymbol_apply_eq_formula ξ (F + G)).symm
    _ = pressureFrequencySymbol ξ F + pressureFrequencySymbol ξ G := map_add _ _ _
    _ = pressureApplyFormula ξ F + pressureApplyFormula ξ G := by
      rw [pressureFrequencySymbol_apply_eq_formula, pressureFrequencySymbol_apply_eq_formula]

theorem regR12PressureApplyFormula_smul (ξ : L2Vec3) (c : ℂ)
    (F : ComplexTensor3) :
    pressureApplyFormula ξ (c • F) = c • pressureApplyFormula ξ F := by
  calc
    pressureApplyFormula ξ (c • F) = pressureFrequencySymbol ξ (c • F) :=
      (pressureFrequencySymbol_apply_eq_formula ξ (c • F)).symm
    _ = c • pressureFrequencySymbol ξ F := map_smul _ _ _
    _ = c • pressureApplyFormula ξ F := by
      rw [pressureFrequencySymbol_apply_eq_formula]

/-- The double-Riesz Fourier symbol as a bounded linear map on frequency
space tensor fields. -/
@[expose]
noncomputable def regR12PressureFourierCLM :
    ComplexTensorL2 →L[ℂ] RegR12ScalarL2 := by
  let m : L2Vec3 × ComplexTensor3 → ℂ := fun p => pressureApplyFormula p.1 p.2
  let hm : Measurable m := pressureApplyFormula_measurable
  let hb : ∀ ξ F, ‖m (ξ, F)‖ ≤ 1 * ‖F‖ := by
    intro ξ F
    simpa only [m, one_mul] using pressureApplyFormula_norm_le ξ F
  let L : ComplexTensorL2 →ₗ[ℂ] RegR12ScalarL2 := {
    toFun := pressureFourierMultiplier
    map_add' := by
      intro F G
      apply Lp.ext
      filter_upwards [
        measurableFourierMultiplier_ae_eq m hm 1 hb (F + G),
        measurableFourierMultiplier_ae_eq m hm 1 hb F,
        measurableFourierMultiplier_ae_eq m hm 1 hb G,
        Lp.coeFn_add F G,
        Lp.coeFn_add (pressureFourierMultiplier F) (pressureFourierMultiplier G)]
        with ξ hsum hF hG hinput houtput
      change pressureFourierMultiplier (F + G) ξ =
        (pressureFourierMultiplier F + pressureFourierMultiplier G) ξ
      rw [houtput]
      change pressureFourierMultiplier (F + G) ξ =
        pressureFourierMultiplier F ξ + pressureFourierMultiplier G ξ
      calc
        pressureFourierMultiplier (F + G) ξ =
            pressureApplyFormula ξ ((F + G) ξ) := by
              change measurableFourierMultiplier m hm 1 hb (F + G) ξ = _
              exact hsum
        _ = pressureApplyFormula ξ (F ξ + G ξ) := by
          have hin : (F + G) ξ = F ξ + G ξ := by
            simpa only [Pi.add_apply] using hinput
          exact congrArg (pressureApplyFormula ξ) hin
        _ = pressureApplyFormula ξ (F ξ) + pressureApplyFormula ξ (G ξ) :=
          regR12PressureApplyFormula_add ξ (F ξ) (G ξ)
        _ = pressureFourierMultiplier F ξ + pressureFourierMultiplier G ξ := by
          rw [show pressureFourierMultiplier F ξ = pressureApplyFormula ξ (F ξ) by
            change measurableFourierMultiplier m hm 1 hb F ξ = _
            exact hF,
            show pressureFourierMultiplier G ξ = pressureApplyFormula ξ (G ξ) by
              change measurableFourierMultiplier m hm 1 hb G ξ = _
              exact hG]
    map_smul' := by
      intro c F
      apply Lp.ext
      filter_upwards [
        measurableFourierMultiplier_ae_eq m hm 1 hb (c • F),
        measurableFourierMultiplier_ae_eq m hm 1 hb F,
        Lp.coeFn_smul c F,
        Lp.coeFn_smul c (pressureFourierMultiplier F)]
        with ξ hsmul hF hinput houtput
      change pressureFourierMultiplier (c • F) ξ =
        (c • pressureFourierMultiplier F) ξ
      calc
        pressureFourierMultiplier (c • F) ξ =
            pressureApplyFormula ξ ((c • F) ξ) := by
              change measurableFourierMultiplier m hm 1 hb (c • F) ξ = _
              exact hsmul
        _ = c • pressureApplyFormula ξ (F ξ) := by
          have hin : (c • F) ξ = c • F ξ := by
            simpa only [Pi.smul_apply] using hinput
          calc
            pressureApplyFormula ξ ((c • F) ξ) = pressureApplyFormula ξ (c • F ξ) :=
              congrArg (pressureApplyFormula ξ) hin
            _ = c • pressureApplyFormula ξ (F ξ) :=
              regR12PressureApplyFormula_smul ξ c (F ξ)
        _ = (c • pressureFourierMultiplier F) ξ := by
          have hF' : pressureFourierMultiplier F ξ = pressureApplyFormula ξ (F ξ) := by
            change measurableFourierMultiplier m hm 1 hb F ξ = _
            exact hF
          exact (congrArg (fun z : ℂ => c • z) hF'.symm).trans houtput.symm
  }
  exact L.mkContinuous 1 (by
    intro F
    change ‖pressureFourierMultiplier F‖ ≤ 1 * ‖F‖
    simpa only [one_mul] using pressureFourierMultiplier_norm_le F)

/-- The H⁴ pressure map obtained by applying the double-Riesz symbol to the
weighted Fourier transform of an H⁴ tensor. -/
@[expose]
noncomputable def regR12PressureBesselMap :
    RegR12TensorH4 →L[ℂ] RegR12ScalarH4 :=
  ((BesselPotentialSpace.toLpₗᵢ (E := L2Vec3) (F := ℂ)
    ((2 * 2 : ℕ) : ℝ) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (((Lp.fourierTransformₗᵢ (E := L2Vec3)
      (F := ℂ)).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (regR12PressureFourierCLM.comp
        (((Lp.fourierTransformₗᵢ (E := L2Vec3)
          (F := ComplexTensor3)).toContinuousLinearEquiv.toContinuousLinearMap).comp
          (BesselPotentialSpace.toLpₗᵢ (E := L2Vec3) (F := ComplexTensor3)
            ((2 * 2 : ℕ) : ℝ) 2).toContinuousLinearEquiv.toContinuousLinearMap)))

/-- The H⁴ pressure path associated with the global H⁴ velocity path. -/
@[expose]
def regR12PressurePath
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2)) :
    ℝ → RegR12ScalarH4 :=
  fun s => regR12PressureBesselMap
    (regularisedBesselClampedTensorPath ρ ε hε 2 T hT v s)

private theorem regR12PressurePath_continuous
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2)) :
    Continuous (regR12PressurePath ρ ε hε T hT v) := by
  exact regR12PressureBesselMap.continuous.comp
    (regularisedBesselClampedTensorPath_continuous ρ ε hε 2 T hT v)

@[expose]
def regR12PressureFreqPath
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2)) :
    ℝ → RegR12ScalarL2 :=
  fun t => Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ℂ)
    (regR12PressurePath ρ ε hε T hT v t).toLp

private theorem regR12PressureFreqPath_continuous
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2)) :
    Continuous (regR12PressureFreqPath ρ ε hε T hT v) := by
  have h := (BesselPotentialSpace.toLpₗᵢ (E := L2Vec3) (F := ℂ)
      ((2 * 2 : ℕ) : ℝ) 2).continuous.comp
      (regR12PressurePath_continuous ρ ε hε T hT v)
  have h' : Continuous fun t => (regR12PressurePath ρ ε hε T hT v t).toLp := by
    simpa only [Function.comp_def, BesselPotentialSpace.toLpₗᵢ_apply] using h
  exact (Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ℂ)).continuous.comp h'

/-- The continuous Fourier realization of the canonical pressure on `[0,T]`.
The canonical pressure itself is identified with this field below. -/
@[expose]
def regR12PressureModel
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2)) :
    ParabolicPoint → ℝ :=
  regR12SpaceTimeField Complex.reCLM (fun _ => 1)
    (regR12PressureFreqPath ρ ε hε T hT v)

private theorem regR12PressureModel_continuous
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2)) :
    Continuous (fun z : Vec3 × ℝ => regR12PressureModel ρ ε hε T hT v z) := by
  exact regR12SpaceTimeField_continuous Complex.reCLM (fun _ => 1)
    aestronglyMeasurable_const 1 zero_le_one
    (fun ξ => by
      rw [norm_one, one_mul]
      nlinarith only [sq_nonneg ‖ξ‖])
    (regR12PressureFreqPath ρ ε hε T hT v)
    (regR12PressureFreqPath_continuous ρ ε hε T hT v)

@[expose]
def regR12PressureRealCurvePath
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (T : ℝ) :
    C(RegularizedMildTimeInterval T, RealVectorL2) :=
  ⟨fun t => regR12Curve ρ ε hε a ha t.1,
    (regularizedGlobalMildCurve_continuous ρ ε hε _
      (regUniformMollifiedInitial_mildJData ρ ε hε ha)).comp continuous_subtype_val⟩

@[expose]
def regR12TensorBesselSymbol : L2Vec3 × ComplexTensor3 → ComplexTensor3 := fun p =>
  (((1 + ‖p.1‖ ^ 2) ^ (-((2 * 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ) • p.2

private theorem regR12TensorBesselSymbol_measurable : Measurable regR12TensorBesselSymbol := by
  unfold regR12TensorBesselSymbol
  fun_prop

private theorem regR12TensorBesselSymbol_norm_le (ξ : L2Vec3) (F : ComplexTensor3) :
    ‖regR12TensorBesselSymbol (ξ, F)‖ ≤ 1 * ‖F‖ := by
  dsimp [regR12TensorBesselSymbol]
  have hbase : 1 ≤ 1 + ‖ξ‖ ^ 2 := by
    have hsquare : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    linarith only [hsquare]
  have hexp : -((2 * 2 : ℕ) : ℝ) / 2 ≤ 0 := by norm_num
  have hw := Real.rpow_le_one_of_one_le_of_nonpos hbase hexp
  calc
    ‖(((1 + ‖ξ‖ ^ 2) ^ (-((2 * 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ) • F‖ =
        (1 + ‖ξ‖ ^ 2) ^ (-((2 * 2 : ℕ) : ℝ) / 2) * ‖F‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg F)

private theorem regR12TensorBessel_fourier_ae
    (W : RegR12TensorH4) :
    (Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ComplexTensor3)
      (regularisedTensorBesselSobolevToL2 ((2 * 2 : ℕ) : ℝ) (by positivity) W) :
        L2Vec3 → ComplexTensor3) =ᵐ[volume]
      fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
        (Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ComplexTensor3) W.toLp :
          L2Vec3 → ComplexTensor3) ξ := by
  let ℱ := Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ComplexTensor3)
  simp only [regularisedTensorBesselSobolevToL2, LinearMap.mkContinuous_apply]
  let m := regR12TensorBesselSymbol
  have hm : Measurable m := regR12TensorBesselSymbol_measurable
  have hb : ∀ ξ F, ‖m (ξ, F)‖ ≤ 1 * ‖F‖ := by
    intro ξ F
    exact regR12TensorBesselSymbol_norm_le ξ F
  change ℱ (ℱ.symm (measurableFourierMultiplier m hm 1 hb (ℱ W.toLp))) =ᵐ[volume] _
  rw [ℱ.apply_symm_apply]
  filter_upwards [measurableFourierMultiplier_ae_eq m hm 1 hb (ℱ W.toLp)] with ξ hξ
  rw [hξ]
  have hexp : -((2 * 2 : ℕ) : ℝ) / 2 = (-2 : ℝ) := by norm_num
  simp only [m, regR12TensorBesselSymbol, hexp]
  rfl

private theorem regR12PressurePath_fourier_eq
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2))
    (t : ℝ) :
    (Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ℂ)
      (regR12PressurePath ρ ε hε T hT v t).toLp : L2Vec3 → ℂ) =ᵐ[volume]
      fun ξ => pressureApplyFormula ξ
        ((Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ComplexTensor3)
          (regularisedBesselClampedTensorPath ρ ε hε 2 T hT v t).toLp :
            L2Vec3 → ComplexTensor3) ξ) := by
  have hmap : (Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ℂ)
      (regR12PressurePath ρ ε hε T hT v t).toLp : RegR12ScalarL2) =
      pressureFourierMultiplier
        (Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ComplexTensor3)
          (regularisedBesselClampedTensorPath ρ ε hε 2 T hT v t).toLp) := by
    let ℱs := Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ℂ)
    let ℱt := Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ComplexTensor3)
    let F := ℱt (regularisedBesselClampedTensorPath ρ ε hε 2 T hT v t).toLp
    dsimp only [regR12PressurePath, regR12PressureBesselMap,
      ContinuousLinearMap.comp_apply]
    simp only [ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      BesselPotentialSpace.toLpₗᵢ_apply]
    have h := (BesselPotentialSpace.toLpₗᵢ (E := L2Vec3) (F := ℂ)
      ((2 * 2 : ℕ) : ℝ) 2).apply_symm_apply
        (ℱs.symm (regR12PressureFourierCLM F))
    rw [BesselPotentialSpace.toLpₗᵢ_apply] at h
    rw [h, ℱs.apply_symm_apply]
    rfl
  rw [hmap]
  exact measurableFourierMultiplier_ae_eq _ _ _ _ _

private theorem regR12PressureModel_slice_ae_eq_quad
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2))
    (hv : ∀ t : RegularizedMildTimeInterval T,
      regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) (by positivity) (v t) =
        complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (fun x : Vec3 => regR12PressureModel ρ ε hε T hT v (x, t)) =ᵐ[volume]
      quadPressureTilde (regularizedMildClampedTensorTrajectory ρ ε hε T hT
        (regR12PressureRealCurvePath ρ ε hε a ha T) t) := by
  let W := regularisedBesselClampedTensorPath ρ ε hε 2 T hT v t
  let V := regularizedMildClampedTensorTrajectory ρ ε hε T hT
    (regR12PressureRealCurvePath ρ ε hε a ha T) t
  have hV : V = regularizedMildTensor ρ ε hε (regR12Curve ρ ε hε a ha t) := by
    simp [V, regularizedMildClampedTensorTrajectory,
      regR12PressureRealCurvePath, regularizedMildTimeClamp_eq_of_mem T hT ht]
    rfl
  have hphys : regularisedTensorBesselSobolevToL2 ((2 * 2 : ℕ) : ℝ)
      (by positivity) W = complexifyTensorL2 V := by
    exact regularisedBesselClampedTensorPath_real_toLp ρ ε hε 2 T hT v
      (regR12PressureRealCurvePath ρ ε hε a ha T)
      (by intro q; exact hv q) t
  have htensor :
      (Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ComplexTensor3)
        (complexifyTensorL2 V) : L2Vec3 → ComplexTensor3) =ᵐ[volume]
        fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
          (Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ComplexTensor3)
            W.toLp : L2Vec3 → ComplexTensor3) ξ := by
    rw [← hphys]
    exact regR12TensorBessel_fourier_ae W
  have hpress := fourier_pressureL2Operator (complexifyTensorL2 V)
  have hmodel := regR12PressurePath_fourier_eq ρ ε hε T hT v t
  have hweighted :
      (Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ℂ)
        (pressureL2Operator (complexifyTensorL2 V)) : L2Vec3 → ℂ) =ᵐ[volume]
        fun ξ => (1 : ℂ) • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
          (regR12PressureFreqPath ρ ε hε T hT v t : L2Vec3 → ℂ) ξ := by
    filter_upwards [hpress, htensor, hmodel] with ξ hp htensor hmodel
    rw [hp, htensor, regR12PressureApplyFormula_smul]
    rw [← hmodel]
    simp only [regR12PressureFreqPath, one_smul]
  have hae := regR12WeightedField_ae_eq (fun _ : L2Vec3 => (1 : ℂ))
    aestronglyMeasurable_const 1 zero_le_one regR12_one_norm_le
    (regR12PressureFreqPath ρ ε hε T hT v t)
    (pressureL2Operator (complexifyTensorL2 V)) hweighted
  have hpull := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hae
  filter_upwards [hpull] with x hx
  change regR12PressureModel ρ ε hε T hT v (x, t) = quadPressureTilde V x
  simpa [regR12PressureModel, regR12SpaceTimeField, quadPressureTilde,
    Complex.reCLM_apply] using congrArg Complex.re hx

private theorem regR12PressureModel_eq_forcedQuad
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2))
    (hv : ∀ t : RegularizedMildTimeInterval T,
      regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) (by positivity) (v t) =
        complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    forcedQuadPressure ρ ε hε (regR12Curve ρ ε hε a ha) (x, t) =
      regR12PressureModel ρ ε hε T hT v (x, t) := by
  let V := regularizedMildClampedTensorTrajectory ρ ε hε T hT
    (regR12PressureRealCurvePath ρ ε hε a ha T) t
  have hV : V = regularizedMildTensor ρ ε hε (regR12Curve ρ ε hε a ha t) := by
    simp [V, regularizedMildClampedTensorTrajectory,
      regR12PressureRealCurvePath, regularizedMildTimeClamp_eq_of_mem T hT ht]
    rfl
  have hquad := regR12PressureModel_slice_ae_eq_quad ρ ε hε a ha T hT v hv ht
  have hrep := rieszPressure_ae_eq_quadPressureTilde V
  have hrep' : (fun y : Vec3 =>
      rieszPressureSliceRepresentative 2 (by norm_num) (forcedPressureTensorLp V) y) =ᵐ[volume]
      (fun y => regR12PressureModel ρ ε hε T hT v (y, t)) := by
    filter_upwards [hrep, hquad] with y h1 h2
    exact h1.trans (h2.symm)
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hmodelCont : Continuous (fun y : Vec3 =>
      regR12PressureModel ρ ε hε T hT v (y, t)) :=
    (regR12PressureModel_continuous ρ ε hε T hT v).comp
      (continuous_id.prodMk continuous_const)
  have hlim := CKN.mollify_tendsto_of_continuous
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    (fun n => by positivity) hmodelCont x
  have hmollify : ∀ n : ℕ,
      CKN.mollify
          (rieszPressureSliceRepresentative 2 (by norm_num) (forcedPressureTensorLp V))
          (δ n) (by positivity) x =
        CKN.mollify (fun y => regR12PressureModel ρ ε hε T hT v (y, t))
          (δ n) (by positivity) x := by
    intro n
    unfold CKN.mollify
    exact congrArg (fun f => f x) <| MeasureTheory.convolution_congr
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (ae_eq_refl _) hrep'
  have hlim' : Filter.Tendsto (fun n : ℕ => CKN.mollify
      (rieszPressureSliceRepresentative 2 (by norm_num) (forcedPressureTensorLp V))
      (δ n) (by positivity) x) Filter.atTop
      (nhds (regR12PressureModel ρ ε hε T hT v (x, t))) := by
    exact hlim.congr' (Filter.Eventually.of_forall fun n => (hmollify n).symm)
  change forcedQuadPressure ρ ε hε (regR12Curve ρ ε hε a ha) (x, t) = _
  unfold forcedQuadPressure
  rw [← hV]
  exact hlim'.limUnder_eq

private theorem regR12PressureBesselMap_norm_le (W : RegR12TensorH4) :
    ‖regR12PressureBesselMap W‖ ≤ ‖W‖ := by
  unfold regR12PressureBesselMap
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    BesselPotentialSpace.toLpₗᵢ_apply]
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  calc
    ‖regR12PressureFourierCLM
        (Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ComplexTensor3) W.toLp)‖ ≤
      ‖Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ComplexTensor3) W.toLp‖ := by
        change ‖pressureFourierMultiplier
          (Lp.fourierTransformₗᵢ (E := L2Vec3) (F := ComplexTensor3) W.toLp)‖ ≤ _
        exact pressureFourierMultiplier_norm_le _
    _ = ‖W‖ := by
      rw [LinearIsometryEquiv.norm_map, BesselPotentialSpace.norm_toLp_eq]

private theorem regR12PressureFreqPath_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2))
    (t : ℝ) :
    ‖regR12PressureFreqPath ρ ε hε T hT v t‖ ≤
      regularisedBesselTensorConstant ρ ε hε 2 * ‖v‖ ^ 2 := by
  rw [regR12PressureFreqPath, LinearIsometryEquiv.norm_map,
    BesselPotentialSpace.norm_toLp_eq]
  exact (regR12PressureBesselMap_norm_le _).trans
    (regularisedBesselClampedTensorPath_norm_le ρ ε hε 2 T hT v ‖v‖
      (norm_nonneg _) (fun q => v.norm_coe_le_norm q) t)

private theorem regR12Pressure_spatialPartial_eq_model
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2))
    (hv : ∀ t : RegularizedMildTimeInterval T,
      regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) (by positivity) (v t) =
        complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))
    (z : ParabolicPoint) (hz : z.2 ∈ Icc 0 T) (j : Fin 3) :
    spatialPartial (fun y => forcedQuadPressure ρ ε hε
      (regR12Curve ρ ε hε a ha) y) j z =
        spatialPartial (regR12PressureModel ρ ε hε T hT v) j z := by
  exact regR12_spatialPartial_congr_slice
    (F := fun y => forcedQuadPressure ρ ε hε (regR12Curve ρ ε hε a ha) y)
    (F' := regR12PressureModel ρ ε hε T hT v) z
    (fun x => regR12PressureModel_eq_forcedQuad ρ ε hε a ha T hT v hv hz x) j

private theorem regR12Pressure_sliceC1
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2)) :
    (∀ z : ParabolicPoint, DifferentiableAt ℝ
      (fun x : Vec3 => regR12PressureModel ρ ε hε T hT v (x, z.2)) z.1) ∧
    (∀ j : Fin 3, Continuous (fun z : Vec3 × ℝ =>
      spatialPartial (regR12PressureModel ρ ε hε T hT v) j z)) := by
  have h := regR12ScalarPressureField_sliceC1_bound
    (regR12PressureFreqPath ρ ε hε T hT v)
    (regR12PressureFreqPath_continuous ρ ε hε T hT v)
    (regularisedBesselTensorConstant ρ ε hε 2 * ‖v‖ ^ 2)
    (fun t => regR12PressureFreqPath_norm_le ρ ε hε T hT v t)
  exact ⟨h.1, h.2.1⟩

/-- The canonical pressure of the global regularized curve is continuously
differentiable in space on positive times, with uniform strip bounds and
square integrability on bounded positive-time slabs. -/
theorem regR12Pressure_regularity
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (hPath : ∀ T : ℝ, 0 ≤ T → ∃ v : C(RegularizedMildTimeInterval T,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2),
      ∀ t : RegularizedMildTimeInterval T,
        regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) (by positivity) (v t) =
          complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1)) :
    let p : ParabolicPoint → ℝ := forcedQuadPressure ρ ε hε
      (regR12Curve ρ ε hε a ha)
    ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
    (∀ i : Fin 3, ContinuousOn (fun z => spatialPartial (fun y => p y) i z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
        |p z| ≤ C ∧ ∀ i : Fin 3, |spatialPartial (fun y => p y) i z| ≤ C) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) ∧
      ∀ i : Fin 3, MemLp (fun z => spatialPartial (fun y => p y) i z) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) := by
  let p : ParabolicPoint → ℝ := forcedQuadPressure ρ ε hε
    (regR12Curve ρ ε hε a ha)
  dsimp only [p]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine regR12_continuousOn_of_local_models fun T hT => ?_
    obtain ⟨v, hv⟩ := hPath T hT.le
    refine ⟨regR12PressureModel ρ ε hε T hT.le v,
      regR12PressureModel_continuous ρ ε hε T hT.le v, fun z hz => ?_⟩
    exact regR12PressureModel_eq_forcedQuad ρ ε hε a ha T hT.le v hv
      ⟨hz.1.le, hz.2.le⟩ z.1
  · intro i
    refine regR12_continuousOn_of_local_models fun T hT => ?_
    obtain ⟨v, hv⟩ := hPath T hT.le
    have hSlice := regR12Pressure_sliceC1 ρ ε hε T hT.le v
    refine ⟨fun z => spatialPartial (regR12PressureModel ρ ε hε T hT.le v) i z,
      ?_, fun z hz => ?_⟩
    · exact hSlice.2 i
    exact regR12Pressure_spatialPartial_eq_model ρ ε hε a ha T hT.le v hv
      (z.1, z.2) ⟨hz.1.le, hz.2.le⟩ i
  · intro z hz
    obtain ⟨v, hv⟩ := hPath z.2 hz.2.le
    have hSlice := regR12Pressure_sliceC1 ρ ε hε z.2 hz.2.le v
    have hm := hSlice.1 z
    refine hm.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    exact regR12PressureModel_eq_forcedQuad ρ ε hε a ha z.2 hz.2.le v hv
      ⟨hz.2.le, le_rfl⟩ x
  · intro δ T hδ hδT
    have hT : 0 ≤ T := le_trans hδ.le hδT.le
    obtain ⟨v, hv⟩ := hPath T hT
    have hconstant : 0 ≤ regularisedBesselTensorConstant ρ ε hε 2 :=
      (regularisedBesselTensorMap_norm_le ρ ε hε 2).1
    let C := ‖Complex.reCLM‖ * ((1 + 2 * π) *
      ((eLpNorm regR12Kernel 2 volume).toReal *
        (regularisedBesselTensorConstant ρ ε hε 2 * ‖v‖ ^ 2)))
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    refine ⟨C, hC, fun z hz => ?_⟩
    let zPair : Vec3 × ℝ := z
    have hzT : z.2 ∈ Icc 0 T := ⟨le_trans hδ.le hz.2.1, hz.2.2⟩
    let B := regularisedBesselTensorConstant ρ ε hε 2 * ‖v‖ ^ 2
    let G := regR12PressureFreqPath ρ ε hε T hT v
    have hGz : ‖G zPair.2‖ ≤ B := regR12PressureFreqPath_norm_le ρ ε hε T hT v zPair.2
    have hKernel : 0 ≤ (eLpNorm regR12Kernel 2 volume).toReal := ENNReal.toReal_nonneg
    have hone : 1 ≤ 1 + 2 * π := by linarith only [Real.pi_pos]
    have hfirst : 2 * π ≤ 1 + 2 * π := le_add_of_nonneg_left (by norm_num)
    constructor
    · have hpField := regR12SpaceTimeField_abs_le Complex.reCLM
        (fun _ => (1 : ℂ)) aestronglyMeasurable_const 1 zero_le_one
        regR12_one_norm_le G zPair
      have hpModel : |regR12PressureModel ρ ε hε T hT v zPair| ≤ C := by
        change |regR12SpaceTimeField Complex.reCLM (fun _ => (1 : ℂ)) G zPair| ≤ C
        calc
          |regR12SpaceTimeField Complex.reCLM (fun _ => (1 : ℂ)) G zPair| ≤
              ‖Complex.reCLM‖ *
                (1 * (eLpNorm regR12Kernel 2 volume).toReal * ‖G zPair.2‖) := hpField
          _ ≤ C := by
            dsimp [C]
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            calc
              1 * (eLpNorm regR12Kernel 2 volume).toReal * ‖G zPair.2‖ =
                  (eLpNorm regR12Kernel 2 volume).toReal * ‖G zPair.2‖ := by ring
              _ ≤ (eLpNorm regR12Kernel 2 volume).toReal * B :=
                mul_le_mul_of_nonneg_left hGz hKernel
              _ ≤ (1 + 2 * π) *
                  ((eLpNorm regR12Kernel 2 volume).toReal * B) :=
                by
                  simpa only [one_mul] using
                    mul_le_mul_of_nonneg_right hone (by positivity)
      have hpModel' : |regR12PressureModel ρ ε hε T hT v (zPair.1, zPair.2)| ≤ C := by
        simpa using hpModel
      have hzTpair : zPair.2 ∈ Icc 0 T := by simpa [zPair] using hzT
      change |forcedQuadPressure ρ ε hε (regR12Curve ρ ε hε a ha)
        (zPair.1, zPair.2)| ≤ C
      rw [regR12PressureModel_eq_forcedQuad ρ ε hε a ha T hT v hv hzTpair zPair.1]
      exact hpModel'
    · intro i
      have hformula : spatialPartial (regR12PressureModel ρ ε hε T hT v) i z =
          regR12SpaceTimeField Complex.reCLM
            (fun ξ => regR12CoordSymbol i ξ * (fun _ : L2Vec3 => (1 : ℂ)) ξ) G z := by
        simpa only [regR12PressureModel] using
          (regR12SpaceTimeField_spatialPartial Complex.reCLM (fun _ => (1 : ℂ))
            aestronglyMeasurable_const 1 zero_le_one regR12_one_norm_le G
            regR12_one_norm_le' z).2 i
      have hdpField := regR12SpaceTimeField_abs_le Complex.reCLM
        (fun ξ => regR12CoordSymbol i ξ * (fun _ : L2Vec3 => (1 : ℂ)) ξ)
        (((regR12CoordSymbol_continuous i).mul continuous_const).aestronglyMeasurable)
        (2 * π) (by positivity) (regR12_first_norm_le i) G z
      have hdpModel : |spatialPartial (regR12PressureModel ρ ε hε T hT v) i z| ≤ C := by
        rw [hformula]
        calc
          |regR12SpaceTimeField Complex.reCLM
              (fun ξ => regR12CoordSymbol i ξ * (fun _ : L2Vec3 => (1 : ℂ)) ξ) G z| ≤
              ‖Complex.reCLM‖ *
                (2 * π * (eLpNorm regR12Kernel 2 volume).toReal * ‖G z.2‖) := hdpField
          _ ≤ C := by
            dsimp [C]
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            calc
              2 * π * (eLpNorm regR12Kernel 2 volume).toReal * ‖G z.2‖ ≤
                  2 * π * ((eLpNorm regR12Kernel 2 volume).toReal * B) :=
                calc
                  2 * π * (eLpNorm regR12Kernel 2 volume).toReal * ‖G z.2‖ =
                      (2 * π) * ((eLpNorm regR12Kernel 2 volume).toReal * ‖G z.2‖) := by ring
                  _ ≤ (2 * π) * ((eLpNorm regR12Kernel 2 volume).toReal * B) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_left hGz hKernel) (by positivity)
              _ ≤ (1 + 2 * π) *
                  ((eLpNorm regR12Kernel 2 volume).toReal * B) :=
                mul_le_mul_of_nonneg_right hfirst (by positivity)
      rw [regR12Pressure_spatialPartial_eq_model ρ ε hε a ha T hT v hv z hzT i]
      exact hdpModel
  · intro δ T hδ hδT
    have hT : 0 ≤ T := le_trans hδ.le hδT.le
    obtain ⟨v, hv⟩ := hPath T hT
    have hconstant : 0 ≤ regularisedBesselTensorConstant ρ ε hε 2 :=
      (regularisedBesselTensorMap_norm_le ρ ε hε 2).1
    let B := regularisedBesselTensorConstant ρ ε hε 2 * ‖v‖ ^ 2
    have hB : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg hconstant (sq_nonneg _)
    have hG : ∀ t ∈ Ioo δ T, ‖regR12PressureFreqPath ρ ε hε T hT v t‖ ≤ B := by
      intro t ht
      exact regR12PressureFreqPath_norm_le ρ ε hε T hT v t
    have hmodelP := regR12SpaceTimeField_memLp_slab Complex.reCLM
      (fun _ => (1 : ℂ)) aestronglyMeasurable_const 1 zero_le_one regR12_one_norm_le
      (regR12PressureFreqPath ρ ε hε T hT v)
      (regR12PressureFreqPath_continuous ρ ε hε T hT v) δ T B hG
    have hmodelDfreq (i : Fin 3) := regR12SpaceTimeField_memLp_slab Complex.reCLM
      (fun ξ => regR12CoordSymbol i ξ * (fun _ : L2Vec3 => (1 : ℂ)) ξ)
      (((regR12CoordSymbol_continuous i).mul continuous_const).aestronglyMeasurable)
      (2 * π) (by positivity) (regR12_first_norm_le i)
      (regR12PressureFreqPath ρ ε hε T hT v)
      (regR12PressureFreqPath_continuous ρ ε hε T hT v) δ T B hG
    have hmodelD (i : Fin 3) : MemLp
        (fun z => spatialPartial (regR12PressureModel ρ ε hε T hT v) i z) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) := by
      have hEq : (fun z => spatialPartial (regR12PressureModel ρ ε hε T hT v) i z) =
          fun z => regR12SpaceTimeField Complex.reCLM
            (fun ξ => regR12CoordSymbol i ξ * (fun _ : L2Vec3 => (1 : ℂ)) ξ)
            (regR12PressureFreqPath ρ ε hε T hT v) z := by
        funext z
        simpa [regR12PressureModel] using
          (regR12SpaceTimeField_spatialPartial Complex.reCLM (fun _ => (1 : ℂ))
            aestronglyMeasurable_const 1 zero_le_one regR12_one_norm_le
            (regR12PressureFreqPath ρ ε hε T hT v) regR12_one_norm_le' z).2 i
      rw [hEq]
      exact hmodelDfreq i
    have hSlab : MeasurableSet
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)) := by
      change MeasurableSet ((Set.univ : Set Vec3) ×ˢ Ioo δ T)
      exact MeasurableSet.univ.prod measurableSet_Ioo
    have hpEq : p =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))]
        regR12PressureModel ρ ε hε T hT v := by
      filter_upwards [ae_restrict_mem hSlab] with z hz
      exact regR12PressureModel_eq_forcedQuad ρ ε hε a ha T hT v hv
        ⟨le_trans hδ.le hz.2.1.le, hz.2.2.le⟩ z.1
    have hpLp : MemLp p 2 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) := by
      have hpmeas := hmodelP.aestronglyMeasurable.congr hpEq.symm
      have hpNorm : (fun z => ‖regR12PressureModel ρ ε hε T hT v z‖) =ᵐ[
          volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))]
          (fun z => ‖p z‖) := by
        filter_upwards [hpEq.symm] with z hz
        rw [hz]
      exact hmodelP.congr_norm hpmeas hpNorm
    refine ⟨hpLp, fun i => ?_⟩
    have hDEq : (fun z => spatialPartial p i z) =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))]
        (fun z => spatialPartial (regR12PressureModel ρ ε hε T hT v) i z) := by
      filter_upwards [ae_restrict_mem hSlab] with z hz
      exact regR12Pressure_spatialPartial_eq_model ρ ε hε a ha T hT v hv z
        ⟨le_trans hδ.le hz.2.1.le, hz.2.2.le⟩ i
    have hDmeas := (hmodelD i).aestronglyMeasurable.congr hDEq.symm
    have hDnorm : (fun z => ‖spatialPartial
        (regR12PressureModel ρ ε hε T hT v) i z‖) =ᵐ[
          volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))]
          (fun z => ‖spatialPartial p i z‖) := by
      filter_upwards [hDEq.symm] with z hz
      rw [hz]
    exact (hmodelD i).congr_norm hDmeas hDnorm

end CKN.Leray

end
