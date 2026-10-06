/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMollifierContraction
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpConvolution
public import Mathlib.Analysis.Convolution

/-!
# Finite-exponent contraction for the regularizing convolution

The convolution by the normalized nonnegative kernel is contractive on every
finite spatial `L^p` space on which the input also has the `L²` regularity
needed to define its Bochner convolution.
-/

public section

open MeasureTheory
open scoped Convolution ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The regularized radial profile written as a function on native three-dimensional
coordinates. -/
@[expose]
def regUniformProfileOnVec3 (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) : Vec3 → ℝ :=
  fun x => regMollifierKernel ρ ε hε (WithLp.toLp 2 x)

/-- The pointwise norm of a spatial `L²` vector field in Euclidean
coordinates. -/
@[expose]
def regUniformL2VectorNormOnVec3 (f : L2Vec3 → L2Vec3) : Vec3 → ℝ :=
  fun x => ‖f (WithLp.toLp 2 x)‖

/-- The coordinate-space norm profile used to dominate the regularized convolution uniformly. -/
@[expose]
def regUniformConvolutionMajor (f : L2Vec3 → L2Vec3)
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) : L2Vec3 → ℝ :=
  fun x => MeasureTheory.convolution (regMollifierKernel ρ ε hε)
    (fun y => ‖f y‖) (ContinuousLinearMap.lsmul ℝ ℝ) volume x

private theorem regUniformProfile_integrable (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) :
    Integrable (regUniformProfileOnVec3 ρ ε hε) volume := by
  have htransport : MeasurePreserving
      (WithLp.toLp 2 : Vec3 → L2Vec3) volume volume := vec3ToL2Vec3_measurePreserving
  have hkernel : MemLp (regMollifierKernel ρ ε hε) 1 volume :=
    memLp_one_iff_integrable.mpr (regMollifierKernel_integrable ρ ε hε)
  have hprofile : MemLp (regUniformProfileOnVec3 ρ ε hε) 1 volume := by
    change MemLp (fun x : Vec3 => regMollifierKernel ρ ε hε
      (WithLp.toLp 2 x)) 1 volume
    exact hkernel.comp_measurePreserving htransport
  exact memLp_one_iff_integrable.mp hprofile

private theorem regUniformProfile_integral (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) :
    ∫ x : Vec3, regUniformProfileOnVec3 ρ ε hε x = 1 := by
  have htransport : MeasurePreserving
      (WithLp.toLp 2 : Vec3 → L2Vec3) volume volume := vec3ToL2Vec3_measurePreserving
  change ∫ x : Vec3, regMollifierKernel ρ ε hε (WithLp.toLp 2 x) = 1
  calc
    _ = ∫ x : L2Vec3, regMollifierKernel ρ ε hε x :=
      htransport.integral_comp (MeasurableEquiv.toLp 2 Vec3).measurableEmbedding _
    _ = 1 := regMollifierKernel_integral_eq_one ρ ε hε

private theorem regUniformNorm_aemeasurable
    {f : L2Vec3 → L2Vec3} (hf : MemLp f 2 volume) :
    AEMeasurable (regUniformL2VectorNormOnVec3 f) volume := by
  exact (continuous_norm.comp_aestronglyMeasurable
    (hf.aestronglyMeasurable.comp_measurePreserving
      vec3ToL2Vec3_measurePreserving)).aemeasurable

private theorem regUniformConvolutionMajor_eLpNorm_le
    {f : L2Vec3 → L2Vec3} (hf₂ : MemLp f 2 volume)
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ⊤) :
    eLpNorm (regUniformConvolutionMajor f ρ ε hε) p volume ≤
      eLpNorm (regUniformL2VectorNormOnVec3 f) p volume := by
  let κ := regUniformProfileOnVec3 ρ ε hε
  let g := regUniformL2VectorNormOnVec3 f
  have hκint : Integrable κ volume := regUniformProfile_integrable ρ ε hε
  have hκmeas : Measurable κ := by
    have hκcont : Continuous κ := by
      change Continuous (fun x : Vec3 =>
        (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • WithLp.toLp 2 x))
      have htoLp : Continuous (fun x : Vec3 => WithLp.toLp 2 x) :=
        PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)
      exact continuous_const.mul
        ((ρ.smooth.continuous).comp
          ((continuous_const_smul (ε⁻¹ : ℝ)).comp htoLp))
    exact hκcont.measurable
  have hgmeas : AEMeasurable g volume := regUniformNorm_aemeasurable hf₂
  have hyoung := CKN.young_convolution_nonneg_integral_one_of_aemeasurable
    hp hpTop (fun x => regMollifierKernel_nonneg ρ ε hε
      (WithLp.toLp 2 x)) hκint (regUniformProfile_integral ρ ε hε)
    hκmeas hgmeas
  have hmajorMeas : AEStronglyMeasurable
      (regUniformConvolutionMajor f ρ ε hε) volume := by
    change AEStronglyMeasurable
      (MeasureTheory.convolution (regMollifierKernel ρ ε hε)
        (fun y => ‖f y‖) (ContinuousLinearMap.lsmul ℝ ℝ) volume) volume
    exact (regMollifierKernel_memLp_two ρ ε hε).aestronglyMeasurable.convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hf₂.norm.aestronglyMeasurable
  have hmajorEq (x : Vec3) :
      regUniformConvolutionMajor f ρ ε hε (WithLp.toLp 2 x) =
        MeasureTheory.convolution κ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    change (∫ y : L2Vec3, regMollifierKernel ρ ε hε y *
        ‖f (WithLp.toLp 2 x - y)‖) = _
    calc
      _ = ∫ y : Vec3, regMollifierKernel ρ ε hε (WithLp.toLp 2 y) *
          ‖f (WithLp.toLp 2 x - WithLp.toLp 2 y)‖ := by
        exact (vec3ToL2Vec3_measurePreserving.integral_comp
          (MeasurableEquiv.toLp 2 Vec3).measurableEmbedding _).symm
      _ = MeasureTheory.convolution κ g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
        rfl
  calc
    eLpNorm (regUniformConvolutionMajor f ρ ε hε) p volume =
        eLpNorm (fun x : Vec3 =>
          regUniformConvolutionMajor f ρ ε hε (WithLp.toLp 2 x)) p volume := by
            exact (eLpNorm_comp_measurePreserving hmajorMeas
              vec3ToL2Vec3_measurePreserving).symm
    _ = eLpNorm (MeasureTheory.convolution κ g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume) p volume := by
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall hmajorEq
    _ ≤ eLpNorm g p volume := hyoung

private theorem regMollifyVector_norm_le_major
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : L2Vec3 → L2Vec3} (x : L2Vec3) :
    ‖regMollifyVector ρ ε hε f x‖ ≤
      regUniformConvolutionMajor f ρ ε hε x := by
  change ‖∫ y : L2Vec3,
      regMollifierKernel ρ ε hε y • f (x - y)‖ ≤ _
  calc
    _ ≤ ∫ y : L2Vec3,
        ‖regMollifierKernel ρ ε hε y • f (x - y)‖ := norm_integral_le_integral_norm _
    _ = regUniformConvolutionMajor f ρ ε hε x := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (regMollifierKernel_nonneg ρ ε hε y)]
      change regMollifierKernel ρ ε hε y * ‖f (x - y)‖ =
        regMollifierKernel ρ ε hε y * ‖f (x - y)‖
      rfl

/-- Normalized regularizing convolution is contractive at any finite exponent
`p ≥ 1`, provided its input also lies in `L²`. -/
theorem regMollifyVector_eLpNorm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : L2Vec3 → L2Vec3} (hf₂ : MemLp f 2 volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ⊤) :
    eLpNorm (regMollifyVector ρ ε hε f) p volume ≤
      eLpNorm (regUniformL2VectorNormOnVec3 f) p volume := by
  calc
    eLpNorm (regMollifyVector ρ ε hε f) p volume ≤
      eLpNorm (regUniformConvolutionMajor f ρ ε hε) p volume := by
      apply eLpNorm_mono_ae_real
        (regMollifyVector_aestronglyMeasurable ρ ε hε hf₂)
      exact Filter.Eventually.of_forall fun x =>
        regMollifyVector_norm_le_major ρ ε hε x
    _ ≤ eLpNorm (regUniformL2VectorNormOnVec3 f) p volume :=
      regUniformConvolutionMajor_eLpNorm_le hf₂ ρ ε hε hp hpTop

end CKN.Leray

end
