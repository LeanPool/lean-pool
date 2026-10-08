/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMollifierGeneral
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpConvolution
public import Mathlib.Analysis.Convolution

/-!
# The `L²` contraction for the general regularizing profile

Probability averaging by `regMollifierKernel` does not increase the spatial
`L²` norm. This is the contraction estimate in `lem:reg-mollifier-bounds`.
-/

public section

open MeasureTheory
open scoped Convolution ENNReal

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- The bilinear scalar multiplication map used in the mollifier contraction estimate. -/
@[expose]
def contractionScalarActionLinear : ℝ →ₗ[ℝ] L2Vec3 →ₗ[ℝ] L2Vec3 :=
  LinearMap.mk₂ ℝ (fun c x => c • x)
    (by intro c d x; exact add_smul c d x)
    (by intro c d x; exact mul_smul c d x)
    (by intro c x y; exact smul_add c x y)
    (by intro c d x; exact (smul_comm c d x).symm)

/-- The continuous scalar multiplication map used to bound the mollifier action. -/
@[expose]
def contractionScalarAction : ℝ →L[ℝ] L2Vec3 →L[ℝ] L2Vec3 :=
  contractionScalarActionLinear.mkContinuous₂ 1 (by
    intro c x
    change ‖c • x‖ ≤ 1 * ‖c‖ * ‖x‖
    simpa [one_mul] using (norm_smul_le c x))

/-- The dilated mollifier kernel expressed on the native coordinate space. -/
@[expose]
def scalarProfileOnVec3 (ρ : RegMollifierProfile) (ε : ℝ)
    (hε : 0 < ε) : Vec3 → ℝ :=
  fun x => regMollifierKernel ρ ε hε (WithLp.toLp 2 x)

/-- The pointwise norm of a Hilbert-valued map expressed on coordinate vectors. -/
@[expose]
def scalarNormOnVec3 (f : L2Vec3 → L2Vec3) : Vec3 → ℝ :=
  fun x => ‖f (WithLp.toLp 2 x)‖

/-- The convolution of the mollifier kernel with the pointwise norm of a vector field. -/
@[expose]
def scalarConvolutionMajor (f : L2Vec3 → L2Vec3)
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) : L2Vec3 → ℝ :=
  fun x => MeasureTheory.convolution (regMollifierKernel ρ ε hε)
    (fun y => ‖f y‖) (ContinuousLinearMap.lsmul ℝ ℝ) volume x

private theorem scalarProfileOnVec3_nonneg (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) (x : Vec3) :
    0 ≤ scalarProfileOnVec3 ρ ε hε x :=
  regMollifierKernel_nonneg ρ ε hε _

private theorem scalarProfileOnVec3_integral (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) :
    ∫ x : Vec3, scalarProfileOnVec3 ρ ε hε x = 1 := by
  have htransport : MeasurePreserving
      (WithLp.toLp 2 : Vec3 → L2Vec3) volume volume := vec3ToL2Vec3_measurePreserving
  change ∫ x : Vec3,
      regMollifierKernel ρ ε hε (WithLp.toLp 2 x) = 1
  calc
    ∫ x : Vec3, regMollifierKernel ρ ε hε (WithLp.toLp 2 x) =
        ∫ x : L2Vec3, regMollifierKernel ρ ε hε x :=
      (htransport.integral_comp
        (MeasurableEquiv.toLp 2 Vec3).measurableEmbedding
        (regMollifierKernel ρ ε hε))
    _ = 1 := regMollifierKernel_integral_eq_one ρ ε hε

private theorem scalarProfileOnVec3_integrable (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) :
  Integrable (scalarProfileOnVec3 ρ ε hε) volume := by
  have htransport : MeasurePreserving
      (WithLp.toLp 2 : Vec3 → L2Vec3) volume volume := vec3ToL2Vec3_measurePreserving
  have hkernelMem : MemLp (regMollifierKernel ρ ε hε) 1 volume :=
    memLp_one_iff_integrable.mpr (regMollifierKernel_integrable ρ ε hε)
  have hprofileMem : MemLp (scalarProfileOnVec3 ρ ε hε) 1 volume := by
    change MemLp (fun x : Vec3 => regMollifierKernel ρ ε hε
      (WithLp.toLp 2 x)) 1 volume
    exact hkernelMem.comp_measurePreserving htransport
  exact memLp_one_iff_integrable.mp hprofileMem

private theorem scalarNormOnVec3_aemeasurable
    {f : L2Vec3 → L2Vec3} (hf : MemLp f 2 volume) :
    AEMeasurable (scalarNormOnVec3 f) volume := by
  exact (continuous_norm.comp_aestronglyMeasurable
    ((hf.aestronglyMeasurable.comp_measurePreserving
      vec3ToL2Vec3_measurePreserving))).aemeasurable

private theorem scalarNormOnVec3_eLpNorm
    {f : L2Vec3 → L2Vec3} (hf : MemLp f 2 volume) :
    eLpNorm (scalarNormOnVec3 f) 2 volume = eLpNorm f 2 volume := by
  change eLpNorm (fun x : Vec3 => ‖f (WithLp.toLp 2 x)‖) 2 volume = _
  calc
    eLpNorm (fun x : Vec3 => ‖f (WithLp.toLp 2 x)‖) 2 volume =
        eLpNorm (fun x : L2Vec3 => ‖f x‖) 2 volume := by
          exact eLpNorm_comp_measurePreserving
            (continuous_norm.comp_aestronglyMeasurable hf.aestronglyMeasurable)
            vec3ToL2Vec3_measurePreserving
    _ = eLpNorm f 2 volume := eLpNorm_norm f hf.aestronglyMeasurable

private theorem scalarConvolutionMajor_eLpNorm_le
    {f : L2Vec3 → L2Vec3} (hf : MemLp f 2 volume)
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    eLpNorm (scalarConvolutionMajor f ρ ε hε) 2 volume ≤ eLpNorm f 2 volume := by
  let htransport : MeasurePreserving
      (WithLp.toLp 2 : Vec3 → L2Vec3) volume volume := vec3ToL2Vec3_measurePreserving
  let kernelV := scalarProfileOnVec3 ρ ε hε
  let fV := scalarNormOnVec3 f
  have hkernelInt : Integrable kernelV volume := scalarProfileOnVec3_integrable ρ ε hε
  have hkernelMeas : Measurable kernelV := by
    have hcont : Continuous kernelV := by
      unfold kernelV scalarProfileOnVec3 regMollifierKernel
      fun_prop
    exact hcont.measurable
  have hfMeas : AEMeasurable fV volume := by
    exact scalarNormOnVec3_aemeasurable hf
  have hYoung := CKN.young_convolution_nonneg_integral_one_of_aemeasurable
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    (scalarProfileOnVec3_nonneg ρ ε hε) hkernelInt
    (scalarProfileOnVec3_integral ρ ε hε) hkernelMeas hfMeas
  have hmajorEq (x : Vec3) :
      scalarConvolutionMajor f ρ ε hε (WithLp.toLp 2 x) =
        MeasureTheory.convolution kernelV fV
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    let F : L2Vec3 → ℝ := fun y =>
      regMollifierKernel ρ ε hε y * ‖f (WithLp.toLp 2 x - y)‖
    change (∫ y : L2Vec3, F y) = _
    calc
      (∫ y : L2Vec3, F y) = ∫ y : Vec3, F (WithLp.toLp 2 y) :=
        (htransport.integral_comp
          (MeasurableEquiv.toLp 2 Vec3).measurableEmbedding F).symm
      _ = MeasureTheory.convolution kernelV fV
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
        change (∫ y : Vec3,
          scalarProfileOnVec3 ρ ε hε y * scalarNormOnVec3 f (x - y)) = _
        rfl
  calc
    eLpNorm (scalarConvolutionMajor f ρ ε hε) 2 volume =
        eLpNorm (fun x : Vec3 => scalarConvolutionMajor f ρ ε hε
          (WithLp.toLp 2 x)) 2 volume := by
            have hmeas : AEStronglyMeasurable
                (scalarConvolutionMajor f ρ ε hε) volume := by
              apply (regMollifierKernel_memLp_two ρ ε hε).aestronglyMeasurable.convolution
              exact (hf.norm.aestronglyMeasurable)
            exact (eLpNorm_comp_measurePreserving
              hmeas htransport).symm
    _ = eLpNorm (MeasureTheory.convolution kernelV fV
          (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume := by
            apply eLpNorm_congr_ae
            exact Filter.Eventually.of_forall hmajorEq
    _ ≤ eLpNorm fV 2 volume := hYoung
    _ = eLpNorm f 2 volume := scalarNormOnVec3_eLpNorm hf

private theorem regMollifyVector_norm_le_scalarConvolutionMajor
    {f : L2Vec3 → L2Vec3} (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) (x : L2Vec3) :
    ‖regMollifyVector ρ ε hε f x‖ ≤ scalarConvolutionMajor f ρ ε hε x := by
  change ‖∫ y : L2Vec3,
    regMollifierKernel ρ ε hε y • f (x - y)‖ ≤ _
  calc
    ‖∫ y : L2Vec3, regMollifierKernel ρ ε hε y • f (x - y)‖ ≤
        ∫ y : L2Vec3, ‖regMollifierKernel ρ ε hε y • f (x - y)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y : L2Vec3,
        regMollifierKernel ρ ε hε y * ‖f (x - y)‖ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (regMollifierKernel_nonneg ρ ε hε y)]
    _ = scalarConvolutionMajor f ρ ε hε x := rfl

/-- Convolution by a normalized nonnegative regularizing kernel is a
contraction on spatial `L²`, as required by `lem:reg-mollifier-bounds`. -/
theorem regMollifyVector_eLpNorm_two_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : L2Vec3 → L2Vec3} (hf : MemLp f (2 : ℝ≥0∞) volume) :
    eLpNorm (regMollifyVector ρ ε hε f) 2 volume ≤ eLpNorm f 2 volume := by
  calc
    eLpNorm (regMollifyVector ρ ε hε f) 2 volume ≤
        eLpNorm (scalarConvolutionMajor f ρ ε hε) 2 volume :=
      eLpNorm_mono_ae_real
        (regMollifyVector_aestronglyMeasurable ρ ε hε hf)
        (Filter.Eventually.of_forall
          (regMollifyVector_norm_le_scalarConvolutionMajor ρ ε hε))
    _ ≤ eLpNorm f 2 volume := scalarConvolutionMajor_eLpNorm_le hf ρ ε hε

end CKN.Leray

end
