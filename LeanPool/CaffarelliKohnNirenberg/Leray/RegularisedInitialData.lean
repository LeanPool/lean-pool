/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceMollify
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierLimit
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# The mollified initial state in the Leray space

Convolution with the smooth compactly supported profile in `eq:reg-mollifier`
preserves the divergence-free space used in `lem:reg-local-mild`.
-/

public section

open MeasureTheory
open scoped ENNReal Convolution
open CKN
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The continuous coordinate equivalence for the regularized initial-data construction. -/
@[expose]
def regularisedCoordinateEquiv : L2Vec3 ≃L[ℝ] Vec3 :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

/-- The physical-space regularized convolution kernel. -/
@[expose]
def regularisedPhysicalKernel (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) : Vec3 → ℝ :=
  fun x => regMollifierKernel ρ ε hε (WithLp.toLp 2 x)

/-- Scalar convolution by the dilated regularized mollifier kernel. -/
@[expose]
def regularisedScalarConvolution (κ : Vec3 → ℝ)
    (f : Vec3 → ℝ) : Vec3 → ℝ :=
  MeasureTheory.convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- The bilinear scalar action on vector-valued functions used by regularized convolution. -/
@[expose]
def regularisedVectorActionLinear : ℝ →ₗ[ℝ] L2Vec3 →ₗ[ℝ] L2Vec3 :=
  LinearMap.mk₂ ℝ (fun c x => c • x)
    (by intro c d x; exact add_smul c d x)
    (by intro c d x; exact mul_smul c d x)
    (by intro c x y; exact smul_add c x y)
    (by intro c d x; exact (smul_comm c d x).symm)

/-- The continuous scalar action on vector-valued `L²` functions. -/
@[expose]
def regularisedVectorAction : ℝ →L[ℝ] L2Vec3 →L[ℝ] L2Vec3 :=
  regularisedVectorActionLinear.mkContinuous₂ 1 (by
    intro c x
    change ‖c • x‖ ≤ 1 * ‖c‖ * ‖x‖
    simpa [one_mul] using (norm_smul_le c x))

/-- Convolution of a scalar profile with vector-valued initial data. -/
@[expose]
def regularisedProfileConvolution (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) (a : Vec3 → Vec3) : Vec3 → Vec3 :=
  fun x i => regularisedScalarConvolution
    (regularisedPhysicalKernel ρ ε hε) (fun y => a y i) x

private theorem regularisedPhysicalKernel_smooth
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (regularisedPhysicalKernel ρ ε hε) := by
  have hto : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => WithLp.toLp 2 x) := by
    fun_prop
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : Vec3 => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • WithLp.toLp 2 x))
  exact contDiff_const.mul (ρ.smooth.comp ((contDiff_const_smul ε⁻¹).comp hto))

private theorem regularisedPhysicalKernel_compact
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (regularisedPhysicalKernel ρ ε hε) := by
  let hhomeo : Vec3 ≃ₜ L2Vec3 := CKN.Foundation.Parabolic.vec3Homeomorph
  let hscale : L2Vec3 ≃ₜ L2Vec3 := Homeomorph.smulOfNeZero ε⁻¹
    (inv_ne_zero (ne_of_gt hε))
  have hcomp := ρ.compact.comp_homeomorph (hhomeo.trans hscale)
  have hcompact : HasCompactSupport (fun x : Vec3 =>
      (ε ^ 3)⁻¹ * ρ.rho ((hhomeo.trans hscale) x)) := hcomp.mul_left
  have heq : regularisedPhysicalKernel ρ ε hε = fun x : Vec3 =>
      (ε ^ 3)⁻¹ * ρ.rho ((hhomeo.trans hscale) x) := by
    funext x
    simp [regularisedPhysicalKernel, regMollifierKernel, hhomeo, hscale,
      Homeomorph.trans_apply]
  rw [heq]
  exact hcompact

private theorem regularisedPhysicalKernel_memLp_two
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    MemLp (regularisedPhysicalKernel ρ ε hε) (2 : ℝ≥0∞) volume := by
  have hmem := regMollifierKernel_memLp_two ρ ε hε
  change MemLp (fun x : Vec3 => regMollifierKernel ρ ε hε
    (WithLp.toLp 2 x)) 2 volume
  exact hmem.comp_measurePreserving vec3ToL2Vec3_measurePreserving

private theorem regularisedPhysicalKernel_integrable
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    Integrable (regularisedPhysicalKernel ρ ε hε) volume := by
  exact (regularisedPhysicalKernel_smooth ρ ε hε).continuous.integrable_of_hasCompactSupport
    (regularisedPhysicalKernel_compact ρ ε hε)

private theorem regularisedPhysicalKernel_nonneg
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (x : Vec3) :
    0 ≤ regularisedPhysicalKernel ρ ε hε x :=
  regMollifierKernel_nonneg ρ ε hε (WithLp.toLp 2 x)

private theorem regularisedPhysicalKernel_integral
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    ∫ x : Vec3, regularisedPhysicalKernel ρ ε hε x = 1 := by
  calc
    ∫ x : Vec3, regularisedPhysicalKernel ρ ε hε x =
        ∫ x : L2Vec3, regMollifierKernel ρ ε hε x := by
          exact vec3ToL2Vec3_measurePreserving.integral_comp
            (MeasurableEquiv.toLp 2 Vec3).measurableEmbedding _
    _ = 1 := regMollifierKernel_integral_eq_one ρ ε hε

private theorem regularisedScalarConvolution_memLp
    {κ f : Vec3 → ℝ} (hκ : Measurable κ)
    (hκnonneg : ∀ x, 0 ≤ κ x)
    (hκint : Integrable κ volume) (hκmass : ∫ x, κ x = 1)
    (hf : MemLp f (2 : ℝ≥0∞)) :
    MemLp (regularisedScalarConvolution κ f) (2 : ℝ≥0∞) volume := by
  have hyoung := CKN.young_convolution_nonneg_integral_one_of_aemeasurable
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hκnonneg hκint hκmass
    hκ hf.aestronglyMeasurable.aemeasurable
  rw [memLp_iff]
  exact hyoung.trans_lt hf.eLpNorm_lt_top

private theorem regularisedScalarConvolution_derivative
    {κ f : Vec3 → ℝ} (hκ : ContDiff ℝ 2 κ)
    (hκc : HasCompactSupport κ) (hf : MemLp f (2 : ℝ≥0∞))
    (i : Fin 3) (x : Vec3) :
    spatialDeriv (regularisedScalarConvolution κ f) i x =
      ∫ y : Vec3, (fderiv ℝ κ y) (CKN.basisVec i) * f (x - y) := by
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hκ1 : ContDiff ℝ 1 κ := hκ.of_le (by norm_num)
  have hfd := hκc.hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hκ1 hloc x
  have hconv : ConvolutionExists (fderiv ℝ κ) f
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Vec3) volume := by
    exact HasCompactSupport.convolutionExists_left
      (𝕜 := ℝ) (G := Vec3) (E := Vec3 →L[ℝ] ℝ) (E' := ℝ)
      (F := Vec3 →L[ℝ] ℝ)
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Vec3)
      (hκc.fderiv (𝕜 := ℝ))
      (hκ.continuous_fderiv (by norm_num)) hloc
  change (fderiv ℝ (regularisedScalarConvolution κ f) x) (CKN.basisVec i) = _
  rw [(by simpa [regularisedScalarConvolution] using hfd.fderiv :
    fderiv ℝ (regularisedScalarConvolution κ f) x =
      (MeasureTheory.convolution (fderiv ℝ κ) f
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Vec3) volume) x)]
  rw [MeasureTheory.convolution,
    ContinuousLinearMap.integral_apply (hconv x) (CKN.basisVec i)]
  simp [ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

private theorem regularisedProfileConvolution_component_smooth
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsInJ a) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => regularisedProfileConvolution ρ ε hε a x i) := by
  have hloc : LocallyIntegrable (fun x : Vec3 => a x i) volume :=
    (ha.1.eval i).locallyIntegrable (by norm_num)
  exact (regularisedPhysicalKernel_compact ρ ε hε).contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (regularisedPhysicalKernel_smooth ρ ε hε) hloc

private theorem regularisedProfileConvolution_component_memLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsInJ a) (i : Fin 3) :
    MemLp (fun x : Vec3 => regularisedProfileConvolution ρ ε hε a x i)
      (2 : ℝ≥0∞) volume := by
  exact regularisedScalarConvolution_memLp
    (regularisedPhysicalKernel_smooth ρ ε hε).continuous.measurable
    (regularisedPhysicalKernel_nonneg ρ ε hε)
    (regularisedPhysicalKernel_integrable ρ ε hε)
    (regularisedPhysicalKernel_integral ρ ε hε) (ha.1.eval i)

private theorem regularisedScalarConvolution_memLp_of_compactSupport
    (ρ₀ : RegMollifierProfile) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    {κ f : Vec3 → ℝ} (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (hf : MemLp f (2 : ℝ≥0∞) volume) :
    MemLp (regularisedScalarConvolution κ f) (2 : ℝ≥0∞) volume := by
  let κabs : Vec3 → ℝ := fun x => |κ x|
  let mass : ℝ := ∫ x : Vec3, κabs x
  have hκabsContinuous : Continuous κabs := continuous_abs.comp hκ
  have hκabsCompact : HasCompactSupport κabs := by
    apply HasCompactSupport.of_support_subset_isCompact hκc.isCompact
    intro x hx
    by_contra hnot
    have hzero : κ x = 0 := image_eq_zero_of_notMem_tsupport (f := κ) hnot
    apply hx
    simp [κabs, hzero]
  have hκabsIntegrable : Integrable κabs volume :=
    hκabsContinuous.integrable_of_hasCompactSupport hκabsCompact
  have hmassNonneg : 0 ≤ mass := by
    dsimp [mass, κabs]
    exact integral_nonneg (fun x => abs_nonneg (κ x))
  let base := regularisedPhysicalKernel ρ₀ ε₀ hε₀
  have hbaseSmooth : ContDiff ℝ (⊤ : ℕ∞) base :=
    regularisedPhysicalKernel_smooth ρ₀ ε₀ hε₀
  have hbaseCompact : HasCompactSupport base :=
    regularisedPhysicalKernel_compact ρ₀ ε₀ hε₀
  have hbaseNonneg : ∀ x, 0 ≤ base x :=
    regularisedPhysicalKernel_nonneg ρ₀ ε₀ hε₀
  have hbaseInt : Integrable base volume :=
    regularisedPhysicalKernel_integrable ρ₀ ε₀ hε₀
  have hbaseMass : ∫ x : Vec3, base x = 1 :=
    regularisedPhysicalKernel_integral ρ₀ ε₀ hε₀
  let q : Vec3 → ℝ := fun x => (mass + 1)⁻¹ * (κabs x + base x)
  have hden : 0 < mass + 1 := by linarith only [hmassNonneg]
  have hqContinuous : Continuous q := by
    dsimp [q]
    exact continuous_const.mul (hκabsContinuous.add hbaseSmooth.continuous)
  have hqCompact : HasCompactSupport q := by
    have hsum : HasCompactSupport (fun x : Vec3 => κabs x + base x) :=
      hκabsCompact.add hbaseCompact
    exact hsum.mul_left
  have hqMeas : Measurable q := hqContinuous.measurable
  have hqNonneg : ∀ x, 0 ≤ q x := by
    intro x
    dsimp [q]
    exact mul_nonneg (inv_nonneg.mpr hden.le)
      (add_nonneg (abs_nonneg _) (hbaseNonneg x))
  have hqInt : Integrable q volume := hqContinuous.integrable_of_hasCompactSupport hqCompact
  have hqMass : ∫ x : Vec3, q x = 1 := by
    dsimp [q]
    rw [integral_const_mul, integral_add hκabsIntegrable hbaseInt, hbaseMass]
    change (mass + 1)⁻¹ * (mass + 1) = 1
    exact inv_mul_cancel₀ (ne_of_gt hden)
  have hfabs : MemLp (fun x : Vec3 => |f x|) (2 : ℝ≥0∞) volume := hf.norm
  have hqYoung := CKN.young_convolution_nonneg_integral_one_of_aemeasurable
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hqNonneg hqInt hqMass hqMeas
    hfabs.aestronglyMeasurable.aemeasurable
  have hqMajor : MemLp (regularisedScalarConvolution q (fun x => |f x|))
      (2 : ℝ≥0∞) volume := by
    rw [memLp_iff]
    exact hqYoung.trans_lt hfabs.eLpNorm_lt_top
  have hqLp : MemLp q (2 : ℝ≥0∞) volume :=
    hqContinuous.memLp_of_hasCompactSupport hqCompact
  have hκabsLp : MemLp κabs (2 : ℝ≥0∞) volume :=
    hκabsContinuous.memLp_of_hasCompactSupport hκabsCompact
  have hconvQ : ConvolutionExists q (fun x => |f x|)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    ConvolutionExists.of_memLp_memLp
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hqLp hfabs
  have hconvAbs : ConvolutionExists κabs (fun x => |f x|)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    ConvolutionExists.of_memLp_memLp
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hκabsLp hfabs
  have hkernelBound (x : Vec3) : κabs x ≤ (mass + 1) * q x := by
    dsimp [q]
    have heq :
        (mass + 1) * ((mass + 1)⁻¹ * (κabs x + base x)) =
          κabs x + base x := by
      field_simp [ne_of_gt hden]
    calc
      κabs x ≤ κabs x + base x := le_add_of_nonneg_right (hbaseNonneg x)
      _ = (mass + 1) * ((mass + 1)⁻¹ * (κabs x + base x)) := heq.symm
  have hmajorBound (x : Vec3) :
      regularisedScalarConvolution κabs (fun y => |f y|) x ≤
        (mass + 1) * regularisedScalarConvolution q (fun y => |f y|) x := by
    change (∫ y : Vec3, κabs y * |f (x - y)|) ≤
      (mass + 1) * ∫ y : Vec3, q y * |f (x - y)|
    have hleft := (hconvAbs x).integrable
    have hright := (hconvQ x).integrable
    have hright' : Integrable
        (fun y : Vec3 => ((mass + 1) * q y) * |f (x - y)|) volume := by
      convert hright.const_mul (mass + 1) using 1
      funext y
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      ring_nf
    calc
      _ ≤ ∫ y : Vec3, ((mass + 1) * q y) * |f (x - y)| :=
        integral_mono hleft hright' (fun y =>
            mul_le_mul_of_nonneg_right (hkernelBound y) (abs_nonneg _))
      _ = (mass + 1) * ∫ y : Vec3, q y * |f (x - y)| := by
        calc
          _ = ∫ y : Vec3, (mass + 1) * (q y * |f (x - y)|) := by
            apply integral_congr_ae
            filter_upwards [] with y
            ring
          _ = _ := integral_const_mul (mass + 1) _
  have habsConvolutionMeas : AEStronglyMeasurable
      (regularisedScalarConvolution κabs (fun y => |f y|)) volume := by
    exact hκabsLp.aestronglyMeasurable.convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hfabs.aestronglyMeasurable
  have habsNonneg (x : Vec3) :
      0 ≤ regularisedScalarConvolution κabs (fun y => |f y|) x := by
    change 0 ≤ ∫ y : Vec3, κabs y * |f (x - y)|
    exact integral_nonneg fun y => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hqNonnegValue (x : Vec3) :
      0 ≤ regularisedScalarConvolution q (fun y => |f y|) x := by
    change 0 ≤ ∫ y : Vec3, q y * |f (x - y)|
    exact integral_nonneg fun y => mul_nonneg (hqNonneg y) (abs_nonneg _)
  have hnormMajorBound (x : Vec3) :
      ‖regularisedScalarConvolution κabs (fun y => |f y|) x‖ ≤
        (mass + 1) * ‖regularisedScalarConvolution q (fun y => |f y|) x‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (habsNonneg x),
      Real.norm_eq_abs, abs_of_nonneg (hqNonnegValue x)]
    exact hmajorBound x
  have habsConvolutionLp : MemLp
      (regularisedScalarConvolution κabs (fun y => |f y|))
      (2 : ℝ≥0∞) volume :=
    hqMajor.of_le_mul habsConvolutionMeas
      (Filter.Eventually.of_forall hnormMajorBound)
  have hκLp : MemLp κ (2 : ℝ≥0∞) volume := hκ.memLp_of_hasCompactSupport hκc
  have hconvκ : ConvolutionExists κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    ConvolutionExists.of_memLp_memLp
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hκLp hf
  have hpoint (x : Vec3) :
      ‖regularisedScalarConvolution κ f x‖ ≤
        regularisedScalarConvolution κabs (fun y => |f y|) x := by
    change ‖∫ y : Vec3, κ y * f (x - y)‖ ≤
      ∫ y : Vec3, |κ y| * |f (x - y)|
    calc
      _ ≤ ∫ y : Vec3, ‖κ y * f (x - y)‖ := norm_integral_le_integral_norm _
      _ = ∫ y : Vec3, |κ y| * |f (x - y)| := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [Real.norm_eq_abs, abs_mul]
  have hconvκMeas : AEStronglyMeasurable (regularisedScalarConvolution κ f) volume :=
    hκLp.aestronglyMeasurable.convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hf.aestronglyMeasurable
  have hpointNorm (x : Vec3) :
      ‖regularisedScalarConvolution κ f x‖ ≤
        ‖regularisedScalarConvolution κabs (fun y => |f y|) x‖ := by
    have hright :
        ‖regularisedScalarConvolution κabs (fun y => |f y|) x‖ =
          regularisedScalarConvolution κabs (fun y => |f y|) x := by
      rw [Real.norm_eq_abs, abs_of_nonneg (habsNonneg x)]
    rw [hright]
    exact hpoint x
  exact habsConvolutionLp.of_le hconvκMeas
    (Filter.Eventually.of_forall hpointNorm)

/-- The tuple of coordinate functions associated with the regularized vector data. -/
@[expose]
def regularisedCoordinateTuple (n : ℕ) (w : Fin n → Fin 3) :
    Fin n → Vec3 := fun j => CKN.basisVec (w j)

private theorem regularisedScalarConvolution_iterated
    (n : ℕ) (w : Fin n → Fin 3) (κ : Vec3 → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    {f : Vec3 → ℝ} (hf : MemLp f (2 : ℝ≥0∞) volume) (x : Vec3) :
    (iteratedFDeriv ℝ n (regularisedScalarConvolution κ f) x)
        (regularisedCoordinateTuple n w) =
      regularisedScalarConvolution
        (fun y => (iteratedFDeriv ℝ n κ y) (regularisedCoordinateTuple n w)) f x := by
  induction n generalizing κ x with
  | zero =>
      simp [regularisedScalarConvolution]
  | succ n ih =>
      let κtail : Vec3 → ℝ := fun y =>
        (iteratedFDeriv ℝ n κ y) (regularisedCoordinateTuple n (Fin.tail w))
      have htupleTail : regularisedCoordinateTuple n (Fin.tail w) =
          Fin.tail (regularisedCoordinateTuple (n + 1) w) := rfl
      have hκtailCont : ContDiff ℝ 2 κtail := by
        have hiter : ContDiff ℝ 2 (iteratedFDeriv ℝ n κ) := by
          have hnat : ContDiff ℝ (2 + n) κ := hκ.of_le (by simp)
          exact hnat.iteratedFDeriv_right' (m := 2) (i := n)
        change ContDiff ℝ 2 (fun y =>
          (iteratedFDeriv ℝ n κ y) (regularisedCoordinateTuple n (Fin.tail w)))
        exact hiter.continuousLinearMap_comp (ContinuousMultilinearMap.apply ℝ
          (fun _ : Fin n => Vec3) ℝ
          (regularisedCoordinateTuple n (Fin.tail w)))
      have hκtailCompact : HasCompactSupport κtail := by
        have hiter : HasCompactSupport (iteratedFDeriv ℝ n κ) := hκc.iteratedFDeriv n
        apply HasCompactSupport.of_support_subset_isCompact hiter.isCompact
        intro y hy
        simp only [Function.mem_support] at hy
        by_contra hnot
        have hzero : iteratedFDeriv ℝ n κ y = 0 :=
          image_eq_zero_of_notMem_tsupport (f := iteratedFDeriv ℝ n κ) hnot
        exact hy (by simp [κtail, hzero])
      have hIHfun :
          (fun z : Vec3 => (iteratedFDeriv ℝ n
            (regularisedScalarConvolution κ f) z)
              (regularisedCoordinateTuple n (Fin.tail w))) =
            regularisedScalarConvolution κtail f := by
        funext z
        exact ih (Fin.tail w) κ hκ hκc z
      have hconvSmooth : ContDiff ℝ (⊤ : ℕ∞)
          (regularisedScalarConvolution κ f) :=
        hκc.contDiff_convolution_left (n := ⊤)
          (L := ContinuousLinearMap.lsmul ℝ ℝ) hκ
          (hf.locallyIntegrable (by norm_num))
      have hconvDiff : DifferentiableAt ℝ
          (iteratedFDeriv ℝ n (regularisedScalarConvolution κ f)) x :=
        hconvSmooth.contDiffAt.differentiableAt_iteratedFDeriv
          (by exact_mod_cast ENat.natCast_lt_top n)
      rw [hconvDiff.iteratedFDeriv_succ_apply_left'
        (m := regularisedCoordinateTuple (n + 1) w)]
      rw [← htupleTail, hIHfun]
      change (fderiv ℝ (regularisedScalarConvolution κtail f) x)
          (CKN.basisVec (w 0)) = _
      have hderiv := regularisedScalarConvolution_derivative
        (hκtailCont.of_le (by norm_num))
        hκtailCompact hf (w 0) x
      change spatialDeriv (regularisedScalarConvolution κtail f) (w 0) x = _
      rw [hderiv]
      apply integral_congr_ae
      filter_upwards [] with y
      have hkernelDeriv (y : Vec3) :
          (fderiv ℝ κtail y) (CKN.basisVec (w 0)) =
            (iteratedFDeriv ℝ (n + 1) κ y)
              (regularisedCoordinateTuple (n + 1) w) := by
        have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n κ) y :=
          hκ.contDiffAt.differentiableAt_iteratedFDeriv
            (by exact_mod_cast ENat.natCast_lt_top n)
        symm
        simpa [κtail, regularisedCoordinateTuple, htupleTail] using
          hdiff.iteratedFDeriv_succ_apply_left'
            (m := regularisedCoordinateTuple (n + 1) w)
      rw [hkernelDeriv]
      simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- Ordered derivatives commute with convolution by a smooth compactly
supported scalar kernel, as in `lem:reg-mollifier-bounds`. -/
theorem regularisedScalarConvolution_iterated_derivative
    (n : ℕ) (w : Fin n → Fin 3) (κ : Vec3 → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    {f : Vec3 → ℝ} (hf : MemLp f (2 : ℝ≥0∞) volume) (x : Vec3) :
    (iteratedFDeriv ℝ n
      (MeasureTheory.convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x)
        (fun j => CKN.basisVec (w j)) =
      MeasureTheory.convolution
        (fun y => (iteratedFDeriv ℝ n κ y)
          (fun j => CKN.basisVec (w j))) f
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  change (iteratedFDeriv ℝ n
      (MeasureTheory.convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x)
        (regularisedCoordinateTuple n w) =
      MeasureTheory.convolution
        (fun y => (iteratedFDeriv ℝ n κ y)
          (regularisedCoordinateTuple n w)) f
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x
  simpa [regularisedScalarConvolution] using
    regularisedScalarConvolution_iterated n w κ hκ hκc hf x

private theorem regularisedProfileConvolution_divergence_eq_zero
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsWeakDivFreeL2 a) (x : Vec3) :
    ∑ i : Fin 3, spatialDeriv
      (fun y => regularisedProfileConvolution ρ ε hε a y i) i x = 0 := by
  let κ := regularisedPhysicalKernel ρ ε hε
  have hκ : ContDiff ℝ (⊤ : ℕ∞) κ := regularisedPhysicalKernel_smooth ρ ε hε
  have hκc : HasCompactSupport κ := regularisedPhysicalKernel_compact ρ ε hε
  let ψ : CKN.WeakTestFunction (Set.univ : Set Vec3) :=
    ⟨fun y => κ (x - y), hκ.comp (contDiff_const.sub contDiff_id),
      hκc.comp_homeomorph (Homeomorph.subLeft x), Set.subset_univ _⟩
  have hψderiv (y : Vec3) (i : Fin 3) :
      ψ.partialDeriv i y = -(fderiv ℝ κ (x - y)) (CKN.basisVec i) := by
    have hinner : HasFDerivAt (fun z : Vec3 => x - z)
        (-(1 : Vec3 →L[ℝ] Vec3)) y := (hasFDerivAt_id y).const_sub x
    have houter : HasFDerivAt κ (fderiv ℝ κ (x - y)) (x - y) :=
      (hκ.differentiable (by simp) (x - y)).hasFDerivAt
    have hcomp := houter.comp y hinner
    change (fderiv ℝ (fun z => κ (x - z)) y) (CKN.basisVec i) = _
    simpa [ContinuousLinearMap.comp_apply, Function.comp_def] using
      congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i)) hcomp.fderiv
  have hgradCont (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec3 => ψ.partialDeriv i y) :=
    CKN.contDiff_spatialDeriv_smooth ψ.contDiff i
  have hgradCompact (i : Fin 3) : HasCompactSupport
      (fun y : Vec3 => ψ.partialDeriv i y) := by
    change HasCompactSupport (fun y => (fderiv ℝ ψ.toFun y) (CKN.basisVec i))
    exact ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)
  have hgradLp (i : Fin 3) : MemLp
      (fun y : Vec3 => ψ.partialDeriv i y) (2 : ℝ≥0∞) volume :=
    (hgradCont i).continuous.memLp_of_hasCompactSupport (hgradCompact i)
  have hpartsInt (i : Fin 3) : Integrable
      (fun y : Vec3 => a y i * ψ.partialDeriv i y) volume :=
    (ha.1.eval i).integrable_mul (hgradLp i)
  have hsumInt :
      ∫ y : Vec3, ∑ i : Fin 3, a y i * ψ.partialDeriv i y ∂volume =
        ∑ i : Fin 3, ∫ y : Vec3, a y i * ψ.partialDeriv i y ∂volume := by
    simpa using integral_finsetSum (μ := volume) Finset.univ
      (f := fun i y => a y i * ψ.partialDeriv i y)
      (by intro i hi; exact hpartsInt i)
  have hweakSum :
      ∑ i : Fin 3, ∫ y : Vec3, a y i * ψ.partialDeriv i y ∂volume = 0 := by
    rw [← hsumInt]
    exact ha.2 ψ
  have hchange (i : Fin 3) :
      ∫ y : Vec3, a y i * (fderiv ℝ κ (x - y)) (CKN.basisVec i) ∂volume =
        ∫ t : Vec3, (fderiv ℝ κ t) (CKN.basisVec i) * a (x - t) i ∂volume := by
    have h := (MeasureTheory.Measure.measurePreserving_sub_left volume x).integral_comp
      (Homeomorph.subLeft x).measurableEmbedding
      (fun y => a y i * (fderiv ℝ κ (x - y)) (CKN.basisVec i))
    rw [← h]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [sub_sub_cancel]
    ring
  have hpart (i : Fin 3) :
      ∫ y : Vec3, a y i * ψ.partialDeriv i y ∂volume =
        -(∫ t : Vec3, (fderiv ℝ κ t) (CKN.basisVec i) * a (x - t) i ∂volume) := by
    have hfun : (fun y : Vec3 => a y i * ψ.partialDeriv i y) =
        fun y => -(a y i * (fderiv ℝ κ (x - y)) (CKN.basisVec i)) := by
      funext y
      rw [hψderiv]
      ring
    rw [hfun, integral_neg, hchange]
  have hsumKernel :
      ∑ i : Fin 3, ∫ t : Vec3,
        (fderiv ℝ κ t) (CKN.basisVec i) * a (x - t) i ∂volume = 0 := by
    have hneg : -(∑ i : Fin 3, ∫ t : Vec3,
        (fderiv ℝ κ t) (CKN.basisVec i) * a (x - t) i ∂volume) = 0 := by
      simpa [hpart, ← Finset.sum_neg_distrib] using hweakSum
    exact neg_eq_zero.mp hneg
  calc
    ∑ i : Fin 3, spatialDeriv
        (fun y => regularisedProfileConvolution ρ ε hε a y i) i x =
      ∑ i : Fin 3, ∫ t : Vec3,
        (fderiv ℝ κ t) (CKN.basisVec i) * a (x - t) i ∂volume := by
          apply Finset.sum_congr rfl
          intro i hi
          exact regularisedScalarConvolution_derivative
            (hκ.of_le (by norm_num)) hκc
            (ha.1.eval i) i x
    _ = 0 := hsumKernel

private theorem regularisedProfileConvolution_isWeakDivFreeL2
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsInJ a) :
    CKN.IsWeakDivFreeL2 (regularisedProfileConvolution ρ ε hε a) := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞)
      (regularisedProfileConvolution ρ ε hε a) := by
    rw [contDiff_pi]
    intro i
    exact regularisedProfileConvolution_component_smooth ρ ε hε ha i
  refine ⟨memLp_pi_iff.mpr (fun i =>
    regularisedProfileConvolution_component_memLp ρ ε hε ha i), ?_⟩
  intro ψ
  exact CKN.smoothSolenoidal_test_integral_zero
    (regularisedProfileConvolution ρ ε hε a) hsm
    (fun x => regularisedProfileConvolution_divergence_eq_zero ρ ε hε
      (CKN.isInJ_weakDivFree ha) x) ψ

private theorem regUniformMollifiedInitial_eq_regularisedProfileConvolution
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume) :
    regUniformMollifiedInitial ρ ε hε a =
      regularisedProfileConvolution ρ ε hε a := by
  have hinput : MemLp (regUniformSpatialField a) (2 : ℝ≥0∞) volume := by
    have hcoord : MemLp
        (fun x : L2Vec3 => a (WithLp.ofLp x)) (2 : ℝ≥0∞) volume :=
      ha.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hkernel : MemLp (regMollifierKernel ρ ε hε)
      (2 : ℝ≥0∞) volume := regMollifierKernel_memLp_two ρ ε hε
  have heq (x : Vec3) (i : Fin 3) :
      regUniformMollifiedInitial ρ ε hε a x i =
        regularisedProfileConvolution ρ ε hε a x i := by
    let f := regUniformSpatialField a
    let xL2 : L2Vec3 := WithLp.toLp 2 x
    have hconv : ConvolutionExists (regMollifierKernel ρ ε hε) f
        regularisedVectorAction volume := by
      exact ConvolutionExists.of_memLp_memLp (L := regularisedVectorAction)
        hkernel hinput
    have hintBase : Integrable
        (fun y : L2Vec3 => regMollifierKernel ρ ε hε y • f (xL2 - y)) volume := by
      exact (hconv xL2).integrable
    have hintCoordinate : Integrable
        (fun y : L2Vec3 => regularisedCoordinateEquiv
          (regMollifierKernel ρ ε hε y • f (xL2 - y))) volume := by
      exact regularisedCoordinateEquiv.toContinuousLinearMap.integrable_comp hintBase
    change (regularisedCoordinateEquiv
      (regMollifyVector ρ ε hε f xL2)) i = _
    change (regularisedCoordinateEquiv
      (MeasureTheory.convolution (regMollifierKernel ρ ε hε) f
        regularisedVectorAction volume xL2)) i = _
    rw [show MeasureTheory.convolution (regMollifierKernel ρ ε hε) f
        regularisedVectorAction volume xL2 =
          ∫ y : L2Vec3, regMollifierKernel ρ ε hε y • f (xL2 - y) by rfl]
    rw [← regularisedCoordinateEquiv.integral_comp_comm]
    rw [MeasureTheory.eval_integral hintCoordinate.eval i]
    rw [← vec3ToL2Vec3_measurePreserving.integral_comp
      (MeasurableEquiv.toLp 2 Vec3).measurableEmbedding]
    change (∫ y : Vec3, regularisedPhysicalKernel ρ ε hε y *
        a (x - y) i) =
      regularisedScalarConvolution (regularisedPhysicalKernel ρ ε hε)
        (fun y => a y i) x
    rfl
  funext x
  ext i
  exact heq x i

/-- Each component of the mollified state is the scalar convolution of the
physical kernel with the corresponding input component, as in
`lem:reg-mollifier-bounds`. -/
theorem regUniformMollifiedInitial_component_convolution
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume) :
    ∀ x i, regUniformMollifiedInitial ρ ε hε a x i =
      MeasureTheory.convolution
        (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y))
        (fun y : Vec3 => a y i) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  have heq := regUniformMollifiedInitial_eq_regularisedProfileConvolution
    ρ ε hε ha
  intro x i
  have h := congrFun (congrFun heq x) i
  have hk : regularisedPhysicalKernel ρ ε hε =
      (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) := rfl
  simpa [regularisedProfileConvolution, regularisedScalarConvolution] using
    (congrArg (fun k : Vec3 → ℝ =>
      MeasureTheory.convolution k (fun y => a y i)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x) hk ▸ h)

/-- Every ordered spatial derivative of the mollified initial state in
`eq:reg-mollifier` remains square integrable; this is the initial Sobolev
input for the regularized evolution in `thm:regularised`. -/
theorem regUniformMollifiedInitial_coordinateDerivative_memLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
    (n : ℕ) (w : Fin n → Fin 3) (i : Fin 3) :
    MemLp
      (fun x : Vec3 =>
        (iteratedFDeriv ℝ n
          (fun z => regUniformMollifiedInitial ρ ε hε a z i) x)
          (fun j => CKN.basisVec (w j)))
      (2 : ℝ≥0∞) volume := by
  have hfield := regUniformMollifiedInitial_eq_regularisedProfileConvolution
    ρ ε hε ha.1
  have hcomponent :
      (fun x : Vec3 => regUniformMollifiedInitial ρ ε hε a x i) =
        regularisedScalarConvolution (regularisedPhysicalKernel ρ ε hε)
          (fun y => a y i) := by
    funext x
    have hvalue := congrFun hfield x
    change regUniformMollifiedInitial ρ ε hε a x i = _
    rw [hvalue]
    rfl
  have hderivativeField :
      (fun x : Vec3 =>
        (iteratedFDeriv ℝ n
          (fun z => regUniformMollifiedInitial ρ ε hε a z i) x)
          (regularisedCoordinateTuple n w)) =
        regularisedScalarConvolution
          (fun y => (iteratedFDeriv ℝ n
            (regularisedPhysicalKernel ρ ε hε) y)
              (regularisedCoordinateTuple n w)) (fun y => a y i) := by
    funext x
    rw [hcomponent]
    exact regularisedScalarConvolution_iterated n w
      (regularisedPhysicalKernel ρ ε hε)
      (regularisedPhysicalKernel_smooth ρ ε hε)
      (regularisedPhysicalKernel_compact ρ ε hε) (ha.1.eval i) x
  change MemLp (fun x : Vec3 =>
    (iteratedFDeriv ℝ n
      (fun z => regUniformMollifiedInitial ρ ε hε a z i) x)
      (regularisedCoordinateTuple n w)) (2 : ℝ≥0∞) volume
  rw [hderivativeField]
  refine regularisedScalarConvolution_memLp_of_compactSupport ρ ε hε ?_ ?_
    (ha.1.eval i)
  · have hiter : ContDiff ℝ 2
        (iteratedFDeriv ℝ n (regularisedPhysicalKernel ρ ε hε)) := by
      have hnat : ContDiff ℝ (2 + n) (regularisedPhysicalKernel ρ ε hε) :=
        (regularisedPhysicalKernel_smooth ρ ε hε).of_le (by simp)
      exact hnat.iteratedFDeriv_right' (m := 2) (i := n)
    exact (hiter.continuousLinearMap_comp (ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin n => Vec3) ℝ (regularisedCoordinateTuple n w))).continuous
  · have hiter : HasCompactSupport
        (iteratedFDeriv ℝ n (regularisedPhysicalKernel ρ ε hε)) :=
      (regularisedPhysicalKernel_compact ρ ε hε).iteratedFDeriv n
    apply HasCompactSupport.of_support_subset_isCompact hiter.isCompact
    intro y hy
    simp only [Function.mem_support] at hy
    by_contra hnot
    have hzero : iteratedFDeriv ℝ n (regularisedPhysicalKernel ρ ε hε) y = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := iteratedFDeriv ℝ n (regularisedPhysicalKernel ρ ε hε)) hnot
    exact hy (by simp [hzero])

/-- Convolution by the smooth compactly supported profile in
`eq:reg-mollifier` preserves the Leray space `J`. -/
theorem regMollifiedInitial_isInJ
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsInJ a) :
    CKN.IsInJ (regUniformMollifiedInitial ρ ε hε a) := by
  have hweak := regularisedProfileConvolution_isWeakDivFreeL2 ρ ε hε ha
  have hmem : MemLp (regUniformMollifiedInitial ρ ε hε a)
      (2 : ℝ≥0∞) volume := by
    rw [regUniformMollifiedInitial_eq_regularisedProfileConvolution ρ ε hε ha.1]
    exact hweak.1
  have heq := regUniformMollifiedInitial_eq_regularisedProfileConvolution
    ρ ε hε ha.1
  have houtWeak : CKN.IsWeakDivFreeL2 (regUniformMollifiedInitial ρ ε hε a) := by
    rw [heq]
    exact hweak
  exact CKN.weakDivFreeL2_isInJ ⟨hmem, houtWeak.2⟩

end CKN.Leray

end
