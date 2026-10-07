/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergySource

/-!
# Bounds for the source of the mollified velocity

The source of the mollified forced regularized velocity is jointly
measurable, and on almost every time slice it is bounded uniformly in space by
the `L²` norms of the transport-minus-viscous tensor, the quadratic pressure
and the force, which are integrable in time. These bounds justify the
exchanges of integrals in the local energy inequality
`eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Convolution

noncomputable section

namespace CKN.Leray

/-- The integral of a field against a translated reflected kernel is a
convolution. -/
theorem integral_mul_reflect_eq_convolution (g κ : Vec3 → ℝ) (x : Vec3) :
    ∫ y, g y * κ (x - y) = (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  rw [convolution_def]
  rw [← integral_sub_left_eq_self (fun y => g y * κ (x - y)) volume x]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only [sub_sub_cancel, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  ring

/-- The `L²` pairing of a field with a translated reflected kernel. -/
theorem abs_integral_mul_reflect_le {g κ : Vec3 → ℝ} (hg : MemLp g 2 volume)
    (hκ : MemLp κ 2 volume) (x : Vec3) :
    |∫ y, g y * κ (x - y)| ≤ (eLpNorm κ 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  rw [integral_mul_reflect_eq_convolution, ← Real.norm_eq_abs, ← ENNReal.toReal_mul]
  exact norm_convolution_le_of_memLp_two hκ hg x

/-- The time integral of the slice `L²` norms of a field that is square
integrable on a bounded slab. -/
theorem integrableOn_eLpNorm_slice {X : Vec3 × ℝ → ℝ} (hX : StronglyMeasurable X) {T : ℝ}
    (h2 : MemLp X 2 ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T)))) :
    IntegrableOn (fun t => (eLpNorm (fun x => X (x, t)) 2 volume).toReal) (Ioo 0 T) := by
  have hlin := lintegral_eLpNorm_real_slice_sq hX (μt := (volume : Measure ℝ).restrict (Ioo 0 T))
  have hm : Measurable fun t => eLpNorm (fun x => X (x, t)) 2 volume :=
    measurable_eLpNorm_slice hX (by norm_num) (by norm_num) volume
  have hfin : ∫⁻ t in Ioo 0 T, eLpNorm (fun x => X (x, t)) 2 volume ^ (2 : ℝ) ≠ ⊤ := by
    rw [hlin]
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h2.eLpNorm_ne_top).ne
  have hsq : IntegrableOn (fun t => (eLpNorm (fun x => X (x, t)) 2 volume ^ (2 : ℝ)).toReal)
      (Ioo 0 T) :=
    integrable_toReal_of_lintegral_ne_top (hm.pow_const _).aemeasurable hfin
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 T) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  refine Integrable.mono' ((hone.add hsq).div_const 2) hm.ennreal_toReal.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  simp only [Pi.add_apply]
  rw [← ENNReal.toReal_rpow, Real.rpow_two]
  nlinarith only [sq_nonneg ((eLpNorm (fun x => X (x, t)) 2 volume).toReal - 1)]

/-- The vector version of `integrableOn_eLpNorm_slice`. -/
theorem integrableOn_eLpNorm_vector_slice {X : Vec3 × ℝ → Vec3} (hX : StronglyMeasurable X)
    {T : ℝ}
    (h2 : MemLp X 2 ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T)))) :
    IntegrableOn (fun t => (eLpNorm (fun x => X (x, t)) 2 volume).toReal) (Ioo 0 T) := by
  have hlin := lintegral_eLpNorm_slice_sq_eq hX (μt := (volume : Measure ℝ).restrict (Ioo 0 T))
  have hm : Measurable fun t => eLpNorm (fun x => X (x, t)) 2 volume :=
    measurable_eLpNorm_two_slice hX
  have hfin : ∫⁻ t in Ioo 0 T, eLpNorm (fun x => X (x, t)) 2 volume ^ (2 : ℝ) ≠ ⊤ := by
    rw [hlin]
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h2.eLpNorm_ne_top).ne
  have hsq : IntegrableOn (fun t => (eLpNorm (fun x => X (x, t)) 2 volume ^ (2 : ℝ)).toReal)
      (Ioo 0 T) :=
    integrable_toReal_of_lintegral_ne_top (hm.pow_const _).aemeasurable hfin
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 T) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  refine Integrable.mono' ((hone.add hsq).div_const 2) hm.ennreal_toReal.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  simp only [Pi.add_apply]
  rw [← ENNReal.toReal_rpow, Real.rpow_two]
  nlinarith only [sq_nonneg ((eLpNorm (fun x => X (x, t)) 2 volume).toReal - 1)]

theorem memLp_reflect {κ : Vec3 → ℝ} (hκ : Continuous κ) (hκc : HasCompactSupport κ) (x : Vec3) :
    MemLp (fun y => κ (x - y)) 2 volume :=
  (hκ.comp (continuous_const.sub continuous_id)).memLp_of_hasCompactSupport
    (hκc.comp_homeomorph (Homeomorph.subLeft x))

theorem integrable_mul_reflect {g κ : Vec3 → ℝ} (hg : MemLp g 2 volume) (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) (x : Vec3) : Integrable fun y => g y * κ (x - y) :=
  hg.integrable_mul (memLp_reflect hκ hκc x)

section SourceBound

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f)

/-- The uniform bound of the source on one time slice. -/
@[expose]
def leSourceBound (η : Vec3 → ℝ) (k : Fin 3) (t : ℝ) : ℝ :=
  (∑ j : Fin 3, (eLpNorm (CKN.spatialDeriv η j) 2 volume).toReal *
      (eLpNorm (fun y => leTensor ρ ε hε ha hf j k (y, t)) 2 volume).toReal) +
    (eLpNorm (CKN.spatialDeriv η k) 2 volume).toReal *
      (eLpNorm (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) 2
        volume).toReal +
    (eLpNorm η 2 volume).toReal *
      (5 * (eLpNorm (fun y => forcedForceMod f hf (y, t)) 2 volume).toReal)

/-- The force-pressure pairing with a reflected kernel is the pairing of its
gradient with the undifferentiated kernel. -/
theorem integral_forcePressure_mul_reflect {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) {t : ℝ} {hft : MemLp (fun x => f (x, t)) 2 volume}
    (hpf : CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => forcePressure f hf (x, t))
      (forcePressureGradientFunction (fun x => f (x, t)) hft)) (x : Vec3) (k : Fin 3) :
    ∫ y, forcePressure f hf (y, t) * CKN.spatialDeriv η k (x - y) =
      ∫ y, forcePressureGradientFunction (fun x => f (x, t)) hft y k * η (x - y) := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y => η (x - y)) := hη.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun y => η (x - y)) := hηc.comp_homeomorph (Homeomorph.subLeft x)
  have h := hpf k (fun y => η (x - y)) hψ hψc (subset_univ _)
  have hfd : ∀ y, fderiv ℝ (fun y => η (x - y)) y (CKN.basisVec k) =
      -CKN.spatialDeriv η k (x - y) := by
    intro y
    have hd : HasFDerivAt (fun y => η (x - y))
        ((fderiv ℝ η (x - y)).comp (-(ContinuousLinearMap.id ℝ Vec3))) y :=
      ((hη.differentiable (by simp)) (x - y)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).const_sub x)
    rw [hd.fderiv]
    simp [CKN.spatialDeriv]
  simp only [Measure.restrict_univ, hfd, mul_neg, integral_neg, neg_inj] at h
  exact h

theorem eLpNorm_forcePressureGradient_le {t : ℝ} (hft : MemLp (fun x => f (x, t)) 2 volume)
    (k : Fin 3) :
    (eLpNorm (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k) 2 volume).toReal
      ≤ 4 * (eLpNorm (fun x => f (x, t)) 2 volume).toReal := by
  set W := realVectorL2OfCoordinateFunction (fun x => f (x, t)) hft with hW
  have hG2 := forcePressureGradientFunction_memLp (fun x => f (x, t)) hft
  have h1 : eLpNorm (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k) 2 volume
      ≤ eLpNorm (forcePressureGradientFunction (fun x => f (x, t)) hft) 2 volume :=
    eLpNorm_mono (hG2.eval k).aestronglyMeasurable fun y => norm_le_pi_norm _ k
  have h2 : eLpNorm (forcePressureGradientFunction (fun x => f (x, t)) hft) 2 volume ≤
      ENNReal.ofReal ‖forcePressureGradientL2 W‖ :=
    eLpNorm_realVectorL2Representative_le _
  have h3 : ‖forcePressureGradientL2 W‖ ≤ 2 * ‖W‖ := forcePressureGradientL2_norm_le W
  have h4 : ‖W‖ ≤ 2 * (eLpNorm (fun x => f (x, t)) 2 volume).toReal := by
    rw [Lp.norm_def]
    have h := eLpNorm_realVectorL2OfCoordinateFunction_le (fun x => f (x, t)) hft
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hft.eLpNorm_ne_top) h
    rwa [ENNReal.toReal_mul, show (2 : ℝ≥0∞).toReal = 2 by norm_num] at h'
  have hfin : ENNReal.ofReal ‖forcePressureGradientL2 W‖ ≠ ⊤ := ENNReal.ofReal_ne_top
  have h5 := ENNReal.toReal_mono hfin (h1.trans h2)
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at h5
  linarith only [h5, h3, h4]

/-- The uniform bound of the source on a good time slice. -/
theorem abs_leSF_le {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {t : ℝ} (k : Fin 3)
    (hA : ∀ j, MemLp (fun y => leTensor ρ ε hε ha hf j k (y, t)) 2 volume)
    (hF2 : MemLp (fun y => forcedForceMod f hf (y, t)) 2 volume)
    (hFf : (fun y => forcedForceMod f hf (y, t)) =ᵐ[volume] fun y => f (y, t))
    (hft : MemLp (fun x => f (x, t)) 2 volume)
    (hpf : CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => forcePressure f hf (x, t))
      (forcePressureGradientFunction (fun x => f (x, t)) hft))
    (hpfl : LocallyIntegrable (fun x => forcePressure f hf (x, t)) volume) (x : Vec3) :
    |leSF ρ ε hε ha hf η x t k| ≤ leSourceBound ρ ε hε ha hf η k t := by
  have hq2 : MemLp (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) 2
      volume :=
    (memLp_rieszPressureSliceRepresentative_two _).ae_eq
      (forcedQuadPressure_slice ρ ε hε (forcedRegCurve ρ ε hε ha hf) t).symm
  have hdη : ∀ j, Continuous (CKN.spatialDeriv η j) := fun j =>
    (CKN.contDiff_spatialDeriv_smooth hη j).continuous
  have hdηc : ∀ j, HasCompactSupport (CKN.spatialDeriv η j) := fun j =>
    CKN.hasCompactSupport_spatialDeriv hηc j
  have hdη2 : ∀ j, MemLp (CKN.spatialDeriv η j) 2 volume := fun j =>
    (hdη j).memLp_of_hasCompactSupport (hdηc j)
  have hη2 : MemLp η 2 volume := hη.continuous.memLp_of_hasCompactSupport hηc
  have iA : ∀ j, Integrable fun y =>
      leTensor ρ ε hε ha hf j k (y, t) * CKN.spatialDeriv η j (x - y) := fun j =>
    integrable_mul_reflect (hA j) (hdη j) (hdηc j) x
  have iq : Integrable fun y =>
      forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t) *
        CKN.spatialDeriv η k (x - y) :=
    integrable_mul_reflect hq2 (hdη k) (hdηc k) x
  have ip : Integrable fun y => forcePressure f hf (y, t) * CKN.spatialDeriv η k (x - y) := by
    have h := hpfl.integrable_smul_right_of_hasCompactSupport
      ((hdη k).comp (continuous_const.sub continuous_id))
      ((hdηc k).comp_homeomorph (Homeomorph.subLeft x))
    exact h
  have iF : Integrable fun y => forcedForceMod f hf (y, t) k * η (x - y) :=
    integrable_mul_reflect (hF2.eval k) hη.continuous hηc x
  have hsplit : leSF ρ ε hε ha hf η x t k =
      (∑ j : Fin 3, ∫ y, leTensor ρ ε hε ha hf j k (y, t) * CKN.spatialDeriv η j (x - y)) +
        ((∫ y, forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t) *
          CKN.spatialDeriv η k (x - y)) +
          ∫ y, forcePressure f hf (y, t) * CKN.spatialDeriv η k (x - y)) -
        ∫ y, forcedForceMod f hf (y, t) k * η (x - y) := by
    unfold leSF leKernelF lePressure
    have e1 : ∀ y, (∑ j : Fin 3, leTensor ρ ε hε ha hf j k (y, t) *
        CKN.spatialDeriv η j (x - (y, t).1) +
        (forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t) +
          forcePressure f hf (y, t)) * CKN.spatialDeriv η k (x - (y, t).1) -
        forcedForceMod f hf (y, t) k * η (x - (y, t).1)) =
        (∑ j : Fin 3, leTensor ρ ε hε ha hf j k (y, t) * CKN.spatialDeriv η j (x - y)) +
          (forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t) *
            CKN.spatialDeriv η k (x - y) +
            forcePressure f hf (y, t) * CKN.spatialDeriv η k (x - y)) -
          forcedForceMod f hf (y, t) k * η (x - y) := fun y => by
      simp only
      ring
    simp_rw [e1]
    have jA : Integrable fun y => ∑ j : Fin 3, leTensor ρ ε hε ha hf j k (y, t) *
        CKN.spatialDeriv η j (x - y) := integrable_finsetSum _ fun j _ => iA j
    have jqp : Integrable fun y =>
        forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t) *
          CKN.spatialDeriv η k (x - y) +
        forcePressure f hf (y, t) * CKN.spatialDeriv η k (x - y) := iq.add ip
    have jAqp : Integrable fun y => (∑ j : Fin 3, leTensor ρ ε hε ha hf j k (y, t) *
        CKN.spatialDeriv η j (x - y)) +
        (forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t) *
          CKN.spatialDeriv η k (x - y) +
        forcePressure f hf (y, t) * CKN.spatialDeriv η k (x - y)) := jA.add jqp
    rw [integral_sub jAqp iF, integral_add jA jqp, integral_add iq ip,
      integral_finsetSum _ fun j _ => iA j]
  have bA : ∀ j, |∫ y, leTensor ρ ε hε ha hf j k (y, t) * CKN.spatialDeriv η j (x - y)| ≤
      (eLpNorm (CKN.spatialDeriv η j) 2 volume).toReal *
        (eLpNorm (fun y => leTensor ρ ε hε ha hf j k (y, t)) 2 volume).toReal := fun j =>
    abs_integral_mul_reflect_le (hA j) (hdη2 j) x
  have bq := abs_integral_mul_reflect_le hq2 (hdη2 k) x
  have bp : |∫ y, forcePressure f hf (y, t) * CKN.spatialDeriv η k (x - y)| ≤
      (eLpNorm η 2 volume).toReal * (4 * (eLpNorm (fun y => forcedForceMod f hf (y, t)) 2
        volume).toReal) := by
    rw [integral_forcePressure_mul_reflect hf hη hηc hpf x k]
    have h1 := abs_integral_mul_reflect_le
      ((forcePressureGradientFunction_memLp (fun x => f (x, t)) hft).eval k) hη2 x
    have h2 := eLpNorm_forcePressureGradient_le hft k
    rw [eLpNorm_congr_ae hFf.symm] at h2
    refine h1.trans (mul_le_mul_of_nonneg_left h2 ENNReal.toReal_nonneg)
  have bF : |∫ y, forcedForceMod f hf (y, t) k * η (x - y)| ≤
      (eLpNorm η 2 volume).toReal *
        (eLpNorm (fun y => forcedForceMod f hf (y, t)) 2 volume).toReal := by
    refine (abs_integral_mul_reflect_le (hF2.eval k) hη2 x).trans ?_
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hF2.eLpNorm_ne_top ?_)
      ENNReal.toReal_nonneg
    exact eLpNorm_mono (hF2.eval k).aestronglyMeasurable fun y => norm_le_pi_norm _ k
  rw [hsplit]
  unfold leSourceBound
  have hsumb : |∑ j : Fin 3, ∫ y, leTensor ρ ε hε ha hf j k (y, t) *
      CKN.spatialDeriv η j (x - y)| ≤ ∑ j : Fin 3,
        (eLpNorm (CKN.spatialDeriv η j) 2 volume).toReal *
          (eLpNorm (fun y => leTensor ρ ε hε ha hf j k (y, t)) 2 volume).toReal :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => bA j)
  have hη0 : 0 ≤ (eLpNorm η 2 volume).toReal := ENNReal.toReal_nonneg
  have hF0 : 0 ≤ (eLpNorm (fun y => forcedForceMod f hf (y, t)) 2 volume).toReal :=
    ENNReal.toReal_nonneg
  set SA := ∑ j : Fin 3, ∫ y, leTensor ρ ε hε ha hf j k (y, t) * CKN.spatialDeriv η j (x - y)
  set SQ := ∫ y, forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t) *
    CKN.spatialDeriv η k (x - y)
  set SP := ∫ y, forcePressure f hf (y, t) * CKN.spatialDeriv η k (x - y)
  set SF := ∫ y, forcedForceMod f hf (y, t) k * η (x - y)
  have t1 := abs_sub (SA + (SQ + SP)) SF
  have t2 := abs_add_le SA (SQ + SP)
  have t3 := abs_add_le SQ SP
  nlinarith only [hsumb, bq, bp, bF, hη0, hF0, t1, t2, t3]

theorem stronglyMeasurable_leTensor (j k : Fin 3) :
    StronglyMeasurable (leTensor ρ ε hε ha hf j k) := by
  have h1 := measurable_forcedRegTransport ρ ε hε ha hf j
  have h2 : Measurable fun z : Vec3 × ℝ => forcedRegRep ρ ε hε ha hf z k :=
    (measurable_pi_apply k).comp (forcedRegRep_stronglyMeasurable ρ ε hε ha hf).measurable
  have h3 := (forcedMollifiedGrad_stronglyMeasurable (forcedRegRep_stronglyMeasurable ρ ε hε ha hf)
    (forcedRegRep_locallyIntegrable ρ ε hε ha hf) k j).measurable
  exact ((h1.mul h2).sub h3).stronglyMeasurable

theorem memLp_leTensor_prod (j k : Fin 3) {T : ℝ} (hT : 0 ≤ T) :
    MemLp (leTensor ρ ε hε ha hf j k)
      2 ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  obtain ⟨M, hM0, hM⟩ := forcedRegTransport_bound ρ ε hε ha hf T
  have hu2 := (memLp_forcedRegRep_prod ρ ε hε ha hf T).eval k
  have hJu : MemLp (fun z => regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) z j *
      forcedRegRep ρ ε hε ha hf z k) 2
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
    refine hu2.of_le_mul (c := M) ?_ ?_
    · exact ((measurable_forcedRegTransport ρ ε hε ha hf j).mul ((measurable_pi_apply k).comp
        (forcedRegRep_stronglyMeasurable ρ ε hε ha hf).measurable)).aestronglyMeasurable
    · filter_upwards [ae_mem_Ioo_prod T] with z hz
      rw [norm_mul]
      have h := hM z ⟨hz.1.le, hz.2.le⟩ j
      rw [← Real.norm_eq_abs] at h
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  exact hJu.sub (((memLp_forcedRegGrad_prod ρ ε hε ha hf T hT).eval k).eval j)

theorem integrableOn_leSourceBound {η : Vec3 → ℝ} (k : Fin 3) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (leSourceBound ρ ε hε ha hf η k) (Ioo 0 T) := by
  have hA : ∀ j, IntegrableOn (fun t =>
      (eLpNorm (fun y => leTensor ρ ε hε ha hf j k (y, t)) 2 volume).toReal) (Ioo 0 T) :=
    fun j => integrableOn_eLpNorm_slice (stronglyMeasurable_leTensor ρ ε hε ha hf j k)
      (memLp_leTensor_prod ρ ε hε ha hf j k hT.le)
  have hq : IntegrableOn (fun t => (eLpNorm (fun y =>
      forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) 2 volume).toReal)
      (Ioo 0 T) :=
    integrableOn_eLpNorm_slice
      (forcedQuadPressure_stronglyMeasurable ρ ε hε (continuous_forcedRegCurve ρ ε hε ha hf))
      (memLp_forcedQuadPressure_slab ρ ε hε (continuous_forcedRegCurve ρ ε hε ha hf) T)
  have hF : IntegrableOn (fun t =>
      (eLpNorm (fun y => forcedForceMod f hf (y, t)) 2 volume).toReal) (Ioo 0 T) :=
    integrableOn_eLpNorm_vector_slice (forcedForceMod_stronglyMeasurable f hf)
      (memLp_forcedForceMod_prod f hf hT)
  unfold leSourceBound
  exact ((integrable_finsetSum _ fun j _ => (hA j).const_mul _).add (hq.const_mul _)).add
    ((hF.const_mul 5).const_mul _)

end SourceBound

end CKN.Leray

end
