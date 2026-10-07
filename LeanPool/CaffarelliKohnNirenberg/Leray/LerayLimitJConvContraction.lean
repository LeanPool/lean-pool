/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropMollifier
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessFiniteRankCore
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpConvolution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# The `L³` contraction of the regularized transport velocity

The transport velocity J_ε u of `thm:regularised` is, on each time slice,
the convolution of the slice with the normalized dilate of the regularizing
profile, written in coordinates. Convolution with a nonnegative kernel of unit
mass is contractive in every finite Lebesgue norm, slice by slice; integrating
in time gives the space-time contraction used for the `L³` assertion of
`prop:leray-limit`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology Convolution
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The regularizing kernel in coordinates is a nonnegative, continuous,
compactly supported kernel of unit mass supported in the ball of radius ε. -/
theorem lerayLimit_regMollifierKernel_vec3_props
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    (∀ y : Vec3, 0 ≤ regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) ∧
    Continuous (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) ∧
    Integrable (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y))
      volume ∧
    (∫ y : Vec3, regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) = 1 ∧
    Function.support
      (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) ⊆
      Metric.ball (0 : Vec3) ε ∧
    HasCompactSupport
      (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) := by
  have htransport : MeasurePreserving
      (WithLp.toLp 2 : Vec3 → L2Vec3) volume volume :=
    vec3ToL2Vec3_measurePreserving
  have hcont : Continuous
      (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) :=
    have hk : Continuous (regMollifierKernel ρ ε hε) := by
      unfold regMollifierKernel
      exact continuous_const.mul
        (ρ.smooth.continuous.comp (continuous_const_smul _))
    hk.comp (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ))
  have hint : Integrable
      (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) volume := by
    have hkernel : MemLp (regMollifierKernel ρ ε hε) 1 volume :=
      memLp_one_iff_integrable.mpr (regMollifierKernel_integrable ρ ε hε)
    exact memLp_one_iff_integrable.mp
      (hkernel.comp_measurePreserving htransport)
  have hone : (∫ y : Vec3, regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) = 1 := by
    calc
      _ = ∫ x : L2Vec3, regMollifierKernel ρ ε hε x :=
        htransport.integral_comp (MeasurableEquiv.toLp 2 Vec3).measurableEmbedding _
      _ = 1 := regMollifierKernel_integral_eq_one ρ ε hε
  have hsupp : Function.support
      (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) ⊆
      Metric.ball (0 : Vec3) ε := by
    intro y hy
    have hρ : ρ.rho (ε⁻¹ • WithLp.toLp 2 y) ≠ 0 := by
      intro h
      apply hy
      simp only [regMollifierKernel, h, mul_zero]
    have hmem : ε⁻¹ • WithLp.toLp 2 y ∈ Metric.ball (0 : L2Vec3) 1 :=
      ρ.support_unit (subset_tsupport _ hρ)
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hε] at hmem
    have hlt : ‖WithLp.toLp 2 y‖ < ε := by
      have h := (inv_mul_lt_iff₀ hε).mp hmem
      linarith only [h]
    rw [mem_ball_zero_iff]
    have hle : ‖y‖ ≤ ‖WithLp.toLp 2 y‖ := by
      rw [← vec3EuclideanNorm_eq_l2]
      exact norm_le_vec3EuclideanNorm y
    exact lt_of_le_of_lt hle hlt
  refine ⟨fun y => regMollifierKernel_nonneg ρ ε hε _, hcont, hint, hone, hsupp, ?_⟩
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec3) ε) ?_
  intro y hy
  by_contra hne
  exact hy (Metric.ball_subset_closedBall (hsupp hne))

/-- On each time slice, the regularized transport velocity is the coordinate
convolution of the slice with the regularizing kernel. -/
theorem lerayLimit_regUniformMollifiedVelocity_eq_convolution
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (v : ParabolicPoint → Vec3) (x : Vec3) (t : ℝ) :
    regUniformMollifiedVelocity ρ ε hε v (x, t) =
      ((fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y : Vec3 => v (y, t))) x := by
  let E := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  let g : L2Vec3 → Vec3 := fun y =>
    E (regMollifierKernel ρ ε hε y • regUniformVelocitySlice v t
      (WithLp.toLp 2 x - y))
  have h1 : regUniformMollifiedVelocity ρ ε hε v (x, t) =
      E (∫ y : L2Vec3, regMollifierKernel ρ ε hε y • regUniformVelocitySlice v t
        (WithLp.toLp 2 x - y)) := by
    change WithLp.ofLp (regMollifyVector ρ ε hε
      (regUniformVelocitySlice v t) (WithLp.toLp 2 x)) = _
    rw [lerayHopfLimit_regMollifyVector_eq_convolution, convolution_def]
    rfl
  rw [h1, ← E.integral_comp_comm, convolution_def]
  change (∫ y : L2Vec3, g y) = _
  rw [← vec3ToL2Vec3_measurePreserving.integral_comp
    (MeasurableEquiv.toLp 2 Vec3).measurableEmbedding g]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [g, E, regUniformVelocitySlice, PiLp.coe_continuousLinearEquiv]

/-- Convolution with the coordinate regularizing kernel is dominated
pointwise by the convolution of the norm. -/
theorem lerayLimit_regMollifierKernel_convolution_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (f : Vec3 → Vec3) (x : Vec3) :
    ‖((fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x‖ ≤
      ((fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => ‖f y‖)) x := by
  have hnonneg := (lerayLimit_regMollifierKernel_vec3_props ρ ε hε).1
  rw [convolution_def, convolution_def]
  calc
    _ ≤ ∫ y : Vec3, ‖ContinuousLinearMap.lsmul ℝ ℝ
          (regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) (f (x - y))‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (hnonneg y), smul_eq_mul]

/-- On each time slice, the regularized transport velocity has finite-exponent
Lebesgue norm at most that of the slice itself. -/
theorem lerayLimit_regUniformMollifiedVelocity_slice_eLpNorm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : AEStronglyMeasurable (fun x : Vec3 => u (x, t)) volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ⊤) :
    eLpNorm (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t))
      p volume ≤ eLpNorm (fun x : Vec3 => u (x, t)) p volume := by
  obtain ⟨hκ0, hκc, hκi, hκ1, -, -⟩ :=
    lerayLimit_regMollifierKernel_vec3_props ρ ε hε
  let κ : Vec3 → ℝ := fun y => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)
  have heq : (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t)) =
      κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y : Vec3 => u (y, t)) := by
    funext x
    exact lerayLimit_regUniformMollifiedVelocity_eq_convolution ρ ε hε u x t
  rw [heq]
  have hmeas : AEStronglyMeasurable
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y : Vec3 => u (y, t)))
      volume :=
    hκc.aestronglyMeasurable.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hu
  calc
    _ ≤ eLpNorm (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (fun y : Vec3 => ‖u (y, t)‖)) p volume :=
      eLpNorm_mono_real hmeas (fun x =>
        lerayLimit_regMollifierKernel_convolution_norm_le ρ ε hε _ x)
    _ ≤ eLpNorm (fun y : Vec3 => ‖u (y, t)‖) p volume :=
      CKN.young_convolution_nonneg_integral_one_of_aemeasurable hp hpTop
        hκ0 hκi hκ1 hκc.measurable hu.norm.aemeasurable
    _ = eLpNorm (fun x : Vec3 => u (x, t)) p volume := eLpNorm_norm _ hu

/-- The regularized transport velocity of a measurable space-time field is
strongly measurable. -/
theorem lerayLimit_regUniformMollifiedVelocity_stronglyMeasurable
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {v : ParabolicPoint → Vec3} (hv : Measurable v) :
    StronglyMeasurable (regUniformMollifiedVelocity ρ ε hε v) := by
  obtain ⟨-, hκc, -, -, -, -⟩ := lerayLimit_regMollifierKernel_vec3_props ρ ε hε
  let κ : Vec3 → ℝ := fun y => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)
  have hfun : regUniformMollifiedVelocity ρ ε hε v =
      fun z : ParabolicPoint => ∫ y : Vec3,
        κ y • v (((z.1 - y, z.2) : Vec3 × ℝ) : ParabolicPoint) := by
    funext z
    rcases z with ⟨x, t⟩
    rw [lerayLimit_regUniformMollifiedVelocity_eq_convolution, convolution_def]
    rfl
  rw [hfun]
  apply StronglyMeasurable.integral_prod_right'
    (f := fun q : ParabolicPoint × Vec3 =>
      κ q.2 • v (((q.1.1 - q.2, q.1.2) : Vec3 × ℝ) : ParabolicPoint))
  have hmap : Measurable (fun q : ParabolicPoint × Vec3 =>
      (((q.1.1 - q.2, q.1.2) : Vec3 × ℝ) : ParabolicPoint)) := by
    have h1 : Measurable (fun q : ParabolicPoint × Vec3 => (q.1 : Vec3 × ℝ)) :=
      measurable_fst
    exact (h1.fst.sub measurable_snd).prodMk h1.snd
  exact ((hκc.measurable.comp measurable_snd).smul
    (hv.comp hmap)).stronglyMeasurable

/-- Integrating the per-time contraction over a time slab gives the
space-time `L³` contraction of the regularized transport velocity. -/
theorem lerayLimit_regUniformMollifiedVelocity_spaceTime_eLpNorm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {v : ParabolicPoint → Vec3} (hv : Measurable v) (T : ℝ) :
    eLpNorm (regUniformMollifiedVelocity ρ ε hε v) 3
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ≤
      eLpNorm v 3
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  have hJ := lerayLimit_regUniformMollifiedVelocity_stronglyMeasurable ρ ε hε hv
  have h3 : (3 : ℝ≥0∞).toReal = 3 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hJ.aestronglyMeasurable.restrict,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hv.aestronglyMeasurable.restrict, h3]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  have hJm : Measurable (fun z : ParabolicPoint =>
      ‖regUniformMollifiedVelocity ρ ε hε v z‖ₑ ^ (3 : ℝ)) :=
    hJ.measurable.enorm.pow_const _
  have hvm : Measurable (fun z : ParabolicPoint => ‖v z‖ₑ ^ (3 : ℝ)) :=
    hv.enorm.pow_const _
  change (∫⁻ z in (Set.univ : Set Vec3) ×ˢ Ioo 0 T,
      ‖regUniformMollifiedVelocity ρ ε hε v z‖ₑ ^ (3 : ℝ)
        ∂(volume : Measure ParabolicPoint)) ≤
    ∫⁻ z in (Set.univ : Set Vec3) ×ˢ Ioo 0 T, ‖v z‖ₑ ^ (3 : ℝ)
        ∂(volume : Measure ParabolicPoint)
  rw [lintegral_parabolic_rectangle_eq_iterated _ hJm,
    lintegral_parabolic_rectangle_eq_iterated _ hvm]
  apply lintegral_mono
  intro t
  simp only [Measure.restrict_univ]
  have hslice : Measurable (fun x : Vec3 => v (x, t)) :=
    hv.comp (measurable_prodMk_right (m := (inferInstance : MeasurableSpace Vec3)))
  have hJslice : Measurable
      (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε v (x, t)) :=
    hJ.measurable.comp
      (measurable_prodMk_right (m := (inferInstance : MeasurableSpace Vec3)))
  have hle := lerayLimit_regUniformMollifiedVelocity_slice_eLpNorm_le ρ ε hε v t
    hslice.aestronglyMeasurable (p := 3) (by norm_num) (by norm_num)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hJslice.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hslice.aestronglyMeasurable, h3] at hle
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 1 / 3)).mp hle

end CKN.Leray

end
