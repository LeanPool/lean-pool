/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.SpaceTimeMollifier
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreMixed

/-!
# Backward space-time mollification

The regularity bootstrap of `thm:vorticity-regularity` of the Escauriaza–Seregin–Šverák manuscript works on cylinders whose top is the
terminal time of the hypotheses. A space-time mollification evaluated `5ε` earlier in time only
uses values of the field strictly below the top, so smooth approximations are available up to
the top face. This file records the derivative formulas for kernels, the pairing identities with
the reflected kernel, and the resulting pointwise form of constant-coefficient weak identities.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Convolution Pointwise
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

local instance vorticityBackVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure Vec3) (volume : Measure ℝ)

/-- A directional derivative of a smooth compactly supported kernel is again smooth. -/
theorem vorticityKernelDeriv_contDiff {k : Vec3 × ℝ → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (v : Vec3 × ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => (fderiv ℝ k t) v) := by
  exact (hk.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

/-- A directional derivative of a compactly supported kernel is compactly supported. -/
theorem vorticityKernelDeriv_hasCompactSupport {k : Vec3 × ℝ → ℝ}
    (hkc : HasCompactSupport k) (v : Vec3 × ℝ) :
    HasCompactSupport (fun t => (fderiv ℝ k t) v) :=
  hkc.fderiv_apply (𝕜 := ℝ) v

/-- A scalar convolution is the integral of the reflected kernel against the function. -/
theorem vorticityConvolution_eq_integral (k g : Vec3 × ℝ → ℝ) (c : Vec3 × ℝ) :
    (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) c =
      ∫ y, k (c - y) * g y ∂(volume : Measure (Vec3 × ℝ)) := by
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have h := integral_sub_left_eq_self
    (fun y : Vec3 × ℝ => k (c - y) * g y) (volume : Measure (Vec3 × ℝ)) c
  simp only [sub_sub_cancel] at h
  exact h

/-- The directional derivative of a convolution with a smooth compactly supported kernel is the
convolution with the directional derivative of the kernel. -/
theorem vorticityKernel_convolution_fderiv {k f : Vec3 × ℝ → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkc : HasCompactSupport k)
    (hf : LocallyIntegrable f (volume : Measure (Vec3 × ℝ))) (x v : Vec3 × ℝ) :
    (fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x) v =
      ((fun t => (fderiv ℝ k t) v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x := by
  have hfd := hkc.hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (hk.of_le (by simp)) hf x
  rw [hfd.fderiv]
  have hderivCont : Continuous (fun t : Vec3 × ℝ => fderiv ℝ k t) :=
    hk.continuous_fderiv (by simp)
  have hconv : ConvolutionExists (fderiv ℝ k) f
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec3 × ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
    HasCompactSupport.convolutionExists_left
      (𝕜 := ℝ) (G := Vec3 × ℝ) (E := (Vec3 × ℝ) →L[ℝ] ℝ)
      (E' := ℝ) (F := (Vec3 × ℝ) →L[ℝ] ℝ)
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec3 × ℝ))
      (hkc.fderiv (𝕜 := ℝ)) hderivCont hf
  simp only [convolution_def]
  rw [ContinuousLinearMap.integral_apply (hconv x) v]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul]

/-- The time shift `(0, 5ε)` of the backward mollifier. -/
@[expose]
def vorticityBackShift (ε : ℝ) : Vec3 × ℝ := (0, 5 * ε)

/-- Backward mollification on `W`: the zero extension of `f` outside `W`, convolved with the
space-time kernel of radius `ε` and evaluated at the earlier time `t - 5ε`. -/
@[expose]
def vorticityBackMollify (W : Set (Vec3 × ℝ)) (f : Vec3 × ℝ → ℝ) (ε : ℝ) (hε : 0 < ε) :
    Vec3 × ℝ → ℝ :=
  fun z => spaceTimeMollify (W.indicator f) ε hε (z - vorticityBackShift ε)

/-- The reflected kernel centred at the shifted point: pairing a field with it evaluates the
backward mollification at `z`. -/
@[expose]
def vorticityBackTest (ε : ℝ) (hε : 0 < ε) (z : Vec3 × ℝ) : Vec3 × ℝ → ℝ :=
  fun y => spaceTimeMollifier ε hε (z - vorticityBackShift ε - y)

/-- Backward mollification of an integrable zero extension is smooth. -/
theorem vorticityBackMollify_contDiff {W : Set (Vec3 × ℝ)} {f : Vec3 × ℝ → ℝ}
    {ε : ℝ} (hε : 0 < ε)
    (hf : LocallyIntegrable (W.indicator f) (volume : Measure (Vec3 × ℝ))) :
    ContDiff ℝ (⊤ : ℕ∞) (vorticityBackMollify W f ε hε) :=
  (spaceTimeMollify_contDiff hε hf).comp (contDiff_id.sub contDiff_const)

/-- The first derivative of a backward mollification is the backward convolution with the
derivative of the kernel. -/
theorem vorticityBackMollify_fderiv {W : Set (Vec3 × ℝ)} {f : Vec3 × ℝ → ℝ}
    {ε : ℝ} (hε : 0 < ε)
    (hf : LocallyIntegrable (W.indicator f) (volume : Measure (Vec3 × ℝ)))
    (z v : Vec3 × ℝ) :
    (fderiv ℝ (vorticityBackMollify W f ε hε) z) v =
      ((fun t => (fderiv ℝ (spaceTimeMollifier ε hε) t) v)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] W.indicator f)
        (z - vorticityBackShift ε) := by
  have hcomp : vorticityBackMollify W f ε hε =
      fun y => spaceTimeMollify (W.indicator f) ε hε (y - vorticityBackShift ε) := rfl
  rw [hcomp, fderiv_comp_sub]
  exact vorticityKernel_convolution_fderiv (spaceTimeMollifier_contDiff hε)
    (spaceTimeMollifier_hasCompactSupport hε) hf _ v

/-- The second derivative of a backward mollification is the backward convolution with the
second derivative of the kernel. -/
theorem vorticityBackMollify_fderiv_fderiv {W : Set (Vec3 × ℝ)} {f : Vec3 × ℝ → ℝ}
    {ε : ℝ} (hε : 0 < ε)
    (hf : LocallyIntegrable (W.indicator f) (volume : Measure (Vec3 × ℝ)))
    (z v w : Vec3 × ℝ) :
    (fderiv ℝ (fun y => (fderiv ℝ (vorticityBackMollify W f ε hε) y) v) z) w =
      ((fun t => (fderiv ℝ (fun t' => (fderiv ℝ (spaceTimeMollifier ε hε) t') v) t) w)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] W.indicator f)
        (z - vorticityBackShift ε) := by
  have hfirst : (fun y => (fderiv ℝ (vorticityBackMollify W f ε hε) y) v) =
      fun y => ((fun t => (fderiv ℝ (spaceTimeMollifier ε hε) t) v)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] W.indicator f)
        (y - vorticityBackShift ε) := by
    funext y
    exact vorticityBackMollify_fderiv hε hf y v
  rw [hfirst, fderiv_comp_sub]
  exact vorticityKernel_convolution_fderiv
    (vorticityKernelDeriv_contDiff (spaceTimeMollifier_contDiff hε) v)
    (vorticityKernelDeriv_hasCompactSupport (spaceTimeMollifier_hasCompactSupport hε) v)
    hf _ w

/-- The backward test is smooth. -/
theorem vorticityBackTest_contDiff {ε : ℝ} (hε : 0 < ε) (z : Vec3 × ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (vorticityBackTest ε hε z) :=
  (spaceTimeMollifier_contDiff hε).comp (contDiff_const.sub contDiff_id)

/-- The backward test is supported in the closed ball of radius `ε` about the shifted point. -/
theorem vorticityBackTest_tsupport_subset {ε : ℝ} (hε : 0 < ε) (z : Vec3 × ℝ) :
    tsupport (vorticityBackTest ε hε z) ⊆
      Metric.closedBall (z - vorticityBackShift ε) ε := by
  have hsupp : Function.support (vorticityBackTest ε hε z) ⊆
      Metric.ball (z - vorticityBackShift ε) ε := by
    intro y hy
    have hy' : z - vorticityBackShift ε - y ∈
        Function.support (spaceTimeMollifier ε hε) := hy
    rw [spaceTimeMollifier_support hε, Metric.mem_ball, dist_zero_right] at hy'
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    exact hy'
  exact (closure_mono hsupp).trans Metric.closure_ball_subset_closedBall

/-- The backward test has compact support. -/
theorem vorticityBackTest_hasCompactSupport {ε : ℝ} (hε : 0 < ε) (z : Vec3 × ℝ) :
    HasCompactSupport (vorticityBackTest ε hε z) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (z - vorticityBackShift ε) ε)
    ((subset_tsupport _).trans (vorticityBackTest_tsupport_subset hε z))

/-- Derivative of a reflected kernel. -/
theorem vorticityReflectedKernel_fderiv {k : Vec3 × ℝ → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (c y v : Vec3 × ℝ) :
    (fderiv ℝ (fun q => k (c - q)) y) v = -((fderiv ℝ k (c - y)) v) := by
  have hinner : HasFDerivAt (fun q : Vec3 × ℝ => c - q)
      (-(1 : Vec3 × ℝ →L[ℝ] Vec3 × ℝ)) y :=
    (hasFDerivAt_id y).const_sub c
  have houter : HasFDerivAt k (fderiv ℝ k (c - y)) (c - y) :=
    (hk.differentiable (by simp) (c - y)).hasFDerivAt
  have hcomp := houter.comp y hinner
  have hfd : fderiv ℝ (fun q => k (c - q)) y =
      (fderiv ℝ k (c - y)).comp (-(1 : Vec3 × ℝ →L[ℝ] Vec3 × ℝ)) := by
    simpa only [Function.comp_def] using hcomp.fderiv
  rw [hfd]
  simp [ContinuousLinearMap.comp_apply]

/-- Pairing the zero extension with the backward test evaluates the backward mollification. -/
theorem vorticityBackTest_pairing {W : Set (Vec3 × ℝ)} (hW : MeasurableSet W)
    {f : Vec3 × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (z : Vec3 × ℝ) :
    ∫ y in W, f y * vorticityBackTest ε hε z y =
      vorticityBackMollify W f ε hε z := by
  rw [← integral_indicator hW]
  have hind : W.indicator (fun y => f y * vorticityBackTest ε hε z y) =
      fun y => spaceTimeMollifier ε hε (z - vorticityBackShift ε - y) * W.indicator f y := by
    funext y
    by_cases hy : y ∈ W
    · simp [hy, vorticityBackTest, mul_comm]
    · simp [hy]
  rw [hind]
  unfold vorticityBackMollify spaceTimeMollify
  rw [vorticityConvolution_eq_integral]

/-- Pairing the zero extension with a first derivative of the backward test gives minus the
corresponding derivative of the backward mollification. -/
theorem vorticityBackTest_pairing_fderiv {W : Set (Vec3 × ℝ)} (hW : MeasurableSet W)
    {f : Vec3 × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hf : LocallyIntegrable (W.indicator f) (volume : Measure (Vec3 × ℝ)))
    (z v : Vec3 × ℝ) :
    ∫ y in W, f y * (fderiv ℝ (vorticityBackTest ε hε z) y) v =
      -((fderiv ℝ (vorticityBackMollify W f ε hε) z) v) := by
  rw [vorticityBackMollify_fderiv hε hf z v, vorticityConvolution_eq_integral,
    ← integral_neg, ← integral_indicator hW]
  congr 1
  funext y
  have hderiv := vorticityReflectedKernel_fderiv (spaceTimeMollifier_contDiff hε)
    (z - vorticityBackShift ε) y v
  change (fderiv ℝ (fun q => spaceTimeMollifier ε hε
    (z - vorticityBackShift ε - q)) y) v = _ at hderiv
  by_cases hy : y ∈ W
  · simp only [Set.indicator_of_mem hy]
    rw [show vorticityBackTest ε hε z = fun q => spaceTimeMollifier ε hε
      (z - vorticityBackShift ε - q) from rfl, hderiv]
    ring
  · simp [Set.indicator_of_notMem hy]

/-- Pairing the zero extension with a second derivative of the backward test gives the
corresponding second derivative of the backward mollification. -/
theorem vorticityBackTest_pairing_fderiv_fderiv {W : Set (Vec3 × ℝ)} (hW : MeasurableSet W)
    {f : Vec3 × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hf : LocallyIntegrable (W.indicator f) (volume : Measure (Vec3 × ℝ)))
    (z v w : Vec3 × ℝ) :
    ∫ y in W, f y *
        (fderiv ℝ (fun q => (fderiv ℝ (vorticityBackTest ε hε z) q) v) y) w =
      (fderiv ℝ (fun y => (fderiv ℝ (vorticityBackMollify W f ε hε) y) v) z) w := by
  rw [vorticityBackMollify_fderiv_fderiv hε hf z v w, vorticityConvolution_eq_integral,
    ← integral_indicator hW]
  congr 1
  funext y
  have hk := spaceTimeMollifier_contDiff hε (n := (⊤ : ℕ∞))
  have hfirst : (fun q => (fderiv ℝ (vorticityBackTest ε hε z) q) v) =
      fun q => -((fderiv ℝ (spaceTimeMollifier ε hε) (z - vorticityBackShift ε - q)) v) := by
    funext q
    exact vorticityReflectedKernel_fderiv hk (z - vorticityBackShift ε) q v
  have hsecond : (fderiv ℝ (fun q => (fderiv ℝ (vorticityBackTest ε hε z) q) v) y) w =
      (fderiv ℝ (fun t => (fderiv ℝ (spaceTimeMollifier ε hε) t) v)
        (z - vorticityBackShift ε - y)) w := by
    rw [hfirst]
    have hneg : (fun q => -((fderiv ℝ (spaceTimeMollifier ε hε)
        (z - vorticityBackShift ε - q)) v)) =
        -(fun q => (fun t => (fderiv ℝ (spaceTimeMollifier ε hε) t) v)
          (z - vorticityBackShift ε - q)) := rfl
    rw [hneg, fderiv_neg, neg_apply,
      vorticityReflectedKernel_fderiv (vorticityKernelDeriv_contDiff hk v)]
    ring
  by_cases hy : y ∈ W
  · simp only [Set.indicator_of_mem hy]
    rw [hsecond]
    ring
  · simp [Set.indicator_of_notMem hy]

/-- Translation is continuous in `L²` on the compactly supported continuous functions. -/
private theorem vorticity_translate_tendsto_of_continuous {g : Vec3 × ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    {h : ℕ → Vec3 × ℝ} (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun z => g (z - h n) - g z) 2
      (volume : Measure (Vec3 × ℝ))) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  let K : Set (Vec3 × ℝ) := tsupport g + Metric.closedBall 0 1
  have hK : IsCompact K := hgc.isCompact.add (isCompact_closedBall 0 1)
  let bound : Vec3 × ℝ → ℝ≥0∞ := K.indicator (fun _ => ENNReal.ofReal ((2 * C) ^ 2))
  have hbound_fin : ∫⁻ z, bound z ∂(volume : Measure (Vec3 × ℝ)) ≠ ∞ := by
    rw [lintegral_indicator hK.measurableSet, setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK.measure_lt_top.ne
  have hsmall : ∀ᶠ n in atTop, ‖h n‖ ≤ 1 := by
    have := (hh.norm).eventually (ge_mem_nhds (show ‖(0 : Vec3 × ℝ)‖ < 1 by simp))
    exact this.mono fun n hn => hn
  have hlint : Tendsto (fun n => ∫⁻ z, ‖g (z - h n) - g z‖ₑ ^ (2 : ℝ)
      ∂(volume : Measure (Vec3 × ℝ))) atTop (𝓝 (∫⁻ _z, (0 : ℝ≥0∞)
        ∂(volume : Measure (Vec3 × ℝ)))) := by
    refine tendsto_lintegral_filter_of_dominated_convergence bound ?_ ?_ hbound_fin ?_
    · exact Eventually.of_forall fun n =>
        ((hg.comp (continuous_id.sub continuous_const)).sub hg).measurable.enorm.pow_const _
    · filter_upwards [hsmall] with n hn
      refine Eventually.of_forall fun z => ?_
      by_cases hz : z ∈ K
      · simp only [bound, Set.indicator_of_mem hz]
        have hnorm : ‖g (z - h n) - g z‖ ≤ 2 * C := by
          calc
            ‖g (z - h n) - g z‖ ≤ ‖g (z - h n)‖ + ‖g z‖ := norm_sub_le _ _
            _ ≤ C + C := add_le_add (hC _) (hC _)
            _ = 2 * C := by ring
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
          (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        have h2 : ‖g (z - h n) - g z‖ ^ (2 : ℝ) = ‖g (z - h n) - g z‖ ^ (2 : ℕ) := by
          exact_mod_cast Real.rpow_natCast _ 2
        rw [h2]
        exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      · have hz1 : g z = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hzs
          apply hz
          exact ⟨z, hzs, 0, Metric.mem_closedBall_self zero_le_one, by simp⟩
        have hz2 : g (z - h n) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hzs
          apply hz
          refine ⟨z - h n, hzs, h n, ?_, by simp⟩
          simpa [Metric.mem_closedBall, dist_zero_right] using hn
        simp [hz1, hz2]
    · refine Eventually.of_forall fun z => ?_
      have hcont : Tendsto (fun n => g (z - h n) - g z) atTop (𝓝 (g (z - 0) - g z)) :=
        ((hg.tendsto (z - 0)).comp (tendsto_const_nhds.sub hh)).sub tendsto_const_nhds
      simp only [sub_zero, sub_self] at hcont
      have hcont' := (continuous_enorm.tendsto 0).comp hcont
      have hpow := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _ |>.comp hcont'
      simpa [Function.comp_def] using hpow
  simp only [lintegral_const, zero_mul] at hlint
  have heq : (fun n => eLpNorm (fun z => g (z - h n) - g z) 2
      (volume : Measure (Vec3 × ℝ))) = fun n =>
      (∫⁻ z, ‖g (z - h n) - g z‖ₑ ^ (2 : ℝ) ∂(volume : Measure (Vec3 × ℝ))) ^
        (1 / (2 : ℝ)) := by
    funext n
    have hm : AEStronglyMeasurable (fun z => g (z - h n) - g z)
        (volume : Measure (Vec3 × ℝ)) :=
      (show Continuous fun z => g (z - h n) - g z by fun_prop).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm]
    norm_num
  rw [heq]
  have hlim := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0 |>.comp hlint
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using hlim

/-- Translation is continuous in `L²`. -/
theorem vorticity_translate_tendsto {g : Vec3 × ℝ → ℝ}
    (hg : MemLp g 2 (volume : Measure (Vec3 × ℝ)))
    {h : ℕ → Vec3 × ℝ} (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun z => g (z - h n) - g z) 2
      (volume : Measure (Vec3 × ℝ))) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨η₁, hη₁, hη₁sum⟩ := exists_Lp_half (μ := (volume : Measure (Vec3 × ℝ)))
    (ε := ℝ) (2 : ℝ≥0∞) hη.ne'
  obtain ⟨η₂, hη₂, hη₂sum⟩ := exists_Lp_half (μ := (volume : Measure (Vec3 × ℝ)))
    (ε := ℝ) (2 : ℝ≥0∞) hη₁.ne'
  obtain ⟨g', _hg'c, hg'close, hg'cont, hg'mem⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) (lt_min hη₁ hη₂).ne'
  have hmid := (ENNReal.tendsto_nhds_zero.1
    (vorticity_translate_tendsto_of_continuous hg'cont _hg'c hh)) η₂ hη₂
  filter_upwards [hmid] with n hn
  have hdiff : AEStronglyMeasurable (g - g') (volume : Measure (Vec3 × ℝ)) :=
    hg.aestronglyMeasurable.sub hg'mem.aestronglyMeasurable
  have htrans : eLpNorm (fun z => (g - g') (z - h n)) 2 (volume : Measure (Vec3 × ℝ)) =
      eLpNorm (g - g') 2 (volume : Measure (Vec3 × ℝ)) := by
    have hmp : MeasurePreserving (fun z : Vec3 × ℝ => z - h n)
        (volume : Measure (Vec3 × ℝ)) (volume : Measure (Vec3 × ℝ)) :=
      measurePreserving_sub_right _ (h n)
    exact eLpNorm_comp_measurePreserving hdiff hmp
  have hA : eLpNorm (fun z => (g - g') (z - h n)) 2 (volume : Measure (Vec3 × ℝ)) ≤ η₂ :=
    htrans.le.trans (hg'close.trans (min_le_right _ _))
  have hAB := hη₂sum _ _ hA hn
  have hC : eLpNorm (g' - g) 2 (volume : Measure (Vec3 × ℝ)) ≤ η₁ := by
    rw [← eLpNorm_neg, neg_sub]
    exact hg'close.trans (min_le_left _ _)
  have htotal := hη₁sum _ _ hAB.le hC
  have hfun : ((fun z => (g - g') (z - h n)) + (fun z => g' (z - h n) - g' z)) + (g' - g) =
      fun z => g (z - h n) - g z := by
    funext z
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hfun] at htotal
  exact htotal.le

/-- Backward mollifications converge in `L²` to the zero extension. -/
theorem vorticityBackMollify_tendsto {W : Set (Vec3 × ℝ)} {f : Vec3 × ℝ → ℝ}
    (hf : MemLp (W.indicator f) 2 (volume : Measure (Vec3 × ℝ)))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ n, 0 < ε n) :
    Tendsto (fun n => eLpNorm
      (fun z => vorticityBackMollify W f (ε n) (hεpos n) z - W.indicator f z) 2
      (volume : Measure (Vec3 × ℝ))) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n => vorticityBackShift (ε n)) atTop (𝓝 0) := by
    have h5 : Tendsto (fun n => 5 * ε n) atTop (𝓝 0) := by
      simpa using hε.const_mul 5
    have hprod := (tendsto_const_nhds (x := (0 : Vec3))).prodMk_nhds h5
    have h00 : ((0 : Vec3), (0 : ℝ)) = (0 : Vec3 × ℝ) := rfl
    rw [h00] at hprod
    exact hprod
  have hmoll := tendsto_eLpNorm_sub_zero_spaceTimeMollify hf hε hεpos
  have htr := vorticity_translate_tendsto hf hshift
  have hsum := hmoll.add htr
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun n => ?_)
  have hmeasA : AEStronglyMeasurable
      (fun z => spaceTimeMollify (W.indicator f) (ε n) (hεpos n) z - W.indicator f z)
      (volume : Measure (Vec3 × ℝ)) :=
    ((spaceTimeMollify_contDiff (hεpos n) (hf.locallyIntegrable (by norm_num))
      (n := 0)).continuous.aestronglyMeasurable).sub hf.aestronglyMeasurable
  have hmp : MeasurePreserving (fun z : Vec3 × ℝ => z - vorticityBackShift (ε n))
      (volume : Measure (Vec3 × ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    measurePreserving_sub_right _ _
  have hfirst := eLpNorm_comp_measurePreserving (p := 2) hmeasA hmp
  have hsplit : (fun z => vorticityBackMollify W f (ε n) (hεpos n) z - W.indicator f z) =
      (fun z => spaceTimeMollify (W.indicator f) (ε n) (hεpos n) (z - vorticityBackShift (ε n))
          - W.indicator f (z - vorticityBackShift (ε n))) +
        fun z => W.indicator f (z - vorticityBackShift (ε n)) - W.indicator f z := by
    funext z
    simp only [vorticityBackMollify, Pi.add_apply]
    ring
  rw [hsplit]
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  gcongr
  exact hfirst.le

/-- Backward mollification preserves a pointwise bound of the zero extension. -/
theorem vorticityBackMollify_abs_le {W : Set (Vec3 × ℝ)} {f : Vec3 × ℝ → ℝ}
    {ε : ℝ} (hε : 0 < ε) {M : ℝ}
    (hbound : ∀ᵐ y ∂(volume : Measure (Vec3 × ℝ)), |W.indicator f y| ≤ M)
    (z : Vec3 × ℝ) :
    |vorticityBackMollify W f ε hε z| ≤ M := by
  have hρint : Integrable (spaceTimeMollifier ε hε) (volume : Measure (Vec3 × ℝ)) :=
    (spaceTimeMollifier_contDiff hε (n := 0)).continuous.integrable_of_hasCompactSupport
      (spaceTimeMollifier_hasCompactSupport hε)
  let c := z - vorticityBackShift ε
  have hae : ∀ᵐ t ∂(volume : Measure (Vec3 × ℝ)), |W.indicator f (c - t)| ≤ M := by
    have hqmp :=
      (Measure.measurePreserving_sub_left (volume : Measure (Vec3 × ℝ)) c).quasiMeasurePreserving
    exact hqmp.ae hbound
  change |∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (spaceTimeMollifier ε hε t)
    (W.indicator f (c - t)) ∂(volume : Measure (Vec3 × ℝ))| ≤ M
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  calc
    |∫ t, spaceTimeMollifier ε hε t * W.indicator f (c - t) ∂(volume : Measure (Vec3 × ℝ))|
        ≤ ∫ t, |spaceTimeMollifier ε hε t * W.indicator f (c - t)|
          ∂(volume : Measure (Vec3 × ℝ)) := abs_integral_le_integral_abs
    _ ≤ ∫ t, spaceTimeMollifier ε hε t * M ∂(volume : Measure (Vec3 × ℝ)) := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _)
        (hρint.mul_const M)
      filter_upwards [hae] with t ht
      rw [abs_mul, abs_of_nonneg (spaceTimeMollifier_nonneg hε t)]
      exact mul_le_mul_of_nonneg_left ht (spaceTimeMollifier_nonneg hε t)
    _ = M := by
      rw [integral_mul_const, spaceTimeMollifier_integral_one hε, one_mul]

end CKN
