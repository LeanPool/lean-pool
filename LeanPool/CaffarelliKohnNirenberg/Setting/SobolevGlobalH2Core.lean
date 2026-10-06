/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.Lp
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.Geometry
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Sobolev Global H2Core

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

@[expose]
def h2CoreBall : Set Vec3 := Metric.ball (0 : Vec3) 2

private lemma h2CoreBall_pos : 0 < volume h2CoreBall := by
  exact Metric.isOpen_ball.measure_pos volume ⟨0, by simp⟩

private lemma h2CoreBall_top : volume h2CoreBall < ∞ :=
  measure_ball_lt_top

private lemma h2Core_average_bound {f : Vec3 → ℝ}
    (hf : MemLp f 2 (volume.restrict h2CoreBall)) :
    |integralAverage h2CoreBall f| ≤
      (volume h2CoreBall).toReal ^ (-(1 / 2 : ℝ)) *
        lpNorm f 2 (volume.restrict h2CoreBall) := by
  let μ : Measure Vec3 := volume.restrict h2CoreBall
  let _ : IsFiniteMeasure μ := ⟨by simpa [μ] using h2CoreBall_top⟩
  have hμ0 : μ Set.univ ≠ 0 := by
    simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      h2CoreBall_pos.ne'
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (show (2 : ℝ).HolderConjugate 2 by
      exact Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    hf.aestronglyMeasurable.enorm
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have hh : ∫⁻ x, ‖f x‖ₑ ∂μ ≤
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
        (μ Set.univ) ^ (1 / 2 : ℝ) := by
    simpa only [Pi.mul_apply, mul_one, one_mul, ENNReal.one_rpow, lintegral_const] using hh
  have he : ‖average μ f‖ₑ = (μ Set.univ)⁻¹ * ‖∫ x, f x ∂μ‖ₑ := by
    rw [average_eq, smul_eq_mul, enorm_mul, Real.enorm_eq_ofReal,
      ENNReal.ofReal_inv_of_pos, measureReal_def, ENNReal.ofReal_toReal
        (measure_ne_top μ Set.univ)]
    · exact ENNReal.toReal_pos hμ0 (measure_ne_top μ Set.univ)
    · positivity
  have hE : ‖average μ f‖ₑ ≤
      (μ Set.univ) ^ (-(1 / 2 : ℝ)) * eLpNorm f 2 μ := by
    rw [he]
    calc
      _ ≤ (μ Set.univ)⁻¹ * ∫⁻ x, ‖f x‖ₑ ∂μ := by
        gcongr
        exact enorm_integral_le_lintegral_enorm f
      _ ≤ (μ Set.univ)⁻¹ *
          ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
            (μ Set.univ) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
          (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num) hf.aestronglyMeasurable]
        norm_num only [ENNReal.toReal_ofNat]
        rw [mul_comm _ ((μ Set.univ) ^ (1 / 2 : ℝ)), ← mul_assoc,
          ← ENNReal.rpow_neg_one, ← ENNReal.rpow_add _ _ hμ0
            (measure_ne_top μ Set.univ)]
        norm_num
        simp [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  have hreal := ENNReal.toReal_mono
    (by finiteness : (μ Set.univ) ^ (-(1 / 2 : ℝ)) * eLpNorm f 2 μ ≠ ∞)
    hE
  simpa [integralAverage, μ, lpNorm, Real.enorm_eq_ofReal,
    ENNReal.toReal_mul, ENNReal.toReal_rpow,
    Measure.restrict_apply MeasurableSet.univ, univ_inter] using hreal

private lemma h2Core_fderiv_norm_le_sum {f : Vec3 → ℝ} (x : Vec3) :
    ‖fderiv ℝ f x‖ ≤ ∑ i : Fin 3, |(fderiv ℝ f x) (basisVec i)| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  calc
    ‖(fderiv ℝ f x) z‖ =
        ‖∑ i : Fin 3, z i • (fderiv ℝ f x) (basisVec i)‖ := by
      congr 1
      rw [← sum_smul_basisVec z, map_sum]
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        basisVec_apply]
      simp
    _ ≤ ∑ i : Fin 3, ‖z i • (fderiv ℝ f x) (basisVec i)‖ := norm_sum_le _ _
    _ ≤ (∑ i : Fin 3, |(fderiv ℝ f x) (basisVec i)|) * ‖z‖ := by
      calc
        _ ≤ ∑ i : Fin 3, ‖z‖ * |(fderiv ℝ f x) (basisVec i)| := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (norm_le_pi_norm z i) (abs_nonneg _)
        _ = _ := by
          rw [Finset.sum_mul]
          ac_rfl

private lemma h2Core_kernel_memLp :
    MemLp (fun y : Vec3 => rieszKernel 0 y)
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict h2CoreBall) := by
  have hmeas : AEStronglyMeasurable (fun y : Vec3 => rieszKernel 0 y) volume := by
    apply Measurable.aestronglyMeasurable
    unfold rieszKernel
    measurability
  have hpow : IntegrableOn
      (fun y : Vec3 => ‖y‖ ^ (-(12 / 5 : ℝ))) h2CoreBall volume := by
    apply integrableOn_ball_of_norm_le_rpow (E := Vec3) (F := ℝ)
      (C := (1 : ℝ)) (α := (12 / 5 : ℝ)) (r := 2)
      (by norm_num : 1 ≤ Module.finrank ℝ Vec3)
      (by norm_num : (12 / 5 : ℝ) < Module.finrank ℝ Vec3)
    · filter_upwards [] with y
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _)]
      simpa only [one_mul] using (le_refl (‖y‖ ^ (-(12 / 5 : ℝ)) : ℝ))
    · unfold rieszKernel at hmeas
      have hpowMeas : Measurable (fun y : Vec3 => ‖y‖ ^ (-(12 / 5 : ℝ))) := by
        measurability
      exact hpowMeas.aestronglyMeasurable
  have heq : (fun y : Vec3 =>
      ‖rieszKernel 0 y‖ ^ (ENNReal.ofReal (6 / 5 : ℝ)).toReal) =ᵐ[
        volume.restrict h2CoreBall] (fun y => ‖y‖ ^ (-(12 / 5 : ℝ))) := by
    filter_upwards [] with y
    by_cases hy : y = 0
    · subst y
      have hne : (1 - (3 : ℝ)) ≠ 0 := by norm_num
      have hp : (ENNReal.ofReal (6 / 5 : ℝ)).toReal = 6 / 5 := by norm_num
      simp [rieszKernel, hne, hp]
    · rw [show (ENNReal.ofReal (6 / 5 : ℝ)).toReal = 6 / 5 by norm_num]
      simp only [rieszKernel, zero_sub, norm_neg]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _)]
      norm_num only [show (1 - (3 : ℝ)) = -2 by norm_num]
      have hnorm : 0 < ‖y‖ := norm_pos_iff.mpr hy
      rw [← Real.rpow_mul hnorm.le]
      congr 1
      norm_num
  rw [← (integrable_norm_rpow_iff hmeas.restrict (by norm_num) (by norm_num))]
  exact hpow.congr heq.symm

/-- Smooth functions with an `L²` value and coordinate `L⁶` derivatives obey
the global pointwise estimate used by the weak embedding. -/
theorem smooth_global_linf_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : Vec3 → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f →
      MemLp f 2 volume →
      (∀ i : Fin 3, MemLp (fun x => (fderiv ℝ f x) (basisVec i))
        (ENNReal.ofReal (6 : ℝ)) volume) →
      ∀ x : Vec3,
        |f x| ≤ C * (lpNorm f 2 volume +
          ∑ i : Fin 3, lpNorm (fun y => (fderiv ℝ f y) (basisVec i)) 6 volume) := by
  let U : Set Vec3 := h2CoreBall
  let hU : IsOpenBoundedConvexDomain U :=
    isOpenBoundedConvexDomain_ball (0 : Vec3) (by norm_num)
  let _ : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  let C₀ : ℝ := (volume U).toReal⁻¹ *
      (((2 * Classical.choose hU.isBoundedDomain) ^ 3) / 3) *
        (∫ y in U, ‖rieszKernel 0 y‖ ^ (6 / 5 : ℝ) ∂volume) ^ (5 / 6 : ℝ)
  let C₁ : ℝ := (volume U).toReal ^ (-(1 / 2 : ℝ))
  have hchoose : 0 ≤ Classical.choose hU.isBoundedDomain := by
    exact (Classical.choose_spec hU.isBoundedDomain).1.le
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁]
    positivity
  refine ⟨C₀ + C₁, add_nonneg hC₀ hC₁, ?_⟩
  intro f hf hf2 hD x
  let g : Vec3 → ℝ := fun y => f (y + x)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    hf.comp (contDiff_id.add contDiff_const)
  have hgf : MemLp g 2 volume := hf2.comp_measurePreserving
    (measurePreserving_add_right (volume : Measure Vec3) x)
  have hgi (i : Fin 3) : MemLp
      (fun y => (fderiv ℝ g y) (basisVec i))
      (ENNReal.ofReal (6 : ℝ)) volume := by
    have heq : (fun y => (fderiv ℝ g y) (basisVec i)) =
        (fun y => (fderiv ℝ f (y + x)) (basisVec i)) := by
      funext y
      simpa [g] using congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i))
        (fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := y) x)
    rw [heq]
    exact (hD i).comp_measurePreserving
      (measurePreserving_add_right (volume : Measure Vec3) x)
  have hUmem : (0 : Vec3) ∈ U := by simp [U, h2CoreBall]
  have hgfU : IntegrableOn g U volume := by
    exact (hgf.mono_measure Measure.restrict_le_self).integrable (by norm_num)
  have hP := norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_rieszKernel_of_isOpenBoundedConvexDomain
    hU (u := g) hgfU (hg.of_le (by norm_num)) hUmem (by
      have hp : 0 < volume U := by simpa [U] using h2CoreBall_pos
      exact ENNReal.toReal_pos hp.ne' (by simpa [U] using h2CoreBall_top.ne))
  have hkernel := h2Core_kernel_memLp
  have hderMem : MemLp (fun y => ‖fderiv ℝ g y‖)
      (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) := by
    apply (memLp_iff.mpr ?_)
    let S : Vec3 → ℝ := fun y => ∑ i : Fin 3,
      |(fderiv ℝ g y) (basisVec i)|
    have hS : (∑ i : Fin 3, fun y : Vec3 =>
        |(fderiv ℝ g y) (basisVec i)|) = S := by
      funext y
      rfl
    have hmeas : AEStronglyMeasurable (fun y => ‖fderiv ℝ g y‖)
        (volume.restrict U) :=
      (hg.continuous_fderiv (by norm_num)).norm.aestronglyMeasurable.restrict
    have hsum : eLpNorm (fun y => ‖fderiv ℝ g y‖)
        (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) ≤
        ∑ i : Fin 3, eLpNorm (fun y =>
          |(fderiv ℝ g y) (basisVec i)|)
          (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) := by
      calc
        _ ≤ eLpNorm S (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) := by
          apply eLpNorm_mono_ae hmeas
          filter_upwards [] with y
          have hSnonneg : 0 ≤ S y := by
            dsimp [S]
            exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
          calc
            ‖‖fderiv ℝ g y‖‖ = ‖fderiv ℝ g y‖ := norm_norm _
            _ ≤ S y := by
              exact h2Core_fderiv_norm_le_sum (f := g) y
            _ = ‖S y‖ := by
              rw [Real.norm_eq_abs, abs_of_nonneg hSnonneg]
        _ ≤ _ := by
          rw [← hS]
          simpa using (eLpNorm_sum_le
            (f := fun i : Fin 3 => fun y : Vec3 =>
              |(fderiv ℝ g y) (basisVec i)|)
            (p := ENNReal.ofReal (6 : ℝ))
            (s := Finset.univ) (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 6))
    have hsumtop : ∀ i : Fin 3, eLpNorm (fun y =>
        |(fderiv ℝ g y) (basisVec i)|) (ENNReal.ofReal (6 : ℝ))
        (volume.restrict U) < ∞ := by
      intro i
      calc
        _ = eLpNorm (fun y => (fderiv ℝ g y) (basisVec i))
            (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) := by
          exact eLpNorm_norm _ (hgi i).aestronglyMeasurable.restrict
        _ ≤ eLpNorm (fun y => (fderiv ℝ g y) (basisVec i))
            (ENNReal.ofReal (6 : ℝ)) volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
        _ < ∞ := (hgi i).eLpNorm_lt_top
    exact hsum.trans_lt (ENNReal.sum_lt_top.2 (fun i _ => hsumtop i))
  have hholder : ∫ y in U, ‖fderiv ℝ g y‖ * ‖rieszKernel 0 y‖ ∂volume ≤
      (∫ y in U, ‖fderiv ℝ g y‖ ^ (6 : ℝ) ∂volume) ^ (1 / 6 : ℝ) *
        (∫ y in U, ‖rieszKernel 0 y‖ ^ (6 / 5 : ℝ) ∂volume) ^ (5 / 6 : ℝ) := by
    have hh := integral_mul_norm_le_Lp_mul_Lq
      (μ := volume.restrict U)
      (show (6 : ℝ).HolderConjugate (6 / 5 : ℝ) by
        exact Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      hderMem hkernel
    simpa [MeasureTheory.IntegrableOn] using hh
  have hsum' : eLpNorm (fun y => ‖fderiv ℝ g y‖)
      (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) ≤
      ∑ i : Fin 3, eLpNorm (fun y =>
        |(fderiv ℝ g y) (basisVec i)|)
        (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) := by
    let S : Vec3 → ℝ := fun y => ∑ i : Fin 3,
      |(fderiv ℝ g y) (basisVec i)|
    have hS : (∑ i : Fin 3, fun y : Vec3 =>
        |(fderiv ℝ g y) (basisVec i)|) = S := by
      funext y
      rfl
    have hmeas : AEStronglyMeasurable (fun y => ‖fderiv ℝ g y‖)
        (volume.restrict U) :=
      (hg.continuous_fderiv (by norm_num)).norm.aestronglyMeasurable.restrict
    calc
      _ ≤ eLpNorm S (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) := by
        apply eLpNorm_mono_ae hmeas
        filter_upwards [] with y
        have hSnonneg : 0 ≤ S y := by
          dsimp [S]
          exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
        calc
          ‖‖fderiv ℝ g y‖‖ = ‖fderiv ℝ g y‖ := norm_norm _
          _ ≤ S y := h2Core_fderiv_norm_le_sum (f := g) y
          _ = ‖S y‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hSnonneg]
      _ ≤ _ := by
        rw [← hS]
        simpa using (eLpNorm_sum_le
          (f := fun i : Fin 3 => fun y : Vec3 =>
            |(fderiv ℝ g y) (basisVec i)|)
          (p := ENNReal.ofReal (6 : ℝ))
          (s := Finset.univ) (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 6))
  have hgradBound : (∫ y in U, ‖fderiv ℝ g y‖ ^ (6 : ℝ) ∂volume) ^ (1 / 6 : ℝ) ≤
      ∑ i : Fin 3, lpNorm (fun y => (fderiv ℝ g y) (basisVec i)) 6 volume := by
    have hsumtop' : (∑ i : Fin 3, eLpNorm (fun y =>
        |(fderiv ℝ g y) (basisVec i)|) (ENNReal.ofReal (6 : ℝ))
        (volume.restrict U)) < ∞ :=
      ENNReal.sum_lt_top.2 (fun i _ => by
        calc
          _ = eLpNorm (fun y => (fderiv ℝ g y) (basisVec i))
              (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) := by
            exact eLpNorm_norm _ (hgi i).aestronglyMeasurable.restrict
          _ ≤ eLpNorm (fun y => (fderiv ℝ g y) (basisVec i))
              (ENNReal.ofReal (6 : ℝ)) volume :=
            eLpNorm_mono_measure _ Measure.restrict_le_self
          _ < ∞ := (hgi i).eLpNorm_lt_top)
    have hreal := ENNReal.toReal_mono hsumtop'.ne hsum'
    have hleft : (∫ y in U, ‖fderiv ℝ g y‖ ^ (6 : ℝ) ∂volume) ^ (1 / 6 : ℝ) =
        (eLpNorm (fun y => ‖fderiv ℝ g y‖) (ENNReal.ofReal (6 : ℝ))
          (volume.restrict U)).toReal := by
      have he := hderMem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      have ht := congrArg ENNReal.toReal he
      convert ht.symm using 1; norm_num
      rw [ENNReal.toReal_ofReal]
      positivity
    calc
      _ = (eLpNorm (fun y => ‖fderiv ℝ g y‖) (ENNReal.ofReal (6 : ℝ))
          (volume.restrict U)).toReal := hleft
      _ ≤ (∑ i : Fin 3, (eLpNorm (fun y =>
          |(fderiv ℝ g y) (basisVec i)|) (ENNReal.ofReal (6 : ℝ))
          (volume.restrict U))).toReal := hreal
      _ = ∑ i : Fin 3, (eLpNorm (fun y =>
          |(fderiv ℝ g y) (basisVec i)|) (ENNReal.ofReal (6 : ℝ))
          (volume.restrict U)).toReal := by
        apply ENNReal.toReal_sum
        intro i hi
        have hnormRestr : eLpNorm (fun y => |(fderiv ℝ g y) (basisVec i)|)
            (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) =
            eLpNorm (fun y => (fderiv ℝ g y) (basisVec i))
              (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) := by
          simpa [Real.norm_eq_abs] using eLpNorm_norm
            (fun y => (fderiv ℝ g y) (basisVec i))
              (hgi i).aestronglyMeasurable.restrict
        rw [hnormRestr]
        exact (lt_of_le_of_lt
          (eLpNorm_mono_measure _ (Measure.restrict_le_self : volume.restrict U ≤ volume))
          (hgi i).eLpNorm_lt_top).ne
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [lpNorm]
        have hmono : eLpNorm (fun y => |(fderiv ℝ g y) (basisVec i)|)
            (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) ≤
            eLpNorm (fun y => |(fderiv ℝ g y) (basisVec i)|)
              (ENNReal.ofReal (6 : ℝ)) volume :=
          eLpNorm_mono_measure _ (Measure.restrict_le_self : volume.restrict U ≤ volume)
        have hnormRestr : eLpNorm (fun y => |(fderiv ℝ g y) (basisVec i)|)
            (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) =
            eLpNorm (fun y => (fderiv ℝ g y) (basisVec i))
              (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) := by
          simpa [Real.norm_eq_abs] using eLpNorm_norm
            (fun y => (fderiv ℝ g y) (basisVec i))
              (hgi i).aestronglyMeasurable.restrict
        have hnormVol : eLpNorm (fun y => |(fderiv ℝ g y) (basisVec i)|)
            (ENNReal.ofReal (6 : ℝ)) volume =
            eLpNorm (fun y => (fderiv ℝ g y) (basisVec i))
              (ENNReal.ofReal (6 : ℝ)) volume := by
          simpa [Real.norm_eq_abs] using eLpNorm_norm
            (fun y => (fderiv ℝ g y) (basisVec i))
              (hgi i).aestronglyMeasurable
        have htop := (hgi i).eLpNorm_ne_top
        have hmono' : eLpNorm (fun y => |(fderiv ℝ g y) (basisVec i)|)
            (6 : ℝ≥0∞) (volume.restrict U) ≤
            eLpNorm (fun y => |(fderiv ℝ g y) (basisVec i)|)
              (6 : ℝ≥0∞) volume := by simpa using hmono
        have hnormRestr' : eLpNorm (fun y => |(fderiv ℝ g y) (basisVec i)|)
            (6 : ℝ≥0∞) (volume.restrict U) =
            eLpNorm (fun y => (fderiv ℝ g y) (basisVec i))
              (6 : ℝ≥0∞) (volume.restrict U) := by simpa using hnormRestr
        have hnormVol' : eLpNorm (fun y => |(fderiv ℝ g y) (basisVec i)|)
            (6 : ℝ≥0∞) volume =
            eLpNorm (fun y => (fderiv ℝ g y) (basisVec i))
              (6 : ℝ≥0∞) volume := by simpa using hnormVol
        have htop' : eLpNorm (fun y => (fderiv ℝ g y) (basisVec i))
            (6 : ℝ≥0∞) volume ≠ ∞ := by simpa using htop
        change (eLpNorm (fun y => |(fderiv ℝ g y) (basisVec i)|)
          (ENNReal.ofReal (6 : ℝ)) (volume.restrict U)).toReal ≤
          (eLpNorm (fun y => (fderiv ℝ g y) (basisVec i))
            (6 : ℝ≥0∞) volume).toReal
        have hle : eLpNorm (fun y => |(fderiv ℝ g y) (basisVec i)|)
              (ENNReal.ofReal (6 : ℝ)) (volume.restrict U) ≤
            eLpNorm (fun y => (fderiv ℝ g y) (basisVec i))
              (6 : ℝ≥0∞) volume := by
          simpa using (hmono.trans_eq hnormVol)
        exact ENNReal.toReal_mono htop'
          hle
  have hmean : |integralAverage U g| ≤ C₁ * lpNorm f 2 volume := by
    have havg := h2Core_average_bound (f := g)
      (hgf.mono_measure Measure.restrict_le_self)
    have htrans : eLpNorm g 2 volume = eLpNorm f 2 volume := by
      exact eLpNorm_comp_measurePreserving hf2.aestronglyMeasurable
        (measurePreserving_add_right (volume : Measure Vec3) x)
    have hnorm : lpNorm g 2 (volume.restrict h2CoreBall) ≤
        (eLpNorm f 2 volume).toReal := by
      change (eLpNorm g 2 (volume.restrict h2CoreBall)).toReal ≤ _
      apply ENNReal.toReal_mono hf2.eLpNorm_ne_top
      calc
        eLpNorm g 2 (volume.restrict h2CoreBall) ≤ eLpNorm g 2 volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
        _ = eLpNorm f 2 volume := htrans
    have hvol : (volume U).toReal ^ (-(1 / 2 : ℝ)) *
        (eLpNorm f 2 volume).toReal = C₁ * lpNorm f 2 volume := by
      simp [C₁, lpNorm]
    exact (havg.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))).trans_eq hvol
  have hzero : |g 0| ≤
      |g 0 - integralAverage U g| + |integralAverage U g| := by
    calc
      |g 0| = |(g 0 - integralAverage U g) + integralAverage U g| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hgrad : |g 0 - integralAverage U g| ≤
      C₀ * (∑ i : Fin 3, lpNorm (fun y => (fderiv ℝ g y) (basisVec i)) 6 volume) := by
    have hP' : |g 0 - integralAverage U g| ≤
        (volume U).toReal⁻¹ * ((((2 * Classical.choose hU.isBoundedDomain) ^ 3) / 3) *
          (∫ y in U, ‖fderiv ℝ g y‖ * ‖rieszKernel 0 y‖ ∂volume)) := by
      have hki : (∫ y in U, ‖fderiv ℝ g y‖ * rieszKernel 0 y ∂volume) =
          ∫ y in U, ‖fderiv ℝ g y‖ * ‖rieszKernel 0 y‖ ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [Real.norm_eq_abs, abs_of_nonneg (rieszKernel_nonneg 0 y)]
      simpa [Real.norm_eq_abs, hki] using hP
    calc
      _ ≤ (volume U).toReal⁻¹ * ((((2 * Classical.choose hU.isBoundedDomain) ^ 3) / 3) *
          ((∫ y in U, ‖fderiv ℝ g y‖ ^ (6 : ℝ) ∂volume) ^ (1 / 6 : ℝ) *
            (∫ y in U, ‖rieszKernel 0 y‖ ^ (6 / 5 : ℝ) ∂volume) ^ (5 / 6 : ℝ))) := by
        have hmid :
            (((2 * Classical.choose hU.isBoundedDomain) ^ 3) / 3) *
                (∫ y in U, ‖fderiv ℝ g y‖ * ‖rieszKernel 0 y‖ ∂volume) ≤
              (((2 * Classical.choose hU.isBoundedDomain) ^ 3) / 3) *
                ((∫ y in U, ‖fderiv ℝ g y‖ ^ (6 : ℝ) ∂volume) ^ (1 / 6 : ℝ) *
                  (∫ y in U, ‖rieszKernel 0 y‖ ^ (6 / 5 : ℝ) ∂volume) ^ (5 / 6 : ℝ)) :=
          mul_le_mul_of_nonneg_left hholder (by positivity)
        exact hP'.trans (mul_le_mul_of_nonneg_left hmid (by positivity))
      _ ≤ C₀ * (∑ i : Fin 3, lpNorm (fun y => (fderiv ℝ g y) (basisVec i)) 6 volume) := by
        let A : ℝ := (volume U).toReal⁻¹ *
          (((2 * Classical.choose hU.isBoundedDomain) ^ 3) / 3)
        let K : ℝ := (∫ y in U, ‖rieszKernel 0 y‖ ^ (6 / 5 : ℝ) ∂volume) ^
          (5 / 6 : ℝ)
        have hA : 0 ≤ A := by
          dsimp [A]
          positivity
        have hK : 0 ≤ K := by
          dsimp [K]
          positivity
        calc
          _ = A * ((∫ y in U, ‖fderiv ℝ g y‖ ^ (6 : ℝ) ∂volume) ^ (1 / 6 : ℝ) * K) := by
            dsimp [A, K]
            ring
          _ ≤ A * ((∑ i : Fin 3,
              lpNorm (fun y => (fderiv ℝ g y) (basisVec i)) 6 volume) * K) := by
            gcongr
          _ = C₀ * (∑ i : Fin 3,
              lpNorm (fun y => (fderiv ℝ g y) (basisVec i)) 6 volume) := by
            dsimp [C₀, K]
            ring
  have hfinal : |f x| ≤ (C₀ + C₁) *
      (lpNorm f 2 volume +
        ∑ i : Fin 3, lpNorm (fun y => (fderiv ℝ f y) (basisVec i)) 6 volume) := by
    have hshift : ∀ i, lpNorm (fun y => (fderiv ℝ g y) (basisVec i)) 6 volume =
        lpNorm (fun y => (fderiv ℝ f y) (basisVec i)) 6 volume := by
      intro i
      simp only [lpNorm]
      have heq : (fun y => (fderiv ℝ g y) (basisVec i)) =
          (fun y => (fderiv ℝ f (y + x)) (basisVec i)) := by
        funext y
        simpa [g] using congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i))
          (fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := y) x)
      rw [heq]
      have hcomp := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal (6 : ℝ))
        (hD i).aestronglyMeasurable
        (measurePreserving_add_right (volume : Measure Vec3) x)
      simpa [Function.comp_def] using congrArg ENNReal.toReal hcomp
    have hsum_nonneg : 0 ≤ ∑ i : Fin 3,
        lpNorm (fun y => (fderiv ℝ f y) (basisVec i)) 6 volume := by
      apply Finset.sum_nonneg
      intro i hi
      exact ENNReal.toReal_nonneg
    have hLp_nonneg : 0 ≤ lpNorm f 2 volume := ENNReal.toReal_nonneg
    calc
      |f x| = |g 0| := by simp [g]
      _ ≤ |g 0 - integralAverage U g| + |integralAverage U g| := hzero
      _ ≤ C₀ * (∑ i : Fin 3, lpNorm (fun y => (fderiv ℝ g y) (basisVec i)) 6 volume) +
          C₁ * lpNorm f 2 volume := add_le_add hgrad hmean
      _ = C₀ * (∑ i : Fin 3, lpNorm (fun y => (fderiv ℝ f y) (basisVec i)) 6 volume) +
          C₁ * lpNorm f 2 volume := by simp_rw [hshift]
      _ ≤ (C₀ + C₁) *
          (lpNorm f 2 volume + ∑ i : Fin 3,
            lpNorm (fun y => (fderiv ℝ f y) (basisVec i)) 6 volume) := by
        nlinarith only [hC₀, hC₁, hLp_nonneg, hsum_nonneg]
  exact hfinal

end

end CKN
