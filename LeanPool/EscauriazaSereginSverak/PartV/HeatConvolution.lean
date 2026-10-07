/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Convolution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.BackwardPotentialKernelBridge
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.SpaceSecondDeriv
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Heat Convolution

A smooth compactly supported input has a smooth Gaussian heat orbit at
every positive time.
-/

public section

open MeasureTheory
open scoped Convolution
open CKN.Foundation.Heat CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A smooth compactly supported input has a smooth Gaussian heat orbit at
every positive time. -/
theorem heatConv_smooth_input {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (heatConv t f) := by
  rw [heatConv]
  exact hfc.contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (heatKernel_integrable ht).locallyIntegrable hf

/-- Smooth compact data have a uniform polynomial tail under positive-time heat
convolution. This is used to justify the whole-space entropy test in
`lem:pv-heat-critical`. -/
theorem heatConv_abs_le_spatial_decay {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t : ℝ}, 0 < t → ∀ x : Vec3,
      |heatConv t f x| ≤ C / (1 + vec3EuclideanNorm x) ^ 3 := by
  have hball := hfc.isCompact.isBounded.subset_closedBall_lt 1 (0 : Vec3)
  obtain ⟨R, hRone, hRball⟩ := hball
  have hRpos : 0 < R := lt_trans zero_lt_one hRone
  have hRnonneg : 0 ≤ R := le_of_lt hRpos
  have hfBounded : BddAbove (Set.range (fun y : Vec3 => ‖f y‖)) :=
    hf.continuous.norm.bddAbove_range_of_hasCompactSupport hfc.norm
  let M : ℝ := ⨆ y : Vec3, ‖f y‖
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    exact le_ciSup_of_le hfBounded (0 : Vec3) (abs_nonneg _)
  have hMbound (y : Vec3) : ‖f y‖ ≤ M := by
    dsimp [M]
    exact le_ciSup hfBounded y
  have hfInt : Integrable (fun y : Vec3 => ‖f y‖) volume :=
    hf.continuous.norm.integrable_of_hasCompactSupport hfc.norm
  let C : ℝ := max (M * (1 + 4 * R) ^ 3)
    (64000 * ∫ y : Vec3, ‖f y‖)
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    apply le_max_of_le_right
    positivity
  refine ⟨C, hCnonneg, ?_⟩
  intro t ht x
  have hkernelContinuous : Continuous (fun z : Vec3 => heatKernel z t) := by
    rw [show (fun z : Vec3 => heatKernel z t) = fun z : Vec3 =>
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i : Fin 3, z i ^ 2) / (4 * t)) by
      funext z
      exact heatKernel_eq_formula_sum ht]
    fun_prop (disch := positivity)
  have hfShiftContinuous (x : Vec3) : Continuous (fun z : Vec3 => f (x - z)) := by
    fun_prop
  have hfShiftSupport (x : Vec3) : HasCompactSupport (fun z : Vec3 => f (x - z)) :=
    hfc.comp_homeomorph (Homeomorph.subLeft x)
  have hconvIntegrable (x : Vec3) :
      Integrable (fun z : Vec3 => heatKernel z t * f (x - z)) volume :=
    (hkernelContinuous.mul (hfShiftContinuous x)).integrable_of_hasCompactSupport
      (hfShiftSupport x).mul_left
  have hnear (x : Vec3) :
      |heatConv t f x| ≤ M := by
    rw [heatConv_eq_integral]
    have hprod : Integrable (fun z : Vec3 => heatKernel z t * M) volume := by
      simpa only [mul_comm] using (heatKernel_integrable ht).mul_const M
    have hbound : ∀ z : Vec3,
        ‖heatKernel z t * f (x - z)‖ ≤ heatKernel z t * M := by
      intro z
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg z t)]
      exact mul_le_mul_of_nonneg_left (hMbound (x - z)) (heatKernel_nonneg z t)
    calc
      |∫ z : Vec3, heatKernel z t * f (x - z)| ≤
          ∫ z : Vec3, ‖heatKernel z t * f (x - z)‖ := by
            simpa only [Real.norm_eq_abs] using
              (norm_integral_le_integral_norm
                (fun z : Vec3 => heatKernel z t * f (x - z)))
      _ ≤ ∫ z : Vec3, heatKernel z t * M :=
        integral_mono_ae (hconvIntegrable x).norm hprod
          (Filter.Eventually.of_forall hbound)
      _ = M := by rw [integral_mul_const, heatKernel_integral t ht, one_mul]
  have hfar (x : Vec3) (hx : 4 * R ≤ vec3EuclideanNorm x) :
      |heatConv t f x| ≤
        (64000 * ∫ y : Vec3, ‖f y‖) /
          (1 + vec3EuclideanNorm x) ^ 3 := by
    let n : ℝ := vec3EuclideanNorm x
    have hn : 0 < n := by dsimp [n]; linarith only [hx, hRpos]
    have htwoR : 2 * R ≤ n / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      dsimp [n]
      linarith only [hx]
    have hfShiftAbs : Integrable (fun z : Vec3 => |f (x - z)|) volume :=
      (hfShiftContinuous x).abs.integrable_of_hasCompactSupport
        (hfShiftSupport x).abs
    have hpoint : ∀ z : Vec3,
        ‖heatKernel z t * f (x - z)‖ ≤
          (64000 / (1 + n) ^ 3) * |f (x - z)| := by
      intro z
      by_cases hfz : f (x - z) = 0
      · simp [hfz]
      · have hySupport : x - z ∈ tsupport f :=
          subset_tsupport f (by change f (x - z) ≠ 0; exact hfz)
        have hyBall : x - z ∈ Metric.closedBall (0 : Vec3) R := hRball hySupport
        have hysup : ‖x - z‖ ≤ R := by
          simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hyBall
        have hyEuclidean : vec3EuclideanNorm (x - z) ≤ 2 * R := by
          calc
            vec3EuclideanNorm (x - z) ≤ Real.sqrt 3 * ‖x - z‖ :=
              vec3EuclideanNorm_le_sqrt_three_mul_norm (x - z)
            _ ≤ 2 * R := by
              have hsqrt : Real.sqrt 3 ≤ 2 := by nlinarith only [Real.sq_sqrt (by norm_num : (0
                : ℝ) ≤ 3)]
              exact mul_le_mul hsqrt hysup (norm_nonneg _) (by norm_num)
        have hxadd : x = z + (x - z) := by
          ext i
          simp
        have hxtriangle : n ≤ vec3EuclideanNorm z + 2 * R := by
          dsimp [n]
          rw [hxadd]
          calc
            vec3EuclideanNorm (z + (x - z)) ≤
                vec3EuclideanNorm z + vec3EuclideanNorm (x - z) :=
              vec3EuclideanNorm_add_le z (x - z)
            _ = vec3EuclideanNorm (x - z) + vec3EuclideanNorm z := by ring
            _ ≤ 2 * R + vec3EuclideanNorm z :=
              add_le_add_left hyEuclidean (vec3EuclideanNorm z)
            _ = vec3EuclideanNorm z + 2 * R := by ring
        have hzlarge : n / 2 ≤ vec3EuclideanNorm z := by
          dsimp [n] at *
          linarith only [hxtriangle, htwoR]
        have hrho : n / 2 ≤ rhoTwo z t := by
          unfold rhoTwo
          exact le_trans hzlarge (le_add_of_nonneg_right (Real.sqrt_nonneg t))
        have hk : heatKernel z t ≤ 1000 / (n / 2) ^ 3 := by
          calc
            heatKernel z t ≤ 1000 / rhoTwo z t ^ 3 :=
              heatKernel_le_rho_inv_cube ht
            _ ≤ 1000 / (n / 2) ^ 3 := by
              rw [div_le_div_iff₀
                (pow_pos (lt_of_lt_of_le (by positivity) hrho) 3)
                (pow_pos (by positivity : 0 < n / 2) 3)]
              gcongr
        have hk' : heatKernel z t ≤ 8000 / n ^ 3 := by
          calc
            heatKernel z t ≤ 1000 / (n / 2) ^ 3 := hk
            _ = 8000 / n ^ 3 := by field_simp; ring
        have hnlarge : 2 ≤ n := by dsimp [n] at *; linarith only [hx, hRone]
        have hcompare : 8000 / n ^ 3 ≤ 64000 / (1 + n) ^ 3 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          calc
            8000 * (1 + n) ^ 3 ≤ 8000 * (2 * n) ^ 3 := by
              gcongr
              linarith only [hnlarge]
            _ = 64000 * n ^ 3 := by ring
        have hk'' : heatKernel z t ≤ 64000 / (1 + n) ^ 3 := hk'.trans hcompare
        rw [norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (heatKernel_nonneg z t)]
        exact mul_le_mul_of_nonneg_right hk'' (abs_nonneg _)
    have hdom : Integrable (fun z : Vec3 =>
        (64000 / (1 + n) ^ 3) * |f (x - z)|) volume := by
      exact hfShiftAbs.const_mul _
    rw [heatConv_eq_integral]
    calc
      |∫ z : Vec3, heatKernel z t * f (x - z)| ≤
          ∫ z : Vec3, ‖heatKernel z t * f (x - z)‖ := by
            simpa only [Real.norm_eq_abs] using
              (norm_integral_le_integral_norm
                (fun z : Vec3 => heatKernel z t * f (x - z)))
      _ ≤ ∫ z : Vec3,
          (64000 / (1 + n) ^ 3) * |f (x - z)| :=
        integral_mono_ae (hconvIntegrable x).norm hdom
          (Filter.Eventually.of_forall hpoint)
      _ = (64000 / (1 + n) ^ 3) * ∫ y : Vec3, ‖f y‖ := by
        rw [integral_const_mul, integral_sub_left_eq_self
          (fun y : Vec3 => |f y|) volume x]
        simp only [Real.norm_eq_abs]
      _ = (64000 * ∫ y : Vec3, ‖f y‖) /
          (1 + vec3EuclideanNorm x) ^ 3 := by
        dsimp [n]
        ring
  by_cases hx : vec3EuclideanNorm x < 4 * R
  · have hpow : (1 + vec3EuclideanNorm x) ^ 3 ≤ (1 + 4 * R) ^ 3 := by
      exact pow_le_pow_left₀
        (add_nonneg (by norm_num) (vec3EuclideanNorm_nonneg x))
        (by linarith only [hx]) 3
    have hnearC : M * (1 + vec3EuclideanNorm x) ^ 3 ≤ C := by
      calc
        M * (1 + vec3EuclideanNorm x) ^ 3 ≤ M * (1 + 4 * R) ^ 3 :=
          mul_le_mul_of_nonneg_left hpow hMnonneg
        _ ≤ C := le_max_left _ _
    have hbasepos : 0 < 1 + vec3EuclideanNorm x :=
      add_pos_of_pos_of_nonneg (by norm_num) (vec3EuclideanNorm_nonneg x)
    have hdenpos : 0 < (1 + vec3EuclideanNorm x) ^ 3 := pow_pos hbasepos 3
    exact (hnear x).trans ((le_div_iff₀ hdenpos).2 hnearC)
  · have hx' : 4 * R ≤ vec3EuclideanNorm x := le_of_not_gt hx
    calc
      |heatConv t f x| ≤
          (64000 * ∫ y : Vec3, ‖f y‖) /
            (1 + vec3EuclideanNorm x) ^ 3 := hfar x hx'
      _ ≤ C / (1 + vec3EuclideanNorm x) ^ 3 := by
        have hC : 64000 * ∫ y : Vec3, ‖f y‖ ≤ C := le_max_right _ _
        have hbasepos : 0 < 1 + vec3EuclideanNorm x :=
          add_pos_of_pos_of_nonneg (by norm_num) (vec3EuclideanNorm_nonneg x)
        have hden : 0 ≤ (1 + vec3EuclideanNorm x) ^ 3 :=
          le_of_lt (pow_pos hbasepos 3)
        exact div_le_div_of_nonneg_right hC hden

/-- Positive-time heat evolution of smooth compact data belongs to spatial
`L²`; the tail estimate is uniform up to time zero. -/
theorem heatConv_memLp_two_smooth {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    {t : ℝ} (ht : 0 < t) : MemLp (heatConv t f) 2 volume := by
  obtain ⟨C, hC, htail⟩ := heatConv_abs_le_spatial_decay hf hfc
  have hfin : (Module.finrank ℝ Vec3 : ℝ) < 6 := by
    rw [Module.finrank_fin_fun]
    norm_num
  have hweight : Integrable (fun x : Vec3 => (1 + ‖x‖) ^ (-(6 : ℝ))) volume := by
    exact integrable_one_add_norm (μ := volume) (E := Vec3) (r := 6) hfin
  have hmajorant : Integrable (fun x : Vec3 => C ^ 2 * (1 + ‖x‖) ^ (-(6 : ℝ))) volume := by
    simpa only [mul_comm] using hweight.const_mul (C ^ 2)
  have hmeas : AEStronglyMeasurable (heatConv t f) volume :=
    (heatConv_smooth_input hf hfc ht).continuous.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  refine hmajorant.mono' (hmeas.pow 2) ?_
  filter_upwards [] with x
  have hden : 0 < 1 + vec3EuclideanNorm x :=
    add_pos_of_pos_of_nonneg (by norm_num) (vec3EuclideanNorm_nonneg x)
  have hnorm : ‖x‖ ≤ vec3EuclideanNorm x := norm_le_vec3EuclideanNorm x
  have hdenle : 1 + ‖x‖ ≤ 1 + vec3EuclideanNorm x := by
    calc
      1 + ‖x‖ = ‖x‖ + 1 := by ring
      _ ≤ vec3EuclideanNorm x + 1 := by
        simpa only [add_comm] using add_le_add_right hnorm 1
      _ = 1 + vec3EuclideanNorm x := by ring
  have hpow : |heatConv t f x| ^ 2 ≤
      (C / (1 + vec3EuclideanNorm x) ^ 3) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (htail ht x) 2
  have htailSquare : |heatConv t f x| ^ 2 ≤
      C ^ 2 / (1 + vec3EuclideanNorm x) ^ 6 := by
    calc
      |heatConv t f x| ^ 2 ≤
          (C / (1 + vec3EuclideanNorm x) ^ 3) ^ 2 := hpow
      _ = C ^ 2 / (1 + vec3EuclideanNorm x) ^ 6 := by
        rw [div_pow, ← pow_mul]
  have hcompare : C ^ 2 / (1 + vec3EuclideanNorm x) ^ 6 ≤
      C ^ 2 / (1 + ‖x‖) ^ 6 := by
    exact div_le_div_of_nonneg_left (sq_nonneg C)
      (pow_pos (by positivity) 6)
      (pow_le_pow_left₀ (by positivity) hdenle 6)
  have hweightEq : (1 + ‖x‖) ^ (-(6 : ℝ)) =
      ((1 + ‖x‖) ^ 6)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    norm_num
  calc
    ‖(heatConv t f x) ^ 2‖ = |heatConv t f x| ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
    _ ≤ C ^ 2 / (1 + vec3EuclideanNorm x) ^ 6 := htailSquare
    _ ≤ C ^ 2 / (1 + ‖x‖) ^ 6 := hcompare
    _ = C ^ 2 * (1 + ‖x‖) ^ (-(6 : ℝ)) := by rw [hweightEq]; ring

/-- A spatial derivative of a Gaussian heat orbit is the heat orbit of the
corresponding derivative of smooth compactly supported data. -/
theorem heatConv_fderiv {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    {t : ℝ} (ht : 0 < t) (x v : Vec3) :
    fderiv ℝ (heatConv t f) x v =
      heatConv t (fun y => fderiv ℝ f y v) x := by
  have h := hfc.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (heatKernel_integrable ht).locallyIntegrable (hf.of_le (by norm_num)) x
  have h' := h.fderiv
  have hv := congrArg (fun D : Vec3 →L[ℝ] ℝ => D v) h'
  let df : Vec3 → Vec3 →L[ℝ] ℝ := fun y => fderiv ℝ f y
  have hdfc : Continuous df := by
    simpa [df] using hf.continuous_fderiv
      (by simp : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have hdfs : HasCompactSupport df := by
    exact hfc.fderiv ℝ
  have hconv := MeasureTheory.convolution_precompR_apply
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (f := fun y : Vec3 => heatKernel y t) (g := df) (μ := volume)
    (heatKernel_integrable ht).locallyIntegrable hdfs hdfc x v
  calc
    (fderiv ℝ ((fun y : Vec3 => heatKernel y t) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x) v =
        (((fun y : Vec3 => heatKernel y t) ⋆[
          ContinuousLinearMap.precompR Vec3 (ContinuousLinearMap.lsmul ℝ ℝ),
          volume] df) x) v := hv
    _ = ((fun y : Vec3 => heatKernel y t) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] fun y => df y v) x := hconv
    _ = heatConv t (fun y => fderiv ℝ f y v) x := rfl


end ESS

end
