/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatConv
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Spatial decay of the causal heat potential

The causal heat potential of a continuous compactly supported source decays
like `|x|^{-3}` in space, uniformly in time. This justifies the whole-space
integrations by parts in the smooth-data energy estimates of `lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

local instance : Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

private theorem heatKernelPlus_pair (y : Vec3) (s : ℝ) :
    heatKernelPlus (show ParabolicPoint from (y, s)) =
      if 0 < s then heatKernel y s else 0 := rfl

private theorem heatKernelPlus_vecTime_measurable :
    Measurable (fun p : Vec3 × ℝ => heatKernelPlus p) := by
  unfold heatKernelPlus heatKernel
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd) ?_ measurable_const
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd) ?_ measurable_const
  fun_prop

private theorem heatKernelPlus_slice_lintegral_le_one (s : ℝ) :
    ∫⁻ y : Vec3, ENNReal.ofReal (heatKernelPlus (y, s)) ≤ 1 := by
  by_cases hs : 0 < s
  · have heq : (fun y : Vec3 => ENNReal.ofReal (heatKernelPlus (y, s))) =
        fun y => ENNReal.ofReal (heatKernel y s) := by
      funext y
      simp only [heatKernelPlus_pair, hs, ↓reduceIte]
    rw [heq, ← ofReal_integral_eq_lintegral_ofReal (heatKernel_integrable hs)
      (Eventually.of_forall fun y => heatKernel_nonneg y s),
      heatKernel_integral s hs, ENNReal.ofReal_one]
  · have heq : (fun y : Vec3 => ENNReal.ofReal (heatKernelPlus (y, s))) = fun _ => 0 := by
      funext y
      simp only [heatKernelPlus_pair, hs, ↓reduceIte, ENNReal.ofReal_zero]
    rw [heq, lintegral_zero]
    exact zero_le_one

/-- The causal heat kernel has total mass at most the length of a time window. -/
private theorem heatKernelPlus_time_window_lintegral (a b : ℝ) (c : ℝ≥0∞) :
    ∫⁻ p : Vec3 × ℝ, ENNReal.ofReal (heatKernelPlus p) *
        (Icc a b).indicator (fun _ => c) p.2 ≤ c * ENNReal.ofReal (b - a) := by
  have hmeas : Measurable (fun p : Vec3 × ℝ => ENNReal.ofReal (heatKernelPlus p) *
      (Icc a b).indicator (fun _ => c) p.2) :=
    (ENNReal.measurable_ofReal.comp heatKernelPlus_vecTime_measurable).mul
      ((measurable_const.indicator measurableSet_Icc).comp measurable_snd)
  rw [Measure.volume_eq_prod, lintegral_prod_symm' _ hmeas]
  calc
    ∫⁻ s : ℝ, ∫⁻ y : Vec3, ENNReal.ofReal (heatKernelPlus (y, s)) *
        (Icc a b).indicator (fun _ => c) s ≤
        ∫⁻ s : ℝ, (Icc a b).indicator (fun _ => c) s := by
      apply lintegral_mono
      intro s
      have hy : Measurable (fun y : Vec3 => ENNReal.ofReal (heatKernelPlus (y, s))) :=
        (ENNReal.measurable_ofReal.comp heatKernelPlus_vecTime_measurable).comp
          measurable_prodMk_right
      dsimp only
      rw [lintegral_mul_const _ hy]
      calc
        (∫⁻ y : Vec3, ENNReal.ofReal (heatKernelPlus (y, s))) *
            (Icc a b).indicator (fun _ => c) s ≤
            1 * (Icc a b).indicator (fun _ => c) s :=
          mul_le_mul_left (heatKernelPlus_slice_lintegral_le_one s) _
        _ = _ := one_mul _
    _ = c * ENNReal.ofReal (b - a) := by
      rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]

/-- The causal heat potential of a continuous compactly supported source
decays like `|x|^{-3}` uniformly in time. -/
theorem causalHeatConv_abs_le_decay {h : Vec3 × ℝ → ℝ}
    (hh : Continuous h) (hc : HasCompactSupport h) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v : Vec3 × ℝ,
      |causalHeatConv h v| ≤ M / (1 + vec3EuclideanNorm v.1) ^ 3 := by
  obtain ⟨R, hRone, hRball⟩ :=
    hc.isCompact.isBounded.subset_closedBall_lt 1 (0 : Vec3 × ℝ)
  have hRpos : 0 < R := lt_trans zero_lt_one hRone
  have hBdd : BddAbove (Set.range (fun p : Vec3 × ℝ => ‖h p‖)) :=
    hh.norm.bddAbove_range_of_hasCompactSupport hc.norm
  let B : ℝ := ⨆ p : Vec3 × ℝ, ‖h p‖
  have hB (p : Vec3 × ℝ) : ‖h p‖ ≤ B := le_ciSup hBdd p
  have hBnonneg : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hsupp (q : Vec3 × ℝ) (hq : h q ≠ 0) : ‖q‖ ≤ R := by
    have hmem := hRball (subset_tsupport h hq)
    simpa [Metric.mem_closedBall, dist_zero_right] using hmem
  have hintAbs : Integrable (fun p : Vec3 × ℝ => |h p|) :=
    hh.abs.integrable_of_hasCompactSupport hc.abs
  let I : ℝ := ∫ p : Vec3 × ℝ, |h p|
  have hInonneg : 0 ≤ I := integral_nonneg fun p => abs_nonneg _
  -- near bound, uniform in space
  have hnear (v : Vec3 × ℝ) : |causalHeatConv h v| ≤ B * (2 * R) := by
    rw [causalHeatConv_eq_integral, ← Real.norm_eq_abs]
    refine (norm_integral_le_lintegral_norm _).trans ?_
    have hpoint (p : Vec3 × ℝ) : ENNReal.ofReal ‖heatKernelPlus p * h (v - p)‖ ≤
        ENNReal.ofReal (heatKernelPlus p) *
          (Icc (v.2 - R) (v.2 + R)).indicator (fun _ => ENNReal.ofReal B) p.2 := by
      by_cases hvp : h (v - p) = 0
      · rw [hvp, mul_zero, norm_zero, ENNReal.ofReal_zero]
        exact bot_le
      · have hnorm := hsupp _ hvp
        have htime : |(v - p).2| ≤ R :=
          (Real.norm_eq_abs _ ▸ norm_snd_le (v - p)).trans hnorm
        have hmem : p.2 ∈ Icc (v.2 - R) (v.2 + R) := by
          rw [Prod.snd_sub, abs_le] at htime
          constructor <;> linarith only [htime.1, htime.2]
        rw [indicator_of_mem hmem, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (heatKernelPlus_nonneg p),
          ENNReal.ofReal_mul (heatKernelPlus_nonneg p)]
        exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hB _)) _
    have hlint := (lintegral_mono hpoint).trans
      (heatKernelPlus_time_window_lintegral (v.2 - R) (v.2 + R) (ENNReal.ofReal B))
    have hfin : ENNReal.ofReal B * ENNReal.ofReal (v.2 + R - (v.2 - R)) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    calc
      (∫⁻ p : Vec3 × ℝ, ENNReal.ofReal ‖heatKernelPlus p * h (v - p)‖).toReal ≤
          (ENNReal.ofReal B * ENNReal.ofReal (v.2 + R - (v.2 - R))).toReal :=
        ENNReal.toReal_mono hfin hlint
      _ = B * (2 * R) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hBnonneg,
          ENNReal.toReal_ofReal (by linarith only [hRpos])]
        ring
  -- far bound
  have hfar (v : Vec3 × ℝ) (hv : 4 * R ≤ vec3EuclideanNorm v.1) :
      |causalHeatConv h v| ≤ 64000 * I / (1 + vec3EuclideanNorm v.1) ^ 3 := by
    let n : ℝ := vec3EuclideanNorm v.1
    have hn : 4 * R ≤ n := hv
    have hnpos : 0 < n := by linarith only [hn, hRpos]
    have hpoint (p : Vec3 × ℝ) : ‖heatKernelPlus p * h (v - p)‖ ≤
        (64000 / (1 + n) ^ 3) * |h (v - p)| := by
      by_cases hvp : h (v - p) = 0
      · rw [hvp, mul_zero, norm_zero, abs_zero, mul_zero]
      by_cases hp : 0 < p.2
      swap
      · rw [show heatKernelPlus p = 0 from
          heatKernelPlus_eq_zero_of_nonpos (x := p.1) (le_of_not_gt hp), zero_mul,
          norm_zero]
        positivity
      have hnorm := hsupp _ hvp
      have hspace : ‖v.1 - p.1‖ ≤ R := (norm_fst_le (v - p)).trans hnorm
      have heucl : vec3EuclideanNorm (v.1 - p.1) ≤ 2 * R := by
        calc
          vec3EuclideanNorm (v.1 - p.1) ≤ Real.sqrt 3 * ‖v.1 - p.1‖ :=
            vec3EuclideanNorm_le_sqrt_three_mul_norm _
          _ ≤ 2 * R := by
            have hsqrt : Real.sqrt 3 ≤ 2 := by
              nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
                Real.sqrt_nonneg 3]
            exact mul_le_mul hsqrt hspace (norm_nonneg _) (by norm_num)
      have htri : n ≤ vec3EuclideanNorm p.1 + 2 * R := by
        have hsplit : v.1 = p.1 + (v.1 - p.1) := by abel
        calc
          n = vec3EuclideanNorm (p.1 + (v.1 - p.1)) := by
            rw [← hsplit]
          _ ≤ vec3EuclideanNorm p.1 + vec3EuclideanNorm (v.1 - p.1) :=
            vec3EuclideanNorm_add_le _ _
          _ ≤ vec3EuclideanNorm p.1 + 2 * R := by linarith only [heucl]
      have hlarge : n / 2 ≤ rhoTwo p.1 p.2 := by
        unfold rhoTwo
        have := Real.sqrt_nonneg p.2
        linarith only [htri, hn, this]
      have hk : heatKernelPlus p ≤ 64000 / (1 + n) ^ 3 := by
        rw [show heatKernelPlus p = heatKernel p.1 p.2 from
          heatKernelPlus_eq_heatKernel p]
        calc
          heatKernel p.1 p.2 ≤ 1000 / rhoTwo p.1 p.2 ^ 3 := heatKernel_le_rho_inv_cube hp
          _ ≤ 1000 / (n / 2) ^ 3 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            exact pow_le_pow_left₀ (by positivity) hlarge 3
          _ ≤ 64000 / (1 + n) ^ 3 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have hn1 : 1 + n ≤ 2 * n := by linarith only [hn, hRone]
            have hcube : (1 + n) ^ 3 ≤ (2 * n) ^ 3 :=
              pow_le_pow_left₀ (by positivity) hn1 3
            nlinarith only [hcube]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (heatKernelPlus_nonneg p)]
      exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
    have hdom : Integrable (fun p : Vec3 × ℝ => (64000 / (1 + n) ^ 3) * |h (v - p)|) := by
      have hshift : Integrable (fun p : Vec3 × ℝ => |h (v - p)|) :=
        (hh.comp (continuous_const.sub continuous_id)).abs.integrable_of_hasCompactSupport
          (hc.comp_homeomorph (Homeomorph.subLeft v)).abs
      exact hshift.const_mul _
    rw [causalHeatConv_eq_integral, ← Real.norm_eq_abs]
    calc
      ‖∫ p : Vec3 × ℝ, heatKernelPlus p * h (v - p)‖ ≤
          ∫ p : Vec3 × ℝ, (64000 / (1 + n) ^ 3) * |h (v - p)| :=
        norm_integral_le_of_norm_le hdom (Eventually.of_forall hpoint)
      _ = 64000 * I / (1 + n) ^ 3 := by
        rw [integral_const_mul,
          integral_sub_left_eq_self (fun p : Vec3 × ℝ => |h p|) volume v]
        ring
  refine ⟨max (B * (2 * R) * (1 + 4 * R) ^ 3) (64000 * I), by positivity, ?_⟩
  intro v
  have hden : 0 < (1 + vec3EuclideanNorm v.1) ^ 3 := by
    have := vec3EuclideanNorm_nonneg v.1
    positivity
  by_cases hv : vec3EuclideanNorm v.1 < 4 * R
  · rw [le_div_iff₀ hden]
    have hpow : (1 + vec3EuclideanNorm v.1) ^ 3 ≤ (1 + 4 * R) ^ 3 :=
      pow_le_pow_left₀ (by have := vec3EuclideanNorm_nonneg v.1; positivity)
        (by linarith only [hv]) 3
    calc
      |causalHeatConv h v| * (1 + vec3EuclideanNorm v.1) ^ 3 ≤
          B * (2 * R) * (1 + 4 * R) ^ 3 :=
        mul_le_mul (hnear v) hpow hden.le (by positivity)
      _ ≤ _ := le_max_left _ _
  · calc
      |causalHeatConv h v| ≤ 64000 * I / (1 + vec3EuclideanNorm v.1) ^ 3 :=
        hfar v (le_of_not_gt hv)
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hden.le

end ESS

end
