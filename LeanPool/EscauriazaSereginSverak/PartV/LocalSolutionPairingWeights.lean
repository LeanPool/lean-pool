/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Space-time weights in `L^{5/3}`

The spatial weight `(1 + |y|)^{-3}` lies in `L^{5/3}(ℝ³)` and the time weight
`r^{-1/2}` on `(0, τ)` lies in `L^{5/3}(ℝ)`, since `5 > 3` and `5/6 < 1`. A
product of such weights pairs integrably, by Hölder's inequality, with a
space-time function in `L^{5/2}`; this is the integrability used for the
forced heat response against a test field in `prop:pv-local-solution`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The spatial weight `(1 + |y|)^{-3}` lies in `L^{5/3}(ℝ³)`. -/
theorem memLp_one_add_norm_rpow_neg_three :
    MemLp (fun y : Vec3 => (1 + ‖y‖) ^ (-3 : ℝ)) (ENNReal.ofReal (5 / 3)) volume := by
  have hmeas : AEStronglyMeasurable (fun y : Vec3 => (1 + ‖y‖) ^ (-3 : ℝ)) volume :=
    (Measurable.aestronglyMeasurable (by fun_prop))
  rw [← integrable_norm_rpow_iff hmeas (by norm_num) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by norm_num)]
  have hint := integrable_one_add_norm (E := Vec3) (μ := volume) (r := 5) (by simp; norm_num)
  refine hint.congr (Eventually.of_forall fun y => ?_)
  have hpos : 0 ≤ 1 + ‖y‖ := by positivity
  simp only
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hpos _), ← Real.rpow_mul hpos]
  norm_num

/-- The time weight `r^{-1/2}` on `(0, τ)` lies in `L^{5/3}(ℝ)`. -/
theorem memLp_inv_sqrt_indicator {τ : ℝ} (hτ : 0 < τ) :
    MemLp (fun r : ℝ => (Ioo 0 τ).indicator (fun r => (Real.sqrt r)⁻¹) r)
      (ENNReal.ofReal (5 / 3)) volume := by
  have hmeas : AEStronglyMeasurable
      (fun r : ℝ => (Ioo 0 τ).indicator (fun r => (Real.sqrt r)⁻¹) r) volume :=
    (Measurable.indicator (by fun_prop) measurableSet_Ioo).aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hmeas (by norm_num) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by norm_num)]
  have hon : IntegrableOn (fun r : ℝ => r ^ (-(5 / 6) : ℝ)) (Ioo 0 τ) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hτ).2 (by norm_num)
  have hind : Integrable (fun r : ℝ => (Ioo 0 τ).indicator (fun r => r ^ (-(5 / 6) : ℝ)) r) :=
    (integrable_indicator_iff measurableSet_Ioo).2 hon
  refine hind.congr (Eventually.of_forall fun r => ?_)
  simp only
  by_cases hr : r ∈ Ioo 0 τ
  · rw [indicator_of_mem hr, indicator_of_mem hr]
    have hr0 : 0 ≤ r := hr.1.le
    rw [Real.norm_of_nonneg (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_neg hr0,
      ← Real.rpow_mul hr0]
    norm_num
  · rw [indicator_of_notMem hr, indicator_of_notMem hr, norm_zero,
      Real.zero_rpow (by norm_num)]

/-- A space-time function in `L^{5/2}` pairs integrably with the product of an
`L^{5/3}` time weight and the spatial weight `(1 + |y|)^{-3}`. -/
theorem integrable_mul_spaceTime_weight {g : Vec3 × ℝ → ℝ}
    (hg : MemLp g (ENNReal.ofReal (5 / 2)) volume) {b : ℝ → ℝ}
    (hb : MemLp b (ENNReal.ofReal (5 / 3)) volume) :
    Integrable (fun q : Vec3 × ℝ => g q * (b q.2 * (1 + ‖q.1‖) ^ (-3 : ℝ))) volume := by
  set a : Vec3 → ℝ := fun y => (1 + ‖y‖) ^ (-3 : ℝ) with hadef
  have ha := memLp_one_add_norm_rpow_neg_three
  have hWmeas : AEStronglyMeasurable (fun q : Vec3 × ℝ => b q.2 * a q.1)
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) :=
    (hb.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
      (ha.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  have hW : MemLp (fun q : Vec3 × ℝ => b q.2 * a q.1) (ENNReal.ofReal (5 / 3)) volume := by
    rw [Measure.volume_eq_prod]
    rw [← integrable_norm_rpow_iff hWmeas (by norm_num) ENNReal.ofReal_ne_top]
    have hA : Integrable (fun y : Vec3 => ‖a y‖ ^ (ENNReal.ofReal (5 / 3)).toReal) volume :=
      (integrable_norm_rpow_iff ha.aestronglyMeasurable (by norm_num) ENNReal.ofReal_ne_top).2 ha
    have hB : Integrable (fun s : ℝ => ‖b s‖ ^ (ENNReal.ofReal (5 / 3)).toReal) volume :=
      (integrable_norm_rpow_iff hb.aestronglyMeasurable (by norm_num) ENNReal.ofReal_ne_top).2 hb
    refine (hA.mul_prod hB).congr (Eventually.of_forall fun q => ?_)
    simp only
    rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_comm]
  have : ENNReal.HolderTriple (ENNReal.ofReal (5 / 2)) (ENNReal.ofReal (5 / 3)) 1 := by
    refine ⟨?_⟩
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  exact hg.integrable_mul hW

end ESS

end
