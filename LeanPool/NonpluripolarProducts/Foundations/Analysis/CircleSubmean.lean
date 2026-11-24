/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Plurisubharmonic
public import Mathlib.Tactic.Linarith

/-!
# The deficit definition and the ordinary real circle average

For real-valued circle-integrable functions bounded above on the circle,
the nonnegative extended integral in the PSH definition computes the usual
submean inequality. This is the interface to ordinary differential calculus.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem circleDeficit_coe_eq {u : E → ℝ} (x v : E) (r C : ℝ)
    (hu : IntervalIntegrable (fun t : ℝ => u (x + circleMap 0 r t • v))
      volume 0 (2 * Real.pi))
    (hC : ∀ t : ℝ, u (x + circleMap 0 r t • v) ≤ C) :
    circleDeficit (fun y => (u y : EReal)) x v r C =
      ENNReal.ofReal ((2 * Real.pi) * C -
        ∫ t in 0..2 * Real.pi, u (x + circleMap 0 r t • v)) := by
  have hp : 0 ≤ 2 * Real.pi := by positivity
  have hfi : IntegrableOn (fun t : ℝ => C - u (x + circleMap 0 r t • v))
      (Ioc 0 (2 * Real.pi)) := (intervalIntegrable_const.sub hu).1
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
      (fun t : ℝ => C - u (x + circleMap 0 r t • v)) :=
    ae_of_all _ (fun t => sub_nonneg.mpr (hC t))
  simp only [circleDeficit, ← EReal.coe_sub, EReal.real_coe_toENNReal]
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hnn,
    ← intervalIntegral.integral_of_le hp,
    intervalIntegral.integral_sub intervalIntegrable_const hu,
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

/-- For finite values, the extended-real test is exactly the usual mean inequality. -/
theorem circleDeficit_coe_le_iff {u : E → ℝ} (x v : E) (r C : ℝ)
    (hu : IntervalIntegrable (fun t : ℝ => u (x + circleMap 0 r t • v))
      volume 0 (2 * Real.pi))
    (hC : ∀ t : ℝ, u (x + circleMap 0 r t • v) ≤ C) (hxC : u x ≤ C) :
    (circleDeficit (fun y => (u y : EReal)) x v r C ≤
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - (u x : EReal)).toENNReal) ↔
    u x ≤ Real.circleAverage (fun z : ℂ => u (x + z • v)) 0 r := by
  have hp : 0 < 2 * Real.pi := by positivity
  rw [circleDeficit_coe_eq x v r C hu hC, ← EReal.coe_sub,
    EReal.real_coe_toENNReal, ← ENNReal.ofReal_mul hp.le,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hp.le (sub_nonneg.mpr hxC))]
  simp only [Real.circleAverage, smul_eq_mul]
  rw [← div_eq_inv_mul, le_div_iff₀ hp]
  constructor <;> intro h <;> nlinarith

/-- A continuous real potential satisfying ordinary circle submean inequalities
satisfies the extended-real disc criterion. -/
theorem discPshOn_of_circleAverage {u : E → ℝ} {U : Set E} (hu : Continuous u)
    (hmean : ∀ (x v : E) (r : ℝ), 0 < r → affineClosedDisc x v r ⊆ U →
      u x ≤ Real.circleAverage (fun z : ℂ => u (x + z • v)) 0 r) :
    DiscPshOn (fun y => (u y : EReal)) U := by
  refine ⟨fun _ _ => EReal.coe_ne_top _,
    (continuous_coe_real_ereal.comp hu).upperSemicontinuous.upperSemicontinuousOn U, ?_⟩
  intro x v r hr hD C hC
  have hcirc : Continuous (fun t : ℝ => u (x + circleMap 0 r t • v)) := by fun_prop
  apply (circleDeficit_coe_le_iff x v r C (hcirc.intervalIntegrable _ _)
    (fun t => EReal.coe_le_coe_iff.mp (hC _ (circle_mem_affineClosedDisc x v hr.le t)))
    (EReal.coe_le_coe_iff.mp (hC x (center_mem_affineClosedDisc x v hr.le)))).mpr
  exact hmean x v r hr hD

end SGPT.Foundations.Analysis
