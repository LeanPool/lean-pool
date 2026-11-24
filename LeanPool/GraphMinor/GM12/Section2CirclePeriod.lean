/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Field.Periodic

/-!
# One real period parametrizes the circle once

The trace definition of XII, page 243, uses a period of a closed curve.
The map `t ↦ exp(2πt)` is periodic with period one and restricts to a
bijection from every half-open interval of length one onto the circle.
This identifies its real-parameter vertex hits with its circle hits.
-/

public section

namespace GraphMinor.GM12

open Set

/-- The circle parameter used by XII's periodic curve has period one. -/
theorem circle_parameter_periodic :
    Function.Periodic (fun t : ℝ => Circle.exp (2 * Real.pi * t)) 1 := by
  intro t
  change Circle.exp (2 * Real.pi * (t + 1)) = Circle.exp (2 * Real.pi * t)
  rw [mul_add, mul_one]
  exact Circle.periodic_exp _

/-- The real circle parameter is injective on each half-open period. -/
theorem circle_parameter_injOn (a : ℝ) :
    InjOn (fun t : ℝ => Circle.exp (2 * Real.pi * t)) (Ico a (a + 1)) := by
  intro x hx y hy hxy
  have hpos : 0 < 2 * Real.pi := Real.two_pi_pos
  have hmem : ∀ t ∈ Ico a (a + 1),
      2 * Real.pi * t ∈ Ico (2 * Real.pi * a) (2 * Real.pi * (a + 1)) := by
    intro t ht
    exact ⟨mul_le_mul_of_nonneg_left ht.1 hpos.le, mul_lt_mul_of_pos_left ht.2 hpos⟩
  have heq := Circle.exp_injOn_Ico (a := 2 * Real.pi * a) (b := 2 * Real.pi * (a + 1))
    (by ring_nf; exact le_rfl) (hmem x hx) (hmem y hy) hxy
  exact mul_left_cancel₀ (ne_of_gt hpos) heq

/-- Each half-open real period parametrizes the whole circle exactly once. -/
theorem circle_parameter_bijOn (a : ℝ) :
    BijOn (fun t : ℝ => Circle.exp (2 * Real.pi * t)) (Ico a (a + 1)) univ := by
  refine ⟨fun _ _ => mem_univ _, circle_parameter_injOn a, ?_⟩
  intro z _
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective z
  let t := θ / (2 * Real.pi)
  have ht : Circle.exp (2 * Real.pi * t) = z := by
    rw [mul_div_cancel₀ _ (ne_of_gt Real.two_pi_pos)]
    exact hθ
  obtain ⟨s, hs, hts⟩ := circle_parameter_periodic.exists_mem_Ico (by norm_num : (0 : ℝ) < 1) t a
  exact ⟨s, hs, hts.symm.trans ht⟩

end GraphMinor.GM12
