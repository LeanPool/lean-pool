/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A smooth majorant for small translates of a compact cutoff

Continuity and compact support bound the translated cutoff and the exponential weight by one
smooth compact nonnegative function. The translation parameter satisfies `|t| ≤ 1`; every finite
dimension, including zero, and every direction are allowed. This supports the Hessian-increment
energy estimates without assuming a majorant or an energy bound.
-/

@[expose] public section

noncomputable section
open Set
open scoped Topology ContDiff
namespace FunctionalInequalities.Analysis

/-- A single smooth compact nonnegative testing weight for every small translate
of a compact cutoff, as needed to consume the original Hessian-increment estimate.
Continuity and compact support produce the majorant; no energy or cutoff-envelope
premise is assumed. Every finite dimension and arbitrary direction are included. -/
theorem exists_smooth_compact_translate_majorant {n : ℕ}
    {u χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∃ η : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ x, 0 ≤ η x) ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ x,
        (χ (x + t • v)) ^ 2 * Real.exp (u x) ≤ η x := by
  obtain ⟨r, hr⟩ := hχc.isBounded.subset_ball (0 : EuclideanSpace ℝ (Fin n))
  let R : ℝ := |r| + ‖v‖ + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  obtain ⟨C, hC⟩ :=
    hχc.exists_bound_of_continuousOn (hχ.pow 2).continuousOn
  obtain ⟨D, hD⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).exists_bound_of_continuousOn
      (Real.continuous_exp.comp hu).continuousOn
  let A : ℝ := |C| * |D|
  have hA : 0 ≤ A := mul_nonneg (abs_nonneg C) (abs_nonneg D)
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨R, R + 1, hR, lt_add_one R⟩
  refine ⟨fun x => A * b x, contDiff_const.mul b.contDiff, ?_, ?_, ?_⟩
  · exact b.hasCompactSupport.mul_left (f := fun _ => A)
  · intro x
    exact mul_nonneg hA (b.nonneg' x)
  · intro t ht x
    by_cases hz : χ (x + t • v) = 0
    · simpa only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul] using
        (mul_nonneg hA (b.nonneg' x))
    · have hy : x + t • v ∈ tsupport χ :=
        subset_tsupport χ (Function.mem_support.mpr hz)
      have hyr : ‖x + t • v‖ < r := by
        simpa only [Metric.mem_ball, dist_zero_right] using hr hy
      have htv : ‖t • v‖ ≤ ‖v‖ := by
        calc
          ‖t • v‖ = |t| * ‖v‖ := by
            rw [norm_smul, Real.norm_eq_abs]
          _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg v)
          _ = ‖v‖ := one_mul _
      have hxnorm : ‖x‖ ≤ R := by
        calc
          ‖x‖ = ‖(x + t • v) - t • v‖ := by
            rw [add_sub_cancel_right]
          _ ≤ ‖x + t • v‖ + ‖t • v‖ := norm_sub_le _ _
          _ ≤ |r| + ‖v‖ :=
            add_le_add (hyr.le.trans (le_abs_self r)) htv
          _ ≤ R := le_add_of_nonneg_right zero_le_one
      have hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hxnorm
      have hb : b x = 1 := b.one_of_mem_closedBall hx
      have hχbound : χ (x + t • v) ^ 2 ≤ |C| := by
        have hc := hC (x + t • v) hy
        change ‖χ (x + t • v) ^ 2‖ ≤ C at hc
        rw [Real.norm_eq_abs] at hc
        exact (le_abs_self _).trans (hc.trans (le_abs_self C))
      have hexp : Real.exp (u x) ≤ |D| := by
        have hd := hD x hx
        change ‖Real.exp (u x)‖ ≤ D at hd
        rw [Real.norm_eq_abs] at hd
        exact (le_abs_self _).trans (hd.trans (le_abs_self D))
      calc
        χ (x + t • v) ^ 2 * Real.exp (u x) ≤ |C| * |D| :=
          mul_le_mul hχbound hexp (Real.exp_pos _).le (abs_nonneg C)
        _ = A * b x := by rw [hb, mul_one]

end FunctionalInequalities.Analysis
