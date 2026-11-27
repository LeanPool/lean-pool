/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ExponentialMultiplication

/-!
# Positivity, full domain and exact square of exponential multiplication

The square-root graph equality includes the intermediate L2 vector. Its
existence follows from the actual bound exp(t/2) ≤ 1+exp(t); no domain
inclusion is assumed. This applies to arbitrary measures and measurable
real weights, including the unbounded rapidity-frequency exponent.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem exponentialMultiplication_mem_domain (w : α → ℝ) (hw : Measurable w)
    (f : Lp ℂ 2 μ) :
    f ∈ (exponentialMultiplication μ w hw).domain ↔
      MemLp (fun x => (Real.exp (w x) : ℂ) * f x) 2 μ := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact MemLp.ae_eq ((exponentialMultiplication_mem_graph μ w hw f g).mp hg) (Lp.memLp g)
  · intro h
    refine ⟨h.toLp _, (exponentialMultiplication_mem_graph μ w hw f _).mpr ?_⟩
    exact h.coeFn_toLp

theorem exponentialMultiplication_dense_domain (w : α → ℝ) (hw : Measurable w) :
    Dense ((exponentialMultiplication μ w hw).domain : Set (Lp ℂ 2 μ)) :=
  selfAdjoint_denseRange_of_injective (exponentialResolvent μ w hw)
    (exponentialResolvent_isSelfAdjoint μ w hw) (exponentialResolvent_injective μ w hw)

/-- Positivity on the full maximal domain, not just on compact test vectors. -/
theorem exponentialMultiplication_inner_nonneg (w : α → ℝ) (hw : Measurable w)
    (f g : Lp ℂ 2 μ) (hfg : (f, g) ∈ (exponentialMultiplication μ w hw).graph) :
    0 ≤ (inner ℂ f g).re := by
  have heq := (exponentialMultiplication_mem_graph μ w hw f g).mp hfg
  rw [L2.inner_def, ← RCLike.re_eq_complex_re,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) f g)]
  apply integral_nonneg_of_ae
  filter_upwards [heq] with x hx
  rw [hx, show (Real.exp (w x) : ℂ) * f x = (Real.exp (w x) : ℂ) • f x from rfl,
    inner_smul_right, inner_self_eq_norm_sq_to_K]
  change 0 ≤ ((Real.exp (w x) : ℂ) * ((‖f x‖ : ℂ) ^ 2)).re
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

theorem exponentialMultiplication_resolvent (w : α → ℝ) (hw : Measurable w)
    (x y : Lp ℂ 2 μ) :
    (∃ hy : y ∈ (exponentialMultiplication μ w hw).domain,
      y + exponentialMultiplication μ w hw ⟨y, hy⟩ = x) ↔
        exponentialResolvent μ w hw x = y := by
  let R := exponentialResolvent μ w hw
  have he : R + (1 - R) = 1 := by abel
  have hQ : IsUnit (R + (1 - R)) := by rw [he]; exact isUnit_one
  have h := boundedRatio_resolvent_iff R (1 - R) (exponentialResolvent_injective μ w hw) hQ x y
  simpa only [exponentialMultiplication, R, he, Ring.inverse_one, mul_one] using h

theorem exp_half_sq (t : ℝ) : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem exp_half_le_one_add_exp (t : ℝ) : Real.exp (t / 2) ≤ 1 + Real.exp t := by
  have h := exp_half_sq t
  nlinarith [sq_nonneg (Real.exp (t / 2) - 1 / 2)]

/-- The full graph of the exponential is exactly the composition of two
maximal half-exponential graphs. -/
theorem exponentialMultiplication_graph_half_square (w : α → ℝ) (hw : Measurable w)
    (f g : Lp ℂ 2 μ) :
    (f, g) ∈ (exponentialMultiplication μ w hw).graph ↔
      ∃ h : Lp ℂ 2 μ,
        (f, h) ∈ (exponentialMultiplication μ (fun x => w x / 2) (hw.div_const 2)).graph ∧
        (h, g) ∈ (exponentialMultiplication μ (fun x => w x / 2) (hw.div_const 2)).graph := by
  simp only [exponentialMultiplication_mem_graph]
  constructor
  · intro hfg
    have hcoef : Measurable (fun x => (Real.exp (w x / 2) : ℂ)) := by fun_prop
    have hmhalf : MemLp (fun x => (Real.exp (w x / 2) : ℂ) * f x) 2 μ := by
      apply ((Lp.memLp f).norm.add (Lp.memLp g).norm).mono'
        (hcoef.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
      filter_upwards [hfg] with x hx
      have hgnorm : ‖g x‖ = Real.exp (w x) * ‖f x‖ := by
        rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      change ‖(Real.exp (w x / 2) : ℂ) * f x‖ ≤ ‖f x‖ + ‖g x‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h := mul_le_mul_of_nonneg_right (exp_half_le_one_add_exp (w x)) (norm_nonneg (f x))
      nlinarith
    refine ⟨hmhalf.toLp _, hmhalf.coeFn_toLp, ?_⟩
    filter_upwards [hfg, hmhalf.coeFn_toLp] with x hx hh
    rw [hx, hh]
    have hc : (Real.exp (w x / 2) : ℂ) * (Real.exp (w x / 2) : ℂ) = (Real.exp (w x) : ℂ) :=
      by exact_mod_cast exp_half_sq (w x)
    rw [← mul_assoc, hc]
  · rintro ⟨h, hfh, hhg⟩
    filter_upwards [hfh, hhg] with x hx hy
    rw [hy, hx, ← mul_assoc]
    have hc : (Real.exp (w x / 2) : ℂ) * (Real.exp (w x / 2) : ℂ) = (Real.exp (w x) : ℂ) :=
      by exact_mod_cast exp_half_sq (w x)
    rw [hc]

end VacuumBellSeparation
