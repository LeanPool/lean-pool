/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.AlphaShiftedWeakSolution

/-!
# ScalarL2Order

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Internal scalar L² order identities

This module collects elementary scalar `L²` identities used by the
divergence-form comparison and positivity arguments.
-/

namespace DivergenceFormProcess.Form.Internal

open HCPolySupport MeasureTheory
open scoped RealInnerProductSpace

variable {d : ℕ} {U : Set (Vec d)}

/-- The scalar `L²` inner product of almost-everywhere nonnegative functions
is nonnegative. -/
theorem scalarL2_inner_nonneg_of_ae_nonneg
    (f g : ScalarL2 U)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x)
    (hg : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ g x) :
    0 ≤ inner ℝ f g := by
  rw [scalarInner_eq_integral]
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [hf, hg] with x hfx hgx
  exact mul_nonneg hfx hgx

/-- Ordered scalar `L²` functions have nonpositive difference pairing against
an almost-everywhere nonnegative function. -/
theorem scalarL2_inner_sub_nonpos_of_ae_le
    (f g p : ScalarL2 U)
    (hfg : ∀ᵐ x ∂volumeMeasureOn U, f x ≤ g x)
    (hp : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ p x) :
    inner ℝ (f - g) p ≤ 0 := by
  rw [scalarInner_eq_integral]
  apply MeasureTheory.integral_nonpos_of_ae
  filter_upwards [hfg, hp, MeasureTheory.Lp.coeFn_sub f g] with x hfgx hpx hsub
  rw [hsub]
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hfgx) hpx

/-- Pairing with the positive part equals the positive part's self-pairing. -/
theorem scalarL2_inner_eq_self_of_ae_eq_max
    (z p : ScalarL2 U)
    (hp : ∀ᵐ x ∂volumeMeasureOn U, p x = max (z x) 0) :
    inner ℝ z p = inner ℝ p p := by
  rw [scalarInner_eq_integral, scalarInner_eq_integral]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hp] with x hpx
  rw [hpx]
  by_cases hx : 0 ≤ z x
  · rw [max_eq_left hx]
  · rw [max_eq_right (le_of_not_ge hx)]
    ring

/-- Pairing with the negative part is the negative of that part's
self-pairing. -/
theorem scalarL2_inner_eq_neg_self_of_ae_eq_max_neg
    (u v : ScalarL2 U)
    (hv : ∀ᵐ x ∂volumeMeasureOn U, v x = max (-u x) 0) :
    inner ℝ u v = -inner ℝ v v := by
  rw [scalarInner_eq_integral, scalarInner_eq_integral,
    ← MeasureTheory.integral_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hv] with x hvx
  rw [hvx]
  by_cases hx : 0 ≤ u x
  · rw [max_eq_right]
    · ring
    · simpa only [neg_nonpos] using hx
  · have hx' : 0 ≤ -u x := neg_nonneg.mpr (le_of_not_ge hx)
    rw [max_eq_left hx']
    ring

end DivergenceFormProcess.Form.Internal
