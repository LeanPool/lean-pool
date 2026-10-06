/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedContraction

/-!
# Weighted Abel kernel in elapsed time

The exponentially weighted Stokes kernel has a bound independent of the
length of the time interval.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

/-- The elapsed-time Abel kernel has an exponentially weighted integral
bounded by the complete Gamma integral. -/
theorem regularisedAbelElapsedExpIntegral_le {lam T : ℝ}
    (hlam : 0 < lam) :
    ∫ τ in Ioc 0 T, τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ) ≤
      lam ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2) := by
  have hint := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := -(1 / 2 : ℝ)) (p := 1) (b := lam)
    (by norm_num) one_pos hlam
  have hval := integral_rpow_mul_exp_neg_mul_rpow
    (q := -(1 / 2 : ℝ)) (p := 1) (b := lam)
    one_pos (by norm_num) hlam
  simp only [Real.rpow_one, div_one, mul_one] at hint hval
  have hmono :
      ∫ τ in Ioc 0 T, τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ) ≤
        ∫ τ in Ioi 0, τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ) := by
    refine setIntegral_mono_set hint ?_ (Eventually.of_forall Ioc_subset_Ioi_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hτ) _) (Real.exp_pos _).le
  refine hmono.trans_eq ?_
  rw [hval]
  norm_num

end CKN.Leray

end
