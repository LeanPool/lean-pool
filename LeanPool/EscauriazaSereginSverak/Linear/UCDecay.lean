/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoff
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponential decay at the initial time

Gaussian decay dominates every inverse power of time, as used in
`lem:uc-gaussian` and `thm:uc`.
-/

public section


open Filter Set

noncomputable section

namespace ESS

/-- A positive Gaussian exponent dominates any inverse power as time tends
to zero from above. -/
theorem uc_exp_dominates_inverse_power (b p : ℝ) (hb : 0 < b) :
    Tendsto (fun t : ℝ => Real.rpow t (-p) * Real.exp (-(b / t)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p b hb).comp
    tendsto_inv_nhdsGT_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t _ht
  change t⁻¹ ^ p * Real.exp (-b * t⁻¹) =
    t ^ (-p) * Real.exp (-(b / t))
  rw [Real.rpow_neg_eq_inv_rpow]
  simp only [div_eq_mul_inv, neg_mul]

end ESS
