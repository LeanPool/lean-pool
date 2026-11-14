/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# LocalizedBoundaryAsymptotics

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The elementary asymptotic behind localized conservativity

An exponential in the inward triadic distance dominates both the
volume-order prefactor and one logarithmic loss in the localized decay rate.
The proof compares everything with `(sqrt 3)^m` and keeps `exp` opaque.
-/

namespace DivergenceFormProcess.Form

open Filter Topology

noncomputable section

/-- A volume-order geometric prefactor times an exponential with one linear
loss in the exponent tends to zero along the triadic exhaustion. -/
theorem tendsto_triadicVolume_mul_exp_neg_triadic_div_linear
    (d : ℕ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    Tendsto (fun m : ℕ ↦
      C * ((m : ℝ) + 1) * ((3 : ℝ) ^ d) ^ m *
        Real.exp (-(c * (3 : ℝ) ^ m / ((m : ℝ) + 1))))
      atTop (nhds 0) := by
  let r : ℝ := Real.sqrt 3
  let K : ℝ := (r - 1)⁻¹ + 1
  have hr : 1 < r := by
    dsimp only [r]
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hK : 0 < K := by
    dsimp only [K]
    have : 0 < (r - 1)⁻¹ := inv_pos.mpr (sub_pos.mpr hr)
    positivity
  have hpowTop : Tendsto (fun m : ℕ ↦ r ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hr
  have hmajor : Tendsto (fun m : ℕ ↦
      C * K * (r ^ m) ^ (2 * d + 1) *
        Real.exp (-((c / K) * (r ^ m)))) atTop (nhds 0) := by
    have hb : 0 < c / K := div_pos hc hK
    have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((2 * d + 1 : ℕ) : ℝ) (c / K) hb
    have hcomp := hbase.comp hpowTop
    change Tendsto (fun m : ℕ ↦
      (r ^ m) ^ (((2 * d + 1 : ℕ) : ℝ)) *
        Real.exp (-(c / K) * (r ^ m))) atTop (nhds 0) at hcomp
    have heq : (fun m : ℕ ↦
        (r ^ m) ^ (((2 * d + 1 : ℕ) : ℝ)) *
          Real.exp (-(c / K) * (r ^ m))) =
        fun m : ℕ ↦ (r ^ m) ^ (2 * d + 1) *
          Real.exp (-((c / K) * (r ^ m))) := by
      funext m
      rw [Real.rpow_natCast]
      congr 2
      ring
    rw [heq] at hcomp
    simpa only [mul_assoc, mul_zero] using hcomp.const_mul (C * K)
  refine squeeze_zero' (Filter.Eventually.of_forall fun m ↦ ?_) ?_ hmajor
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (by positivity)) (pow_nonneg (by norm_num) m))
      (Real.exp_pos _).le
  · filter_upwards with m
    have hm : (m : ℝ) ≤ r ^ m / (r - 1) := m.cast_le_pow_div_sub hr
    have hone : 1 ≤ r ^ m := one_le_pow₀ hr.le
    have hmK : (m : ℝ) + 1 ≤ K * r ^ m := by
      dsimp only [K]
      calc
        (m : ℝ) + 1 ≤ r ^ m / (r - 1) + r ^ m := add_le_add hm hone
        _ = ((r - 1)⁻¹ + 1) * r ^ m := by
          rw [div_eq_inv_mul]
          ring
    have hmpos : 0 < (m : ℝ) + 1 := by positivity
    have hpowpos : 0 < r ^ m := pow_pos hr0 m
    have hrSq : r ^ 2 = 3 := by
      dsimp only [r]
      exact Real.sq_sqrt (by norm_num)
    have hthree : (3 : ℝ) ^ m = (r ^ m) ^ 2 := by
      calc
        (3 : ℝ) ^ m = (r ^ 2) ^ m := by rw [hrSq]
        _ = r ^ (2 * m) := (pow_mul _ _ _).symm
        _ = r ^ (m * 2) := by rw [Nat.mul_comm 2 m]
        _ = (r ^ m) ^ 2 := pow_mul _ _ _
    have hvolume : ((3 : ℝ) ^ d) ^ m = (r ^ m) ^ (2 * d) := by
      calc
        ((3 : ℝ) ^ d) ^ m = (3 : ℝ) ^ (d * m) := (pow_mul _ _ _).symm
        _ = (3 : ℝ) ^ (m * d) := by rw [Nat.mul_comm d m]
        _ = ((3 : ℝ) ^ m) ^ d := pow_mul _ _ _
        _ = ((r ^ m) ^ 2) ^ d := by rw [hthree]
        _ = (r ^ m) ^ (2 * d) := (pow_mul _ _ _).symm
    have hrate : (c / K) * r ^ m ≤ c * (3 : ℝ) ^ m / ((m : ℝ) + 1) := by
      rw [hthree]
      apply (le_div_iff₀ hmpos).2
      calc
        (c / K * r ^ m) * ((m : ℝ) + 1) ≤
            (c / K * r ^ m) * (K * r ^ m) :=
          mul_le_mul_of_nonneg_left hmK
            (mul_nonneg (div_nonneg hc.le hK.le) hpowpos.le)
        _ = c * (r ^ m) ^ 2 := by field_simp [hK.ne']
    have hexp : Real.exp (-(c * (3 : ℝ) ^ m / ((m : ℝ) + 1))) ≤
        Real.exp (-((c / K) * r ^ m)) :=
      Real.exp_le_exp.2 (neg_le_neg hrate)
    rw [hvolume]
    calc
      C * ((m : ℝ) + 1) * (r ^ m) ^ (2 * d) *
          Real.exp (-(c * (3 : ℝ) ^ m / ((m : ℝ) + 1))) ≤
        C * (K * r ^ m) * (r ^ m) ^ (2 * d) *
          Real.exp (-((c / K) * r ^ m)) := by
        gcongr
      _ = C * K * (r ^ m) ^ (2 * d + 1) *
          Real.exp (-((c / K) * r ^ m)) := by ring

end

end DivergenceFormProcess.Form
