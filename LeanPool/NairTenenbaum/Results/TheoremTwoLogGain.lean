/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.DivisorSums.GreatestPrimeFactorExponent

/-! # Absorbing the linear mass error and retaining an exponential gain -/

@[expose] public section

namespace NairTenenbaum

open Filter Real
open scoped Topology

theorem exists_divisorHit_exponent_margin_lt_one {α : ℝ} (hα : α < 2 - Real.log 4) :
    ∃ η : ℝ, Real.log 4 - 1 < η ∧ η < 1 ∧ α < 1 - η := by
  have hlog : Real.log 4 < 2 := by rw [Real.log_four_eq]; linarith [Real.log_two_lt_d9]
  obtain ⟨η, hη, hηupper⟩ := exists_between (show Real.log 4 - 1 < min 1 (1 - α) by
    exact lt_min (by linarith) (by linarith))
  exact ⟨η, hη, hηupper.trans_le (min_le_left _ _), by
    linarith [hηupper.trans_le (min_le_right _ _)]⟩

theorem eventually_divisorHit_log_gain {β c η B D : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hη : η < 1) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, ∀ H N : ℝ,
      c * x ^ β / (Real.log x) ^ η ≤ H → 0 < N → N ≤ 2 * x ^ β →
        B * x ^ β ≤ H * Real.log (x ^ β) / 2 ∧
        c * β / (4 * D) * (Real.log x) ^ (1 - η) ≤
          H * Real.log (x ^ β) / (2 * (D * N)) := by
  have Hpow : Tendsto (fun x : ℝ => (Real.log x) ^ (1 - η)) atTop atTop :=
    (tendsto_rpow_atTop (show 0 < 1 - η by linarith)).comp Real.tendsto_log_atTop
  filter_upwards [Hpow.eventually_ge_atTop (2 * B / (c * β)), eventually_gt_atTop (1 : ℝ)]
    with x hlarge hx H N hH hN hNbound
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hy : 0 < x ^ β := Real.rpow_pos_of_pos hx0 _
  have hly : 0 ≤ Real.log (x ^ β) := Real.log_nonneg (Real.one_le_rpow hx.le hβ.le)
  have Hmass : c * β * x ^ β * (Real.log x) ^ (1 - η) ≤ H * Real.log (x ^ β) := by
    have HM := mul_le_mul_of_nonneg_right hH hly
    have HE : c * x ^ β / (Real.log x) ^ η * Real.log (x ^ β) =
        c * β * x ^ β * (Real.log x) ^ (1 - η) := by
      rw [Real.log_rpow hx0, Real.rpow_sub hl, Real.rpow_one]
      ring
    rwa [HE] at HM
  have hmain : 2 * B ≤ c * β * (Real.log x) ^ (1 - η) := by
    have H := (div_le_iff₀ (mul_pos hc hβ)).mp hlarge
    nlinarith
  constructor
  · have H := mul_le_mul_of_nonneg_right hmain hy.le
    nlinarith
  · apply (le_div_iff₀ (by positivity : 0 < 2 * (D * N))).mpr
    have HN := mul_le_mul_of_nonneg_left hNbound
      (show 0 ≤ c * β / 2 * (Real.log x) ^ (1 - η) by positivity)
    have HE : c * β / (4 * D) * (Real.log x) ^ (1 - η) * (2 * (D * N)) =
        c * β / 2 * (Real.log x) ^ (1 - η) * N := by
      field_simp
      ring
    rw [HE]
    nlinarith

end NairTenenbaum
