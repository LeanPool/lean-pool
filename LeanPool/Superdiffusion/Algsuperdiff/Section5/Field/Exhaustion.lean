/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.Growth

/-!
# Exhaustion

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A spatial exhaustion function for the stream field

The reciprocal affine norm gives a positive, one-Lipschitz exhaustion of
`Vec d`.  Its compact superlevel sets control escape to spatial infinity.  A
radius amplification records the extra Euclidean separation forced when a
distant point remains in a sufficiently high exhaustion superlevel set.

## Main definitions

* `streamExhaustionRho` — the exhaustion `(1 + ‖x‖)⁻¹`.
* `streamExhaustionAmp` — the amplified radius used by spatial tail bounds.
-/

namespace Algsuperdiff.Section5.Field

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-- The reciprocal affine sup norm used to exhaust `Vec d`. -/
def streamExhaustionRho (x : Vec d) : ℝ := (1 + ‖x‖)⁻¹

theorem continuous_streamExhaustionRho : Continuous (streamExhaustionRho (d := d)) := by
  apply Continuous.inv₀
  · exact continuous_const.add continuous_norm
  · intro x hx
    have : 0 < (1 : ℝ) + ‖x‖ := by positivity
    exact this.ne' hx

theorem streamExhaustionRho_pos (x : Vec d) : 0 < streamExhaustionRho x := by
  unfold streamExhaustionRho
  positivity

theorem streamExhaustionRho_le_one (x : Vec d) : streamExhaustionRho x ≤ 1 := by
  unfold streamExhaustionRho
  exact (inv_le_one₀ (by positivity)).2 (le_add_of_nonneg_right (norm_nonneg x))

theorem lipschitzWith_streamExhaustionRho :
    LipschitzWith 1 (streamExhaustionRho (d := d)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hx : 0 < (1 : ℝ) + ‖x‖ := by positivity
  have hy : 0 < (1 : ℝ) + ‖y‖ := by positivity
  have hden : 1 ≤ ((1 : ℝ) + ‖x‖) * (1 + ‖y‖) := by
    nlinarith only [norm_nonneg x, norm_nonneg y]
  have hnorm : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  rw [Real.dist_eq]
  unfold streamExhaustionRho
  rw [inv_sub_inv hx.ne' hy.ne', abs_div, abs_mul, abs_of_pos hx, abs_of_pos hy]
  have hdiv : |‖y‖ - ‖x‖| / (((1 : ℝ) + ‖x‖) * (1 + ‖y‖)) ≤ |‖y‖ - ‖x‖| :=
    div_le_self (abs_nonneg _) hden
  have hxy : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    rw [abs_sub_comm]
    exact hnorm
  simpa only [add_sub_add_left_eq_sub, NNReal.coe_one, one_mul, dist_eq_norm] using
    hdiv.trans hxy

theorem isCompact_streamExhaustionRho_superlevel {eps : ℝ} (heps : 0 < eps) :
    IsCompact {x : Vec d | eps ≤ streamExhaustionRho x} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le continuous_const continuous_streamExhaustionRho
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨eps⁻¹, fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hden : 0 < (1 : ℝ) + ‖x‖ := by positivity
    have hmul : eps * (1 + ‖x‖) ≤ 1 := by
      change eps ≤ ((1 : ℝ) + ‖x‖)⁻¹ at hx
      rw [inv_eq_one_div] at hx
      exact (le_div_iff₀ hden).mp hx
    rw [inv_eq_one_div]
    apply (le_div_iff₀ heps).2
    nlinarith only [hmul, heps, norm_nonneg x]

/-- Increase a radius when its exhaustion scale forces additional separation. -/
def streamExhaustionAmp (x : Vec d) (r : ℝ) : ℝ :=
  if 4 * streamExhaustionRho x ≤ r then max r (2 / 3 * (1 + ‖x‖)) else r

theorem streamExhaustionAmp_pos {x : Vec d} {r : ℝ} (hr : 0 < r) :
    0 < streamExhaustionAmp x r := by
  rw [streamExhaustionAmp]
  split_ifs
  · exact hr.trans_le (le_max_left _ _)
  · exact hr

/-- The amplified radius of an exhaustion tail: a point Euclidean-far from `x`
and in the superlevel set `{rho ≥ r - rho x}` is at distance at least the
amplified radius from `x`. -/
theorem streamExhaustionAmp_le_dist {x z : Vec d} {r : ℝ}
    (hdist : r ≤ dist z x) (hlevel : r - streamExhaustionRho x ≤ streamExhaustionRho z) :
    streamExhaustionAmp x r ≤ dist z x := by
  rw [streamExhaustionAmp]
  split_ifs with hamp
  · rw [max_le_iff]
    refine ⟨hdist, ?_⟩
    have hrho : 3 * streamExhaustionRho x ≤ streamExhaustionRho z := by
      linarith only [hamp, hlevel]
    have hx : 0 < (1 : ℝ) + ‖x‖ := by positivity
    have hz : 0 < (1 : ℝ) + ‖z‖ := by positivity
    have hnorm : 3 * (1 + ‖z‖) ≤ 1 + ‖x‖ := by
      change 3 * ((1 : ℝ) + ‖x‖)⁻¹ ≤ ((1 : ℝ) + ‖z‖)⁻¹ at hrho
      have hdiv : 3 / (1 + ‖x‖) ≤ 1 / (1 + ‖z‖) := by
        simpa only [div_eq_mul_inv, one_mul] using hrho
      simpa only [one_mul] using (div_le_div_iff₀ hx hz).mp hdiv
    have hreverse : ‖x‖ - ‖z‖ ≤ dist z x := by
      rw [dist_eq_norm, ← norm_neg (z - x), neg_sub]
      exact norm_sub_norm_le x z
    linarith only [hnorm, hreverse]
  · exact hdist

end

end Algsuperdiff.Section5.Field
