/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Reciprocal estimates retain the exact leading coefficients when solving
the normalized determinant inequality, even when its bracket is negative. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- If `a ≥ X (M - d) / ((r + 1) M)` with `X > 0`, `d ≥ 1` and `M ≥ 2 d`, then `a` is positive and
`1 / a ≤ (r + 1) / X * (1 + 2 d / M)`. -/
lemma auxiliary_reciprocal_bound {r d M X a : ℝ} (hr : 0 ≤ r) (hd : 1 ≤ d)
    (hM : 2 * d ≤ M) (hX : 0 < X)
    (ha : X * (M - d) / ((r + 1) * M) ≤ a) :
    0 < a ∧ 1 / a ≤ (r + 1) / X * (1 + 2 * d / M) := by
  have hd0 : 0 < d := by linarith
  have hM0 : 0 < M := by linarith
  have hr1 : 0 < r + 1 := by linarith
  have hMd : 0 < M - d := by linarith
  have hlow : 0 < X * (M - d) / ((r + 1) * M) := by positivity
  have ha0 : 0 < a := hlow.trans_le ha
  refine ⟨ha0, (div_le_iff₀ ha0).mpr ?_⟩
  have hprod : 1 ≤ (r + 1) / X * (1 + 2 * d / M) *
      (X * (M - d) / ((r + 1) * M)) := by
    field_simp
    nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr hM)]
  exact hprod.trans (mul_le_mul_of_nonneg_left ha (by positivity))

/-- If `0 < a ≤ X (M + r) / ((r + 1) M)` and `k ≥ 1 / (d (r + 1)) - 1 / M` is nonnegative, then
`k / a ≥ 1 / (d X) - (2 r + 1) / (X M)`. -/
lemma auxiliary_kernel_quotient_bound {r d M X a k : ℝ}
    (hr : 0 ≤ r) (hd : 1 ≤ d) (hM : 0 < M) (hX : 0 < X) (ha : 0 < a) (hk : 0 ≤ k)
    (hupper : a ≤ X * (M + r) / ((r + 1) * M))
    (hlower : 1 / (d * (r + 1)) - 1 / M ≤ k) :
    1 / (d * X) - (2 * r + 1) / (X * M) ≤ k / a := by
  have hd0 : 0 < d := by linarith
  have hr1 : 0 < r + 1 := by linarith
  let q := 1 / (d * X) - (2 * r + 1) / (X * M)
  change q ≤ k / a
  by_cases hq : q ≤ 0
  · exact hq.trans (div_nonneg hk ha.le)
  have hq0 : 0 ≤ q := le_of_not_ge hq
  apply (le_div_iff₀ ha).mpr
  have hh := mul_le_mul_of_nonneg_left hupper hq0
  have hcalc : q * (X * (M + r) / ((r + 1) * M)) ≤ 1 / (d * (r + 1)) - 1 / M := by
    dsimp only [q]
    field_simp
    have h1 := mul_nonneg (mul_nonneg hr hM.le) (show 0 ≤ d - 1 by linarith)
    have h2 := mul_nonneg (mul_nonneg hd0.le hr) (show 0 ≤ 2 * r + 1 by linarith)
    nlinarith
  exact hh.trans (hcalc.trans hlower)

/-- Solve the normalized inequality without imposing a sign on its bracket.
The small-height assumptions absorb both reciprocal errors into C(r). -/
theorem auxiliary_small_height_bracket_bound {r d M X a k u b l : ℝ}
    (hr : 0 ≤ r) (hd : 1 ≤ d) (hM : 2 * d ≤ M) (hX : 0 < X)
    (halow : X * (M - d) / ((r + 1) * M) ≤ a)
    (haup : a ≤ X * (M + r) / ((r + 1) * M))
    (hk : 0 ≤ k) (hklow : 1 / (d * (r + 1)) - 1 / M ≤ k)
    (hb : 0 ≤ b) (hl : 0 ≤ l) (hheight : l ≤ 2 * d * (r + 1) * b)
    (hscale : d * b ≤ X * M) (hcomparison : a * u ≤ b - k * l) :
    u ≤ (r + 1) / X * b - l / (d * X) + 4 * (r + 1) ^ 2 := by
  have hM0 : 0 < M := by linarith
  have hd0 : 0 < d := by linarith
  obtain ⟨ha, hrecip⟩ := auxiliary_reciprocal_bound hr hd hM hX halow
  have hquot := auxiliary_kernel_quotient_bound hr hd hM0 hX ha hk haup hklow
  have hu : u ≤ b / a - (k / a) * l := by
    have hh := (le_div_iff₀ ha).mpr (by nlinarith [hcomparison] : u * a ≤ b - k * l)
    convert hh using 1
    ring
  have hb' : b / a ≤ ((r + 1) / X * (1 + 2 * d / M)) * b := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
      mul_le_mul_of_nonneg_right hrecip hb
  have hl' := mul_le_mul_of_nonneg_right hquot hl
  have herr1 : 2 * (r + 1) * d * b / (X * M) ≤ 2 * (r + 1) := by
    apply (div_le_iff₀ (mul_pos hX hM0)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2 * (r + 1) by linarith)]
  have herr2 : (2 * r + 1) * l / (X * M) ≤ 2 * (2 * r + 1) * (r + 1) := by
    apply (div_le_iff₀ (mul_pos hX hM0)).mpr
    have hh := mul_le_mul_of_nonneg_left hheight (show 0 ≤ 2 * r + 1 by linarith)
    have hh' := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2 * (2 * r + 1) * (r + 1) by positivity)
    nlinarith
  have he : ((r + 1) / X * (1 + 2 * d / M)) * b -
      (1 / (d * X) - (2 * r + 1) / (X * M)) * l =
        (r + 1) / X * b - l / (d * X) +
          2 * (r + 1) * d * b / (X * M) + (2 * r + 1) * l / (X * M) := by ring
  have hbound : u ≤ ((r + 1) / X * (1 + 2 * d / M)) * b -
      (1 / (d * X) - (2 * r + 1) / (X * M)) * l := by
    nlinarith [hb', hl']
  rw [he] at hbound
  nlinarith

end
end CCDN
