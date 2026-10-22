/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Real

/-! Sharp leading constant for sums of surface standard-monomial degrees.
The numerical argument retains 2/3 of the cutoff in the weighted rank. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset

private lemma sum_successor_squares_lower (M : ℕ) :
    (M : ℝ) ^ 3 / 3 ≤ ∑ i ∈ range M, ((i : ℝ) + 1) ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ]
    push_cast
    nlinarith [sq_nonneg (M : ℝ), Nat.cast_nonneg (α := ℝ) M]

/-- If `H k ≥ d * (k - d + 1) ^ 2 / 2` for all `k ≥ d`, then for `M ≥ d` the prefix sum
`∑ k < M, H k` is at least `d * (M - d) ^ 3 / 6`. -/
theorem surface_rank_prefix_sum_lower (H : ℕ → ℕ) {d M : ℕ} (hdM : d ≤ M)
    (hlower : ∀ k, d ≤ k →
      (d : ℝ) * ((k : ℝ) - d + 1) ^ 2 / 2 ≤ H k) :
    (d : ℝ) * ((M : ℝ) - d) ^ 3 / 6 ≤ ∑ k ∈ range M, (H k : ℝ) := by
  have hsum : (d : ℝ) / 2 * ∑ i ∈ range (M - d), ((i : ℝ) + 1) ^ 2 ≤
      ∑ i ∈ range (M - d), (H (d + i) : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    have h := hlower (d + i) (by omega)
    push_cast at h
    convert h using 1
    ring
  have hnum := mul_le_mul_of_nonneg_left (sum_successor_squares_lower (M - d))
    (show 0 ≤ (d : ℝ) / 2 by positivity)
  rw [Nat.cast_sub hdM] at hnum
  have hprefix : (∑ i ∈ range (M - d), (H (d + i) : ℝ)) ≤
      ∑ k ∈ range M, (H k : ℝ) := by
    conv_rhs => rw [show M = d + (M - d) by omega, sum_range_add]
    exact le_add_of_nonneg_left (sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  convert (hnum.trans hsum).trans hprefix using 1
  ring

/-- Let `R ≥ 0` satisfy `d * R ^ 2 = 2 * s` and `M - d ≤ R ≤ M + 2`, where `0 < d ≤ M` and
`s ≥ 0`. If `W + d * (M - d) ^ 3 / 6 ≤ M * s`, then `W ≤ (2 / 3) * s * R + (2 * d + 2) * s`. -/
theorem surface_weight_root_bound {d M s W : ℝ}
    (hd : 0 < d) (hM : d ≤ M) (hs : 0 ≤ s) (R : ℝ) (hR : 0 ≤ R)
    (hroot : d * R ^ 2 = 2 * s)
    (hlo : M - d ≤ R) (hhi : R ≤ M + 2)
    (hweight : W + d * (M - d) ^ 3 / 6 ≤ M * s) :
    W ≤ (2 / 3 : ℝ) * s * R + (2 * d + 2) * s := by
  have ht : 0 ≤ M - d := sub_nonneg.mpr hM
  have htR : (M - d) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ ht hlo 2
  have hprod : R * (M - d) ≤ R ^ 2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hlo hR
  have hdiff : 0 ≤ R - (M - d) := sub_nonneg.mpr hlo
  have hfactor : R ^ 2 + R * (M - d) + (M - d) ^ 2 ≤ 3 * R ^ 2 := by
    linarith only [htR, hprod]
  have hcube : R ^ 3 - (M - d) ^ 3 ≤ 3 * (d + 2) * R ^ 2 := by
    calc
      _ = (R - (M - d)) * (R ^ 2 + R * (M - d) + (M - d) ^ 2) := by ring
      _ ≤ (R - (M - d)) * (3 * R ^ 2) :=
        mul_le_mul_of_nonneg_left hfactor hdiff
      _ ≤ (d + 2) * (3 * R ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have hc := mul_le_mul_of_nonneg_left hcube hd.le
  have hr3 : d * R ^ 3 = 2 * s * R := by
    calc
      _ = (d * R ^ 2) * R := by ring
      _ = _ := congrArg (fun x : ℝ => x * R) hroot
  have hr2 : 3 * d * (d + 2) * R ^ 2 = 6 * (d + 2) * s := by
    calc
      _ = 3 * (d + 2) * (d * R ^ 2) := by ring
      _ = 3 * (d + 2) * (2 * s) := congrArg (fun x : ℝ => 3 * (d + 2) * x) hroot
      _ = _ := by ring
  have hMs : M * s ≤ (R + d) * s :=
    mul_le_mul_of_nonneg_right (by linarith) hs
  nlinarith only [hweight, hc, hr3, hr2, hMs]

end
end CCDN
