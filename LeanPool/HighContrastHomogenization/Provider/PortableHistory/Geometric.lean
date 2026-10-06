/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Moments

/-!
# High-contrast homogenization: Provider.PortableHistory.Geometric

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The geometric weight of the nonlinear rows

The nonlinear rows of `e.scale.selection.complete.profile` carry the weights
`3^{-a(T-1-j)}` over `j` in a bounded range below `T`.  Two of the estimates of
`p.fixed.geometry.one.grid.propagation` — the additive part of the transported
nonlinear row in `e.fixed.geometry.profile.majorization`, and the additive part
of the contraction of the mean terms over one service step — bound the total
weight by the geometric sum `(1 - 3^{-a})^{-1}`, uniformly in the endpoints.

The exponents are the nonnegative integers `T - 1 - j`, so the weight is the
`(T-1-j)`-th power of the ratio `3^{-a} < 1`, and the range is in bijection with
an initial segment of the naturals.
-/

namespace HCPolySupport
namespace HighContrast
namespace PortableHistory

noncomputable section

/-! ## The ratio -/

/-- The geometric ratio of the nonlinear rows is strictly between zero and
one. -/
theorem geom_ratio_lt_one {a : ℝ} (ha : 0 < a) : (3 : ℝ) ^ (-a) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_iff_pos.mpr ha)

/-- The geometric ratio of the nonlinear rows is positive. -/
theorem geom_ratio_pos (a : ℝ) : (0 : ℝ) < (3 : ℝ) ^ (-a) :=
  Real.rpow_pos_of_pos (by norm_num) _

/-! ## The total weight -/

/-- The weights of a nonlinear row form an initial segment of a geometric
progression. -/
theorem sum_geom_Ico_eq (a : ℝ) (b T : ℤ) :
    ∑ j ∈ Finset.Ico b T, (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) =
      ∑ k ∈ Finset.range (T - b).toNat, ((3 : ℝ) ^ (-a)) ^ k := by
  refine Finset.sum_nbij' (fun x : ℤ => (T - 1 - x).toNat) (fun k : ℕ => T - 1 - (k : ℤ))
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_Ico] at hx
    rw [Finset.mem_range]
    omega
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Ico]
    omega
  · intro x hx
    rw [Finset.mem_Ico] at hx
    omega
  · intro k hk
    rw [Finset.mem_range] at hk
    omega
  · intro x hx
    rw [Finset.mem_Ico] at hx
    have hcast : (((T - 1 - x).toNat : ℤ) : ℝ) = (T : ℝ) - 1 - (x : ℝ) := by
      have : ((T - 1 - x).toNat : ℤ) = T - 1 - x := Int.toNat_of_nonneg (by omega)
      rw [this]
      push_cast
      ring
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-a)) ((T - 1 - x).toNat), ← Real.rpow_mul (by norm_num)]
    congr 1
    rw [← hcast]
    push_cast
    ring

/-- **The total geometric weight of a nonlinear row.**  The weights
`3^{-a(T-1-j)}` over a bounded range below `T` sum to at most `(1 - 3^{-a})^{-1}`,
uniformly in the endpoints. -/
theorem sum_geom_Ico_le {a : ℝ} (ha : 0 < a) (b T : ℤ) :
    ∑ j ∈ Finset.Ico b T, (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) ≤
      1 / (1 - (3 : ℝ) ^ (-a)) := by
  have hr1 : (3 : ℝ) ^ (-a) < 1 := geom_ratio_lt_one ha
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-a) := geom_ratio_pos a
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-a) := by linarith only [hr1]
  have hpow : (0 : ℝ) ≤ ((3 : ℝ) ^ (-a)) ^ (T - b).toNat := pow_nonneg hr0.le _
  rw [sum_geom_Ico_eq, geom_sum_eq (ne_of_lt hr1)]
  have heq : (((3 : ℝ) ^ (-a)) ^ (T - b).toNat - 1) / ((3 : ℝ) ^ (-a) - 1) =
      (1 - ((3 : ℝ) ^ (-a)) ^ (T - b).toNat) / (1 - (3 : ℝ) ^ (-a)) := by
    rw [div_eq_div_iff (by linarith only [hden]) (ne_of_gt hden)]
    ring
  rw [heq]
  gcongr
  linarith only [hpow]

end

end PortableHistory
end HighContrast
end HCPolySupport
