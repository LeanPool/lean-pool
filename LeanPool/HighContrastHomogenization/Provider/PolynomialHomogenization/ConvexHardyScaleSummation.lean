/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Max

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyScaleSummation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Dyadic scale summation for convex-domain Hardy chains

The radius cutoff on a chain link turns a growing dyadic scale factor into a
finite geometric head.  The remaining distance from the initial link carries
a decaying geometric tail.  Their product is bounded uniformly in the
physical radius and in the reference interior-ball radius.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

open scoped ENNReal

/-- The dyadic radius at depth `n` below a reference radius. -/
@[expose]
def convexHardyDyadicRadius (rho : ℝ) (n : ℕ) : ℝ :=
  rho / (2 : ℝ) ^ n

/-- The scale exponent left after combining the two Hardy radii. -/
@[expose]
def convexHardyScaleExponent (d : ℕ) (s : ℝ) : ℝ :=
  (d : ℝ) + 2 * s

/-- The positive exponent gap between fractional decay and chain weights. -/
@[expose]
def convexHardyScaleGap (s beta : ℝ) : ℝ :=
  1 - 2 * s - beta

/-- The decaying ratio along links below a fixed dyadic scale. -/
@[expose]
def convexHardyScaleInnerRatio (s beta : ℝ) : ℝ :=
  Real.rpow 2 (-convexHardyScaleGap s beta)

/-- The growing ratio of consecutive dyadic scale heads. -/
@[expose]
def convexHardyScaleOuterRatio (d : ℕ) (s : ℝ) : ℝ :=
  Real.rpow 2 (convexHardyScaleExponent d s)

/-- The explicit constant produced by the inner tail and the cutoff outer
head. -/
@[expose]
def convexHardyScaleSummationConstant (d : ℕ) (s beta D : ℝ) : ℝ≥0∞ :=
  (1 - ENNReal.ofReal (convexHardyScaleInnerRatio s beta))⁻¹ *
    ENNReal.ofReal
      (convexHardyScaleOuterRatio d s /
          (convexHardyScaleOuterRatio d s - 1) *
        Real.rpow D (convexHardyScaleExponent d s))

private theorem sum_geometric_head_le
    {q X C : ℝ} (hq : 1 < q) (hX : 0 ≤ X) (hC : 0 ≤ C)
    (S : Finset ℕ) (hS : ∀ k ∈ S, X * q ^ (k + 1) ≤ C) :
    ∑ k ∈ S, X * q ^ (k + 1) ≤ q / (q - 1) * C := by
  classical
  by_cases hEmpty : S = ∅
  · subst S
    simp only [Finset.sum_empty]
    exact mul_nonneg
      (div_nonneg (le_trans zero_le_one hq.le) (sub_nonneg.mpr hq.le)) hC
  · have hNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    let K : ℕ := S.max' hNonempty
    have hSubset : S ⊆ Finset.range (K + 1) := by
      intro k hk
      rw [Finset.mem_range]
      exact Nat.lt_succ_iff.mpr (S.le_max' k hk)
    have hq0 : 0 ≤ q := le_trans zero_le_one hq.le
    have hqSub0 : 0 ≤ q - 1 := sub_nonneg.mpr hq.le
    have hqSubPos : 0 < q - 1 := sub_pos.mpr hq
    have hHead :
        ∑ k ∈ Finset.range (K + 1), X * q ^ (k + 1) =
          X * q * ((q ^ (K + 1) - 1) / (q - 1)) := by
      rw [show (∑ k ∈ Finset.range (K + 1), X * q ^ (k + 1)) =
          X * q * ∑ k ∈ Finset.range (K + 1), q ^ k by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_succ]
        ring]
      rw [geom_sum_eq (ne_of_gt hq)]
    calc
      ∑ k ∈ S, X * q ^ (k + 1) ≤
          ∑ k ∈ Finset.range (K + 1), X * q ^ (k + 1) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hSubset fun k _ _ =>
          mul_nonneg hX (pow_nonneg hq0 k.succ)
      _ = X * q * ((q ^ (K + 1) - 1) / (q - 1)) := hHead
      _ ≤ X * q * (q ^ (K + 1) / (q - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hX hq0)
        exact div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) hqSub0
      _ = q / (q - 1) * (X * q ^ (K + 1)) := by ring
      _ ≤ q / (q - 1) * C := by
        refine mul_le_mul_of_nonneg_left (hS K (S.max'_mem hNonempty)) ?_
        exact div_nonneg hq0 hqSub0

/-- A geometric head cut off by a pointwise ceiling has uniformly bounded
extended nonnegative mass. -/
theorem tsum_cutoff_geometric_head_le
    {q X C : ℝ} (hq : 1 < q) (hX : 0 ≤ X) (hC : 0 ≤ C) :
    (∑' k : ℕ, if X * q ^ (k + 1) ≤ C then
        ENNReal.ofReal (X * q ^ (k + 1)) else 0) ≤
      ENNReal.ofReal (q / (q - 1) * C) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  let T : Finset ℕ := S.filter fun k => X * q ^ (k + 1) ≤ C
  have hTerm0 : ∀ k ∈ S,
      0 ≤ if X * q ^ (k + 1) ≤ C then X * q ^ (k + 1) else 0 := by
    intro k _
    split_ifs
    · exact mul_nonneg hX (pow_nonneg (le_trans zero_le_one hq.le) _)
    · exact le_rfl
  have hReal :
      ∑ k ∈ S, (if X * q ^ (k + 1) ≤ C then X * q ^ (k + 1) else 0) ≤
        q / (q - 1) * C := by
    rw [← Finset.sum_filter]
    exact sum_geometric_head_le hq hX hC T fun k hk => (Finset.mem_filter.mp hk).2
  have hLift :
      (∑ k ∈ S, if X * q ^ (k + 1) ≤ C then
          ENNReal.ofReal (X * q ^ (k + 1)) else 0) =
        ENNReal.ofReal
          (∑ k ∈ S, if X * q ^ (k + 1) ≤ C then
            X * q ^ (k + 1) else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg hTerm0]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : X * q ^ (k + 1) ≤ C
    · simp only [ite_eq_left hk]
    · simp only [ite_eq_right hk, ENNReal.ofReal_zero]
  rw [hLift]
  exact ENNReal.ofReal_le_ofReal hReal

end

end HighContrast
end HCPolySupport
