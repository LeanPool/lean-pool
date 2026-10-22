/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.TwoTorsion
import LeanPool.CCDN.ClassGroup.BalancedGenerator
import LeanPool.CCDN.ClassGroup.OddDegreeClassGroupBound
import LeanPool.CCDN.ClassGroup.UniformBound

/-! CCDN Theorem 6 for the two-torsion subgroup of the ideal class
group. Constants are uniform over all number fields of the given degree.
Odd degrees have no logarithm; even degrees have exactly one logarithm.
The quadratic descent, exceptional subfields, lattice and curve counts
used by the proof are all proved in the imported modules. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
universe u

/-- The full class-group application, including the logarithmic exponent
specified by the parity of the field degree. -/
theorem classGroup_two_torsion_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
        (classGroupTwoTorsionCard K : ℝ) ≤
          C * |(discr K : ℝ)| ^ (1 / 2 - 1 / (2 * (n : ℝ))) *
            (Real.log |(discr K : ℝ)|) ^ (1 - n % 2) := by
  obtain ⟨C, hC, hbound⟩ := classGroup_uniform_logarithmic_bound.{u} n (by omega)
  let T := max (oddDegreeClassGroupConstant n) (2 * C)
  have hCT : 2 * C ≤ T := le_max_right _ _
  refine ⟨T, (mul_pos (by norm_num) hC).trans_le hCT, ?_⟩
  intro K _ _ hdeg
  have hlog : 1 ≤ Real.log |(discr K : ℝ)| := one_le_log_abs_discr K (by omega)
  by_cases hodd : Odd n
  · rw [Nat.odd_iff.mp hodd, Nat.sub_self, pow_zero, mul_one]
    have hh := odd_degree_classGroup_two_torsion_bound K (by omega)
      (by simpa only [hdeg] using hodd)
    rw [hdeg] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · rw [Nat.not_odd_iff.mp hodd, Nat.sub_zero, pow_one]
    have hh := hbound K hdeg
    rw [numberField_discriminant_natAbs_cast] at hh
    have hcost := mul_le_mul_of_nonneg_left
      (show Real.log |(discr K : ℝ)| + 1 ≤ 2 * Real.log |(discr K : ℝ)| by linarith)
      (show 0 ≤ C * |(discr K : ℝ)| ^ (1 / 2 - 1 / (2 * (n : ℝ))) by positivity)
    have hh' : (classGroupTwoTorsionCard K : ℝ) ≤
        (2 * C) * |(discr K : ℝ)| ^ (1 / 2 - 1 / (2 * (n : ℝ))) *
          Real.log |(discr K : ℝ)| := by
      convert hh.trans hcost using 1
      ring
    exact hh'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCT (by positivity)) (by linarith))

end
end CCDN
