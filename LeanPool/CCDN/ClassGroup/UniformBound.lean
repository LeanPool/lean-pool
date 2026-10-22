/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.NoIndexTwoClassGroupBound
import LeanPool.CCDN.ClassGroup.BalancedGenerator
import LeanPool.CCDN.ClassGroup.DiscriminantPrimeIdealCover
import LeanPool.CCDN.ClassGroup.QuadraticClassGroupDescent
import LeanPool.CCDN.ClassGroup.QuadraticClassGroupNumerics

/-!
Uniform class-group bounds by strong induction on the field
degree. A quadratic subfield has smaller degree, and discriminant descent
leaves enough exponent saving to absorb the proved ramification factor.
The coefficient is chosen before the field.

Degree and discriminant facts used to assemble the class-group bound
by strong induction on the number-field degree.
-/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField

variable (K : Type*) [Field K] [NumberField K]

private lemma one_le_log_discr_natAbs_add_one : 1 ≤ Real.log ((discr K).natAbs : ℝ) + 1 := by
  rw [numberField_discriminant_natAbs_cast]
  linarith [Real.log_nonneg (one_le_abs_discr K)]

private theorem index_two_subfield_degree
    (hn : 3 ≤ Module.finrank ℚ K) (L : IntermediateField ℚ K)
    (hL : Module.finrank L K = 2) :
    Module.finrank ℚ L = Module.finrank ℚ K / 2 ∧
      2 ≤ Module.finrank ℚ L ∧
      Module.finrank ℚ L < Module.finrank ℚ K := by
  have ht := Module.finrank_mul_finrank ℚ L K
  rw [hL] at ht
  omega

private theorem no_index_two_classGroup_log_one_bound
    (hn : 2 ≤ Module.finrank ℚ K)
    (hnoTwo : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2) :
    (classGroupTwoTorsionCard K : ℝ) ≤
      noIndexTwoClassGroupConstant (Module.finrank ℚ K) *
        ((discr K).natAbs : ℝ) ^
          (1 / 2 - 1 / (2 * (Module.finrank ℚ K : ℝ))) *
            (Real.log ((discr K).natAbs : ℝ) + 1) := by
  rw [numberField_discriminant_natAbs_cast]
  apply (no_index_two_classGroup_two_torsion_bound K hn hnoTwo).trans
  exact mul_le_mul_of_nonneg_left (by linarith : Real.log |(discr K : ℝ)| ≤
    Real.log |(discr K : ℝ)| + 1) (by
      exact mul_nonneg (noIndexTwoClassGroupConstant_pos _).le
        (Real.rpow_nonneg (abs_nonneg _) _))

end
end CCDN

namespace CCDN
noncomputable section
open NumberField
universe u

/-- The statement that every number field `K` of degree `n` satisfies
`h₂(K) ≤ C * |discr K| ^ (1 / 2 - 1 / (2 * n)) * (log |discr K| + 1)`. -/
def ClassGroupLogarithmicBound (n : ℕ) (C : ℝ) : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
    (classGroupTwoTorsionCard K : ℝ) ≤
      C * ((discr K).natAbs : ℝ) ^ (1 / 2 - 1 / (2 * (n : ℝ))) *
        (Real.log ((discr K).natAbs : ℝ) + 1)

/-- For every `n ≥ 2` there is a constant `C > 0` such that every number field `K` of degree `n`
satisfies `h₂(K) ≤ C * |discr K| ^ (1 / 2 - 1 / (2 * n)) * (log |discr K| + 1)`. -/
theorem classGroup_uniform_logarithmic_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ClassGroupLogarithmicBound.{u} n C := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn2 : n = 2
    · subst n
      obtain ⟨C, hC, hbound⟩ := quadratic_class_group_base_numeric
      refine ⟨C, hC, ?_⟩
      intro K _ _ hdeg
      have hh : (classGroupTwoTorsionCard K : ℝ) ≤
          (2 : ℝ) ^ (4 * (discr K).natAbs.primeFactors.card + 2) := by
        exact_mod_cast quadratic_field_classGroupTwoTorsionCard_le K hdeg
      have hb := hh.trans (hbound (discr K).natAbs (numberField_discriminant_natAbs_pos K))
      have ht := hb.trans (le_mul_of_one_le_right
        (by positivity : 0 ≤ C * ((discr K).natAbs : ℝ) ^ (1 / 4 : ℝ))
        (one_le_log_discr_natAbs_add_one K))
      convert ht using 1
      norm_num
    have hn3 : 3 ≤ n := by omega
    by_cases hm : 2 ≤ n / 2
    · obtain ⟨C, hC, hbase⟩ := ih (n / 2)
        (Nat.div_lt_self (by omega) (by omega)) hm
      obtain ⟨A, hA, hstep⟩ := quadratic_class_group_numeric_descent (n / 2) hm C hC
      let T := max A (noIndexTwoClassGroupConstant n)
      have hAT : A ≤ T := le_max_left _ _
      have hNT : noIndexTwoClassGroupConstant n ≤ T := le_max_right _ _
      refine ⟨T, hA.trans_le hAT, ?_⟩
      intro K _ _ hdeg
      have hD : 1 ≤ (discr K).natAbs := numberField_discriminant_natAbs_pos K
      have hlog := one_le_log_discr_natAbs_add_one K
      by_cases hno : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2
      · have hh := no_index_two_classGroup_log_one_bound K (by omega) hno
        rw [hdeg] at hh
        apply hh.trans
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hNT (by positivity)) (by linarith)
      push Not at hno
      obtain ⟨L, hL⟩ := hno
      obtain ⟨hLdeg, _, _⟩ := index_two_subfield_degree K (by omega) L hL
      rw [hdeg] at hLdeg
      have hnEq : n = 2 * (n / 2) := by
        have ht := Module.finrank_mul_finrank ℚ L K
        rw [hL, hLdeg, hdeg] at ht
        omega
      have hLD : (1 : ℝ) ≤ ((discr L).natAbs : ℝ) := by
        exact_mod_cast numberField_discriminant_natAbs_pos L
      have hdisc : (((discr L).natAbs : ℝ) ^ 2) ≤ ((discr K).natAbs : ℝ) := by
        exact_mod_cast quadratic_absolute_discriminant_square_le K L hL
      have hgenus : (classGroupTwoTorsionCard K : ℝ) ≤
          ((classGroupTwoTorsionCard L : ℝ) *
            (2 : ℝ) ^ ((2 * (n / 2)) * (discr K).natAbs.primeFactors.card + n / 2)) ^ 2 := by
        have hh := quadratic_classGroupTwoTorsion_descent L K hL
        rw [hdeg, hLdeg] at hh
        nth_rw 1 [hnEq] at hh
        exact_mod_cast hh
      have hh := hstep (discr K).natAbs hD
        ((discr L).natAbs : ℝ) (classGroupTwoTorsionCard L : ℝ)
        (classGroupTwoTorsionCard K : ℝ) hLD hdisc (by positivity)
        (hbase L hLdeg) hgenus
      have hh' : (classGroupTwoTorsionCard K : ℝ) ≤
          A * ((discr K).natAbs : ℝ) ^ (1 / 2 - 1 / (2 * (n : ℝ))) := by
        simpa only [← hnEq] using hh
      apply hh'.trans
      exact (mul_le_mul_of_nonneg_right hAT (by positivity)).trans
        (le_mul_of_one_le_right (by positivity) hlog)
    · refine ⟨noIndexTwoClassGroupConstant n, noIndexTwoClassGroupConstant_pos n, ?_⟩
      intro K _ _ hdeg
      have hno : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2 := by
        intro L hL
        obtain ⟨hLdeg, hmL, _⟩ := index_two_subfield_degree K (by omega) L hL
        rw [hdeg] at hLdeg
        exact hm (hLdeg ▸ hmL)
      simpa only [hdeg] using no_index_two_classGroup_log_one_bound K (by omega) hno

end
end CCDN
