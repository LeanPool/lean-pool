/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Sector/Character.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; `[IsAlgClosed K]` is assumed by the
declarations that use it.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Degeneration
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Degeneration
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Laws
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.TagInequality
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Branches
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.BranchTagging
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The character inequality from the three-sector degeneration

The retained tensor has three branches sharing its actual first-input space.
Their two remaining coordinate intervals determine matching branch labels.
The uniform three-branch tag inequality and polynomial degeneration then yield
the character inequality of Section 5.2 before symmetrization.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation.Sector

variable (K) in
open Classical in
/-- The actual three retained tensors in their original ambient spaces. -/
def branchFamily (a h : ℕ) (b : Fin 3) :
    Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  if b = 0 then leftTensor K a h else if b = 1 then middleTensor K a h else rightTensor K a h

@[simp] theorem branchFamily_zero (a h : ℕ) :
    branchFamily K a h 0 = leftTensor K a h := by simp [branchFamily]

@[simp] theorem branchFamily_one (a h : ℕ) :
    branchFamily K a h 1 = middleTensor K a h := by simp [branchFamily]

@[simp] theorem branchFamily_two (a h : ℕ) :
    branchFamily K a h 2 = rightTensor K a h := by simp [branchFamily]

open Classical in
/-- Label a second-leg coordinate by its interval. -/
def yLabel (a h : ℕ) (j : YIndex a h) : Fin 3 :=
  if j.val < h then 0 else if j.val < rightStart a h then 1 else 2

open Classical in
/-- Label a third-leg coordinate by its corresponding interval. -/
def zLabel (a h : ℕ) (k : ZIndex a h) : Fin 3 :=
  if k.val < h + a - 1 then 0 else if k.val < rightStart a h then 1 else 2

/-- Every nonzero branch coefficient lies in the two matching labelled sectors. -/
theorem branchFamily_labels (a h : ℕ) (b : Fin 3) (i : Fin a)
    (j : YIndex a h) (k : ZIndex a h) (hn : branchFamily K a h b i j k ≠ 0) :
    yLabel a h j = b ∧ zLabel a h k = b := by
  classical
  fin_cases b
  · have hb : LeftBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, leftTensor, hb])
    have h := (leftBranch_iff hb.support).mp hb
    simp [yLabel, zLabel, h.1, h.2]
  · have hb : MiddleBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, middleTensor, hb])
    rcases (middleBranch_iff hb.support).mp hb with ⟨⟨hy₀, hy₁⟩, ⟨hz₀, hz₁⟩⟩
    simp [yLabel, zLabel, not_lt.mpr hy₀, hy₁, not_lt.mpr hz₀, hz₁]
  · have hb : RightBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, rightTensor, hb])
    rcases (rightBranch_iff hb.support).mp hb with ⟨hy, hz⟩
    have hi := i.isLt
    have hy₀ : h ≤ j.val := by unfold rightStart at hy; omega
    have hz₀ : h + a - 1 ≤ k.val := by unfold rightStart at hz; omega
    simp [yLabel, zLabel, not_lt.mpr hy₀, not_lt.mpr hy,
      not_lt.mpr hz₀, not_lt.mpr hz]

/-- The branch family sums to exactly the retained tensor. -/
theorem sum_branchFamily (a h : ℕ) :
    (∑ b : Fin 3, branchFamily K a h b) = retained K a h := by
  classical
  simp only [Fin.sum_univ_three, branchFamily_zero, branchFamily_one, branchFamily_two]
  exact (retained_eq_three_branches a h).symm

/-- The character comparison uses the actual polynomial degeneration. -/
theorem value_retained_le_source [IsAlgClosed K] (χ : Character K) (a h : ℕ) :
    χ.value (retained K a h) ≤ χ.value (source K a h) :=
  χ.value_polynomialRestrictionDegeneration_le (restriction K a h)

/-- Both interval labels can be recovered without changing the common first
input, so the tagged branch tensor has precisely the retained tensor's value. -/
theorem value_sharedFirst_branchFamily (χ : Character K) (a h : ℕ) :
    χ.value (sharedFirstTensor (branchFamily K a h)) = χ.value (retained K a h) := by
  classical
  rw [χ.value_sharedFirstTensor_eq_sum (branchFamily K a h)
    (yLabel a h) (zLabel a h) (branchFamily_labels a h), sum_branchFamily]

theorem branchFamily_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h)
    (b : Fin 3) : branchFamily K a h b ≠ 0 := by
  classical
  fin_cases b
  · simpa [branchFamily] using leftTensor_nonzero ha hh
  · simpa [branchFamily] using middleTensor_nonzero ha hh
  · simpa [branchFamily] using rightTensor_nonzero ha hh

/-- The uniform branch product combines the two outer convolution values. -/
theorem uniform_branchFamily_product (χ : Character K) (a h : ℕ)
    (ha : 0 < a) (hh : 0 < h) :
    (∏ b, χ.value (branchFamily K a h b) ^ (FiniteLaw.uniform (Fin 3)).mass b) =
      χ.value (convolution K a h) ^ (2 / 3 : ℝ) *
        χ.value (exchangedConvolution K a h) ^ (1 / 3 : ℝ) := by
  classical
  rw [uniformThree_product]
  simp only [branchFamily_zero, branchFamily_one, branchFamily_two,
    value_leftTensor, value_middleTensor, value_rightTensor]
  have hc : 0 < χ.value (convolution K a h) :=
    lt_of_lt_of_le zero_lt_one (χ.one_le_value (convolution_nonzero ha hh))
  calc
    χ.value (convolution K a h) ^ (1 / 3 : ℝ) *
        χ.value (exchangedConvolution K a h) ^ (1 / 3 : ℝ) *
        χ.value (convolution K a h) ^ (1 / 3 : ℝ) =
      (χ.value (convolution K a h) ^ (1 / 3 : ℝ) *
        χ.value (convolution K a h) ^ (1 / 3 : ℝ)) *
          χ.value (exchangedConvolution K a h) ^ (1 / 3 : ℝ) := by ring
    _ = _ := by
      rw [← Real.rpow_add hc]
      norm_num

/-- The per-character three-sector inequality, before multiplication over
the six tensor-leg permutations. All tensor values are actual convolution
values, with only the middle branch exchanging its last two legs. -/
theorem convolution_tripling_tag [IsAlgClosed K] (χ : Character K) (a h : ℕ)
    (ha : 0 < a) (hh : 0 < h) :
    (3 : ℝ) ^ χ.pX * χ.value (convolution K a h) ^ (2 / 3 : ℝ) *
      χ.value (fun i s r => convolution K a h i r s) ^ (1 / 3 : ℝ) ≤
        χ.value (convolution K a (3 * h + a - 1)) := by
  classical
  have htag := χ.sharedFirst_tag (FiniteLaw.uniform (Fin 3))
    (branchFamily K a h) (branchFamily_nonzero ha hh)
  rw [uniformThree_entropy_factor, uniform_branchFamily_product χ a h ha hh,
    value_sharedFirst_branchFamily] at htag
  have hresult := htag.trans (value_retained_le_source χ a h)
  change (3 : ℝ) ^ χ.pX * (χ.value (convolution K a h) ^ (2 / 3 : ℝ) *
    χ.value (fun i s r => convolution K a h i r s) ^ (1 / 3 : ℝ)) ≤
      χ.value (convolution K a (3 * h + a - 1)) at hresult
  simpa only [mul_assoc] using hresult

end MatrixMultiplication.AuxiliarySeparation.Sector

end

end MatrixMultiplicationAllFields
