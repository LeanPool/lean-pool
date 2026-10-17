/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Determinant/Character.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; `[IsAlgClosed K]` is assumed by the
declarations that use it.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Filtration
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Degeneration
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Dot
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.SupportExtension
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.TagInequality
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Laws
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.BranchTagging
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The determinant inequality for an actual tensor character

The shared-input tag inequality is applied to the two concrete branches of the
checked determinant degeneration. All basis changes and the output-dual change
are supplied by `DeterminantFiltration`.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration

variable (K) in
/-- The two graded blocks, padded with zeros in common coordinate spaces. -/
def branch (d e : ℕ) (n : Fin 2) :
    Tensor K (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if n = 0 then if i.val + j.val = k.val then 1 else 0 else 0
  | i, .inr j, .inr k => if n = 1 then if i.val + j.val = k.val then 1 else 0 else 0
  | _, _, _ => 0

def branchLabel (e : ℕ) : Index e → Fin 2
  | .inl _ => 0
  | .inr _ => 1

theorem branch_support (d e : ℕ) (n : Fin 2) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) (h : branch K d e n i j k ≠ 0) :
    branchLabel e j = n ∧ branchLabel (d + e) k = n := by
  fin_cases n <;> rcases j with j | j <;> rcases k with k | k <;>
    simp_all [branch, branchLabel]

theorem sum_branch (d e : ℕ) : (∑ n, branch K d e n) = gradedTensor K d e := by
  funext i j k
  rcases j with j | j <;> rcases k with k | k <;>
    simp [branch, gradedTensor]

theorem branch_ne_zero (d e : ℕ) (he : 0 < e) (n : Fin 2) : branch K d e n ≠ 0 := by
  intro h
  fin_cases n
  · have hv := congrFun (congrFun (congrFun h ⟨0, by omega⟩)
      (.inl ⟨0, by omega⟩)) (.inl ⟨0, by omega⟩)
    simp [branch] at hv
  · have hv := congrFun (congrFun (congrFun h ⟨0, by omega⟩)
      (.inr ⟨0, he⟩)) (.inr ⟨0, by omega⟩)
    simp [branch] at hv

end DeterminantFiltration

namespace Character

open DeterminantFiltration

variable (χ : Character K)

theorem value_determinant_branch_zero (d e : ℕ) :
    χ.value (branch K d e 0) = χ.value (convolution K (d + 1) (e + 2)) := by
  let fz : Fin ((d + 1) + (e + 2) - 1) → Index (d + e) :=
    fun k => .inl (Fin.cast (by omega) k)
  have hfz : Function.Injective fz := by
    intro a b h
    exact Fin.ext (congrArg (fun z : Index (d + e) =>
      match z with | .inl k => k.val | .inr k => k.val) h)
  have hs : ∀ i j k, branch K d e 0 i j k ≠ 0 →
      i ∈ Set.range (id : Fin (d + 1) → Fin (d + 1)) ∧
      j ∈ Set.range (Sum.inl : Fin (e + 2) → Index e) ∧ k ∈ Set.range fz := by
    intro i j k h
    rcases j with j | j <;> rcases k with k | k
    · exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨Fin.cast (by omega) k, by simp [fz]⟩⟩
    all_goals simp [branch] at h
  have hv := χ.value_eq_pullback_of_support (branch K d e 0) id Sum.inl fz
    Function.injective_id Sum.inl_injective hfz hs
  have ht : Tensor.pullback id Sum.inl fz (branch K d e 0) =
      convolution K (d + 1) (e + 2) := by
    funext i j k
    simp [Tensor.pullback, branch, fz, convolution]
  simpa only [ht] using hv

theorem value_determinant_branch_one (d e : ℕ) :
    χ.value (branch K d e 1) = χ.value (convolution K (d + 1) e) := by
  let fz : Fin ((d + 1) + e - 1) → Index (d + e) :=
    fun k => .inr (Fin.cast (by omega) k)
  have hfz : Function.Injective fz := by
    intro a b h
    exact Fin.ext (congrArg (fun z : Index (d + e) =>
      match z with | .inl k => k.val | .inr k => k.val) h)
  have hs : ∀ i j k, branch K d e 1 i j k ≠ 0 →
      i ∈ Set.range (id : Fin (d + 1) → Fin (d + 1)) ∧
      j ∈ Set.range (Sum.inr : Fin e → Index e) ∧ k ∈ Set.range fz := by
    intro i j k h
    rcases j with j | j <;> rcases k with k | k
    any_goals simp [branch] at h
    exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨Fin.cast (by omega) k, by simp [fz]⟩⟩
  have hv := χ.value_eq_pullback_of_support (branch K d e 1) id Sum.inr fz
    Function.injective_id Sum.inr_injective hfz hs
  have ht : Tensor.pullback id Sum.inr fz (branch K d e 1) =
      convolution K (d + 1) e := by
    funext i j k
    simp [Tensor.pullback, branch, fz, convolution]
  simpa only [ht] using hv

private theorem value_bool_dot :
    χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool))) =
      (2 : ℝ) ^ χ.pX := by
  have hv := χ.value_reindex
    (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool)))
    (Equiv.refl Unit) finTwoEquiv finTwoEquiv
  have ht : Tensor.pullback (Equiv.refl Unit) finTwoEquiv finTwoEquiv
      (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool))) =
        Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin 2))) := by
    funext i j k
    simp [Tensor.pullback, Tensor.cyclic, Tensor.dotPairing]
  rw [ht] at hv
  exact hv.symm.trans (χ.value_cyclic_cyclic_dotPairing (by decide))

/-- The auxiliary dot product is charged once, on the actual source tensor. -/
theorem value_determinant_source_le (d e : ℕ) :
    χ.value (sourceTensor K d e) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution K (d + 1) (e + 1)) := by
  rw [sourceTensor_product]
  apply (χ.value_pullback_le _ _ _ _).trans_eq
  rw [χ.map_product, χ.value_bool_dot]
  ring

/-- Actual basis-change and degeneration certificates give this comparison. -/
theorem value_determinant_graded_le [IsAlgClosed K] (d e : ℕ) :
    χ.value (gradedTensor K d e) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution K (d + 1) (e + 1)) := by
  calc
    χ.value (gradedTensor K d e) ≤ χ.value (adaptedTensor K d e) :=
      χ.value_polynomialRestrictionDegeneration_le (degeneration K d e)
    _ ≤ χ.value (sourceTensor K d e) := by
      simpa only [sourceTensor_coordinate_change] using
        χ.monotone (sourceTensor K d e) (fixedFirst K d) (inputChange K e)
          (outputDualChange K (d + e))
    _ ≤ _ := χ.value_determinant_source_le d e

/-- The binary tag bound before normalizing over all six characters. -/
theorem convolution_concavity_tag_dims [IsAlgClosed K] (d e : ℕ) (he : 0 < e)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    Real.exp (χ.pX * Real.binEntropy q) *
        χ.value (convolution K (d + 1) (e + 2)) ^ q *
        χ.value (convolution K (d + 1) e) ^ (1 - q) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution K (d + 1) (e + 1)) := by
  have ht := χ.sharedFirst_tag (binaryLaw q hq₀ hq₁) (branch K d e)
    (branch_ne_zero d e he)
  rw [χ.value_sharedFirstTensor_eq_sum (branch K d e)
    (branchLabel e) (branchLabel (d + e)) (branch_support d e), sum_branch] at ht
  rw [binaryLaw_entropy, binaryLaw_product,
    χ.value_determinant_branch_zero, χ.value_determinant_branch_one] at ht
  apply le_trans (b := χ.value (gradedTensor K d e))
  · simpa only [mul_assoc] using ht
  · exact χ.value_determinant_graded_le d e

/-- The determinant inequality in the paper's positive-dimension notation. -/
theorem convolution_concavity_tag [IsAlgClosed K] (a b : ℕ) (ha : 0 < a) (hb : 2 ≤ b)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    Real.exp (χ.pX * Real.binEntropy q) *
        χ.value (convolution K a (b + 1)) ^ q *
        χ.value (convolution K a (b - 1)) ^ (1 - q) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution K a b) := by
  obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
  obtain ⟨e, rfl, he⟩ : ∃ e, b = e + 1 ∧ 0 < e := ⟨b - 1, by omega, by omega⟩
  simpa [Nat.add_assoc] using χ.convolution_concavity_tag_dims d e he q hq₀ hq₁

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
