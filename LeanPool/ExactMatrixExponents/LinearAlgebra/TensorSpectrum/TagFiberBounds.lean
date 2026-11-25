/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagTensorWords
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorCharacterPowers

/-!
# The exact finite-word character inequality

Every count fiber is selected by actual local coordinate maps from a tensor
power of the original shared-input tensor.  Charged separation is then applied
to that finite fiber.  This is the tensor input to the later scalar limit;
neither the separation nor the word restriction is an assumption here.
-/

@[expose] public section

noncomputable section

open scoped BigOperators NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor

namespace MatrixMultiplicationAllFields.TensorSpectrum.TensorClass

variable {K : Type*} [CommSemiring K]

theorem Character.shared_branch_le (f : Character K)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {s : ℕ} (A : Fin s → Tensor K X Y Z) (i : Fin s) :
    f (ofTensor (A i)) ≤ f (ofTensor (TagTensorWords.sharedLabels A)) := by
  have hr := CoefficientTensor.Restricts.pullback (TagTensorWords.sharedLabels A)
    id (fun y => (i, y)) (fun z => (i, z))
  have heq : Tensor.pullback id (fun y => (i, y)) (fun z => (i, z))
      (TagTensorWords.sharedLabels A) = A i := by
    funext x y z
    simp [Tensor.pullback, TagTensorWords.sharedLabels]
  rw [heq] at hr
  exact f.monotone' (ofTensor_le hr)

/-- The finite word-fiber bound using the charged separation inequality. -/
theorem Character.tag_count_fiber (f : Character K)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {s N : ℕ} (A : Fin s → Tensor K X Y Z)
    (c : TagWords.CountVector s N) (hc : 0 < (TagWords.fiber c).card) (factor : ℝ≥0)
    (hcharge : ∀ {M : ℕ}, 0 < M →
      ∀ (B : Fin M → Tensor K (Fin N → X) (Fin N → Y) (Fin N → Z)) (C : ℝ≥0),
        (∀ i, f (ofTensor (B i)) = C) →
        C * f (dotX M) ≤ factor * f (ofTensor (TagTensorWords.sharedLabels B))) :
    ((TagWords.fiber c).card : ℝ) ^ f.pX *
        TagWords.countWeight (fun i => (f (ofTensor (A i)) : ℝ)) c ≤
      (factor : ℝ) * (f (ofTensor (TagTensorWords.sharedLabels A)) : ℝ) ^ N := by
  classical
  let M := (TagWords.fiber c).card
  let e : Fin M ≃ {w // w ∈ TagWords.fiber c} :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe (TagWords.fiber c))).symm
  let B := fun i : Fin M => TagTensorWords.wordBranch A (e i).val
  let C : ℝ≥0 := TagWords.countWeight (fun i => f (ofTensor (A i))) c
  have hvalue : ∀ i, f (ofTensor (B i)) = C := by
    intro i
    exact TagTensorWords.map_wordBranch_of_mem_fiber f A (e i).property
  have hsep := hcharge hc B C hvalue
  have hselect := TagTensorWords.restricts_power_shared_fiber_enumeration A c e
  have hmono : f (ofTensor (TagTensorWords.sharedLabels B)) ≤
      (f (ofTensor (TagTensorWords.sharedLabels A))) ^ N := by
    have h := f.monotone' (ofTensor_le hselect)
    simpa only [Character.map_power_tensor] using h
  have hfinite : C * f (dotX M) ≤
      factor * (f (ofTensor (TagTensorWords.sharedLabels A))) ^ N :=
    hsep.trans (mul_le_mul_of_nonneg_left hmono (by positivity))
  have hreal : (C : ℝ) * f.dotXValue M ≤
      (factor : ℝ) * (f (ofTensor (TagTensorWords.sharedLabels A)) : ℝ) ^ N := by
    exact_mod_cast hfinite
  rw [f.dotXValue_eq_rpow M (Nat.succ_le_iff.mpr hc)] at hreal
  have hC : (C : ℝ) =
      TagWords.countWeight (fun i => (f (ofTensor (A i)) : ℝ)) c := by
    simp [C, TagWords.countWeight]
  rw [hC, mul_comm] at hreal
  exact hreal

end MatrixMultiplicationAllFields.TensorSpectrum.TensorClass
