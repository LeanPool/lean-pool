/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145N6HelmertFrame

/-!
# Realization of the six-vertex tensor data by physical frames.
-/

@[expose] public section
noncomputable section
namespace C145N6Frame
open scoped BigOperators

theorem physical_tensor_feature_sum (i j k : Fin 6) :
    C145PhysicalFrame.T frame overlap i j k = ∑ v, feature v i * feature v j * feature v k := by
  simp only [C145PhysicalFrame.T, C145PhysicalFrame.C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [← overlap_frame_feature, ← overlap_frame_feature, ← overlap_frame_feature]
  ring

theorem actual_tensor_slice_0 (j k : Fin 6) :
    C145PhysicalFrame.T frame overlap 0 j k = C145N6Literal.baseTensor 0 j k := by
  rw [physical_tensor_feature_sum]
  fin_cases j <;> fin_cases k <;>
    norm_num [feature, helmert, numerator, gramWeight, C145N6Literal.baseTensor, Fin.sum_univ_succ]

theorem actual_tensor_slice_1 (j k : Fin 6) :
    C145PhysicalFrame.T frame overlap 1 j k = C145N6Literal.baseTensor 1 j k := by
  rw [physical_tensor_feature_sum]
  fin_cases j <;> fin_cases k <;>
    norm_num [feature, helmert, numerator, gramWeight, C145N6Literal.baseTensor, Fin.sum_univ_succ]

theorem actual_tensor_slice_2 (j k : Fin 6) :
    C145PhysicalFrame.T frame overlap 2 j k = C145N6Literal.baseTensor 2 j k := by
  rw [physical_tensor_feature_sum]
  fin_cases j <;> fin_cases k <;>
    norm_num [feature, helmert, numerator, gramWeight, C145N6Literal.baseTensor, Fin.sum_univ_succ]

theorem actual_tensor_slice_3 (j k : Fin 6) :
    C145PhysicalFrame.T frame overlap 3 j k = C145N6Literal.baseTensor 3 j k := by
  rw [physical_tensor_feature_sum]
  fin_cases j <;> fin_cases k <;>
    norm_num [feature, helmert, numerator, gramWeight, C145N6Literal.baseTensor, Fin.sum_univ_succ]

theorem actual_tensor_slice_4 (j k : Fin 6) :
    C145PhysicalFrame.T frame overlap 4 j k = C145N6Literal.baseTensor 4 j k := by
  rw [physical_tensor_feature_sum]
  fin_cases j <;> fin_cases k <;>
    norm_num [feature, helmert, numerator, gramWeight, C145N6Literal.baseTensor, Fin.sum_univ_succ]

theorem actual_tensor_slice_5 (j k : Fin 6) :
    C145PhysicalFrame.T frame overlap 5 j k = C145N6Literal.baseTensor 5 j k := by
  rw [physical_tensor_feature_sum]
  fin_cases j <;> fin_cases k <;>
    norm_num [feature, helmert, numerator, gramWeight, C145N6Literal.baseTensor, Fin.sum_univ_succ]

theorem actual_tensor_saved_base : C145PhysicalFrame.T frame overlap = C145N6Literal.baseTensor :=
  by
  funext i j k
  fin_cases i
  · exact actual_tensor_slice_0 j k
  · exact actual_tensor_slice_1 j k
  · exact actual_tensor_slice_2 j k
  · exact actual_tensor_slice_3 j k
  · exact actual_tensor_slice_4 j k
  · exact actual_tensor_slice_5 j k

/-- The saved literal witness has an actual calibrated orthonormal-frame realization.
This is not a graph or differential-equation realization theorem. -/
theorem saved_frame_response_unique (μ : ℝ) (Q : Fin 6 → Fin 6 → ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (hground : ∀ v, Q v 0 = 1 / Real.sqrt 6)
    (hresponse : C145.H2.SamePositive (C145.H2.fullRates μ C145N6.rates)
      (C145PhysicalFrame.T frame overlap) (C145PhysicalFrame.T Q overlap)) :
    C145PhysicalFrame.T Q overlap = C145N6Literal.baseTensor := by
  exact C145N6.physical_saved_base_unique μ frame Q overlap (1 / Real.sqrt 6)
    frame_orthonormal hQ overlap_nonzero frame_ground hground overlap_square
    actual_tensor_saved_base hresponse

end C145N6Frame

end
