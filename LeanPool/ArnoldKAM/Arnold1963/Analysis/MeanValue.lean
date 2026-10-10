/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Functions
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
Mean-value estimates on contained segments. Coordinate bounds give operator bounds with the
explicit dimension factor required by the maximum norm.
-/

@[expose] public section

noncomputable section
namespace KamProject.Arnold1963

section Segment
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem norm_sub_le_of_segment_bound {f : E → F} {U : Set E} {a b : E} {C : ℝ}
    (hab : segment ℝ a b ⊆ U) (hf : ∀ x ∈ U, DifferentiableAt ℂ f x)
    (hC : NormBoundOn (fderiv ℂ f) U C) :
    ‖f b - f a‖ ≤ C * ‖b - a‖ := by
  exact (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => hf x (hab hx)) (fun x hx => hC.norm_le (hab hx))
    (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)

theorem norm_sub_le_of_analytic_segment_bound {f : E → F} {U : Set E}
    {a b : E} {C : ℝ} (hab : segment ℝ a b ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hC : NormBoundOn (fderiv ℂ f) U C) :
    ‖f b - f a‖ ≤ C * ‖b - a‖ :=
  norm_sub_le_of_segment_bound hab (fun x hx => (hf x hx).differentiableAt) hC

end Segment

theorem norm_linearMap_le_of_coordinate_bound {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : ComplexSpace n →L[ℂ] F) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ j, ‖A (Pi.single j 1)‖ ≤ C) : ‖A‖ ≤ n * C := by
  apply A.opNorm_le_bound (mul_nonneg (Nat.cast_nonneg _) hC)
  intro v
  have hv : A v = ∑ j, v j • A (Pi.single j 1) := by
    conv_lhs => rw [pi_eq_sum_univ' v]
    simp only [map_sum, map_smul]
  rw [hv]
  calc
    _ ≤ ∑ j, ‖v j • A (Pi.single j 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ‖v‖ * C := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm v j) (hA j) (norm_nonneg _) (norm_nonneg _)
    _ = (n : ℝ) * C * ‖v‖ := by simp; ring

theorem norm_sub_le_of_coordinate_bound {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ComplexSpace n → F} {U : Set (ComplexSpace n)} {a b : ComplexSpace n} {C : ℝ}
    (hab : segment ℝ a b ⊆ U) (hf : AnalyticOnNhd ℂ f U) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ U, ∀ j, ‖fderiv ℂ f x (Pi.single j 1)‖ ≤ C) :
    ‖f b - f a‖ ≤ (n : ℝ) * C * ‖b - a‖ := by
  exact norm_sub_le_of_analytic_segment_bound hab hf
    ⟨mul_nonneg (Nat.cast_nonneg _) hC, fun x hx =>
      norm_linearMap_le_of_coordinate_bound _ hC (hbound x hx)⟩

end KamProject.Arnold1963
