/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite coefficient tensors and their algebraic transformations. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation

variable (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]

def groupTensor : Tensor ℂ G G G := fun a b c => if a + b = c then 1 else 0

theorem groupTensor_fourier :
    groupTensor G = fun a b c => ∑ χ : AddChar G ℂ,
      Tensor.rankOne (fun a => χ a / (Fintype.card G : ℂ))
        (fun b => χ b) (fun c => χ (-c)) a b c := by
  funext a b c
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    groupTensor G a b c =
        (∑ χ : AddChar G ℂ, χ (a + b - c)) / (Fintype.card G : ℂ) := by
      rw [AddChar.sum_apply_eq_ite]
      by_cases h : a + b = c
      · simp [groupTensor, h, hcard]
      · simp [groupTensor, h, sub_ne_zero.mpr h]
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro χ hχ
      simp only [Tensor.rankOne, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring

theorem groupTensor_rankAtMost : Tensor.RankAtMost (groupTensor G) (Fintype.card G) := by
  rw [groupTensor_fourier]
  simpa only [AddChar.card_eq] using
    Tensor.rankAtMost_sum_rankOne
      (fun χ : AddChar G ℂ => fun a => χ a / (Fintype.card G : ℂ))
      (fun χ : AddChar G ℂ => fun b => χ b)
      (fun χ : AddChar G ℂ => fun c => χ (-c))

end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
