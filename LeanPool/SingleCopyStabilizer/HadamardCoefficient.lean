/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt

/-! The normalization coefficient for arbitrary-qubit Hadamard actions. -/

@[expose] public section

noncomputable section
namespace LeanPool.SingleCopyStabilizer.QubitGates

/-- The positive real coefficient `1 / √2`, regarded as a complex number. -/
def hadamardCoefficient : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)

lemma hadamardCoefficient_mul :
    hadamardCoefficient * hadamardCoefficient = (1 / 2 : ℂ) := by
  unfold hadamardCoefficient
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num

@[simp] lemma hadamardCoefficient_star :
    star hadamardCoefficient = hadamardCoefficient := by
  simp [hadamardCoefficient]

end LeanPool.SingleCopyStabilizer.QubitGates
