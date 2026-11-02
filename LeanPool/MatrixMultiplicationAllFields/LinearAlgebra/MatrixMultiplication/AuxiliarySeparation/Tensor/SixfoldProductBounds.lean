/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/SixfoldProductBounds.lean`,
by Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K`
algebraically closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Symmetrization
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization
public import Mathlib.Tactic.GCongr
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Algebra and bounds for the sixfold character product

The product over all six leg orders is multiplicative and nonnegative. A
nonzero tensor has product at least one, and every rank decomposition bounds
the product by the sixth power of its size.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



namespace MatrixMultiplication.AuxiliarySeparation
namespace Character

open MatrixMultiplication.Foundation

variable (χ : Character K)
variable {X Y Z U V W : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]

/-- Taking the product over all six leg orders preserves tensor multiplication. -/
theorem sixfoldProduct_product (T : Tensor K X Y Z) (S : Tensor K U V W) :
    χ.sixfoldProduct (Tensor.product T S) = χ.sixfoldProduct T * χ.sixfoldProduct S := by
  unfold sixfoldProduct
  change χ.value (Tensor.product T S) *
      χ.value (Tensor.product (fun y z x => T x y z) (fun v w u => S u v w)) *
      χ.value (Tensor.product (fun z x y => T x y z) (fun w u v => S u v w)) *
      χ.value (Tensor.product (fun x z y => T x y z) (fun u w v => S u v w)) *
      χ.value (Tensor.product (fun z y x => T x y z) (fun w v u => S u v w)) *
      χ.value (Tensor.product (fun y x z => T x y z) (fun v u w => S u v w)) = _
  simp only [χ.map_product]
  ring

/-- All six factors of the symmetrized product are nonnegative. -/
theorem sixfoldProduct_nonneg (T : Tensor K X Y Z) : 0 ≤ χ.sixfoldProduct T := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (χ.nonneg T) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)

/-- Every nonzero tensor has symmetrized character product at least one. -/
theorem one_le_sixfoldProduct {T : Tensor K X Y Z} (hT : T ≠ 0) :
    1 ≤ χ.sixfoldProduct T := by
  classical
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hT
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hx
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hy
  change T x y z ≠ 0 at hz
  have h0 := χ.one_le_value hT
  have h1 : 1 ≤ χ.value (fun y z x => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S y z x) h))
  have h2 : 1 ≤ χ.value (fun z x y => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S z x y) h))
  have h3 : 1 ≤ χ.value (fun x z y => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S x z y) h))
  have h4 : 1 ≤ χ.value (fun z y x => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S z y x) h))
  have h5 : 1 ≤ χ.value (fun y x z => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S y x z) h))
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h0 h1) h2) h3) h4) h5

/-- In particular, the sixfold product of a nonzero tensor is positive. -/
theorem sixfoldProduct_pos {T : Tensor K X Y Z} (hT : T ≠ 0) :
    0 < χ.sixfoldProduct T :=
  zero_lt_one.trans_le (χ.one_le_sixfoldProduct hT)

private theorem rankAtMost_swap12 {K X Y Z : Type*} [CommSemiring K]
    {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) :
    Tensor.RankAtMost (fun y x z => T x y z) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨b, a, c, ?_⟩
  funext y x z
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [Tensor.rankOne]
  ring

/-- A rank decomposition bounds each of the six character factors. -/
theorem sixfoldProduct_le_rank {T : Tensor K X Y Z} {r : ℕ}
    (h : Tensor.RankAtMost T r) : χ.sixfoldProduct T ≤ (r : ℝ) ^ 6 := by
  have h0 := χ.value_le_rank h
  have h1 := χ.value_le_rank h.cyclic
  have h2 := χ.value_le_rank h.cyclic.cyclic
  have h5 := χ.value_le_rank (rankAtMost_swap12 h)
  have h3 := χ.value_le_rank (rankAtMost_swap12 h).cyclic
  have h4 := χ.value_le_rank (rankAtMost_swap12 h).cyclic.cyclic
  unfold sixfoldProduct
  calc
    _ ≤ (r : ℝ) * r * r * r * r * r := by
      gcongr <;> first
        | exact χ.nonneg _
        | exact h0
        | exact h1
        | exact h2
        | exact h3
        | exact h4
    _ = _ := by ring

end Character
end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
