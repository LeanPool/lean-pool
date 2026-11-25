/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Descent of rank along a finite algebra basis

Expand the two input legs in the basis and apply a linear functional to the
output. The functional sending one to one recovers the original coefficients.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor

open scoped BigOperators

/-- A basis of size `d` gives a rank bound with `d²` copies of each term. -/
theorem RankAtMost.descend_algebra {R L X Y Z : Type*} [CommSemiring R] [CommSemiring L]
    [Algebra R L] {d r : ℕ} (B : Module.Basis (Fin d) R L) (π : L →ₗ[R] R)
    (hπ : π 1 = 1) {T : Tensor R X Y Z}
    (h : RankAtMost (fun x y z => algebraMap R L (T x y z)) r) :
    RankAtMost T (r * d ^ 2) := by
  classical
  obtain ⟨a, b, c, habc⟩ := h
  have expand (u v w : L) :
      ∑ l : Fin d, ∑ m : Fin d, B.repr u l * B.repr v m * π (B l * B m * w) =
        π (u * v * w) := by
    conv_rhs =>
      rw [← B.sum_repr u, Finset.sum_mul, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro l _
    conv_rhs =>
      rw [← B.sum_repr v, Finset.mul_sum, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul, mul_assoc]
  rw [pow_two]
  let e : Fin r × Fin d × Fin d ≃ Fin (r * (d * d)) :=
    ((Equiv.refl (Fin r)).prodCongr finProdFinEquiv).trans finProdFinEquiv
  refine ⟨fun l x => B.repr (a (e.symm l).1 x) (e.symm l).2.1,
    fun l y => B.repr (b (e.symm l).1 y) (e.symm l).2.2,
    fun l z => π (B (e.symm l).2.1 * B (e.symm l).2.2 * c (e.symm l).1 z), ?_⟩
  funext x y z
  rw [← e.sum_comp]
  simp only [rankOne, Equiv.symm_apply_apply, Fintype.sum_prod_type, expand, ← map_sum]
  have hxyz : algebraMap R L (T x y z) = ∑ i, a i x * b i y * c i z :=
    congrFun (congrFun (congrFun habc x) y) z
  rw [← hxyz, Algebra.algebraMap_eq_smul_one, map_smul, hπ, smul_eq_mul, mul_one]

end MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor
