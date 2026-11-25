/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.RankDescent
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Weights
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Descent of weighted rank along finite field extensions -/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle

/-- A degree-`d` extension increases the cost of descending a rank witness
by at most a factor of `d²`. Only the two input legs are expanded in a basis.
A linear functional sending one to one recovers the output coefficients,
even in characteristics dividing `d`. -/
theorem descendWeighted {F : Type*} {L : Type*} [Field F] [Field L] [Algebra F L]
    [Module.Finite F L]
    {i j k r : ℕ} {W : Fin i → Fin j → Fin k → F}
    (h : WeightedRankLE (fun x y z => algebraMap F L (W x y z)) r) :
    WeightedRankLE W (r * Module.finrank F L ^ 2) := by
  classical
  obtain ⟨π, hπ⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : L) ≠ 0)
  let T : Tensor F (Pos i k) (Pos k j) (Pos i j) := fun x y z =>
    if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then W x.1 y.2 x.2 else 0
  have hT : Tensor.RankAtMost (fun x y z => algebraMap F L (T x y z)) r := by
    obtain ⟨a, b, c, habc⟩ := h
    refine ⟨a, b, c, ?_⟩
    funext x y z
    simp only [Tensor.rankOne]
    dsimp only [T]
    rw [habc, apply_ite (algebraMap F L), map_zero]
  obtain ⟨a, b, c, habc⟩ := hT.descend_algebra (Module.finBasis F L) π hπ
  exact ⟨a, b, c, fun x y z => (congrFun (congrFun (congrFun habc x) y) z).symm⟩

theorem descendRank {F : Type*} {L : Type*} [Field F] [Field L] [Algebra F L] [Module.Finite F L]
    {i j k r : ℕ} (h : RankLE L i j k r) : RankLE F i j k (r * Module.finrank F L ^ 2) := by
  have h' : WeightedRankLE (fun (_ : Fin i) (_ : Fin j) (_ : Fin k) => algebraMap F L 1) r := by
    simpa only [map_one, WeightedRankLE, RankLE] using h
  exact descendWeighted (F := F) (W := fun _ _ _ => 1) h'

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle

namespace MatrixMultiplicationAllFields.MatrixExponent

theorem descendRank {F : Type*} {L : Type*} [Field F] [Field L] [Algebra F L] [Module.Finite F L]
    {n r : ℕ} (h : RankLE L n r) : RankLE F n (r * Module.finrank F L ^ 2) :=
  Rectangle.descendRank h

end MatrixMultiplicationAllFields.MatrixExponent
