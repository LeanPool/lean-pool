/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Equiv.Prod

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Binary sums of finite coefficient tensors

The coordinate types of the summands may differ.  The identities below give
the explicit changes of coordinates needed for the tensor semiring, together
with the block-diagonal restriction maps.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

variable {K X Y Z U V W A B C : Type*} [CommSemiring K]

/-- The binary direct sum, with each of its three block labels retained. -/
def sumTensor (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X ⊕ U) (Y ⊕ V) (Z ⊕ W)
  | .inl x, .inl y, .inl z => T x y z
  | .inr u, .inr v, .inr w => S u v w
  | .inl _, .inl _, .inr _ => 0
  | .inl _, .inr _, .inl _ => 0
  | .inl _, .inr _, .inr _ => 0
  | .inr _, .inl _, .inl _ => 0
  | .inr _, .inl _, .inr _ => 0
  | .inr _, .inr _, .inl _ => 0

/-- The block-diagonal sum of two restriction matrices. -/
def sumRestriction {X' U' : Type*} (f : X' → X → K) (g : U' → U → K) :
    (X' ⊕ U') → (X ⊕ U) → K
  | .inl x', .inl x => f x' x
  | .inr u', .inr u => g u' u
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0

/-- Independent restrictions of both summands give a restriction of the sum. -/
theorem sumTensor_restrict
    {X' Y' Z' U' V' W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (f : X' → X → K) (g : Y' → Y → K) (h : Z' → Z → K)
    (f' : U' → U → K) (g' : V' → V → K) (h' : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.restrict (sumRestriction f f') (sumRestriction g g')
      (sumRestriction h h') (sumTensor T S) =
      sumTensor (Tensor.restrict f g h T) (Tensor.restrict f' g' h' S) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.restrict, sumRestriction, sumTensor, Fintype.sum_sum_type]

/-- Exchanging the two blocks is a coordinate permutation. -/
theorem sumTensor_comm (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.sumComm X U) (Equiv.sumComm Y V)
      (Equiv.sumComm Z W) (sumTensor S T) = sumTensor T S := by
  funext x y z
  cases x <;> cases y <;> cases z <;> rfl

/-- Reassociating the three blocks is a coordinate permutation. -/
theorem sumTensor_assoc (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.sumAssoc X U A) (Equiv.sumAssoc Y V B)
      (Equiv.sumAssoc Z W C) (sumTensor T (sumTensor S R)) =
      sumTensor (sumTensor T S) R := by
  funext x y z
  rcases x with (x | x) | x <;>
    rcases y with (y | y) | y <;>
    rcases z with (z | z) | z <;> rfl

/-- An empty right summand disappears under its canonical coordinates. -/
theorem sumTensor_empty_right [IsEmpty U] [IsEmpty V] [IsEmpty W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.sumEmpty X U).symm (Equiv.sumEmpty Y V).symm
      (Equiv.sumEmpty Z W).symm (sumTensor T S) = T := by
  rfl

/-- An empty left summand disappears under its canonical coordinates. -/
theorem sumTensor_empty_left [IsEmpty X] [IsEmpty Y] [IsEmpty Z]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.emptySum X U).symm (Equiv.emptySum Y V).symm
      (Equiv.emptySum Z W).symm (sumTensor T S) = S := by
  rfl

/-- Tensor product distributes over the first binary sum by coordinate
permutation. -/
theorem sumTensor_product (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.sumProdDistrib X U A).symm
      (Equiv.sumProdDistrib Y V B).symm (Equiv.sumProdDistrib Z W C).symm
      (Tensor.product (sumTensor T S) R) =
      sumTensor (Tensor.product T R) (Tensor.product S R) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.pullback, Tensor.product, sumTensor]

/-- Tensor product distributes over the second binary sum by coordinate
permutation. -/
theorem product_sumTensor (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.prodSumDistrib X U A).symm
      (Equiv.prodSumDistrib Y V B).symm (Equiv.prodSumDistrib Z W C).symm
      (Tensor.product T (sumTensor S R)) =
      sumTensor (Tensor.product T S) (Tensor.product T R) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.pullback, Tensor.product, sumTensor]

/-- Exchanging product factors is a coordinate permutation. -/
theorem tensorProduct_comm (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.prodComm X U) (Equiv.prodComm Y V)
      (Equiv.prodComm Z W) (Tensor.product S T) = Tensor.product T S := by
  funext x y z
  simp [Tensor.pullback, Tensor.product, mul_comm]

/-- Reassociating product factors is a coordinate permutation. -/
theorem tensorProduct_assoc (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.prodAssoc X U A) (Equiv.prodAssoc Y V B)
      (Equiv.prodAssoc Z W C) (Tensor.product T (Tensor.product S R)) =
      Tensor.product (Tensor.product T S) R := by
  funext x y z
  simp [Tensor.pullback, Tensor.product, mul_assoc]

/-- Scalar multiplication by one is the right unit for tensor product. -/
theorem tensorProduct_one_right (T : Tensor K X Y Z) :
    Tensor.pullback (Equiv.prodPUnit X).symm (Equiv.prodPUnit Y).symm
      (Equiv.prodPUnit Z).symm
      (Tensor.product T (fun (_ _ _ : PUnit) => (1 : K))) = T := by
  funext x y z
  simp [Tensor.pullback, Tensor.product]

/-- Scalar multiplication by one is the left unit for tensor product. -/
theorem tensorProduct_one_left (T : Tensor K X Y Z) :
    Tensor.pullback (Equiv.punitProd X).symm (Equiv.punitProd Y).symm
      (Equiv.punitProd Z).symm
      (Tensor.product (fun (_ _ _ : PUnit) => (1 : K)) T) = T := by
  funext x y z
  simp [Tensor.pullback, Tensor.product]

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
