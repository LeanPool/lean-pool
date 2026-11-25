/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Model

/-! # Bilinear formulas with a private product for each output -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Interior

/-- Coefficients of a decomposable bilinear form. -/
structure Product (F : Type*) (X Y : Type) where
  /-- The left-side data carried by `Product`, with type `X → F`. -/
  left : X → F
  /-- The right-side data carried by `Product`, with type `Y → F`. -/
  right : Y → F

/-- The quantity computed by `p.left x * p.right y`. -/
def Product.apply {F : Type*} [Mul F] {X Y : Type} (p : Product F X Y) (x : X) (y : Y) :=
  p.left x * p.right y

/-- Each output reads its own product and a linear combination of
common products. No other output reads the private product. -/
def Private {F : Type*} [Field F] {X Y Z : Type} (M : Z → X → Y → F) (r : ℕ) : Prop :=
  ∃ (a : Z → Product F X Y) (b : Fin r → Product F X Y) (c : Z → Fin r → F),
    ∀ z x y, M z x y = (a z).apply x y + ∑ l, c z l * (b l).apply x y

/-- Requires `Private (fun (z : Pos i j) (x : Pos i k) (y : Pos k j) => if x.1 = z.1 ∧ x.2 = y.1
∧ y.2 = z.2 then (1 : F) else 0) r`. -/
def PrivateProducts (F : Type*) [Field F] (i j k r : ℕ) : Prop :=
  Private (fun (z : Pos i j) (x : Pos i k) (y : Pos k j) =>
    if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then (1 : F) else 0) r

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Interior
