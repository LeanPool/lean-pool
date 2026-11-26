/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Bounds
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Character.DotsPower
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.RectangularRank

/-!
# From the character estimate to rectangular algorithms

Each pairing belongs to the two legs other than its named leg. Reading
the first two legs as inputs and the third as output gives a rank bound
on the formal product. Ceiling costs at most a factor of two per pairing.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Integral
open Rectangle
open Upper Upper.TensorClass

/-- The product of dot tensors for a rectangular matrix shape. -/
abbrev dots := TensorSpectrum.TensorClass.dots (K := O)

theorem dots_power (i j k t : ℕ) :
    dots (i ^ t) (j ^ t) (k ^ t) = (dots i j k) ^ t :=
  TensorSpectrum.TensorClass.dots_power i j k t

theorem rank_of_dots {i j k r : ℕ} (h : dots i j k ≤ (r : TensorClass)) :
    Rank O i j k r := by
  obtain ⟨a, b, c, hcoeff⟩ := TensorSpectrum.TensorClass.rank_of_dots h
  exact ⟨a, b, c, fun x y z => (congrFun (congrFun (congrFun hcoeff x) y) z).symm⟩

export MatrixMultiplicationAllFields.MatrixExponent.Rectangle (rounded_dot)

theorem price_dots (f : Character) {n : ℕ} (hn : 0 < n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (f (dots (side n a) (side n b) (side n c)) : ℝ) ≤
      8 * (n : ℝ) ^ (b * f.pX + a * f.pY + c * f.pZ) :=
  TensorSpectrum.TensorClass.price_dots f hn ha hb hc


end MatrixMultiplicationAllFields.MatrixExponent.Integral
