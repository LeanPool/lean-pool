/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Fin.VecNotation

/-! # The one-sided coordinate derivatives of an exponent -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle
open Set

/-- Changes the chosen one of three weights before applying the comparison function. -/
def vary (L : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) (e : Fin 3) (t : ℝ) : ℝ :=
  ![L (a + t) b c, L a (b + t) c, L a b (c + t)] e

/-- Computes the partial right by the application `derivWithin (vary L a b c e) (Ici 0) 0`. -/
def partialRight (L : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) (e : Fin 3) : ℝ :=
  derivWithin (vary L a b c e) (Ici 0) 0

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle
