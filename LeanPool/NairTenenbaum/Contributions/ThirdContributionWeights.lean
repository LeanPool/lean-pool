/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.ValueWeightBounds
public import LeanPool.NairTenenbaum.Smooth.SmoothDivisorCounting

/-! # The weighted sum over large smooth divisor tuples -/

@[expose] public section

namespace NairTenenbaum

/-- The arithmetic contribution of values with a large smooth radical divisor. -/
noncomputable def PolynomialSystem.smoothDivisorContribution {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (s : Finset ℕ) (N : ℕ+) (T : ℝ) (a b : ℤ) : ℝ :=
  ∑ t ∈ smoothDivisorExceptionalSet P.radical s N T a b,
    extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)

end NairTenenbaum
