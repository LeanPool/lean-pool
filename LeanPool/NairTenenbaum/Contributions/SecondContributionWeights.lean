/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.ValueWeightBounds
public import LeanPool.NairTenenbaum.Contributions.SecondContributionCounting

/-! # The weighted second-class exceptional sum -/

@[expose] public section

namespace NairTenenbaum

/-- The arithmetic contribution of the small-prime power exceptional set. -/
noncomputable def PolynomialSystem.primePowerContribution {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (z : ℝ) (a b : ℤ) : ℝ :=
  ∑ t ∈ primePowerExceptionalSet P.R z (z ^ 3) a b,
    extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)

end NairTenenbaum
