/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Hooley.HooleyLogarithmicSaving

/-! # A uniform negligible tail for large divisor-window counts -/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial Filter
open scoped Topology

/-- The part of the divisor-window sum above the Hooley truncation threshold. -/
noncomputable def polynomialDivisorLargeSum (Q : ℤ[X]) (η x y : ℝ) : ℝ :=
  ∑ n ∈ (shortInterval x y).filter
    (fun n : ℕ => (Real.log x) ^ η < (dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y : ℝ)),
    (dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y : ℝ)

end NairTenenbaum
