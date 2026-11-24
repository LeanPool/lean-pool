/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Algebra.Lie.BCH.CommutatorFamily

/-!
# The quintic Suzuki combination of binary commutators

The eight quadratic scalar polynomials use a representation with zero coefficients
at zero-based indices `2` and `6`. They are reduced using `4p³ + (1 - 4p)³ = 0`.
Their linear combination is defined for every parameter in an arbitrary field algebra;
its identification with the five-stage Strang logarithm requires cubic cancellation.

## Main definitions

* `suzukiQuinticCoeff`: the eight signed coefficient polynomials.
* `suzukiQuinticTerm`: their linear combination of the binary quintic commutators.
-/

@[expose] public noncomputable section

namespace FQFP.BCH

/-- The signed quintic Suzuki coefficients in the eight-element binary commutator family,
reduced by cubic cancellation. Indices `2` and `6` are zero. -/
def suzukiQuinticCoeff {K : Type*} [Field K] (p : K) : Fin 8 → K :=
  ![127 * p ^ 2 / 144000 + 13 * p / 36000 - 1 / 24000,
    p ^ 2 / 12000 + 13 * p / 6000 - 1 / 4000,
    0,
    -61 * p ^ 2 / 9000 + 13 * p / 3000 - 1 / 2000,
    31 * p ^ 2 / 9000 - 13 * p / 18000 + 1 / 12000,
    31 * p ^ 2 / 3000 - 13 * p / 6000 + 1 / 4000,
    0,
    p ^ 2 / 18000 + 13 * p / 9000 - 1 / 6000]

/-- The reduced quintic combination for an arbitrary parameter. Under cubic cancellation
it is the coefficient `L₅` in the five-stage Strang logarithm. -/
def suzukiQuinticTerm {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (a b : A) (p : K) : A :=
  ∑ i : Fin 8, suzukiQuinticCoeff p i • binaryQuinticCommutator a b i

end FQFP.BCH
