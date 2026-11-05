/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxHalfLevel

/-!
# HomSeamFluxHalfBundle

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The re-cut bundle with the Step-4 gauge re-pinned to `α = 1/2`

## The split this file performs

The re-cut bundle at a single order binds ONE order `s` and
uses it for THREE different jobs:

1. the multiscale/Step-3c base order (the coarse-graining clause, the energy
   partial sums, `hlevel`, and the lifting factor of `spineClauseConst`);
2. the Hölder gauge `α` of the Step-4 dual test (`cgTestConst d □_m α s′ p′` and
   the matching scale power `3^{αm}` in `hlevelDual`);
3. the order at which the produced `WeakNegDualBoundOn` is read, hence the
   Hölder order at which `∇v` is paired.

Job 1 is genuinely at `s = |log γ|⁻¹`.  Jobs 2 and 3 are at `1/2` in the print:
the Step-4 test is `∇v`, and its only regularity is the `C^{0,1/2}` Schauder
estimate.  Identifying 2 and 3 with 1 is OUR wiring, and it is what makes the
test-class conversion's order gap `α - s′ = s/8` close with `s`, which is the
divergence.

This file re-cuts jobs 2 and 3 at `1/2` and leaves job 1 alone.

## The cascade, measured

The split does NOT propagate:

* `HomSeamFluxLane.exists_weakNegDualBounds_of_fluxPair` already binds its four
  orders `(s₁′, s′, s₂, α)` SEPARATELY — no hypothesis ties `α` to the base
  order; only `0 < (α - s′)p′ < d` is asked, and at `α = 1/2` both halves are
  free (`cgOrderWindow_half`, `cgOrderWindowHi_half`);
* `HomSeamFluxLane.stepFourEnergyFlux_of_dualBounds_uniform` is stated for every
  `0 < α ≤ 1/2`, so `α = 1/2` is its own endpoint, at the `s`-FREE constant
  `stepFourSchauderConstU d` it already uses;
* `spineClauseConst d s p C_w C_sch` is untouched: its Step-4 leg `2 C_w C_sch`
  never mentions an order, and its Step-3c leg `96 d² liftGeomFactor(s + d/p)`
  is at job 1's order, unchanged;
* the clause supplier, the consumer, mentions no order
  at all.

So the re-cut stops one theorem below the supplier interface: the produced
`HomSpineClauseSupplierAt` is BYTE-IDENTICAL to the one.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The upper half of the conversion window at `α = 1/2` -/

/-- The Gagliardo window's upper end at the re-pin.  At `α = 1/2` the order gap
is at most `1/2` and the dual exponent at most `2`, so the product is at most
`1`, which is `< d` for every `d ≥ 2`.  (The order-window check at the printed
gauge needed the gap `≤ 1/4`; here the crude bound suffices.) -/
theorem cgOrderWindowHi_half {p : FiniteLpExponent} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s)
    (hp2 : (2 : ℝ≥0∞) ≤ p.exponent) :
    (1 / 2 - 7 * s / 8) * p.conjugate.exponent.toReal < (d : ℝ) := by
  have ht2 : p.conjugate.exponent.toReal ≤ 2 := conjugate_toReal_le_two hp2
  have htpos : 0 < p.conjugate.exponent.toReal :=
    finiteLpExponent_toReal_pos p.conjugate
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hgap : 1 / 2 - 7 * s / 8 < 1 / 2 := by linarith only [hs0]
  have hstep : (1 / 2 - 7 * s / 8) * p.conjugate.exponent.toReal <
      1 / 2 * p.conjugate.exponent.toReal :=
    mul_lt_mul_of_pos_right hgap htpos
  have hhalf : 1 / 2 * p.conjugate.exponent.toReal ≤ 1 := by linarith only [ht2]
  linarith only [hstep, hhalf, hdR]

end

end Algsuperdiff.Section4.Provider.Homogenization
