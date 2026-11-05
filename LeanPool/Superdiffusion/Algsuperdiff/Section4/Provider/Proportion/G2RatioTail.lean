/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2Concentration
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2Arith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2CubeBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.RatioTailArith

/-!
# G2RatioTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two per-cube amplitudes of the `𝒢₂` lane

ABK26, §4.1, `l.ratio.of.good.scales.for.mathcal.E` composed into
`e.no.bad.scales.applied.for.lambdas` for the `𝒢₂` lane.

* `cubeAmpOne` — the `Γ_2`-lane per-cube amplitude produced by the Section 3
  anchor through `G2CubeBound`: `√3·(1+2d log 3)^{1/2}·C c⋆^{−1}s^{−1}√γ`;
* `cubeAmpTwo` — the `Γ_{1/2}`-lane per-cube amplitude of the same anchor:
  `√3·(1+2d log 3)²·exp(−C^{−1}c⋆³γ^{−1})`.

## Scope

Provider material: proved local helpers.  The `c⋆^{10}` regime is carried
explicitly, exactly as the anchor states it.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

variable {d : ℕ}

/-! ## 1. The two per-cube amplitudes of the anchor -/

/-- The `Γ_2`-lane per-cube amplitude produced by the Section 3 anchor through
`G2CubeBound`: `√3·(1+2d log 3)^{1/2}·C c⋆^{−1}s^{−1}√γ`. -/
def cubeAmpOne (d : ℕ) (C : ℝ) (M : ABKModel d) (s : ℝ) : ℝ :=
  Real.sqrt 3 * (annulusPenalty d 2 1 *
    (C * (Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma))

/-- The `Γ_{1/2}`-lane per-cube amplitude produced by the Section 3 anchor through
`G2CubeBound`: `√3·(1+2d log 3)²·exp(−C^{−1}c⋆³γ^{−1})`. -/
def cubeAmpTwo (d : ℕ) (C : ℝ) (M : ABKModel d) : ℝ :=
  Real.sqrt 3 * (annulusPenalty d (1 / 2) 1 *
    Real.exp (-(C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹)))

end

end Algsuperdiff.Section4.Provider.Proportion
