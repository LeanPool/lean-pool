/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionSeam2
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementTranslation

/-!
# LayerPerCubePricing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Seam 2, per-cube pricing: the ladder

`Provider/Multiscale/ConclusionSeam2.lean` currently prices a whole Whitney
layer by DOMINATING it with the root cube: its
`sum_cubeMassRatio_mul_cubeAverage_le_streamIncrementLpMass` bounds the
volume-weighted layer mass by `streamIncrementLpMass p m n1 n2`, and the
layer's own mass fraction is thrown away.  The corrected Step-3 aggregation,
with the exponent bookkeeping amended, asks for something else: the translated
`Gamma_2` wave estimate applied to the squared variables, then the
normalized `Gamma` triangle inequality over the layer, then the square root.

This module supplies the measurability input that the first rung of that ladder
needs.

## The ladder

For a sub-family `S` of the depth-`j` descendants of `cu_m` (the Whitney layer
is such a sub-family, by `mem_descendantsAtDepth_of_mem_whitneyLayer`):

```
  per cube          ||k_{n2} - k_{n1}||_{Lbar^p(Q)}   =  O_{Gamma_2}( normScale ) ,
  fourth powers     avg_Q |k_{n2}-k_{n1}|^p           =  O_{Gamma_{2/p}}( massScale ) ,
  weighted sum      sum_Q w_Q avg_Q ...               =  O_{Gamma_{2/p}}( C_tri massScale ) ,
  square root (p=4) sqrt( sum_Q w_Q avg_Q ... )       =  O_{Gamma_1}( sqrt(C_tri massScale) ) .
```

## What is NOT claimed

* No per-layer geometric weight (in particular no `3^{-3k/4}`) appears
  anywhere:.
* No large-scale gain is claimed: the amplitude is the `Q`-uniform envelope of
  `e.kmn.bounds`.  The gain lives in
  `Stream.cubeStreamIncrementLpNorm_head_tail_gain`.
* `ConclusionSeam2` is NOT rewired.

## Main results

* `Algsuperdiff.Section3.Provider.Multiscale.measurable_cubeAverage_streamIncrementLpDensity`:
  the per-cube `L^p` mass is a random variable, being the origin-cube mass at
  the cube's own scale read at the translated sample.

## References

* ABK26, (the Step-3 aggregation), `e.kmn.bounds`.
* `Provider/Stream/IncrementTranslation.lean` (the per-cube generator),
  `Provider/Multiscale/ConclusionSeam2.lean` (the consumer that this module
  prepares, and does not edit).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## The weights are normalized -/


/-! ## Measurability of the per-cube mass -/

/-- The per-cube `L^p` mass is a random variable: it is the origin-cube mass at
scale `Q.scale`, read at the translated sample. -/
theorem measurable_cubeAverage_streamIncrementLpDensity {p : ℝ} (hp : 0 < p)
    (Q : TriadicCube d) (n1 n2 : ℤ) :
    Measurable fun omega : ShellSeq d =>
      cubeAverage Q (streamIncrementLpDensity p n1 n2 omega) := by
  have hrw : (fun omega : ShellSeq d =>
      cubeAverage Q (streamIncrementLpDensity p n1 n2 omega)) =
      fun omega : ShellSeq d => streamIncrementLpMass p Q.scale n1 n2
        (ShellField.translateSequence (triadicCubeShift Q) omega) :=
    funext fun omega =>
      cubeAverage_streamIncrementLpDensity_eq_streamIncrementLpMass_translate hp Q n1 n2 omega
  rw [hrw]
  exact (measurable_streamIncrementLpMass hp Q.scale n1 n2).comp
    (ShellField.measurable_translateSequence (triadicCubeShift Q))

/-! ## The per-cube-priced layer bound -/


end

end Algsuperdiff.Section3.Provider.Multiscale
