/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationMeshTransfer

/-!
# GammaTenStripTransfer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Signed boundary transfer on recurrence meshes

The earlier `LocalizationFluctuationMeshTransfer` module proves the signed
finite-grid transfer under its original `Closure` name and derives the
nonnegative estimate from it. This module combines that shared transfer with
the recurrence's boundary count, retaining arbitrary real families and the
scale bookkeeping `K = n + p`, `outer + 1 = n + g`, `g ≤ p`.

The Step-2 fluctuation integrand is a difference of energies and can have either
sign. The signed transfer uses the nonnegative part of its interior average.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.localization.terms`, `e.recurrence.params`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

variable {d : ℕ}

/-! ## The signed split at the recurrence's own two meshes -/

/-- **The signed boundary split on the mesh.**

The full-mesh average of an arbitrary real family is below the truncated interior
average plus `sqrt(d 3^{g-p})` times the square root of the full-mesh average of
its square.  The signed mirror of
`LocalizationFluctuationMeshTransfer.gridFourthMoment_mesoCubeGrid_le_interior_add`.

only on the scale bookkeeping. -/
theorem cubeFamilyAverage_mesoCubeGrid_le_max_interior_add (d : ℕ) {K n outer : ℤ}
    {p g : ℕ} (hK : K = n + (p : ℤ)) (houter : outer + 1 = n + (g : ℤ)) (hgp : g ≤ p)
    (F : TriadicCube d → ℝ) :
    cubeFamilyAverage (mesoCubeGrid d K n) F ≤
      max (cubeFamilyAverage (interiorMesoCubeGrid d K n outer) F) 0 +
        Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p)) *
          Real.sqrt (cubeFamilyAverage (mesoCubeGrid d K n) (fun R => F R ^ 2)) := by
  have hmain := cubeFamilyAverage_le_max_add_sqrt_boundaryFraction
    (I := mesoCubeGrid d K n) (J := interiorMesoCubeGrid d K n outer)
    interiorMesoCubeGrid_subset F
  have hfrac : Real.sqrt (1 - ((interiorMesoCubeGrid d K n outer).card : ℝ) /
        ((mesoCubeGrid d K n).card : ℝ)) ≤
      Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p)) :=
    Real.sqrt_le_sqrt (one_sub_interior_card_ratio_le d hK houter hgp)
  have hsq : (0 : ℝ) ≤ Real.sqrt (cubeFamilyAverage (mesoCubeGrid d K n)
      (fun R => F R ^ 2)) := Real.sqrt_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hfrac hsq
  linarith [hmain, hmul]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
