/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenInteriorArithmetic

/-!
# GammaTenStripEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The depth endpoints, in the form the interior envelope device reads

ABK26, Step 2 of `l.approximate.recurrence.formula`,
`e.lower.bound.oscillations`, `e.nablaw.oscillations`.

## Where this module sits

The Besov envelope of Step 2 on the interior mesh is assembled out of four
pieces:

* `Closure.GammaTenInteriorFamily.exists_besovEnvelope_of_family_depth_oscillation`
  --- the envelope device at an **arbitrary** sub-mesh `I`, whose per-depth input
  is `avsum_{R in I} avsum_{R' in desc(R,i)} E[osc_{n-i}(u)(R')^4] <= D i`;
* `Closure.GammaTenInteriorGeometry.cubeFamilyAverage_descendantsAverage_interiorMesoCubeGrid_le`
  --- that per-depth input, on the interior mesh, at the refinement cost `2`,
  read against `interiorMesoCubeGrid d K (n - i) (outer - 1)`;
* `Closure.GammaTenStripEnvelopeConst.sum_depth_fold_const_le` --- the fold of
  `D i = 2 (A cgamma^{16} (1+i) 3^{-i})^4` down to `200 A^4 cgamma^{64}`;
* `Closure.GammaTenInteriorGeometry.exists_gamma_threshold_mesh_boundary_half`
  --- the numerical gate `d 3^{g-p} <= 1/2` the refinement cost needs.

The glue is
`Closure.GammaTenStripEnvelopeConst.exists_besovEnvelope_interiorMesoCubeGrid_of_depth_gridRoot_const`.
Its per-depth binder `hdepth` is stated in exactly the shape the depth-indexed
endpoints of `Closure.GammaTenDepthOscillation` conclude in --- a
`gridFourthMomentRoot` on `interiorMesoCubeGrid d K (n - i) (outer - 1)` below
`A cgamma^{16} (1+i) 3^{-i}` --- and its conclusion is the four-fold shape
`Closure.ClosureInteriorSplit.ClosureInteriorBesovEnvelopeInput` consumes, with
the grid fourth-moment **root** below `cgamma^{15}`.

The endpoints speak of a root and the device reads an average of natural-power
fourth moments.  This module is the one passage between those two forms.

## The window scale is one larger than the endpoints'

The source mesh of the composite is `interiorMesoCubeGrid d K n outer` and its
depth-`i` refinement proves in `interiorMesoCubeGrid d K (n - i) (outer - 1)`,
by
`Closure.GammaTenInteriorGeometry.mem_interiorMesoCubeGrid_of_mem_descendantsAtDepth`.
Since the depth endpoints of `Closure.GammaTenDepthOscillation` live at window
scale `m - h - 1`, the envelope the interior route produces lives at window
scale `outer = m - h`: **one window scale larger** than the endpoints', the
carrier change the interior route forces.  The boundary count survives it: with
`outer + 1 = n + g` the gap is `g = Ngap + 1` and the large-cube gate still
gives `10^{10} cgamma^{-1} <= K - m <= p - g` for `h >= 1`.

## What is proved

* `cubeFamilyAverage_pow_four_le_of_gridFourthMomentRoot_le` --- the passage from
  the endpoints' `gridFourthMomentRoot` form to the family device's
  `cubeFamilyAverage` of natural-power fourth moments.

## Binders

None beyond the root bound itself: the statement holds at an arbitrary finite
family of cubes, an arbitrary measure and an arbitrary sample-indexed cell
functional.  Nothing about the corrector, the coefficient field or the sample
space occurs.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.oscillations`, `e.nablaw.oscillations`, `e.recurrence.params`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]

/-! ## From the endpoints' root form to the device's average form -/

/-- The grid average of the natural-power fourth moments, from the grid
fourth-moment **root**.  Unconditional. -/
theorem cubeFamilyAverage_pow_four_le_of_gridFourthMomentRoot_le
    (mu : Measure Omega) (I : Finset (TriadicCube d)) (F : TriadicCube d → Omega → ℝ)
    {c : ℝ} (h : gridFourthMomentRoot mu I F ≤ c) :
    cubeFamilyAverage I (fun R => ∫ w, F R w ^ (4 : ℕ) ∂mu) ≤ c ^ (4 : ℕ) := by
  have hbase := gridFourthMoment_le_pow_four_of_root_le mu I F h
  have hcongr : (fun R => ∫ w, F R w ^ (4 : ℝ) ∂mu) =
      fun R => ∫ w, F R w ^ (4 : ℕ) ∂mu := by
    funext R
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => rpow_four_eq_pow_four _)
  rwa [gridFourthMoment, hcongr] at hbase

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
