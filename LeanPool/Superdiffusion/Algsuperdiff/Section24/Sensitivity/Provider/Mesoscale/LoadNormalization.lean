/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale.ScaleSelection
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Multiscale.UnitCubeTransfer

/-!
# LoadNormalization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Load normalization for the unconditional response estimate

The unconditional response estimate is proved at the loading `((mu
sigma0)^{-1/2} e, (mu sigma0)^{1/2} e)`.  The source first removes the `mu`-part
of the loading with `e.shaking.lambda`

applied with `lam = mu`, `p = sigma0^{-1/2} e` and `q = sigma0^{1/2} e`, and then
applies the conditional response estimate cube-by-cube at the mesoscopic scale.

This module contains the *load-normalization algebra* of that step, together
with the mesoscale factor bookkeeping of the four frozen terms of
`responseJ_sensitivity_unconditional`.  Everything here is proved.

## What is here

* `le_of_shaking_lambda_bound` — the gauge-free arithmetic that turns the
  square on the right of `e.shaking.lambda` into the two frozen terms
  `2 mu^{-1} J` and `mu^{-1} (mu - 1)^2 V`.

## Consumption points (deliberately NOT proved here)

1. **`e.shaking.lambda`.**  There is no Lean declaration for it in
   CoarseGraining or in this repository (only the exact scaling identity
   `responseJ_homogeneous`).  `le_of_shaking_lambda_bound` is written so that
   the shaking-lambda inequality enters as a hypothesis of the *caller*, not of
   any statement of this module.
2. **The conditional response estimate at mesoscopic cubes** (frozen theorem
   `responseJ_sensitivity` at `delta = 1`), stated on descendant cubes.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02

noncomputable section

/-! ## The `mu`-normalization arithmetic -/

/-- **The `mu`-normalization arithmetic of `e.shaking.lambda`.**  Any quantity
bounded by the right-hand side of the shaking-lambda inequality at `lam = mu` is
bounded by the two frozen terms `2 mu^{-1} J` and `mu^{-1} (mu - 1)^2 V`.

The shaking-lambda inequality itself is a consumption point: it enters as the
hypothesis `hK` supplied by the caller. -/
theorem le_of_shaking_lambda_bound {K J V μ : ℝ} (hμ : 0 < μ) (hJ : 0 ≤ J)
    (hV : 0 ≤ V)
    (hK : K ≤ μ⁻¹ * (Real.sqrt J + Real.sqrt 2⁻¹ * |μ - 1| * Real.sqrt V) ^ 2) :
    K ≤ 2 * μ⁻¹ * J + μ⁻¹ * (μ - 1) ^ 2 * V := by
  have hμinv : 0 < μ⁻¹ := inv_pos.mpr hμ
  have hsJ : Real.sqrt J ^ 2 = J := Real.sq_sqrt hJ
  have hsV : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV
  have hs2 : Real.sqrt 2⁻¹ ^ 2 = 2⁻¹ := Real.sq_sqrt (by norm_num)
  have habs : |μ - 1| ^ 2 = (μ - 1) ^ 2 := sq_abs _
  have hexpand : (Real.sqrt J + Real.sqrt 2⁻¹ * |μ - 1| * Real.sqrt V) ^ 2 ≤
      2 * J + (μ - 1) ^ 2 * V := by
    have hsq : 0 ≤ (Real.sqrt J - Real.sqrt 2⁻¹ * |μ - 1| * Real.sqrt V) ^ 2 :=
      sq_nonneg _
    have hkey : (Real.sqrt J + Real.sqrt 2⁻¹ * |μ - 1| * Real.sqrt V) ^ 2 ≤
        2 * Real.sqrt J ^ 2 +
          2 * (Real.sqrt 2⁻¹ ^ 2 * |μ - 1| ^ 2 * Real.sqrt V ^ 2) := by
      nlinarith [hsq]
    rw [hsJ, hsV, hs2, habs] at hkey
    linarith
  calc K ≤ μ⁻¹ * (Real.sqrt J + Real.sqrt 2⁻¹ * |μ - 1| * Real.sqrt V) ^ 2 := hK
    _ ≤ μ⁻¹ * (2 * J + (μ - 1) ^ 2 * V) :=
        mul_le_mul_of_nonneg_left hexpand hμinv.le
    _ = 2 * μ⁻¹ * J + μ⁻¹ * (μ - 1) ^ 2 * V := by ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale
