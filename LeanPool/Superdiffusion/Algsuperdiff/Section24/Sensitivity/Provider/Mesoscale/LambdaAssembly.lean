/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale.Patching
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale.ScaleSelection
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Multiscale.UnitCubeTransfer

/-!
# LambdaAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Assembly of the unconditional `lambda` sensitivity spine

This module assembles the mesoscopic scale selection
(`Mesoscale.ScaleSelection`) with the mesoscale patching estimate
(`Mesoscale.Patching`) and the root transfer of
`Multiscale.UnitCubeTransfer`, producing the exact shape of the frozen
`lambda_sensitivity_unconditional` conclusion

  `(unitCubeLambda t q b)⁻¹ ≤ 6 * (1 + X)^{2t/(1-2s)} * (unitCubeLambda t q a)⁻¹`

for `0 < s, t ≤ 1/4`, every admissible `q` (including `q = infinity`) and every
`X ≥ 0`, from a single *consumption point*: the per-cube ratio estimate with
constant `2` on the triadic descendants of the unit cube at scales at most
`-h`, where `h = mesoscaleDepth s (1 + X)`.

## The literal constant `6`

`6 = 2 * 3`, where the `2` is the factor of the conditional `lambda`
sensitivity estimate at a mesoscopic cube (its smallness parameter is at most
`1` there by `sub_one_mul_three_rpow_neg_mesoscaleDepth_le_one`) and the `3` is
`three_rpow_two_mul_mesoscaleDepth_le`.  Neither the patching step nor the
transfer step loses any constant, so the assembled constant is exactly `6`.

## Consumption points

* `hdeep` in `unitCubeLambda_inv_le_of_mesoscale_descendant_ratio` — the
  per-cube ratio estimate on descendant cubes.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.  The public unconditional statements will be obtained by
discharging the consumption points, never by carrying them.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The assembled unconditional shape -/

/-- **The unconditional `lambda` spine.**  From the per-cube ratio estimate with
constant `2` on all triadic descendants of the unit cube at scales at most
`-h`, with `h = mesoscaleDepth s (1 + X)`, one obtains the exact frozen shape
of `lambda_sensitivity_unconditional`, with the literal constant `6` and the
exponent `2t/(1-2s)`, for every admissible `q` including `q = infinity`. -/
theorem unitCubeLambda_inv_le_of_mesoscale_descendant_ratio
    (a b : CoeffOn (cubeDomain (originCube d 0))) {s t X : ℝ}
    {q : Ch02.MultiscaleExponent}
    (hs0 : 0 < s) (hs : s ≤ 1 / 4) (ht0 : 0 < t) (ht : t ≤ 1 / 4)
    (hq : q.IsAdmissible) (hX : 0 ≤ X)
    (hdeep : ∀ F G : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
      CoeffOn.AEEq (G.coeffOn (originCube d 0)) b →
      ∀ k : ℤ, k ≤ (originCube d 0).scale - (mesoscaleDepth s (1 + X) : ℤ) →
        ∀ R ∈ descendantsAtScale (originCube d 0) k,
          coarseSigmaStarInvMatrixNorm R G ≤ 2 * coarseSigmaStarInvMatrixNorm R F) :
    (unitCubeLambda t q b)⁻¹ ≤
      6 * Real.rpow (1 + X) (2 * t / (1 - 2 * s)) * (unitCubeLambda t q a)⁻¹ := by
  have hu : (1 : ℝ) ≤ 1 + X := by linarith
  refine unitCubeLambda_inv_le_of_family_bound a b t q _ ?_
  intro F G hF hG
  have hpatch := lambdaSq_inv_le_of_deep_descendant_ratio (originCube d 0) F G
    (mesoscaleDepth s (1 + X)) (by norm_num : (0 : ℝ) ≤ 2) ht0 hq (hdeep F G hF hG)
  refine hpatch.trans ?_
  have hY0 : (0 : ℝ) ≤ (Ch02.lambdaSq (originCube d 0) t q F)⁻¹ :=
    inv_nonneg.mpr (lambdaSq_nonneg (originCube d 0) F ht0 hq)
  refine mul_le_mul_of_nonneg_right ?_ hY0
  have hscale := three_rpow_two_mul_mesoscaleDepth_le hs0 hs hu ht0.le ht
  linarith [hscale]

end

end Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale
