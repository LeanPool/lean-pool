/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ZerothOrderGradient
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.SchauderRepresentative

/-!
# ZerothOrderSchauder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Interior Schauder estimate with a bounded scalar source
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport Filter Topology
open Algsuperdiff.Section4.Support

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Dimension coefficient for the Hölder row with scalar forcing. -/
def smallContrastZerothHolderOutputConstant (d : ℕ) [NeZero d] : ℝ :=
  (smallContrastHolderChainLength d : ℝ) *
    smallContrastLocalHolderConstant d * smallContrastZerothGradientConstant d

theorem smallContrastZerothHolderOutputConstant_nonneg (d : ℕ) [NeZero d] :
    0 ≤ smallContrastZerothHolderOutputConstant d := by
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (smallContrastLocalHolderConstant_nonneg d))
    (smallContrastZerothGradientConstant_nonneg d)

/-- The single dimension coefficient in the zeroth-order estimate. -/
def smallContrastZerothSchauderConstant (d : ℕ) [NeZero d] : ℝ :=
  max (smallContrastZerothGradientConstant d)
    (smallContrastZerothHolderOutputConstant d)

theorem smallContrastZerothSchauderConstant_nonneg (d : ℕ) [NeZero d] :
    0 ≤ smallContrastZerothSchauderConstant d :=
  (smallContrastZerothGradientConstant_nonneg d).trans (le_max_left _ _)

/-- Full representative and gradient conclusion for a bounded scalar source. -/
theorem smallContrastSchauder_zerothOrder [NeZero d]
    {a : CoeffField d} {u : H1Function (smallContrastUnitBall d)}
    {g : Vec d → ℝ} {f : Vec d → Vec d} {delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hmeas : Measurable a)
    (ha : CoefficientIdentityDistanceLE (smallContrastUnitBall d) a delta)
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a (smallContrastUnitBall d) u g f)
    (hg : MemScalarLInfOn (smallContrastUnitBall d) g)
    (hf : MemVectorLpOn (smallContrastUnitBall d) (schauderSourceExponent d alpha) f) :
    SmallContrastSchauderConclusion alpha
      (smallContrastZerothSchauderConstant d *
        smallContrastZerothOrderDataSize d alpha u f g) u := by
  let D := smallContrastZerothOrderDataSize d alpha u f g
  have hD : 0 ≤ D := smallContrastZerothOrderDataSize_nonneg halpha.2 u f g
  have hgrad := gradientScaleBound_of_smallContrast_zerothOrder
    hd halpha hdelta0 hdelta hmeas ha hu hg hf
  have hgradInterior := interiorGradientScaleBound_of_smallContrast_zerothOrder
    hd halpha hdelta0 hdelta hmeas ha hu hg hf
  have hcamp := ballCampanatoBound_of_interiorGradient halpha hgradInterior
  constructor
  · intro r hr hr1
    exact (hgrad r hr hr1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hD)
  · refine ⟨smallContrastSchauderRepresentative u,
      continuousOn_smallContrastSchauderRepresentative halpha
        (mul_nonneg (smallContrastZerothGradientConstant_nonneg d) hD) hcamp,
      smallContrastSchauderRepresentative_ae_eq halpha hcamp, ?_⟩
    intro x hx y hy
    have hsup := holder_smallContrastCampanatoRepresentative halpha
      (mul_nonneg (smallContrastZerothGradientConstant_nonneg d) hD) hcamp
      (x := x) (y := y) hx hy
    have hpow : ‖x - y‖ ^ alpha ≤ euclideanNorm (x - y) ^ alpha :=
      Real.rpow_le_rpow (norm_nonneg _) (norm_le_euclideanNorm _)
        (le_trans (by norm_num) halpha.1)
    have hholderCoeff : 0 ≤
        (smallContrastHolderChainLength d : ℝ) *
          smallContrastLocalHolderConstant d * smallContrastZerothGradientConstant d * D :=
      mul_nonneg (smallContrastZerothHolderOutputConstant_nonneg d) hD
    rw [smallContrastSchauderRepresentative_of_mem hx,
      smallContrastSchauderRepresentative_of_mem hy]
    calc
      |smallContrastCampanatoRepresentative (d := d) u.toFun x -
          smallContrastCampanatoRepresentative (d := d) u.toFun y| ≤
          (smallContrastHolderChainLength d : ℝ) *
            smallContrastLocalHolderConstant d *
              (smallContrastZerothGradientConstant d * D) * ‖x - y‖ ^ alpha := hsup
      _ = smallContrastZerothHolderOutputConstant d * D * ‖x - y‖ ^ alpha := by
        rw [smallContrastZerothHolderOutputConstant]
        ring
      _ ≤ smallContrastZerothHolderOutputConstant d * D *
          euclideanNorm (x - y) ^ alpha := mul_le_mul_of_nonneg_left hpow hholderCoeff
      _ ≤ smallContrastZerothSchauderConstant d * D *
          euclideanNorm (x - y) ^ alpha := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hD)
          (Real.rpow_nonneg (euclideanNorm_nonneg _) _)

/-- Interior Schauder estimate with `g` in `L^infinity`; the scalar term has
no factor `(1-alpha)⁻¹`. -/
theorem schauder_interior_holder_zerothOrder [NeZero d]
    {a : CoeffField d} {u : H1Function (smallContrastUnitBall d)}
    {g : Vec d → ℝ} {f : Vec d → Vec d} {delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hmeas : Measurable a)
    (ha : CoefficientIdentityDistanceLE (smallContrastUnitBall d) a delta)
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a (smallContrastUnitBall d) u g f)
    (hg : MemScalarLInfOn (smallContrastUnitBall d) g)
    (hf : MemVectorLpOn (smallContrastUnitBall d) (schauderSourceExponent d alpha) f) :
    SmallContrastSchauderConclusion alpha
      (smallContrastZerothSchauderConstant d *
        smallContrastZerothOrderDataSize d alpha u f g) u :=
  smallContrastSchauder_zerothOrder hd halpha hdelta0 hdelta hmeas ha hu hg hf

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
