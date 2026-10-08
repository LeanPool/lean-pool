/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.FillingCoefficientAbsorption

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.EnergyPrice.ResidualWindowFillingBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The filling coefficient on the residual window `λ ∈ [1,3]`

The energy leg never evaluates `observationFillingCoefficient` at the physical
`ε`: `RowRetainingPrintOrderGoodScale.exists_residualFrameResponseRate`
evaluates it at the residual dilation `λ = ε·3^N ∈ Set.Icc 1 3` produced by the
triadic `ε`-frame transport
`RowRetainingPrintOrderGoodScale.exists_scaledResponseWindowTail`, whose
hypotheses are exactly the binder surface used here.

`HCPoly.Provider.PolynomialHomogenization.Root.EnergyPrice.FillingCoefficientAbsorption`
bounded the coefficient for `ε ≤ 1`.  The residual window needs `λ ≤ 3`, so the absorption is
restated here
with an arbitrary upper bound on the dilation.
-/

namespace HCPolySupport
namespace HighContrast
namespace EnergyPrice

open Book Book.Ch03
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The filling coefficient under a bounded dilation.**  The absolute gauge
scale `α` is absorbed by the inner-ellipsoid premise and the consumer's
outer ball; the dilation contributes only its own upper bound. -/
theorem observationFillingCoefficient_le_of_boundedDilation [NeZero d]
    {abar : Mat d} {U : Set (Vec d)} {cc : Vec d} {epsilon B Rad : ℝ}
    (hS : (symmPart abar).PosDef) (hepsilon : 0 < epsilon)
    (hepsilonB : epsilon ≤ B) (hRad : 0 ≤ Rad)
    (hInner : ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U)
    (hOut : matImage (matSqrt (symmPart abar))⁻¹ U ⊆ euclideanBallAt cc Rad) :
    RowSupply.observationFillingCoefficient d epsilon abar ≤
      max 1 (18 * (d : ℝ) ^ 2 * B * Rad) := by
  have hd : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hsqrtd : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd
  have hsqrtsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
    Real.mul_self_sqrt hd.le
  set alpha : ℝ := Real.sqrt (specBound ((symmPart abar)⁻¹)) with halphaDef
  have halpha0 : 0 ≤ alpha := Real.sqrt_nonneg _
  have hcpos : (0 : ℝ) ≤ 1 / (3 * Real.sqrt (d : ℝ)) := by positivity
  have hkey := normalizedRootScale_mul_le_of_innerEllipsoid_outerBall
    hS hcpos hRad hInner hOut
  rw [← halphaDef] at hkey
  have halphaBound : alpha ≤ 3 * Real.sqrt (d : ℝ) * Rad := by
    have h3 : (0 : ℝ) < 3 * Real.sqrt (d : ℝ) := by positivity
    have hrw : alpha * (1 / (3 * Real.sqrt (d : ℝ))) =
        alpha / (3 * Real.sqrt (d : ℝ)) := by ring
    rw [hrw, div_le_iff₀ h3] at hkey
    linarith only [hkey]
  have hepsAlpha : epsilon * alpha ≤ B * (3 * Real.sqrt (d : ℝ) * Rad) := by
    have hB0 : 0 ≤ B := le_trans hepsilon.le hepsilonB
    calc
      epsilon * alpha ≤ B * alpha :=
        mul_le_mul_of_nonneg_right hepsilonB halpha0
      _ ≤ B * (3 * Real.sqrt (d : ℝ) * Rad) :=
        mul_le_mul_of_nonneg_left halphaBound hB0
  have hcoef : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt (d : ℝ) := by positivity
  have hmain :
      6 * (d : ℝ) * Real.sqrt (d : ℝ) * (epsilon * alpha) ≤
        18 * (d : ℝ) ^ 2 * B * Rad := by
    calc
      6 * (d : ℝ) * Real.sqrt (d : ℝ) * (epsilon * alpha) ≤
          6 * (d : ℝ) * Real.sqrt (d : ℝ) *
            (B * (3 * Real.sqrt (d : ℝ) * Rad)) :=
        mul_le_mul_of_nonneg_left hepsAlpha hcoef
      _ = 18 * (d : ℝ) *
            (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) * B * Rad := by ring
      _ = 18 * (d : ℝ) ^ 2 * B * Rad := by rw [hsqrtsq]; ring
  rw [RowSupply.observationFillingCoefficient_eq_absoluteScale hepsilon hS,
    ← halphaDef]
  exact max_le_max (le_refl 1) hmain

/-- **The residual-window instance.**  On the residual window
`λ ∈ [1,3]` the filling coefficient is bounded by a function of `d` and the
outer radius only — the form the energy leg needs. -/
theorem observationFillingCoefficient_le_of_residualWindow [NeZero d]
    {abar : Mat d} {U : Set (Vec d)} {cc : Vec d} {lambda Rad : ℝ}
    (hS : (symmPart abar).PosDef) (hlambda : lambda ∈ Set.Icc (1 : ℝ) 3)
    (hRad : 0 ≤ Rad)
    (hInner : ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U)
    (hOut : matImage (matSqrt (symmPart abar))⁻¹ U ⊆ euclideanBallAt cc Rad) :
    RowSupply.observationFillingCoefficient d lambda abar ≤
      max 1 (54 * (d : ℝ) ^ 2 * Rad) := by
  have hpos : (0 : ℝ) < lambda := lt_of_lt_of_le zero_lt_one hlambda.1
  have hbase := observationFillingCoefficient_le_of_boundedDilation
    (B := (3 : ℝ)) hS hpos hlambda.2 hRad hInner hOut
  have hrw : 18 * (d : ℝ) ^ 2 * 3 * Rad = 54 * (d : ℝ) ^ 2 * Rad := by ring
  rwa [hrw] at hbase

end

end EnergyPrice
end HighContrast
end HCPolySupport
