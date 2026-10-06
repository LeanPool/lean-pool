/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.InnerEllipsoidNormalization

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.GaugeMaxPowerFluxFrameAbsorption

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The law-free flux frame at a truncated gauge power

The response chain's filling coefficient is a truncation at one of a multiple of
the absolute gauge scale, because the cross-grid matrix of the affine grid
against the exact normalized root is `lambda * alpha` times the identity.  A
truncation at one is not bounded by any positive power of the gauge scale — it
tends to one as the scale tends to zero, while the power tends to zero — so the
absorption has to be recorded at the truncated power rather than at the bare
one.

The inner-ellipsoid normalization premise gives exactly that: the gauge scale is below
the ratio of the outer sandwich radius to the normalization radius, and a
truncation at one is monotone, so the truncated power is absorbed exactly as the
bare power was.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Set

noncomputable section

variable {d : ℕ}

/-- **The absorption at a truncated gauge power.**  The truncation at one is
monotone, so the inner-ellipsoid normalization premise absorbs it unchanged. -/
theorem cellAnchoredObservationRateBound_of_gaugeMaxPowerRate
    [NeZero d] {Uphys U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {b c epsilon Xval kappaRate q K : ℝ}
    (responseBound : system.CellIndex → ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hq : 0 ≤ q)
    (hEX : 0 ≤ epsilon * Xval)
    (hInner : ellipsoid abar c ⊆ Uphys)
    (hSandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ Uphys) rho Rad)
    (hrate : ∀ i, 0 ≤ responseBound i ∧
      printCellScaleFactor (ruledObservationCube system i) b *
          responseBound i ≤
        K * max 1 (Real.sqrt (specBound ((symmPart abar)⁻¹)) ^ q) *
          (epsilon * Xval) ^ kappaRate) :
    CellAnchoredObservationRateBound system b responseBound epsilon Xval
      kappaRate (K * max 1 ((Rad / c) ^ q)) := by
  have halpha0 : (0 : ℝ) ≤ Real.sqrt (specBound ((symmPart abar)⁻¹)) :=
    Real.sqrt_nonneg _
  have habsorb : Real.sqrt (specBound ((symmPart abar)⁻¹)) ≤ Rad / c :=
    (le_div_iff₀ hc).2
      (normalizedRootScale_mul_le_of_innerEllipsoid hS hc.le hInner hSandwich)
  have hpow : max 1 (Real.sqrt (specBound ((symmPart abar)⁻¹)) ^ q) ≤
      max 1 ((Rad / c) ^ q) :=
    max_le_max (le_refl (1 : ℝ)) (Real.rpow_le_rpow halpha0 habsorb hq)
  have hmax0 : (0 : ℝ) ≤ max 1 ((Rad / c) ^ q) :=
    le_trans zero_le_one (le_max_left _ _)
  refine ⟨mul_nonneg hK hmax0, fun i => ?_⟩
  obtain ⟨hnn, hle⟩ := hrate i
  refine ⟨hnn, hle.trans ?_⟩
  have hEXpow : (0 : ℝ) ≤ (epsilon * Xval) ^ kappaRate := Real.rpow_nonneg hEX _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK) hEXpow

/-- **The law-free physical flux frame at a truncated gauge power.**  No
comparison matrix, sample, law, microscopic parameter or cell index survives in
the frame constant. -/
theorem physicalFluxEpsilonFrameBound_of_gaugeMaxPowerRate
    [NeZero d] {Uphys U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {b r Cflux c epsilon Xval kappaRate q K : ℝ}
    (responseBound : system.CellIndex → ℝ)
    (hUopen : IsOpen U) (hRad : 0 ≤ Rad)
    (hb : 0 < b) (hbr : b < r) (hCflux : 0 ≤ Cflux)
    (hc : 0 < c) (hK : 0 ≤ K) (hq : 0 ≤ q)
    (hEX : 0 ≤ epsilon * Xval)
    (hInner : ellipsoid abar c ⊆ Uphys)
    (hSandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ Uphys) rho Rad)
    (hrate : ∀ i, 0 ≤ responseBound i ∧
      printCellScaleFactor (ruledObservationCube system i) b *
          responseBound i ≤
        K * max 1 (Real.sqrt (specBound ((symmPart abar)⁻¹)) ^ q) *
          (epsilon * Xval) ^ kappaRate) :
    PhysicalFluxEpsilonFrameBound system b r Cflux responseBound
      epsilon Xval kappaRate
        (Real.rpow (3 : ℝ) (-b) * Real.rpow (2 * Rad) (r - b) *
          Cflux * r⁻¹ *
          Book.Ch03.constantCoeffMatrixNormHalf
            (identityConstantCoeffMatrix d) *
          responseOneFromTwoGapFactor b r * (K * max 1 ((Rad / c) ^ q))) :=
  physicalFluxEpsilonFrameBound_of_cellAnchoredObservationRate
    system hUopen hRad hb hbr hCflux responseBound
    (cellAnchoredObservationRateBound_of_gaugeMaxPowerRate
      (Uphys := Uphys) system hS responseBound hc hK hq hEX hInner
      hSandwich hrate)

end

end RowSupply
end HighContrast
end HCPolySupport
