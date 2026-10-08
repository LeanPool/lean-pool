/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexFractionalChainMeanJumpAmplitude
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyCellRawMean

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.ConvexFractionalChainBallVolumeScaling

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Volume normalization for fractional convex chains
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The exact-volume coefficient appearing in a chain jump. -/
@[expose]
def convexFractionalChainExactCoefficient
    (c x : Vec d) (rho Rad s : ℝ) (n : ℕ) : ℝ≥0∞ :=
  let E := convexFractionalChainBall c x rho n
  let F := convexFractionalChainBall c x rho (n + 1)
  let D := (3 / 2 : ℝ) * convexFractionalChainScale n * (Rad + rho)
  (volume F)⁻¹ *
    (volume F * ENNReal.ofReal (D ^ ((d : ℝ) + 2 * s))) ^ (1 / 2 : ℝ) *
      (volume E)⁻¹

/-- The corresponding coefficient with both ball volumes replaced by the
explicit dimension-dependent lower bounds. -/
@[expose]
def convexFractionalChainLowerCoefficient
    (d : ℕ) (rho Rad s : ℝ) (n : ℕ) : ℝ≥0∞ :=
  let t := convexFractionalChainScale n
  let vE := convexHardyBallVolumeLower d (t * rho)
  let vF := convexHardyBallVolumeLower d ((1 / 2 : ℝ) * t * rho)
  let K := ENNReal.ofReal
    (((3 / 2 : ℝ) * t * (Rad + rho)) ^ ((d : ℝ) + 2 * s))
  (vF⁻¹) ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) * vE⁻¹

private theorem inv_mul_mul_rpow_half
    {v K : ℝ≥0∞} (hv0 : v ≠ 0) (hvtop : v ≠ ⊤) :
    v⁻¹ * (v * K) ^ (1 / 2 : ℝ) =
      (v⁻¹) ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hcancel : v⁻¹ * v ^ (1 / 2 : ℝ) =
      (v⁻¹) ^ (1 / 2 : ℝ) := by
    calc
      v⁻¹ * v ^ (1 / 2 : ℝ) =
          v ^ (-1 : ℝ) * v ^ (1 / 2 : ℝ) := by
        rw [ENNReal.rpow_neg, ENNReal.rpow_one]
      _ = v ^ ((-1 : ℝ) + 1 / 2) :=
        (ENNReal.rpow_add _ _ hv0 hvtop).symm
      _ = v ^ (-(1 / 2 : ℝ)) := by norm_num
      _ = (v ^ (1 / 2 : ℝ))⁻¹ := ENNReal.rpow_neg _ _
      _ = (v⁻¹) ^ (1 / 2 : ℝ) := (ENNReal.inv_rpow _ _).symm
  rw [← mul_assoc, hcancel]

/-- Exact ball volumes are bounded by their explicit lower-volume
normalization in the fractional chain coefficient. -/
theorem convexFractionalChainExactCoefficient_le_lowerCoefficient
    (hd : 1 ≤ d) (c x : Vec d) {rho Rad s : ℝ} (hrho : 0 < rho) (n : ℕ) :
    convexFractionalChainExactCoefficient c x rho Rad s n ≤
      convexFractionalChainLowerCoefficient d rho Rad s n := by
  let t := convexFractionalChainScale n
  let E := convexFractionalChainBall c x rho n
  let F := convexFractionalChainBall c x rho (n + 1)
  let vE := convexHardyBallVolumeLower d (t * rho)
  let vF := convexHardyBallVolumeLower d ((1 / 2 : ℝ) * t * rho)
  let K := ENNReal.ofReal
    (((3 / 2 : ℝ) * t * (Rad + rho)) ^ ((d : ℝ) + 2 * s))
  have ht : 0 < t := convexFractionalChainScale_pos n
  have hEpos : 0 < volume E := by
    dsimp only [E, convexFractionalChainBall]
    exact IsOpen.measure_pos volume (isOpen_euclideanBallAt _ _)
      ⟨_, center_mem_euclideanBallAt _ (mul_pos ht hrho)⟩
  have hFpos : 0 < volume F := by
    dsimp only [F, convexFractionalChainBall]
    exact IsOpen.measure_pos volume (isOpen_euclideanBallAt _ _)
      ⟨_, center_mem_euclideanBallAt _
        (mul_pos (convexFractionalChainScale_pos (n + 1)) hrho)⟩
  have hFtop : volume F ≠ ⊤ := by
    dsimp only [F, convexFractionalChainBall]
    exact (isOpenBoundedConvexDomain_euclideanBallAt _
      (mul_pos (convexFractionalChainScale_pos (n + 1)) hrho)).volume_lt_top.ne
  have hElower : vE ≤ volume E := by
    dsimp only [vE, E, t, convexFractionalChainBall]
    exact convexHardyBallVolumeLower_le_volume_euclideanBallAt hd _
      (mul_pos ht hrho)
  have hFlower : vF ≤ volume F := by
    dsimp only [vF, F, t, convexFractionalChainBall]
    rw [convexFractionalChainScale_succ]
    exact convexHardyBallVolumeLower_le_volume_euclideanBallAt hd _
      (by positivity)
  have hInvE : (volume E)⁻¹ ≤ vE⁻¹ := ENNReal.inv_le_inv.mpr hElower
  have hInvF : ((volume F)⁻¹) ^ (1 / 2 : ℝ) ≤
      (vF⁻¹) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.mpr hFlower) (by norm_num)
  rw [convexFractionalChainExactCoefficient,
    convexFractionalChainLowerCoefficient]
  change (volume F)⁻¹ * (volume F * K) ^ (1 / 2 : ℝ) * (volume E)⁻¹ ≤
    (vF⁻¹) ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) * vE⁻¹
  rw [inv_mul_mul_rpow_half hFpos.ne' hFtop]
  have hFirst : (volume F)⁻¹ ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) ≤
      vF⁻¹ ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) := by
    simpa only [mul_comm] using mul_le_mul_right hInvF (K ^ (1 / 2 : ℝ))
  exact mul_le_mul hFirst hInvE bot_le bot_le

end

end HighContrast
end HCPolySupport
