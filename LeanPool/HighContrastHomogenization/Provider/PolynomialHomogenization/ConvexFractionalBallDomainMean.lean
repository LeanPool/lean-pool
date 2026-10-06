/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexFractionalChainPotential
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyCellRawMean
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalPotentialSchurAssembly

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexFractionalBallDomainMean

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Core-ball and domain mean comparison
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The core-ball mean differs from the domain mean by a structural multiple
of the fractional energy. -/
theorem ofReal_vecNormSq_coreMean_sub_domainMean_le
    (hd : 1 ≤ d) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {c : Vec d} {rho Rad s : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad)
    (hinner : euclideanBallAt c rho ⊆ U)
    (houter : U ⊆ euclideanBallAt c Rad)
    {G : Vec d → Vec d} (hGint : Integrable G (volume.restrict U))
    (hs : 0 ≤ s) :
    ENNReal.ofReal (vecNormSq
        (volumeAverageVec (euclideanBallAt c rho) G - volumeAverageVec U G)) ≤
      (2 * (convexHardyBallVolumeLower d rho)⁻¹ *
          ENNReal.ofReal ((2 * Rad) ^ ((d : ℝ) + 2 * s))) *
        fracSeminormSq U s G := by
  let B := euclideanBallAt c rho
  have hBmeas : MeasurableSet B := (isOpen_euclideanBallAt c rho).measurableSet
  have hBpos : 0 < volume B := by
    exact IsOpen.measure_pos volume (isOpen_euclideanBallAt c rho)
      ⟨c, center_mem_euclideanBallAt c hrho⟩
  have hBtop : volume B ≠ ∞ :=
    (isOpenBoundedConvexDomain_euclideanBallAt c hrho).volume_lt_top.ne
  have hUpos : 0 < volume U := hBpos.trans_le (measure_mono hinner)
  have hUtop : volume U ≠ ∞ := hU.volume_lt_top.ne
  have hGB : Integrable G (volume.restrict B) :=
    hGint.mono_measure (Measure.restrict_mono_set volume hinner)
  have hcross : ∀ x ∈ B, ∀ y ∈ U,
      Real.sqrt (vecNormSq (x - y)) ≤ 2 * Rad := by
    intro x hx y hy
    have hxc : Real.sqrt (vecNormSq (x - c)) < Rad := by
      apply lt_of_sq_lt_sq' hRad.le
      rw [Real.sq_sqrt (vecNormSq_nonneg (x - c))]
      exact houter (hinner hx)
    have hyc : Real.sqrt (vecNormSq (y - c)) < Rad := by
      apply lt_of_sq_lt_sq' hRad.le
      rw [Real.sq_sqrt (vecNormSq_nonneg (y - c))]
      exact houter hy
    have hdecomp : x - y = (x - c) + -(y - c) := by abel
    calc
      Real.sqrt (vecNormSq (x - y)) =
          Real.sqrt (vecNormSq ((x - c) + -(y - c))) := by rw [hdecomp]
      _ ≤ Real.sqrt (vecNormSq (x - c)) +
          Real.sqrt (vecNormSq (-(y - c))) := sqrt_vecNormSq_add_le _ _
      _ = Real.sqrt (vecNormSq (x - c)) +
          Real.sqrt (vecNormSq (y - c)) := by rw [vecNormSq_neg]
      _ ≤ 2 * Rad := (add_lt_add hxc hyc).le.trans_eq (two_mul Rad).symm
  have hbase := ofReal_vecNormSq_sub_volumeAverageVec_le_unionFracSeminormSq
    hd hBmeas hU.1.measurableSet hBpos hBtop hUpos hUtop hGB hGint
      hs (mul_pos (by norm_num) hRad) hcross
  rw [Set.union_eq_right.mpr hinner] at hbase
  have hlowerB : convexHardyBallVolumeLower d rho ≤ volume B :=
    convexHardyBallVolumeLower_le_volume_euclideanBallAt hd c hrho
  have hlowerU : convexHardyBallVolumeLower d rho ≤ volume U :=
    hlowerB.trans (measure_mono hinner)
  have hcoef : (volume B)⁻¹ + (volume U)⁻¹ ≤
      2 * (convexHardyBallVolumeLower d rho)⁻¹ := by
    calc
      _ ≤ (convexHardyBallVolumeLower d rho)⁻¹ +
          (convexHardyBallVolumeLower d rho)⁻¹ :=
        add_le_add (ENNReal.inv_le_inv.mpr hlowerB)
          (ENNReal.inv_le_inv.mpr hlowerU)
      _ = _ := by ring
  apply hbase.trans
  have hmul := mul_le_mul_right
    (mul_le_mul_right hcoef
      (ENNReal.ofReal ((2 * Rad) ^ ((d : ℝ) + 2 * s))))
    (fracSeminormSq U s G)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul

end

end HighContrast
end HCPolySupport
