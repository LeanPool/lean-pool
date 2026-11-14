/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.FaceMeasureBasic
public import LeanPool.LiebThirring.Electrostatics.PlaneLocal

/-!
# Density bounds and local Coulomb integrals of the face measure

Uniform bound of the density on one plane.

Domination by bounded-density surface measure, with its literal coefficient.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace LiebThirring

variable {M : ℕ}

/-- Uniform bound of the density on one plane. -/
noncomputable def nuclearFaceDensityBound (R : Fin M → Position) (Z : ℝ) (k l : Fin M) : ℝ :=
  Z / (2 * Real.pi * nuclearHalfDistance R k l ^ 2)

theorem nuclearFaceDensityBound_nonneg (R : Fin M → Position) {Z : ℝ} (hZ : 0 ≤ Z)
    (k l : Fin M) : 0 ≤ nuclearFaceDensityBound R Z k l := by
  unfold nuclearFaceDensityBound
  positivity

theorem nuclearFaceDensity_le_bound (R : Fin M → Position) (hR : Function.Injective R)
    {Z : ℝ} (hZ : 0 ≤ Z) {k l : Fin M} (hkl : k ≠ l) {y : Position}
    (hy : y ∈ bisectorPlane R k l) :
    nuclearFaceDensity R Z k l y ≤ nuclearFaceDensityBound R Z k l := by
  have ha := nuclearHalfDistance_pos R hR hkl
  have hr := nuclearHalfDistance_le_norm_on_bisector R hR hkl hy
  have hc : nuclearFaceDensity R Z k l y ≤
      Z * nuclearHalfDistance R k l / (2 * Real.pi * nuclearHalfDistance R k l ^ 3) := by
    apply div_le_div_of_nonneg_left (mul_nonneg hZ ha.le)
      (by positivity : 0 < 2 * Real.pi * nuclearHalfDistance R k l ^ 3)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hr 3) (by positivity)
  have he : Z * nuclearHalfDistance R k l / (2 * Real.pi * nuclearHalfDistance R k l ^ 3) =
      nuclearFaceDensityBound R Z k l := by
    unfold nuclearFaceDensityBound
    field_simp
  exact hc.trans_eq he

theorem voronoiFaceDensity_le_bound (R : Fin M → Position) (hR : Function.Injective R)
    {Z : ℝ} (hZ : 0 ≤ Z) (k l : Fin M) (hkl : k ≠ l) (y : Position) :
    voronoiFaceDensity R Z k l y ≤ ENNReal.ofReal (nuclearFaceDensityBound R Z k l) := by
  by_cases hy : y ∈ voronoiFace R k l
  · rw [voronoiFaceDensity, indicator_of_mem hy]
    exact ENNReal.ofReal_le_ofReal (nuclearFaceDensity_le_bound R hR hZ hkl hy.2.1)
  · simp only [voronoiFaceDensity, indicator_of_notMem hy, zero_le]

/-- Domination by bounded-density surface measure, with its literal coefficient. -/
theorem nuclearFaceMeasure_le_smul_surface (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z)
    (k l : Fin M) (hkl : k ≠ l) :
    nuclearFaceMeasure R hR Z k l hkl ≤
      ENNReal.ofReal (nuclearFaceDensityBound R Z k l) • bisectorSurfaceMeasure R hR k l hkl := by
  rw [nuclearFaceMeasure, ← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall
    (voronoiFaceDensity_le_bound R hR hZ k l hkl))

/-- The local estimate includes off-plane centres and the infinite kernel value. -/
theorem lintegral_coulombKernel_ball_nuclearFaceMeasure_le
    (R : Fin M → Position) (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z)
    (k l : Fin M) (hkl : k ≠ l) (x : Position) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ y in Metric.ball x ε, coulombKernel x y ∂nuclearFaceMeasure R hR Z k l hkl) ≤
      ENNReal.ofReal (2 * Real.pi * ε * nuclearFaceDensityBound R Z k l) := by
  have hle := lintegral_mono' (Measure.restrict_mono_measure
    (nuclearFaceMeasure_le_smul_surface R hR hZ k l hkl) (Metric.ball x ε))
      (le_refl (fun y => coulombKernel x y))
  rw [Measure.restrict_smul, lintegral_smul_measure] at hle
  have hb := lintegral_coulombKernel_ball_planeMeasure_le
    (bisectorNormal R k l) (midpoint ℝ (R k) (R l)) x
    (norm_bisectorNormal R hR hkl) (bisectorSurfaceFrame R hR k l hkl) hε
  have hprod := mul_le_mul (le_refl (ENNReal.ofReal (nuclearFaceDensityBound R Z k l))) hb (by
    positivity) (by positivity)
  have he : ENNReal.ofReal (nuclearFaceDensityBound R Z k l) * ENNReal.ofReal (2 * Real.pi * ε) =
      ENNReal.ofReal (2 * Real.pi * ε * nuclearFaceDensityBound R Z k l) := by
    rw [← ENNReal.ofReal_mul (nuclearFaceDensityBound_nonneg R hZ k l), mul_comm]
  exact hle.trans (hprod.trans_eq he)

/-- The coefficient in the uniform local singular-integral bound (6.4). -/
noncomputable def voronoiLocalCoefficient (R : Fin M → Position) (Z : ℝ) : ℝ :=
  2 * Real.pi * ∑ p : NuclearPair M, nuclearFaceDensityBound R Z p.val.1 p.val.2

theorem voronoiLocalCoefficient_nonneg (R : Fin M → Position) {Z : ℝ} (hZ : 0 ≤ Z) :
    0 ≤ voronoiLocalCoefficient R Z := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun p _ => nuclearFaceDensityBound_nonneg R hZ _ _

/-- Equation (6.4) for the actual unordered-face measure. -/
theorem lintegral_coulombKernel_ball_voronoiFaceMeasure_le
    (R : Fin M → Position) (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z)
    (x : Position) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ y in Metric.ball x ε, coulombKernel x y ∂voronoiFaceMeasure R hR Z) ≤
      ENNReal.ofReal (voronoiLocalCoefficient R Z * ε) := by
  rw [voronoiFaceMeasure, ← Measure.sum_fintype, Measure.restrict_sum _
    Metric.isOpen_ball.measurableSet,
    lintegral_sum_measure, tsum_fintype]
  calc
    _ ≤ ∑ p : NuclearPair M,
        ENNReal.ofReal (2 * Real.pi * ε * nuclearFaceDensityBound R Z p.val.1 p.val.2) :=
      Finset.sum_le_sum fun p _ =>
        lintegral_coulombKernel_ball_nuclearFaceMeasure_le R hR hZ _ _ _ x hε
    _ = ENNReal.ofReal (voronoiLocalCoefficient R Z * ε) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        simp only [voronoiLocalCoefficient, ← Finset.mul_sum]
        ring
      · intro p _
        exact mul_nonneg (by positivity) (nuclearFaceDensityBound_nonneg R hZ _ _)

end LiebThirring

end
