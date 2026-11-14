/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.FaceMeasure
public import LeanPool.LiebThirring.Electrostatics.ScreenedRegularityCells
public import LeanPool.LiebThirring.Electrostatics.ScreenedRegularityBounds
public import LeanPool.LiebThirring.Electrostatics.ShellAssemblyGeometry
public import LeanPool.LiebThirring.Electrostatics.ScreenedRegularityIntegrability
import LeanPool.LiebThirring.Analysis.FundamentalSolution
import LeanPool.LiebThirring.Analysis.WeakHarmonic
import LeanPool.LiebThirring.Electrostatics.Slicing

/-!
# Equality of the screened and face-charge potentials

The screened and face-charge potentials have a weakly harmonic difference. Continuity and decay
force that difference to vanish everywhere.
-/

public section

open MeasureTheory Filter Laplacian
open scoped ENNReal NNReal Topology ContDiff

namespace LiebThirring

/-- The screened real potential tends uniformly to zero outside large balls. -/
theorem tendsto_screenedPotentialReal_zero {M : ℕ} (hM : 1 ≤ M)
    (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R) :
    Tendsto (screenedPotentialReal Z R) (Bornology.cobounded Position) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_screenedPotentialReal_le_one_add_norm hM Z R hR
  have ht : Tendsto (fun x : Position => C / (1 + ‖x‖))
      (Bornology.cobounded Position) (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_const_nhds.add_atTop tendsto_norm_cobounded_atTop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall (screenedPotentialReal_nonneg Z R))
    (Eventually.of_forall (fun x => (le_abs_self _).trans (hC x)))

/-- the potential identity from the screened-potential test-function identity for smooth compactly
supported tests.
This is the expansion of the former `ScreenedLaplacianIdentity` premise. -/
theorem screenedPotential_eq_coulombPotential_of_laplacian_identity {M : ℕ}
    (hM : 1 ≤ M) (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (hLap : ∀ f : Position → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, screenedPotentialReal Z R x * Δ f x) =
        -4 * Real.pi * ∫ x, f x ∂voronoiFaceMeasure R hR (Z : ℝ))
    (x : Position) :
    screenedPotential Z R x = coulombPotential (voronoiFaceMeasure R hR (Z : ℝ)) x := by
  let ν := voronoiFaceMeasure R hR (Z : ℝ)
  have : IsFiniteMeasure ν := isFiniteMeasure_voronoiFaceMeasure R hR Z.coe_nonneg
  let C : ℝ≥0∞ := ENNReal.ofReal (voronoiDecayCoefficient R (Z : ℝ))
  have hC : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hν : ∀ y, coulombPotential ν y ≤ C := by
    intro y
    exact (coulombPotential_voronoiFaceMeasure_decay R hR Z.coe_nonneg y).trans
      (ENNReal.ofReal_le_ofReal (div_le_self (voronoiDecayCoefficient_nonneg R Z.coe_nonneg)
        (le_add_of_nonneg_right (norm_nonneg y))))
  let w := fun y => screenedPotentialReal Z R y - (coulombPotential ν y).toReal
  have hw : Continuous w :=
    (continuous_screenedPotentialReal hM Z R hR).sub
      (continuous_toReal_coulombPotential_voronoiFaceMeasure R hR Z.coe_nonneg)
  have hweak : ∀ f : Position → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ y, w y * Δ f y) = 0 := by
    intro f hf hfc
    have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
    have hi := integrable_screenedPotentialReal_mul_laplacian hM Z R hR hf2 hfc
    have hj := integrable_coulombPotential_toReal_mul_laplacian ν hC hν hf2 hfc
    simp only [w, sub_mul]
    rw [integral_sub hi hj, hLap f hf hfc,
      integral_coulombPotential_toReal_mul_laplacian ν hC hν hf2 hfc, sub_self]
  have hd : Tendsto w (cocompact Position) (𝓝 0) := by
    have ht := (tendsto_screenedPotentialReal_zero hM Z R hR).sub
      (tendsto_toReal_coulombPotential_voronoiFaceMeasure_zero R hR Z.coe_nonneg)
    simpa only [sub_zero, Metric.cobounded_eq_cocompact] using ht
  have hz := congrFun (weak_harmonic_eq_zero hw hweak hd) x
  apply (ENNReal.toReal_eq_toReal_iff' (screenedPotential_ne_top hM Z R hR x)
    (ne_of_lt (coulombPotential_voronoiFaceMeasure_lt_top R hR Z.coe_nonneg x))).mp
  exact sub_eq_zero.mp hz

/-- the potential identity: the actual face-charge measure represents the screened potential
everywhere. -/
theorem screenedPotential_eq_coulombPotential_voronoiFaceMeasure {M : ℕ}
    (hM : 1 ≤ M) (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (x : Position) :
    screenedPotential Z R x = coulombPotential (voronoiFaceMeasure R hR (Z : ℝ)) x :=
  screenedPotential_eq_coulombPotential_of_laplacian_identity hM Z R hR
    (fun f hf hfc => integral_screenedPotentialReal_mul_laplacian hM Z R hR f
      (hf.of_le (by simp)) hfc) x

end LiebThirring

end
