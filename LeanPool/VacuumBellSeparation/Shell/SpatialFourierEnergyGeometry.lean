/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.NullDiscs
public import LeanPool.VacuumBellSeparation.Gaussian.SpatialComplexRadius

/-!
# The two actual shell energies used for entire spatial Fourier evaluation

All spatial norms are the genuine Euclidean norm on complex three-space.
The squared energy is the complex bilinear quadratic polynomial.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Spatial Fourier energy squared. -/
noncomputable def spatialFourierEnergySquared (m : ℝ) (z : EuclideanSpace ℂ (Fin 3)) : ℂ :=
  (m : ℂ) ^ 2 + spatialDot (WithLp.ofLp z) (WithLp.ofLp z)

/-- Spatial Fourier energy obtained from `Complex.sqrt`. -/
noncomputable def spatialFourierEnergy (m : ℝ) (z : EuclideanSpace ℂ (Fin 3)) : ℂ :=
  Complex.sqrt (spatialFourierEnergySquared m z)

theorem spatialFourierEnergy_sq (m : ℝ) (z : EuclideanSpace ℂ (Fin 3)) :
    spatialFourierEnergy m z ^ 2 = spatialFourierEnergySquared m z := by
  exact Complex.cpow_ofNat_inv_pow _ 2

theorem spatialFourierEnergySquared_norm_le (m : ℝ) (z : EuclideanSpace ℂ (Fin 3)) :
    ‖spatialFourierEnergySquared m z‖ ≤ m ^ 2 + ‖z‖ ^ 2 := by
  calc
    _ ≤ ‖(m : ℂ) ^ 2‖ + ‖spatialDot (WithLp.ofLp z) (WithLp.ofLp z)‖ := norm_add_le _ _
    _ ≤ m ^ 2 + ‖z‖ ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact _root_.add_le_add_right
        (by simpa only [spatialDot, ← pow_two] using Gaussian.spatial_bilinear_square_norm_le z) _

theorem actualSpatialEnergy_shell (m : ℝ) (z : EuclideanSpace ℂ (Fin 3))
    {e : ℂ} (he : e ^ 2 = spatialFourierEnergySquared m z) :
    (e, WithLp.ofLp z) ∈ complexShell m := by
  change e ^ 2 - spatialDot (WithLp.ofLp z) (WithLp.ofLp z) = (m : ℂ) ^ 2
  rw [he]
  simp only [spatialFourierEnergySquared, add_sub_cancel_right]

theorem actualSpatialEnergy_euclidSq_le (m : ℝ) (z : EuclideanSpace ℂ (Fin 3))
    {e : ℂ} (he : e ^ 2 = spatialFourierEnergySquared m z) :
    euclidSq (e, WithLp.ofLp z) ≤ m ^ 2 + 2 * ‖z‖ ^ 2 := by
  have hn := congrArg norm he
  rw [norm_pow] at hn
  have hq := spatialFourierEnergySquared_norm_le m z
  simp only [euclidSq, ← PiLp.norm_sq_eq_of_L2]
  linarith

theorem actualSpatialEnergy_in_ball {m E : ℝ} (hm : 0 ≤ m)
    (z : EuclideanSpace ℂ (Fin 3)) (hE : m + ‖z‖ ≤ E)
    {e : ℂ} (he : e ^ 2 = spatialFourierEnergySquared m z) :
    euclidSq (e, WithLp.ofLp z) ≤ (2 * E) ^ 2 := by
  have hb := actualSpatialEnergy_euclidSq_le m z he
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ m + ‖z‖) hE 2
  nlinarith [norm_nonneg z, mul_nonneg hm (norm_nonneg z), sq_nonneg m]

theorem spatialFourierEnergy_pair_in_shell (m : ℝ) (z : EuclideanSpace ℂ (Fin 3)) :
    (spatialFourierEnergy m z, WithLp.ofLp z) ∈ complexShell m ∧
      (-spatialFourierEnergy m z, WithLp.ofLp z) ∈ complexShell m := by
  exact ⟨actualSpatialEnergy_shell m z (spatialFourierEnergy_sq m z),
    actualSpatialEnergy_shell m z (by rw [neg_sq, spatialFourierEnergy_sq])⟩

end VacuumBellSeparation
