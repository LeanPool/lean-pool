/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.LayerCakeMass
public import LeanPool.LiebThirring.Kinetic.FourierFactorDensity

/-!
# Exact kinetic layer cake

The Fourier density-field energy equals the kinetic energy and its extended high-field layer
cake. The two half-line conventions differ only at the null zero cutoff.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring

/-- the layer cake extended layer-cake identity on the nonnegative real half-line. -/
theorem kineticEnergy_eq_densityField_layerCake {N q : ℕ} (i : Fin N)
    (ψ : State N q) (hψ : antisymmetric ψ) :
    kineticEnergy ψ = ∫⁻ E in Ici (0 : ℝ), ∫⁻ x : Position,
      ‖highFourierField (densityField i ψ) E x‖ₑ ^ 2 := by
  exact (kineticEnergy_eq_densityField_fourier i ψ hψ).trans
    (lintegral_highFourierField_layerCake (densityField i ψ)).symm

/-- The positive half-line convention consumed by the scalar Rumin integral. -/
theorem kineticEnergy_eq_densityField_layerCake_Ioi {N q : ℕ} (i : Fin N)
    (ψ : State N q) (hψ : antisymmetric ψ) :
    kineticEnergy ψ = ∫⁻ E in Ioi (0 : ℝ), ∫⁻ x : Position,
      ‖highFourierField (densityField i ψ) E x‖ₑ ^ 2 := by
  rw [restrict_Ioi_eq_restrict_Ici]
  exact kineticEnergy_eq_densityField_layerCake i ψ hψ

end LiebThirring
end
