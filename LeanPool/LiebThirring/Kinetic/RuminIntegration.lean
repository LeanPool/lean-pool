/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.RuminCoefficient
public import LeanPool.LiebThirring.Kinetic.LayerCakeBounds
public import LeanPool.LiebThirring.Kinetic.LayerCakeIdentity

/-! # Rumin integration of the high Fourier field

The exact scalar integral and the kinetic layer cake turn the pointwise
low-momentum estimate into the kinetic Lieb--Thirring bound.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LiebThirring

/-- Conditional the Rumin bound: the exact pointwise low-momentum bound implies the kinetic
Lieb--Thirring inequality. the low-momentum bound supplies the sole conditional input. -/
theorem rumin_bound_of_lowMomentumBound (q : ℕ) (hq : 1 ≤ q) {N : ℕ}
    (i : Fin N) (ψ : State N q) (hanti : antisymmetric ψ)
    (hLow : ∀ E : ℝ, 0 ≤ E → ∀ x : Position,
      ‖lowFourierField (densityField i ψ) E x‖ ^ 2 ≤
        (q : ℝ) * (1 / (6 * Real.pi ^ 2)) * E ^ ((3 : ℝ) / 2)) :
    (ruminConstant : ℝ≥0∞) * (q : ℝ≥0∞) ^ (-(2 : ℝ) / 3) *
        (∫⁻ x : Position, density ψ x ^ ((5 : ℝ) / 3)) ≤ kineticEnergy ψ := by
  let κ : ℝ≥0∞ :=
    (ruminConstant : ℝ≥0∞) * (q : ℝ≥0∞) ^ (-(2 : ℝ) / 3)
  let d : ℝ := (q : ℝ) * (1 / (6 * Real.pi ^ 2))
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hswap :
      (∫⁻ E in Ioi (0 : ℝ), ∫⁻ x : Position,
          ‖highFourierField (densityField i ψ) E x‖ₑ ^ 2) =
        ∫⁻ x : Position, ∫⁻ E in Ioi (0 : ℝ),
          ‖highFourierField (densityField i ψ) E x‖ₑ ^ 2 := by
    apply MeasureTheory.lintegral_lintegral_swap
    exact ((stronglyMeasurable_highFourierField_canonical
      (densityField i ψ)).enorm.pow_const 2).aemeasurable
  rw [kineticEnergy_eq_densityField_layerCake_Ioi i ψ hanti, hswap]
  have hρmeas : Measurable (fun x : Position =>
      density ψ x ^ ((5 : ℝ) / 3)) :=
    ENNReal.continuous_rpow_const.measurable.comp (measurable_density ψ)
  change κ * (∫⁻ x : Position, density ψ x ^ ((5 : ℝ) / 3)) ≤ _
  rw [← lintegral_const_mul κ hρmeas]
  apply lintegral_mono_ae
  filter_upwards [densityField_density_data_ae i ψ hanti,
    densityField_high_bound_ae_of_lowMomentumBound i ψ hanti hLow] with x hρ hhigh
  let t : ℝ := (density ψ x).toReal
  have ht : 0 ≤ t := ENNReal.toReal_nonneg
  have hscalar : κ * density ψ x ^ ((5 : ℝ) / 3) =
      ENNReal.ofReal ((9 / 35 : ℝ) * d ^ (-(2 : ℝ) / 3) *
        t ^ ((5 : ℝ) / 3)) := by
    have hκ : κ = ENNReal.ofReal ((9 / 35 : ℝ) * d ^ (-(2 : ℝ) / 3)) := by
      dsimp [κ, d]
      exact (ofReal_ruminCoefficient_eq q hq).symm
    rw [hκ, ← ENNReal.ofReal_toReal hρ.1]
    rw [ENNReal.ofReal_rpow_of_nonneg ht (by norm_num : 0 ≤ (5 : ℝ) / 3)]
    rw [← ENNReal.ofReal_mul]
    positivity
  rw [hscalar, ← Assembly.lintegral_rumin t d ht hd]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
  have hb := hhigh E hE.le
  have hsq :
      (max (Real.sqrt t - Real.sqrt d * E ^ ((3 : ℝ) / 4)) 0) ^ 2 ≤
        ‖highFourierField (densityField i ψ) E x‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hb
  calc
    ENNReal.ofReal
        ((max (Real.sqrt t - Real.sqrt d * E ^ ((3 : ℝ) / 4)) 0) ^ 2) ≤
        ENNReal.ofReal (‖highFourierField (densityField i ψ) E x‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal hsq
    _ = ‖highFourierField (densityField i ψ) E x‖ₑ ^ 2 := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end LiebThirring

end
