/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.KineticEnergy
import LeanPool.LiebThirring.Fourier.Schwartz

/-!
# Kinetic energy of Schwartz states

The Fourier kinetic form agrees with the integral of squared coordinate derivatives on Schwartz
states.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

open scoped SchwartzMap FourierTransform

namespace LiebThirring

theorem kineticEnergy_schwartz (N q : ℕ) (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    kineticEnergy (f.toLp 2 (volume : Measure (Configuration N))) =
      ∑ i : Fin N, ∑ a : Fin 3, ∫⁻ x : Configuration N,
        (‖fderiv ℝ (fun y => f y) x (PiLp.single 2 (i, a) (1 : ℝ))‖₊ : ℝ≥0∞) ^ 2 := by
  classical
  have hnorm (x : Configuration N) :
      (‖x‖₊ : ℝ≥0∞) ^ 2 =
        ∑ i : Fin N, ∑ a : Fin 3, ENNReal.ofReal (x (i, a) ^ 2) := by
    change ‖x‖ₑ ^ 2 = _
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
      ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
    exact Fintype.sum_prod_type _
  have hderiv (i : Fin N) (a : Fin 3) :
      (∫⁻ x : Configuration N,
        (‖fderiv ℝ (fun y => f y) x (PiLp.single 2 (i, a) (1 : ℝ))‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x : Configuration N, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        ENNReal.ofReal (x (i, a) ^ 2) * (‖(𝓕 f) x‖₊ : ℝ≥0∞) ^ 2 := by
    simpa only [EuclideanSpace.inner_single_right, map_one, one_mul,
      RCLike.conj_to_real] using
      Fourier.lintegral_fderiv_eq_fourier f (PiLp.single 2 (i, a) (1 : ℝ))
  unfold kineticEnergy
  change (∫⁻ x : Configuration N, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
    (‖x‖₊ : ℝ≥0∞) ^ 2 *
      (‖(𝓕 (f.toLp 2 (volume : Measure (Configuration N))) : State N q) x‖₊ : ℝ≥0∞) ^ 2) = _
  rw [SchwartzMap.toLp_fourier_eq]
  calc
    _ = ∫⁻ x : Configuration N, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        (‖x‖₊ : ℝ≥0∞) ^ 2 * (‖(𝓕 f) x‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [(𝓕 f).coeFn_toLp 2 (volume : Measure (Configuration N))] with x hx
      rw [hx]
    _ = ∫⁻ x : Configuration N, ∑ i : Fin N, ∑ a : Fin 3,
        ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal (x (i, a) ^ 2) *
          (‖(𝓕 f) x‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr
      intro x
      rw [hnorm]
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i : Fin N, ∑ a : Fin 3, ∫⁻ x : Configuration N,
        ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal (x (i, a) ^ 2) *
          (‖(𝓕 f) x‖₊ : ℝ≥0∞) ^ 2 := by
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [lintegral_finsetSum]
        intro a _
        fun_prop
      · intro i _
        fun_prop
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      exact (hderiv i a).symm

end LiebThirring

end
