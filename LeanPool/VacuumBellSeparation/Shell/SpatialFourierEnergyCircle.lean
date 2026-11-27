/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.SpatialFourierEnergyGeometry

/-!
# The actual nonzero-energy circle for momentum Fourier evaluation

Changing only the first spatial coordinate by 8E zeta gives exactly the
manuscript lower bound 47E² for the energy square. The resulting shell
points have Euclidean norm less than 14E. No principal-root continuity
is needed for these algebraic estimates.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Spatial energy circle given by `z + PiLp.single 2 0 ((8 * E : ℂ) * ζ)`. -/
noncomputable def spatialEnergyCircle (z : EuclideanSpace ℂ (Fin 3))
    (E : ℝ) (ζ : ℂ) : EuclideanSpace ℂ (Fin 3) :=
  z + PiLp.single 2 0 ((8 * E : ℂ) * ζ)

theorem spatialEnergyCircle_norm_le (z : EuclideanSpace ℂ (Fin 3))
    {E : ℝ} (hE : 0 ≤ E) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖spatialEnergyCircle z E ζ‖ ≤ ‖z‖ + 8 * E := by
  calc
    _ ≤ ‖z‖ + ‖PiLp.single 2 (0 : Fin 3) ((8 * E : ℂ) * ζ)‖ := norm_add_le _ _
    _ = _ := by simp only [PiLp.norm_single, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hE, hζ, mul_one]

theorem spatialEnergyCircle_energy_expand (m : ℝ) (z : EuclideanSpace ℂ (Fin 3))
    (E : ℝ) (ζ : ℂ) :
    spatialFourierEnergySquared m (spatialEnergyCircle z E ζ) =
      ((8 * E : ℂ) * ζ) ^ 2 + 2 * z 0 * ((8 * E : ℂ) * ζ) +
        spatialFourierEnergySquared m z := by
  simp only [spatialFourierEnergySquared, spatialEnergyCircle, spatialDot,
    Fin.sum_univ_three, PiLp.add_apply, PiLp.single_apply]
  norm_num
  ring

theorem spatialEnergyCircle_energy_lower {m E : ℝ} (hm : 0 ≤ m) (hE : 0 < E)
    (z : EuclideanSpace ℂ (Fin 3)) (hz : m + ‖z‖ ≤ E)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    47 * E ^ 2 ≤ ‖spatialFourierEnergySquared m (spatialEnergyCircle z E ζ)‖ := by
  have hzE : ‖z‖ ≤ E := by linarith [norm_nonneg z]
  have hz₀ : ‖z 0‖ ≤ E := (PiLp.norm_apply_le z 0).trans hzE
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ m + ‖z‖) hz 2
  have hq : ‖spatialFourierEnergySquared m z‖ ≤ E ^ 2 :=
    (spatialFourierEnergySquared_norm_le m z).trans (by
      nlinarith [mul_nonneg hm (norm_nonneg z)])
  have hlarge : ‖((8 * E : ℂ) * ζ) ^ 2‖ = 64 * E ^ 2 := by
    simp only [norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hE, hζ, mul_one]
    ring
  have hcross : ‖2 * z 0 * ((8 * E : ℂ) * ζ)‖ ≤ 16 * E ^ 2 := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hE, hζ, mul_one]
    nlinarith [mul_le_mul_of_nonneg_right hz₀ hE.le]
  have heq : ((8 * E : ℂ) * ζ) ^ 2 =
      spatialFourierEnergySquared m (spatialEnergyCircle z E ζ) -
        (2 * z 0 * ((8 * E : ℂ) * ζ) + spatialFourierEnergySquared m z) := by
    rw [spatialEnergyCircle_energy_expand]
    ring
  have htri : ‖((8 * E : ℂ) * ζ) ^ 2‖ ≤
      ‖spatialFourierEnergySquared m (spatialEnergyCircle z E ζ)‖ +
        (‖2 * z 0 * ((8 * E : ℂ) * ζ)‖ + ‖spatialFourierEnergySquared m z‖) := by
    calc
      _ = ‖spatialFourierEnergySquared m (spatialEnergyCircle z E ζ) -
          (2 * z 0 * ((8 * E : ℂ) * ζ) + spatialFourierEnergySquared m z)‖ := congrArg norm heq
      _ ≤ _ := (norm_sub_le _ _).trans (_root_.add_le_add_right (norm_add_le _ _) _)
  rw [hlarge] at htri
  linarith

theorem spatialEnergyCircle_shell_size {m E : ℝ} (hm : 0 ≤ m) (hE : 0 < E)
    (z : EuclideanSpace ℂ (Fin 3)) (hz : m + ‖z‖ ≤ E)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {e : ℂ}
    (he : e ^ 2 = spatialFourierEnergySquared m (spatialEnergyCircle z E ζ)) :
    euclidSq (e, WithLp.ofLp (spatialEnergyCircle z E ζ)) < (14 * E) ^ 2 := by
  have hmE : m ≤ E := by linarith [norm_nonneg z]
  have hzE : ‖z‖ ≤ E := by linarith
  have hwE : ‖spatialEnergyCircle z E ζ‖ ≤ 9 * E := by
    have hw := spatialEnergyCircle_norm_le z hE.le hζ
    linarith
  have hmsq := pow_le_pow_left₀ hm hmE 2
  have hwsq := pow_le_pow_left₀ (norm_nonneg _) hwE 2
  have hb := actualSpatialEnergy_euclidSq_le m (spatialEnergyCircle z E ζ) he
  nlinarith [sq_pos_of_pos hE]

theorem spatialEnergyCircle_energy_norm_lower {m E : ℝ} (hm : 0 ≤ m) (hE : 0 < E)
    (z : EuclideanSpace ℂ (Fin 3)) (hz : m + ‖z‖ ≤ E)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {e : ℂ}
    (he : e ^ 2 = spatialFourierEnergySquared m (spatialEnergyCircle z E ζ)) :
    E ≤ ‖e‖ ∧ e ≠ 0 := by
  have hn := congrArg norm he
  rw [norm_pow] at hn
  have hl := spatialEnergyCircle_energy_lower hm hE z hz hζ
  have hle : E ≤ ‖e‖ := by nlinarith [norm_nonneg e]
  exact ⟨hle, norm_pos_iff.mp (hE.trans_le hle)⟩

end VacuumBellSeparation
