/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianAverageTools
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianShellCaccioppoli

/-!
# Uniform collar coefficient

The spatial covering radius is inverse to the square root of the Gaussian
parameter. This keeps every weight comparison factor independent of the
rescaling point in `eq:bu-gaussian-collar`.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The weighted collar Caccioppoli coefficient grows at most linearly in
its Gaussian parameter once the covering radius is fixed. -/
theorem buGaussian_shell_coefficient_bound
    {a r ρ scale c₁ R₀ : ℝ}
    (ha : 0 < a) (hr : r = 1 / (16 * Real.sqrt a))
    (hR : ρ * r = R₀) (hscale : scale ^ 2 ≤ 1 / 4) :
    (Real.exp (2 * (56 * a * (2 * r) ^ 2 + 12 * ρ * (2 * r) +
      36 * ρ ^ 2 * (2 * r) ^ 2)) *
      (256 * (1 + (c₁ * scale) ^ 2 + 1 / ((2 * r) / 2) ^ 2))) *
      (8 * Besicovitch.multiplicity BUGaussianSpace ^ 2 : ℝ) ≤
    (Real.exp (2 * (56 / 64 + 24 * R₀ + 144 * R₀ ^ 2)) *
      (256 * 256 * (1 + c₁ ^ 2)) *
      (8 * Besicovitch.multiplicity BUGaussianSpace ^ 2 : ℝ)) *
      (1 + a) := by
  have hroot : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hrpos : 0 < r := by rw [hr]; positivity
  have hArSq : a * r ^ 2 = 1 / 256 := by
    rw [hr, div_pow, mul_pow, Real.sq_sqrt ha.le]
    field_simp [hroot.ne', ha.ne']
    ring
  have hInvR2 : 1 / r ^ 2 = 256 * a := by
    apply (div_eq_iff (pow_ne_zero 2 hrpos.ne')).2
    nlinarith only [hArSq]
  have hExpEq :
      2 * (56 * a * (2 * r) ^ 2 + 12 * ρ * (2 * r) +
        36 * ρ ^ 2 * (2 * r) ^ 2) =
      2 * (56 / 64 + 24 * R₀ + 144 * R₀ ^ 2) := by
    calc
      _ = 2 * (224 * (a * r ^ 2) + 24 * (ρ * r) +
          144 * (ρ * r) ^ 2) := by ring
      _ = 2 * (56 / 64 + 24 * R₀ + 144 * R₀ ^ 2) := by
        rw [hArSq, hR]
        ring
  have hscaleC := mul_le_mul_of_nonneg_left hscale (sq_nonneg c₁)
  have hcSq : 0 ≤ c₁ ^ 2 := sq_nonneg c₁
  have ha0 : 0 ≤ a := ha.le
  have hcross : 0 ≤ c₁ ^ 2 * a := mul_nonneg hcSq ha0
  have hcoeff : 1 + (c₁ * scale) ^ 2 + 256 * a ≤
      256 * (1 + c₁ ^ 2) * (1 + a) := by
    nlinarith only [hscaleC, hcSq, ha0, hcross]
  have hcoeff' : 256 * (1 + (c₁ * scale) ^ 2 + 256 * a) ≤
      (256 * 256 * (1 + c₁ ^ 2)) * (1 + a) := by
    nlinarith only [hcoeff]
  rw [show (2 * r) / 2 = r by ring, hInvR2, hExpEq]
  have hcoeff'' := mul_le_mul_of_nonneg_left hcoeff'
    (Real.exp_pos (2 * (56 / 64 + 24 * R₀ + 144 * R₀ ^ 2))).le
  have hM : 0 ≤ (8 * Besicovitch.multiplicity BUGaussianSpace ^ 2 : ℝ) := by
    positivity
  have hproduct := mul_le_mul_of_nonneg_right hcoeff'' hM
  convert hproduct using 1
  ring

/-- The spatial cutoff coefficients are controlled by fixed derivative
bounds once the localization radius exceeds four. -/
theorem buGaussian_shell_amplitude_bound
    {ρ scale c₁ Cg Cs : ℝ}
    (hρ : 4 < ρ) (hscale : 0 ≤ scale)
    (hscaleSq : scale ^ 2 ≤ 1 / 4)
    (hc₁ : 0 ≤ c₁) (hCg : 0 ≤ Cg) (hCs : 0 ≤ Cs) :
    0 ≤ 32 + 3 * (Cs / ρ ^ 2) + 3 * c₁ * scale * (Cg / ρ) ∧
    32 + 3 * (Cs / ρ ^ 2) + 3 * c₁ * scale * (Cg / ρ) ≤
      32 + 3 * Cs + 3 * c₁ * Cg ∧
    0 ≤ 18 * (Cg / ρ) ∧ 18 * (Cg / ρ) ≤ 18 * Cg := by
  have hρpos : 0 < ρ := by linarith only [hρ]
  have hρone : 1 ≤ ρ := by linarith only [hρ]
  have hρsq : 1 ≤ ρ ^ 2 := by nlinarith only [hρone, hρ]
  have hscaleOne : scale ≤ 1 := by
    nlinarith only [hscaleSq, hscale]
  have hCsDiv : Cs / ρ ^ 2 ≤ Cs := div_le_self hCs hρsq
  have hCgDiv : Cg / ρ ≤ Cg := div_le_self hCg hρone
  have hCgDiv0 : 0 ≤ Cg / ρ := div_nonneg hCg hρpos.le
  have hCsDiv0 : 0 ≤ Cs / ρ ^ 2 := div_nonneg hCs (sq_nonneg ρ)
  have hscaleCoeff : c₁ * scale ≤ c₁ := by
    have h := mul_le_mul_of_nonneg_left hscaleOne hc₁
    simpa only [mul_one] using h
  have hprod₀ := mul_le_mul_of_nonneg_right hscaleCoeff hCgDiv0
  have hprod₁ := mul_le_mul_of_nonneg_left hCgDiv hc₁
  have hprod : c₁ * scale * (Cg / ρ) ≤ c₁ * Cg :=
    hprod₀.trans hprod₁
  constructor
  · positivity
  constructor
  · nlinarith only [hCsDiv, hprod]
  constructor
  · positivity
  · nlinarith only [hCgDiv]

/-- Apply the uniform collar coefficient to a nonnegative radial mass. -/
theorem buGaussian_shell_gradient_integral_bound
    {I R F C a M : ℝ}
    (hI : I ≤ F * R) (hF : F ≤ C * (1 + a))
    (hR0 : 0 ≤ R) (hR : R ≤ M) (hC : 0 ≤ C * (1 + a)) :
    I ≤ C * (1 + a) * M := by
  calc
    I ≤ F * R := hI
    _ ≤ C * (1 + a) * R := mul_le_mul_of_nonneg_right hF hR0
    _ ≤ C * (1 + a) * M := mul_le_mul_of_nonneg_left hR hC

/-- The fixed cubic polynomial dominates the volume factors in the Gaussian
collar and late-time estimates. -/
theorem buGaussian_polynomial_domination
    {a ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 ≤ ρ) :
    1 ≤ (1 + a) * (1 + ρ) ^ 3 ∧
      ρ ^ 3 ≤ (1 + a) * (1 + ρ) ^ 3 ∧
      (1 + a) * ρ ^ 3 ≤ (1 + a) * (1 + ρ) ^ 3 := by
  have hpow : ρ ^ 3 ≤ (1 + ρ) ^ 3 := by
    gcongr
    linarith only [hρ]
  have hpowone : 1 ≤ (1 + ρ) ^ 3 := by
    calc
      1 = (1 : ℝ) ^ 3 := by norm_num
      _ ≤ (1 + ρ) ^ 3 := by
        gcongr
        linarith only [hρ]
  have haone : 1 ≤ 1 + a := by linarith only [ha]
  have hPone : 1 ≤ (1 + a) * (1 + ρ) ^ 3 := by
    have hmul := mul_le_mul haone hpowone
      (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith only [ha] : 0 ≤ 1 + a)
    simpa only [one_mul] using hmul
  have hPρ : ρ ^ 3 ≤ (1 + a) * (1 + ρ) ^ 3 := by
    calc
      ρ ^ 3 ≤ (1 + ρ) ^ 3 := hpow
      _ = 1 * (1 + ρ) ^ 3 := by ring
      _ ≤ (1 + a) * (1 + ρ) ^ 3 :=
        mul_le_mul_of_nonneg_right haone (by positivity)
  have hPρ' : (1 + a) * ρ ^ 3 ≤ (1 + a) * (1 + ρ) ^ 3 :=
    mul_le_mul_of_nonneg_left hpow (by linarith only [ha])
  exact ⟨hPone, hPρ, hPρ'⟩

end ESS
