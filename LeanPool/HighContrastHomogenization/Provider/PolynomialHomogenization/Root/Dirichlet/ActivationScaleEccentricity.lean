/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FormulaicShiftedNormalizedReferencePowerTail
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.EccentricityFoldFactor

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.ActivationScaleEccentricity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The activation length in terms of the eccentricity

The certificate's activation length is a triadic power whose generation is the
formulaic tail shift, the ceiling of a logarithm of the deterministic absorption
prefactor.  That prefactor carries the homogenized matrix only through the
triadic bracket of its witness eccentricity, and it carries it as a fixed power.

The two estimates below make that quantitative: the activation length is at most
three times the ceiling-free root of the prefactor, and the prefactor is at most
a law-free constant times a fixed power of the eccentricity bracket.  Together
they exhibit the activation length as a law-free constant times a fixed power of
the eccentricity, which is the form the scale fold consumes.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-- A triadic power of a truncated exponent is the corresponding truncated
power. -/
private theorem rpow_three_max_zero (z : ℝ) :
    (3 : ℝ) ^ max 0 z = max 1 ((3 : ℝ) ^ z) := by
  rcases le_total 0 z with hz | hz
  · rw [max_eq_right hz, max_eq_right]
    exact one_le_rpow_of_one_le (by norm_num) hz
  · rw [max_eq_left hz, Real.rpow_zero, max_eq_left]
    calc (3 : ℝ) ^ z ≤ (3 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hz
      _ = 1 := Real.rpow_zero _

/-- **The activation length in terms of the absorption prefactor.**  The
formulaic tail shift is a ceiling, so the triadic power it names is at most
three times the truncated `kappa`-th root of the prefactor. -/
theorem pow_three_formulaicTailShift_le
    {s rho kappa : ℝ} {G : ℕ} (hkappa : 0 < kappa)
    (hP : 0 < Certificate.shiftedTailAbsorptionPrefactor d s rho G) :
    (3 : ℝ) ^
        ((Certificate.formulaicNormalizedReferenceTailShift d s rho kappa G :
          ℕ) : ℝ) ≤
      3 * max 1
        (Certificate.shiftedTailAbsorptionPrefactor d s rho G ^ kappa⁻¹) := by
  set P : ℝ := Certificate.shiftedTailAbsorptionPrefactor d s rho G with hPdef
  set L : ℕ := Certificate.formulaicNormalizedReferenceTailShift d s rho kappa G
    with hLdef
  have hspec :=
    (Certificate.formulaicNormalizedReferenceTailShift_spec
      (d := d) (s := s) (rho := rho) (kappa := kappa) (G := G) hkappa hP).2
  have hbound : ((L : ℕ) : ℝ) < max 0 (Real.logb 3 P / kappa) + 1 := hspec
  have hmono : (3 : ℝ) ^ ((L : ℕ) : ℝ) ≤
      (3 : ℝ) ^ (max 0 (Real.logb 3 P / kappa) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hbound.le
  have hsplit : (3 : ℝ) ^ (max 0 (Real.logb 3 P / kappa) + 1) =
      3 * (3 : ℝ) ^ max 0 (Real.logb 3 P / kappa) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3), Real.rpow_one, mul_comm]
  have hroot : (3 : ℝ) ^ (Real.logb 3 P / kappa) = P ^ kappa⁻¹ := by
    rw [div_eq_mul_inv, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.rpow_logb (by norm_num) (by norm_num) hP]
  calc (3 : ℝ) ^ ((L : ℕ) : ℝ)
      ≤ 3 * (3 : ℝ) ^ max 0 (Real.logb 3 P / kappa) := by
        rw [← hsplit]; exact hmono
    _ = 3 * max 1 ((3 : ℝ) ^ (Real.logb 3 P / kappa)) := by
        rw [rpow_three_max_zero]
    _ = 3 * max 1 (P ^ kappa⁻¹) := by rw [hroot]

/-- **The absorption prefactor in terms of the eccentricity bracket.**  The only
appearance of the homogenized matrix in the prefactor is the triadic bracket of
its witness eccentricity, raised to the row order. -/
theorem shiftedTailAbsorptionPrefactor_le_of_bracket
    {s rho bracket : ℝ} {G : ℕ} (hrho : 0 ≤ rho)
    (hgeom : 0 < 1 - (3 : ℝ) ^ (-(2 * s - rho)))
    (hG : (3 : ℝ) ^ ((G : ℕ) : ℝ) ≤ bracket) :
    Certificate.shiftedTailAbsorptionPrefactor d s rho G ≤
      (6 * (d : ℝ) * Real.sqrt d) *
        (bracket ^ rho * (1 / (1 - (3 : ℝ) ^ (-(2 * s - rho))))) := by
  have hGpos : (0 : ℝ) < (3 : ℝ) ^ ((G : ℕ) : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hpow : (3 : ℝ) ^ (rho * ((G : ℕ) : ℝ)) ≤ bracket ^ rho := by
    have hstep : ((3 : ℝ) ^ ((G : ℕ) : ℝ)) ^ rho ≤ bracket ^ rho :=
      Real.rpow_le_rpow hGpos.le hG hrho
    rwa [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), mul_comm ((G : ℕ) : ℝ) rho]
      at hstep
  have hdim : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d := by positivity
  have hinv : (0 : ℝ) ≤ 1 / (1 - (3 : ℝ) ^ (-(2 * s - rho))) :=
    le_of_lt (by positivity)
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hpow hinv) hdim

end

end RowSupply
end HighContrast
end HCPolySupport
