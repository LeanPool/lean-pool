/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FoldedFrameExponent
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.ActivationScaleEccentricity
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.PerGOrderGapAudit

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.Dirichlet.ActivationFold

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The activation length folded into the eccentricity factor

The certificate's activation length is a triadic power of the formulaic tail
shift; the shift is a logarithm of the absorption prefactor; and the prefactor
carries the homogenized matrix only through the triadic bracket of its witness
eccentricity, at the row order.  Composing those three facts writes any fixed
nonnegative power of the activation length as a law-free constant times the
eccentricity fold factor raised to the rate — which is exactly what the folded
homogenization length pays for.

The exponent of the fold factor is `rho * c / (2 kappa^2)`, with `rho` the row
order, `c` the power of the activation length being folded and `kappa` the rate:
law-free, as the frozen polynomial-length clause requires.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-! ## The fold factor as a power of the truncated eccentricity -/

/-- The fold factor is the truncated eccentricity raised to its exponent. -/
theorem eccentricityFoldFactor_eq_max_rpow (abar : Mat d) {p : ℝ} (hp : 0 ≤ p) :
    eccentricityFoldFactor abar p =
      (max 1 (witnessEccentricity (symmPart abar))) ^ p := by
  have he0 : (0 : ℝ) ≤ witnessEccentricity (symmPart abar) :=
    witnessEccentricity_nonneg _
  rcases le_or_gt (witnessEccentricity (symmPart abar)) 1 with he | he
  · rw [eccentricityFoldFactor, max_eq_left he, Real.one_rpow, max_eq_left]
    calc witnessEccentricity (symmPart abar) ^ p ≤ (1 : ℝ) ^ p :=
          Real.rpow_le_rpow he0 he hp
      _ = 1 := Real.one_rpow p
  · rw [eccentricityFoldFactor, max_eq_right he.le, max_eq_right]
    exact one_le_rpow_of_one_le he.le hp

/-! ## The law-free prefactor -/

/-- The law-free part of the absorption prefactor, at the root the fold takes. -/
@[expose]
def foldPrefactorBase (d : ℕ) (g kappaRate : ℝ) : ℝ :=
  ((6 * (d : ℝ) * Real.sqrt d) *
      (1 / (1 - (3 : ℝ) ^
        (-(2 * responseWindowOrder g - Certificate.printRowOrder g))))) ^
      (2 * kappaRate)⁻¹ *
    (1 + 3 * Real.sqrt d) ^
      (Certificate.printRowOrder g / (2 * kappaRate))

/-- The law-free constant multiplying the folded activation power. -/
@[expose]
def activationFoldConstant (d : ℕ) (g kappaRate c : ℝ) : ℝ :=
  (3 * max 1 (foldPrefactorBase d g kappaRate)) ^ c

/-! ## The fold -/

/-- **The activation power folds.**  Any nonnegative power of the certificate's
activation length is a law-free constant times the eccentricity fold factor
raised to the rate. -/
theorem rpow_activation_le_foldFactor
    {abar : Mat d} {g kappaRate c : ℝ} {G L : ℕ}
    (hkappa : 0 < kappaRate) (hc : 0 ≤ c)
    (hrho : 0 ≤ Certificate.printRowOrder g)
    (hgeom : 0 < 1 - (3 : ℝ) ^
      (-(2 * responseWindowOrder g - Certificate.printRowOrder g)))
    (hP : 0 < Certificate.shiftedTailAbsorptionPrefactor d
      (responseWindowOrder g) (Certificate.printRowOrder g) G)
    (hLeq : L = Certificate.formulaicNormalizedReferenceTailShift d
      (responseWindowOrder g) (Certificate.printRowOrder g)
        (2 * kappaRate) G)
    (hGupper : (3 : ℝ) ^ ((G : ℕ) : ℝ) ≤
      1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d)) :
    ((3 : ℝ) ^ ((L : ℕ) : ℝ)) ^ c ≤
      activationFoldConstant d g kappaRate c *
        (eccentricityFoldFactor abar
          (Certificate.printRowOrder g * c /
            (2 * kappaRate * kappaRate))) ^ kappaRate := by
  have h2k : (0 : ℝ) < 2 * kappaRate := by linarith only [hkappa]
  have hexp : (0 : ℝ) ≤ (2 * kappaRate)⁻¹ := (inv_pos.mpr h2k).le
  have hquot : (0 : ℝ) ≤ Certificate.printRowOrder g / (2 * kappaRate) :=
    div_nonneg hrho h2k.le
  set rho : ℝ := Certificate.printRowOrder g with hrhoDef
  set E : ℝ := max 1 (witnessEccentricity (symmPart abar)) with hEdef
  have hE1 : (1 : ℝ) ≤ E := le_max_left _ _
  have hE0 : (0 : ℝ) ≤ E := le_trans zero_le_one hE1
  have hd0 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  set geom : ℝ := 1 / (1 - (3 : ℝ) ^
    (-(2 * responseWindowOrder g - rho)) : ℝ) with hgeomDef
  have hgeom0 : (0 : ℝ) ≤ geom := by
    rw [hgeomDef]
    exact le_of_lt (one_div_pos.mpr hgeom)
  set A : ℝ := (6 * (d : ℝ) * Real.sqrt d) * geom with hAdef
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hAdef]; positivity
  have hdimBase0 : (0 : ℝ) ≤ 1 + 3 * Real.sqrt d := by positivity
  -- the shift bound
  have hshift := pow_three_formulaicTailShift_le (d := d)
    (s := responseWindowOrder g) (rho := rho)
    (kappa := 2 * kappaRate) (G := G) h2k hP
  rw [← hLeq] at hshift
  -- the prefactor bound in terms of the truncated eccentricity
  have hbracket0 : (0 : ℝ) ≤
      1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d) := by
    have h := witnessEccentricity_nonneg (symmPart abar)
    positivity
  have hbracket : 1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d) ≤
      (1 + 3 * Real.sqrt d) * E := by
    have hecc : witnessEccentricity (symmPart abar) ≤ E := le_max_right _ _
    have hstep : 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d) ≤
        3 * Real.sqrt d * E := by
      have hmul := mul_le_mul_of_nonneg_right hecc hd0
      calc 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d)
          ≤ 3 * (E * Real.sqrt d) :=
            mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = 3 * Real.sqrt d * E := by ring
    linarith only [hstep, hE1]
  have hPle := shiftedTailAbsorptionPrefactor_le_of_bracket (d := d)
    (s := responseWindowOrder g) (rho := rho)
    (bracket := 1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d))
    (G := G) hrho hgeom hGupper
  have hPfinal : Certificate.shiftedTailAbsorptionPrefactor d
      (responseWindowOrder g) rho G ≤
      (A * (1 + 3 * Real.sqrt d) ^ rho) * E ^ rho := by
    refine hPle.trans ?_
    have hpow : (1 + 3 * (witnessEccentricity (symmPart abar) *
        Real.sqrt d)) ^ rho ≤ ((1 + 3 * Real.sqrt d) * E) ^ rho :=
      Real.rpow_le_rpow hbracket0 hbracket hrho
    have hsplit : ((1 + 3 * Real.sqrt d) * E) ^ rho =
        (1 + 3 * Real.sqrt d) ^ rho * E ^ rho :=
      Real.mul_rpow hdimBase0 hE0
    rw [hsplit] at hpow
    have hdim0 : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d := by positivity
    calc (6 * (d : ℝ) * Real.sqrt d) *
          ((1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d)) ^ rho
            * geom) ≤
        (6 * (d : ℝ) * Real.sqrt d) *
          (((1 + 3 * Real.sqrt d) ^ rho * E ^ rho) * geom) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow hgeom0) hdim0
      _ = (A * (1 + 3 * Real.sqrt d) ^ rho) * E ^ rho := by
          rw [hAdef]; ring
  -- take the root
  have hbaseFactor0 : (0 : ℝ) ≤ A * (1 + 3 * Real.sqrt d) ^ rho :=
    mul_nonneg hA0 (Real.rpow_nonneg hdimBase0 _)
  have hErho0 : (0 : ℝ) ≤ E ^ rho := Real.rpow_nonneg hE0 _
  have hrootEq : ((A * (1 + 3 * Real.sqrt d) ^ rho) * E ^ rho) ^
        (2 * kappaRate)⁻¹ =
      foldPrefactorBase d g kappaRate * E ^ (rho / (2 * kappaRate)) := by
    rw [Real.mul_rpow hbaseFactor0 hErho0,
      Real.mul_rpow hA0 (Real.rpow_nonneg hdimBase0 _),
      ← Real.rpow_mul hdimBase0, ← Real.rpow_mul hE0, foldPrefactorBase]
    rw [hAdef, hgeomDef, hrhoDef]
    rw [div_eq_mul_inv, div_eq_mul_inv]
  have hroot : Certificate.shiftedTailAbsorptionPrefactor d
      (responseWindowOrder g) rho G ^ (2 * kappaRate)⁻¹ ≤
      foldPrefactorBase d g kappaRate * E ^ (rho / (2 * kappaRate)) := by
    rw [← hrootEq]
    exact Real.rpow_le_rpow hP.le hPfinal hexp
  -- truncate
  have hEpow1 : (1 : ℝ) ≤ E ^ (rho / (2 * kappaRate)) :=
    one_le_rpow_of_one_le hE1 hquot
  have hmaxStep : max 1 (Certificate.shiftedTailAbsorptionPrefactor d
        (responseWindowOrder g) rho G ^ (2 * kappaRate)⁻¹) ≤
      max 1 (foldPrefactorBase d g kappaRate) * E ^ (rho / (2 * kappaRate)) := by
    refine (max_le_max (le_refl (1 : ℝ)) hroot).trans ?_
    refine (max_one_mul_le_mul_max_one (Real.rpow_nonneg hE0 _)).trans ?_
    exact le_of_eq (by rw [max_eq_right hEpow1])
  have hLbound : (3 : ℝ) ^ ((L : ℕ) : ℝ) ≤
      (3 * max 1 (foldPrefactorBase d g kappaRate)) *
        E ^ (rho / (2 * kappaRate)) := by
    refine hshift.trans ?_
    have := mul_le_mul_of_nonneg_left hmaxStep (by norm_num : (0 : ℝ) ≤ 3)
    calc 3 * max 1 (Certificate.shiftedTailAbsorptionPrefactor d
            (responseWindowOrder g) rho G ^ (2 * kappaRate)⁻¹)
        ≤ 3 * (max 1 (foldPrefactorBase d g kappaRate) *
            E ^ (rho / (2 * kappaRate))) := this
      _ = (3 * max 1 (foldPrefactorBase d g kappaRate)) *
            E ^ (rho / (2 * kappaRate)) := by ring
  -- raise to the power c
  have hL0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((L : ℕ) : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have hconst0 : (0 : ℝ) ≤ 3 * max 1 (foldPrefactorBase d g kappaRate) := by
    have : (1 : ℝ) ≤ max 1 (foldPrefactorBase d g kappaRate) := le_max_left _ _
    linarith only [this]
  have hpowStep : ((3 : ℝ) ^ ((L : ℕ) : ℝ)) ^ c ≤
      ((3 * max 1 (foldPrefactorBase d g kappaRate)) *
        E ^ (rho / (2 * kappaRate))) ^ c :=
    Real.rpow_le_rpow hL0 hLbound hc
  have hsplitc : ((3 * max 1 (foldPrefactorBase d g kappaRate)) *
        E ^ (rho / (2 * kappaRate))) ^ c =
      activationFoldConstant d g kappaRate c *
        E ^ (rho * c / (2 * kappaRate)) := by
    rw [Real.mul_rpow hconst0 (Real.rpow_nonneg hE0 _),
      ← Real.rpow_mul hE0, activationFoldConstant]
    congr 2
    field_simp
  -- rewrite the fold factor
  have hpEcc0 : (0 : ℝ) ≤ rho * c / (2 * kappaRate * kappaRate) := by
    have hden : (0 : ℝ) < 2 * kappaRate * kappaRate := by positivity
    exact div_nonneg (mul_nonneg hrho hc) hden.le
  have hfold : (eccentricityFoldFactor abar
        (rho * c / (2 * kappaRate * kappaRate))) ^ kappaRate =
      E ^ (rho * c / (2 * kappaRate)) := by
    rw [eccentricityFoldFactor_eq_max_rpow abar hpEcc0, ← hEdef,
      ← Real.rpow_mul hE0]
    congr 1
    field_simp
  rw [hfold]
  exact hpowStep.trans (le_of_eq hsplitc)

end

end RowSupply
end HighContrast
end HCPolySupport
