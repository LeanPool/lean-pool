/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValueBasePar

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastWeakValueBaseAbsorb

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Absorbing released group coefficients into the base's normalizer

The line producer reads the weak base at the pinned group coefficients, and the
released weak-norm chain produces it at coefficients that move with the split
level.  The two are reconciled without touching the line producer: the base's
normalizer is a free parameter of the consumer's constant bundle, and each
group is linear in it, so a coefficient above the pinned one is paid for by
enlarging the normalizer.

This is the only reconciliation the released route needs on the value side; the
threshold pair itself is carried through the line producer as a parameter.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- **The absorption.**  A parametrized base at released coefficients is
dominated by the pinned-coefficient base at an enlarged normalizer. -/
theorem weakValueBaseIsotropyAtPar_absorb
    {cfirst cmax M M' L rho bmaj beta lev : ℝ} {Hw : ℕ}
    {V : ℕ → ℝ} {V0 : ℝ} {Dr : ℕ → ℝ} {Vmean : ℝ}
    (hcf : cfirst * M ≤ 16 * M') (hcm : cmax * M ≤ 16 * M') (hMM : M ≤ M')
    (hrho1 : rho < 1) (hbmaj : 0 ≤ bmaj) (hbeta : 0 ≤ beta)
    (hV : ∀ j, 0 ≤ V j) (hV0 : 0 ≤ V0) (hDr : ∀ j, 0 ≤ Dr j)
    (hVmean : 0 ≤ Vmean) :
    weakValueBaseIsotropyAtPar (d := d) cfirst cmax M L rho Hw bmaj beta lev
        V V0 Dr Vmean ≤
      weakValueBaseIsotropyAtPar (d := d) 16 16 M' L rho Hw bmaj beta lev
        V V0 Dr Vmean := by
  have hsum0 : (0 : ℝ) ≤
      ((∑ j ∈ Finset.range (Hw + 1),
          (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j)) +
        ∑ j ∈ Finset.range (Hw + 1),
          (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
            Real.sqrt (2 * (d : ℝ) * Dr j)) := by
    refine add_nonneg (Finset.sum_nonneg fun j _ => ?_)
      (Finset.sum_nonneg fun j _ => ?_)
    · refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
      linarith only [hV j, hV0, hDr j]
    · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
  have hbad0 : (0 : ℝ) ≤
      (Real.sqrt 2 * Real.sqrt (L + 1) *
          Response.profileBadMajorantAt 4 bmaj beta lev +
        Real.sqrt 2 * (3 : ℝ) ^ (-((1 - rho) / 2) * (Hw : ℝ)) *
          Real.sqrt (L + 1)) := by
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (Response.profileBadMajorantAt_nonneg hbmaj hbeta)
    · exact mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
        (Real.sqrt_nonneg _)
  have hden : (0 : ℝ) < 2 * ((1 - rho) / 2) := by linarith only [hrho1]
  have hsem : (0 : ℝ) ≤ Response.constantSeminormCoefficient := by
    rw [Response.constantSeminormCoefficient_eq]
    have hlt : (3 : ℝ) ^ (-(1 : ℝ) / 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 2) := by
      linarith only [hlt]
    positivity
  rw [weakValueBaseIsotropyAtPar, weakValueBaseIsotropyAtPar]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcf (Real.sqrt_nonneg L)) hsum0
  · exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hcm hden.le) hbad0
  · refine mul_le_mul_of_nonneg_left ?_ hsem
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hMM (Real.sqrt_nonneg 7)) hVmean

end

end HCPolySupport.HighContrast.Quenched
