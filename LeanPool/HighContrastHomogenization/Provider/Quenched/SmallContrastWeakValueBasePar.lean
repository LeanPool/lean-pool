/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSharpLineAtJb
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSupplyPorts

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastWeakValueBasePar

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The weak base with both group coefficients as parameters

`weakValueBaseIsotropyAtPar` releases the bad group's threshold pair but leaves both
group coefficients pinned at sixteen.  That is the wrong interface once the
split level moves: the recent group's coefficient and the maximum group's are
both functions of the level, and a base whose pinned-level equation is
definitional cannot express a coefficient that changes off the pin.

This file carries both as parameters.  The two invariants are still `rfl`: at
`(16, 16)` the parametrized base is `weakValueBaseIsotropyAtPar`, and at
`(16, 16, 1/2, 1)` it is `weakValueBaseIsotropyAtPar`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- **The metric-free weak base with both group coefficients free.** -/
@[expose]
def weakValueBaseIsotropyAtPar (cfirst cmax M L rho : ℝ) (Hw : ℕ)
    (bmaj beta lev : ℝ)
    (V : ℕ → ℝ) (V0 : ℝ) (Dr : ℕ → ℝ) (Vmean : ℝ) : ℝ :=
  cfirst * M * Real.sqrt L *
      ((∑ j ∈ Finset.range (Hw + 1),
          (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j)) +
        ∑ j ∈ Finset.range (Hw + 1),
          (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
            Real.sqrt (2 * d * Dr j)) +
    cmax * M / (2 * ((1 - rho) / 2)) *
      (Real.sqrt 2 * Real.sqrt (L + 1) *
          Response.profileBadMajorantAt 4 bmaj beta lev +
        Real.sqrt 2 * (3 : ℝ) ^ (-((1 - rho) / 2) * (Hw : ℝ)) *
          Real.sqrt (L + 1)) +
    Response.constantSeminormCoefficient * (M * Real.sqrt 7 * Vmean)

/-- Nonnegativity, at free coefficients. -/
theorem weakValueBaseIsotropyAtPar_nonneg {cfirst cmax M L rho : ℝ} {Hw : ℕ}
    {bmaj beta lev : ℝ} {V : ℕ → ℝ} {V0 : ℝ} {Dr : ℕ → ℝ} {Vmean : ℝ}
    (hcfirst : 0 ≤ cfirst) (hcmax : 0 ≤ cmax)
    (hM0 : 0 ≤ M) (hrho1 : rho < 1) (hbmaj : 0 ≤ bmaj) (hbeta : 0 ≤ beta)
    (hV : ∀ j, 0 ≤ V j) (hV0 : 0 ≤ V0) (hDr : ∀ j, 0 ≤ Dr j)
    (hVmean : 0 ≤ Vmean) :
    0 ≤ weakValueBaseIsotropyAtPar (d := d) cfirst cmax M L rho Hw bmaj beta lev
      V V0 Dr Vmean := by
  have hMf : (0 : ℝ) ≤ cfirst * M := mul_nonneg hcfirst hM0
  have hMx : (0 : ℝ) ≤ cmax * M := mul_nonneg hcmax hM0
  have hsem : (0 : ℝ) < Response.constantSeminormCoefficient := by
    rw [Response.constantSeminormCoefficient_eq]
    have hlt : (3 : ℝ) ^ (-(1 : ℝ) / 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    exact inv_pos.mpr (by linarith only [hlt])
  rw [weakValueBaseIsotropyAtPar]
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · refine mul_nonneg (mul_nonneg hMf (Real.sqrt_nonneg _)) ?_
    refine add_nonneg (Finset.sum_nonneg fun j _ => ?_)
      (Finset.sum_nonneg fun j _ => ?_)
    · refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
      linarith only [hV j, hV0, hDr j]
    · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
  · refine mul_nonneg (div_nonneg hMx (by linarith only [hrho1])) ?_
    refine add_nonneg ?_ ?_
    · refine mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        ?_
      exact Response.profileBadMajorantAt_nonneg hbmaj hbeta
    · exact mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
        (Real.sqrt_nonneg _)
  · exact mul_nonneg hsem.le
      (mul_nonneg (mul_nonneg hM0 (Real.sqrt_nonneg _)) hVmean)

end

end HCPolySupport.HighContrast.Quenched
