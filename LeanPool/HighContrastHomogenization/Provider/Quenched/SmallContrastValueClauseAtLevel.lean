/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValueBaseAbsorb

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastValueClauseAtLevel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The value clause at the line producer's pinned coefficients

The line producer reads the weak base at the pinned group coefficients; the
released weak value reports at coefficients that move with the split level.
This file names the normalizer that reconciles them, so the assembly can
supply the value clause without a producer of its own.

The normalizer is `(cfirst + cmax + 1) · M`, which is above `M` and dominates
both released coefficients after division by sixteen.  It is a choice, not an
estimate: every group of the base is linear in the normalizer and the
consumer's constant bundle asks only that it be nonnegative.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- The normalizer that carries a released pair of group coefficients into the
pinned pair. -/
@[expose]
def absorbedNormalizer (cfirst cmax M : ℝ) : ℝ := (cfirst + cmax + 1) * M

theorem absorbedNormalizer_nonneg {cfirst cmax M : ℝ} (hcfirst : 0 ≤ cfirst)
    (hcmax : 0 ≤ cmax) (hM : 0 ≤ M) : 0 ≤ absorbedNormalizer cfirst cmax M := by
  rw [absorbedNormalizer]
  have : (0 : ℝ) ≤ cfirst + cmax + 1 := by linarith only [hcfirst, hcmax]
  exact mul_nonneg this hM

/-- **The value clause at the pinned coefficients.**  A bound by the released
base is a bound by the pinned-coefficient base at the absorbed normalizer. -/
theorem le_baseIsotropyAtPar_pinned_of_atLevel
    {cfirst cmax M L rho bmaj beta lev wv : ℝ} {Hw : ℕ}
    {V : ℕ → ℝ} {V0 : ℝ} {Dr : ℕ → ℝ} {Vmean : ℝ}
    (hcfirst : 0 ≤ cfirst) (hcmax : 0 ≤ cmax) (hM : 0 ≤ M)
    (hrho1 : rho < 1) (hbmaj : 0 ≤ bmaj) (hbeta : 0 ≤ beta)
    (hV : ∀ j, 0 ≤ V j) (hV0 : 0 ≤ V0) (hDr : ∀ j, 0 ≤ Dr j)
    (hVmean : 0 ≤ Vmean)
    (hmaj : wv ≤ weakValueBaseIsotropyAtPar (d := d) cfirst cmax M L rho Hw
      bmaj beta lev V V0 Dr Vmean ^ 2) :
    wv ≤ weakValueBaseIsotropyAtPar (d := d) 16 16
      (absorbedNormalizer cfirst cmax M) L rho Hw bmaj beta lev
      V V0 Dr Vmean ^ 2 := by
  have hbase0 : 0 ≤ weakValueBaseIsotropyAtPar (d := d) cfirst cmax M L rho Hw
      bmaj beta lev V V0 Dr Vmean :=
    weakValueBaseIsotropyAtPar_nonneg hcfirst hcmax hM hrho1 hbmaj hbeta hV hV0
      hDr hVmean
  refine le_trans hmaj (pow_le_pow_left₀ hbase0 ?_ 2)
  rw [absorbedNormalizer]
  refine weakValueBaseIsotropyAtPar_absorb ?_ ?_ ?_ hrho1 hbmaj hbeta hV hV0 hDr
    hVmean
  · nlinarith only [hcfirst, hcmax, hM]
  · nlinarith only [hcfirst, hcmax, hM]
  · nlinarith only [hcfirst, hcmax, hM]

end

end HCPolySupport.HighContrast.Quenched
