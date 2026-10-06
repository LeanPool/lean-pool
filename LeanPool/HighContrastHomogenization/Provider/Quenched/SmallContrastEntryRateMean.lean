/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRate

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastEntryRateMean

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The mean slot's source, and `hentry` at named constants

the corresponding argument.1 left one hole: `hVmeanle : Vmean ≤ vmsrc + cVm · F j_b` was consumed
everywhere and produced nowhere.  This file closes it from the construction's own
mean-slot machinery and instantiates the leg-bound entry estimate so that `hentry`
stands fully discharged at named constants.

**Where `Vmean` comes from.**  `entry_supply_mean_slot_bound_at`
(the cited theorem) converts the reference-normalized terminal
scale variance into the mean-normalized one:

  `scaleVariance P q (adaptedMean P q t) t ≤ ofReal (meanSlotConversion C_d g m_Al G_acc 𝐄 · V₀)`,

i.e. `Vmean ≤ conv · V₀` with `conv = meanSlotConversion …`.  The slot family
already bounds `V₀` — it *is* `slotFamilyValue d Csub Msc delta F(j_b) J 0`,
which is by definition `slotSourceSeq … J 0 + slotBaseCoefficient d · F(j_b)`.
So the mean slot splits into a source part and a base part with no new
estimate, only the conversion factor:

  `vmsrc = conv · slotSourceSeq d Csub Msc delta J 0`,
  `cVm   = conv · slotBaseCoefficient d`.

Its decay is the same `3^{-J/2}` as the variance leg, because
`slotSourceSeq … J 0 = slotSourceValue d Csub Msc J`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The `hVmeanle` hypothesis -/

/-- **The conversion splits the mean slot.**  Any bound `Vmean ≤ conv · V₀` with
`V₀` in source-plus-base shape gives `hVmeanle`'s shape. -/
theorem hVmeanle_of_conversion {conv V0 v0src cv0 Fjb Vmean : ℝ}
    (hconv0 : 0 ≤ conv) (hVmean : Vmean ≤ conv * V0)
    (hV0 : V0 ≤ v0src + cv0 * Fjb) :
    Vmean ≤ conv * v0src + conv * cv0 * Fjb := by
  have h := mul_le_mul_of_nonneg_left hV0 hconv0
  nlinarith only [hVmean, h]

/-- The mean slot's base coefficient. -/
@[expose]
def cVmConstant (d : ℕ) (conv : ℝ) : ℝ := conv * slotBaseCoefficient d

/-- **`hVmeanle` at the slot family.**  The `V₀` bound is definitional, so this
is the conversion step alone. -/
theorem hVmeanle_of_slot_family {conv Csub Msc delta Fjb Vmean : ℝ} {J : ℕ}
    (hconv0 : 0 ≤ conv)
    (hVmean : Vmean ≤ conv * slotFamilyValue d Csub Msc delta Fjb J 0) :
    Vmean ≤ conv * slotSourceSeq d Csub Msc delta J 0 +
      cVmConstant d conv * Fjb := by
  have h := hVmeanle_of_conversion (v0src := slotSourceSeq d Csub Msc delta J 0)
    (cv0 := slotBaseCoefficient d) hconv0 hVmean (le_of_eq rfl)
  rw [cVmConstant]
  linarith only [h]

/-! ## The mean leg at the common rate -/

/-! ## `hentry` at the construction's own three constants -/

end

end HCPolySupport.HighContrast.Quenched
