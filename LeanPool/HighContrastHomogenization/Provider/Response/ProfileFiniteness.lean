/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSkewCarriers
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileWeakCarriers

/-!
# High-contrast homogenization: Provider.Response.ProfileFiniteness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finiteness bridges for terminal response profiles

Fail-closed extended nonnegative profile quantities are converted to real
estimates only after an explicit finite upper bound has been established.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- An extended nonnegative quantity below `ofReal C` has the exact real
upper bound when `C` is nonnegative. -/
theorem toReal_le_of_le_ofReal {x : ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C)
    (h : x ≤ ENNReal.ofReal C) : x.toReal ≤ C := by
  have htop : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal hC] at hreal

end

end HCPolySupport.HighContrast.Response
