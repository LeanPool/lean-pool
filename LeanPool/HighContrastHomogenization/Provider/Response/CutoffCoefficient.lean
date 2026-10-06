/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.SourceObjects

/-!
# High-contrast homogenization: Provider.Response.CutoffCoefficient

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The dimensional cutoff coefficient

The first adapted-coordinate derivative of the pre-Young cutoff is bounded by
`C_d 3^{-t}`.  Multiplication by the scale-`s` cell diameter therefore leaves
the dimensional coefficient `C_d` and the scale-gap factor `3^{-H}`, where
`H = t - s`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

/-- The dimensional derivative bound contributes `C_d 3^{-H}` to the
cutoff-energy term when `H = t - s`. -/
theorem cutoff_energy_coefficient {Cd J : ℝ} {s t H : ℤ} (hH : H = t - s) :
    Cd * (3 : ℝ) ^ s * ((3 : ℝ) ^ (-t) * J) =
      Cd * (3 : ℝ) ^ (-H) * J := by
  subst H
  calc
    Cd * (3 : ℝ) ^ s * ((3 : ℝ) ^ (-t) * J) =
        Cd * ((3 : ℝ) ^ s * (3 : ℝ) ^ (-t)) * J := by ring
    _ = Cd * (3 : ℝ) ^ (s + -t) * J := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    _ = Cd * (3 : ℝ) ^ (-(t - s)) * J := by
      rw [show s + -t = -(t - s) by ring]

end Response
end HighContrast
end HCPolySupport
