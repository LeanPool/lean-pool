/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungExplicitAssembly

/-!
# High-contrast homogenization: Provider.Response.PreYoungWeakTop

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The infinite weak-quantity branch

The compact pre-Young estimate is automatic when its weak quantity is
infinite and the response coefficient is positive.  Separating this branch
keeps finiteness assumptions local to the analytic component estimates.
-/

namespace HCPolySupport.HighContrast.Response

open scoped ENNReal

/-- The compact pre-Young right-hand side is top when its weak quantity is top
and its coefficient is positive. -/
theorem le_compact_pre_young_of_weak_eq_top
    {J a b row weak expo : ℝ≥0∞} {Cresp : ℝ}
    (hCresp : 0 < Cresp) (hweak : weak = ⊤) :
    J ≤
      ENNReal.ofReal Cresp * a * (a + b + row) +
      ENNReal.ofReal Cresp * expo * b * (b + row) +
      ENNReal.ofReal Cresp * weak := by
  have hC : ENNReal.ofReal Cresp ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hCresp).ne'
  rw [hweak, ENNReal.mul_top hC]
  simpa only [add_top] using (le_top : J ≤ (⊤ : ℝ≥0∞))

/-- It suffices to prove the compact estimate under finiteness of the weak
quantity; the complementary branch is automatic. -/
theorem compact_pre_young_of_finite_weak
    {J a b row weak expo : ℝ≥0∞} {Cpre : ℝ}
    (hCpre : 1 ≤ Cpre)
    (hfinite : weak ≠ ⊤ → ∀ Cresp, Cpre ≤ Cresp →
      J ≤
        ENNReal.ofReal Cresp * a * (a + b + row) +
        ENNReal.ofReal Cresp * expo * b * (b + row) +
        ENNReal.ofReal Cresp * weak) :
    ∀ Cresp, Cpre ≤ Cresp →
      J ≤
        ENNReal.ofReal Cresp * a * (a + b + row) +
        ENNReal.ofReal Cresp * expo * b * (b + row) +
        ENNReal.ofReal Cresp * weak := by
  intro Cresp hCresp
  by_cases hweak : weak = ⊤
  · exact le_compact_pre_young_of_weak_eq_top
      (zero_lt_one.trans_le (hCpre.trans hCresp)) hweak
  · exact hfinite hweak Cresp hCresp

/-- Component estimates are needed only in the finite weak-quantity branch.
The resulting compact estimate remains unconditional. -/
theorem compact_pre_young_of_finite_component_bounds
    {J boundaryRow a b scaleRoot rowRoot weak expo : ℝ≥0∞}
    {Ccut Crow Cdiv Cpre : ℝ}
    (hCpre : 1 ≤ Cpre)
    (hcomponents : weak ≠ ⊤ → ∃ divCurl cutoffEnergy : ℝ≥0∞,
      J ≤ divCurl + cutoffEnergy + boundaryRow ∧
      divCurl ≤ ENNReal.ofReal Cdiv * weak ∧
      cutoffEnergy ≤
        ENNReal.ofReal 2 * a * a +
          ENNReal.ofReal 4 * a * b +
            ENNReal.ofReal Ccut * expo * b * b ∧
      boundaryRow ≤
        ENNReal.ofReal (Real.sqrt 2) * a * scaleRoot +
          ENNReal.ofReal Crow * expo * b * rowRoot)
    (hscaleRoot : scaleRoot ≤ rowRoot)
    (hfour : 4 ≤ Cpre) (hsqrtTwo : Real.sqrt 2 ≤ Cpre)
    (hcut : Ccut ≤ Cpre) (hrow : Crow ≤ Cpre)
    (hdiv : Cdiv ≤ Cpre) :
    ∀ Cresp, Cpre ≤ Cresp →
      J ≤
        ENNReal.ofReal Cresp * a * (a + b + rowRoot) +
        ENNReal.ofReal Cresp * expo * b * (b + rowRoot) +
        ENNReal.ofReal Cresp * weak := by
  apply compact_pre_young_of_finite_weak hCpre
  intro hweak Cresp hCresp
  obtain ⟨divCurl, cutoffEnergy, hdecomposition, hdivCurl,
    hcutoffEnergy, hboundaryRow⟩ := hcomponents hweak
  exact compact_pre_young_of_component_bounds hdecomposition hdivCurl
    hcutoffEnergy hboundaryRow hscaleRoot (hfour.trans hCresp)
    (hsqrtTwo.trans hCresp) (hcut.trans hCresp) (hrow.trans hCresp)
    (hdiv.trans hCresp)

end HCPolySupport.HighContrast.Response
