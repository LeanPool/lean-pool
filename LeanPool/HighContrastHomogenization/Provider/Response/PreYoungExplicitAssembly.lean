/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungAssemblyAlgebra

/-!
# High-contrast homogenization: Provider.Response.PreYoungExplicitAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Explicit pre-Young component assembly

The deterministic decomposition separates the centered response into a
div--curl term, a cutoff-energy term, and a boundary-row term.  This file
combines bounds for those three components and passes the resulting six-term
estimate to the compact pre-Young algebra.
-/

namespace HCPolySupport.HighContrast.Response

open scoped ENNReal

noncomputable section

/-- Component bounds for the three terms of the centered-response
decomposition give the explicit six-term pre-Young estimate. -/
theorem explicit_pre_young_of_component_bounds
    {J divCurl cutoffEnergy boundaryRow : ℝ≥0∞}
    {a b scaleRoot rowRoot weak expo : ℝ≥0∞}
    {Ccut Crow Cdiv : ℝ}
    (hdecomposition : J ≤ divCurl + cutoffEnergy + boundaryRow)
    (hdivCurl : divCurl ≤ ENNReal.ofReal Cdiv * weak)
    (hcutoffEnergy : cutoffEnergy ≤
      ENNReal.ofReal 2 * a * a +
        ENNReal.ofReal 4 * a * b +
          ENNReal.ofReal Ccut * expo * b * b)
    (hboundaryRow : boundaryRow ≤
      ENNReal.ofReal (Real.sqrt 2) * a * scaleRoot +
        ENNReal.ofReal Crow * expo * b * rowRoot) :
    J ≤
      ENNReal.ofReal 2 * a * a +
      ENNReal.ofReal 4 * a * b +
      ENNReal.ofReal (Real.sqrt 2) * a * scaleRoot +
      ENNReal.ofReal Ccut * expo * b * b +
      ENNReal.ofReal Crow * expo * b * rowRoot +
      ENNReal.ofReal Cdiv * weak := by
  calc
    J ≤ divCurl + cutoffEnergy + boundaryRow := hdecomposition
    _ ≤ (ENNReal.ofReal Cdiv * weak) +
        (ENNReal.ofReal 2 * a * a +
          ENNReal.ofReal 4 * a * b +
          ENNReal.ofReal Ccut * expo * b * b) +
        (ENNReal.ofReal (Real.sqrt 2) * a * scaleRoot +
          ENNReal.ofReal Crow * expo * b * rowRoot) :=
      add_le_add (add_le_add hdivCurl hcutoffEnergy) hboundaryRow
    _ = ENNReal.ofReal 2 * a * a +
        ENNReal.ofReal 4 * a * b +
        ENNReal.ofReal (Real.sqrt 2) * a * scaleRoot +
        ENNReal.ofReal Ccut * expo * b * b +
        ENNReal.ofReal Crow * expo * b * rowRoot +
        ENNReal.ofReal Cdiv * weak := by ring

/-- The same three component bounds imply the exact compact mixed-ENNReal
right-hand side used by the conditional response theorem. -/
theorem compact_pre_young_of_component_bounds
    {J divCurl cutoffEnergy boundaryRow : ℝ≥0∞}
    {a b scaleRoot rowRoot weak expo : ℝ≥0∞}
    {Ccut Crow Cdiv Cresp : ℝ}
    (hdecomposition : J ≤ divCurl + cutoffEnergy + boundaryRow)
    (hdivCurl : divCurl ≤ ENNReal.ofReal Cdiv * weak)
    (hcutoffEnergy : cutoffEnergy ≤
      ENNReal.ofReal 2 * a * a +
        ENNReal.ofReal 4 * a * b +
          ENNReal.ofReal Ccut * expo * b * b)
    (hboundaryRow : boundaryRow ≤
      ENNReal.ofReal (Real.sqrt 2) * a * scaleRoot +
        ENNReal.ofReal Crow * expo * b * rowRoot)
    (hscaleRoot : scaleRoot ≤ rowRoot)
    (hfour : 4 ≤ Cresp)
    (hsqrtTwo : Real.sqrt 2 ≤ Cresp)
    (hcut : Ccut ≤ Cresp)
    (hrow : Crow ≤ Cresp)
    (hdiv : Cdiv ≤ Cresp) :
    J ≤
      ENNReal.ofReal Cresp * a * (a + b + rowRoot) +
      ENNReal.ofReal Cresp * expo * b * (b + rowRoot) +
      ENNReal.ofReal Cresp * weak := by
  apply compact_pre_young_of_explicit_components
    (hscaleRoot := hscaleRoot) (hfour := hfour) (hsqrtTwo := hsqrtTwo)
    (hcut := hcut) (hrow := hrow) (hdiv := hdiv)
  exact explicit_pre_young_of_component_bounds hdecomposition hdivCurl
    hcutoffEnergy hboundaryRow

end

end HCPolySupport.HighContrast.Response
