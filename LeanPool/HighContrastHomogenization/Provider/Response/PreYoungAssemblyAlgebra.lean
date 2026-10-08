/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffEnergy

/-!
# High-contrast homogenization: Provider.Response.PreYoungAssemblyAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Algebraic closure of the pre-Young response estimate

The cutoff, div--curl, and boundary-row estimates produce six nonnegative
terms.  This file records the coefficient enlargement and the distributive
calculation that put those terms into the compact mixed form used by the
response argument.
-/

namespace HCPolySupport.HighContrast.Response

open scoped ENNReal

noncomputable section

/-- A dimension-only cutoff constant and any further dimension-only transport
coefficient admit one common pre-Young constant. -/
theorem exists_one_le_pre_young_constant (d : ℕ) (Ctransport : ℝ) :
    ∃ Cpre : ℝ,
      1 ≤ Cpre ∧
      32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound ≤ Cpre ∧
      Ctransport ≤ Cpre ∧
      4 ≤ Cpre ∧
      Real.sqrt 2 ≤ Cpre := by
  obtain ⟨Ccut, hCcutOne, hCcut⟩ := exists_one_le_sharpCutoffConstant d
  let Cpre := max 4 (max (Real.sqrt 2) (max Ccut Ctransport))
  refine ⟨Cpre, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (by norm_num) (le_max_left _ _)
  · exact hCcut.trans
      (le_trans (le_max_left _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))
  · exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  · exact le_max_left _ _
  · exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- The explicit defect, energy, boundary-row, and weak terms are dominated by
the compact mixed pre-Young expression once their coefficients share one
upper bound. -/
theorem compact_pre_young_of_explicit_components
    {J a b scaleRoot rowRoot weak expo : ℝ≥0∞}
    {Ccut Crow Cdiv Cresp : ℝ}
    (hJ : J ≤
      ENNReal.ofReal 2 * a * a +
      ENNReal.ofReal 4 * a * b +
      ENNReal.ofReal (Real.sqrt 2) * a * scaleRoot +
      ENNReal.ofReal Ccut * expo * b * b +
      ENNReal.ofReal Crow * expo * b * rowRoot +
      ENNReal.ofReal Cdiv * weak)
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
  have htwo : (2 : ℝ) ≤ Cresp := le_trans (by norm_num) hfour
  have haa : ENNReal.ofReal 2 * a * a ≤ ENNReal.ofReal Cresp * a * a := by
    gcongr
  have hab : ENNReal.ofReal 4 * a * b ≤ ENNReal.ofReal Cresp * a * b := by
    gcongr
  have har : ENNReal.ofReal (Real.sqrt 2) * a * scaleRoot ≤
      ENNReal.ofReal Cresp * a * rowRoot := by
    gcongr
  have hbb : ENNReal.ofReal Ccut * expo * b * b ≤
      ENNReal.ofReal Cresp * expo * b * b := by
    gcongr
  have hbr : ENNReal.ofReal Crow * expo * b * rowRoot ≤
      ENNReal.ofReal Cresp * expo * b * rowRoot := by
    gcongr
  have hw : ENNReal.ofReal Cdiv * weak ≤ ENNReal.ofReal Cresp * weak := by
    gcongr
  calc
    J ≤ ENNReal.ofReal 2 * a * a +
        ENNReal.ofReal 4 * a * b +
        ENNReal.ofReal (Real.sqrt 2) * a * scaleRoot +
        ENNReal.ofReal Ccut * expo * b * b +
        ENNReal.ofReal Crow * expo * b * rowRoot +
        ENNReal.ofReal Cdiv * weak := hJ
    _ ≤ ENNReal.ofReal Cresp * a * a +
        ENNReal.ofReal Cresp * a * b +
        ENNReal.ofReal Cresp * a * rowRoot +
        ENNReal.ofReal Cresp * expo * b * b +
        ENNReal.ofReal Cresp * expo * b * rowRoot +
        ENNReal.ofReal Cresp * weak := by
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add haa hab) har) hbb) hbr) hw
    _ = ENNReal.ofReal Cresp * a * (a + b + rowRoot) +
        ENNReal.ofReal Cresp * expo * b * (b + rowRoot) +
        ENNReal.ofReal Cresp * weak := by ring

end

end HCPolySupport.HighContrast.Response
