/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowOscillationSum

/-!
# High-contrast homogenization: Provider.Response.PreYoungRowClosingAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Closing the pre-Young boundary rows

The boundary means split into a defect contribution and a cutoff-oscillation
contribution.  This file records the carrier conversion for that split and
specializes the four scale-sum estimates to the literal primal and adjoint row
premises used by the boundary-mean assembly.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Generic component assembly -/

/-- An exact decomposition into defect and oscillation terms gives the
corresponding mixed-ENNReal triangle bound. -/
theorem ofReal_abs_le_add_of_eq_add {mean defect oscillation : ℝ}
    (hmean : mean = defect + oscillation) :
    ENNReal.ofReal |mean| ≤
      ENNReal.ofReal |defect| + ENNReal.ofReal |oscillation| := by
  rw [hmean]
  calc
    ENNReal.ofReal |defect + oscillation| ≤
        ENNReal.ofReal (|defect| + |oscillation|) :=
      ENNReal.ofReal_le_ofReal (abs_add_le defect oscillation)
    _ = ENNReal.ofReal |defect| + ENNReal.ofReal |oscillation| :=
      ENNReal.ofReal_add (abs_nonneg defect) (abs_nonneg oscillation)

/-- A triangle bound closes once its defect and oscillation components have
been bounded separately. -/
theorem ofReal_abs_le_add_of_component_bounds
    {mean defect oscillation : ℝ} {defectBound oscillationBound : ℝ≥0∞}
    (hsplit : ENNReal.ofReal |mean| ≤
      ENNReal.ofReal |defect| + ENNReal.ofReal |oscillation|)
    (hdefect : ENNReal.ofReal |defect| ≤ defectBound)
    (hoscillation : ENNReal.ofReal |oscillation| ≤ oscillationBound) :
    ENNReal.ofReal |mean| ≤ defectBound + oscillationBound :=
  hsplit.trans (add_le_add hdefect hoscillation)

/-! ## Primal rows -/

/-! ## Adjoint rows -/

end

end HCPolySupport.HighContrast.Response
