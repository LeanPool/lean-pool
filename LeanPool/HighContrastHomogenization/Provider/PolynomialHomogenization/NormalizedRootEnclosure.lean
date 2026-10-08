/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.EuclideanAdapter
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedRootCoefficient
public import LeanPool.HighContrastHomogenization.Provider.Selection.EnclosureGeometry

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.NormalizedRootEnclosure

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Enclosure bounds for the exact normalized root

The exact identity-normalizing root has a triadic enclosure controlled by its
projective eccentricity.  Its inverse norm also removes the coefficient
dependence from the boundary-filling factor.
-/

namespace HCPolySupport.HighContrast

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- For the exact normalized root, the boundary-filling factor is bounded by
the dimension-only factor. -/
theorem normalizedRoot_fillingBoundaryFactor_le
    (hd : 1 ≤ d) {m : Mat d} (hm : m.PosDef) :
    max 1
        (6 * (d : ℝ) * Real.sqrt d * ‖(Selection.normalizedRoot m)⁻¹‖) ≤
      6 * (d : ℝ) * Real.sqrt d := by
  let : NeZero d := ⟨by omega⟩
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsqrt : (1 : ℝ) ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
    exact Real.sqrt_le_sqrt hdR
  have hprod : (1 : ℝ) ≤ (d : ℝ) * Real.sqrt d := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (d : ℝ) * Real.sqrt d :=
        mul_le_mul hdR hsqrt (by norm_num) (by norm_num)
  have hfactor : (1 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d := by
    calc
      (1 : ℝ) ≤ 6 := by norm_num
      _ = 6 * 1 := by ring
      _ ≤ 6 * ((d : ℝ) * Real.sqrt d) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 6 * (d : ℝ) * Real.sqrt d := by ring
  refine max_le hfactor ?_
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Selection.normalizedRoot_inv_norm_le_one hm) (zero_le_one.trans hfactor)

end

end HCPolySupport.HighContrast
