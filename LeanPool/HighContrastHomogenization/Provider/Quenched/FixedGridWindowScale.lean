/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Selection.RoundedHops
public import LeanPool.HighContrastHomogenization.Setup.SelectionObjects

/-!
# High-contrast homogenization: Provider.Quenched.FixedGridWindowScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scale account for a fixed canonical grid

A fixed rounded grid whose witness eccentricity is bounded by the reference
aspect ratio fits in a dimensionally enlarged centered cube.  The enlargement
is linear in the logarithmic reference scale, so a fixed four-generation
response lag fits inside a coupled source window with a dimensional execution
coefficient.
-/

namespace HCPolySupport.HighContrast.Quenched

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The number of extra triadic generations needed to enclose a rounded grid
whose witness eccentricity is at most `Pi`. -/
@[expose]
def canonicalGridEnlargement (d : ℕ) (Pi : ℝ) : ℕ :=
  ⌈Real.logb 3 ((100 / 99 : ℝ) * Pi * Real.sqrt d)⌉₊

/-- Rounding at any admissible fixed scale preserves the canonical enclosure
bound. -/
theorem norm_roundedGrid_mul_sqrt_le_canonicalGridEnlargement
    (hd : 2 ≤ d) {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {m : Mat d} (hm : m.PosDef) {Pi : ℝ} (hPi : 1 ≤ Pi)
    (hecc : witnessEccentricity m ≤ Pi) :
    ‖roundedGrid l m‖ * Real.sqrt d ≤
      (3 : ℝ) ^ canonicalGridEnlargement d Pi := by
  let : NeZero d := ⟨by omega⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsqrt0 : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  have hPi0 : 0 < Pi := lt_of_lt_of_le zero_lt_one hPi
  let a : ℝ := (100 / 99 : ℝ) * Pi * Real.sqrt d
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have hceil : Real.logb 3 a ≤ (canonicalGridEnlargement d Pi : ℝ) := by
    dsimp only [canonicalGridEnlargement, a]
    exact Nat.le_ceil _
  have hlarge : a ≤ (3 : ℝ) ^ canonicalGridEnlargement d Pi := by
    have hmono := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hceil
    rw [Real.rpow_logb (by norm_num) (by norm_num) ha,
      Real.rpow_natCast] at hmono
    exact hmono
  have hnorm := Selection.norm_roundedGrid_le hl hm
  calc
    ‖roundedGrid l m‖ * Real.sqrt d ≤
        ((100 / 99 : ℝ) * witnessEccentricity m) * Real.sqrt d :=
      mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg d)
    _ ≤ ((100 / 99 : ℝ) * Pi) * Real.sqrt d :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hecc (by norm_num))
        (Real.sqrt_nonneg d)
    _ = a := by rfl
    _ ≤ (3 : ℝ) ^ canonicalGridEnlargement d Pi := hlarge

end

end HCPolySupport.HighContrast.Quenched
