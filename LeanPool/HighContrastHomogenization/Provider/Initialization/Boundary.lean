/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.RoundedGrid
public import LeanPool.HighContrastHomogenization.Setup.SpectralNorm
public import LeanPool.HighContrastHomogenization.Setup.SourceObjects

/-!
# High-contrast homogenization: Provider.Initialization.Boundary

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Lower bounds for the source boundary constant

The witness eccentricity is a matrix condition number and is at least one.
The geometric-series factor is also at least one for `0 ≤ g < 1`; hence the
printed boundary constant is at least one as soon as its dimensional factor is.
-/

namespace HCPolySupport
namespace HighContrast
namespace Initialization

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The eccentricity of a positive witness is at least one in positive
dimension. -/
theorem one_le_witnessEccentricity [Nonempty (Fin d)] {mu : Mat d}
    (hmu : mu.PosDef) :
    1 ≤ witnessEccentricity mu := by
  have hunit : IsUnit mu.det := isUnit_det_of_posDef hmu
  have hnorm := norm_mul_le mu mu⁻¹
  rw [Matrix.mul_nonsing_inv mu hunit, norm_one,
    ← specBound_eq_norm hmu.posSemidef,
    ← specBound_eq_norm hmu.inv.posSemidef] at hnorm
  have hsqrt := Real.sqrt_le_sqrt hnorm
  simpa only [witnessEccentricity, Real.sqrt_one] using hsqrt

/-- The geometric series factor is at least one for the source exponent
range. -/
theorem one_le_zetaG {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    1 ≤ zetaG g := by
  have hexp : -(1 - g) < 0 := by linarith only [hg.2]
  have hpowpos : (0 : ℝ) < (3 : ℝ) ^ (-(1 - g)) := by positivity
  have hpowlt : (3 : ℝ) ^ (-(1 - g)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
  rw [zetaG]
  exact (one_le_inv₀ (sub_pos.mpr hpowlt)).2 (by linarith only [hpowpos])

/-- The exact boundary-constant lower bound in the initialization anchor. -/
theorem one_le_boundaryConst [Nonempty (Fin d)] {Cd g : ℝ}
    (hCd : 1 ≤ Cd) (hg : g ∈ Set.Ico (0 : ℝ) 1) {mu : Mat d}
    (hmu : mu.PosDef) :
    1 ≤ boundaryConst Cd g mu := by
  rw [boundaryConst]
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hCd (one_le_witnessEccentricity hmu))
    (one_le_zetaG hg)

end

end Initialization
end HighContrast
end HCPolySupport
