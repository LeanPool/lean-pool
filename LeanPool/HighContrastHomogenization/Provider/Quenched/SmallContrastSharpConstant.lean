/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSharpDrop
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFusionIsotropy

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSharpConstant

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The isotropy recursion constant without geometric slack

The drop branch of the isotropic fusion recursion constant is

```
dropCoefficient d Cpre eta * (((3 ^ (-recursionAlpha g)) ^ H)⁻¹ * (1 - 3 ^ (-recursionAlpha g))⁻¹)
  + 3 * weakCoefficient d Cpre * weakDropConstant …
```

The factor `(1 - r)⁻¹` produces the lower bound `A ≳ 1 / alpha`.
The definition `fusionRecursionConstantIsotropySharp` removes this factor from the
same maximum, as permitted by `SmallContrastSharpDrop.hrec_final_sharp`.

The comparison `fusionRecursionConstantIsotropySharp ≤ fusionRecursionConstantIso`
certifies that the replacement is a genuine improvement and never a weakening:
`(1 - r)⁻¹ ≥ 1` for `0 < r < 1`, so every use site that needed the old constant
as an *upper* bound is still served.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- **The sharp isotropy recursion constant.**  The isotropic fusion recursion
constant with the geometric factor `(1 - 3 ^ (-recursionAlpha g))⁻¹` removed
from the
drop branch.  Licensed by `hrec_final_sharp_at_jb_src`, whose `hA1` slot is
`a * (r ^ H)⁻¹ + 3 * cw * cdrop ≤ A`. -/
@[expose]
def fusionRecursionConstantIsotropySharp (d : ℕ) (Cpre eta : ℝ) (H : ℕ) (M L g : ℝ)
    (cRow kap cD delta cVsum cVm : ℝ) : ℝ :=
  max 1 (max
    (dropCoefficient d Cpre eta * ((((3 : ℝ) ^ (-recursionAlpha g)) ^ H)⁻¹) +
      3 * weakCoefficient d Cpre *
        weakDropConstant (d := d) M L (contrastAlpha g) cD delta)
    (quadCoefficient d Cpre (rowCoefficientIsotropy d cRow kap) +
      3 * weakCoefficient d Cpre * weakBaseCoefficientSummed M L cVsum cVm ^ 2))

theorem one_le_fusionRecursionConstantIsotropySharp (d : ℕ) (Cpre eta : ℝ) (H : ℕ)
    (M L g cRow kap cD delta cVsum cVm : ℝ) :
    1 ≤ fusionRecursionConstantIsotropySharp d Cpre eta H M L g cRow kap cD delta
      cVsum cVm := by
  rw [fusionRecursionConstantIsotropySharp]
  exact le_max_left _ _

/-- The one-step ratio lies in `(0,1)` whenever `g < 1`. -/
theorem ratio_mem_Ioo {g : ℝ} (hg1 : g < 1) :
    0 < (3 : ℝ) ^ (-recursionAlpha g) ∧ (3 : ℝ) ^ (-recursionAlpha g) < 1 := by
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by linarith only [recursionAlpha_pos hg1])

end

end HCPolySupport.HighContrast.Quenched
