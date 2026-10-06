/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSharpConstant

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSharpLine

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The per-generation recursion at the sharp constant

The theorem `per_generation_hrec_at_recursionAlpha_sharp_at_jb_src` specializes the
drop-history recursion to the ratio `3 ^ (-recursionAlpha g)`.  Its `hA1`
hypothesis contains
geometric factor

```
a * (((3 ^ (-recursionAlpha g)) ^ H)⁻¹ * (1 - 3 ^ (-recursionAlpha g))⁻¹) + 3 * cw * cdrop ≤ A .
```

The specialization built from `hrec_final_sharp_at_jb_src` instead uses

```
a * ((3 ^ (-recursionAlpha g)) ^ H)⁻¹ + 3 * cw * cdrop ≤ A ,
```

which deletes `(1 - r)⁻¹`.  The constant
`fusionRecursionConstantIsotropySharp` supplies this sharper hypothesis.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- The drop branch of the sharp constant satisfies the sharp `hA1` hypothesis
by `le_max`. -/
theorem hA1_of_fusionRecursionConstantIsotropySharp (d : ℕ) (Cpre eta : ℝ) (H : ℕ)
    (M L g cRow kap cD delta cVsum cVm : ℝ) :
    dropCoefficient d Cpre eta *
        ((((3 : ℝ) ^ (-recursionAlpha g)) ^ H)⁻¹) +
      3 * weakCoefficient d Cpre *
        weakDropConstant (d := d) M L (contrastAlpha g) cD delta ≤
      fusionRecursionConstantIsotropySharp d Cpre eta H M L g cRow kap cD delta
        cVsum cVm := by
  rw [fusionRecursionConstantIsotropySharp]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- The quadratic branch of the sharp constant, for the `hA2` slot. -/
theorem hA2_of_fusionRecursionConstantIsotropySharp (d : ℕ) (Cpre eta : ℝ) (H : ℕ)
    (M L g cRow kap cD delta cVsum cVm : ℝ) :
    quadCoefficient d Cpre (rowCoefficientIsotropy d cRow kap) +
      3 * weakCoefficient d Cpre *
        weakBaseCoefficientSummed M L cVsum cVm ^ 2 ≤
      fusionRecursionConstantIsotropySharp d Cpre eta H M L g cRow kap cD delta
        cVsum cVm := by
  rw [fusionRecursionConstantIsotropySharp]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

end

end HCPolySupport.HighContrast.Quenched
