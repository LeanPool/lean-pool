/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowValueIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFusionAdapters

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastFusionIsotropy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The isotropy one-step chain and recursion constant steps 2 and 3, under the doctrine rule.

The mapping of the fusion chain shows that almost none of it needs a parallel
definition.  `weakDropConstant`, `weakBaseCoefficientSummed`,
`weakSourceGroupSummed`, `split_at_recursionAlpha_at_level`, `iterationDropSum`,
`per_generation_hrec_at_recursionAlpha_sharp_at_jb_src` and the recursion-family
core body are already **abstract** in the metric factor `M`, the load scale `L`
and the
recursion constant `A`; they carry no aspect ratio and are reused unchanged.

`Π` enters the one-step chain at exactly **one** link:
the one-step-to-scalar conversion of
`HCPoly.Provider.Quenched.SmallContrastHrecInstance`, whose `hone`
carries `rowValue2 Cd g mAl G s t kap` and whose conclusion carries
`quadCoefficient d Cpre (rowCoefficient Cd g mAl G s t kap)`.  Its proof is the
row-value equation followed by `one_step_scalar_shape`, which
is itself abstract in the row coefficient.

So the parallel copies needed are exactly three, and they are the ones here:
`one_step_to_scalar_step_isotropy`, `hrec_line_of_one_step_isotropy_sharp_at_jb_src` and
`fusionRecursionConstantIsotropySharp`.  The last differs from
`fusionRecursionConstantIsotropySharp`
only in taking `L` as a parameter instead of fixing
`weakLoadScale Cd g mAl G kap` in its body, and in using `rowCoefficientIsotropy`;
fixing it in the body is precisely what cannot be repaired by an inequality.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The one-step scalar shape at the isotropy row -/

/-- **The parallel copy of the one-step-to-scalar conversion.**  Identical
proof: the
row value is converted to its coefficient by an equation, and
`one_step_scalar_shape` — abstract in the row coefficient — does the rest. -/
theorem one_step_to_scalar_step_isotropy (d : ℕ) {Cpre eta : ℝ}
    {cRow kap wv W hatS hatT : ℝ}
    (hd0 : (0 : ℝ) ≤ (d : ℝ)) (hCpre : 0 ≤ Cpre)
    (hmaj : wv ≤ W ^ 2)
    (hone : hatT - 1 ≤
      4 * Cpre * ((3 / 2 + 1 / (4 * eta)) * (16 * (d : ℝ) * (hatS - hatT)) +
          rowValue2Isotropy d cRow kap ((d : ℝ) * (hatT - 1)) + wv) +
        2 * ((3 * (d : ℝ) + 4) * ((d : ℝ) * (hatT - 1)) ^ 2)) :
    (d : ℝ) * (hatT - 1) ≤
      dropCoefficient d Cpre eta *
          ((d : ℝ) * (hatS - 1) - (d : ℝ) * (hatT - 1)) +
        quadCoefficient d Cpre (rowCoefficientIsotropy d cRow kap) *
          ((d : ℝ) * (hatT - 1)) ^ 2 +
        weakCoefficient d Cpre * W ^ 2 := by
  have hrow := rowValue2Isotropy_eq_coefficient d cRow kap ((d : ℝ) * (hatT - 1))
  rw [hrow] at hone
  have hone' : hatT - 1 ≤
      4 * Cpre * ((3 / 2 + 1 / (4 * eta)) * (16 * (d : ℝ) * (hatS - hatT)) +
          rowCoefficientIsotropy d cRow kap * ((d : ℝ) * (hatT - 1)) ^ 2 +
          W ^ 2) +
        2 * ((3 * (d : ℝ) + 4) * ((d : ℝ) * (hatT - 1)) ^ 2) := by
    have h4 : (0 : ℝ) ≤ 4 * Cpre := by linarith only [hCpre]
    nlinarith only [hone, hmaj, h4]
  exact one_step_scalar_shape d hd0 hone'

/-! ## The recursion line at the isotropy row -/

/-! ## The isotropy recursion constant -/

/-! ## The weak-value base at an abstract load -/

/-! ## The fusion's binder body, `Π`-free -/

end

end HCPolySupport.HighContrast.Quenched
