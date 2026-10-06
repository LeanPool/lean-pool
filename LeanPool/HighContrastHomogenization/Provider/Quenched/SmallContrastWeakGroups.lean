/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdjointMirrors
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAverageDrops
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMetricFactorAccount
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryExponent

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastWeakGroups

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The three-group split of the sharp weak value

`hrec_final_sharp_at_jb_src` consumes the weak base in the shape

  `W ≤ u + v·F(j_b) + w`,   `w² ≤ c_drop · iterationDropSum r F n`,

with `u` the source group, `v·F(j_b)` the base-scale group (which squares into
the recursion's quadratic slot) and `w` the drop group.  This file performs
that split for `weakValueSharpMajorant_le_three_group_summed_at_level`, from per-slot bounds of
exactly the
shape the (repaired) lagged variance supply and the mean-drop carrier produce:

* every variance slot — `V j`, `V0`, `Vmean` — is `≤ vsrc + cV·F(j_b)`;
* every drop slot is `≤ c_D·(F(n-j) - F n)`;
* the bad-event group and the window tail are `≤ bsrc`.

The output constants are explicit; in particular the **source constant**

  `C_src = (32·M·√L·(1-3^{-1/2})⁻¹ + c_const·M·√7)·vsrc + (16·M/(1-ρ))·bsrc`

is named here (`weakSourceGroup`), which is what
the polynomial bootstrap entry needs.

The two drop conversions are read at the *same* rate: the linear slot's weight
is `3^{-1/2}` and the rooted slot's is `3^{-(1/2-ρ/2)} = 3^{-α}`, and
`iterationDropSum` is increasing in its ratio
(`iterationDropSum_mono_r`), so both land on `iterationDropSum (3^{-α}) F n`
whenever `α ≤ 1/2`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The geometric constant of the linear weight `3^{-1/2}`. -/
@[expose]
def halfGeom : ℝ := (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

theorem halfGeom_pos : 0 < halfGeom := by
  rw [halfGeom]
  have hlt : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact inv_pos.mpr (by linarith only [hlt])

/-- The coefficient with which every variance slot enters the weak base. -/
@[expose]
def weakSlotCoefficient (M L : ℝ) : ℝ :=
  32 * M * Real.sqrt L * halfGeom + Response.constantSeminormCoefficient * M * Real.sqrt 7

/-- **The source group** of the weak base: the constant `C_src`. -/
@[expose]
def weakSourceGroup (M L rho vsrc bsrc : ℝ) : ℝ :=
  weakSlotCoefficient M L * vsrc + 16 * M / (2 * ((1 - rho) / 2)) * bsrc

/-- **The drop-group constant** of the weak base. -/
@[expose]
def weakDropConstant (M L alpha cD delta : ℝ) : ℝ :=
  2 * (16 * M * Real.sqrt L) ^ 2 *
    (delta * halfGeom * (cD * halfGeom) +
      (1 - (3 : ℝ) ^ (-alpha))⁻¹ *
        (2 * (d : ℝ) * (cD * (1 - (3 : ℝ) ^ (-alpha))⁻¹)))

/-! ## The split -/

end

end HCPolySupport.HighContrast.Quenched
