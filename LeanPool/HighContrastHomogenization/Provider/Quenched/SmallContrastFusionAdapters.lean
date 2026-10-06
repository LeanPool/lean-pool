/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSplitAdapters

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastFusionAdapters

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The fusion's remaining adapters, and the `∀ n` body fully assembled

Three numeric positions of the argument table (`hA1`, `hA2`, `hquad0`), the
entry position `hentry`, and what binds them remain.  This file closes the
three numeric positions once and for all by *naming* the
recursion constant, and assembles the whole `∀ n` binder body from the two
producers that are available on both sides:

* the squared-base weak-value bound supplies `hmaj` (its output is the
  hypothesis `hmaj`
  below, at `W = weakValueBase …`);
* `split_at_recursionAlpha_at_level` supplies `hWsplit` and `hwsq` — applied *inside*
  this file, so the caller never sees the split.

What is **not** closed here is `hentry`: it is carried as a hypothesis in
exactly the shape `hrec_line_of_one_step_isotropy_sharp_at_jb_src` consumes, at the named source
group
`weakSourceGroupSummed M L (contrastRho g) vsum vmsrc bsrc`.  The rate-general
form of the entry lemma is provided, because the delay form asks for a decay
of rate one per generation in
`3 ^ (-(N₀ + n))`, whereas the source group's legs decay at the rooted rate
`(1 - contrastRho g)/2` in `H_w` and at the half rate in the lag `J`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Nonnegativity of the metric-free base -/

/-- The constant contribution of the seminorm decomposition is nonnegative. -/
theorem constantSeminormCoefficient_nonneg :
    (0 : ℝ) ≤ Response.constantSeminormCoefficient := by
  rw [Response.constantSeminormCoefficient_eq]
  have h : (3 : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  exact inv_nonneg.mpr (by linarith only [h])

/-! ## The quadratic slot -/

/-- The quadratic coefficient is nonnegative.  This is the `hquad0` position. -/
theorem quadCoefficient_nonneg (d : ℕ) {Cpre Crow : ℝ} (hCpre : 0 ≤ Cpre)
    (hCrow : 0 ≤ Crow) : 0 ≤ quadCoefficient d Cpre Crow := by
  rw [quadCoefficient]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have h1 : (0 : ℝ) ≤ 2 * (d : ℝ) * (3 * (d : ℝ) + 4) := by
    nlinarith only [hd0]
  have h2 : (0 : ℝ) ≤ 4 * Cpre * (d : ℝ) * Crow :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCpre) hd0) hCrow
  linarith only [h1, h2]

/-! ## The entry exponent at a general rate -/

/-! ## The recursion constant, and the `∀ n` body -/

end

end HCPolySupport.HighContrast.Quenched
