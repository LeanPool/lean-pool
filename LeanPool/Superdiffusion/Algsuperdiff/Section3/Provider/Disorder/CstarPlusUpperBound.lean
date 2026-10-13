/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound

/-!
# CstarPlusUpperBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A dimension-only upper bound on `cstarPlus`

The clean Section 3 convention is

```text
cstarPlus M = E[‖j_0(0)‖_F^2] / log 3.
```

The value term of the J2 observable dominates the operator norm of `j_0(0)`.
The Frobenius/operator comparison therefore bounds the origin Frobenius mass by
`d^2 E[X^2]`, where `X` is the J2 observable.  Its normalized Gaussian tail
gives `E[X^2] <= 1 + exp (-1)`.  This module packages the resulting explicit
dimension-only envelope, with a harmless additive `1` so that the envelope is
positive even before imposing the standing model's dimension lower bound.

## Sources and conventions

* ABK26, `e.kn.reg.ass`, ABK26: the J2 observable and its normalized Gaussian
  tail.
* The clean convention divides the origin Frobenius mass by `log 3`; this is the
  already-verified definition `Section3.Disorder.cstarPlus`.

## Main results

* `cstarPlusUpperBound`: an explicit positive function of `d` only.
* `cstarPlus_le_cstarPlusUpperBound`: every standing ABK model obeys that
  bound, using no additional hypothesis.
-/

namespace Algsuperdiff.Section3.Provider.Disorder

open MeasureTheory HCPolySupport
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- A positive dimension-only envelope for the normalized Frobenius origin
mass. -/
def cstarPlusUpperBound (d : ℕ) : ℝ :=
  1 + (d : ℝ) ^ 2 * (1 + Real.exp (-1)) / Real.log 3

/-- The dimension-only envelope is nonnegative. -/
theorem cstarPlusUpperBound_nonneg (d : ℕ) :
    0 ≤ cstarPlusUpperBound d := by
  unfold cstarPlusUpperBound
  refine add_nonneg zero_le_one (div_nonneg ?_ (Real.log_nonneg (by norm_num)))
  exact mul_nonneg (sq_nonneg _) (add_nonneg zero_le_one (Real.exp_pos (-1)).le)

/-- The harmless additive constant makes the envelope strictly positive for
every natural dimension. -/
theorem cstarPlusUpperBound_pos (d : ℕ) :
    0 < cstarPlusUpperBound d := by
  exact lt_of_lt_of_le zero_lt_one
    (le_add_of_nonneg_right
      (div_nonneg
        (mul_nonneg (sq_nonneg _) (add_nonneg zero_le_one (Real.exp_pos (-1)).le))
        (Real.log_nonneg (by norm_num))))

private theorem originFrobeniusIntegrand_le_j2Observable_sq
    (F : ℤ → ShellField d) :
    HCPolySupport.Book.Ch02.matrixFrobeniusNormSq ((F 0) 0) ≤
      (d : ℝ) ^ 2 * ShellField.j2Observable d (F 0) ^ 2 := by
  have hXnonneg : 0 ≤ ShellField.j2Observable d (F 0) :=
    ShellField.j2Observable_nonneg d (F 0)
  have hunit :
      ShellField.unitCubeValueNorm (F 0) ≤ ShellField.j2Observable d (F 0) := by
    calc
      ShellField.unitCubeValueNorm (F 0) ≤
          ShellField.unitCubeValueNorm (F 0) +
            Real.sqrt d * ShellField.unitCubeDerivNorm (F 0) :=
        le_add_of_nonneg_right
          (mul_nonneg (Real.sqrt_nonneg _)
            (ShellField.unitCubeDerivNorm_nonneg (F 0)))
      _ ≤ ShellField.unitCubeValueNorm (F 0) +
            Real.sqrt d * ShellField.unitCubeDerivNorm (F 0) +
            (d : ℝ) * ShellField.unitCubeSecondDerivNorm (F 0) :=
        le_add_of_nonneg_right
          (mul_nonneg (Nat.cast_nonneg d)
            (ShellField.unitCubeSecondDerivNorm_nonneg (F 0)))
      _ = ShellField.j2Observable d (F 0) := rfl
  have hop : HCPolySupport.Book.Ch02.matrixOperatorNorm ((F 0) 0) ≤
      ShellField.j2Observable d (F 0) := by
    calc
      HCPolySupport.Book.Ch02.matrixOperatorNorm ((F 0) 0) ≤
          ShellField.unitCubeValueNorm (F 0) :=
        ShellField.matrixOperatorNorm_zero_le_unitCubeValueNorm (F 0)
      _ ≤ ShellField.j2Observable d (F 0) := hunit
  calc
    HCPolySupport.Book.Ch02.matrixFrobeniusNormSq ((F 0) 0) =
        HCPolySupport.Book.Ch02.matrixFrobeniusNorm ((F 0) 0) ^ 2 := by
      rw [HCPolySupport.Book.Ch02.matrixFrobeniusNorm,
        Real.sq_sqrt
          (HCPolySupport.Book.Ch02.matrixFrobeniusNormSq_nonneg ((F 0) 0))]
    _ ≤ ((d : ℝ) * HCPolySupport.Book.Ch02.matrixOperatorNorm ((F 0) 0)) ^ 2 :=
      (sq_le_sq₀
        (HCPolySupport.Book.Ch02.matrixFrobeniusNorm_nonneg ((F 0) 0))
        (mul_nonneg (Nat.cast_nonneg d)
          (HCPolySupport.Book.Ch02.matrixOperatorNorm_nonneg ((F 0) 0)))).mpr
        (HCPolySupport.Book.Ch02.matrixFrobeniusNorm_le_dim_mul_matrixOperatorNorm
          ((F 0) 0))
    _ = (d : ℝ) ^ 2 *
        HCPolySupport.Book.Ch02.matrixOperatorNorm ((F 0) 0) ^ 2 := by
      ring
    _ ≤ (d : ℝ) ^ 2 * ShellField.j2Observable d (F 0) ^ 2 :=
      mul_le_mul_of_nonneg_left
        ((sq_le_sq₀
          (HCPolySupport.Book.Ch02.matrixOperatorNorm_nonneg ((F 0) 0))
          hXnonneg).mpr hop)
        (sq_nonneg _)

/-- J2 alone bounds the normalized Frobenius constant by the explicit
dimension-only envelope. -/
theorem cstarPlus_le_cstarPlusUpperBound (M : ABKModel d) :
    Algsuperdiff.Section3.Disorder.cstarPlus M ≤ cstarPlusUpperBound d := by
  let X : (ℤ → ShellField d) → ℝ := fun F ↦ ShellField.j2Observable d (F 0)
  have hXmeas : Measurable X :=
    (ShellField.j2Observable_measurable d).comp ShellField.measurable_zeroShellMap
  have hXnonneg : ∀ F, 0 ≤ X F := fun F ↦ ShellField.j2Observable_nonneg d (F 0)
  have hXmem : MemLp X 2 M.P.toMeasure :=
    Algsuperdiff.Probability.memLp_two_of_gaussian_tail
      hXmeas hXnonneg M.J2.gaussian_tail
  have hXsq : Integrable (fun F ↦ X F ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hXmeas.aestronglyMeasurable).mp hXmem
  have hmass : Algsuperdiff.Section3.Disorder.originFrobeniusMass M ≤
      (d : ℝ) ^ 2 * ∫ F, X F ^ 2 ∂M.P.toMeasure := by
    unfold Algsuperdiff.Section3.Disorder.originFrobeniusMass
    calc
      (∫ F, HCPolySupport.Book.Ch02.matrixFrobeniusNormSq ((F 0) 0)
          ∂M.P.toMeasure) ≤
          ∫ F, (d : ℝ) ^ 2 * X F ^ 2 ∂M.P.toMeasure := by
        refine integral_mono
          (Algsuperdiff.Section3.Disorder.integrable_originFrobeniusMass M)
          (hXsq.const_mul ((d : ℝ) ^ 2)) ?_
        exact fun F ↦ originFrobeniusIntegrand_le_j2Observable_sq F
      _ = (d : ℝ) ^ 2 * ∫ F, X F ^ 2 ∂M.P.toMeasure :=
        integral_const_mul ((d : ℝ) ^ 2) (fun F ↦ X F ^ 2)
  have hsecond : (∫ F, X F ^ 2 ∂M.P.toMeasure) ≤ 1 + Real.exp (-1) :=
    integral_sq_le_of_gaussian_tail hXmeas hXnonneg M.J2.gaussian_tail
  have hmassBound : Algsuperdiff.Section3.Disorder.originFrobeniusMass M ≤
      (d : ℝ) ^ 2 * (1 + Real.exp (-1)) :=
    hmass.trans (mul_le_mul_of_nonneg_left hsecond (sq_nonneg _))
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold Algsuperdiff.Section3.Disorder.cstarPlus cstarPlusUpperBound
  calc
    Algsuperdiff.Section3.Disorder.originFrobeniusMass M / Real.log 3 ≤
        ((d : ℝ) ^ 2 * (1 + Real.exp (-1))) / Real.log 3 :=
      div_le_div_of_nonneg_right hmassBound hlog.le
    _ ≤ 1 + ((d : ℝ) ^ 2 * (1 + Real.exp (-1))) / Real.log 3 :=
      le_add_of_nonneg_left zero_le_one

end

end Algsuperdiff.Section3.Provider.Disorder
