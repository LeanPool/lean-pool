/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.FunctionalHessian
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Smoothness of the quantile functional on its open probability box -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ContDiff

namespace EhrhardGaussian.Ehrhard

/-- The standard Gaussian density is smooth. -/
theorem contDiff_gaussianPDFReal : ContDiff ℝ ∞ (gaussianPDFReal 0 1) := by
  change ContDiff ℝ ∞ (fun x : ℝ => gaussianPDFReal 0 1 x)
  simp_rw [gaussianPDFReal_zero_one]
  fun_prop

/-- The standard Gaussian distribution function is smooth. -/
theorem contDiff_gaussianCDF : ContDiff ℝ ∞ gaussianCDF := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_gaussianCDF x).differentiableAt, ?_⟩
  have heq : deriv gaussianCDF = gaussianPDFReal 0 1 :=
    funext fun x => (hasDerivAt_gaussianCDF x).deriv
  rw [heq]
  exact contDiff_gaussianPDFReal

/-- The Gaussian quantile is smooth at every probability strictly between zero and one. -/
theorem contDiffAt_gaussianCDFChart_symm {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ gaussianCDFChart.symm p := by
  apply gaussianCDFChart.contDiffAt_symm_deriv
    (gaussianPDFReal_pos 0 1 _ (by norm_num)).ne'
    (gaussianCDFChart_target.symm ▸ hp)
    (hasDerivAt_gaussianCDF _)
  exact contDiff_gaussianCDF.contDiffAt

/-- The Gaussian quantile is smooth on the open probability interval. -/
theorem contDiffOn_gaussianCDFChart_symm :
    ContDiffOn ℝ ∞ gaussianCDFChart.symm (Ioo (0 : ℝ) 1) :=
  fun _ hp => (contDiffAt_gaussianCDFChart_symm hp).contDiffWithinAt

variable {ι : Type*} [Fintype ι]

/-- Linear combinations of Gaussian quantiles are smooth inside the probability box. -/
theorem contDiffAt_quantileLinear (θ : ι → ℝ) {x : ι → ℝ}
    (hx : x ∈ probabilityBox) : ContDiffAt ℝ ∞ (quantileLinear θ) x := by
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_const.mul ((contDiffAt_gaussianCDFChart_symm (hx i)).comp x
    (by fun_prop : ContDiffAt ℝ ∞ (fun y : ι → ℝ => y i) x))



end EhrhardGaussian.Ehrhard

end
