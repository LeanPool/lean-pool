/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Sobolev.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar


/-!
# Dilations of a function on `ℝ^d`

Scaling `x ↦ f (r • x)` multiplies the `Lᵖ` seminorm by `|r|^{-d/p}` and each partial derivative
by `r`, and it shrinks the support by `|r|⁻¹`. These are the three identities the sharpness of the
Sobolev embedding turns on: the exponent `p⋆` is the one at which the two factors cancel, so a
dilated family keeps its `L^{p⋆}` norm while its `L²` norm tends to zero.

## Main declarations

* `EllipticPdes.Analysis.eLpNorm_comp_smul`: the `Lᵖ` seminorm of a dilate.
* `EllipticPdes.Analysis.partialD_comp_smul`: the partial derivatives of a dilate.
* `EllipticPdes.Analysis.tsupport_comp_smul_subset`: the support of a dilate.

## References

Y. Guo, *Partial Differential Equations*, Example IV.2.11.
-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace EllipticPdes.Analysis

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- **`Lᵖ` seminorm of a dilate.** Scaling the argument by `r` multiplies the seminorm by
`|r^d|^{-1/p}`. -/
theorem eLpNorm_comp_smul {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    {r : ℝ} (hr : r ≠ 0) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    eLpNorm (fun x => f (r • x)) p volume
      = ENNReal.ofReal |(r ^ d)⁻¹| ^ (1 / p.toReal) * eLpNorm f p volume := by
  have hmeas : Measurable fun y : EuclideanSpace ℝ (Fin d) => ‖f y‖ₑ ^ p.toReal :=
    (hf.enorm.pow_const _)
  have hfr : AEStronglyMeasurable (fun x => f (r • x)) volume := by
    simpa only [Function.comp_def] using
      (hf.comp (measurable_const_smul r)).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hfr,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf.aestronglyMeasurable,
    show (∫⁻ x, ‖f (r • x)‖ₑ ^ p.toReal ∂(volume : Measure (EuclideanSpace ℝ (Fin d))))
        = ∫⁻ y, ‖f y‖ₑ ^ p.toReal ∂(Measure.map (r • ·) volume) from
      (lintegral_map hmeas (measurable_const_smul r)).symm,
    MeasureTheory.Measure.map_addHaar_smul volume hr, lintegral_smul_measure, smul_eq_mul,
    finrank_euclideanSpace_fin, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]

/-- **Partial derivatives of a dilate.** -/
theorem partialD_comp_smul {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Differentiable ℝ f)
    (r : ℝ) (i : Fin d) :
    partialD i (fun x => f (r • x)) = fun x => r * partialD i f (r • x) := by
  funext x
  have hL : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin d) => r • x)
      (r • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))) x :=
    (hasFDerivAt_id x).const_smul r
  have hcomp : HasFDerivAt (fun x => f (r • x))
      ((fderiv ℝ f (r • x)).comp (r • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))))) x :=
    (hf (r • x)).hasFDerivAt.comp x hL
  simp only [partialD, hcomp.fderiv, ContinuousLinearMap.coe_comp, Function.comp_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq,
    map_smul, smul_eq_mul]

/-- **Support of a dilate.** For `1 ≤ r`, a function supported in the unit ball dilates to one
supported in the ball of radius `r⁻¹`. -/
theorem tsupport_comp_smul_subset {f : EuclideanSpace ℝ (Fin d) → ℝ} {r : ℝ} (hr : 0 < r)
    (hf : tsupport f ⊆ closedBall 0 1) :
    tsupport (fun x => f (r • x)) ⊆ closedBall 0 r⁻¹ := by
  refine closure_minimal (fun x hx => ?_) isClosed_closedBall
  have hx' : r • x ∈ tsupport f := subset_tsupport _ hx
  have := hf hx'
  rw [mem_closedBall, dist_zero_right] at this ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr] at this
  have h2 : ‖x‖ ≤ 1 / r := by
    rw [le_div_iff₀ hr]
    nlinarith [norm_nonneg x]
  simpa [one_div] using h2

end EllipticPdes.Analysis
