/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Flow.PlaneFlowRegularity

/-!
# The plane flow is Lipschitz with a constant linear in the time

`FastDynamo/Dynamics/Flow/PlaneFlowRegularity.lean` supplies the chart-side plane flow
`planeTransverseFlow`, the axial shift `planeAxialShift`, their `ℤ²`-periodisations
`planePeriodizedTransverseFlow` / `planePeriodizedAxialShift`, and the complete differential
calculus of all four: they are differentiable at *every* point of the plane, their differentials
are the cell differentials of `Flow/CellFlowMap.lean` inside a buffer disc, and the identity
(respectively zero) outside every buffer disc.

This module converts that pointwise information into the Lipschitz half of
`prop:particle-flow`, `eq:linear-flow-lipschitz`.  The route is the one of the paper's proof and
of `Global/TorusGlobalVelocityRegularity.lean`: a *uniform in the cell index* bound for the
differential, then `lipschitzWith_of_nnNorm_fderiv_le`.  The paper reads the derivative of the
Lipschitz lift almost everywhere; here the flow is differentiable at every point, so no
mean-value theorem on a merely Lipschitz map and no Rademacher is needed.

The named constants are

* `flowLipschitzSlope h P angularSpeed axialSpeed tau`, the uniform bound on the derivative of
  the *displacement*.  It is the sum of the transverse shear `2 |Ω| · radialShearBound h` of
  `eq:omega-shear-bound` and the axial slope
  `parameterizedHelicalFirstDerivativeBound h Ω U + κ · axialGradientScale tau 0` of
  `eq:axial-shear-bound`.  The factor `2` in the transverse term is the
  sup-versus-Euclidean dual loss already carried by `globalVelocityLipschitzBound`
  (`Global/TorusGlobalVelocityLipschitz.lean`); the outer factor `2` of `flowLipschitzBound` is
  the loss of `norm_planeRotateCLM_le`.
* `flowLipschitzBound h P angularSpeed axialSpeed tau t = 2 * (1 + |t| * flowLipschitzSlope …)`,
  the uniform bound on the derivative of the flow itself, of the shape `A * (1 + |t| * B)` with
  `A = 2 ≥ 1`, the shape `flowLipschitzBound_natCast_mul_le` needs for the entropy criterion.
* `flowCL h P angularSpeed axialSpeed tau = 4 * (1 + flowLipschitzSlope …)`, the paper's
  `C_L` of `eq:linear-flow-lipschitz`: `flowLipschitzBound … t + flowLipschitzBound … (-t) ≤
  flowCL … * (1 + |t|)` and `1 ≤ flowCL …`.

The `ℤ²`-periodisation is Lipschitz with **the same** constant that bounds the differential of
the chart-side flow: near every point the periodisation coincides with a single integer
translate of the chart-side map (`UnitBoxPeriodization.eventuallyEq_translate`), so its
differential at `x` is the chart-side differential at `x - chartTranslation x`, and no factor is
paid for the periodisation.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open scoped NNReal Topology

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete
open UnitBoxPeriodization

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## The named constants -/

/-- **The flow's displacement slope.**  The uniform-in-`n` bound on the derivative of the
displacement of the plane flow: the transverse shear `2 |Ω| sup_s s|χ_h'(s)|` of
`eq:omega-shear-bound` plus the axial slope
`|U| ‖χ_h'‖_∞ + η_ax` of `eq:axial-shear-bound`, the latter in the library's form
`parameterizedHelicalFirstDerivativeBound + κ · axialGradientScale tau 0`.

The leading `2` of the transverse term is the sup-versus-Euclidean dual loss already carried by
`globalVelocityLipschitzBound` (`Global/TorusGlobalVelocityLipschitz.lean`): the differential of
the angular profile is a functional on the sup-normed chart, whose dual norm is the `ℓ¹` norm,
while `radialShearBound` is measured in the Euclidean dual norm. -/
def flowLipschitzSlope : ℝ :=
  2 * (|angularSpeed| * radialShearBound h) +
    (parameterizedHelicalFirstDerivativeBound h angularSpeed axialSpeed +
      (axialPlateauLipschitzConstant : ℝ) * P.scaleFamily.axialGradientScale tau 0)

/-- The transverse half of `flowLipschitzSlope` is nonnegative, being a product of absolute
values with a supremum of nonnegative quantities. -/
theorem two_mul_abs_mul_radialShearBound_nonneg :
    0 ≤ 2 * (|angularSpeed| * radialShearBound h) :=
  mul_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) (radialShearBound_nonneg h))

/-- **The displacement slope is nonnegative** for nonnegative axial separation parameters, the
axial gradient scale `a_0 / R_0` being proportional to `tau`. -/
theorem flowLipschitzSlope_nonneg (htau : 0 ≤ tau) :
    0 ≤ flowLipschitzSlope h P angularSpeed axialSpeed tau := by
  have hshear : 0 ≤ 2 * (|angularSpeed| * radialShearBound h) :=
    two_mul_abs_mul_radialShearBound_nonneg h angularSpeed
  have haxial : 0 ≤ parameterizedHelicalFirstDerivativeBound h angularSpeed axialSpeed +
      (axialPlateauLipschitzConstant : ℝ) * P.scaleFamily.axialGradientScale tau 0 :=
    globalVelocityCoordinateDerivativeBound_nonneg h P angularSpeed axialSpeed tau htau
  rw [flowLipschitzSlope]
  linarith

/-- The axial half of the slope is dominated by the slope itself. -/
theorem globalVelocityCoordinateDerivativeBound_le_flowLipschitzSlope :
    parameterizedHelicalFirstDerivativeBound h angularSpeed axialSpeed +
        (axialPlateauLipschitzConstant : ℝ) * P.scaleFamily.axialGradientScale tau 0 ≤
      flowLipschitzSlope h P angularSpeed axialSpeed tau := by
  have hshear : 0 ≤ 2 * (|angularSpeed| * radialShearBound h) :=
    two_mul_abs_mul_radialShearBound_nonneg h angularSpeed
  rw [flowLipschitzSlope]
  linarith

/-- The transverse half of the slope is dominated by the slope itself. -/
theorem two_mul_abs_mul_radialShearBound_le_flowLipschitzSlope (htau : 0 ≤ tau) :
    2 * (|angularSpeed| * radialShearBound h) ≤
      flowLipschitzSlope h P angularSpeed axialSpeed tau := by
  have haxial : 0 ≤ parameterizedHelicalFirstDerivativeBound h angularSpeed axialSpeed +
      (axialPlateauLipschitzConstant : ℝ) * P.scaleFamily.axialGradientScale tau 0 :=
    globalVelocityCoordinateDerivativeBound_nonneg h P angularSpeed axialSpeed tau htau
  rw [flowLipschitzSlope]
  linarith

/-- **The flow's Lipschitz bound at time `t`**, the uniform bound on the operator norm of the
differential of `planeTransverseFlow … t`: the identity contributes `1`, the displacement
`|t| · flowLipschitzSlope`, and the outer factor `2` is the loss of `norm_planeRotateCLM_le`
(`‖R_α‖ ≤ 2` for the sup norm).  This is the `C(1 + |t|)` of the bound `‖DΦ_t‖ ≤ C(1 + |t|)` in
the proof of `prop:particle-flow`. -/
def flowLipschitzBound (t : ℝ) : ℝ :=
  2 * (1 + |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau)

/-- The flow's Lipschitz bound is at least `2`, in particular at least `1`. -/
theorem two_le_flowLipschitzBound (htau : 0 ≤ tau) (t : ℝ) :
    2 ≤ flowLipschitzBound h P angularSpeed axialSpeed tau t := by
  have hslope : 0 ≤ |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau :=
    mul_nonneg (abs_nonneg t) (flowLipschitzSlope_nonneg h P angularSpeed axialSpeed tau htau)
  rw [flowLipschitzBound]
  linarith

/-- The flow's Lipschitz bound is at least `1`. -/
theorem one_le_flowLipschitzBound (htau : 0 ≤ tau) (t : ℝ) :
    1 ≤ flowLipschitzBound h P angularSpeed axialSpeed tau t :=
  le_trans (by norm_num) (two_le_flowLipschitzBound h P angularSpeed axialSpeed tau htau t)

/-- The flow's Lipschitz bound is nonnegative. -/
theorem flowLipschitzBound_nonneg (htau : 0 ≤ tau) (t : ℝ) :
    0 ≤ flowLipschitzBound h P angularSpeed axialSpeed tau t :=
  le_trans (by norm_num) (one_le_flowLipschitzBound h P angularSpeed axialSpeed tau htau t)

/-- **The constant `C_L` of `eq:linear-flow-lipschitz`**: the two-sided bound
`Lip(Φ_t) + Lip(Φ_{-t}) ≤ C_L (1 + |t|)` holds with this value, and `1 ≤ C_L`. -/
def flowCL : ℝ := 4 * (1 + flowLipschitzSlope h P angularSpeed axialSpeed tau)

/-- `1 ≤ C_L`, the normalisation `prop:particle-flow` asks for. -/
theorem one_le_flowCL (htau : 0 ≤ tau) :
    1 ≤ flowCL h P angularSpeed axialSpeed tau := by
  have hslope : 0 ≤ flowLipschitzSlope h P angularSpeed axialSpeed tau :=
    flowLipschitzSlope_nonneg h P angularSpeed axialSpeed tau htau
  rw [flowCL]
  linarith

/-- `0 < C_L`, the strict positivity the entropy criterion consumes. -/
theorem flowCL_pos (htau : 0 ≤ tau) : 0 < flowCL h P angularSpeed axialSpeed tau :=
  lt_of_lt_of_le zero_lt_one (one_le_flowCL h P angularSpeed axialSpeed tau htau)

/-! ## The `ℝ≥0` forms of the two constants

`LipschitzWith` takes an `ℝ≥0` constant, so the Lipschitz statements below are phrased with these
rather than with `Real.toNNReal` of the real ones.  The real forms stay, because they are the
constants of the *norm* bounds `‖fderiv …‖ ≤ flowLipschitzBound … t` and of the real arithmetic
of `flowDerivativeBound`, `flowComplexDerivativeBound`, `flowCL` and `dynamicalCL`, which ends in
the real `C_L` of `MainLagrangianClauses` (`FastDynamo/Dynamics/ParticleFlow.lean`). -/

/-- The displacement slope as an `ℝ≥0`. -/
def flowLipschitzSlopeNN : ℝ≥0 :=
  Real.toNNReal (flowLipschitzSlope h P angularSpeed axialSpeed tau)

/-- Under `0 ≤ tau` the slope is nonnegative, so its `ℝ≥0` form coerces back to it. -/
theorem coe_flowLipschitzSlopeNN (htau : 0 ≤ tau) :
    ((flowLipschitzSlopeNN h P angularSpeed axialSpeed tau : ℝ≥0) : ℝ) =
      flowLipschitzSlope h P angularSpeed axialSpeed tau :=
  Real.coe_toNNReal _ (flowLipschitzSlope_nonneg h P angularSpeed axialSpeed tau htau)

/-- The axial constant `‖t‖ · slope` of the shift, as an `ℝ≥0`, coerces to `|t| · slope`. -/
theorem coe_nnnorm_mul_flowLipschitzSlopeNN (htau : 0 ≤ tau) (t : ℝ) :
    ((‖t‖₊ * flowLipschitzSlopeNN h P angularSpeed axialSpeed tau : ℝ≥0) : ℝ) =
      |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau := by
  rw [NNReal.coe_mul, coe_nnNorm, Real.norm_eq_abs,
    coe_flowLipschitzSlopeNN h P angularSpeed axialSpeed tau htau]

/-- **The flow's Lipschitz bound as an `ℝ≥0`**: `2 (1 + ‖t‖ · slope)`, the constant every
`LipschitzWith` statement about the flow carries. -/
def flowLipschitzBoundNN (t : ℝ) : ℝ≥0 :=
  2 * (1 + ‖t‖₊ * flowLipschitzSlopeNN h P angularSpeed axialSpeed tau)

/-- The `ℝ≥0` bound coerces to `flowLipschitzBound`, which is the form the arithmetic uses. -/
theorem coe_flowLipschitzBoundNN (htau : 0 ≤ tau) (t : ℝ) :
    ((flowLipschitzBoundNN h P angularSpeed axialSpeed tau t : ℝ≥0) : ℝ) =
      flowLipschitzBound h P angularSpeed axialSpeed tau t := by
  rw [flowLipschitzBoundNN, flowLipschitzBound, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one,
    coe_nnnorm_mul_flowLipschitzSlopeNN h P angularSpeed axialSpeed tau htau]
  norm_num

/-! ## The uniform differential bound on the chart-side flow -/

/-- **The differential of the plane flow is uniformly bounded**, with the bound linear in `|t|`
and independent of the cell index.  Inside a buffer disc the differential is the cell
differential of `Flow/CellFlowMap.lean`, whose norm `norm_fderiv_cellTransverseFlow_le` bounds
by `2 (1 + |t| · 2 |Ω| · radialShearBound h)`; outside every buffer disc it is the identity, of
sup-operator norm at most `1`.  This is the display `‖DΦ_t‖ ≤ C(1 + |t|)` of the proof of
`prop:particle-flow`, uniform in `n` exactly because `eq:omega-shear-bound` is scale invariant. -/
theorem norm_fderiv_planeTransverseFlow_le (htau : 0 ≤ tau) (t : ℝ) (x : ℝ × ℝ) :
    ‖fderiv ℝ (planeTransverseFlow h P angularSpeed t) x‖ ≤
      flowLipschitzBound h P angularSpeed axialSpeed tau t := by
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [fderiv_planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed t hn,
      flowLipschitzBound]
    refine (norm_fderiv_cellTransverseFlow_le h P angularSpeed n t x).trans ?_
    have hstep : |t| * (2 * (|angularSpeed| * radialShearBound h)) ≤
        |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau :=
      mul_le_mul_of_nonneg_left
        (two_mul_abs_mul_radialShearBound_le_flowLipschitzSlope h P angularSpeed axialSpeed tau
          htau)
        (abs_nonneg t)
    linarith
  · push Not at hbuffer
    rw [fderiv_planeTransverseFlow_eq_id_of_outside_buffers h P angularSpeed t hbuffer]
    exact ContinuousLinearMap.norm_id_le.trans
      (one_le_flowLipschitzBound h P angularSpeed axialSpeed tau htau t)

/-- **The differential of the axial shift is uniformly bounded** by `|t| · flowLipschitzSlope`.
Inside a buffer disc it is `t` times the differential of the axial profile, bounded by
`norm_fderiv_cellAxialDisplacement_le`; outside every buffer disc it vanishes. -/
theorem norm_fderiv_planeAxialShift_le (htau : 0 ≤ tau) (t : ℝ) (x : ℝ × ℝ) :
    ‖fderiv ℝ (planeAxialShift h P axialSpeed tau t) x‖ ≤
      |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau := by
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [fderiv_planeAxialShift_eq_cell_of_mem_bufferDisk h P axialSpeed tau t hn]
    refine (norm_fderiv_cellAxialDisplacement_le h P angularSpeed axialSpeed tau htau n t x).trans
      ?_
    exact mul_le_mul_of_nonneg_left
      (globalVelocityCoordinateDerivativeBound_le_flowLipschitzSlope h P angularSpeed axialSpeed
        tau)
      (abs_nonneg t)
  · push Not at hbuffer
    rw [fderiv_planeAxialShift_eq_zero_of_outside_buffers h P axialSpeed tau t hbuffer, norm_zero]
    exact mul_nonneg (abs_nonneg t)
      (flowLipschitzSlope_nonneg h P angularSpeed axialSpeed tau htau)

/-! ## The differential of the periodised flow -/

/-- **Near every point the periodised displacement is a single integer translate of the
chart-side one** — not merely at the point, but on a whole neighbourhood.  This is what lets the
chart-side derivative bound pass to the periodisation with no loss. -/
theorem planePeriodizedTransverseDisplacement_eventuallyEq (t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTransverseDisplacement h P angularSpeed t =ᶠ[𝓝 x]
      fun y ↦ planeTransverseDisplacement h P angularSpeed t (y - chartTranslation x) :=
  eventuallyEq_translate
    (supportedInPlacementChart_planeTransverseDisplacement h P angularSpeed t) x

/-- Near every point the periodised axial shift is a single integer translate of the chart-side
one. -/
theorem planePeriodizedAxialShift_eventuallyEq (t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedAxialShift h P axialSpeed tau t =ᶠ[𝓝 x]
      fun y ↦ planeAxialShift h P axialSpeed tau t (y - chartTranslation x) :=
  eventuallyEq_translate (supportedInPlacementChart_planeAxialShift h P axialSpeed tau t) x

/-- Near every point the periodised flow is the chart-side flow of the recentred point,
translated back. -/
theorem planePeriodizedTransverseFlow_eventuallyEq (t : ℝ) (x : ℝ × ℝ) :
    planePeriodizedTransverseFlow h P angularSpeed t =ᶠ[𝓝 x]
      fun y ↦ planeTransverseFlow h P angularSpeed t (y - chartTranslation x) +
        chartTranslation x := by
  filter_upwards [planePeriodizedTransverseDisplacement_eventuallyEq h P angularSpeed t x]
    with y hy
  rw [planePeriodizedTransverseFlow, hy, planeTransverseFlow_eq_add_displacement]
  abel

/-- **The differential of the periodised flow at `x` is the chart-side differential at the
recentred point.**  Translation has the identity differential, so the recentring costs nothing. -/
theorem hasFDerivAt_planePeriodizedTransverseFlow (t : ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (planePeriodizedTransverseFlow h P angularSpeed t)
      (fderiv ℝ (planeTransverseFlow h P angularSpeed t) (x - chartTranslation x)) x := by
  refine (planePeriodizedTransverseFlow_eventuallyEq h P angularSpeed t x).hasFDerivAt_iff.2 ?_
  have hsub : HasFDerivAt (fun y : ℝ × ℝ ↦ y - chartTranslation x)
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x := (hasFDerivAt_id x).sub_const _
  have hcomp :=
    ((differentiable_planeTransverseFlow h P angularSpeed t
      (x - chartTranslation x)).hasFDerivAt).comp x hsub
  have hadd := hcomp.add_const (chartTranslation x)
  rwa [ContinuousLinearMap.comp_id] at hadd

/-- The differential of the periodised axial shift at `x` is the chart-side differential at the
recentred point. -/
theorem hasFDerivAt_planePeriodizedAxialShift (t : ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (planePeriodizedAxialShift h P axialSpeed tau t)
      (fderiv ℝ (planeAxialShift h P axialSpeed tau t) (x - chartTranslation x)) x := by
  refine (planePeriodizedAxialShift_eventuallyEq h P axialSpeed tau t x).hasFDerivAt_iff.2 ?_
  have hsub : HasFDerivAt (fun y : ℝ × ℝ ↦ y - chartTranslation x)
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x := (hasFDerivAt_id x).sub_const _
  have hcomp :=
    ((differentiable_planeAxialShift h P axialSpeed tau t
      (x - chartTranslation x)).hasFDerivAt).comp x hsub
  rwa [ContinuousLinearMap.comp_id] at hcomp

/-- The periodised flow is differentiable at every point of the plane. -/
theorem differentiable_planePeriodizedTransverseFlow (t : ℝ) :
    Differentiable ℝ (planePeriodizedTransverseFlow h P angularSpeed t) := fun x =>
  (hasFDerivAt_planePeriodizedTransverseFlow h P angularSpeed t x).differentiableAt

/-- The periodised axial shift is differentiable at every point of the plane. -/
theorem differentiable_planePeriodizedAxialShift (t : ℝ) :
    Differentiable ℝ (planePeriodizedAxialShift h P axialSpeed tau t) := fun x =>
  (hasFDerivAt_planePeriodizedAxialShift h P axialSpeed tau t x).differentiableAt

/-- The differential of the periodised flow, read off the chart-side one. -/
theorem fderiv_planePeriodizedTransverseFlow (t : ℝ) (x : ℝ × ℝ) :
    fderiv ℝ (planePeriodizedTransverseFlow h P angularSpeed t) x =
      fderiv ℝ (planeTransverseFlow h P angularSpeed t) (x - chartTranslation x) :=
  (hasFDerivAt_planePeriodizedTransverseFlow h P angularSpeed t x).fderiv

/-- The differential of the periodised axial shift, read off the chart-side one. -/
theorem fderiv_planePeriodizedAxialShift (t : ℝ) (x : ℝ × ℝ) :
    fderiv ℝ (planePeriodizedAxialShift h P axialSpeed tau t) x =
      fderiv ℝ (planeAxialShift h P axialSpeed tau t) (x - chartTranslation x) :=
  (hasFDerivAt_planePeriodizedAxialShift h P axialSpeed tau t x).fderiv

/-- **The periodised flow obeys the chart-side derivative bound**, with no extra factor: the
periodisation is locally a single translate. -/
theorem norm_fderiv_planePeriodizedTransverseFlow_le (htau : 0 ≤ tau) (t : ℝ) (x : ℝ × ℝ) :
    ‖fderiv ℝ (planePeriodizedTransverseFlow h P angularSpeed t) x‖ ≤
      flowLipschitzBound h P angularSpeed axialSpeed tau t := by
  rw [fderiv_planePeriodizedTransverseFlow]
  exact norm_fderiv_planeTransverseFlow_le h P angularSpeed axialSpeed tau htau t _

/-- The periodised axial shift obeys the chart-side derivative bound. -/
theorem norm_fderiv_planePeriodizedAxialShift_le (htau : 0 ≤ tau) (t : ℝ) (x : ℝ × ℝ) :
    ‖fderiv ℝ (planePeriodizedAxialShift h P axialSpeed tau t) x‖ ≤
      |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau := by
  rw [fderiv_planePeriodizedAxialShift]
  exact norm_fderiv_planeAxialShift_le h P angularSpeed axialSpeed tau htau t _

/-! ## The Lipschitz estimates -/

/-- **Periodised.**  The `ℤ²`-equivariant flow — the one that descends to the
transverse two-torus — is Lipschitz with **the same** constant `flowLipschitzBound … t` that
bounds the differential of the chart-side flow.  The generic
periodisation factor `2` of `UnitBoxPeriodization.lipschitzWith_periodization` is not paid: the
displacement vanishes near every translate boundary, so the periodisation is locally a single
translate and its differential obeys the chart-side bound pointwise. -/
theorem lipschitzWith_planePeriodizedTransverseFlow (htau : 0 ≤ tau) (t : ℝ) :
    LipschitzWith (flowLipschitzBoundNN h P angularSpeed axialSpeed tau t)
      (planePeriodizedTransverseFlow h P angularSpeed t) := by
  refine lipschitzWith_of_nnNorm_fderiv_le
    (differentiable_planePeriodizedTransverseFlow h P angularSpeed t) fun x => ?_
  rw [← NNReal.coe_le_coe, coe_nnNorm,
    coe_flowLipschitzBoundNN h P angularSpeed axialSpeed tau htau]
  exact norm_fderiv_planePeriodizedTransverseFlow_le h P angularSpeed axialSpeed tau htau t x

/-- **Periodised, axial component.**  The `ℤ²`-periodic axial shift is Lipschitz with the
chart-side constant `|t| · slope`. -/
theorem lipschitzWith_planePeriodizedAxialShift (htau : 0 ≤ tau) (t : ℝ) :
    LipschitzWith (‖t‖₊ * flowLipschitzSlopeNN h P angularSpeed axialSpeed tau)
      (planePeriodizedAxialShift h P axialSpeed tau t) := by
  refine lipschitzWith_of_nnNorm_fderiv_le
    (differentiable_planePeriodizedAxialShift h P axialSpeed tau t) fun x => ?_
  rw [← NNReal.coe_le_coe, coe_nnNorm,
    coe_nnnorm_mul_flowLipschitzSlopeNN h P angularSpeed axialSpeed tau htau]
  exact norm_fderiv_planePeriodizedAxialShift_le h P angularSpeed axialSpeed tau htau t x

/-! ## Lipschitz dependence on the time -/

/-- **The periodised flow is Lipschitz in the time**, uniformly in the point, with the chart-side
speed bound `dist_planeTransverseFlow_le`.  Both sides are the chart-side flow of the same
recentred point, translated by the same vector, and translation is an isometry. -/
theorem dist_planePeriodizedTransverseFlow_le (s t : ℝ) (x : ℝ × ℝ) :
    dist (planePeriodizedTransverseFlow h P angularSpeed t x)
        (planePeriodizedTransverseFlow h P angularSpeed s x) ≤
      planeTransverseSpeedBound h P angularSpeed * |t - s| := by
  rw [planePeriodizedTransverseFlow_eq, planePeriodizedTransverseFlow_eq, dist_add_right]
  exact dist_planeTransverseFlow_le h P angularSpeed s t (x - chartTranslation x)

/-- The periodised axial shift is Lipschitz in the time, uniformly in the point. -/
theorem abs_planePeriodizedAxialShift_sub_le (s t : ℝ) (x : ℝ × ℝ) :
    |planePeriodizedAxialShift h P axialSpeed tau t x -
        planePeriodizedAxialShift h P axialSpeed tau s x| ≤
      planeAxialSpeedBound h P axialSpeed tau * |t - s| := by
  rw [planePeriodizedAxialShift_eq, planePeriodizedAxialShift_eq]
  exact abs_planeAxialShift_sub_le h P axialSpeed tau s t (x - chartTranslation x)

/-! ## Growth of the bound along the iterates, and the two-sided estimate -/

/-- **The iterate bound.**  Since `(Φ_t)^[m] = Φ_{m t}`, the entropy criterion needs the constant
at time `m t` to grow at most linearly in `m`; it does, with the `m`-independent factor
`2 · max 1 (|t| · slope)`.  Consumed by `lipschitzWith_literalFlow_iterate`
(`Flow/Entropy.lean`), the hypothesis of `coverEntropy_eq_zero_of_lipschitz_iterate`. -/
theorem flowLipschitzBound_natCast_mul_le (t : ℝ) (m : ℕ) :
    flowLipschitzBound h P angularSpeed axialSpeed tau ((m : ℝ) * t) ≤
      2 * max 1 (|t| * flowLipschitzSlope h P angularSpeed axialSpeed tau) * (1 + m) := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hM1 : (1 : ℝ) ≤ max 1 (|t| * flowLipschitzSlope h P angularSpeed axialSpeed tau) :=
    le_max_left _ _
  have hM2 : |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau ≤
      max 1 (|t| * flowLipschitzSlope h P angularSpeed axialSpeed tau) := le_max_right _ _
  have hkey : 0 ≤ (m : ℝ) *
      (max 1 (|t| * flowLipschitzSlope h P angularSpeed axialSpeed tau) -
        |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau) :=
    mul_nonneg hm (by linarith)
  have habs : |(m : ℝ) * t| = (m : ℝ) * |t| := by
    rw [abs_mul, abs_of_nonneg hm]
  rw [flowLipschitzBound, habs]
  nlinarith [hkey, hM1]

/-- **The two-sided estimate `eq:linear-flow-lipschitz`**, in the form the main
theorem consumes: the Lipschitz bounds of `Φ_t` and of `Φ_t^{-1} = Φ_{-t}` add up to at most
`C_L (1 + |t|)` with `C_L = flowCL`. -/
theorem flowLipschitzBound_add_neg_le (htau : 0 ≤ tau) (t : ℝ) :
    flowLipschitzBound h P angularSpeed axialSpeed tau t +
        flowLipschitzBound h P angularSpeed axialSpeed tau (-t) ≤
      flowCL h P angularSpeed axialSpeed tau * (1 + |t|) := by
  have hslope : 0 ≤ flowLipschitzSlope h P angularSpeed axialSpeed tau :=
    flowLipschitzSlope_nonneg h P angularSpeed axialSpeed tau htau
  have habs : |(-t)| = |t| := abs_neg t
  rw [flowLipschitzBound, flowLipschitzBound, flowCL, habs]
  nlinarith [abs_nonneg t, hslope]

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
