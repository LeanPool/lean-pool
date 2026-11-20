/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlaneUnitDiskFibreDerivativeSource
public import LeanPool.FastDynamo.Analysis.WholePlaneSliceProductRule

/-!
# One-sided `C¹` branches and fibre-generic unit-disk sources

`Analysis/WholePlaneUnitDiskFibreDerivativeSource.lean` reduces the whole-plane weak-derivative
identity with a unit-circle source to eight almost-everywhere slice hypotheses.  This module
discharges all of them from *pointwise* data: a field that is `C¹` on the whole plane on the
inside, `C¹` off the origin on the outside, whose branchwise `j`-th partial derivative is the
prescribed bulk field, and whose Schwartz-weighted exterior branch decays along every coordinate
slice.

That is exactly the analytic shape in which the discontinuous Ponomarenko mode of
`lem:jump-horizontal-mode` (the interface terms leading to `eq:transmission-horizontal`, and
the eigenfunction at the end of the proof) presents itself: the pivot field
`D_j = ∂_j b + b_j V⁰_⊥` is smooth inside the closed unit disk and on the punctured exterior,
and jumps across `r = 1`.

Also collected here is the elementary slice geometry of the unit-disk chords: the endpoints are
never on the polar axis, points beyond them lie strictly outside the closed disk, and the inner
slice coordinate map is continuous.  None of it depends on the fibre.
-/

@[expose] public section

namespace FastDynamo

namespace WholePlaneFibreSource

noncomputable section

open Filter MeasureTheory Set Topology
open scoped LineDeriv SchwartzMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [CompleteSpace F]

/-! ## Slice geometry of the unit-disk chords -/

/-- A slice point is nonzero as soon as its selected coordinate is nonzero, since that
coordinate is recovered from the point. -/
theorem sliceEquiv_ne_zero_of_inner_ne_zero (j : Fin 2) (x t : ℝ) (ht : t ≠ 0) :
    wholePlaneSliceEquiv j (x, t) ≠ 0 := by
  intro hzero
  have hcoord := congrArg (fun y : WholePlane ↦ y j) hzero
  apply ht
  simpa using hcoord

/-- A point of norm greater than one is nonzero. -/
theorem ne_zero_of_one_lt_norm' {y : WholePlane} (hy : 1 < ‖y‖) : y ≠ 0 := by
  intro hzero
  rw [hzero, norm_zero] at hy
  norm_num at hy

/-- A point of norm greater than one lies outside the closed unit disk. -/
theorem notMem_unitDisk_of_one_lt_norm {y : WholePlane} (hy : 1 < ‖y‖) :
    y ∉ wholePlaneUnitDisk := by
  intro hmem
  have hle : ‖y‖ ≤ 1 := by
    simpa [wholePlaneUnitDisk, Metric.mem_closedBall] using hmem
  exact (not_lt_of_ge hle) hy

/-- The lower slice endpoint `-sqrt(1 - x²)` (or `-1` on exterior fibres) is strictly
negative, so the corresponding slice point never sits on the polar axis. -/
theorem unitDiskSliceLower_neg (x : ℝ) : wholePlaneUnitDiskSliceLower x < 0 := by
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · rw [wholePlaneUnitDiskSliceLower, ite_eq_left hx]
    refine neg_neg_of_pos (Real.sqrt_pos.2 ?_)
    rcases hx with ⟨hxLower, hxUpper⟩
    nlinarith
  · rw [wholePlaneUnitDiskSliceLower, ite_eq_right hx]
    norm_num

/-- The upper slice endpoint `sqrt(1 - x²)` (or `1` on exterior fibres) is strictly
positive. -/
theorem unitDiskSliceUpper_pos (x : ℝ) : 0 < wholePlaneUnitDiskSliceUpper x := by
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · rw [wholePlaneUnitDiskSliceUpper, ite_eq_left hx]
    refine Real.sqrt_pos.2 ?_
    rcases hx with ⟨hxLower, hxUpper⟩
    nlinarith
  · rw [wholePlaneUnitDiskSliceUpper, ite_eq_right hx]
    norm_num

/-- Below the lower slice endpoint the slice point lies strictly outside the closed unit
disk. -/
theorem one_lt_norm_sliceEquiv_of_lt_lower
    (j : Fin 2) (x t : ℝ) (ht : t < wholePlaneUnitDiskSliceLower x) :
    1 < ‖wholePlaneSliceEquiv j (x, t)‖ := by
  have hnormSq := norm_sq_wholePlaneSliceEquiv j x t
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · have ht' : t < -wholePlaneUnitDiskSliceRadius x := by
      simpa [wholePlaneUnitDiskSliceLower, hx] using ht
    have hnonneg : 0 ≤ 1 - x ^ 2 := by
      rcases hx with ⟨hxLower, hxUpper⟩
      nlinarith
    have hradius : (wholePlaneUnitDiskSliceRadius x) ^ 2 = 1 - x ^ 2 := by
      simpa [wholePlaneUnitDiskSliceRadius] using Real.sq_sqrt hnonneg
    have hradiusNonneg : 0 ≤ wholePlaneUnitDiskSliceRadius x := Real.sqrt_nonneg _
    nlinarith [norm_nonneg (wholePlaneSliceEquiv j (x, t)),
      sq_nonneg (t + wholePlaneUnitDiskSliceRadius x)]
  · have ht' : t < -1 := by
      simpa [wholePlaneUnitDiskSliceLower, hx] using ht
    nlinarith [norm_nonneg (wholePlaneSliceEquiv j (x, t)), sq_nonneg x]

/-- Above the upper slice endpoint the slice point lies strictly outside the closed unit
disk. -/
theorem one_lt_norm_sliceEquiv_of_upper_lt
    (j : Fin 2) (x t : ℝ) (ht : wholePlaneUnitDiskSliceUpper x < t) :
    1 < ‖wholePlaneSliceEquiv j (x, t)‖ := by
  have hnormSq := norm_sq_wholePlaneSliceEquiv j x t
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · have ht' : wholePlaneUnitDiskSliceRadius x < t := by
      simpa [wholePlaneUnitDiskSliceUpper, hx] using ht
    have hnonneg : 0 ≤ 1 - x ^ 2 := by
      rcases hx with ⟨hxLower, hxUpper⟩
      nlinarith
    have hradius : (wholePlaneUnitDiskSliceRadius x) ^ 2 = 1 - x ^ 2 := by
      simpa [wholePlaneUnitDiskSliceRadius] using Real.sq_sqrt hnonneg
    have hradiusNonneg : 0 ≤ wholePlaneUnitDiskSliceRadius x := Real.sqrt_nonneg _
    nlinarith [norm_nonneg (wholePlaneSliceEquiv j (x, t)),
      sq_nonneg (t - wholePlaneUnitDiskSliceRadius x)]
  · have ht' : 1 < t := by
      simpa [wholePlaneUnitDiskSliceUpper, hx] using ht
    nlinarith [norm_nonneg (wholePlaneSliceEquiv j (x, t)), sq_nonneg x]

/-- On a fibre whose transverse coordinate has `|x| > 1` the entire slice lies strictly
outside the closed unit disk. -/
theorem one_lt_norm_sliceEquiv_of_transverse_notMem
    (j : Fin 2) {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) (t : ℝ) :
    1 < ‖wholePlaneSliceEquiv j (x, t)‖ := by
  have hnot := wholePlaneSliceEquiv_notMem_unitDisk_of_transverse_notMem j hx t
  refine lt_of_not_ge ?_
  intro hle
  exact hnot (by simpa [wholePlaneUnitDisk, Metric.mem_closedBall] using hle)

/-- The inner slice coordinate map is continuous. -/
theorem continuous_sliceEquiv_inner (j : Fin 2) (x : ℝ) :
    Continuous (fun v : ℝ ↦ wholePlaneSliceEquiv j (x, v)) := by
  have hrepr : (fun v : ℝ ↦ wholePlaneSliceEquiv j (x, v)) =
      fun v : ℝ ↦ wholePlaneSliceEquiv j (x, 0) + v • wholePlaneBasis j := by
    funext v
    exact wholePlaneSliceEquiv_eq_base_add j x v
  rw [hrepr]
  fun_prop

/-! ## The one-sided `C¹` source constructor -/

section Branches

variable [IsScalarTower ℝ ℂ F] [SMulCommClass ℝ ℂ F]

/-- The unit-disk weak-derivative identity for a field that is one-sided `C¹` up to the unit
circle on each side.

`uInterior` is differentiable on the whole plane with differential `Aint`, `uExterior` is
differentiable off the origin with differential `Aext`, and `du` is the branchwise `j`-th
partial derivative: `Aint · e_j` inside the closed disk and `Aext · e_j` outside it.  Together
with square integrability of the glued field and of `du`, and decay of the Schwartz-weighted
exterior branch along every coordinate slice, this yields

`∂_j F = {∂_j F} + [F] n_j δ_{r=1}`

with `[F] n_j` the oriented jump density `unitCircleJumpDensity`.

This is the fibre-generic form of the local analytic step behind `lem:jump-horizontal-mode`
(the singular interface terms leading to `eq:transmission-horizontal`). -/
theorem hasUnitCircleSourceDerivative_of_unitDisk_branches
    (uInterior uExterior du : WholePlane → F)
    (Aint Aext : WholePlane → (WholePlane →L[ℝ] F))
    (f bulk : WholePlaneL2 F) (j : Fin 2)
    (hu : unitDiskPiecewiseField uInterior uExterior =ᵐ[volume] fun y ↦ (f y : F))
    (hdu : du =ᵐ[volume] fun y ↦ (bulk y : F))
    (hIntDeriv : ∀ y : WholePlane, HasFDerivAt uInterior (Aint y) y)
    (hExtDeriv : ∀ y : WholePlane, y ≠ 0 → HasFDerivAt uExterior (Aext y) y)
    (hduInt : ∀ y : WholePlane, ‖y‖ ≤ 1 → du y = Aint y (wholePlaneBasis j))
    (hduExt : ∀ y : WholePlane, 1 < ‖y‖ → du y = Aext y (wholePlaneBasis j))
    (hDecayBot : ∀ (phi : SchwartzMap WholePlane ℂ) (x : ℝ),
      Tendsto (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
        uExterior (wholePlaneSliceEquiv j (x, t))) atBot (nhds 0))
    (hDecayTop : ∀ (phi : SchwartzMap WholePlane ℂ) (x : ℝ),
      Tendsto (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
        uExterior (wholePlaneSliceEquiv j (x, t))) atTop (nhds 0)) :
    HasUnitCircleSourceDerivative f bulk
      (unitCircleJumpDensity uInterior uExterior j) j := by
  have hIntDiff : Differentiable ℝ uInterior := fun y ↦ (hIntDeriv y).differentiableAt
  have hIntCont : Continuous uInterior := hIntDiff.continuous
  have hExtCont : ∀ y : WholePlane, y ≠ 0 → ContinuousAt uExterior y :=
    fun y hy ↦ (hExtDeriv y hy).continuousAt
  have hprodExt : ∀ (phi : SchwartzMap WholePlane ℂ) (x t : ℝ),
      wholePlaneSliceEquiv j (x, t) ≠ 0 →
      HasDerivAt (fun v : ℝ ↦ phi (wholePlaneSliceEquiv j (x, v)) •
          uExterior (wholePlaneSliceEquiv j (x, v)))
        (((∂_{wholePlaneBasis j} phi) (wholePlaneSliceEquiv j (x, t))) •
            uExterior (wholePlaneSliceEquiv j (x, t)) +
          phi (wholePlaneSliceEquiv j (x, t)) •
            Aext (wholePlaneSliceEquiv j (x, t)) (wholePlaneBasis j)) t :=
    fun phi x t ht ↦ hasDerivAt_schwartz_smul_wholePlaneSliceEquiv phi uExterior
      (Aext (wholePlaneSliceEquiv j (x, t))) j x t (hExtDeriv _ ht)
  have hprodInt : ∀ (phi : SchwartzMap WholePlane ℂ) (x t : ℝ),
      HasDerivAt (fun v : ℝ ↦ phi (wholePlaneSliceEquiv j (x, v)) •
          uInterior (wholePlaneSliceEquiv j (x, v)))
        (((∂_{wholePlaneBasis j} phi) (wholePlaneSliceEquiv j (x, t))) •
            uInterior (wholePlaneSliceEquiv j (x, t)) +
          phi (wholePlaneSliceEquiv j (x, t)) •
            Aint (wholePlaneSliceEquiv j (x, t)) (wholePlaneBasis j)) t :=
    fun phi x t ↦ hasDerivAt_schwartz_smul_wholePlaneSliceEquiv phi uInterior
      (Aint (wholePlaneSliceEquiv j (x, t))) j x t (hIntDeriv _)
  apply hasUnitCircleSourceDerivative_of_unitDisk_slices_ae
    uInterior uExterior du f bulk _ j hu hdu
  · intro phi
    filter_upwards [] with x
    exact (hprodExt phi x (wholePlaneUnitDiskSliceLower x)
      (sliceEquiv_ne_zero_of_inner_ne_zero j x _
        (ne_of_lt (unitDiskSliceLower_neg x)))).continuousAt.continuousWithinAt
  · intro phi
    filter_upwards [] with x t ht
    have hnorm := one_lt_norm_sliceEquiv_of_lt_lower j x t ht
    rw [unitDiskPiecewiseField_of_notMem _ _ (notMem_unitDisk_of_one_lt_norm hnorm),
      hduExt _ hnorm]
    exact hprodExt phi x t (ne_zero_of_one_lt_norm' hnorm)
  · intro phi
    filter_upwards [ae_mem_unitDiskSliceInterior_or_transverse_notMem] with x hx
    rcases hx with hxInterior | hxExterior
    · have hcont : Continuous (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
          uInterior (wholePlaneSliceEquiv j (x, t))) :=
        (phi.continuous.comp (continuous_sliceEquiv_inner j x)).smul
          (hIntCont.comp (continuous_sliceEquiv_inner j x))
      refine hcont.continuousOn.congr fun t ht ↦ ?_
      rw [unitDiskPiecewiseField_slice_of_interior _ _ j hxInterior ht]
    · have hcont : Continuous (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
          uExterior (wholePlaneSliceEquiv j (x, t))) := by
        rw [continuous_iff_continuousAt]
        intro t
        exact (hprodExt phi x t (ne_zero_of_one_lt_norm'
          (one_lt_norm_sliceEquiv_of_transverse_notMem j hxExterior t))).continuousAt
      refine hcont.continuousOn.congr fun t _ ↦ ?_
      rw [unitDiskPiecewiseField_slice_of_strictExterior _ _ j hxExterior t]
  · intro phi
    filter_upwards [ae_mem_unitDiskSliceInterior_or_transverse_notMem] with x hx t ht
    rcases hx with hxInterior | hxExterior
    · have hmem := wholePlaneSliceEquiv_mem_unitDisk_of_mem_endpointInterval
        j hxInterior ⟨ht.1.le, ht.2.le⟩
      have hnormLe : ‖wholePlaneSliceEquiv j (x, t)‖ ≤ 1 := by
        simpa [wholePlaneUnitDisk, Metric.mem_closedBall] using hmem
      have hnormOpen :=
        norm_wholePlaneSliceEquiv_lt_one_of_mem_open_endpointInterval j hxInterior ht
      have hevent : ∀ᶠ v in nhds t, ‖wholePlaneSliceEquiv j (x, v)‖ < 1 :=
        (isOpen_lt (continuous_norm.comp (continuous_sliceEquiv_inner j x))
          continuous_const).mem_nhds hnormOpen
      have heq : (fun v : ℝ ↦ phi (wholePlaneSliceEquiv j (x, v)) •
            unitDiskPiecewiseField uInterior uExterior
              (wholePlaneSliceEquiv j (x, v))) =ᶠ[nhds t]
          fun v : ℝ ↦ phi (wholePlaneSliceEquiv j (x, v)) •
            uInterior (wholePlaneSliceEquiv j (x, v)) := by
        filter_upwards [hevent] with v hv
        rw [unitDiskPiecewiseField_of_mem]
        simpa [wholePlaneUnitDisk, Metric.mem_closedBall] using hv.le
      rw [unitDiskPiecewiseField_of_mem _ _ hmem, hduInt _ hnormLe]
      exact (hprodInt phi x t).congr_of_eventuallyEq heq
    · have hnorm := one_lt_norm_sliceEquiv_of_transverse_notMem j hxExterior t
      have heq : (fun v : ℝ ↦ phi (wholePlaneSliceEquiv j (x, v)) •
            unitDiskPiecewiseField uInterior uExterior
              (wholePlaneSliceEquiv j (x, v))) =ᶠ[nhds t]
          fun v : ℝ ↦ phi (wholePlaneSliceEquiv j (x, v)) •
            uExterior (wholePlaneSliceEquiv j (x, v)) := by
        filter_upwards [] with v
        rw [unitDiskPiecewiseField_slice_of_strictExterior _ _ j hxExterior v]
      rw [unitDiskPiecewiseField_of_notMem _ _ (notMem_unitDisk_of_one_lt_norm hnorm),
        hduExt _ hnorm]
      exact (hprodExt phi x t (ne_zero_of_one_lt_norm' hnorm)).congr_of_eventuallyEq heq
  · intro phi
    filter_upwards [] with x
    exact (hprodExt phi x (wholePlaneUnitDiskSliceUpper x)
      (sliceEquiv_ne_zero_of_inner_ne_zero j x _
        (ne_of_gt (unitDiskSliceUpper_pos x)))).continuousAt.continuousWithinAt
  · intro phi
    filter_upwards [] with x t ht
    have hnorm := one_lt_norm_sliceEquiv_of_upper_lt j x t ht
    rw [unitDiskPiecewiseField_of_notMem _ _ (notMem_unitDisk_of_one_lt_norm hnorm),
      hduExt _ hnorm]
    exact hprodExt phi x t (ne_zero_of_one_lt_norm' hnorm)
  · intro phi
    filter_upwards [] with x
    exact hDecayBot phi x
  · intro phi
    filter_upwards [] with x
    exact hDecayTop phi x
  · intro phi
    exact integral_unitDiskBoundaryTwoJumpValue_eq_unitCircleSurfaceValue j hIntCont
      hExtCont phi

end Branches

end

end WholePlaneFibreSource

end FastDynamo
