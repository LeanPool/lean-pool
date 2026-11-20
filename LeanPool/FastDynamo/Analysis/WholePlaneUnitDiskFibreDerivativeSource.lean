/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlaneUnitDiskSliceGeometry
public import LeanPool.FastDynamo.Analysis.WholePlaneUnitCircleWeightedSlices

/-!
# Fibre-generic unit-disk derivative sources

This module builds, for fields with values in an arbitrary complete complex normed fibre `F`,
the whole-plane weak-derivative identity

`∂_j F = {∂_j F} + [F] n_j δ_{r=1}`

out of coordinate-slice integration by parts across the unit circle.  Its one-dimensional and
geometric ingredients are independent of the fibre: the two-jump fundamental theorem of
calculus and its Fubini wrapper (`Analysis/WholePlaneTwoJumpIntegrationByParts.lean`),
the chord endpoints `± sqrt (1 - x²)` and the interior/exterior fibre dichotomy
(`Analysis/WholePlaneUnitDiskSliceGeometry.lean`) are stated for an arbitrary complete
normed target, or for no target at all.  This module adds the weak-derivative predicate, the
piecewise representative and the two constructors.  Instantiating at `F := C2` gives the
two-component source layer needed by `lem:jump-horizontal-mode` (the interface terms leading
to `eq:transmission-horizontal`, and the eigenfunction at the end of its proof), whose mode has
two Cartesian components and no axial branch.

## Contents

* `HasUnitCircleSourceDerivative`: the fibre-generic test-function semantics of a weak
  coordinate derivative with a unit-circle source, whose surface term is `unitCircleSurfaceValue`
  of `Analysis/WholePlaneUnitCircleSurface.lean`.
* `hasUnitCircleSourceDerivative_of_twoJump_slices_ae`: the generic two-jump slice constructor.
* `hasUnitCircleSourceDerivative_of_unitDisk_slices_ae`: its unit-disk specialization, in which
  all interval bookkeeping and all vanishing exterior-fibre jumps are discharged, leaving only
  the branchwise product-rule facts and one weighted boundary-chart identity.
-/

@[expose] public section

namespace FastDynamo

namespace WholePlaneFibreSource

noncomputable section

open Filter MeasureTheory Set Topology
open scoped LineDeriv SchwartzMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [CompleteSpace F]

/-! ## The fibre-generic unit-circle surface term

The surface value itself, `unitCircleSurfaceValue`, is
`Analysis/WholePlaneUnitCircleSurface.lean`'s; only the derivative predicate built on it is
defined here. -/

/-- Test-function semantics for a weak coordinate derivative consisting of an `L²` bulk
derivative and an integrable `F`-valued source on the unit circle.

The density is already oriented: changing the interface orientation negates it.  The sign
convention is Mathlib's: `∂_j T` evaluates `phi` by applying `T` to `-∂_j phi`. -/
def HasUnitCircleSourceDerivative (f bulk : WholePlaneL2 F)
    (density : WholePlaneUnitCircle → F) (j : Fin 2) : Prop :=
  ∀ phi : SchwartzMap WholePlane ℂ,
    ∫ x : WholePlane,
        ((-∂_{wholePlaneBasis j} phi) x) • (f x : F) ∂volume =
      (∫ x : WholePlane, phi x • (bulk x : F) ∂volume) +
        unitCircleSurfaceValue density phi

/-! ## Whole-plane derivative sources from two-jump coordinate slices -/

/-- The two right-minus-left jumps encountered in the positive `j`-coordinate direction,
already paired with a Schwartz test function.

At the first crossing the branch changes `left → middle`; at the second it changes
`middle → right`.  This orientation is the one produced by the real-line fundamental theorem
and, for a circle, agrees with `n_j (u_out - u_in)` at both intersection points. -/
def sliceTwoJumpValue (uLeft uMiddle uRight : WholePlane → F)
    (j : Fin 2) (a b : ℝ → ℝ) (phi : SchwartzMap WholePlane ℂ) (x : ℝ) : F :=
  let ya := wholePlaneSliceEquiv j (x, a x)
  let yb := wholePlaneSliceEquiv j (x, b x)
  phi ya • (uMiddle ya - uLeft ya) + phi yb • (uRight yb - uMiddle yb)

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- The pointwise product of a Schwartz test function with an `F`-valued `L²` field is
integrable over the plane, by Cauchy-Schwarz; this is what licenses the Fubini step below. -/
private theorem integrable_schwartz_smul_l2 (f : WholePlaneL2 F)
    (g : SchwartzMap WholePlane ℂ) :
    Integrable (fun x : WholePlane ↦ g x • (f x : F)) volume :=
  memLp_one_iff_integrable.mp <|
    (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] F →L[ℂ] F).memLp_of_bilin
      1 (g.memLp 2 volume) (Lp.memLp f)

/-- Construct a whole-plane weak derivative with a unit-circle source from branchwise
two-jump integration by parts on every coordinate slice.

The functions `uLeft`, `uMiddle`, and `uRight` are smooth branch representatives used only in
the one-dimensional fundamental theorem.  The functions `u` and `du` are the global pointwise
representatives of the `L²` value and bulk derivative.  Each branch product is required to have
the same classical derivative, namely the pulled-back product-rule integrand formed from `u`
and `du`.

The last hypothesis is the sole geometric chart identity: it identifies the outer integral of
the two oriented fibre jumps with the desired unit-circle surface functional. -/
theorem hasUnitCircleSourceDerivative_of_twoJump_slices_ae
    (u uLeft uMiddle uRight du : WholePlane → F)
    (f bulk : WholePlaneL2 F) (density : WholePlaneUnitCircle → F)
    (j : Fin 2) (a b : ℝ → ℝ)
    (hu : u =ᵐ[volume] fun y ↦ (f y : F))
    (hdu : du =ᵐ[volume] fun y ↦ (bulk y : F))
    (hab : ∀ᵐ x ∂(volume : Measure ℝ), a x < b x)
    (hLeftCont : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ),
      ContinuousWithinAt
        (fun t : ℝ ↦
          phi (wholePlaneSliceEquiv j (x, t)) •
            uLeft (wholePlaneSliceEquiv j (x, t)))
        (Iic (a x)) (a x))
    (hLeftDeriv : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ), ∀ t : ℝ,
      t ∈ Iio (a x) →
        HasDerivAt
          (fun v : ℝ ↦
            phi (wholePlaneSliceEquiv j (x, v)) •
              uLeft (wholePlaneSliceEquiv j (x, v)))
          (((∂_{wholePlaneBasis j} phi) (wholePlaneSliceEquiv j (x, t))) •
              u (wholePlaneSliceEquiv j (x, t)) +
            phi (wholePlaneSliceEquiv j (x, t)) •
              du (wholePlaneSliceEquiv j (x, t))) t)
    (hMiddleCont : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ),
      ContinuousOn
        (fun t : ℝ ↦
          phi (wholePlaneSliceEquiv j (x, t)) •
            uMiddle (wholePlaneSliceEquiv j (x, t)))
        (Icc (a x) (b x)))
    (hMiddleDeriv : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ), ∀ t : ℝ,
      t ∈ Ioo (a x) (b x) →
        HasDerivAt
          (fun v : ℝ ↦
            phi (wholePlaneSliceEquiv j (x, v)) •
              uMiddle (wholePlaneSliceEquiv j (x, v)))
          (((∂_{wholePlaneBasis j} phi) (wholePlaneSliceEquiv j (x, t))) •
              u (wholePlaneSliceEquiv j (x, t)) +
            phi (wholePlaneSliceEquiv j (x, t)) •
              du (wholePlaneSliceEquiv j (x, t))) t)
    (hRightCont : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ),
      ContinuousWithinAt
        (fun t : ℝ ↦
          phi (wholePlaneSliceEquiv j (x, t)) •
            uRight (wholePlaneSliceEquiv j (x, t)))
        (Ici (b x)) (b x))
    (hRightDeriv : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ), ∀ t : ℝ,
      t ∈ Ioi (b x) →
        HasDerivAt
          (fun v : ℝ ↦
            phi (wholePlaneSliceEquiv j (x, v)) •
              uRight (wholePlaneSliceEquiv j (x, v)))
          (((∂_{wholePlaneBasis j} phi) (wholePlaneSliceEquiv j (x, t))) •
              u (wholePlaneSliceEquiv j (x, t)) +
            phi (wholePlaneSliceEquiv j (x, t)) •
              du (wholePlaneSliceEquiv j (x, t))) t)
    (hLeftDecay : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto
        (fun t : ℝ ↦
          phi (wholePlaneSliceEquiv j (x, t)) •
            uLeft (wholePlaneSliceEquiv j (x, t)))
        atBot (nhds 0))
    (hRightDecay : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto
        (fun t : ℝ ↦
          phi (wholePlaneSliceEquiv j (x, t)) •
            uRight (wholePlaneSliceEquiv j (x, t)))
        atTop (nhds 0))
    (hFiberToSurface : ∀ phi : SchwartzMap WholePlane ℂ,
      ∫ x : ℝ, sliceTwoJumpValue uLeft uMiddle uRight j a b phi x =
        unitCircleSurfaceValue density phi) :
    HasUnitCircleSourceDerivative f bulk density j := by
  intro phi
  let q : WholePlane → F := fun y ↦
    ((∂_{wholePlaneBasis j} phi) y) • u y + phi y • du y
  have hleftL2 : Integrable
      (fun y : WholePlane ↦ ((∂_{wholePlaneBasis j} phi) y) • (f y : F)) volume :=
    integrable_schwartz_smul_l2 f (∂_{wholePlaneBasis j} phi)
  have hrightL2 : Integrable
      (fun y : WholePlane ↦ phi y • (bulk y : F)) volume :=
    integrable_schwartz_smul_l2 bulk phi
  have hleft : Integrable
      (fun y : WholePlane ↦ ((∂_{wholePlaneBasis j} phi) y) • u y) volume :=
    hleftL2.congr <| hu.symm.mono fun y hy ↦ by
      simpa using congrArg
        (fun z : F ↦ ((∂_{wholePlaneBasis j} phi) y) • z) hy
  have hright : Integrable
      (fun y : WholePlane ↦ phi y • du y) volume :=
    hrightL2.congr <| hdu.symm.mono fun y hy ↦ by
      simpa using congrArg (fun z : F ↦ phi y • z) hy
  have hq : Integrable q volume := hleft.add hright
  have hqPull : Integrable
      (q ∘ wholePlaneSliceEquiv j) ((volume : Measure ℝ).prod volume) :=
    (measurePreserving_wholePlaneSliceEquiv j).integrable_comp_of_integrable hq
  have htwoJumpPull :
      ∫ p : ℝ × ℝ, q (wholePlaneSliceEquiv j p)
          ∂((volume : Measure ℝ).prod volume) =
        -∫ x : ℝ, sliceTwoJumpValue uLeft uMiddle uRight j a b phi x := by
    have h := integral_prod_eq_integral_end_sub_start_sub_two_jumps_ae
      (fLeft := fun p : ℝ × ℝ ↦
        phi (wholePlaneSliceEquiv j p) • uLeft (wholePlaneSliceEquiv j p))
      (fMiddle := fun p : ℝ × ℝ ↦
        phi (wholePlaneSliceEquiv j p) • uMiddle (wholePlaneSliceEquiv j p))
      (fRight := fun p : ℝ × ℝ ↦
        phi (wholePlaneSliceEquiv j p) • uRight (wholePlaneSliceEquiv j p))
      (f' := q ∘ wholePlaneSliceEquiv j)
      (a := a) (b := b)
      (atNegInf := fun _ : ℝ ↦ 0) (atPosInf := fun _ : ℝ ↦ 0)
      hab (hLeftCont phi) (hLeftDeriv phi) (hMiddleCont phi)
      (hMiddleDeriv phi) (hRightCont phi) (hRightDeriv phi)
      hqPull (hLeftDecay phi) (hRightDecay phi)
    change (∫ p : ℝ × ℝ, q (wholePlaneSliceEquiv j p)
      ∂((volume : Measure ℝ).prod volume)) = _ at h
    rw [h]
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [zero_sub, neg_zero]
    change -(_ + _) = -sliceTwoJumpValue uLeft uMiddle uRight j a b phi x
    congr 1
    simp [sliceTwoJumpValue, smul_sub]
  have hqGlobal :
      ∫ y : WholePlane, q y = -unitCircleSurfaceValue density phi := by
    rw [← (measurePreserving_wholePlaneSliceEquiv j).integral_comp' q]
    rw [htwoJumpPull, hFiberToSurface phi]
  have hsum :
      (∫ y : WholePlane,
          ((∂_{wholePlaneBasis j} phi) y) • u y ∂volume) +
        ∫ y : WholePlane, phi y • du y ∂volume =
      -unitCircleSurfaceValue density phi := by
    rw [← integral_add hleft hright]
    exact hqGlobal
  have hconcrete :
      (∫ y : WholePlane,
          ((-∂_{wholePlaneBasis j} phi) y) • u y ∂volume) =
        (∫ y : WholePlane, phi y • du y ∂volume) +
          unitCircleSurfaceValue density phi := by
    rw [show (fun y : WholePlane ↦
        ((-∂_{wholePlaneBasis j} phi) y) • u y) =
      fun y : WholePlane ↦
        -(((∂_{wholePlaneBasis j} phi) y) • u y) by
          funext y
          simp]
    rw [integral_neg]
    apply neg_eq_of_add_eq_zero_left
    calc
      ((∫ y : WholePlane, phi y • du y ∂volume) +
          unitCircleSurfaceValue density phi) +
          ∫ y : WholePlane,
            ((∂_{wholePlaneBasis j} phi) y) • u y ∂volume =
        ((∫ y : WholePlane,
            ((∂_{wholePlaneBasis j} phi) y) • u y ∂volume) +
          ∫ y : WholePlane, phi y • du y ∂volume) +
            unitCircleSurfaceValue density phi := by abel
      _ = -unitCircleSurfaceValue density phi +
            unitCircleSurfaceValue density phi := by rw [hsum]
      _ = 0 := neg_add_cancel _
  calc
    (∫ y : WholePlane,
        ((-∂_{wholePlaneBasis j} phi) y) • (f y : F) ∂volume) =
      ∫ y : WholePlane,
        ((-∂_{wholePlaneBasis j} phi) y) • u y ∂volume := by
        apply integral_congr_ae
        exact hu.symm.mono fun y hy ↦ by
          simpa using congrArg
            (fun z : F ↦ ((-∂_{wholePlaneBasis j} phi) y) • z) hy
    _ = (∫ y : WholePlane, phi y • du y ∂volume) +
          unitCircleSurfaceValue density phi := hconcrete
    _ = (∫ y : WholePlane, phi y • (bulk y : F) ∂volume) +
          unitCircleSurfaceValue density phi := by
        congr 1
        apply integral_congr_ae
        exact hdu.mono fun y hy ↦ by
          simpa using congrArg (fun z : F ↦ phi y • z) hy

/-! ## Unit-disk specialization -/

/-- The global closed-disk representative formed from an interior and an exterior branch.  The
interior value is selected on the boundary, matching the true middle-branch endpoint trace. -/
def unitDiskPiecewiseField (uInterior uExterior : WholePlane → F) (y : WholePlane) : F := by
  classical
  exact if y ∈ wholePlaneUnitDisk then uInterior y else uExterior y

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [CompleteSpace F] in
/-- Inside the closed unit disk the piecewise representative takes the interior branch's
value. -/
@[simp] theorem unitDiskPiecewiseField_of_mem
    (uInterior uExterior : WholePlane → F) {y : WholePlane}
    (hy : y ∈ wholePlaneUnitDisk) :
    unitDiskPiecewiseField uInterior uExterior y = uInterior y := by
  simp [unitDiskPiecewiseField, hy]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [CompleteSpace F] in
/-- Outside the closed unit disk the piecewise representative takes the exterior branch's
value. -/
@[simp] theorem unitDiskPiecewiseField_of_notMem
    (uInterior uExterior : WholePlane → F) {y : WholePlane}
    (hy : y ∉ wholePlaneUnitDisk) :
    unitDiskPiecewiseField uInterior uExterior y = uExterior y := by
  simp [unitDiskPiecewiseField, hy]

/-- On an interior fibre the lower crossing point `(x, -sqrt(1 - x²))` lies in the closed unit
disk. -/
private theorem lower_mem_unitDisk (j : Fin 2) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    wholePlaneSliceEquiv j (x, -wholePlaneUnitDiskSliceRadius x) ∈ wholePlaneUnitDisk := by
  refine wholePlaneSliceEquiv_mem_unitDisk_of_mem_endpointInterval j hx ?_
  simp only [wholePlaneUnitDiskSliceLower, wholePlaneUnitDiskSliceUpper, ite_eq_left hx,
    mem_Icc]
  exact ⟨le_rfl, by linarith [Real.sqrt_nonneg (1 - x ^ 2),
    show wholePlaneUnitDiskSliceRadius x = Real.sqrt (1 - x ^ 2) from rfl]⟩

/-- On an interior fibre the upper crossing point `(x, sqrt(1 - x²))` lies in the closed unit
disk. -/
private theorem upper_mem_unitDisk (j : Fin 2) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    wholePlaneSliceEquiv j (x, wholePlaneUnitDiskSliceRadius x) ∈ wholePlaneUnitDisk := by
  refine wholePlaneSliceEquiv_mem_unitDisk_of_mem_endpointInterval j hx ?_
  simp only [wholePlaneUnitDiskSliceLower, wholePlaneUnitDiskSliceUpper, ite_eq_left hx,
    mem_Icc]
  exact ⟨by linarith [Real.sqrt_nonneg (1 - x ^ 2),
    show wholePlaneUnitDiskSliceRadius x = Real.sqrt (1 - x ^ 2) from rfl], le_rfl⟩

/-- On a fibre whose transverse parameter lies outside `(-1, 1)`, the artificial endpoints
`(x, ±1)` lie strictly outside the closed unit disk; this is why both artificial jumps
vanish. -/
private theorem artificial_endpoint_notMem_unitDisk
    (j : Fin 2) {x : ℝ} (hx : x ∉ Ioo (-1 : ℝ) 1) (sign : ℝ) (hsign : sign ^ 2 = 1) :
    wholePlaneSliceEquiv j (x, sign) ∉ wholePlaneUnitDisk := by
  have hxOuter : x ≤ -1 ∨ 1 ≤ x := by
    by_contra h
    rw [not_or, not_le, not_le] at h
    exact hx ⟨h.1, h.2⟩
  have hxSq : 1 ≤ x ^ 2 := by
    rcases hxOuter with hxLower | hxUpper <;> nlinarith [sq_nonneg x]
  have hnormSq := norm_sq_wholePlaneSliceEquiv j x sign
  rw [hsign] at hnormSq
  have hnorm : 1 < ‖wholePlaneSliceEquiv j (x, sign)‖ := by
    nlinarith [norm_nonneg (wholePlaneSliceEquiv j (x, sign))]
  intro hmem
  have hle : ‖wholePlaneSliceEquiv j (x, sign)‖ ≤ 1 := by
    simpa [wholePlaneUnitDisk, Metric.mem_closedBall] using hmem
  exact (not_lt_of_ge hle) hnorm

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [CompleteSpace F] in
/-- On an interior fibre the piecewise representative agrees with the interior branch
throughout the closed interval between the two crossing points. -/
@[simp] theorem unitDiskPiecewiseField_slice_of_interior
    (uInterior uExterior : WholePlane → F) (j : Fin 2) {x t : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Icc (wholePlaneUnitDiskSliceLower x) (wholePlaneUnitDiskSliceUpper x)) :
    unitDiskPiecewiseField uInterior uExterior (wholePlaneSliceEquiv j (x, t)) =
      uInterior (wholePlaneSliceEquiv j (x, t)) :=
  unitDiskPiecewiseField_of_mem _ _
    (wholePlaneSliceEquiv_mem_unitDisk_of_mem_endpointInterval j hx ht)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [CompleteSpace F] in
/-- On a strictly exterior fibre the piecewise representative agrees with the exterior branch
at every inner coordinate. -/
@[simp] theorem unitDiskPiecewiseField_slice_of_strictExterior
    (uInterior uExterior : WholePlane → F) (j : Fin 2) {x : ℝ}
    (hx : x ∉ Icc (-1 : ℝ) 1) (t : ℝ) :
    unitDiskPiecewiseField uInterior uExterior (wholePlaneSliceEquiv j (x, t)) =
      uExterior (wholePlaneSliceEquiv j (x, t)) :=
  unitDiskPiecewiseField_of_notMem _ _
    (wholePlaneSliceEquiv_notMem_unitDisk_of_transverse_notMem j hx t)

/-- The two boundary-trace jumps on an interior transverse fibre. -/
def unitDiskBoundaryTwoJumpValue (uInterior uExterior : WholePlane → F) (j : Fin 2)
    (phi : SchwartzMap WholePlane ℂ) (x : ℝ) : F :=
  let yLower := wholePlaneSliceEquiv j (x, -wholePlaneUnitDiskSliceRadius x)
  let yUpper := wholePlaneSliceEquiv j (x, wholePlaneUnitDiskSliceRadius x)
  phi yLower • (uInterior yLower - uExterior yLower) +
    phi yUpper • (uExterior yUpper - uInterior yUpper)

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- With the closed-disk middle representative, the global artificial-endpoint jump integrand
is the indicator of the two boundary jumps on `(-1, 1)`. -/
theorem sliceTwoJumpValue_unitDisk_eq_indicator
    (uInterior uExterior : WholePlane → F) (j : Fin 2)
    (phi : SchwartzMap WholePlane ℂ) (x : ℝ) :
    sliceTwoJumpValue uExterior (unitDiskPiecewiseField uInterior uExterior) uExterior
        j wholePlaneUnitDiskSliceLower wholePlaneUnitDiskSliceUpper phi x =
      (Ioo (-1 : ℝ) 1).indicator
        (unitDiskBoundaryTwoJumpValue uInterior uExterior j phi) x := by
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx]
    have hLower := lower_mem_unitDisk j hx
    have hUpper := upper_mem_unitDisk j hx
    simp [sliceTwoJumpValue, unitDiskBoundaryTwoJumpValue,
      wholePlaneUnitDiskSliceLower, wholePlaneUnitDiskSliceUpper, hx,
      unitDiskPiecewiseField_of_mem, hLower, hUpper]
  · rw [Set.indicator_of_notMem hx]
    have hLower := artificial_endpoint_notMem_unitDisk j hx (-1) (by norm_num)
    have hUpper := artificial_endpoint_notMem_unitDisk j hx 1 (by norm_num)
    simp [sliceTwoJumpValue, wholePlaneUnitDiskSliceLower,
      wholePlaneUnitDiskSliceUpper, hx,
      unitDiskPiecewiseField_of_notMem, hLower, hUpper]

/-- Unit-disk specialization of the fibre-generic almost-everywhere two-jump source
constructor.

All interval endpoints and all vanishing exterior-fibre jumps are discharged here.  The final
geometric hypothesis is only the weighted chart equality for the two actual lower/upper circle
traces over `x ∈ (-1, 1)`; it is supplied by
`integral_wholePlaneUnitCircle_coordinate_smul_eq_setIntegral`, which is already stated for an
arbitrary normed target. -/
theorem hasUnitCircleSourceDerivative_of_unitDisk_slices_ae
    (uInterior uExterior du : WholePlane → F)
    (f bulk : WholePlaneL2 F) (density : WholePlaneUnitCircle → F) (j : Fin 2)
    (hu : unitDiskPiecewiseField uInterior uExterior =ᵐ[volume] fun y ↦ (f y : F))
    (hdu : du =ᵐ[volume] fun y ↦ (bulk y : F))
    (hLeftCont : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ), ContinuousWithinAt
        (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
          uExterior (wholePlaneSliceEquiv j (x, t)))
        (Iic (wholePlaneUnitDiskSliceLower x))
        (wholePlaneUnitDiskSliceLower x))
    (hLeftDeriv : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ), ∀ t : ℝ,
        t ∈ Iio (wholePlaneUnitDiskSliceLower x) →
        HasDerivAt
          (fun v : ℝ ↦ phi (wholePlaneSliceEquiv j (x, v)) •
            uExterior (wholePlaneSliceEquiv j (x, v)))
          (((∂_{wholePlaneBasis j} phi) (wholePlaneSliceEquiv j (x, t))) •
              unitDiskPiecewiseField uInterior uExterior
                (wholePlaneSliceEquiv j (x, t)) +
            phi (wholePlaneSliceEquiv j (x, t)) •
              du (wholePlaneSliceEquiv j (x, t))) t)
    (hMiddleCont : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ), ContinuousOn
        (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
          unitDiskPiecewiseField uInterior uExterior
            (wholePlaneSliceEquiv j (x, t)))
        (Icc (wholePlaneUnitDiskSliceLower x)
          (wholePlaneUnitDiskSliceUpper x)))
    (hMiddleDeriv : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ), ∀ t : ℝ,
        t ∈ Ioo (wholePlaneUnitDiskSliceLower x)
          (wholePlaneUnitDiskSliceUpper x) →
        HasDerivAt
          (fun v : ℝ ↦ phi (wholePlaneSliceEquiv j (x, v)) •
            unitDiskPiecewiseField uInterior uExterior
              (wholePlaneSliceEquiv j (x, v)))
          (((∂_{wholePlaneBasis j} phi) (wholePlaneSliceEquiv j (x, t))) •
              unitDiskPiecewiseField uInterior uExterior
                (wholePlaneSliceEquiv j (x, t)) +
            phi (wholePlaneSliceEquiv j (x, t)) •
              du (wholePlaneSliceEquiv j (x, t))) t)
    (hRightCont : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ), ContinuousWithinAt
        (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
          uExterior (wholePlaneSliceEquiv j (x, t)))
        (Ici (wholePlaneUnitDiskSliceUpper x))
        (wholePlaneUnitDiskSliceUpper x))
    (hRightDeriv : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ), ∀ t : ℝ,
        t ∈ Ioi (wholePlaneUnitDiskSliceUpper x) →
        HasDerivAt
          (fun v : ℝ ↦ phi (wholePlaneSliceEquiv j (x, v)) •
            uExterior (wholePlaneSliceEquiv j (x, v)))
          (((∂_{wholePlaneBasis j} phi) (wholePlaneSliceEquiv j (x, t))) •
              unitDiskPiecewiseField uInterior uExterior
                (wholePlaneSliceEquiv j (x, t)) +
            phi (wholePlaneSliceEquiv j (x, t)) •
              du (wholePlaneSliceEquiv j (x, t))) t)
    (hLeftDecay : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ), Tendsto
        (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
          uExterior (wholePlaneSliceEquiv j (x, t))) atBot (nhds 0))
    (hRightDecay : ∀ (phi : SchwartzMap WholePlane ℂ),
      ∀ᵐ x ∂(volume : Measure ℝ), Tendsto
        (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
          uExterior (wholePlaneSliceEquiv j (x, t))) atTop (nhds 0))
    (hBoundaryToSurface : ∀ phi : SchwartzMap WholePlane ℂ,
      ∫ x : ℝ in Ioo (-1) 1,
          unitDiskBoundaryTwoJumpValue uInterior uExterior j phi x =
        unitCircleSurfaceValue density phi) :
    HasUnitCircleSourceDerivative f bulk density j := by
  apply hasUnitCircleSourceDerivative_of_twoJump_slices_ae
    (unitDiskPiecewiseField uInterior uExterior)
    uExterior (unitDiskPiecewiseField uInterior uExterior) uExterior du
    f bulk density j wholePlaneUnitDiskSliceLower wholePlaneUnitDiskSliceUpper
    hu hdu
    (Filter.Eventually.of_forall wholePlaneUnitDiskSliceLower_lt_upper)
    hLeftCont hLeftDeriv hMiddleCont hMiddleDeriv hRightCont hRightDeriv
    hLeftDecay hRightDecay
  intro phi
  calc
    (∫ x : ℝ,
        sliceTwoJumpValue uExterior
          (unitDiskPiecewiseField uInterior uExterior) uExterior
          j wholePlaneUnitDiskSliceLower wholePlaneUnitDiskSliceUpper phi x) =
      ∫ x : ℝ, (Ioo (-1 : ℝ) 1).indicator
        (unitDiskBoundaryTwoJumpValue uInterior uExterior j phi) x := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact sliceTwoJumpValue_unitDisk_eq_indicator
            uInterior uExterior j phi x
    _ = ∫ x : ℝ in Ioo (-1) 1,
        unitDiskBoundaryTwoJumpValue uInterior uExterior j phi x :=
      integral_indicator measurableSet_Ioo
    _ = unitCircleSurfaceValue density phi := hBoundaryToSurface phi

/-! ## The oriented jump density and the weighted boundary chart -/

section JumpDensity

variable [SMulCommClass ℝ ℂ F]

/-- The outward-minus-inward coordinate trace of a two-branch field on the unit circle: the
density produced by differentiating the glued field in the `j`-th coordinate direction.  The
weight `y j` is the `j`-th component of the outward unit normal `n = y`. -/
def unitCircleJumpDensity (uInterior uExterior : WholePlane → F) (j : Fin 2)
    (y : WholePlaneUnitCircle) : F :=
  (y.1 j) • (uExterior y.1 - uInterior y.1)

/-- A point of the transverse unit circle is nonzero, so a branch singular only at the origin
is continuous there. -/
private theorem unitCircle_val_ne_zero' (y : WholePlaneUnitCircle) : y.1 ≠ 0 := by
  intro hy
  have hnorm : ‖y.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using y.2
  rw [hy, norm_zero] at hnorm
  norm_num at hnorm

omit [NormedSpace ℂ F] [CompleteSpace F] [SMulCommClass ℝ ℂ F] in
/-- The oriented jump density is continuous whenever the interior branch is continuous and the
exterior branch is continuous away from the origin. -/
theorem unitCircleJumpDensity_continuous
    {uInterior uExterior : WholePlane → F} (j : Fin 2)
    (hInterior : Continuous uInterior)
    (hExterior : ∀ y : WholePlane, y ≠ 0 → ContinuousAt uExterior y) :
    Continuous (unitCircleJumpDensity uInterior uExterior j) := by
  unfold unitCircleJumpDensity
  have hcoord : Continuous (fun y : WholePlaneUnitCircle ↦ y.1 j) := by
    fun_prop
  have hExt : Continuous (fun y : WholePlaneUnitCircle ↦ uExterior y.1) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (hExterior y.1 (unitCircle_val_ne_zero' y)).comp continuousAt_subtype_val
  have hInt : Continuous (fun y : WholePlaneUnitCircle ↦ uInterior y.1) :=
    hInterior.comp continuous_subtype_val
  exact hcoord.smul (hExt.sub hInt)

omit [NormedSpace ℝ F] [NormedSpace ℂ F] [CompleteSpace F] [SMulCommClass ℝ ℂ F] in
/-- A continuous unit-circle density is integrable, the circle being compact. -/
theorem integrable_of_continuous_unitCircleDensity
    {density : WholePlaneUnitCircle → F} (h : Continuous density) :
    Integrable density wholePlaneUnitCircleMeasure := by
  let _ : IsFiniteMeasure wholePlaneUnitCircleMeasure := by
    unfold wholePlaneUnitCircleMeasure
    infer_instance
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [NormedSpace ℂ F] [CompleteSpace F] [SMulCommClass ℝ ℂ F] in
/-- The oriented jump density of a two-branch field is integrable on the unit circle. -/
theorem unitCircleJumpDensity_integrable
    {uInterior uExterior : WholePlane → F} (j : Fin 2)
    (hInterior : Continuous uInterior)
    (hExterior : ∀ y : WholePlane, y ≠ 0 → ContinuousAt uExterior y) :
    Integrable (unitCircleJumpDensity uInterior uExterior j)
      wholePlaneUnitCircleMeasure :=
  integrable_of_continuous_unitCircleDensity
    (unitCircleJumpDensity_continuous j hInterior hExterior)

omit [CompleteSpace F] in
/-- The weighted boundary chart: the outer integral of the two circle traces of a
two-branch field over the transverse interval `(-1, 1)` is the unit-circle surface term of its
oriented jump density.

This is the sole geometric hypothesis of
`hasUnitCircleSourceDerivative_of_unitDisk_slices_ae`.  A cutoff on the half-unit ball turns
the punctured-plane exterior branch into the globally continuous ambient integrand required by
`integral_wholePlaneUnitCircle_coordinate_smul_eq_setIntegral`. -/
theorem integral_unitDiskBoundaryTwoJumpValue_eq_unitCircleSurfaceValue
    {uInterior uExterior : WholePlane → F} (j : Fin 2)
    (hInterior : Continuous uInterior)
    (hExterior : ∀ y : WholePlane, y ≠ 0 → ContinuousAt uExterior y)
    (phi : SchwartzMap WholePlane ℂ) :
    ∫ x : ℝ in Ioo (-1) 1,
        unitDiskBoundaryTwoJumpValue uInterior uExterior j phi x =
      unitCircleSurfaceValue (unitCircleJumpDensity uInterior uExterior j) phi := by
  classical
  set small : Set WholePlane := Metric.ball 0 (1 / 2 : ℝ) with hsmall
  set scale : WholePlane → ℝ := fun y ↦ 2 * ‖y‖ - 1 with hscaledef
  set raw : WholePlane → F := fun y ↦ phi y • (uExterior y - uInterior y) with hrawdef
  set J : WholePlane → F := small.piecewise (fun _ ↦ 0) (fun y ↦ scale y • raw y) with hJdef
  have hscale : Continuous scale := by
    rw [hscaledef]
    fun_prop
  have hJ : Continuous J := by
    rw [hJdef]
    apply continuous_piecewise
    · intro y hy
      have hySphere : y ∈ Metric.sphere (0 : WholePlane) (1 / 2 : ℝ) :=
        Metric.frontier_ball_subset_sphere hy
      have hynorm : ‖y‖ = 1 / 2 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hySphere
      simp [hscaledef, hynorm]
    · exact continuousOn_const
    · intro y hy
      have hyCompl : y ∈ smallᶜ := by
        rw [← Metric.isOpen_ball.isClosed_compl.closure_eq]
        exact hy
      have hynorm : (1 / 2 : ℝ) ≤ ‖y‖ := by
        simpa only [hsmall, Metric.mem_ball, dist_zero_right, mem_compl_iff,
          not_lt] using hyCompl
      have hy0 : y ≠ 0 := by
        intro hyZero
        rw [hyZero, norm_zero] at hynorm
        norm_num at hynorm
      have hraw : ContinuousAt raw y := by
        rw [hrawdef]
        exact phi.continuous.continuousAt.smul
          ((hExterior y hy0).sub hInterior.continuousAt)
      exact (hscale.continuousAt.smul hraw).continuousWithinAt
  have hchart := integral_wholePlaneUnitCircle_coordinate_smul_eq_setIntegral j J hJ
  have hJcircle : ∀ y : WholePlane, ‖y‖ = 1 →
      J y = phi y • (uExterior y - uInterior y) := by
    intro y hy
    have hyNot : y ∉ small := by
      simp only [hsmall, Metric.mem_ball, dist_zero_right, hy, not_lt]
      norm_num
    rw [hJdef]
    simp only [Set.piecewise_eq_of_notMem _ _ _ hyNot, hscaledef, hrawdef, hy]
    norm_num
  symm
  calc
    unitCircleSurfaceValue (unitCircleJumpDensity uInterior uExterior j) phi =
        ∫ y : WholePlaneUnitCircle, (y.1 j) • J y.1 ∂wholePlaneUnitCircleMeasure := by
      unfold unitCircleSurfaceValue
      apply integral_congr_ae
      filter_upwards [] with y
      have hynorm : ‖y.1‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using y.2
      rw [hJcircle y.1 hynorm]
      exact (smul_comm (y.1 j) (phi y.1) (uExterior y.1 - uInterior y.1)).symm
    _ = ∫ x : ℝ in Ioo (-1 : ℝ) 1,
          (J (wholePlaneUnitCircleUpperPoint j x) -
            J (wholePlaneUnitCircleLowerPoint j x)) := hchart
    _ = ∫ x : ℝ in Ioo (-1) 1,
          unitDiskBoundaryTwoJumpValue uInterior uExterior j phi x := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      have hnonneg : (0 : ℝ) ≤ 1 - x ^ 2 := by
        rcases hx with ⟨hxLower, hxUpper⟩
        nlinarith
      have hsqrt : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hnonneg
      have hUpperNorm : ‖wholePlaneUnitCircleUpperPoint j x‖ = 1 := by
        have hsq := norm_sq_wholePlaneSliceEquiv j x (Real.sqrt (1 - x ^ 2))
        rw [← wholePlaneUnitCircleUpperPoint] at hsq
        nlinarith [norm_nonneg (wholePlaneUnitCircleUpperPoint j x)]
      have hLowerNorm : ‖wholePlaneUnitCircleLowerPoint j x‖ = 1 := by
        have hsq := norm_sq_wholePlaneSliceEquiv j x (-(Real.sqrt (1 - x ^ 2)))
        rw [← wholePlaneUnitCircleLowerPoint] at hsq
        nlinarith [norm_nonneg (wholePlaneUnitCircleLowerPoint j x)]
      change J (wholePlaneUnitCircleUpperPoint j x) -
        J (wholePlaneUnitCircleLowerPoint j x) = _
      rw [hJcircle _ hUpperNorm, hJcircle _ hLowerNorm]
      simp only [unitDiskBoundaryTwoJumpValue, wholePlaneUnitCircleUpperPoint,
        wholePlaneUnitCircleLowerPoint, wholePlaneUnitDiskSliceRadius, smul_sub]
      abel

end JumpDensity

end

end WholePlaneFibreSource

end FastDynamo
