/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlaneFourier

/-!
# The scalar Cartesian second-partial layer

The diffusion part of the transverse operator of the paper's local model is
`(Δ_⊥ - N²) b` (`eq:horizontal-induction`, where the paper has `N² = 4π²`), and its polar form
is read component by component in the circular variables (proof of `lem:jump-horizontal-mode`).
Both readings need one
scalar object: the ordered Cartesian second partial `∂_k ∂_j f` of a complex-valued function
on the plane, defined through Mathlib's totalized `fderiv`, together with its trace, the
scalar Laplacian.

Nothing in this module mentions a Ponomarenko mode, a Bessel branch, or a fibre: it is the
generic scalar layer used by `Local/PonomarenkoCartesianPolarLaplacian.lean` and
`Local/HorizontalModeSecondDerivatives.lean`.  Because Mathlib's `fderiv` is
totalized, additivity and homogeneity need a local `C²` hypothesis, which every lemma below
carries explicitly.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace ScalarSecondPartial

open Filter Topology

/-! ## The ordered second partial and its trace -/

/-- The ordered Cartesian second partial `∂ₖ∂ⱼ f`, expressed using totalized `fderiv`. -/
def scalarSecondPartial
    (f : WholePlane → ℂ) (j k : Fin 2) (y : WholePlane) : ℂ :=
  fderiv ℝ (fun x : WholePlane ↦ fderiv ℝ f x (wholePlaneBasis j)) y
    (wholePlaneBasis k)

/-- The two-dimensional Cartesian Laplacian obtained by tracing the scalar Hessian. -/
def scalarCartesianLaplacian (f : WholePlane → ℂ) (y : WholePlane) : ℂ :=
  scalarSecondPartial f 0 0 y + scalarSecondPartial f 1 1 y

/-! The scalar second-partial operator is linear on locally `C²` functions.  The explicit
smoothness hypotheses matter because Mathlib's totalized `fderiv` is not linear at arbitrary
nondifferentiability points. -/

/-- The ordered second Cartesian partial is additive on functions that are `C²` near the point.
The smoothness hypotheses are needed because Mathlib's totalized `fderiv` is not additive at
arbitrary points of nondifferentiability. -/
theorem scalarSecondPartial_add
    {f g : WholePlane → ℂ} {y : WholePlane}
    (hf : ContDiffAt ℝ 2 f y) (hg : ContDiffAt ℝ 2 g y) (j k : Fin 2) :
    scalarSecondPartial (fun x ↦ f x + g x) j k y =
      scalarSecondPartial f j k y + scalarSecondPartial g j k y := by
  have hfevent := hf.eventually (by norm_num)
  have hgevent := hg.eventually (by norm_num)
  have hevent :
      (fun x : WholePlane ↦
        fderiv ℝ (fun z : WholePlane ↦ f z + g z) x (wholePlaneBasis j)) =ᶠ[nhds y]
      fun x : WholePlane ↦
        fderiv ℝ f x (wholePlaneBasis j) + fderiv ℝ g x (wholePlaneBasis j) := by
    filter_upwards [hfevent, hgevent] with x hfx hgx
    rw [fderiv_fun_add (hfx.differentiableAt (by norm_num))
      (hgx.differentiableAt (by norm_num))]
    rfl
  have hfjCont : ContDiffAt ℝ 1
      (fun x : WholePlane ↦ fderiv ℝ f x (wholePlaneBasis j)) y :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hgjCont : ContDiffAt ℝ 1
      (fun x : WholePlane ↦ fderiv ℝ g x (wholePlaneBasis j)) y :=
    (hg.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hfj := hfjCont.differentiableAt (by norm_num)
  have hgj := hgjCont.differentiableAt (by norm_num)
  unfold scalarSecondPartial
  rw [hevent.fderiv_eq, fderiv_fun_add hfj hgj]
  rfl

/-- The ordered second Cartesian partial commutes with multiplication by a complex constant, for a
function that is `C²` near the point. -/
theorem scalarSecondPartial_const_mul
    {f : WholePlane → ℂ} {y : WholePlane} (hf : ContDiffAt ℝ 2 f y)
    (c : ℂ) (j k : Fin 2) :
    scalarSecondPartial (fun x ↦ c * f x) j k y =
      c * scalarSecondPartial f j k y := by
  have hevent :
      (fun x : WholePlane ↦
        fderiv ℝ (fun z : WholePlane ↦ c * f z) x (wholePlaneBasis j)) =ᶠ[nhds y]
      fun x : WholePlane ↦ c * fderiv ℝ f x (wholePlaneBasis j) := by
    filter_upwards [hf.eventually (by norm_num)] with x hfx
    rw [fderiv_const_mul (hfx.differentiableAt (by norm_num)) c]
    simp only [smul_apply, smul_eq_mul]
  have hfjCont : ContDiffAt ℝ 1
      (fun x : WholePlane ↦ fderiv ℝ f x (wholePlaneBasis j)) y :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hfj := hfjCont.differentiableAt (by norm_num)
  unfold scalarSecondPartial
  rw [hevent.fderiv_eq, fderiv_const_mul hfj c]
  simp only [smul_apply, smul_eq_mul]

/-- The transverse Cartesian Laplacian is complex-linear on functions that are `C²` near the point:
`Δ(cf + dg) = cΔf + dΔg`. -/
theorem scalarCartesianLaplacian_linearCombination
    {f g : WholePlane → ℂ} {y : WholePlane}
    (hf : ContDiffAt ℝ 2 f y) (hg : ContDiffAt ℝ 2 g y) (c d : ℂ) :
    scalarCartesianLaplacian (fun x ↦ c * f x + d * g x) y =
      c * scalarCartesianLaplacian f y + d * scalarCartesianLaplacian g y := by
  have hcf : ContDiffAt ℝ 2 (fun x ↦ c * f x) y := by
    convert! contDiffAt_const.mul hf using 1
  have hdg : ContDiffAt ℝ 2 (fun x ↦ d * g x) y := by
    convert! contDiffAt_const.mul hg using 1
  unfold scalarCartesianLaplacian
  rw [scalarSecondPartial_add hcf hdg,
    scalarSecondPartial_add hcf hdg,
    scalarSecondPartial_const_mul hf c,
    scalarSecondPartial_const_mul hg d,
    scalarSecondPartial_const_mul hf c,
    scalarSecondPartial_const_mul hg d]
  ring

/-- The explicit `j`-th Cartesian first partial of a radial mode away from the axis. -/
theorem scalarSecondPartial_congr_of_eventuallyEq
    {f g : WholePlane → ℂ} {y : WholePlane} (h : f =ᶠ[nhds y] g) (j k : Fin 2) :
    scalarSecondPartial f j k y = scalarSecondPartial g j k y := by
  have hev : (fun x : WholePlane ↦ fderiv ℝ f x (wholePlaneBasis j)) =ᶠ[nhds y]
      fun x : WholePlane ↦ fderiv ℝ g x (wholePlaneBasis j) := by
    filter_upwards [h.eventuallyEq_nhds] with x hx
    rw [hx.fderiv_eq]
  unfold scalarSecondPartial
  rw [hev.fderiv_eq]

/-- The transverse Cartesian Laplacian only depends on the germ of the function. -/
theorem scalarCartesianLaplacian_congr_of_eventuallyEq
    {f g : WholePlane → ℂ} {y : WholePlane} (h : f =ᶠ[nhds y] g) :
    scalarCartesianLaplacian f y = scalarCartesianLaplacian g y := by
  unfold scalarCartesianLaplacian
  rw [scalarSecondPartial_congr_of_eventuallyEq h 0 0,
    scalarSecondPartial_congr_of_eventuallyEq h 1 1]

/-! ## Two consequences used by the local model -/

/-- The ordered second Cartesian partial is complex-linear on locally `C²` functions. -/
theorem scalarSecondPartial_linearCombination
    {f g : WholePlane → ℂ} {y : WholePlane}
    (hf : ContDiffAt ℝ 2 f y) (hg : ContDiffAt ℝ 2 g y) (c d : ℂ) (j k : Fin 2) :
    scalarSecondPartial (fun x ↦ c * f x + d * g x) j k y =
      c * scalarSecondPartial f j k y + d * scalarSecondPartial g j k y := by
  have hcf : ContDiffAt ℝ 2 (fun x ↦ c * f x) y := by
    convert! contDiffAt_const.mul hf using 1
  have hdg : ContDiffAt ℝ 2 (fun x ↦ d * g x) y := by
    convert! contDiffAt_const.mul hg using 1
  rw [scalarSecondPartial_add hcf hdg, scalarSecondPartial_const_mul hf c,
    scalarSecondPartial_const_mul hg d]

/-- The order-two truncation of the smoothness scale, used throughout to descend from `⊤`. -/
theorem horizontalTwo_le_top : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl 2

end ScalarSecondPartial

end FastDynamo

end
