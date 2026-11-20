/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneFourier
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Generic first-order calculus for plane bump functions

Both the interior radial weight of
`FastDynamo/Global/WholePlaneW1InfCertificates.lean` and the parametrix
cut-offs are built from `ContDiffBump`s on the transverse whole plane, rescaled affinely by the
buffer radius.  The facts they share are purely generic: a smooth compactly
supported bump is globally Lipschitz, its Fréchet derivative vanishes inside
the inner ball and beyond the outer radius, and a Lipschitz real profile has
coordinate derivatives bounded by its Lipschitz constant.

This module isolates exactly those generic facts.  Nothing here mentions a weight, a
resolvent, or a radius of the paper.  The declarations live in the namespace
`ConstantCoefficientBackground`, shared with the constant-coefficient modules of `Global/`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace ConstantCoefficientBackground

/-- A canonical finite Lipschitz constant for a smooth compactly supported
bump.  It is extracted from the proved compact-support `C¹` theorem. -/
def contDiffBumpLipschitzConstant {p : WholePlane} (b : ContDiffBump p) : NNReal :=
  Classical.choose
    (ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport
      (b.contDiff : ContDiff ℝ 1 b) (by norm_num))

/-- A `ContDiffBump` on the plane is Lipschitz with the canonical constant
`contDiffBumpLipschitzConstant`, obtained from the compact-support `C¹` theorem. -/
theorem contDiffBump_lipschitzWith {p : WholePlane} (b : ContDiffBump p) :
    LipschitzWith (contDiffBumpLipschitzConstant b) b :=
  Classical.choose_spec
    (ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport
      (b.contDiff : ContDiff ℝ 1 b) (by norm_num))

/-- Inside its inner ball a `ContDiffBump` is identically one, so its Fréchet derivative vanishes
there. -/
theorem contDiffBump_fderiv_eq_zero_of_mem_ball {p : WholePlane}
    (b : ContDiffBump p) {x : WholePlane} (hx : x ∈ Metric.ball p b.rIn) :
    fderiv ℝ b x = 0 := by
  have heq : (b : WholePlane → ℝ) =ᶠ[nhds x] fun _ ↦ 1 :=
    b.eventuallyEq_one_of_mem_ball hx
  simpa using heq.fderiv_eq (𝕜 := ℝ)

/-- Beyond its outer radius a `ContDiffBump` is identically zero, so its Fréchet derivative
vanishes there. -/
theorem contDiffBump_fderiv_eq_zero_of_rOut_lt_dist {p : WholePlane}
    (b : ContDiffBump p) {x : WholePlane} (hx : b.rOut < dist x p) :
    fderiv ℝ b x = 0 := by
  have hopen : IsOpen {y : WholePlane | b.rOut < dist y p} :=
    isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have hmem : {y : WholePlane | b.rOut < dist y p} ∈ nhds x :=
    hopen.mem_nhds hx
  have heq : (b : WholePlane → ℝ) =ᶠ[nhds x] fun _ ↦ 0 := by
    filter_upwards [hmem] with y hy
    exact b.zero_of_le_dist hy.le
  simpa using heq.fderiv_eq (𝕜 := ℝ)

/-- The actual coordinate derivative of a real scalar profile. -/
def realProfileCoordinateDerivative (f : WholePlane → ℝ)
    (j : Fin 2) (x : WholePlane) : ℝ :=
  fderiv ℝ f x (wholePlaneBasis j)

/-- A Lipschitz real profile has coordinate derivatives bounded by its Lipschitz constant, the
coordinate basis vectors being unit vectors. -/
theorem norm_realProfileCoordinateDerivative_le_of_lipschitz
    {f : WholePlane → ℝ} {C : NNReal} (hf : LipschitzWith C f)
    (j : Fin 2) (x : WholePlane) :
    ‖realProfileCoordinateDerivative f j x‖ ≤ (C : ℝ) := by
  calc
    ‖realProfileCoordinateDerivative f j x‖ ≤
        ‖fderiv ℝ f x‖ * ‖wholePlaneBasis j‖ :=
      (fderiv ℝ f x).le_opNorm _
    _ ≤ (C : ℝ) * ‖wholePlaneBasis j‖ := by
      gcongr
      exact norm_fderiv_le_of_lipschitz ℝ hf
    _ = (C : ℝ) := by
      simp [wholePlaneBasis]

end ConstantCoefficientBackground

end

end FastDynamo
