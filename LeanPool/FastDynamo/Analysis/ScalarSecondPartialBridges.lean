/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.ScalarSecondPartial
public import LeanPool.FastDynamo.Fourier.PeriodicH2

/-!
# Scalar bridges for two-component fields

The paper's local transverse operator, with diffusion part `(Δ_⊥ - N²) b`
(`eq:horizontal-induction`), acts on `ℂ²`-valued fields, while the polar Laplacian identity in
the proof of `lem:jump-horizontal-mode` is proved one scalar component at a time.  This module
is the bridge: it extracts a component of a `C2` vector as a real-linear continuous map,
transports Fréchet derivatives through that extraction, and identifies a component of the
second Cartesian partial of a locally `C²` two-component field with the scalar second
partial of `Analysis/ScalarSecondPartial.lean`.

Everything here is generic in the fibre index and in the field; no Ponomarenko branch, no
Bessel function and no seed parameter occurs.  The declarations are used by
`Local/HorizontalModeSecondDerivatives.lean`.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace ScalarSecondPartial

/-! ## Scalar bridges for two-component fields -/

/-- Extraction of one of the two components of a `C2` vector as a real-linear continuous map;
used to push Fréchet derivatives of `ℂ²`-valued fields down to their scalar components. -/
def c2ComponentProjection (a : Fin 2) : C2 →L[ℝ] ℂ :=
  (EuclideanSpace.proj (𝕜 := ℂ) a).restrictScalars ℝ

/-- The two-component projection evaluates a `C2` vector at the given index. -/
@[simp] theorem c2ComponentProjection_apply (a : Fin 2) (b : C2) :
    c2ComponentProjection a b = b a :=
  rfl

/-- Differentiating a `C2`-valued map componentwise agrees with taking the component of its
Fréchet derivative, at any point of differentiability. -/
theorem fderiv_c2_component_apply
    {F : WholePlane → C2} {y : WholePlane} (hF : DifferentiableAt ℝ F y)
    (a : Fin 2) (v : WholePlane) :
    fderiv ℝ (fun x : WholePlane ↦ F x a) y v = fderiv ℝ F y v a := by
  have hcomp := (c2ComponentProjection a).hasFDerivAt.comp y hF.hasFDerivAt
  have hcomp' : HasFDerivAt (fun x : WholePlane ↦ F x a)
      ((c2ComponentProjection a).comp (fderiv ℝ F y)) y := by
    convert! hcomp using 1
  rw [hcomp'.fderiv]
  rfl

/-- A component of a differentiable `C2`-valued field has the corresponding component of the
Fréchet derivative as its own derivative. -/
theorem hasFDerivAt_c2_component
    {F : WholePlane → C2} {F' : WholePlane →L[ℝ] C2} {y : WholePlane}
    (hF : HasFDerivAt F F' y) (a : Fin 2) :
    HasFDerivAt (fun x : WholePlane ↦ F x a) ((c2ComponentProjection a).comp F') y := by
  have hcomp := (c2ComponentProjection a).hasFDerivAt.comp y hF
  convert! hcomp using 1

/-- Evaluating the component of a differential: `((π_a ∘ F') v) = F' v a`. -/
@[simp] theorem c2ComponentProjection_comp_apply
    (a : Fin 2) (F' : WholePlane →L[ℝ] C2) (v : WholePlane) :
    (c2ComponentProjection a).comp F' v = F' v a :=
  rfl

/-- A component of the second Cartesian partial of a locally `C²` two-component field
is the corresponding scalar second partial of `PonomarenkoCartesianPolarLaplacian`. -/
theorem c2SecondPartial_apply_eq_scalarSecondPartial
    {F : WholePlane → C2} {y : WholePlane} (hF : ContDiffAt ℝ 2 F y)
    (j k : Fin 2) (a : Fin 2) :
    fderiv ℝ (fun x : WholePlane ↦ fderiv ℝ F x (wholePlaneBasis j)) y
          (wholePlaneBasis k) a =
      scalarSecondPartial (fun x : WholePlane ↦ F x a) j k y := by
  let G : WholePlane → C2 := fun x ↦ fderiv ℝ F x (wholePlaneBasis j)
  have hGcont : ContDiffAt ℝ 1 G y :=
    (hF.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hGdiff : DifferentiableAt ℝ G y := hGcont.differentiableAt (by norm_num)
  have hevent :
      (fun x : WholePlane ↦ G x a) =ᶠ[nhds y]
        fun x : WholePlane ↦
          fderiv ℝ (fun z : WholePlane ↦ F z a) x (wholePlaneBasis j) := by
    filter_upwards [hF.eventually (by norm_num)] with x hx
    exact (fderiv_c2_component_apply
      (hx.differentiableAt (by norm_num)) a (wholePlaneBasis j)).symm
  unfold scalarSecondPartial
  change fderiv ℝ G y (wholePlaneBasis k) a = _
  rw [← fderiv_c2_component_apply hGdiff a (wholePlaneBasis k), hevent.fderiv_eq]

end ScalarSecondPartial

end FastDynamo

end
