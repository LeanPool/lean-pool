/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ClosureAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CorrectorMeasurableGradient

/-!
# ClosureFinalMeasurability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two typing binders of the closure's energy display

ABK26, `e.perturb.assumption` read at the corrector families
`Closure.closureDirichletFamily` and `Closure.closureNeumannFamily` chosen by
`Closure.ClosureAssembly`.

`ClosureAssembly` reduces the drift limit `hlimit` of both assembly skeletons
to the two `AEStronglyMeasurable` binders `hDm`, `hNm` that the proved display
`Corrector.ShellSumEnergyDisplay.tendsto_integral_cutoffSample_cubeAverage_display`
carries, and records that they are "not built here".  This module builds them.

## The chain

The two families are `Classical.choose` selections, so nothing about their
dependence on the path `f` is available from the construction.  What *is*
available is the same fact that
`Corrector.CorrectorMeasurableGradient` uses for the sample carrier: the
gradient of a weak solution is not merely *some* chosen element, it is the value
at the forcing class of the fixed **continuous** solution operator of
`Corrector.MeasurablePrereqSolutionOperator`.  Three steps:

1. `closureForcingL2_eq_contMatrixFieldL2` --- the forcing class of the closure
   families is `Corrector.contMatrixFieldL2` at the direction `(-c) • e`; the
   realization of `valuePathForcing` at a path is the literal matrix-vector
   product, so the two `L^2` classes are the class of one and the same function.
2. `continuous_gradToHilbertVectorL2_closureDirichletFamily` and its Neumann
   mirror --- composing `Corrector.continuous_contMatrixFieldL2` with
   `Corrector.continuous_dirichletGradientOfForcingClass` (resp. the Neumann
   operator) gives continuity of `f |-> grad w(f)` in the `L^2` carrier.
3. `cubeAverage_vecDot_grad_eq_norm_sq` --- the cube energy is the squared
   `L^2` norm of that class, normalized by the cube volume, so it is a
   continuous, hence Borel measurable, hence `AEStronglyMeasurable` function of the path.

## What is supplied

* `aestronglyMeasurable_cubeAverage_closureDirichletFamily`,
  `aestronglyMeasurable_cubeAverage_closureNeumannFamily` --- the binders `hDm`
  and `hNm` of `Closure.tendsto_dirichletCubeEnergy_closureDirichletFamily`,
  `Closure.tendsto_neumannCubeEnergy_closureNeumannFamily` and the two
  conditional assemblies, verbatim.  Discharging them there is what makes those
  drift limits unconditional in the corrector data.

## References

* ABK26, `e.def.w`; `e.perturb.assumption`.
* ABK26 (the fresh-shell measurability parenthetical).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector

noncomputable section

variable {d : ℕ}

/-! ## The forcing class of the closure families -/

open Algsuperdiff.Frozen.Assumptions in
open Algsuperdiff.Section3.Provider.Corrector (realize valuePathForcing
  continuous_toVec_realize_valuePathForcing) in
/-- **The forcing class of the closure's corrector families is the continuous
matrix-field class of `Corrector.CorrectorMeasurableForcing`**, at the direction
`(-c) • e`.

The realization of `valuePathForcing (c • e)` at a continuous path `f` is the
literal matrix-vector product `f(x) (c • e)`, so the two `L^2` classes are the
class of one and the same function; only the membership witnesses differ, and
the class does not depend on those. -/
theorem closureForcingL2_eq_contMatrixFieldL2 (Q : TriadicCube d) (c : ℝ) (e : Vec d)
    (f : C(Vec d, Mat d)) :
    toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          (continuous_toVec_realize_valuePathForcing (c • e) f).neg)
      = contMatrixFieldL2 Q ((-c) • e) f := by
  refine toHilbertVectorL2OfVecField_congr _ _ ?_
  funext x
  show -(realize (valuePathForcing (c • e)) f x).toVec = matVecMul (f x) ((-c) • e)
  show -(HilbertVec.toVec (HilbertVec.ofVec
      (matVecMul (((x +ᵥ f) : C(Vec d, Mat d)) 0) (c • e)))) = _
  rw [HilbertVec.toVec_ofVec, ShellField.vadd_apply, zero_add, matVecMul_smul_right,
    matVecMul_smul_right, neg_smul]

/-! ## Continuity of the two gradient classes in the path -/

/-- **The Dirichlet corrector gradient of the closure family is a continuous
function of the increment path.**

No property of the `Classical.choose` selection is used: the gradient class of
*any* zero-trace weak solution is the value of the continuous Dirichlet solution
operator at the forcing class. -/
theorem continuous_gradToHilbertVectorL2_closureDirichletFamily [NeZero d]
    (c : ℝ) (e : Vec d) (K : ℕ) :
    Continuous fun f : C(Vec d, Mat d) =>
      (closureDirichletFamily c e K f).toH1Function.gradToHilbertVectorL2 := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d (K : ℤ)))) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet _
  have hEq : (fun f : C(Vec d, Mat d) =>
        (closureDirichletFamily c e K f).toH1Function.gradToHilbertVectorL2) =
      (dirichletGradientOfForcingClass
          (PotentialSolenoidalL2Data.ofSubmoduleClosures
            (openCubeSet (originCube d (K : ℤ))))
          (_root_.Algsuperdiff.Section3.Provider.Corrector.nonempty_openCubeSet _)
          (isEllipticFieldOn_const_one_openCubeSet _)) ∘
        contMatrixFieldL2 (originCube d (K : ℤ)) ((-c) • e) := by
    funext f
    show _ = dirichletGradientOfForcingClass _ _ _
      (contMatrixFieldL2 (originCube d (K : ℤ)) ((-c) • e) f)
    rw [← closureForcingL2_eq_contMatrixFieldL2 (originCube d (K : ℤ)) c e f]
    exact gradToHilbertVectorL2_eq_dirichletGradientOfForcingClass _
      (_root_.Algsuperdiff.Section3.Provider.Corrector.hasPotentialZeroTraceClosureRealization_openCubeSet _)
      (_root_.Algsuperdiff.Section3.Provider.Corrector.nonempty_openCubeSet _)
      (isEllipticFieldOn_const_one_openCubeSet _)
      (isZeroTraceDirichletRhsWeakSolution_closureDirichletFamily c e K f)
  rw [hEq]
  exact (continuous_dirichletGradientOfForcingClass _ _ _).comp
    (continuous_contMatrixFieldL2 _ _)

/-- **The Neumann corrector gradient of the closure family is a continuous
function of the increment path.**  The mean-zero mirror of the previous
statement. -/
theorem continuous_gradToHilbertVectorL2_closureNeumannFamily
    (c : ℝ) (e : Vec d) (K : ℕ) :
    Continuous fun f : C(Vec d, Mat d) =>
      (closureNeumannFamily c e K f).gradToHilbertVectorL2 := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d (K : ℤ)))) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet _
  have hEq : (fun f : C(Vec d, Mat d) =>
        (closureNeumannFamily c e K f).gradToHilbertVectorL2) =
      (neumannGradientOfForcingClass (U := openCubeSet (originCube d (K : ℤ)))
          (a := fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (lam := 1) (Lam := 1)
          (translatedCubeMeanZeroH1CoerciveEstimate _)
          (_root_.Algsuperdiff.Section3.Provider.Corrector.nonempty_openCubeSet _)
          (isEllipticFieldOn_const_one_openCubeSet _)) ∘
        contMatrixFieldL2 (originCube d (K : ℤ)) ((-c) • e) := by
    funext f
    show _ = neumannGradientOfForcingClass _ _ _
      (contMatrixFieldL2 (originCube d (K : ℤ)) ((-c) • e) f)
    rw [← closureForcingL2_eq_contMatrixFieldL2 (originCube d (K : ℤ)) c e f]
    exact gradToHilbertVectorL2_eq_neumannGradientOfForcingClass _
      (translatedCubeMeanZeroH1CoerciveEstimate _)
      (_root_.Algsuperdiff.Section3.Provider.Corrector.nonempty_openCubeSet _)
      (isEllipticFieldOn_const_one_openCubeSet _)
      (isMeanZeroNeumannRhsWeakSolution_closureNeumannFamily c e K f)
  rw [hEq]
  exact (continuous_neumannGradientOfForcingClass _ _ _).comp
    (continuous_contMatrixFieldL2 _ _)

/-! ## The cube energy as a continuous functional of the gradient class -/

/-- The cube average of `|grad w|^2` is the squared `L^2` norm of the gradient
class, normalized by the cube volume.  The cube boundary is Lebesgue null, so
the closed-cube average of `cubeAverage` and the open-cube `L^2` norm of the
class agree. -/
theorem cubeAverage_vecDot_grad_eq_norm_sq (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) :
    cubeAverage Q (fun x => vecDot (u.grad x) (u.grad x))
      = (cubeVolume Q)⁻¹ * ‖u.gradToHilbertVectorL2‖ ^ 2 := by
  have hinner := inner_toHilbertVectorL2OfVecField_eq_integral
    (U := openCubeSet Q) u.grad_memVectorL2 u.grad_memVectorL2
  have hnorm : ‖u.gradToHilbertVectorL2‖ ^ 2 =
      ∫ x in openCubeSet Q, vecDot (u.grad x) (u.grad x) ∂volume := by
    rw [← hinner]
    exact (real_inner_self_eq_norm_sq _).symm
  rw [hnorm]
  simp only [cubeAverage]
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]

/-- **The Dirichlet cube energy of the closure family is continuous in the
path.** -/
theorem continuous_cubeAverage_closureDirichletFamily [NeZero d]
    (c : ℝ) (e : Vec d) (K : ℕ) :
    Continuous fun f : C(Vec d, Mat d) =>
      cubeAverage (originCube d (K : ℤ)) fun x =>
        vecDot ((closureDirichletFamily c e K f).toH1Function.grad x)
          ((closureDirichletFamily c e K f).toH1Function.grad x) := by
  have hEq : (fun f : C(Vec d, Mat d) =>
        cubeAverage (originCube d (K : ℤ)) fun x =>
          vecDot ((closureDirichletFamily c e K f).toH1Function.grad x)
            ((closureDirichletFamily c e K f).toH1Function.grad x)) =
      fun f : C(Vec d, Mat d) => (cubeVolume (originCube d (K : ℤ)))⁻¹ *
        ‖(closureDirichletFamily c e K f).toH1Function.gradToHilbertVectorL2‖ ^ 2 :=
    funext fun f => cubeAverage_vecDot_grad_eq_norm_sq _ _
  rw [hEq]
  exact continuous_const.mul
    ((continuous_gradToHilbertVectorL2_closureDirichletFamily c e K).norm.pow 2)

/-- **The Neumann cube energy of the closure family is continuous in the
path.** -/
theorem continuous_cubeAverage_closureNeumannFamily (c : ℝ) (e : Vec d) (K : ℕ) :
    Continuous fun f : C(Vec d, Mat d) =>
      cubeAverage (originCube d (K : ℤ)) fun x =>
        vecDot ((closureNeumannFamily c e K f).toH1Function.grad x)
          ((closureNeumannFamily c e K f).toH1Function.grad x) := by
  have hEq : (fun f : C(Vec d, Mat d) =>
        cubeAverage (originCube d (K : ℤ)) fun x =>
          vecDot ((closureNeumannFamily c e K f).toH1Function.grad x)
            ((closureNeumannFamily c e K f).toH1Function.grad x)) =
      fun f : C(Vec d, Mat d) => (cubeVolume (originCube d (K : ℤ)))⁻¹ *
        ‖(closureNeumannFamily c e K f).gradToHilbertVectorL2‖ ^ 2 :=
    funext fun f => cubeAverage_vecDot_grad_eq_norm_sq _ _
  rw [hEq]
  exact continuous_const.mul
    ((continuous_gradToHilbertVectorL2_closureNeumannFamily c e K).norm.pow 2)

/-! ## The two typing binders -/

open Algsuperdiff.Section3.Provider.Corrector (shellSumValuePathLaw) in
/-- **The binder `hDm` of the closure's energy display, discharged.** -/
theorem aestronglyMeasurable_cubeAverage_closureDirichletFamily [NeZero d]
    (M : ABKModel d) (n : ℤ) (h : ℕ) (e : Vec d) :
    ∀ K : ℕ, AEStronglyMeasurable
      (fun f => cubeAverage (originCube d (K : ℤ))
        fun x => vecDot
          ((closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x)
          ((closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x))
      (shellSumValuePathLaw M.P n (n + (h : ℤ))).toMeasure := fun K =>
  (continuous_cubeAverage_closureDirichletFamily
    ((Annealed.sigmaBar M n : ℝ))⁻¹ e K).measurable.aestronglyMeasurable

open Algsuperdiff.Section3.Provider.Corrector (shellSumValuePathLaw) in
/-- **The binder `hNm` of the closure's energy display, discharged.** -/
theorem aestronglyMeasurable_cubeAverage_closureNeumannFamily
    (M : ABKModel d) (n : ℤ) (h : ℕ) (e : Vec d) :
    ∀ K : ℕ, AEStronglyMeasurable
      (fun f => cubeAverage (originCube d (K : ℤ))
        fun x => vecDot
          ((closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x)
          ((closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K f).toH1Function.grad x))
      (shellSumValuePathLaw M.P n (n + (h : ℤ))).toMeasure := fun K =>
  (continuous_cubeAverage_closureNeumannFamily
    ((Annealed.sigmaBar M n : ℝ))⁻¹ e K).measurable.aestronglyMeasurable

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
