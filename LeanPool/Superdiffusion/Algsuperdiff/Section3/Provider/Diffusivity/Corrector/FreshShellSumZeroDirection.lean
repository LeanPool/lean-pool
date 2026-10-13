/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellUniqueness

/-!
# FreshShellSumZeroDirection

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The correctors of `e.def.w` vanish at the zero direction

ABK26, `e.def.w`.

Step 6 of `l.approximate.recurrence.formula#localization` reads the Step-4 and
Step-5 displays at a *single* direction: the Dirichlet leg at `e = 0` and the
Neumann leg at `e' = 0`.  At those branches the manuscript writes the bare
direction in the load slot, whereas the formal load
(`gaugedPrincipalLoadShell`) carries `direction + (grad w)_R`.  The two agree
because the corresponding forcing `-streamForcing c ω n m 0` vanishes
identically, so the corrector's gradient vanishes by **uniqueness** of the weak
solution -- `FreshShellUniqueness`, whose two side conditions (nonempty domain,
uniform ellipticity) are already discharged there.

## What is supplied

* `streamForcing_zero_direction` -- the forcing at direction `0` is the zero
  field.
* `isZeroTraceDirichletRhsWeakSolution_one_zero`,
  `isMeanZeroNeumannRhsWeakSolution_one_zero` -- the zero function solves the
  zero-forcing problem in both gauges.
* `gradToVectorL2_eq_zero_of_isZeroTraceDirichletRhsWeakSolution_streamForcing_zero`,
  `gradToVectorL2_eq_zero_of_isMeanZeroNeumannRhsWeakSolution_streamForcing_zero`
  -- the `L²` gradient of either corrector vanishes at the zero direction.
* `grad_ae_eq_zero_of_isZeroTraceDirichletRhsWeakSolution_streamForcing_zero`,
  `grad_ae_eq_zero_of_isMeanZeroNeumannRhsWeakSolution_streamForcing_zero` --
  the pointwise a.e. form, which is what collapses a cube average of the
  corrector gradient to `0`.

No uniqueness *hypothesis* is introduced: uniqueness is proved upstream and
consumed.  No normalization, scale gate or model field enters; the statements
hold at every triadic cube, every gauge `c`, every sample and every shell pair.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **The fresh-shell forcing at the zero direction is the zero field.** -/
theorem streamForcing_zero_direction (c : ℝ) (omega : Cutoff.ShellSeq d) (n m : ℤ) :
    streamForcing c omega n m (0 : Vec d) = fun _ : Vec d => (0 : Vec d) := by
  funext x
  funext i
  show c * (∑ j, Cutoff.finiteShellIncrement omega n m x i j * (0 : Vec d) j) = 0
  simp

/-- The negated forcing at the zero direction is again the zero field. -/
theorem neg_streamForcing_zero_direction (c : ℝ) (omega : Cutoff.ShellSeq d)
    (n m : ℤ) :
    (fun x => -streamForcing c omega n m (0 : Vec d) x) = fun _ : Vec d => (0 : Vec d) := by
  funext x
  rw [streamForcing_zero_direction]
  funext i
  simp

/-- The zero function is a zero-trace Dirichlet weak solution at zero forcing. -/
theorem isZeroTraceDirichletRhsWeakSolution_one_zero (U : Set (Vec d)) :
    IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) U (0 : H10Function U)
      (fun _ : Vec d => (0 : Vec d)) := by
  intro phi
  have hleft : (fun x => vecDot (matVecMul (1 : Matrix (Fin d) (Fin d) ℝ)
        ((0 : H10Function U).toH1Function.grad x)) (phi.toH1Function.grad x))
      = fun _ : Vec d => (0 : ℝ) := by
    funext x
    show vecDot (matVecMul (1 : Matrix (Fin d) (Fin d) ℝ) (0 : Vec d))
      (phi.toH1Function.grad x) = 0
    simp [matVecMul, vecDot, Matrix.one_apply]
  have hright : (fun x => vecDot (0 : Vec d) (phi.toH1Function.grad x))
      = fun _ : Vec d => (0 : ℝ) := by
    funext x
    simp [vecDot]
  rw [hleft, hright]

/-- The zero function is a mean-zero Neumann weak solution at zero forcing. -/
theorem isMeanZeroNeumannRhsWeakSolution_one_zero (U : Set (Vec d)) :
    IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) U (0 : H1MeanZeroFunction U)
      (fun _ : Vec d => (0 : Vec d)) := by
  intro phi
  have hleft : (fun x => vecDot (matVecMul (1 : Matrix (Fin d) (Fin d) ℝ)
        ((0 : H1MeanZeroFunction U).toH1Function.grad x)) (phi.toH1Function.grad x))
      = fun _ : Vec d => (0 : ℝ) := by
    funext x
    show vecDot (matVecMul (1 : Matrix (Fin d) (Fin d) ℝ) (0 : Vec d))
      (phi.toH1Function.grad x) = 0
    simp [matVecMul, vecDot, Matrix.one_apply]
  have hright : (fun x => vecDot (0 : Vec d) (phi.toH1Function.grad x))
      = fun _ : Vec d => (0 : ℝ) := by
    funext x
    simp [vecDot]
  rw [hleft, hright]

/-- The `L²` gradient of the zero `H¹₀` function vanishes. -/
theorem gradToVectorL2_zero_h10 (U : Set (Vec d)) :
    (0 : H10Function U).toH1Function.gradToVectorL2 = 0 :=
  MemLp.toLp_zero (α := Vec d) (E := Vec d) (p := 2) (μ := volumeMeasureOn U)
    MemLp.zero

/-- The `L²` gradient of the zero mean-zero `H¹` function vanishes. -/
theorem gradToVectorL2_zero_h1MeanZero (U : Set (Vec d)) :
    (0 : H1MeanZeroFunction U).gradToVectorL2 = 0 :=
  MemLp.toLp_zero (α := Vec d) (E := Vec d) (p := 2) (μ := volumeMeasureOn U)
    MemLp.zero

/-- **The Dirichlet corrector vanishes at the zero direction.** -/
theorem gradToVectorL2_eq_zero_of_isZeroTraceDirichletRhsWeakSolution_streamForcing_zero
    (Q : TriadicCube d) (c : ℝ) (omega : Cutoff.ShellSeq d) (n m : ℤ)
    {w : H10Function (openCubeSet Q)}
    (hw : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) w
      (fun x => -streamForcing c omega n m (0 : Vec d) x)) :
    w.toH1Function.gradToVectorL2 = 0 := by
  rw [neg_streamForcing_zero_direction c omega n m] at hw
  rw [gradToVectorL2_eq_of_isZeroTraceDirichletRhsWeakSolution_openCubeSet Q hw
    (isZeroTraceDirichletRhsWeakSolution_one_zero (openCubeSet Q))]
  exact gradToVectorL2_zero_h10 _

/-- **The Neumann corrector vanishes at the zero direction.** -/
theorem gradToVectorL2_eq_zero_of_isMeanZeroNeumannRhsWeakSolution_streamForcing_zero
    (Q : TriadicCube d) (c : ℝ) (omega : Cutoff.ShellSeq d) (n m : ℤ)
    {w : H1MeanZeroFunction (openCubeSet Q)}
    (hw : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) w
      (fun x => -streamForcing c omega n m (0 : Vec d) x)) :
    w.gradToVectorL2 = 0 := by
  rw [neg_streamForcing_zero_direction c omega n m] at hw
  rw [gradToVectorL2_eq_of_isMeanZeroNeumannRhsWeakSolution_openCubeSet Q hw
    (isMeanZeroNeumannRhsWeakSolution_one_zero (openCubeSet Q))]
  exact gradToVectorL2_zero_h1MeanZero _

/-- **The pointwise form, Dirichlet leg.**  This is what collapses a cube
average of the corrector gradient to `0`. -/
theorem grad_ae_eq_zero_of_isZeroTraceDirichletRhsWeakSolution_streamForcing_zero
    (Q : TriadicCube d) (c : ℝ) (omega : Cutoff.ShellSeq d) (n m : ℤ)
    {w : H10Function (openCubeSet Q)}
    (hw : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) w
      (fun x => -streamForcing c omega n m (0 : Vec d) x)) :
    w.toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet Q)] 0 := by
  have hL2 :=
    gradToVectorL2_eq_zero_of_isZeroTraceDirichletRhsWeakSolution_streamForcing_zero
      Q c omega n m hw
  have hcoe := H1Function.coeFn_gradToVectorL2 w.toH1Function
  rw [hL2] at hcoe
  exact hcoe.symm.trans (Lp.coeFn_zero (Vec d) 2 (volumeMeasureOn (openCubeSet Q)))

/-- **The pointwise form, Neumann leg.** -/
theorem grad_ae_eq_zero_of_isMeanZeroNeumannRhsWeakSolution_streamForcing_zero
    (Q : TriadicCube d) (c : ℝ) (omega : Cutoff.ShellSeq d) (n m : ℤ)
    {w : H1MeanZeroFunction (openCubeSet Q)}
    (hw : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) w
      (fun x => -streamForcing c omega n m (0 : Vec d) x)) :
    w.toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet Q)] 0 := by
  have hL2 :=
    gradToVectorL2_eq_zero_of_isMeanZeroNeumannRhsWeakSolution_streamForcing_zero
      Q c omega n m hw
  rw [H1MeanZeroFunction.gradToVectorL2] at hL2
  have hcoe := H1Function.coeFn_gradToVectorL2 w.toH1Function
  rw [hL2] at hcoe
  exact hcoe.symm.trans (Lp.coeFn_zero (Vec d) 2 (volumeMeasureOn (openCubeSet Q)))

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
