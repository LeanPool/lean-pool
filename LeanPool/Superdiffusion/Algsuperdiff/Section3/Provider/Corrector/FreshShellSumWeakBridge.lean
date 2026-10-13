/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.PDE.DirichletRHS
public import LeanPool.HighContrastHomogenization.Support.PDE.NeumannRHS

/-!
# FreshShellSumWeakBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two weak formulations of `e.def.w` and the potential/solenoidal pair

ABK26, `e.def.w` and `e.corrector.limit.pde`.

The manuscript writes the fresh-shell correctors as the solutions of
`-Delta w = div f` on `cu_K`, once with zero trace and once with the mean-zero
Neumann gauge.  The formalization records this in *two different but equivalent
shapes*:

* the **weak-solution shape** used by the recurrence consumers
  (`Provider/Diffusivity/ApproximateRecurrence/**`,
  `Provider/Diffusivity/Corrector/FreshShellExistence.lean`):
  `IsZeroTraceDirichletRhsWeakSolution 1 U w (-f)` and
  `IsMeanZeroNeumannRhsWeakSolution 1 U w (-f)`;
* the **Helmholtz shape** used by the corrector-limit endpoints
  (`Provider/Corrector/CorrectorLimitNode.lean`,
  `Provider/Corrector/FreshShellCorrectorEnergy.lean`):
  `IsPotentialZeroTraceOn U (grad w)` together with
  `IsSolenoidalOn U (grad w + f)`, respectively `IsPotentialOn U (grad w)`
  together with `IsSolenoidalZeroNormalTraceOn U (grad w + f)`.

This module proves the two shapes equivalent, in both directions, at an
arbitrary carrier `U`.  Nothing here is specific to a cube, to a shell law or
to a model: the content is the first-variation identity read twice.

## Relation to the existing existential forms

`Provider/Corrector/CorrectorLimitNonVacuity.lean` already proves the
*existential* statements
`exists_isPotentialZeroTraceOn_and_isSolenoidalOn_openCubeSet_of_continuous` and
`exists_isPotentialOn_and_isSolenoidalZeroNormalTraceOn_openCubeSet_of_continuous`:
at a continuous forcing on a triadic cube *some* Helmholtz pair exists, obtained
by solving the cube problem and reading its solution in the Helmholtz shape.
Those statements do not help a consumer that already **has** the two correctors
`w_D`, `w_N` -- which is exactly the situation of
`ApproximateRecurrence/LocalizationRecurrenceMesh.lean`, whose
`_of_freshShellCorrectors` form produces them.  This module exports the
statement for a *given* solution, in both directions, at an arbitrary carrier
and without any continuity hypothesis.

## Why the equivalence is not a triviality on the Neumann side

`IsMeanZeroNeumannRhsWeakSolution` tests against `H1MeanZeroFunction U` only,
while `IsSolenoidalZeroNormalTraceOn` tests against **all** of `H1Function U`.
The two agree because subtracting its own average from a test function does not
change its gradient (`H1Function.grad_subAverage`) and proves it in the
mean-zero gauge (`H1Function.meanZeroOn_subAverage`); the enlargement of the
test class therefore costs nothing.  This step needs `U` to carry a finite
volume measure, which is why the Neumann statements alone carry the
`[IsFiniteMeasure (volumeMeasureOn U)]` instance.

## Main results

* `isSolenoidalOn_grad_add_of_isZeroTraceDirichletRhsWeakSolution_one`,
  `isSolenoidalZeroNormalTraceOn_grad_add_of_isMeanZeroNeumannRhsWeakSolution_one`
  -- weak formulation `⟹` solenoidality of the corrected field, in the
  zero-trace Dirichlet gauge and in the mean-zero Neumann gauge respectively.
-/

namespace Algsuperdiff.Section3.Provider.Corrector

open HCPolySupport
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The identity coefficient field -/

/-- The identity matrix acts trivially. -/
private theorem matVecMul_one_eq (v : Vec d) :
    matVecMul (1 : Matrix (Fin d) (Fin d) ℝ) v = v := by
  funext i
  simp [matVecMul, Matrix.one_apply]

/-- The `L²` pairing of a square-integrable field against an `H¹` gradient is
integrable. -/
private theorem integrableOn_pairing {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (phi : H1Function U) :
    IntegrableOn (fun x => vecDot (f x) (phi.grad x)) U :=
  integrableOn_vecDot_of_memVectorL2 hf phi.grad_memVectorL2

/-! ## The Dirichlet shape -/

/-- **Weak zero-trace formulation `⟹` solenoidality of the corrected field.**

If `w` solves `-div (grad w) = div (-f)` in the zero-trace weak sense, then
`grad w + f` is solenoidal against zero-trace test gradients: this is the same
first-variation identity with the two sides collected. -/
theorem isSolenoidalOn_grad_add_of_isZeroTraceDirichletRhsWeakSolution_one
    {U : Set (Vec d)} {w : H10Function U} {f : Vec d → Vec d}
    (hf : MemVectorL2 U f)
    (hw : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) U w (fun x => -f x)) :
    IsSolenoidalOn U (fun x => w.toH1Function.grad x + f x) := by
  intro phi
  have hgradInt : IntegrableOn
      (fun x => vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x)) U :=
    integrableOn_pairing w.toH1Function.grad_memVectorL2 phi.toH1Function
  have hfInt : IntegrableOn (fun x => vecDot (f x) (phi.toH1Function.grad x)) U :=
    integrableOn_pairing hf phi.toH1Function
  have hsplit : (fun x => vecDot (w.toH1Function.grad x + f x) (phi.toH1Function.grad x))
      = fun x => vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x)
        + vecDot (f x) (phi.toH1Function.grad x) := by
    funext x
    exact vecDot_add_left _ _ _
  have hweak := hw phi
  have hleft : ∫ x in U, vecDot (matVecMul (1 : Matrix (Fin d) (Fin d) ℝ)
        (w.toH1Function.grad x)) (phi.toH1Function.grad x) ∂volume
      = ∫ x in U, vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume := by
    simp only [matVecMul_one_eq]
  have hright : ∫ x in U, vecDot (-f x) (phi.toH1Function.grad x) ∂volume
      = -∫ x in U, vecDot (f x) (phi.toH1Function.grad x) ∂volume := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => vecDot_neg_left _ _)
  rw [hleft, hright] at hweak
  rw [hsplit, integral_add hgradInt.integrable hfInt.integrable, hweak]
  ring

/-! ## The Neumann shape -/

section Neumann

variable {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]

/-- Every `H¹` test function is, after subtracting its own average, a mean-zero
test function with the same gradient.  The mean-zero representative is
CoarseGraining's `H1Function.toMeanZero`; only `H1Function.toMeanZero_grad` is
used. -/
private theorem grad_toMeanZero (phi : H1Function U) :
    phi.toMeanZero.toH1Function.grad = phi.grad := by
  funext x
  exact H1Function.toMeanZero_grad phi x

/-- **Weak mean-zero Neumann formulation `⟹` solenoidality with zero normal
trace.**

The enlargement of the test class from the mean-zero gauge to all of `H¹(U)` is
free: subtracting the average of a test function changes neither its gradient
nor the two integrals. -/
theorem isSolenoidalZeroNormalTraceOn_grad_add_of_isMeanZeroNeumannRhsWeakSolution_one
    {w : H1MeanZeroFunction U} {f : Vec d → Vec d}
    (hf : MemVectorL2 U f)
    (hw : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) U w (fun x => -f x)) :
    IsSolenoidalZeroNormalTraceOn U (fun x => w.toH1Function.grad x + f x) := by
  intro phi
  have hgradInt : IntegrableOn
      (fun x => vecDot (w.toH1Function.grad x) (phi.grad x)) U :=
    integrableOn_pairing w.toH1Function.grad_memVectorL2 phi
  have hfInt : IntegrableOn (fun x => vecDot (f x) (phi.grad x)) U :=
    integrableOn_pairing hf phi
  have hsplit : (fun x => vecDot (w.toH1Function.grad x + f x) (phi.grad x))
      = fun x => vecDot (w.toH1Function.grad x) (phi.grad x)
        + vecDot (f x) (phi.grad x) := by
    funext x
    exact vecDot_add_left _ _ _
  have hweak := hw phi.toMeanZero
  rw [grad_toMeanZero phi] at hweak
  have hleft : ∫ x in U, vecDot (matVecMul (1 : Matrix (Fin d) (Fin d) ℝ)
        (w.toH1Function.grad x)) (phi.grad x) ∂volume
      = ∫ x in U, vecDot (w.toH1Function.grad x) (phi.grad x) ∂volume := by
    simp only [matVecMul_one_eq]
  have hright : ∫ x in U, vecDot (-f x) (phi.grad x) ∂volume
      = -∫ x in U, vecDot (f x) (phi.grad x) ∂volume := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => vecDot_neg_left _ _)
  rw [hleft, hright] at hweak
  rw [hsplit, integral_add hgradInt.integrable hfInt.integrable, hweak]
  ring

end Neumann

end

end Algsuperdiff.Section3.Provider.Corrector
