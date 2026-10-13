/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellExistence

/-!
# FreshShellUniqueness

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Uniqueness of the two correctors of `e.def.w`

ABK26 writes "let `w_D` and `w_N` be *the* solutions" of the two perturbative
problems `e.def.w`, i.e. it asserts uniqueness as well as existence.
`FreshShellExistence` supplies existence; this module supplies the uniqueness
half, in the only form the manuscript ever uses it.

Uniqueness holds at the level of the G, not of the function.  That is the
correct statement in both gauges and is not a weakening: the Dirichlet problem
determines its solution outright, but the Neumann problem determines it only up
to an additive constant, and `H1MeanZeroFunction` already quotients that
constant away.  Every downstream consumer -- `e.nablaw.in.L.eight` and the
displays it feeds -- reads only `grad w_D` and `grad w_N`, so gradient
uniqueness is exactly what "the solutions" needs to mean.

## What is proved here

* `gradToVectorL2_eq_of_isZeroTraceDirichletRhsWeakSolution_openCubeSet`
* `gradToVectorL2_eq_of_isMeanZeroNeumannRhsWeakSolution_openCubeSet`

Both are specializations of CoarseGraining's general uniqueness theorems to the
ambient Laplacian on an open triadic cube; the two side conditions those
theorems carry -- nonemptiness of the domain and uniform ellipticity of the
coefficient field -- are discharged here from
`Algsuperdiff.Section3.Provider.Corrector.nonempty_openCubeSet` and
`isEllipticFieldOn_const_one_openCubeSet`, so neither appears as a hypothesis.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **Uniqueness, Dirichlet leg of `e.def.w`.**

Two zero-trace Dirichlet weak solutions of the ambient Laplacian on an open
triadic cube, for the same forcing, have the same gradient.

The ellipticity and nonemptiness side conditions of the general CoarseGraining
theorem are discharged internally, so this statement carries neither. -/
theorem gradToVectorL2_eq_of_isZeroTraceDirichletRhsWeakSolution_openCubeSet
    (Q : TriadicCube d) {g : Vec d → Vec d} {u v : H10Function (openCubeSet Q)}
    (hu : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) u g)
    (hv : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) v g) :
    u.toH1Function.gradToVectorL2 = v.toH1Function.gradToVectorL2 :=
  IsZeroTraceDirichletRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
    (Algsuperdiff.Section3.Provider.Corrector.nonempty_openCubeSet Q) hu hv
    (isEllipticFieldOn_const_one_openCubeSet Q)

/-- **Uniqueness, Neumann leg of `e.def.w`.**

Two mean-zero Neumann weak solutions of the ambient Laplacian on an open triadic
cube, for the same forcing, have the same gradient.  The additive constant the
Neumann problem leaves free is already quotiented away by
`H1MeanZeroFunction`. -/
theorem gradToVectorL2_eq_of_isMeanZeroNeumannRhsWeakSolution_openCubeSet
    (Q : TriadicCube d) {g : Vec d → Vec d}
    {u v : H1MeanZeroFunction (openCubeSet Q)}
    (hu : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) u g)
    (hv : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) v g) :
    u.gradToVectorL2 = v.gradToVectorL2 :=
  haveI := isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  IsMeanZeroNeumannRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
    (Algsuperdiff.Section3.Provider.Corrector.nonempty_openCubeSet Q) hu hv
    (isEllipticFieldOn_const_one_openCubeSet Q)

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
