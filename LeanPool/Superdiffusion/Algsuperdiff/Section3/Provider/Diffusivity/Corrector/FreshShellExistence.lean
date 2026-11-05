/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.DirichletClosure
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellL8
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.PublicTheorems
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCoerciveH1

/-!
# FreshShellExistence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open _root_.Algsuperdiff.Section3.Provider.Corrector
  (exists_isZeroTraceDirichletRhsWeakSolution_openCubeSet)

/-!
# Existence of the two correctors of `e.def.w`

ABK26 introduces, on the large cube `cu_K`, the two perturbative correctors

```
  { -Delta w_D = div (shom_{m-h}^{-1} h e)   in cu_K ,
  {  w_D = 0                                 on d cu_K ,
  { -Delta w_N = div (shom_{m-h}^{-1} h e')  in cu_K ,
  {  n . (grad w_N + shom_{m-h}^{-1} h e') = 0  on d cu_K ,
```

with `w_D in H^1_0(cu_K)` and `w_N in H^1(cu_K)`, and simply says "let. be the
solutions".  Everything downstream of `e.def.w` -- in particular the display
`e.nablaw.in.L.eight` -- is stated for those solutions.

The estimates in `FreshShellCZ` and `FreshShellL8` are *universally quantified*
over such solutions, which is the correct and stronger form for an estimate but
carries no information on a parameter range where no solution exists.  This
module supplies the missing side: for the actual fresh-shell forcing, on the
actual cube, in the actual carriers, a solution of each problem exists.

## What is proved here

* `exists_isZeroTraceDirichletRhsWeakSolution_openCubeSet_of_continuous` and
  `exists_isMeanZeroNeumannRhsWeakSolution_openCubeSet_of_continuous`: on every
  triadic cube and for every continuous forcing, the constant-coefficient
  Laplacian has a zero-trace Dirichlet weak solution and a mean-zero Neumann
  weak solution.
* `exists_isZeroTraceDirichletRhsWeakSolution_streamForcing` and
  `exists_isMeanZeroNeumannRhsWeakSolution_streamForcing`: the same two
  statements at the fresh-shell forcing `streamForcing`, i.e. exactly the two
  problems `e.def.w`.

Nothing here is conditional on a caller-supplied solvability hypothesis: the two
existence statements take only the cube, the forcing, and its continuity.

## Method

Both legs are the standard variational argument, and CoarseGraining already
carries it:

* Dirichlet:
`Homogenization.exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization`,
  whose closure-realization hypothesis is discharged on any bounded open convex
  set by
`hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain`,
  and an open triadic cube is such a set.
* Neumann: `Homogenization.exists_isMeanZeroNeumannRhsWeakSolution_of_h1CoerciveEstimate`,
  whose coercivity hypothesis is the Poincare-Wirtinger datum
  `Homogenization.H1CoerciveEstimate`, discharged on every triadic cube by
  `Homogenization.translatedCubeMeanZeroH1CoerciveEstimate`.

The only genuinely local obligations are that the ambient constant field
`fun _ => (1 : Mat d)` is elliptic on the cube, and that a continuous forcing is
square integrable there.

## References

* ABK26, `e.def.w` (the two corrector problems).
* ABK26, `e.recurrence.params` (the parameter ranges; note that existence needs
  none of them).
* `FreshShellL8.lean` (`streamForcing`, and the display whose solutions these
  are).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

noncomputable section



variable {d : ℕ}

/-! ## The ambient constant coefficient field -/

/-- CoarseGraining's `identityCoeffField` is the constant field with value the
identity matrix, which is the coefficient field the two problems `e.def.w`
carry. -/
theorem identityCoeffField_eq_const_one (d : ℕ) :
    identityCoeffField d = fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ) := by
  funext x
  simp [identityCoeffField, scalarMatrix]

/-- The Laplacian's coefficient field is uniformly elliptic on every open
triadic cube, with both constants equal to `1`. -/
theorem isEllipticFieldOn_const_one_openCubeSet (Q : TriadicCube d) :
    IsEllipticFieldOn 1 1 (openCubeSet Q)
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  have h := isEllipticFieldOn_identityCoeffField (d := d) (U := openCubeSet Q)
    (measurableSet_openCubeSet Q)
  rwa [identityCoeffField_eq_const_one d] at h

/-- A continuous field is square integrable on an open triadic cube. -/
theorem memVectorL2_openCubeSet_of_continuous (Q : TriadicCube d)
    {g : Vec d → Vec d} (hg : Continuous g) :
    MemVectorL2 (openCubeSet Q) g :=
  memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q
    (memLp_normalizedCubeMeasure_of_continuous Q 2 hg)

/-- An open triadic cube carries a finite volume measure. -/
theorem isFiniteMeasure_volumeMeasureOn_openCubeSet (Q : TriadicCube d) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
  simpa [volumeMeasureOn] using
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-! ## Existence for a continuous forcing -/

/-- **Existence, Dirichlet leg of `e.def.w`.**

On every triadic cube and for every continuous forcing `g`, the zero-trace
Dirichlet problem for the constant-coefficient Laplacian has a weak solution in
`H^1_0`.  In the sign convention of the CoarseGraining weak-solution
predicates, taking `g = fun x => -f x` is the weak form of `-Delta w = div f`.

The variational content is the repository's own
`Algsuperdiff.Section3.Provider.Corrector.exists_isZeroTraceDirichletRhsWeakSolution_openCubeSet`,
which is already unconditional on an open triadic cube; only the two ambient
inputs -- ellipticity of the Laplacian's coefficient field and square
integrability of a continuous forcing -- are supplied here. -/
theorem exists_isZeroTraceDirichletRhsWeakSolution_openCubeSet_of_continuous
    [NeZero d] (Q : TriadicCube d) {g : Vec d → Vec d} (hg : Continuous g) :
    ∃ wD : H10Function (openCubeSet Q),
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) wD g :=
  exists_isZeroTraceDirichletRhsWeakSolution_openCubeSet
    Q (memVectorL2_openCubeSet_of_continuous Q hg)
    (isEllipticFieldOn_const_one_openCubeSet Q)

/-- **Existence, Neumann leg of `e.def.w`.**

On every triadic cube and for every continuous forcing `g`, the Neumann problem
for the constant-coefficient Laplacian has a weak solution in the mean-zero
`H^1` gauge.  The manuscript's conormal boundary condition
`n . (grad w_N + f) = 0` is the natural boundary condition of the weak
formulation, and `H^1(cu_K)` is normalized by the mean-zero gauge, which does
not change the gradient.

The proof is CoarseGraining's variational solvability in the mean-zero
subspace; its coercivity input is the Poincare-Wirtinger datum on the cube,
which CoarseGraining proves for every triadic cube, so the statement is
unconditional. -/
theorem exists_isMeanZeroNeumannRhsWeakSolution_openCubeSet_of_continuous
    (Q : TriadicCube d) {g : Vec d → Vec d} (hg : Continuous g) :
    ∃ wN : H1MeanZeroFunction (openCubeSet Q),
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) wN g := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact exists_isMeanZeroNeumannRhsWeakSolution_of_h1CoerciveEstimate
    (lam := 1) (Lam := 1)
    (memVectorL2_openCubeSet_of_continuous Q hg)
    (translatedCubeMeanZeroH1CoerciveEstimate Q)
    (Book.Ch02.openCubeSet_nonempty Q)
    (isEllipticFieldOn_const_one_openCubeSet Q)

/-! ## Existence at the fresh-shell forcing: the two problems `e.def.w` -/

/-- **The Dirichlet corrector `w_{D,e}^{(K)}` of `e.def.w` exists.**

At the fresh-shell forcing `shom^{-1} (k_m - k_n) e`, on the cube `cu_K`, in
the exact carrier the display `e.nablaw.in.L.eight` quantifies over.  No
parameter constraint is needed. -/
theorem exists_isZeroTraceDirichletRhsWeakSolution_streamForcing [NeZero d]
    (Q : TriadicCube d) (sigmaInv : ℝ) (omega : Cutoff.ShellSeq d) (n m : ℤ)
    (e : Vec d) :
    ∃ wD : H10Function (openCubeSet Q),
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) wD
        (fun x => -streamForcing sigmaInv omega n m e x) :=
  exists_isZeroTraceDirichletRhsWeakSolution_openCubeSet_of_continuous Q
    (continuous_streamForcing sigmaInv omega n m e).neg

/-- **The Neumann corrector `w_{N,e'}^{(K)}` of `e.def.w` exists.**

At the fresh-shell forcing `shom^{-1} (k_m - k_n) e'`, on the cube `cu_K`, in
the exact carrier the display `e.nablaw.in.L.eight` quantifies over.  No
parameter constraint is needed. -/
theorem exists_isMeanZeroNeumannRhsWeakSolution_streamForcing
    (Q : TriadicCube d) (sigmaInv : ℝ) (omega : Cutoff.ShellSeq d) (n m : ℤ)
    (e : Vec d) :
    ∃ wN : H1MeanZeroFunction (openCubeSet Q),
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) wN
        (fun x => -streamForcing sigmaInv omega n m e x) :=
  exists_isMeanZeroNeumannRhsWeakSolution_openCubeSet_of_continuous Q
    (continuous_streamForcing sigmaInv omega n m e).neg

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
