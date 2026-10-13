/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicReplaceBridge
public import LeanPool.HighContrastHomogenization.Support.Ambient.ScalarMatrix
public import LeanPool.HighContrastHomogenization.Support.Geometry.ConvexDomain
public import LeanPool.HighContrastHomogenization.Support.PDE.DirichletRHS
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Realization

/-!
# HarmonicReplaceDirichlet

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The Laplace-Dirichlet solve with divergence-form right-hand side

The harmonic replacement of a function on a cube is obtained by subtracting the
`H^1_0` solution of a Dirichlet problem whose forcing is the *whole* right-hand
side of the equation the function solves.  The only elliptic solve the argument
needs is therefore the one at the **identity coefficient field**:

```
  - Delta phi = div g  in  U ,   phi in H^1_0 (U) ,
```

in the weak form `int_U <grad phi, grad psi> = int_U <g, grad psi>` for every
`psi in H^1_0 (U)`.

CoarseGraining proves the general divergence-form Dirichlet solvability
`exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization`
conditionally on `HasPotentialZeroTraceClosureRealization U`, and discharges
that condition on every bounded open convex domain
(`hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain`).  This
module composes the two at the scalar coefficient field `1`, where the flux
`matVecMul (scalarMatrix 1) v` is `v` itself, and states the result in the
gradient-pairing form the harmonic replacement consumes.

The `a = 1` case is re-derived here **directly from CoarseGraining**; nothing
from the manuscript-facing `Provider/Corrector/DirichletClosure.lean` (which is
ABK-specific and restricted to triadic cubes) is used, so the domain class is
the general one and the file stays portable.

## Contents

* `isEllipticFieldOn_one` -- the constant identity coefficient field is elliptic
  with `lam = Lam = 1` on every measurable set.
* `exists_h10Function_integral_vecDot_grad_eq` -- **the solve**: on a nonempty
  bounded open convex domain, every `L^2` forcing field admits an `H^1_0`
  potential whose Dirichlet pairing against every `H^1_0` competitor reproduces
  the pairing of the forcing.

## Portability

This file depends only on **Mathlib**, on **CoarseGraining**
(`Homogenization.*`) and on the harmonic layer of this same directory.  It
mentions no object of the manuscript: no model, no cutoff, no shell, no
corrector, no `sigmaBar`.  It is intended to be portable into CoarseGraining by
a single mechanical namespace rename.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

variable {d : ℕ}

/-- The constant identity coefficient field is elliptic with `lam = Lam = 1` on
every measurable set. -/
theorem isEllipticFieldOn_one {U : Set (Vec d)} (hU : MeasurableSet U) :
    IsEllipticFieldOn 1 1 U (fun _ => scalarMatrix (d := d) (1 : ℝ)) := by
  classical
  refine ⟨?_, fun x _ => isEllipticMatrix_scalarMatrix (by norm_num)⟩
  refine (measurable_pi_iff).2 fun i => (measurable_pi_iff).2 fun j => ?_
  have hpiece :
      Measurable (U.piecewise (fun _ : Vec d => (scalarMatrix (d := d) (1 : ℝ)) i j)
        (fun _ => 0)) :=
    measurable_const.piecewise hU measurable_const
  simpa [Set.piecewise] using! hpiece

/-- **The Laplace-Dirichlet solve with divergence-form right-hand side.**

On a nonempty bounded open convex domain `U`, every `L^2` vector field `g`
admits an `H^1_0 (U)` potential `phi` with

```
  int_U <grad phi, grad psi> = int_U <g, grad psi>   for every  psi in H^1_0 (U) .
```

This is CoarseGraining's conditional Dirichlet solvability at the scalar
coefficient field `1`, with the closure-realization hypothesis discharged by
CoarseGraining's bounded open convex realization theorem. -/
theorem exists_h10Function_integral_vecDot_grad_eq [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) :
    ∃ φ : H10Function U, ∀ ψ : H10Function U,
      ∫ x in U, vecDot (φ.toH1Function.grad x) (ψ.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (g x) (ψ.toH1Function.grad x) ∂volume := by
  have : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  obtain ⟨φ, hφ⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := fun _ => scalarMatrix (d := d) (1 : ℝ)) (U := U) (g := g) (lam := 1) (Lam := 1)
      hg
      (PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_convexDomain
        hU)
      hne (isEllipticFieldOn_one hU.isOpen.measurableSet)
  refine ⟨φ, fun ψ => ?_⟩
  have hflux : ∀ v : Vec d, matVecMul (scalarMatrix (d := d) (1 : ℝ)) v = v := by
    intro v
    rw [matVecMul_scalarMatrix, one_smul]
  have hpair := hφ ψ
  simpa only [hflux] using hpair

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
