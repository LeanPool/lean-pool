/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.NuIdentification
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EquationRestriction
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CoefficientFamily

/-!
# HomBridgeDirichlet

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 2: the `ν`-drop and the Dirichlet carrier entry

## The two obstructions closed here

The obstructions (1) and (2) of Step 2.

**(1) THE `ν`-DROP** ("the left-hand side
`ν^{1/2}‖∇u‖_{L²}` is the symmetric-coefficient energy for `a_L = ν Id + κ`").
`CoarseGraining` prices a Dirichlet solution by `h1EnergyNormOnCube`, i.e. by the square root
of the SYMMETRIC-part energy `⨍_□ ∇u · symm(a) ∇u`.  Step 2's display carries
`ν^{1/2}‖∇u‖_{L²(□_m)}`.  The two agree because `symm(a_L) = ν Id` exactly:
the cutoff field is `ν Id + κ_L` with `κ_L` skew.

Already available (adapted, not re-derived): `Cutoff.symmPart_coefficientCutoff`
(the pointwise identity at the FIELD), `localizedCoeffEnergyValue_eq_mul_of_
symmPart_eq` (the generic drop), and the drops at the flux-corrected and
parent-rebased families.  MISSING and supplied here: the drop at the TRIADIC
FAMILY `Cutoff.coefficientCutoffTriadicCoeffFamily`, which is the family a
`Ch03.DirichletForcedCubeSolution` is indexed by, together with the `√`-split
that produces the printed `ν^{1/2} · ‖∇u‖_{L²}` product rather than
`√(ν · ⨍|∇u|²)`.

**(2) THE CARRIER ENTRY.**  `Support.IsDirichletSolutionOn a Q u h g` (the §4.3
carrier, a conjunction) versus `Ch03.DirichletForcedCubeSolution Q A g` (`CoarseGraining`'s
structure, the object `energyConsequencesRHSTheory` prices).  The structure map
is supplied here in the direction the chain consumes:

* `dirichletForcedCubeSolutionOfIsDirichletSolutionOn` — the entry, at the
  NEGATED forcing.

The exit direction is not stated.  Its boundary half does not come back:
`CoarseGraining`'s zero-trace field is a.e. while the §4.3 carrier's is exact, so
that direction cannot recover the pointwise witness.

## Sign convention (the only subtlety)

`Support.IsDivFormWeakSolutionOn` renders `-∇·a∇u = ∇·g` as
`∫ a∇u·∇φ = -∫ g·∇φ` (the distributional convention), while `CoarseGraining`'s
`Ch03.IsForcedEquation` renders the same equation as `∫ a∇u·∇φ = +∫ g·∇φ`.  The
two therefore correspond at the negated forcing, exactly as
`Support/Dirichlet.lean`'s module docstring records for the sibling zero-trace
surface.  The entry map produced here lands in
`DirichletForcedCubeSolution Q A (fun x => -g x)`.  Every Step-2 leg is a
SEMINORM of the datum, invariant under `g ↦ -g`, so the display is unaffected;
the negation is nevertheless carried visibly and never absorbed.

## The boundary witness

`Support.HasZeroTraceDifferenceOn` carries the `H¹₀` witness with POINTWISE
identities `u = h + w`, `∇u = ∇h + ∇w`; `CoarseGraining`'s
`zeroTraceDifference` field asks only for `w =ᵐ u - h` on the cube.  The entry
map therefore only weakens, via `Filter.Eventually.of_forall`; nothing is
assumed.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 2. The Dirichlet carrier entry -/

/-- **The carrier entry.**  A §4.3 Dirichlet solution `u` of `-∇·A∇u = ∇·g` with
boundary datum `h` IS a `CoarseGraining` `DirichletForcedCubeSolution` for the same `u` and
the same `h`, at the negated forcing.

The four fields: `toH1:= u`; `boundaryData:= h`; `weakSolution` is the
sign-convention converter; `zeroTraceDifference` is the §4.3 witness weakened
from pointwise to a.e.  No analytic content, no existence claim. -/
def dirichletForcedCubeSolutionOfIsDirichletSolutionOn {Q : TriadicCube d}
    {A : CoeffFamily d} {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hsol : IsDirichletSolutionOn ((A.coeffOn Q).toCoeffField) Q u h g) :
    DirichletForcedCubeSolution Q A (fun x => -g x) where
  toH1 := u
  boundaryData := h
  weakSolution := isForcedEquation_neg_of_isDivFormWeakSolutionOn hsol.2
  zeroTraceDifference := by
    obtain ⟨w, hval, _⟩ := hsol.1
    refine ⟨w, Filter.Eventually.of_forall fun x => ?_⟩
    simp only [hval x]
    ring

@[simp]
theorem dirichletForcedCubeSolutionOfIsDirichletSolutionOn_toH1 {Q : TriadicCube d}
    {A : CoeffFamily d} {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hsol : IsDirichletSolutionOn ((A.coeffOn Q).toCoeffField) Q u h g) :
    (dirichletForcedCubeSolutionOfIsDirichletSolutionOn hsol).toH1 = u := rfl

@[simp]
theorem dirichletForcedCubeSolutionOfIsDirichletSolutionOn_boundaryData {Q : TriadicCube d}
    {A : CoeffFamily d} {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hsol : IsDirichletSolutionOn ((A.coeffOn Q).toCoeffField) Q u h g) :
    (dirichletForcedCubeSolutionOfIsDirichletSolutionOn hsol).boundaryData = h := rfl

end

end Algsuperdiff.Section4.Provider.Homogenization
