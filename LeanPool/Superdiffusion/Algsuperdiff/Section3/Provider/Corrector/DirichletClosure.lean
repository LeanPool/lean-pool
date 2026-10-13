/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Geometry.ConvexDomain
public import LeanPool.HighContrastHomogenization.Support.PDE.DirichletRHS
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Realization

/-!
# DirichletClosure

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: zero-trace potential representatives on triadic cubes

`PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U`
  `= ∀ F : VectorL2 U, F ∈ (ofSubmoduleClosures U).potentialZeroTrace →`
      `IsPotentialZeroTraceOn U F`

is the statement that the closure used to build the canonical zero-trace
potential subspace adds no abstract elements, so that every closed `L²`
zero-trace potential class really is the gradient of an `H¹₀` function.

It does, and the two ingredients are both already in CoarseGraining:

*
`hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain`
  (`Homogenization/Sobolev/PotentialSolenoidalL2Realization.lean`), proved from
  the closed-range gradient projection on the `H¹₀` graph; and
* `Homogenization.isOpenBoundedConvexDomain_openCubeSet`
  (`Homogenization/Geometry/ConvexDomain.lean`).

This file records the composition and the unconditional Dirichlet existence it
yields on `cu_K`, which is what the corrector-limit nodes `B3`/`B7` consume.
Note that `HasPotentialZeroTraceClosureRealization` is stated for the *open*
cube; the half-open realization `cubeSet Q` carries the same restricted
Lebesgue measure
(`Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet`) but a
syntactically different `VectorL2` carrier, and CoarseGraining transports
solutions across the two realizations separately.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

variable {d : ℕ}

/-- An open triadic cube is nonempty: its centre lies in it. -/
theorem nonempty_openCubeSet (Q : TriadicCube d) : (openCubeSet Q).Nonempty := by
  have hs : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale
  refine ⟨fun i => (Q.index i : ℝ) * cubeScaleFactor Q, ?_⟩
  simp only [openCubeSet, Set.mem_ofPred_eq]
  intro i
  constructor <;> nlinarith

/-- **Decision D-2, resolved affirmatively.**  Every open triadic cube satisfies
CoarseGraining's zero-trace potential closure realization hypothesis, so no
separate obligation has to be carried through the corrector-limit development. -/
theorem hasPotentialZeroTraceClosureRealization_openCubeSet [NeZero d]
    (Q : TriadicCube d) :
    PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization (openCubeSet Q) :=
  PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_convexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)

/-- Unconditional existence of a zero-trace Dirichlet weak solution of
`-div (a ∇v) = div g` on an open triadic cube.  With `a` the identity
coefficient field and `g := -f` this is the cube problem `w_D^{(K)}` of
ABK26. -/
theorem exists_isZeroTraceDirichletRhsWeakSolution_openCubeSet [NeZero d]
    (Q : TriadicCube d) {a : CoeffField d} {g : Vec d → Vec d} {lam Lam : ℝ}
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    ∃ v : H10Function (openCubeSet Q),
      IsZeroTraceDirichletRhsWeakSolution a (openCubeSet Q) v g := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  exact exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
    (a := a) (U := openCubeSet Q) (g := g) (lam := lam) (Lam := Lam)
    hg (hasPotentialZeroTraceClosureRealization_openCubeSet Q)
    (nonempty_openCubeSet Q) hEll

end Algsuperdiff.Section3.Provider.Corrector
