/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Definitions
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.BasicVariationalIdentities
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.CanonicalSolutions.AverageIdentities

/-!
# Carriers

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Carriers for the Section 3.5 negative-norm estimates

This module fixes the deterministic comparison vector used by the negative-norm
lemmas of Section 3.5 of ABK26.

* `coarseScaleSeparation` is the manuscript comparison vector
  `\s_*^{-1}(\cu_m)(q + \k(\cu_m)p) - p`, written literally from the Chapter 2
  coarse matrices.

The single theorem of the file identifies `coarseScaleSeparation` with the
Chapter 4 measurable representative of the whole-cube maximizer gradient
average, which is the manuscript's `e.v.spatial.averages` on this carrier.

## Formalization readings

Two readings are recorded so the correspondence with the manuscript is
unambiguous.

1. *Everything is volume normalized.*  ABK26 writes the Section 3.5 displays
   with normalized averages `\fint_U`, and that is the reading taken here: the
   Chapter 2 normalized average over the domain of a triadic cube is literally
   the cube average of the same cube, which is what
   `ch02_average_cubeDomain_eq_cubeAverage` records.  No factor `|U|`
   separates the two sides of the identity below.
2. *The comparison vector is written from the coarse matrices, not
   reformulated.*  `coarseScaleSeparation` applies `Ch02.sigmaStarInvCoarse`
   and `Ch02.kappaCoarse`, at the coefficient field restricted to `Q`, to the
   pair `(p, q)` exactly as printed.  Its identification with the Chapter 4
   maximizer-gradient average is then a theorem about that literal expression
   rather than a matter of definition.
-/

namespace Algsuperdiff.Section3.Provider.Besov

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The coarse scale-separation vector -/

/-- The manuscript comparison vector `\s_*^{-1}(\cu_m)( q + \k(\cu_m) p ) - p`,
written on the triadic cube `Q` from the Chapter 2 coarse matrices of the
restricted coefficient field. -/
noncomputable def coarseScaleSeparation (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (p q : Vec d) : Vec d :=
  matVecMul
      (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q)
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q))
      (q +
        matVecMul
          (Ch02.kappaCoarse (Ch02.cubeDomain Q)
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q))
          p) -
    p

omit [NeZero d] in
/-- The Chapter 2 normalized average over the domain of a triadic cube is the
cube average. -/
private theorem ch02_average_cubeDomain_eq_cubeAverage (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    Ch02.average (Ch02.cubeDomain Q) f = cubeAverage Q f := by
  unfold Ch02.average cubeAverage
  rw [Ch02.cubeDomain_coe, ← setIntegral_cubeSet_eq_setIntegral_openCubeSet (Q := Q) (f := f),
    volume_openCubeSet_toReal]

/-- **The manuscript identity `e.v.spatial.averages` on this carrier.**  The
Chapter 4 measurable representative of the whole-cube average of the canonical
maximizer gradient is the coarse scale-separation vector of the same cube. -/
theorem coarseScaleSeparation_eq_canonicalScalarResponseGradientAverageCubeSet
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (p q : Vec d) :
    coarseScaleSeparation a ha Q p q =
      Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q a.toFun := by
  have hself : Q ∈ descendantsAtDepth Q 0 := by
    simp [descendantsAtDepth_zero]
  have hAverage :=
    Ch04.canonicalScalarResponseGradientAverageCubeSet_eq_cubeAverageVec_canonicalMaximizer
      a ha hself p q
  have hCoarse :=
    Ch02.averageGradient_canonicalMaximizer_eq (Ch02.cubeDomain Q)
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q
  have hCubeAverage :
      cubeAverageVec Q
          (fun x =>
            (Ch02.canonicalMaximizer
                (Ch02.responseExistenceTheory (Ch02.cubeDomain Q)
                  ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q))
                p q).toSolution.toH1.grad x) =
        Ch02.averageGradient (Ch02.cubeDomain Q)
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
          (Ch02.canonicalMaximizer
              (Ch02.responseExistenceTheory (Ch02.cubeDomain Q)
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q))
              p q).toSolution := by
    funext i
    rw [Ch02.averageGradient, Ch02.averageVec, ch02_average_cubeDomain_eq_cubeAverage]
    rfl
  rw [hAverage, hCubeAverage, hCoarse, coarseScaleSeparation]
  abel

end

end Algsuperdiff.Section3.Provider.Besov
