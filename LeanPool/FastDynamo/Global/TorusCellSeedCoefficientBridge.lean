/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.MatchingCellScalingParameters
public import LeanPool.FastDynamo.Global.TorusHelicalSource

/-!
# Exact coefficient identification for a placed helical cell

The Euclidean source used to build the torus velocity and the coefficient
package used by the exact whole-plane conjugation are two presentations of
the same rescaled helical profile.  This file identifies their pointwise representatives,
for the value (`parameterizedHelicalCellSource_eq_affineRepresentative`) and for the first
derivatives (`parameterizedHelicalCellSourceDeriv_eq_affineRepresentative`); both hold by
definition.

The equalities are global on the Euclidean chart.  Consequently no
`3R/4`-buffer hypothesis is needed at this layer; that geometric restriction
enters only when the representative is compared with the periodized torus
velocity and the other cells are eliminated.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}

/-! ## Generic affine identities -/

/-- Reassembling a whole-plane point from its two coordinates returns the point itself:
`pairToWholePlane (y 0, y 1) = y`. -/
@[simp] theorem pairToWholePlane_coordinatePair (y : WholePlane) :
    pairToWholePlane (y 0, y 1) = y := by
  ext i
  fin_cases i <;> simp

/-- Pointwise value identity between the concrete Euclidean cell source and
the representative underlying the rescaled whole-plane coefficients. -/
theorem parameterizedHelicalCellSource_eq_affineRepresentative
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) (x : ℝ × ℝ) :
    parameterizedHelicalCellSource h P angularSpeed axialSpeed n x =
      (P.scaleFamily.ell n : ℂ) •
        parameterizedSmoothedVelocity h angularSpeed axialSpeed
          (wholePlaneAffine
            (pairToWholePlane (P.scaleFamily.cellCenter n))
            (P.scaleFamily.ell n) (pairToWholePlane x)) := by
  rfl

/-- Pointwise first-derivative identity between the concrete Euclidean cell
source and the representative underlying the stored rescaled gradient. -/
theorem parameterizedHelicalCellSourceDeriv_eq_affineRepresentative
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) (j : Fin 2) (x : ℝ × ℝ) :
    parameterizedHelicalCellSourceDeriv
        h P angularSpeed axialSpeed n j x =
      (∂_{wholePlaneBasis j}
        (parameterizedSmoothedVelocity h angularSpeed axialSpeed))
          (wholePlaneAffine
            (pairToWholePlane (P.scaleFamily.cellCenter n))
            (P.scaleFamily.ell n) (pairToWholePlane x)) := by
  rfl

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
