/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneCoefficientScaling

/-!
# Coordinates of vector-valued tempered distributions on the whole plane

This file defines the coordinate maps `wholePlaneCoordTempered i` from `C3`-valued to scalar
tempered distributions on `ℝ²` and proves that they commute with distributional line
differentiation (`wholePlaneCoordTempered_lineDeriv`) and with the embedding of `L²`
(`wholePlaneCoordTempered_l2`).  They are used to identify the coordinates of weak `H¹` and
`H²` fields.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped LineDeriv SchwartzMap

/-! ## Coordinate maps on vector-valued tempered distributions -/

/-- Extract the `i`-th coordinate of a `C3`-valued tempered distribution. -/
def wholePlaneCoordTempered (i : Fin 3) :
    TemperedDistribution WholePlane C3 →L[ℂ]
      TemperedDistribution WholePlane ℂ :=
  WholePlaneHorizontalFibre.fibreTempered (EuclideanSpace.proj i)

/-- Coordinate extraction is applied after testing: the `i`-th coordinate distribution
evaluated on `f` is the `i`-th component of the vector value `T f`. -/
@[simp] theorem wholePlaneCoordTempered_apply_apply (i : Fin 3)
    (T : TemperedDistribution WholePlane C3)
    (f : SchwartzMap WholePlane ℂ) :
    wholePlaneCoordTempered i T f = (T f) i :=
  rfl

/-- Coordinate extraction commutes with distributional line differentiation. -/
theorem wholePlaneCoordTempered_lineDeriv (i : Fin 3)
    (e : WholePlane) (T : TemperedDistribution WholePlane C3) :
    wholePlaneCoordTempered i (∂_{e} T) =
      ∂_{e} (wholePlaneCoordTempered i T) :=
  WholePlaneHorizontalFibre.fibreTempered_lineDeriv (EuclideanSpace.proj i) e T

/-- Coordinate extraction commutes with the canonical `L² → tempered distribution`
embedding. -/
theorem wholePlaneCoordTempered_l2 (i : Fin 3) (b : WholePlaneC3L2) :
    wholePlaneCoordTempered i (wholePlaneL2ToTempered C3 b) =
      wholePlaneL2ToTempered ℂ (wholePlaneCoordL2 i b) :=
  WholePlaneHorizontalFibre.fibreTempered_l2 (EuclideanSpace.proj i) b

end

end FastDynamo
