/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
public import LeanPool.CCDN.Projection.BoundedLinearElimination
import LeanPool.CCDN.Noether.GenericPlaneStretch
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
Bounded integral linear elimination with integer coefficients.
Scaling the retained coordinates by the nonzero pivot preserves integrality.

A complete bounded elimination step: the contraction stays prime,
retains dimension, and has no larger Hilbert multiplicity.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The linear forms `X (some i) - (b (some i) / b none) * X none`, projecting away the coordinate
`X none` along the direction `b`. -/
def eliminationLinearCoordinates {σ : Type*} (b : Option σ → ℚ) :
    σ → MvPolynomial (Option σ) ℚ :=
  fun i => X (some i) - C (b (some i) / b none) * X none

/-- For a direction `b` with `b none ≠ 0`, the elimination map of the associated linear coordinate
change is the projection by the elimination linear forms of `b`. -/
lemma coordinateEliminationMap_eq_projection {σ : Type*}
    (I : Ideal (MvPolynomial (Option σ) ℚ)) (b : Option σ → ℚ) (hb : b none ≠ 0) :
    coordinateEliminationMap I (hypersurfaceAffineCoordinates 0 b hb) =
      projectionCoordinateMap I (eliminationLinearCoordinates b) := by
  ext i
  rw [coordinateEliminationMap_direction_X]
  simp [projectionCoordinateMap, eliminationLinearCoordinates]

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- The linear forms `b none * X (some i) - b (some i) * X none` with integer coefficients,
projecting away the coordinate `X none` along the integer direction `b`. -/
def integerEliminationCoordinates {σ : Type*} (b : Option σ → ℤ) :
    σ → MvPolynomial (Option σ) ℚ :=
  fun i => C (b none : ℚ) * X (some i) - C (b (some i) : ℚ) * X none

private lemma integerEliminationCoordinates_eq_scale {σ : Type*}
    (b : Option σ → ℤ) (hb : (b none : ℚ) ≠ 0) (i : σ) :
    integerEliminationCoordinates b i =
      C (b none : ℚ) * eliminationLinearCoordinates (fun i => (b i : ℚ)) i := by
  have hh : (b none : ℚ) * ((b (some i) : ℚ) / b none) = b (some i) := by
    field_simp
  dsimp only [integerEliminationCoordinates, eliminationLinearCoordinates]
  rw [mul_sub, ← mul_assoc, ← map_mul, hh]

/-- If the projection by the rational elimination forms of an integer direction `b` with
`b none ≠ 0` is integral, then so is the projection by the integer elimination forms, which differ
by the scalar `b none`. -/
theorem integerEliminationMap_isIntegral {σ : Type*}
    (I : Ideal (MvPolynomial (Option σ) ℚ)) (b : Option σ → ℤ)
    (hb : (b none : ℚ) ≠ 0)
    (hint : (projectionCoordinateMap I
      (eliminationLinearCoordinates (fun i => (b i : ℚ)))).IsIntegral) :
    (projectionCoordinateMap I (integerEliminationCoordinates b)).IsIntegral := by
  let e := variableScaleEquiv ℚ σ (b none : ℚ) hb
  let ψ := projectionCoordinateMap I (eliminationLinearCoordinates (fun i => (b i : ℚ)))
  have he : e.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ e.surjective
  have hcomp := RingHom.IsIntegral.trans e.toRingHom ψ.toRingHom he hint
  have heq : ψ.comp e.toAlgHom = projectionCoordinateMap I (integerEliminationCoordinates b) := by
    ext i
    change ψ (e (X i)) =
      projectionCoordinateMap I (integerEliminationCoordinates b) (X i)
    rw [show e (X i) = C (b none : ℚ) * X i from variableScaleEquiv_X _ hb i]
    change (Ideal.Quotient.mkₐ ℚ I) (aeval
      (eliminationLinearCoordinates (fun i => (b i : ℚ))) (C (b none : ℚ) * X i)) =
        (Ideal.Quotient.mkₐ ℚ I) (aeval (integerEliminationCoordinates b) (X i))
    rw [map_mul, aeval_C, aeval_X, aeval_X, integerEliminationCoordinates_eq_scale b hb,
      algebraMap_eq]
  change (ψ.comp e.toAlgHom).IsIntegral at hcomp
  rwa [heq] at hcomp

end
end CCDN
