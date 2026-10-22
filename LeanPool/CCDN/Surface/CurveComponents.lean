/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IdealZeroLocus
public import LeanPool.CCDN.Height.Box
public import LeanPool.CCDN.Hilbert.AffineCurveDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Ideal.Height

/-! Named bundles for the curve components of affine surfaces in three-space: an integral
curve of a given degree on a surface, and a positive-degree component of the intersection of
two surfaces. -/

@[expose] public section
namespace CCDN

/-- `I` is an integral affine curve of degree `e` on the surface `f = 0` in affine
three-space: a height-two prime ideal containing `f` whose affine Hilbert function has
slope `e`. -/
structure IsSurfaceCurve (f : CoordinatePolynomial 3) (I : Ideal (CoordinatePolynomial 3))
    (e : ℕ) : Prop where
  /-- The ideal `I` is prime. -/
  isPrime : I.IsPrime
  /-- The ideal `I` has height two, so it defines a curve. -/
  height_eq : I.height = 2
  /-- The curve lies on the surface: `f ∈ I`. -/
  mem : f ∈ I
  /-- The curve has degree `e`. -/
  degree : HasAffineCurveDegree I e

/-- `I` is a curve component, of positive degree `e`, of the intersection of the surfaces
`f = 0` and `g = 0` in affine three-space. -/
structure IsSectionCurve (f g : CoordinatePolynomial 3) (I : Ideal (CoordinatePolynomial 3))
    (e : ℕ) : Prop extends IsSurfaceCurve f I e where
  /-- The curve lies on the second surface: `g ∈ I`. -/
  mem_right : g ∈ I
  /-- The degree `e` is positive. -/
  pos : 0 < e

end CCDN
