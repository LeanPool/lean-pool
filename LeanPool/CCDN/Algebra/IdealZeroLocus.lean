/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Defs

/-! The zero locus of an ideal of multivariate polynomials, with coordinates in the
coefficient ring. Over a field `K` this is Mathlib's `MvPolynomial.zeroLocus K I`,
stated with `eval` rather than `aeval`; that definition is reserved for points with
coordinates in an extension field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The common zeros, with coordinates in the coefficient ring, of all polynomials in `I`. -/
def idealZeroLocus {K σ : Type*} [CommRing K] (I : Ideal (MvPolynomial σ K)) : Set (σ → K) :=
  {x | ∀ f ∈ I, eval x f = 0}

end
end CCDN
