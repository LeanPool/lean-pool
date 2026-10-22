/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.CCDN.ForMathlib.SchwartzZippel

/-! The polynomial zero bound on the full affine parameter space, with its
field-size saving retained in multiplicative form. This is the Schwartz–Zippel
lemma `MvPolynomial.schwartz_zippel_totalDegree_card` applied to the whole finite field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Schwartz--Zippel for an arbitrary finite coordinate type. -/
theorem finite_field_polynomial_zeros_mul_card {K τ : Type*} [Field K] [Fintype K]
    [Fintype τ] (f : MvPolynomial τ K) (hf : f ≠ 0) :
    Nat.card {x : τ → K // eval x f = 0} * Fintype.card K ≤
      f.totalDegree * Fintype.card K ^ Fintype.card τ := by
  classical
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    schwartz_zippel_totalDegree_card hf (Finset.univ : Finset K)

end
end CCDN
