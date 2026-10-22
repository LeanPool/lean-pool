/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! Bounded linear coordinates generating an affine curve's function
field. Degree preservation and control of exceptional fibers are separate
projection obligations; this module proves the quantified birational input. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The bounded integer moment-curve linear form. -/
def momentCoordinate (K : Type*) [CommRing K] (n k : ℕ) : MvPolynomial (Fin n) K :=
  ∑ j : Fin n, C ((k : K) ^ j.val) * X j

/-- The moment coordinate has total degree at most one. -/
lemma momentCoordinate_degree (K : Type*) [CommRing K] [Nontrivial K] (n k : ℕ) :
    (momentCoordinate K n k).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])

/-- In any field `F` receiving the quotient by `I` compatibly with `K`, the image of the moment
coordinate with parameter `k` is `∑ j, x j * k ^ j`, where `x j` is the image of `X j`. -/
lemma momentCoordinate_fraction {K F : Type*} [Field K] [Field F]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    (k : ℕ) :
    algebraMap (MvPolynomial (Fin n) K ⧸ I) F
      ((Ideal.Quotient.mk I) (momentCoordinate K n k)) =
      ∑ j : Fin n, algebraMap (MvPolynomial (Fin n) K ⧸ I) F
        ((Ideal.Quotient.mk I) (X j)) * (k : F) ^ j.val := by
  simp only [momentCoordinate, map_sum, map_mul, map_pow, map_natCast]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end
end CCDN
