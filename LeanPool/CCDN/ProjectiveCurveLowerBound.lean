/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ProjectiveSection
public import LeanPool.CCDN.Height.ProjectiveZeroLocus
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import LeanPool.CCDN.LowerBound.ProjectivePlaneLowerBound
import LeanPool.CCDN.Plane.ProjectivePlaneBezout

/-! CCDN Proposition 5 with its exact constant 1/5, for an absolutely
irreducible projective plane equation. The principal ideal is prime and its
projective Hilbert degree is the prescribed degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The lower-bound equation defines an integral homogeneous plane curve
whose degree is also certified by the projective Hilbert function. -/
theorem projective_integral_curve_lower_bound (d : ℕ) (hd : 0 < d) :
    ∃ F : MvPolynomial (Fin 3) ℚ, ∃ B : ℕ, 1 ≤ B ∧
      F.IsHomogeneous d ∧ F.totalDegree = d ∧
        AbsolutelyIrreducibleRat F ∧
          (Ideal.span {F}).IsPrime ∧ HasProjectiveCurveDegree (Ideal.span {F}) d ∧
            ((d : ℝ) ^ 2 / 5) * (B : ℝ) ^ (2 / (d : ℝ)) ≤
              (projectiveCount (projectiveIdealZeroLocus (Ideal.span {F})) B : ℝ) := by
  obtain ⟨F, B, hB, hhom, hdeg, habs, hcount⟩ := projective_plane_lower_bound d hd
  have hir : Irreducible F :=
    mvPolynomial_irreducible_of_field_map (algebraMap ℚ (AlgebraicClosure ℚ)) F habs
  refine ⟨F, B, hB, hhom, hdeg, habs, Ideal.isPrime_span_singleton_of_prime hir.prime,
    principal_plane_hasProjectiveCurveDegree F hhom hir.ne_zero, ?_⟩
  rwa [projectiveIdealZeroLocus_span_singleton F hhom]

end
end CCDN
