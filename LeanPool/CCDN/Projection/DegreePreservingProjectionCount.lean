/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IdealZeroLocus
public import LeanPool.CCDN.Hilbert.FilteredIntersection
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Algebraic.Defs
import LeanPool.CCDN.Determinant.PlaneSingularities
import LeanPool.CCDN.Projection.CurveDerivativeReconstruction
import LeanPool.CCDN.Projection.ExceptionalCount
import LeanPool.CCDN.Projection.PlaneProjectionDerivative

/-! A degree-preserving linear plane projection of a prime affine curve in
characteristic zero loses at most d(d-1) points from any finite source set.
The proof constructs a common derivative denominator and all reconstruction
identities, with no normalization or exceptional-fiber hypothesis. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- All source coordinates have the same proper reconstruction denominator,
namely the partial derivative of the plane image equation. -/
theorem degree_preserving_projection_reconstruction {K τ : Type*}
    [Field K] [CharZero K] [Finite τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : Fin 2 → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (d : ℕ) (hdegree : HasFilteredCurveDegree I d)
    (hu : Transcendental K ((Ideal.Quotient.mk I) (a 0)))
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (hfd : f.totalDegree = d)
    (hker : ∀ g, aeval a g ∈ I ↔ f ∣ g) :
    aeval a (pderiv 1 f) ∉ I ∧ (pderiv 1 f).totalDegree ≤ d - 1 ∧
      ∃ P : τ → MvPolynomial (Fin 2) K, ∀ i,
        (P i).totalDegree ≤ d ∧ aeval a (pderiv 1 f) * X i - aeval a (P i) ∈ I := by
  classical
  let := Fintype.ofFinite τ
  have hp := projection_derivative_proper I a ha f hf hker 0 1 (by decide) hu
  refine ⟨hp.1, by simpa only [hfd] using pderiv_totalDegree_le f 1, ?_⟩
  choose P hP using fun i : τ => exists_derivative_reconstruction I a ha d hdegree hu
    f hf hfd hker (X i) (by simp)
  exact ⟨P, hP⟩

/-- Uniform exceptional-fiber control for any degree-preserving linear plane
projection, including curves that are not geometrically integral. -/
theorem degree_preserving_projection_card_le {K τ : Type*}
    [Field K] [CharZero K] [Finite τ] [DecidableEq (Fin 2 → K)]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : Fin 2 → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (d : ℕ) (hdegree : HasFilteredCurveDegree I d)
    (hu : Transcendental K ((Ideal.Quotient.mk I) (a 0)))
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (hfd : f.totalDegree = d)
    (hker : ∀ g, aeval a g ∈ I ↔ f ∣ g)
    (S : Finset (τ → K)) (hS : ∀ z ∈ S, z ∈ idealZeroLocus I) :
    S.card ≤ (S.image (fun z j => eval z (a j))).card + d * (d - 1) := by
  classical
  let := Fintype.ofFinite τ
  obtain ⟨hQ, hQd, P, hP⟩ := degree_preserving_projection_reconstruction I a ha d hdegree hu
    f hf hfd hker
  exact (projection_card_le_image_add I d hdegree a ha (pderiv 1 f) P hQ
    (fun i => (hP i).2) S hS).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left d hQd) _)

end
end CCDN
