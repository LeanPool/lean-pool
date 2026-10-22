/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Projection.CurvePrimitivePair
public import LeanPool.CCDN.Projection.InfinityParameterReduction
public import LeanPool.CCDN.Algebra.BoundedLinearSeparation
import LeanPool.CCDN.Algebra.CoordinatePowerGeneration
import Mathlib.Algebra.Polynomial.OfFn

/-! An explicit bounded integer moment form avoids any prescribed finite set
of nonzero directions. No separation of pairs is needed for this step. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The moment coordinate `∑ j, k ^ j * X j` is homogeneous of degree one. -/
lemma momentCoordinate_homogeneous (K : Type*) [Field K] (n k : ℕ) :
    (momentCoordinate K n k).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- Avoiding infinity gives the eventual recurrence of the original
coordinate filtration. -/
theorem filtration_recurrence_of_infinity_avoidance {K L σ : Type*}
    [Field K] [Field L] [Algebra K L] [IsAlgClosed L] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (l : MvPolynomial σ K) (hl : l.IsHomogeneous 1)
    (hzero : ∀ z ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I ⊔ Ideal.span {l}), z = 0) :
    ∃ N : ℕ, ∀ m ≥ N, filteredCoordinateSpace I (m + 1) =
      filteredCoordinateSpace I m ⊔ (filteredCoordinateSpace I m).map
        (LinearMap.mulLeft K ((Ideal.Quotient.mk I) l)) := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨N, hN, hred⟩ := exists_power_reductions_of_infinity_avoidance I l hl hzero
  exact ⟨Fintype.card σ * N,
    eventual_generation_of_power_reductions I l hl.totalDegree_le N hN hred⟩

end
end CCDN
