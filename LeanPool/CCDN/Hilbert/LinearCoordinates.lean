/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Hilbert.PolynomialComparison
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.Tactic.Positivity

/-! Algebraically independent linear coordinates have cardinality at most
the degree of the filtered Hilbert polynomial. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- `projectionCoordinateMap I a` is evaluation at the classes of the coordinate polynomials `a i`
in `K[X] ⧸ I`. -/
lemma projectionCoordinateMap_eq_aeval {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K) :
    projectionCoordinateMap I a =
      aeval (fun i => (Ideal.Quotient.mk I) (a i)) := by
  ext i
  simp [projectionCoordinateMap]

/-- The projection map is injective exactly when the images of the coordinates in the quotient
are algebraically independent. -/
lemma injective_projectionCoordinateMap_iff {K σ τ : Type*} [Field K]
    {I : Ideal (MvPolynomial τ K)} {a : σ → MvPolynomial τ K} :
    Function.Injective (projectionCoordinateMap I a) ↔
      AlgebraicIndependent K (fun i => (Ideal.Quotient.mk I) (a i)) := by
  rw [projectionCoordinateMap_eq_aeval]
  rfl

private lemma independent_linear_filtered_finrank_lower
    {K σ τ : Type*} [Field K] [Fintype σ] [Finite τ]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hi : AlgebraicIndependent K (fun i => (Ideal.Quotient.mk I) (a i))) (N : ℕ) :
    (Fintype.card σ + N).choose (Fintype.card σ) ≤
      Module.finrank K (filteredCoordinateSpace I N) := by
  classical
  let := Fintype.ofFinite τ
  let V := restrictTotalDegree σ K N
  let ψ := projectionCoordinateMap I a
  let T : V →ₗ[K] filteredCoordinateSpace I N :=
    (ψ.toLinearMap.comp V.subtype).codRestrict _ (fun v =>
      projectionCoordinateMap_filtered I a ha v.val
        ((mem_restrictTotalDegree _ _ _).mp v.property))
  have hinj : Function.Injective ψ := injective_projectionCoordinateMap_iff.mpr hi
  have hiT : Function.Injective T := by
    intro x y h
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val h
  have h := LinearMap.finrank_le_finrank_of_injective hiT
  change Module.finrank K (restrictTotalDegree σ K N) ≤ _ at h
  rw [finrank_restrictTotalDegree, ← Nat.choose_symm_add] at h
  exact h

/-- If polynomials `a i` of degree at most one have algebraically independent classes in `K[X] ⧸ I`,
their number is at most the degree of the filtered Hilbert polynomial of `I`. -/
theorem independent_linear_card_le_hilbert_dimension
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ] [LinearOrder τ]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hi : AlgebraicIndependent K (fun i => (Ideal.Quotient.mk I) (a i))) :
    Fintype.card σ ≤ (filteredHilbertPolynomial I).natDegree := by
  have hh := polynomial_natDegree_le_of_eventual_nat_eval_le
    (Polynomial.preHilbertPoly ℚ (Fintype.card σ) 0) (filteredHilbertPolynomial I)
    (by rw [Polynomial.leadingCoeff_preHilbertPoly]; positivity)
  rw [Polynomial.natDegree_preHilbertPoly] at hh
  apply hh
  obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
  refine ⟨M, fun N hN => ?_⟩
  rw [hM N hN, Polynomial.preHilbertPoly_eq_choose_add_sub ℚ
    (Fintype.card σ) (by omega : 0 ≤ N + Fintype.card σ)]
  simpa only [Nat.sub_zero, Nat.add_comm] using
    (Nat.cast_le.mpr (independent_linear_filtered_finrank_lower I a ha hi N) :
      ((Fintype.card σ + N).choose (Fintype.card σ) : ℚ) ≤ _)

/-- If more polynomials `a i` of degree at most one are given than the degree of the filtered
Hilbert polynomial of `I`, then `projectionCoordinateMap I a` is not injective. -/
theorem linear_projection_not_injective_of_hilbert_dimension_lt
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ] [LinearOrder τ]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hd : (filteredHilbertPolynomial I).natDegree < Fintype.card σ) :
    ¬ Function.Injective (projectionCoordinateMap I a) := by
  intro hinj
  exact (not_le_of_gt hd) (independent_linear_card_le_hilbert_dimension I a ha
    (injective_projectionCoordinateMap_iff.mp hinj))

end
end CCDN
