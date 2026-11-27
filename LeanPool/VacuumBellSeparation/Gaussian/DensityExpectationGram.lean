/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveDensityState
public import Mathlib.Analysis.Matrix.Order

/-!
# Actual positive density expectations give positive finite Gram matrices

The matrix entries are expectations of X_i† X_j in the genuine density
functional. Complex linearity and actual operator positivity prove its
positive quadratic forms, and the adjoint expectation identity proves
Hermitian symmetry. No positive-kernel hypothesis is introduced.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix ContinuousLinearMap
open scoped ComplexOrder ComplexConjugate

variable {ι κ E : Type*} [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem densityExpectation_star (b : HilbertBasis ι ℂ E) (A B : E →L[ℂ] E) :
    densityExpectation b A (star B) = star (densityExpectation b A B) := by
  simp only [densityExpectation, familyExpectation, tsum_star]
  apply tsum_congr
  intro i
  change inner ℂ _ (B.adjoint _) = star (inner ℂ _ (B _))
  rw [B.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

/-- Density expectation gram given by `fun i j => densityExpectation b A (star (X i) * X j)`. -/
def densityExpectationGram (b : HilbertBasis ι ℂ E) (A : E →L[ℂ] E)
    (X : κ → E →L[ℂ] E) : Matrix κ κ ℂ :=
  fun i j => densityExpectation b A (star (X i) * X j)

omit [Fintype κ] [DecidableEq κ] in
theorem densityExpectationGram_isHermitian (b : HilbertBasis ι ℂ E)
    (A : E →L[ℂ] E) (X : κ → E →L[ℂ] E) :
    (densityExpectationGram b A X).IsHermitian := by
  change (densityExpectationGram b A X)ᴴ = densityExpectationGram b A X
  ext i j
  simp only [Matrix.conjTranspose_apply, densityExpectationGram,
    ← densityExpectation_star, star_mul, star_star]

omit [DecidableEq κ] in
theorem densityExpectationGram_quadratic (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A)
    (X : κ → E →L[ℂ] E) (c : κ → ℂ) :
    star c ⬝ᵥ (densityExpectationGram b A X *ᵥ c) =
      densityExpectation b A (star (∑ i, c i • X i) * (∑ j, c j • X j)) := by
  let φ := densityExpectationCLM b hA
  change _ = φ _
  simp only [map_sum, star_sum, star_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul,
    dotProduct, Matrix.mulVec, densityExpectationGram, Pi.star_apply]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change star (c i) * (densityExpectation b A (star (X i) * X j) * c j) =
    c j * (star (c i) * densityExpectation b A (star (X i) * X j))
  ring

omit [DecidableEq κ] [Fintype κ] in
theorem densityExpectationGram_posSemidef [Finite κ] (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) (X : κ → E →L[ℂ] E) :
    (densityExpectationGram b A X).PosSemidef := by
  let _ : Fintype κ := Fintype.ofFinite κ
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨densityExpectationGram_isHermitian b A X, ?_⟩
  intro c
  rw [densityExpectationGram_quadratic b hA X c]
  exact densityExpectation_nonneg b A (star_mul_self_nonneg _)

end VacuumBellSeparation.Gaussian
