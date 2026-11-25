/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.QuinticGlobalError
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SepticGlobalRemainder

/-!
# Global operator errors retaining two complete Lie polynomials

The refined global main term is the sum of the quintic and septic discrete
midpoint averages. Both are added as algebra elements before taking a norm.

## Main definitions

* `TrotterError.septicMidpointTerm`: the complete two-polynomial midpoint sum.

## Main results

* `FQFP.norm_interactionProduct_sub_septic_midpoint_le`: the finite-step operator bound.
* `FQFP.abs_norm_pow_sub_exp_sub_septic_midpoint_le`: the two-sided norm estimate.
-/

@[expose] public noncomputable section

open NormedSpace TrotterError Finset
open scoped RealScalar

namespace TrotterError

/-- The complete sum of the quintic and centered septic midpoint averages. -/
def septicMidpointTerm {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (G L N : A) (r : ℕ) (h : ℝ) : A :=
  h ^ 4 • midpointConjugationIntegral G L r h +
    h ^ 6 • midpointConjugationIntegral G N r h

/-- The two midpoint averages are one sum of conjugated centered main terms. -/
lemma septicMidpointTerm_eq_sum {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (G L N : A) (r : ℕ) (h : ℝ) :
    septicMidpointTerm G L N r h =
      ∑ k ∈ range r, expSMulConj (-G) (h ^ 5 • L + h ^ 7 • N)
        (((k : ℝ) + 1 / 2) * h) := by
  simp only [septicMidpointTerm, midpointConjugationIntegral, smul_smul, ← pow_succ,
    expSMulConj, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    sum_add_distrib, smul_sum]

/-- At zero step the complete discrete main term vanishes. -/
@[simp] lemma septicMidpointTerm_zero_step {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] (G L N : A) (r : ℕ) :
    septicMidpointTerm G L N r 0 = 0 := by
  simp [septicMidpointTerm]

/-- With no cells the complete discrete main term vanishes. -/
@[simp] lemma septicMidpointTerm_zero {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] (G L N : A) (h : ℝ) :
    septicMidpointTerm G L N 0 h = 0 := by
  simp [septicMidpointTerm]

end TrotterError

namespace FQFP

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- **Refined discrete operator bound.** The complete quintic and centered septic
polynomials are transported together. All nonlinear accumulation terms are retained. -/
theorem norm_interactionProduct_sub_septic_midpoint_le (G S L N : A) (ℓ μ C D : ℝ)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (hS : ‖S‖ ≤ 1) (h : ℝ)
    (hlocal : ‖exp ((-h / 2) • G) * (S - exp (h • G)) * exp ((-h / 2) • G) -
      (h ^ 5 • L + h ^ 7 • N)‖ ≤ septicCenteredRemainder ℓ μ C D h)
    (hstep : ‖S - exp (h • G)‖ ≤ septicStepBound ℓ μ C h) (r : ℕ) :
    ‖exp (-((r : ℝ) * h) • G) * S ^ r - 1 - septicMidpointTerm G L N r h‖ ≤
      septicGlobalRemainder ℓ μ C D h r := by
  rw [septicMidpointTerm_eq_sum]
  exact norm_interactionProduct_sub_sum_conj_le G S _ hG hS h hlocal hstep r

/-- **Refined two-sided norm bound.** A single norm of the full midpoint sum
approximates the physical splitting error with the same explicit remainder. -/
theorem abs_norm_pow_sub_exp_sub_septic_midpoint_le (G S L N : A) (ℓ μ C D : ℝ)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (hS : ‖S‖ ≤ 1) (h : ℝ)
    (hlocal : ‖exp ((-h / 2) • G) * (S - exp (h • G)) * exp ((-h / 2) • G) -
      (h ^ 5 • L + h ^ 7 • N)‖ ≤ septicCenteredRemainder ℓ μ C D h)
    (hstep : ‖S - exp (h • G)‖ ≤ septicStepBound ℓ μ C h) (r : ℕ) :
    |‖S ^ r - exp (((r : ℝ) * h) • G)‖ - ‖septicMidpointTerm G L N r h‖| ≤
      septicGlobalRemainder ℓ μ C D h r := by
  exact (abs_norm_pow_sub_exp_sub_norm_le G S _ hG _ r).trans
    (norm_interactionProduct_sub_septic_midpoint_le G S L N ℓ μ C D hG hS h hlocal hstep r)

end FQFP
