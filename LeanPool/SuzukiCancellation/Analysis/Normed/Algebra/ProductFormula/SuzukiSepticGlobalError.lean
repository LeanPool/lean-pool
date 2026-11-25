/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiSepticLocalError
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiGlobalError
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SepticGlobalError

/-!
# Seventh-order global cancellation for the Suzuki composition

The complete quintic and centered septic polynomials are summed in the same
discrete interaction picture. The explicit remainder is eighth order at fixed
time along integer step counts, without restricting the finite-step theorem.

## Main definitions

* `suzukiSepticMidpointTerm`: the complete two-polynomial discrete main term.
* `suzukiSepticGlobalRemainder`: the original refined global remainder.

## Main results

* `norm_fiveStageStrangProduct_pow_sub_septic_midpoint_le_div`: the operator bound.
* `abs_norm_fiveStageStrangProduct_pow_error_sub_septic_midpoint_le`: the norm enclosure.
* `isBigO_fiveStageStrangProduct_pow_sub_septic_midpoint`: eighth-order operator remainder.
* `norm_suzukiProduct_pow_sub_septic_midpoint_le_of_skewAdjoint`: the canonical C*-bound.
-/

@[expose] public noncomputable section

open NormedSpace TrotterError Filter Asymptotics
open scoped RealScalar

namespace FQFP.BCH

section Definitions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The full quintic and centered septic discrete averages, added before taking a norm. -/
def suzukiSepticMidpointTerm (a b : A) (p : ℝ) (r : ℕ) (h : ℝ) : A :=
  septicMidpointTerm (a + b) (suzukiQuinticTerm a b p) (suzukiCenteredSepticTerm a b p) r h

end Definitions

section Remainder

variable {A : Type*} [NormedRing A] [Algebra ℝ A]

/-- The original refined global remainder, including every centered and quadratic term. -/
def suzukiSepticGlobalRemainder (a b : A) (p h : ℝ) (r : ℕ) : ℝ :=
  septicGlobalRemainder ‖suzukiQuinticTerm a b p‖ ‖suzukiDefectSepticTerm a b p‖
    (suzukiNonicConstant a b p) (suzukiCenteredNonicConstant a b p) h r

end Remainder

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- **Refined Suzuki global operator bound.** Both complete leading polynomials
are retained at every nonnegative step, with the original nonlinear remainder. -/
theorem norm_fiveStageStrangProduct_pow_sub_septic_midpoint_le (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (h : ℝ) (hh : 0 ≤ h) (r : ℕ) :
    ‖exp (-((r : ℝ) * h) • (a + b)) * fiveStageStrangProduct a b p h ^ r - 1 -
      suzukiSepticMidpointTerm a b p r h‖ ≤ suzukiSepticGlobalRemainder a b p h r := by
  apply norm_interactionProduct_sub_septic_midpoint_le (a + b) _ _ _ _ _ _ _ hG
    (norm_fiveStageStrangProduct_le_one a b p ha hb h) h
  · simpa only [sub_add_eq_sub_sub] using
      norm_fiveStageStrangProduct_centered_sub_septic_le a b p hp ha hb hG h hh
  · simpa only [abs_of_nonneg hh] using
      norm_fiveStageStrangProduct_sub_exp_le_septic a b p hp ha hb hG h

/-- The refined operator bound at fixed nonnegative time and positive integer step count. -/
theorem norm_fiveStageStrangProduct_pow_sub_septic_midpoint_le_div (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t)
    (r : ℕ) (hr : 1 ≤ r) :
    ‖exp ((-t) • (a + b)) * fiveStageStrangProduct a b p (t / r) ^ r - 1 -
      suzukiSepticMidpointTerm a b p r (t / r)‖ ≤
        suzukiSepticGlobalRemainder a b p (t / r) r := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by lia)
  have hrh : (r : ℝ) * (t / r) = t := mul_div_cancel₀ t hr0
  simpa only [hrh] using norm_fiveStageStrangProduct_pow_sub_septic_midpoint_le
    a b p hp ha hb hG (t / r) (div_nonneg ht (Nat.cast_nonneg r)) r

/-- **Refined two-sided error bound.** The norm of the sum of both complete
discrete averages approximates the physical error norm from both sides. -/
theorem abs_norm_fiveStageStrangProduct_pow_error_sub_septic_midpoint_le (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t)
    (r : ℕ) (hr : 1 ≤ r) :
    |‖fiveStageStrangProduct a b p (t / r) ^ r - exp (t • (a + b))‖ -
      ‖suzukiSepticMidpointTerm a b p r (t / r)‖| ≤
        suzukiSepticGlobalRemainder a b p (t / r) r := by
  exact (abs_norm_pow_sub_exp_sub_norm_le (a + b) _ _ hG t r).trans
    (norm_fiveStageStrangProduct_pow_sub_septic_midpoint_le_div a b p hp ha hb hG t ht r hr)

/-- The actual refined Suzuki operator remainder is `O(r⁻⁸)` with fixed inputs and time. -/
theorem isBigO_fiveStageStrangProduct_pow_sub_septic_midpoint (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    (fun r : ℕ ↦ exp ((-t) • (a + b)) * fiveStageStrangProduct a b p (t / r) ^ r - 1 -
      suzukiSepticMidpointTerm a b p r (t / r))
      =O[atTop] (fun r : ℕ ↦ ((r : ℝ)⁻¹) ^ 8) := by
  apply isBigO_inv_nat_pow_eight_of_septicGlobalRemainder
    (ℓ := ‖suzukiQuinticTerm a b p‖) (μ := ‖suzukiDefectSepticTerm a b p‖)
    (C := suzukiNonicConstant a b p) (t := t) _
    (suzukiCenteredNonicConstant a b p) (norm_nonneg _) (norm_nonneg _)
    (suzukiNonicConstant_nonneg a b p) ht
  exact norm_fiveStageStrangProduct_pow_sub_septic_midpoint_le_div a b p hp ha hb hG t ht

/-- The two-sided scalar error in the refined prediction is also `O(r⁻⁸)`. -/
theorem isBigO_norm_fiveStageStrangProduct_pow_error_sub_septic_midpoint (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    (fun r : ℕ ↦ ‖fiveStageStrangProduct a b p (t / r) ^ r - exp (t • (a + b))‖ -
      ‖suzukiSepticMidpointTerm a b p r (t / r)‖)
      =O[atTop] (fun r : ℕ ↦ ((r : ℝ)⁻¹) ^ 8) := by
  refine (isBigO_of_le atTop ?_).trans
    (isBigO_fiveStageStrangProduct_pow_sub_septic_midpoint a b p hp ha hb hG t ht)
  intro r
  exact abs_norm_pow_sub_exp_sub_norm_le (a + b) _ _ hG t r

/-- **Canonical C*-algebra refined global bound.** Skew-adjoint inputs supply
the exponentials' norm bounds, and the canonical parameter supplies the order condition. -/
theorem norm_suzukiProduct_pow_sub_septic_midpoint_le_of_skewAdjoint
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A)
    (ha : star a = -a) (hb : star b = -b) (t : ℝ) (ht : 0 ≤ t)
    (r : ℕ) (hr : 1 ≤ r) :
    ‖exp ((-t) • (a + b)) * fiveStageStrangProduct a b suzukiP (t / r) ^ r - 1 -
      suzukiSepticMidpointTerm a b suzukiP r (t / r)‖ ≤
        suzukiSepticGlobalRemainder a b suzukiP (t / r) r := by
  apply norm_fiveStageStrangProduct_pow_sub_septic_midpoint_le_div a b suzukiP
    isSuzukiCubic_suzukiP (norm_exp_smul_le_one_of_skewAdjoint ha)
    (norm_exp_smul_le_one_of_skewAdjoint hb) _ t ht r hr
  exact norm_exp_smul_le_one_of_skewAdjoint
    ((skewAdjoint A).add_mem ha hb)

/-- The canonical C*-algebra splitting has the refined two-sided error enclosure. -/
theorem abs_norm_suzukiProduct_pow_error_sub_septic_midpoint_le_of_skewAdjoint
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A)
    (ha : star a = -a) (hb : star b = -b) (t : ℝ) (ht : 0 ≤ t)
    (r : ℕ) (hr : 1 ≤ r) :
    |‖fiveStageStrangProduct a b suzukiP (t / r) ^ r - exp (t • (a + b))‖ -
      ‖suzukiSepticMidpointTerm a b suzukiP r (t / r)‖| ≤
        suzukiSepticGlobalRemainder a b suzukiP (t / r) r := by
  apply abs_norm_fiveStageStrangProduct_pow_error_sub_septic_midpoint_le a b suzukiP
    isSuzukiCubic_suzukiP (norm_exp_smul_le_one_of_skewAdjoint ha)
    (norm_exp_smul_le_one_of_skewAdjoint hb) _ t ht r hr
  exact norm_exp_smul_le_one_of_skewAdjoint
    ((skewAdjoint A).add_mem ha hb)

end FQFP.BCH
