/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiCenteredLocalError
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.QuinticGlobalError

/-!
# Global cancellation bounds for the fourth-order Suzuki composition

The main term is the integral of the complete quintic Lie polynomial along
the exact evolution. The original local commutator constants control the
finite-step remainder without a small-step assumption.

## Main definitions

* `suzukiGlobalRemainder`: the original continuous global remainder.

## Main results

* `norm_fiveStageStrangProduct_pow_sub_integral_le`: the operator estimate.
* `two_sided_fiveStageStrangProduct_pow_error`: the scalar enclosure.
* `tendsto_nat_pow_four_mul_norm_fiveStageStrangProduct_pow_sub_exp`: the sharp limit.
* `isBigO_fiveStageStrangProduct_pow_sub_exp_of_integral_eq_zero`: sixth-order decay.
-/

@[expose] public noncomputable section

open NormedSpace TrotterError Filter Asymptotics
open scoped RealScalar Topology

namespace FQFP.BCH

section Definitions

variable {A : Type*} [NormedRing A] [Algebra ℝ A]

/-- The original global remainder with the Suzuki quintic and commutator constants. -/
def suzukiGlobalRemainder (a b : A) (p t h : ℝ) (r : ℕ) : ℝ :=
  quinticGlobalRemainder ‖suzukiQuinticTerm a b p‖ (suzukiSepticConstant a b p)
    (suzukiCenteredConjugationConstant a b p)
    ‖⁅a + b, ⁅a + b, suzukiQuinticTerm a b p⁆⁆‖ t h r

end Definitions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- Two-sided exponential contractions make the Suzuki product a contraction. -/
lemma norm_fiveStageStrangProduct_le_one (a b : A) (p : ℝ)
    (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1) (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (h : ℝ) : ‖fiveStageStrangProduct a b p h‖ ≤ 1 := by
  have hZ : ∀ Z ∈ List.ofFn (fiveStageStrangHalfGenerator a b p),
      ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1 := by
    intro Z hZ t
    rcases List.mem_ofFn.mp hZ with ⟨i, rfl⟩
    exact norm_exp_smul_fiveStageStrangHalfGenerator_le_one a b p ha hb i t
  rw [fiveStageStrangProduct_eq_symmetricExpProduct, symmetricExpProduct,
    norm_expListProduct_mul_eq_of_le_one _ _ hZ,
    ← mul_one (expListProduct _ _), norm_expListProduct_mul_eq_of_le_one _ _
      (fun Z hZ' ↦ hZ Z (List.mem_reverse.mp hZ'))]
  simpa using ha 0

/-- **Discrete Suzuki global bound.** Before quadrature, the finite midpoint
sum retains cancellation between all time steps. -/
theorem norm_fiveStageStrangProduct_pow_sub_midpoint_le (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (h : ℝ) (hh : 0 ≤ h) (r : ℕ) :
    ‖exp (-((r : ℝ) * h) • (a + b)) * fiveStageStrangProduct a b p h ^ r - 1 -
      h ^ 4 • midpointConjugationIntegral (a + b) (suzukiQuinticTerm a b p) r h‖ ≤
        (r : ℝ) * quinticCenteredRemainder ‖suzukiQuinticTerm a b p‖
          (suzukiSepticConstant a b p) (suzukiCenteredConjugationConstant a b p) h +
        (r : ℝ) * ((r : ℝ) - 1) / 2 *
          quinticStepBound ‖suzukiQuinticTerm a b p‖ (suzukiSepticConstant a b p) h ^ 2 := by
  apply norm_interactionProduct_sub_midpoint_le (a + b) _ _ hG
    (norm_fiveStageStrangProduct_le_one a b p ha hb h) h
  · exact norm_fiveStageStrangProduct_centered_sub_quintic_le a b p hp ha hb hG h hh
  · apply le_min
    · exact (norm_sub_le _ _).trans
        (by linarith [norm_fiveStageStrangProduct_le_one a b p ha hb h, hG h])
    · simpa only [abs_of_nonneg hh] using
        norm_fiveStageStrangProduct_sub_exp_le a b p hp ha hb hG h

/-- **Suzuki global operator remainder.** The complete continuous interaction
coefficient is retained, for every nonnegative step and every finite step count. -/
theorem norm_fiveStageStrangProduct_pow_sub_integral_le (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (h : ℝ) (hh : 0 ≤ h) (r : ℕ) :
    ‖exp (-((r : ℝ) * h) • (a + b)) * fiveStageStrangProduct a b p h ^ r - 1 -
      h ^ 4 • conjugationIntegral (a + b) (suzukiQuinticTerm a b p) ((r : ℝ) * h)‖ ≤
        suzukiGlobalRemainder a b p ((r : ℝ) * h) h r := by
  apply norm_interactionProduct_sub_integral_le (a + b) _ _ _ _ hG
    (norm_fiveStageStrangProduct_le_one a b p ha hb h) h hh
  · exact norm_fiveStageStrangProduct_centered_sub_quintic_le a b p hp ha hb hG h hh
  · simpa only [abs_of_nonneg hh] using
      norm_fiveStageStrangProduct_sub_exp_le a b p hp ha hb hG h

/-- The fixed-time operator estimate uses the positive integer step count
and the exact step `h = t / r`. -/
theorem norm_fiveStageStrangProduct_pow_sub_integral_le_div (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t)
    (r : ℕ) (hr : 1 ≤ r) :
    ‖exp ((-t) • (a + b)) * fiveStageStrangProduct a b p (t / r) ^ r - 1 -
      (t / r) ^ 4 • conjugationIntegral (a + b) (suzukiQuinticTerm a b p) t‖ ≤
        suzukiGlobalRemainder a b p t (t / r) r := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by lia)
  have hrh : (r : ℝ) * (t / r) = t := mul_div_cancel₀ t hr0
  simpa only [hrh] using norm_fiveStageStrangProduct_pow_sub_integral_le a b p hp ha hb hG
    (t / r) (div_nonneg ht (Nat.cast_nonneg r)) r

/-- **Two-sided global error bound.** The same finite-step operator remainder
bounds the physical error norm above and below. -/
theorem two_sided_fiveStageStrangProduct_pow_error (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t)
    (r : ℕ) (hr : 1 ≤ r) :
    let K := conjugationIntegral (a + b) (suzukiQuinticTerm a b p) t
    let R := suzukiGlobalRemainder a b p t (t / r) r
    max 0 ((t / r) ^ 4 * ‖K‖ - R) ≤
      ‖fiveStageStrangProduct a b p (t / r) ^ r - exp (t • (a + b))‖ ∧
    ‖fiveStageStrangProduct a b p (t / r) ^ r - exp (t • (a + b))‖ ≤
      (t / r) ^ 4 * ‖K‖ + R := by
  have hbound := two_sided_norm_of_norm_sub_le _ _
    (norm_fiveStageStrangProduct_pow_sub_integral_le_div a b p hp ha hb hG t ht r hr)
  rw [← norm_pow_sub_exp_eq_interaction (a + b) _ hG t r] at hbound
  simpa only [norm_smul, Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (div_nonneg ht (Nat.cast_nonneg r))] using hbound

/-- **Sharp fixed-time coefficient.** The generator and time are fixed while
the integer step count tends to infinity. -/
theorem tendsto_nat_pow_four_mul_norm_fiveStageStrangProduct_pow_sub_exp (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun r : ℕ ↦ (r : ℝ) ^ 4 *
      ‖fiveStageStrangProduct a b p (t / r) ^ r - exp (t • (a + b))‖) atTop
        (𝓝 (t ^ 4 * ‖conjugationIntegral (a + b) (suzukiQuinticTerm a b p) t‖)) := by
  have hlim := tendsto_nat_pow_four_mul_norm_of_quinticGlobalRemainder
    (fun r : ℕ ↦ exp ((-t) • (a + b)) * fiveStageStrangProduct a b p (t / r) ^ r - 1)
    (conjugationIntegral (a + b) (suzukiQuinticTerm a b p) t)
    ‖suzukiQuinticTerm a b p‖ (suzukiSepticConstant a b p)
    (suzukiCenteredConjugationConstant a b p)
    ‖⁅a + b, ⁅a + b, suzukiQuinticTerm a b p⁆⁆‖ t
    (norm_nonneg _) (suzukiSepticConstant_nonneg a b p) ht
    (norm_fiveStageStrangProduct_pow_sub_integral_le_div a b p hp ha hb hG t ht)
  apply hlim.congr'
  filter_upwards with r
  congr 1
  exact (norm_pow_sub_exp_eq_interaction (a + b)
    (fiveStageStrangProduct a b p (t / r)) hG t r).symm

/-- A vanishing continuous interaction coefficient improves the physical
global error to sixth order in the inverse integer step count. -/
theorem isBigO_fiveStageStrangProduct_pow_sub_exp_of_integral_eq_zero (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t)
    (hK : conjugationIntegral (a + b) (suzukiQuinticTerm a b p) t = 0) :
    (fun r : ℕ ↦ fiveStageStrangProduct a b p (t / r) ^ r - exp (t • (a + b)))
      =O[atTop] (fun r : ℕ ↦ ((r : ℝ)⁻¹) ^ 6) := by
  obtain ⟨B, hB⟩ := exists_eventually_le_pow_six_of_le_quinticGlobalRemainder
    (norm_nonneg _) (suzukiSepticConstant_nonneg a b p) ht
    (norm_fiveStageStrangProduct_pow_sub_integral_le_div a b p hp ha hb hG t ht)
  apply isBigO_inv_nat_pow_six_of_remainder_le _ t B
  simpa only [hK, smul_zero, sub_zero, ← norm_pow_sub_exp_eq_interaction _ _ hG] using hB

/-- The global distance between the splitting power and the exact evolution
is at most two, under the same exponential norm hypotheses. -/
theorem norm_fiveStageStrangProduct_pow_sub_exp_le_two (a b : A) (p : ℝ)
    (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1) (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (t h : ℝ) (r : ℕ) :
    ‖fiveStageStrangProduct a b p h ^ r - exp (t • (a + b))‖ ≤ 2 := by
  have hS : ‖fiveStageStrangProduct a b p h ^ r‖ ≤ 1 := by
    induction r with
    | zero => simpa using hG 0
    | succ r ih =>
      rw [pow_succ]
      simpa using norm_mul_le_of_le ih (norm_fiveStageStrangProduct_le_one a b p ha hb h)
  exact (norm_sub_le _ _).trans (by linarith [hG t])

/-- **Canonical C*-algebra global operator bound.** Only skew-adjoint input
generators, nonnegative time, and a positive integer step count are required. -/
theorem norm_suzukiProduct_pow_sub_integral_le_of_skewAdjoint
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A)
    (ha : star a = -a) (hb : star b = -b) (t : ℝ) (ht : 0 ≤ t)
    (r : ℕ) (hr : 1 ≤ r) :
    ‖exp ((-t) • (a + b)) * fiveStageStrangProduct a b suzukiP (t / r) ^ r - 1 -
      (t / r) ^ 4 • conjugationIntegral (a + b) (suzukiQuinticTerm a b suzukiP) t‖ ≤
        suzukiGlobalRemainder a b suzukiP t (t / r) r := by
  apply norm_fiveStageStrangProduct_pow_sub_integral_le_div a b suzukiP
    isSuzukiCubic_suzukiP (norm_exp_smul_le_one_of_skewAdjoint ha)
    (norm_exp_smul_le_one_of_skewAdjoint hb) _ t ht r hr
  exact norm_exp_smul_le_one_of_skewAdjoint
    ((skewAdjoint A).add_mem ha hb)

/-- **Canonical sharp global coefficient.** The fixed-time integer sequence
requires only skew-adjointness of the two splitting generators. -/
theorem tendsto_nat_pow_four_mul_norm_suzukiProduct_pow_sub_exp_of_skewAdjoint
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A)
    (ha : star a = -a) (hb : star b = -b) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun r : ℕ ↦ (r : ℝ) ^ 4 *
      ‖fiveStageStrangProduct a b suzukiP (t / r) ^ r - exp (t • (a + b))‖) atTop
        (𝓝 (t ^ 4 * ‖conjugationIntegral (a + b) (suzukiQuinticTerm a b suzukiP) t‖)) := by
  apply tendsto_nat_pow_four_mul_norm_fiveStageStrangProduct_pow_sub_exp a b suzukiP
    isSuzukiCubic_suzukiP (norm_exp_smul_le_one_of_skewAdjoint ha)
    (norm_exp_smul_le_one_of_skewAdjoint hb) _ t ht
  exact norm_exp_smul_le_one_of_skewAdjoint
    ((skewAdjoint A).add_mem ha hb)

/-- Complete cancellation of the integral coefficient gives sixth-order
decay for the canonical C*-algebra Suzuki composition. -/
theorem isBigO_suzukiProduct_pow_sub_exp_of_skewAdjoint_of_integral_eq_zero
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A)
    (ha : star a = -a) (hb : star b = -b) (t : ℝ) (ht : 0 ≤ t)
    (hK : conjugationIntegral (a + b) (suzukiQuinticTerm a b suzukiP) t = 0) :
    (fun r : ℕ ↦ fiveStageStrangProduct a b suzukiP (t / r) ^ r - exp (t • (a + b)))
      =O[atTop] (fun r : ℕ ↦ ((r : ℝ)⁻¹) ^ 6) := by
  apply isBigO_fiveStageStrangProduct_pow_sub_exp_of_integral_eq_zero a b suzukiP
    isSuzukiCubic_suzukiP (norm_exp_smul_le_one_of_skewAdjoint ha)
    (norm_exp_smul_le_one_of_skewAdjoint hb) _ t ht hK
  exact norm_exp_smul_le_one_of_skewAdjoint
    ((skewAdjoint A).add_mem ha hb)

end FQFP.BCH
