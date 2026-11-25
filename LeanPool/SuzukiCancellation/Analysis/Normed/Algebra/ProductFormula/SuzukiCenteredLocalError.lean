/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SymmetricCenteredLocalError
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiLocalError
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.QuinticGlobalRemainder

/-!
# Centered local remainder for the fourth-order Suzuki composition

The six half-stages determine the original second-order commutator constant.
The centered local estimate uses the same quintic polynomial and septic constant
as the all-real local theorem.

## Main definitions

* `suzukiCenteredConjugationConstant`: the centered second-order commutator constant.

## Main results

* `norm_fiveStageStrangProduct_centered_sub_quintic_le`: the centered local bound.
* `norm_suzukiProduct_centered_sub_quintic_le_of_skewAdjoint`: the canonical C*-corollary.
-/

@[expose] public noncomputable section

open NormedSpace TrotterError FQFP Finset
open scoped RealScalar

namespace FQFP.BCH

section Definitions

variable {A : Type*} [NormedRing A] [Algebra ℝ A]

/-- The centered second-order commutator constant with the whole quintic Lie term retained. -/
def suzukiCenteredConjugationConstant (a b : A) (p : ℝ) : ℝ :=
  centeredConjugationConstant (List.ofFn (fiveStageStrangHalfGenerator a b p))
    (a + b) (suzukiQuinticTerm a b p)

/-- The centered second-order constant is nonnegative. -/
lemma suzukiCenteredConjugationConstant_nonneg (a b : A) (p : ℝ) :
    0 ≤ suzukiCenteredConjugationConstant a b p := centeredConjugationConstant_nonneg ..

/-- The seven generators in innermost-to-outermost order give exactly the
diagonal and strictly ordered mixed double commutators of the paper. -/
theorem suzukiCenteredConjugationConstant_eq_sum (a b : A) (p : ℝ) :
    let W := (centeredConjugationList
      (List.ofFn (fiveStageStrangHalfGenerator a b p)) (a + b)).get
    let L := suzukiQuinticTerm a b p
    suzukiCenteredConjugationConstant a b p =
      (∑ i, ‖⁅W i, ⁅W i, L⁆⁆‖) +
        2 * ∑ i, ∑ j ∈ univ.filter (fun j ↦ i < j), ‖⁅W j, ⁅W i, L⁆⁆‖ :=
  centeredConjugationConstant_eq_sum _ _ _

end Definitions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- **Centered Suzuki local bound.** This estimate holds for every nonnegative step,
with the original septic constant and the complete quintic Lie polynomial. -/
theorem norm_fiveStageStrangProduct_centered_sub_quintic_le (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (h : ℝ) (hh : 0 ≤ h) :
    ‖exp ((-h / 2) • (a + b)) *
        (fiveStageStrangProduct a b p h - exp (h • (a + b))) *
        exp ((-h / 2) • (a + b)) - h ^ 5 • suzukiQuinticTerm a b p‖ ≤
      quinticCenteredRemainder ‖suzukiQuinticTerm a b p‖ (suzukiSepticConstant a b p)
        (suzukiCenteredConjugationConstant a b p) h := by
  rw [fiveStageStrangProduct_eq_symmetricExpProduct]
  apply norm_centered_symmetricExpProduct_sub_quintic_le
  · exact suzukiSepticConstant_nonneg a b p
  · intro Z hZ t
    rcases List.mem_ofFn.mp hZ with ⟨i, rfl⟩
    exact norm_exp_smul_fiveStageStrangHalfGenerator_le_one a b p ha hb i t
  · exact hG
  · rw [fiveStageStrangHalfGenerator_ofFn, fiveStageStrangHalfArguments_sum]
  · exact norm_fiveStageStrang_halfDefect_add_sub_quartic_le a b p hp ha hb
  · exact hh

/-- Skew-adjoint inputs supply all exponential contractions in the centered local bound. -/
theorem norm_fiveStageStrangProduct_centered_sub_quintic_le_of_skewAdjoint
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : star a = -a) (hb : star b = -b) (h : ℝ) (hh : 0 ≤ h) :
    ‖exp ((-h / 2) • (a + b)) *
        (fiveStageStrangProduct a b p h - exp (h • (a + b))) *
        exp ((-h / 2) • (a + b)) - h ^ 5 • suzukiQuinticTerm a b p‖ ≤
      quinticCenteredRemainder ‖suzukiQuinticTerm a b p‖ (suzukiSepticConstant a b p)
        (suzukiCenteredConjugationConstant a b p) h := by
  apply norm_fiveStageStrangProduct_centered_sub_quintic_le a b p hp
    (norm_exp_smul_le_one_of_skewAdjoint ha) (norm_exp_smul_le_one_of_skewAdjoint hb)
    _ h hh
  exact norm_exp_smul_le_one_of_skewAdjoint
    ((skewAdjoint A).add_mem ha hb)

/-- The canonical Suzuki parameter automatically satisfies the cubic cancellation condition. -/
theorem norm_suzukiProduct_centered_sub_quintic_le_of_skewAdjoint
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A)
    (ha : star a = -a) (hb : star b = -b) (h : ℝ) (hh : 0 ≤ h) :
    ‖exp ((-h / 2) • (a + b)) *
        (fiveStageStrangProduct a b suzukiP h - exp (h • (a + b))) *
        exp ((-h / 2) • (a + b)) - h ^ 5 • suzukiQuinticTerm a b suzukiP‖ ≤
      quinticCenteredRemainder ‖suzukiQuinticTerm a b suzukiP‖
        (suzukiSepticConstant a b suzukiP) (suzukiCenteredConjugationConstant a b suzukiP) h :=
  norm_fiveStageStrangProduct_centered_sub_quintic_le_of_skewAdjoint
    a b suzukiP isSuzukiCubic_suzukiP ha hb h hh

end FQFP.BCH
