/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiDefectJet
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SymmetricLocalError
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.HalfDefectConjugation
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiLocalAsymptotics

/-!
# All-real local bounds for the fourth-order Suzuki product

The exact quintic Lie polynomial is retained inside one norm. The ordinary
commutator constant and its grouped counterpart give separate seventh-order
remainders, for arbitrary real steps.

## Main definitions

* `suzukiSepticConstant`: the original seventh-order commutator constant.
* `suzukiGroupedSepticConstant`: the constant retaining combined defect coefficients.

## Main results

* `norm_fiveStageStrangProduct_sub_exp_le`: the original commutator local error bound.
* `norm_fiveStageStrangProduct_sub_exp_le_grouped`: the grouped local error bound.
* `norm_suzukiProduct_sub_exp_le_of_skewAdjoint`: the canonical C*-algebra theorem.
-/

@[expose] public noncomputable section

open NormedSpace TrotterError FQFP Finset
open scoped RealScalar

namespace FQFP.BCH

section Definitions

variable {A : Type*} [NormedRing A] [Algebra ℝ A]

/-- The original seventh-order constant, including the factorial and time-integration factor. -/
def suzukiSepticConstant (a b : A) (p : ℝ) : ℝ :=
  halfDefectCommutatorConstant (List.ofFn (fiveStageStrangHalfGenerator a b p)) a b 6

/-- The original seventh-order remainder constant is nonnegative. -/
lemma suzukiSepticConstant_nonneg (a b : A) (p : ℝ) :
    0 ≤ suzukiSepticConstant a b p := halfDefectCommutatorConstant_nonneg ..

/-- The grouped seventh-order constant, with all combined coefficients retained inside norms. -/
def suzukiGroupedSepticConstant (a b : A) (p : ℝ) : ℝ :=
  2 * groupedConjBound (fun i ↦ -fiveStageStrangHalfGenerator a b p i)
    (fiveStageStrangHalfGenerator a b p) (-(1 / 2 : ℝ) • (a + b)) 6 / 7

/-- The grouped seventh-order remainder constant is nonnegative. -/
lemma suzukiGroupedSepticConstant_nonneg (a b : A) (p : ℝ) :
    0 ≤ suzukiGroupedSepticConstant a b p :=
  div_nonneg (mul_nonneg (by norm_num) (groupedConjBound_nonneg ..)) (by norm_num)

end Definitions

section HalfGenerators

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Exponential contractions of the two generators control every signed half-stage. -/
lemma norm_exp_smul_fiveStageStrangHalfGenerator_le_one (a b : A) (p : ℝ)
    (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1) (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (i : Fin 6) (t : ℝ) : ‖exp (t • fiveStageStrangHalfGenerator a b p i)‖ ≤ 1 := by
  fin_cases i <;> simp only [fiveStageStrangHalfGenerator, Matrix.cons_val,
    Fin.reduceFinMk, smul_smul]
  all_goals first | exact ha _ | exact hb _

end HalfGenerators

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- The original sixth-order finite conjugation remainder of the middle defect. -/
theorem norm_fiveStageStrang_halfDefect_add_sub_quartic_le (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1) (x : ℝ) :
    let l := List.ofFn (fiveStageStrangHalfGenerator a b p)
    ‖halfDefect l (a + b) x + halfDefect l (a + b) (-x) -
      (5 * x ^ 4) • suzukiQuinticTerm a b p‖ ≤ 7 * suzukiSepticConstant a b p * |x| ^ 6 := by
  have h0 := groupedConjCoeff_fiveStageStrang_even a b p hp (0 : Fin 3)
  have h2 := groupedConjCoeff_fiveStageStrang_even a b p hp (1 : Fin 3)
  have h4 := groupedConjCoeff_fiveStageStrang_even a b p hp (2 : Fin 3)
  norm_num only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceMul,
    Fin.reduceEq, ite_false, ite_true] at h0 h2 h4
  have hr := norm_halfDefect_add_sub_sum_le_commutator (fiveStageStrangHalfGenerator a b p)
    a b (norm_exp_smul_fiveStageStrangHalfGenerator_le_one a b p ha hb) 6 (by norm_num) x
  rw [sum_even_pow_smul_eq_quartic _ _ h0 h2 h4] at hr
  simpa only [suzukiSepticConstant, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
    show (6 + 1 : ℝ) = 7 by norm_num] using hr

/-- **All-real local bound.** The quintic Lie polynomial remains combined in
one norm, and the remainder is the original seventh-order commutator constant. -/
theorem norm_fiveStageStrangProduct_sub_exp_le (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1) (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1)
    (h : ℝ) :
    ‖fiveStageStrangProduct a b p h - exp (h • (a + b))‖ ≤
      |h| ^ 5 * ‖suzukiQuinticTerm a b p‖ + |h| ^ 7 * suzukiSepticConstant a b p := by
  rw [fiveStageStrangProduct_eq_symmetricExpProduct]
  apply norm_symmetricExpProduct_sub_exp_le (hC := suzukiSepticConstant_nonneg a b p)
  · intro Z hZ t
    rcases List.mem_ofFn.mp hZ with ⟨i, rfl⟩
    exact norm_exp_smul_fiveStageStrangHalfGenerator_le_one a b p ha hb i t
  · exact hG
  · exact norm_fiveStageStrang_halfDefect_add_sub_quartic_le a b p hp ha hb

/-- The grouped local error bound, with the quintic Lie term combined inside a single norm. -/
theorem norm_fiveStageStrangProduct_sub_exp_le_grouped (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1) (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1)
    (h : ℝ) :
    ‖fiveStageStrangProduct a b p h - exp (h • (a + b))‖ ≤
      |h| ^ 5 * ‖suzukiQuinticTerm a b p‖ + |h| ^ 7 * suzukiGroupedSepticConstant a b p := by
  rw [fiveStageStrangProduct_eq_symmetricExpProduct]
  apply norm_symmetricExpProduct_sub_exp_le_grouped
  · exact norm_exp_smul_fiveStageStrangHalfGenerator_le_one a b p ha hb
  · exact hG
  · simpa using groupedConjCoeff_fiveStageStrang_even a b p hp (0 : Fin 3)
  · simpa using groupedConjCoeff_fiveStageStrang_even a b p hp (1 : Fin 3)
  · simpa using groupedConjCoeff_fiveStageStrang_even a b p hp (2 : Fin 3)

/-- In a C*-algebra, skew-adjoint input generators automatically supply every
exponential norm premise of the grouped local bound. -/
theorem norm_fiveStageStrangProduct_sub_exp_le_grouped_of_skewAdjoint
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : star a = -a) (hb : star b = -b) (h : ℝ) :
    ‖fiveStageStrangProduct a b p h - exp (h • (a + b))‖ ≤
      |h| ^ 5 * ‖suzukiQuinticTerm a b p‖ + |h| ^ 7 * suzukiGroupedSepticConstant a b p := by
  apply norm_fiveStageStrangProduct_sub_exp_le_grouped a b p hp
    (norm_exp_smul_le_one_of_skewAdjoint ha) (norm_exp_smul_le_one_of_skewAdjoint hb)
  exact norm_exp_smul_le_one_of_skewAdjoint (by simp only [star_add, ha, hb, neg_add_rev,
    add_comm])

/-- The original local bound in a C*-algebra requires only skew-adjoint generators. -/
theorem norm_fiveStageStrangProduct_sub_exp_le_of_skewAdjoint
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : star a = -a) (hb : star b = -b) (h : ℝ) :
    ‖fiveStageStrangProduct a b p h - exp (h • (a + b))‖ ≤
      |h| ^ 5 * ‖suzukiQuinticTerm a b p‖ + |h| ^ 7 * suzukiSepticConstant a b p := by
  apply norm_fiveStageStrangProduct_sub_exp_le a b p hp
    (norm_exp_smul_le_one_of_skewAdjoint ha) (norm_exp_smul_le_one_of_skewAdjoint hb)
  exact norm_exp_smul_le_one_of_skewAdjoint (by simp only [star_add, ha, hb, neg_add_rev,
    add_comm])

/-- **Canonical Suzuki local bound.** The cubic cancellation of the fixed
Suzuki parameter is supplied by the library, for every real step. -/
theorem norm_suzukiProduct_sub_exp_le_of_skewAdjoint
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A)
    (ha : star a = -a) (hb : star b = -b) (h : ℝ) :
    ‖fiveStageStrangProduct a b suzukiP h - exp (h • (a + b))‖ ≤
      |h| ^ 5 * ‖suzukiQuinticTerm a b suzukiP‖ + |h| ^ 7 * suzukiSepticConstant a b suzukiP :=
  norm_fiveStageStrangProduct_sub_exp_le_of_skewAdjoint a b suzukiP isSuzukiCubic_suzukiP ha hb h

/-- The canonical grouped local bound automatically uses the certified Suzuki parameter. -/
theorem norm_suzukiProduct_sub_exp_le_grouped_of_skewAdjoint
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A)
    (ha : star a = -a) (hb : star b = -b) (h : ℝ) :
    ‖fiveStageStrangProduct a b suzukiP h - exp (h • (a + b))‖ ≤
      |h| ^ 5 * ‖suzukiQuinticTerm a b suzukiP‖ +
        |h| ^ 7 * suzukiGroupedSepticConstant a b suzukiP :=
  norm_fiveStageStrangProduct_sub_exp_le_grouped_of_skewAdjoint
    a b suzukiP isSuzukiCubic_suzukiP ha hb h

end FQFP.BCH
