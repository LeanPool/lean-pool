/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiSepticCoefficients
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiLocalError
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SepticCenteredLocalError

/-!
# Refined Suzuki local bounds retaining the seventh-degree polynomial

The eighth-order grouped defect constant gives the ninth-order local tail.
The centered estimate uses the distinct centered seventh-degree coefficient,
with the complete grouped transport polynomials inside every norm.

## Main definitions

* `suzukiNonicConstant`: the integrated eighth-order grouped defect bound.
* `suzukiCenteredQuarticConstant`: the fourth-order transport bound on `L₅`.
* `suzukiCenteredQuadraticConstant`: the second-order transport bound on `M₇`.
* `suzukiCenteredNonicConstant`: their integrated combination `D₉`.

## Main results

* `norm_fiveStageStrangProduct_sub_exp_le_septic`: the all-real local bound.
* `norm_fiveStageStrangProduct_centered_sub_septic_le`: the centered bound.
-/

@[expose] public noncomputable section

open NormedSpace TrotterError FQFP Finset
open scoped RealScalar

namespace FQFP.BCH

section Definitions

variable {A : Type*} [NormedRing A] [Algebra ℝ A]

/-- The ninth-order defect remainder constant, with combined coefficients inside norms. -/
def suzukiNonicConstant (a b : A) (p : ℝ) : ℝ :=
  2 * groupedConjBound (fun i ↦ -fiveStageStrangHalfGenerator a b p i)
    (fiveStageStrangHalfGenerator a b p) (-(1 / 2 : ℝ) • (a + b)) 8 / 9

/-- The grouped fourth-order centered transport constant on the complete quintic term. -/
def suzukiCenteredQuarticConstant (a b : A) (p : ℝ) : ℝ :=
  groupedConjBound (centeredConjugationList
    (List.ofFn (fiveStageStrangHalfGenerator a b p)) (a + b)).get
      (fun _ ↦ 0) (suzukiQuinticTerm a b p) 4

/-- The grouped second-order centered transport constant on the complete defect septic term. -/
def suzukiCenteredQuadraticConstant (a b : A) (p : ℝ) : ℝ :=
  groupedConjBound (centeredConjugationList
    (List.ofFn (fiveStageStrangHalfGenerator a b p)) (a + b)).get
      (fun _ ↦ 0) (suzukiDefectSepticTerm a b p) 2

/-- The ninth-order centered transport constant with its exact integration factors. -/
def suzukiCenteredNonicConstant (a b : A) (p : ℝ) : ℝ :=
  suzukiNonicConstant a b p + 5 * suzukiCenteredQuarticConstant a b p / 9 +
    7 * suzukiCenteredQuadraticConstant a b p / 9

/-- The grouped ninth-order constant is nonnegative. -/
lemma suzukiNonicConstant_nonneg (a b : A) (p : ℝ) : 0 ≤ suzukiNonicConstant a b p :=
  div_nonneg (mul_nonneg (by norm_num) (groupedConjBound_nonneg ..)) (by norm_num)

/-- The grouped fourth-order transport constant is nonnegative. -/
lemma suzukiCenteredQuarticConstant_nonneg (a b : A) (p : ℝ) :
    0 ≤ suzukiCenteredQuarticConstant a b p := groupedConjBound_nonneg ..

/-- The grouped second-order transport constant is nonnegative. -/
lemma suzukiCenteredQuadraticConstant_nonneg (a b : A) (p : ℝ) :
    0 ≤ suzukiCenteredQuadraticConstant a b p := groupedConjBound_nonneg ..

/-- The integrated centered constant is nonnegative. -/
lemma suzukiCenteredNonicConstant_nonneg (a b : A) (p : ℝ) :
    0 ≤ suzukiCenteredNonicConstant a b p := by
  unfold suzukiCenteredNonicConstant
  exact add_nonneg (add_nonneg (suzukiNonicConstant_nonneg a b p)
    (div_nonneg (mul_nonneg (by norm_num) (suzukiCenteredQuarticConstant_nonneg a b p))
      (by norm_num)))
    (div_nonneg (mul_nonneg (by norm_num) (suzukiCenteredQuadraticConstant_nonneg a b p))
      (by norm_num))

end Definitions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- The even Suzuki defect retains both complete leading polynomials and a ninth-order tail. -/
theorem norm_fiveStageStrang_halfDefect_add_sub_quartic_sub_sextic_le (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1) (x : ℝ) :
    let l := List.ofFn (fiveStageStrangHalfGenerator a b p)
    ‖halfDefect l (a + b) x + halfDefect l (a + b) (-x) -
      (5 * x ^ 4) • suzukiQuinticTerm a b p -
        (7 * x ^ 6) • suzukiDefectSepticTerm a b p‖ ≤
      9 * suzukiNonicConstant a b p * |x| ^ 8 := by
  have h6 : groupedConjCoeff (fun i ↦ -fiveStageStrangHalfGenerator a b p i)
      (fiveStageStrangHalfGenerator a b p) (-(1 / 2 : ℝ) • (a + b)) 6 =
        (7 / 2 : ℝ) • suzukiDefectSepticTerm a b p := by
    unfold suzukiDefectSepticTerm
    module
  have h := norm_halfDefect_add_sub_quartic_sub_sextic_le
    (fiveStageStrangHalfGenerator a b p) (a + b) (suzukiQuinticTerm a b p)
    (suzukiDefectSepticTerm a b p)
    (norm_exp_smul_fiveStageStrangHalfGenerator_le_one a b p ha hb)
    (by simpa using groupedConjCoeff_fiveStageStrang_even a b p hp (0 : Fin 3))
    (by simpa using groupedConjCoeff_fiveStageStrang_even a b p hp (1 : Fin 3))
    (by simpa using groupedConjCoeff_fiveStageStrang_even a b p hp (2 : Fin 3)) h6 x
  convert h using 1
  unfold suzukiNonicConstant
  ring

/-- **Refined all-real Suzuki local bound.** The two leading polynomials remain unsplit. -/
theorem norm_fiveStageStrangProduct_sub_exp_le_septic (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (h : ℝ) :
    ‖fiveStageStrangProduct a b p h - exp (h • (a + b))‖ ≤
      septicStepBound ‖suzukiQuinticTerm a b p‖ ‖suzukiDefectSepticTerm a b p‖
        (suzukiNonicConstant a b p) |h| := by
  rw [fiveStageStrangProduct_eq_symmetricExpProduct]
  apply norm_symmetricExpProduct_sub_exp_le_septic
  · exact suzukiNonicConstant_nonneg a b p
  · intro Z hZ t
    rcases List.mem_ofFn.mp hZ with ⟨i, rfl⟩
    exact norm_exp_smul_fiveStageStrangHalfGenerator_le_one a b p ha hb i t
  · exact hG
  · exact norm_fiveStageStrang_halfDefect_add_sub_quartic_sub_sextic_le a b p hp ha hb

/-- **Centered refined Suzuki bound.** The septic term is the centered coefficient `N₇`. -/
theorem norm_fiveStageStrangProduct_centered_sub_septic_le (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (h : ℝ) (hh : 0 ≤ h) :
    ‖exp ((-h / 2) • (a + b)) *
        (fiveStageStrangProduct a b p h - exp (h • (a + b))) *
        exp ((-h / 2) • (a + b)) - h ^ 5 • suzukiQuinticTerm a b p -
          h ^ 7 • suzukiCenteredSepticTerm a b p‖ ≤
      septicCenteredRemainder ‖suzukiQuinticTerm a b p‖ ‖suzukiDefectSepticTerm a b p‖
        (suzukiNonicConstant a b p) (suzukiCenteredNonicConstant a b p) h := by
  let l := List.ofFn (fiveStageStrangHalfGenerator a b p)
  have hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1 := by
    intro Z hZ t
    rcases List.mem_ofFn.mp hZ with ⟨i, rfl⟩
    exact norm_exp_smul_fiveStageStrangHalfGenerator_le_one a b p ha hb i t
  rw [fiveStageStrangProduct_eq_symmetricExpProduct]
  simpa only [suzukiCenteredSepticTerm, suzukiCenteredNonicConstant] using
    norm_centered_symmetricExpProduct_sub_septic_le l (a + b) (suzukiQuinticTerm a b p)
      (suzukiDefectSepticTerm a b p)
      ⁅suzukiHalfQuadraticTerm a b p, suzukiQuinticTerm a b p⁆
      (suzukiNonicConstant a b p) (suzukiCenteredQuarticConstant a b p)
      (suzukiCenteredQuadraticConstant a b p) (suzukiNonicConstant_nonneg a b p) hZ hG
      (norm_fiveStageStrang_halfDefect_add_sub_quartic_sub_sextic_le a b p hp ha hb)
      (norm_centeredConjugation_sub_quadratic_le l (a + b) (suzukiQuinticTerm a b p)
        ⁅suzukiHalfQuadraticTerm a b p, suzukiQuinticTerm a b p⁆ hZ hG
        (conjCoeff_suzukiCentered_one ..) (conjCoeff_suzukiCentered_two ..)
        (conjCoeff_suzukiCentered_three a b (suzukiQuinticTerm a b p) p hp))
      (norm_centeredConjugation_sub_le_grouped l (a + b) (suzukiDefectSepticTerm a b p)
        hZ hG (conjCoeff_suzukiCentered_one ..)) h hh

/-- Skew-adjoint inputs supply the exponential bounds in the refined local estimate. -/
theorem norm_fiveStageStrangProduct_sub_exp_le_septic_of_skewAdjoint
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : star a = -a) (hb : star b = -b) (h : ℝ) :
    ‖fiveStageStrangProduct a b p h - exp (h • (a + b))‖ ≤
      septicStepBound ‖suzukiQuinticTerm a b p‖ ‖suzukiDefectSepticTerm a b p‖
        (suzukiNonicConstant a b p) |h| := by
  apply norm_fiveStageStrangProduct_sub_exp_le_septic a b p hp
    (norm_exp_smul_le_one_of_skewAdjoint ha) (norm_exp_smul_le_one_of_skewAdjoint hb)
  exact norm_exp_smul_le_one_of_skewAdjoint
    ((skewAdjoint A).add_mem ha hb)

/-- Skew-adjoint inputs supply all norm bounds in the centered refined estimate. -/
theorem norm_fiveStageStrangProduct_centered_sub_septic_le_of_skewAdjoint
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (ha : star a = -a) (hb : star b = -b) (h : ℝ) (hh : 0 ≤ h) :
    ‖exp ((-h / 2) • (a + b)) *
        (fiveStageStrangProduct a b p h - exp (h • (a + b))) *
        exp ((-h / 2) • (a + b)) - h ^ 5 • suzukiQuinticTerm a b p -
          h ^ 7 • suzukiCenteredSepticTerm a b p‖ ≤
      septicCenteredRemainder ‖suzukiQuinticTerm a b p‖ ‖suzukiDefectSepticTerm a b p‖
        (suzukiNonicConstant a b p) (suzukiCenteredNonicConstant a b p) h :=
  norm_fiveStageStrangProduct_centered_sub_septic_le a b p hp
    (norm_exp_smul_le_one_of_skewAdjoint ha) (norm_exp_smul_le_one_of_skewAdjoint hb)
    (norm_exp_smul_le_one_of_skewAdjoint
      ((skewAdjoint A).add_mem ha hb)) h hh

/-- The canonical parameter gives the refined local bound for all real steps. -/
theorem norm_suzukiProduct_sub_exp_le_septic_of_skewAdjoint
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A)
    (ha : star a = -a) (hb : star b = -b) (h : ℝ) :
    ‖fiveStageStrangProduct a b suzukiP h - exp (h • (a + b))‖ ≤
      septicStepBound ‖suzukiQuinticTerm a b suzukiP‖ ‖suzukiDefectSepticTerm a b suzukiP‖
        (suzukiNonicConstant a b suzukiP) |h| :=
  norm_fiveStageStrangProduct_sub_exp_le_septic_of_skewAdjoint
    a b suzukiP isSuzukiCubic_suzukiP ha hb h

/-- The canonical parameter gives the centered refined bound for every nonnegative step. -/
theorem norm_suzukiProduct_centered_sub_septic_le_of_skewAdjoint
    [StarRing A] [CStarRing A] [StarModule ℝ A] (a b : A)
    (ha : star a = -a) (hb : star b = -b) (h : ℝ) (hh : 0 ≤ h) :
    ‖exp ((-h / 2) • (a + b)) *
        (fiveStageStrangProduct a b suzukiP h - exp (h • (a + b))) *
        exp ((-h / 2) • (a + b)) - h ^ 5 • suzukiQuinticTerm a b suzukiP -
          h ^ 7 • suzukiCenteredSepticTerm a b suzukiP‖ ≤
      septicCenteredRemainder ‖suzukiQuinticTerm a b suzukiP‖
        ‖suzukiDefectSepticTerm a b suzukiP‖ (suzukiNonicConstant a b suzukiP)
        (suzukiCenteredNonicConstant a b suzukiP) h :=
  norm_fiveStageStrangProduct_centered_sub_septic_le_of_skewAdjoint
    a b suzukiP isSuzukiCubic_suzukiP ha hb h hh

end FQFP.BCH
