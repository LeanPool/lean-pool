/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths and consolidated proofs. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiDefectJet
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.ConjugationCoefficients
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.ConjugationSeriesCoefficients
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiHalfTransportJet

/-!
# The distinct seventh-degree Suzuki coefficients

The defect coefficient, centered coefficient, and formal logarithm coefficient
are different mathematical objects. The centered transport begins with its
quadratic coefficient, the ordered pair-bracket sum of the half-generators.

## Main definitions

* `suzukiHalfQuadraticTerm`: the quadratic coefficient of centered half-transport.
* `suzukiDefectSepticTerm`: the degree-six even-defect coefficient divided by seven.
* `suzukiCenteredSepticTerm`: the centered seventh-degree coefficient.
* `suzukiBchSepticTerm`: the formal logarithm's seventh-degree coefficient.
-/

@[expose] public noncomputable section

open FQFP TrotterError Finset PowerSeries

namespace FQFP.BCH

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The quadratic centered half-transport coefficient, in the paper's ordered form. -/
def suzukiHalfQuadraticTerm (a b : A) (p : ℝ) : A :=
  (1 / 2 : ℝ) • ∑ i : Fin 6, ∑ j ∈ univ.filter (fun j ↦ i < j),
    ⁅fiveStageStrangHalfGenerator a b p i, fiveStageStrangHalfGenerator a b p j⁆

/-- The complete septic defect polynomial `M₇ = 2 f₆ / 7`. -/
def suzukiDefectSepticTerm (a b : A) (p : ℝ) : A :=
  (2 / 7 : ℝ) • groupedConjCoeff (fun i ↦ -fiveStageStrangHalfGenerator a b p i)
    (fiveStageStrangHalfGenerator a b p) (-(1 / 2 : ℝ) • (a + b)) 6

/-- The centered septic polynomial `N₇ = M₇ + 5 [Ω₂,L₅] / 7`. -/
def suzukiCenteredSepticTerm (a b : A) (p : ℝ) : A :=
  suzukiDefectSepticTerm a b p +
    (5 / 7 : ℝ) • ⁅suzukiHalfQuadraticTerm a b p, suzukiQuinticTerm a b p⁆

/-- The septic formal BCH coefficient of the symmetric half-generator list. -/
def suzukiBchSepticTerm (a b : A) (p : ℝ) : A :=
  letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
  let l := List.ofFn (fiveStageStrangHalfGenerator a b p)
  expListLogCoeff (l ++ l.reverse) 7

/-- The centered coefficient retains the complete defect and transport polynomials. -/
theorem suzukiCenteredSepticTerm_eq (a b : A) (p : ℝ) :
    suzukiCenteredSepticTerm a b p = suzukiDefectSepticTerm a b p +
      (5 / 7 : ℝ) • ⁅suzukiHalfQuadraticTerm a b p, suzukiQuinticTerm a b p⁆ := rfl

/-- The ordered half-stage sum reduces to a single binary commutator. -/
theorem suzukiHalfQuadraticTerm_eq (a b : A) (p : ℝ) :
    suzukiHalfQuadraticTerm a b p = (2 * p ^ 2 - p + 1 / 8) • ⁅a, b⁆ := by
  simp only [suzukiHalfQuadraticTerm, Fin.sum_univ_succ, Finset.sum_filter]
  norm_num [fiveStageStrangHalfGenerator, Ring.lie_def,
    smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
  module

section Conjugation

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Centering cancels the linear half-transport coefficient. -/
theorem conjCoeff_suzukiCentered_one (a b B : A) (p : ℝ) :
    conjCoeff (centeredConjugationList
      (List.ofFn (fiveStageStrangHalfGenerator a b p)) (a + b)).get B 1 = 0 := by
  apply conjCoeff_centeredConjugationList_one
  rw [fiveStageStrangHalfGenerator_ofFn]
  exact fiveStageStrangHalfArguments_sum a b p

/-- The quadratic centered transport is the bracket with the complete `Ω₂`. -/
theorem conjCoeff_suzukiCentered_two (a b B : A) (p : ℝ) :
    conjCoeff (centeredConjugationList
      (List.ofFn (fiveStageStrangHalfGenerator a b p)) (a + b)).get B 2 =
      ⁅suzukiHalfQuadraticTerm a b p, B⁆ := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  let H := -(1 / 2 : ℝ) • (a + b) :: List.ofFn (fiveStageStrangHalfGenerator a b p)
  rw [← coeff_expListSeries_conjugate, List.ofFn_get]
  have h := coeff_conjugate_two_of_one_eq_zero
    (expListSeries H) (expListSeries (H.reverse.map Neg.neg)) B
    (expListSeries_mul_reverse_neg H) (by simp [expListSeries])
    (by simp [expListSeries])
    (by simpa only [coeff_expListSeries] using expListTerm_suzukiCenteredHalf_one a b p)
  have h2 : coeff 2 (expListSeries H) = suzukiHalfQuadraticTerm a b p := by
    simpa only [H, coeff_expListSeries, suzukiHalfQuadraticTerm_eq] using
      expListTerm_suzukiCenteredHalf_two a b p
  rw [h2] at h
  convert h using 1
  simp only [H, centeredConjugationList, List.reverse_append,
    List.reverse_reverse, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.map_append, List.map_cons, List.map_nil, List.singleton_append]

/-- Fourth-order accuracy removes the cubic centered transport coefficient. -/
theorem conjCoeff_suzukiCentered_three (a b B : A) (p : ℝ) (hp : IsSuzukiCubic p) :
    conjCoeff (centeredConjugationList
      (List.ofFn (fiveStageStrangHalfGenerator a b p)) (a + b)).get B 3 = 0 := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  let H := -(1 / 2 : ℝ) • (a + b) :: List.ofFn (fiveStageStrangHalfGenerator a b p)
  rw [← coeff_expListSeries_conjugate, List.ofFn_get]
  have h := coeff_conjugate_three_of_one_eq_zero_of_three_eq_zero
    (expListSeries H) (expListSeries (H.reverse.map Neg.neg)) B
    (expListSeries_mul_reverse_neg H) (by simp [expListSeries])
    (by simp [expListSeries])
    (by simpa only [coeff_expListSeries] using expListTerm_suzukiCenteredHalf_one a b p)
    (by simpa only [coeff_expListSeries] using expListTerm_suzukiCenteredHalf_three a b p hp)
  convert h using 1
  simp only [H, centeredConjugationList, List.reverse_append,
    List.reverse_reverse, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.map_append, List.map_cons, List.map_nil, List.singleton_append]

end Conjugation

end FQFP.BCH
