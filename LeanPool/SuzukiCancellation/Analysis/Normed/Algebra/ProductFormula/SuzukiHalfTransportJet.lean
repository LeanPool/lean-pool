/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiDefectJet
public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.Palindromic
public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.ExponentialListLowDegree

/-!
# Finite jets of the centered Suzuki half-product

The centered half-product begins with its quadratic commutator coefficient.
The formal logarithm of the full symmetric product has no even coefficients.

## Main results

* `expListTerm_suzukiCenteredHalf_one`: vanishing of the linear coefficient.
* `expListTerm_suzukiCenteredHalf_two`: the complete quadratic coefficient.
* `expListTerm_suzukiCenteredHalf_three`: vanishing of the cubic coefficient.
* `expListLogCoeff_suzuki_even`: parity of the formal Suzuki logarithm.
-/

@[expose] public noncomputable section

open FQFP Finset

namespace FQFP.BCH

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Every even coefficient of the full Suzuki formal logarithm vanishes. -/
theorem expListLogCoeff_suzuki_even (a b : A) (p : ℝ) (n : ℕ) (hn : Even n) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    let l := List.ofFn (fiveStageStrangHalfGenerator a b p)
    expListLogCoeff (l ++ l.reverse) n = 0 := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  exact expListLogCoeff_eq_zero_of_reverse_eq _ (by simp) n hn

/-- In particular, no eighth-degree coefficient is present in the formal logarithm. -/
theorem expListLogCoeff_suzuki_eight (a b : A) (p : ℝ) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    let l := List.ofFn (fiveStageStrangHalfGenerator a b p)
    expListLogCoeff (l ++ l.reverse) 8 = 0 :=
  expListLogCoeff_suzuki_even a b p 8 (by decide)

/-- The centered half-product has no linear coefficient. -/
theorem expListTerm_suzukiCenteredHalf_one (a b : A) (p : ℝ) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    expListTerm (-(1 / 2 : ℝ) • (a + b) ::
      List.ofFn (fiveStageStrangHalfGenerator a b p)) 1 = 0 := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  simp only [expListTerm_one, List.ofFn_succ, fiveStageStrangHalfGenerator,
    List.sum_cons]
  norm_num
  module

/-- The quadratic half-product coefficient is exactly the complete ordered bracket sum. -/
theorem expListTerm_suzukiCenteredHalf_two (a b : A) (p : ℝ) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    expListTerm (-(1 / 2 : ℝ) • (a + b) ::
      List.ofFn (fiveStageStrangHalfGenerator a b p)) 2 =
        (2 * p ^ 2 - p + 1 / 8) • ⁅a, b⁆ := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  simp only [List.ofFn_succ, fiveStageStrangHalfGenerator, expListTerm_cons_two,
    List.sum_cons]
  norm_num [expListTerm, Ring.lie_def, ← Rat.cast_smul_eq_qsmul ℝ,
    smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul,
    smul_pow]
  noncomm_ring
  module

/-- The cubic centered half-product coefficient is half the ordinary cubic defect. -/
theorem expListTerm_suzukiCenteredHalf_three_eq (a b : A) (p : ℝ) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    expListTerm (-(1 / 2 : ℝ) • (a + b) ::
      List.ofFn (fiveStageStrangHalfGenerator a b p)) 3 =
        suzukiCubicCoeff p •
          ((-1 / 48 : ℝ) • ⁅a, ⁅a, b⁆⁆ + (-1 / 24 : ℝ) • ⁅b, ⁅a, b⁆⁆) := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  simp only [List.ofFn_succ, fiveStageStrangHalfGenerator, expListTerm_cons_three,
    expListTerm_cons_two, List.sum_cons]
  norm_num [expListTerm, Ring.lie_def, suzukiCubicCoeff, ← Rat.cast_smul_eq_qsmul ℝ,
    smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul,
    smul_pow]
  noncomm_ring
  module

/-- Cubic cancellation removes the cubic coefficient of the centered half-product. -/
theorem expListTerm_suzukiCenteredHalf_three (a b : A) (p : ℝ) (hp : IsSuzukiCubic p) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    expListTerm (-(1 / 2 : ℝ) • (a + b) ::
      List.ofFn (fiveStageStrangHalfGenerator a b p)) 3 = 0 := by
  rw [expListTerm_suzukiCenteredHalf_three_eq, show suzukiCubicCoeff p = 0 from hp,
    zero_smul]

end FQFP.BCH
