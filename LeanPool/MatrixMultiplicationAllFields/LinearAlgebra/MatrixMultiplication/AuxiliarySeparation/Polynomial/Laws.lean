/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ComplexEntropyContinuity
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FinCases

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Probability laws for the polynomial tensor inequalities

The determinant filtration uses an arbitrary binary law, while the three-sector
filtration uses the uniform law on three branches.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

/-- The common binary probability law used for every permuted character. -/
def binaryLaw (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) : FiniteLaw (Fin 2) where
  mass i := if i = 0 then q else 1 - q
  nonneg i := by
    fin_cases i
    · simpa using hq₀
    · simpa using sub_nonneg.mpr hq₁
  total := by simp [Fin.sum_univ_two]

@[simp] theorem binaryLaw_zero (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    (binaryLaw q hq₀ hq₁).mass 0 = q := by simp [binaryLaw]

@[simp] theorem binaryLaw_one (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    (binaryLaw q hq₀ hq₁).mass 1 = 1 - q := by simp [binaryLaw]

/-- The finite-law entropy agrees exactly with the binary entropy convention. -/
theorem binaryLaw_entropy (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    finiteEntropy (binaryLaw q hq₀ hq₁).mass = Real.binEntropy q := by
  simp [finiteEntropy, Fin.sum_univ_two, entropyTerm,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
  ring

theorem binaryLaw_product (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (f : Fin 2 → ℝ) :
    (∏ i, f i ^ (binaryLaw q hq₀ hq₁).mass i) = f 0 ^ q * f 1 ^ (1 - q) := by
  simp [Fin.prod_univ_two]

/-- The three-sector entropy factor is `3 ^ p`. -/
theorem uniformThree_entropy_factor (p : ℝ) :
    Real.exp (p * finiteEntropy (FiniteLaw.uniform (Fin 3)).mass) = (3 : ℝ) ^ p := by
  rw [FiniteLaw.uniform_entropy]
  norm_num only [Fintype.card_fin]
  rw [Real.rpow_def_of_pos (by norm_num)]
  congr 1
  ring

theorem uniformThree_product (f : Fin 3 → ℝ) :
    (∏ i, f i ^ (FiniteLaw.uniform (Fin 3)).mass i) =
      f 0 ^ (1 / 3 : ℝ) * f 1 ^ (1 / 3 : ℝ) * f 2 ^ (1 / 3 : ℝ) := by
  simp [Fin.prod_univ_three, FiniteLaw.uniform_mass, mul_assoc]

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
