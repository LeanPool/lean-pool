/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurUpperGaussian.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurUpperSplit

/-!
# Matrix Schur upper Gaussian

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `schurStrictUpperGaussianDensity_integral`,
`matrixGaussianDensity_schurUpper_normalized_split`.
-/

@[expose] public section

open Matrix MeasureTheory Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section

theorem matrixHSNormSq_schurUpper {n : ℕ} (y : SchurUpperIndex n → ℂ) :
    matrixHSNormSq (schurUpperCombination y) = ∑ p, Complex.normSq (y p) := by
  classical
  rw [matrixHSNormSq_eq_sum]
  rw [← Fintype.sum_prod_type (fun p : Fin n × Fin n =>
    Complex.normSq (schurUpperCombination y p.1 p.2))]
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun p : Fin n × Fin n => p.1 ≤ p.2)
    (fun p => Complex.normSq (schurUpperCombination y p.1 p.2))]
  have hz : (∑ p : {p : Fin n × Fin n // ¬p.1 ≤ p.2},
      Complex.normSq (schurUpperCombination y p.val.1 p.val.2)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [schurUpperCombination_lower_zero y _ _ (lt_of_not_ge p.property)]
    simp
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro p hp
  rw [schurUpperCombination_entry]

theorem matrixHSNormSq_schurUpper_split {n : ℕ} (y : SchurUpperIndex n → ℂ) :
    matrixHSNormSq (schurUpperCombination y) =
      (∑ i, Complex.normSq ((schurUpperSplit n y).1 i)) +
        ∑ p, Complex.normSq ((schurUpperSplit n y).2 p) := by
  classical
  rw [matrixHSNormSq_schurUpper,
    ← Fintype.sum_subtype_add_sum_subtype
      (fun p : SchurUpperIndex n => p.val.1 = p.val.2) (fun p => Complex.normSq (y p))]
  congr 1
  exact (Equiv.sum_comp (schurUpperDiagonalEquiv n).symm
    (fun p : {p : SchurUpperIndex n // p.val.1 = p.val.2} => Complex.normSq (y p.val))).symm

/-- The product of the complex Gaussian coordinate densities over the strictly upper
entries. -/
def schurStrictUpperGaussianDensity (n : ℕ) (u : SchurStrictUpperIndex n → ℂ) : ℝ≥0∞ :=
  ∏ p, complexCoordinateGaussianDensity n (u p)

theorem schurStrictUpperGaussianDensity_integral {n : ℕ} (hn : 0 < n) :
    ∫⁻ u, schurStrictUpperGaussianDensity n u = 1 := by
  classical
  have hm : (Measure.pi (fun _ : SchurStrictUpperIndex n =>
      (complexCoordinateGaussianProbability n : Measure ℂ))) Set.univ = 1 := measure_univ
  have hsf : ∀ i : SchurStrictUpperIndex n, SigmaFinite
      ((volume : Measure ℂ).withDensity (complexCoordinateGaussianDensity n)) :=
    fun _ => by rw [← complexCoordinateGaussianMeasure_eq_withDensity hn]; infer_instance
  have hp := @Measure.pi_withDensity _ _ _ _
    (fun _ : SchurStrictUpperIndex n => (volume : Measure ℂ)) (by intro i; infer_instance)
    (fun _ : SchurStrictUpperIndex n => complexCoordinateGaussianDensity n)
    (fun _ => measurable_complexCoordinateGaussianDensity n) hsf
  simp_rw [complexCoordinateGaussianMeasure_eq_withDensity hn] at hm
  rw [hp, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at hm
  exact hm

theorem schurStrictUpperGaussianDensity_formula {n : ℕ} (u : SchurStrictUpperIndex n → ℂ) :
    schurStrictUpperGaussianDensity n u =
      ENNReal.ofReal (((n : ℝ) / Real.pi) ^ Fintype.card (SchurStrictUpperIndex n)) *
        ENNReal.ofReal (Real.exp (-(n : ℝ) * ∑ p, Complex.normSq (u p))) := by
  classical
  unfold schurStrictUpperGaussianDensity complexCoordinateGaussianDensity
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← Real.exp_sum, ← Finset.mul_sum]
    exact ENNReal.ofReal_mul (pow_nonneg (div_nonneg (Nat.cast_nonneg n) Real.pi_pos.le) _)
  · intro i hi
    positivity

theorem matrixGaussianDensity_schurUpper_split {n : ℕ} (y : SchurUpperIndex n → ℂ) :
    matrixGaussianDensity n (schurUpperCombination y) =
      ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n*n)) *
      ENNReal.ofReal (Real.exp (-(n : ℝ) * ∑ i, Complex.normSq ((schurUpperSplit n y).1 i))) *
      ENNReal.ofReal (Real.exp (-(n : ℝ) * ∑ p, Complex.normSq ((schurUpperSplit n y).2 p))) := by
  unfold matrixGaussianDensity
  rw [matrixHSNormSq_schurUpper_split, mul_add, Real.exp_add,
    ENNReal.ofReal_mul (pow_nonneg (div_nonneg (Nat.cast_nonneg n) Real.pi_pos.le) _),
    ENNReal.ofReal_mul (Real.exp_nonneg _), ← mul_assoc]

/-- The normalizing factor `(n / π)^(n²) / (n / π)^N`, where `N` is the number of strictly upper
entries. -/
def schurUpperGaussianDiagonalFactor (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n*n)) *
    (ENNReal.ofReal (((n : ℝ) / Real.pi) ^ Fintype.card (SchurStrictUpperIndex n)))⁻¹

theorem matrixGaussianDensity_schurUpper_normalized_split {n : ℕ} (hn : 0 < n)
    (y : SchurUpperIndex n → ℂ) :
    matrixGaussianDensity n (schurUpperCombination y) =
      schurUpperGaussianDiagonalFactor n *
        ENNReal.ofReal (Real.exp (-(n : ℝ) * ∑ i, Complex.normSq ((schurUpperSplit n y).1 i))) *
          schurStrictUpperGaussianDensity n (schurUpperSplit n y).2 := by
  have hb : ENNReal.ofReal (((n : ℝ) / Real.pi) ^ Fintype.card (SchurStrictUpperIndex n)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos (div_pos (Nat.cast_pos.mpr hn) Real.pi_pos) _))
  rw [matrixGaussianDensity_schurUpper_split, schurStrictUpperGaussianDensity_formula]
  unfold schurUpperGaussianDiagonalFactor
  symm
  calc
    _ = ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n*n)) *
      ENNReal.ofReal (Real.exp (-(n : ℝ) * ∑ i, Complex.normSq ((schurUpperSplit n y).1 i))) *
      ((ENNReal.ofReal (((n : ℝ) / Real.pi) ^ Fintype.card (SchurStrictUpperIndex n)))⁻¹ *
        ENNReal.ofReal (((n : ℝ) / Real.pi) ^ Fintype.card (SchurStrictUpperIndex n))) *
      ENNReal.ofReal (Real.exp (-(n : ℝ) * ∑ p, Complex.normSq ((schurUpperSplit n y).2 p))) := by
          ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hb ENNReal.ofReal_ne_top, mul_one]

end
end GinibrePoincare
